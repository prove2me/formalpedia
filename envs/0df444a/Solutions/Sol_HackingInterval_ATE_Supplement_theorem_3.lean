-- Prove2me | solution 1 for HackingInterval.ATE.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:18:55.837101+00:00
-- url     : https://prove2.me/submissions/91776ed8-1d5d-4814-a70f-5745c437e20e

import Mathlib
import Definitions.Def_HackingInterval_ATE_Supplement_Calibration
import Definitions.Def_HackingInterval_ATE_Supplement_GaussianEndpoints
import Definitions.Def_HackingInterval_ATE_Supplement_ChiMean
open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal

open HackingInterval
open HackingInterval.ATE
open HackingInterval.ATE.Supplement

/-- Theorem 3, both conditional variances under Equation (19).
The design is fixed and arbitrary; only Y is sampled. No derived Gaussian/chi law is assumed. -/
theorem solution {n p : ℕ} (D : TreatData n p)
    (hrank : IsUnit (D.Xtᵀ * D.Xt).det) (hdof : p + 1 < n)
    (β : Fin p ⊕ Unit → ℝ) (σ : ℝ≥0) (r : ℝ) (hr : 0 < r) :
    let P := responseLaw D β σ
    let ν := residualDof n p
    let v := (σ : ℝ) ^ 2 * D.Vtt * (1 + r * ((ν : ℝ) - chiMean ν ^ 2))
    MemLp (lowerEndpoint D r) 2 P ∧ MemLp (upperEndpoint D r) 2 P ∧
      variance (lowerEndpoint D r) P = v ∧ variance (upperEndpoint D r) P = v := by
        intro P ν v
        -- standard Gaussian moments of the norm
        have hmom : ∀ m : ℕ, 1 ≤ m →
            (∫ x, ‖x‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))) = chiMean m ∧
            (∫ x, ‖x‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin m)))) = m := by
          intro m hm
          have : Nontrivial (EuclideanSpace ℝ (Fin m)) :=
            Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
          set ρ : (Fin m → ℝ) → ℝ := fun x => ∏ i, gaussianPDFReal 0 1 (x i)
          have hρm : Measurable ρ := by
            simp only [ρ]
            exact Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)
          have hpi : Measure.pi (fun _ : Fin m => gaussianReal 0 1) =
              volume.withDensity (fun x => ENNReal.ofReal (ρ x)) := by

            refine Measure.pi_eq (fun s hs => ?_)
            rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
            have hpt : ∀ x, (Set.univ.pi s).indicator (fun x => ENNReal.ofReal (ρ x)) x =
                ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
              intro x
              by_cases hx : x ∈ Set.univ.pi s
              · rw [Set.indicator_of_mem hx]
                congr 1
                refine Finset.prod_congr rfl fun i _ => ?_
                rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
              · rw [Set.indicator_of_notMem hx]
                simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
                obtain ⟨i, hi⟩ := hx
                rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _), ENNReal.ofReal_zero]
            simp_rw [hpt]
            have hint : ∀ i, Integrable ((s i).indicator (gaussianPDFReal 0 1)) :=
              fun i => (integrable_gaussianPDFReal 0 1).indicator (hs i)
            rw [← ofReal_integral_eq_lintegral_ofReal]
            · rw [integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg]
              · refine Finset.prod_congr rfl fun i _ => ?_
                rw [gaussianReal_apply_eq_integral _ one_ne_zero, integral_indicator (hs i)]
              · intro i _
                exact integral_nonneg fun x => Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) x
            · exact Integrable.fintype_prod (f := fun i => (s i).indicator (gaussianPDFReal 0 1)) hint
            · exact ae_of_all _ fun x => Finset.prod_nonneg fun i _ =>
                Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _

          set C : ℝ := (m : ℝ) * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1) *
            ((Real.sqrt (2 * Real.pi))⁻¹) ^ m
          have hgen : ∀ g : ℝ → ℝ, ∫ x, g ‖x‖ ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) =
              C * ∫ y in Set.Ioi (0:ℝ), y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * g y) := by
            intro g
            rw [← map_pi_eq_stdGaussian, ← MeasurableEquiv.coe_toLp, integral_map_equiv, hpi,
              integral_withDensity_eq_integral_toReal_smul (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
            have hpt : ∀ x : Fin m → ℝ, (ENNReal.ofReal (ρ x)).toReal • g ‖(MeasurableEquiv.toLp 2 (Fin m → ℝ)) x‖ =
                (fun y => ((Real.sqrt (2 * Real.pi))⁻¹) ^ m * (Real.exp (-y ^ 2 / 2) * g y))
                  ‖WithLp.toLp 2 x‖ := by
              intro x
              rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _)]
              simp only [gaussianPDFReal, MeasurableEquiv.coe_toLp, smul_eq_mul]
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
                ← Real.exp_sum, EuclideanSpace.norm_sq_eq]
              simp only [NNReal.coe_one, mul_one, sub_zero, Real.norm_eq_abs, sq_abs]
              rw [show (-∑ i, x i ^ 2) / 2 = ∑ i, -x i ^ 2 / 2 by
                rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]; simp only [neg_div]]
              ring
            refine (integral_congr_ae (ae_of_all _ hpt)).trans ?_
            refine ((PiLp.volume_preserving_toLp (Fin m)).integral_comp
              (MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurableEmbedding (fun z : EuclideanSpace ℝ (Fin m) => (fun y => ((Real.sqrt (2 * Real.pi))⁻¹) ^ m * (Real.exp (-y ^ 2 / 2) * g y)) ‖z‖)).trans ?_
            refine (integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin m)))
              (fun y => ((Real.sqrt (2 * Real.pi))⁻¹) ^ m * (Real.exp (-y ^ 2 / 2) * g y))).trans ?_
            rw [finrank_euclideanSpace_fin]
            simp only [C, nsmul_eq_mul, smul_eq_mul, ← integral_const_mul]
            congr 1; funext y; ring
          have hJ : ∀ k : ℕ, ∫ y in Set.Ioi (0:ℝ), y ^ k * Real.exp (-y ^ 2 / 2) =
              (1/2 : ℝ) ^ (-((k:ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((k:ℝ) + 1) / 2) := by
            intro k
            rw [← integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0:ℝ) < 2)
              (by have := k.cast_nonneg (α := ℝ); linarith) (by norm_num : (0:ℝ) < 1/2)]
            refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
            rw [Real.rpow_natCast, Real.rpow_two]
            ring_nf
          have e0 := hgen (fun _ => 1)
          have e1 := hgen (fun y => y)
          have e2 := hgen (fun y => y ^ 2)
          have c0 : (fun y : ℝ => y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * 1)) =
              fun y => y ^ (m - 1) * Real.exp (-y ^ 2 / 2) := by funext y; ring
          have c1 : (fun y : ℝ => y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * y)) =
              fun y => y ^ m * Real.exp (-y ^ 2 / 2) := by
            funext y
            conv_rhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
            ring
          have c2 : (fun y : ℝ => y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * y ^ 2)) =
              fun y => y ^ (m + 1) * Real.exp (-y ^ 2 / 2) := by
            funext y
            conv_rhs => rw [show m + 1 = (m - 1) + 2 by omega, pow_add]
            ring
          simp only [c0, c1, c2, hJ] at e0 e1 e2
          rw [integral_const, probReal_univ, smul_eq_mul, mul_one] at e0
          have hm1 : (((m - 1 : ℕ) : ℝ) + 1) / 2 = (m : ℝ) / 2 := by
            rw [Nat.cast_sub hm]; push_cast; ring
          rw [hm1] at e0
          have hmpos : (0:ℝ) < (m:ℝ) / 2 := by
            have : (1:ℝ) ≤ m := by exact_mod_cast hm
            linarith
          have hΓ : Real.Gamma ((m:ℝ) / 2) ≠ 0 := (Real.Gamma_pos_of_pos hmpos).ne'
          have hA : ∀ x y : ℝ, (1/2:ℝ) ^ (x + y) = (1/2:ℝ) ^ x * (1/2:ℝ) ^ y :=
            fun x y => Real.rpow_add (by norm_num) x y
          have hs2 : (1/2:ℝ) ^ (-(1/2:ℝ)) = Real.sqrt 2 := by
            rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, Real.sqrt_div' 1 (by norm_num : (0:ℝ) ≤ 2),
              Real.sqrt_one]; field_simp
          have h2 : (1/2:ℝ) ^ (-(1:ℝ)) = 2 := by rw [Real.rpow_neg_one]; norm_num
          constructor
          · rw [e1, show -((m:ℝ) + 1) / 2 = -((m:ℝ) / 2) + (-(1/2)) by ring, hA, hs2,
              show ((m:ℝ) + 1) / 2 = ((m:ℝ) + 1) / 2 from rfl]
            rw [show -(((m - 1 : ℕ) : ℝ) + 1) / 2 = -((m:ℝ) / 2) by rw [← hm1]; ring] at e0
            unfold chiMean
            rw [eq_div_iff hΓ]
            linear_combination (-(Real.sqrt 2 * Real.Gamma (((m:ℝ) + 1) / 2))) * e0
          · rw [e2, show -(((m + 1 : ℕ) : ℝ) + 1) / 2 = -((m:ℝ) / 2) + (-1) by push_cast; ring, hA, h2,
              show (((m + 1 : ℕ) : ℝ) + 1) / 2 = (m:ℝ) / 2 + 1 by push_cast; ring,
              Real.Gamma_add_one hmpos.ne']
            rw [show -(((m - 1 : ℕ) : ℝ) + 1) / 2 = -((m:ℝ) / 2) by rw [← hm1]; ring] at e0
            linear_combination (-(m:ℝ)) * e0
        set E := EuclideanSpace ℝ (Fin n)
        set γ := stdGaussian E
        set W : Submodule ℝ E := LinearMap.range (Matrix.toEuclideanLin D.Xt)
        set K : Submodule ℝ E := Wᗮ
        have hKdim : Module.finrank ℝ K = ν := by
          have hMX : ((D.Xtᵀ * D.Xt)⁻¹ * D.Xtᵀ) * D.Xt = 1 := by
            simp only [Matrix.mul_assoc]
            exact Matrix.nonsing_inv_mul _ hrank
          set M := (D.Xtᵀ * D.Xt)⁻¹ * D.Xtᵀ
          have hinj : Function.Injective (Matrix.toEuclideanLin D.Xt) := by
            rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
            intro b hb
            have h1 : D.Xt *ᵥ WithLp.ofLp b = 0 := congrArg WithLp.ofLp hb
            have h2 : WithLp.ofLp b = 0 := by
              rw [← one_mulVec (WithLp.ofLp b), ← hMX, ← mulVec_mulVec, h1, mulVec_zero]
            exact congrArg (WithLp.toLp 2) h2
          have hW : Module.finrank ℝ W = p + 1 := by
            rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace, Fintype.card_sum,
              Fintype.card_fin, Fintype.card_unit]
          have hsum := Submodule.finrank_add_finrank_orthogonal W
          rw [finrank_euclideanSpace_fin, hW] at hsum
          change p + 1 + Module.finrank ℝ K = n at hsum
          simp only [ν, residualDof]
          omega
        set M := (D.Xtᵀ * D.Xt)⁻¹ * D.Xtᵀ
        set a : E := WithLp.toLp 2 (fun i => M (Sum.inr ()) i)
        have ha : ‖a‖ ^ 2 = D.Vtt := by
          have hMMt : M * Mᵀ = (D.Xtᵀ * D.Xt)⁻¹ᵀ := by
            simp only [M, transpose_mul, transpose_transpose]
            rw [Matrix.mul_assoc, ← Matrix.mul_assoc D.Xtᵀ D.Xt, ← Matrix.mul_assoc,
              nonsing_inv_mul _ hrank, Matrix.one_mul]
          have hV : D.Vtt = (M * Mᵀ) (Sum.inr ()) (Sum.inr ()) := by
            rw [hMMt]; rfl
          rw [hV, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), mul_apply]
          simp only [transpose_apply, a, Real.norm_eq_abs, sq_abs, sq, abs_mul_abs_self]
        set μv : Fin n → ℝ := D.Xt *ᵥ β
        set T : E → (Fin n → ℝ) := fun z => μv + (σ : ℝ) • WithLp.ofLp z
        have hP : P = γ.map T := by
          have hg : ∀ i, (gaussianReal 0 1).map (fun x => μv i + (σ:ℝ) * x) = gaussianReal (μv i) (σ^2) := by
            intro i
            have : (fun x => μv i + (σ:ℝ) * x) = (fun x => x + μv i) ∘ (fun x => (σ:ℝ) * x) := by
              funext x; simp [add_comm]
            rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
              gaussianReal_map_add_const]
            congr 1
            · simp
            · ext; simp
          have hγ : γ = (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (WithLp.toLp 2) :=
            (map_pi_eq_stdGaussian).symm
          rw [hγ, Measure.map_map (by fun_prop) (by fun_prop)]
          have hT' : T ∘ WithLp.toLp 2 = fun x i => (fun i x => μv i + (σ:ℝ) * x) i (x i) := by
            funext x i; simp [T]
          rw [hT', Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1)
            (f := fun i x => μv i + (σ:ℝ) * x) (fun i => by fun_prop)]
          simp only [hg]
          rfl
        have hb0 : ∀ Y, (withResponse D Y).beta0TildeLS = inner ℝ a (WithLp.toLp 2 Y) := by
          intro Y
          simp only [TreatData.beta0TildeLS, TreatData.betaTildeLS, Design.betaLS, TreatData.full,
            withResponse, TreatData.Xt, mulVec_mulVec, a, M, PiLp.inner_apply, RCLike.inner_apply,
            conj_trivial]
          simp only [mulVec, dotProduct, mul_comm]
          rfl
        have hSSE : ∀ Y, (withResponse D Y).SSE = ‖K.starProjection (WithLp.toLp 2 Y)‖ ^ 2 := by
          intro Y
          set f : Fin n → ℝ := D.Xt *ᵥ (M *ᵥ Y) with hf
          have hfW : WithLp.toLp 2 f ∈ W := ⟨WithLp.toLp 2 (M *ᵥ Y), rfl⟩
          have hres : K.starProjection (WithLp.toLp 2 Y) = WithLp.toLp 2 (Y - f) := by
            apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
            · rw [Submodule.mem_orthogonal]
              rintro u ⟨b, rfl⟩
              have h0 : D.Xtᵀ *ᵥ (Y - f) = 0 := by
                simp only [f, M, mulVec_sub, mulVec_mulVec, ← Matrix.mul_assoc]
                rw [Matrix.mul_nonsing_inv _ hrank, Matrix.one_mul, sub_self]
              change inner ℝ (WithLp.toLp 2 (D.Xt *ᵥ WithLp.ofLp b)) (WithLp.toLp 2 (Y - f)) = 0
              rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_mulVec,
                ← mulVec_transpose, h0, zero_dotProduct]
            · intro w hw
              have : WithLp.toLp 2 Y - WithLp.toLp 2 (Y - f) = WithLp.toLp 2 f := by
                rw [← WithLp.toLp_sub, sub_sub_cancel]
              rw [this]
              exact Submodule.inner_right_of_mem_orthogonal hfW hw
          rw [hres, EuclideanSpace.norm_sq_eq]
          change ∑ i, (Y i - (D.Xt *ᵥ ((D.Xtᵀ * D.Xt)⁻¹ *ᵥ (D.Xtᵀ *ᵥ Y))) i) ^ 2 = _
          simp only [Real.norm_eq_abs, sq_abs, f, M, mulVec_mulVec, WithLp.ofLp_toLp, Pi.sub_apply]
        have hμW : WithLp.toLp 2 μv ∈ W := ⟨WithLp.toLp 2 β, rfl⟩
        have hμK : K.starProjection (WithLp.toLp 2 μv) = 0 := by
          rw [Submodule.starProjection_apply_eq_zero_iff]
          exact Submodule.le_orthogonal_orthogonal W hμW
        have hMX : M * D.Xt = 1 := by
          simp only [M, Matrix.mul_assoc]
          exact Matrix.nonsing_inv_mul _ hrank
        have hμa : inner ℝ a (WithLp.toLp 2 μv) = β (Sum.inr ()) := by
          have h1 : inner ℝ a (WithLp.toLp 2 μv) = (M *ᵥ μv) (Sum.inr ()) := by
            simp only [mulVec, dotProduct]
            rw [Finset.sum_congr rfl fun i _ => mul_comm (M (Sum.inr ()) i) (μv i)]
            rfl
          rw [h1, mulVec_mulVec, hMX, one_mulVec]
        -- facts about U = ⟪a,·⟫ and N = ‖P_K ·‖ under γ
        set U : E → ℝ := fun z => inner ℝ a z
        set N : E → ℝ := fun z => ‖K.starProjection z‖
        have hid : MemLp (id : E → E) 2 γ := IsGaussian.memLp_two_id
        have hU2 : MemLp U 2 γ := by
          have := (innerSL ℝ a).comp_memLp' hid
          simpa [U, Function.comp_def, innerSL_apply_apply] using this
        have hN2 : MemLp N 2 γ := by
          refine hid.of_le (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
          simp only [N, id, Real.norm_eq_abs]; rw [abs_of_nonneg (norm_nonneg _)]; exact K.norm_starProjection_apply_le z
        have hUint : ∫ z, U z ∂γ = 0 := by
          have := integral_strongDual_stdGaussian (E := E) (innerSL ℝ a)
          simpa [U, innerSL_apply_apply] using this
        have hUvar : variance U γ = D.Vtt := by
          have := variance_dual_stdGaussian (E := E) (innerSL ℝ a)
          rw [innerSL_apply_norm, ha] at this
          rw [← this]; rfl
        have hν1 : 1 ≤ ν := by simp only [ν, residualDof]; omega
        set bK := stdOrthonormalBasis ℝ K
        set L : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ K)) :=
          bK.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L K.orthogonalProjection
        have hLn : ∀ z, ‖L z‖ = N z := by
          intro z
          simp only [L, N, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
            LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map,
            K.starProjection_apply]
          rfl
        have hLaw : γ.map L = stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ K))) := by
          apply Measure.ext_of_charFunDual
          funext L'
          rw [charFunDual_map, charFunDual_stdGaussian, charFunDual_stdGaussian]
          suffices hn : ‖L'.comp L‖ = ‖L'‖ by rw [hn]
          apply le_antisymm
          · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
            rw [ContinuousLinearMap.comp_apply]
            refine (L'.le_opNorm _).trans ?_
            gcongr
            rw [hLn]; exact K.norm_starProjection_apply_le z
          · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
            have hy : L ((bK.repr.symm y : K) : E) = y := by
              simp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
                LinearIsometryEquiv.coe_toContinuousLinearEquiv, K.orthogonalProjection_mem_subspace_eq_self,
                LinearIsometryEquiv.apply_symm_apply]
            have := (L'.comp L).le_opNorm ((bK.repr.symm y : K) : E)
            rw [ContinuousLinearMap.comp_apply, hy] at this
            refine this.trans (le_of_eq ?_)
            congr 1
            exact LinearIsometryEquiv.norm_map bK.repr.symm y
        have hNint : ∫ z, N z ∂γ = chiMean ν := by
          have := (hmom _ (hKdim ▸ hν1)).1
          rw [← hLaw, integral_map (by fun_prop) (by fun_prop)] at this
          simp only [hLn] at this
          rw [this, hKdim]
        have hNsq : ∫ z, N z ^ 2 ∂γ = ν := by
          have := (hmom _ (hKdim ▸ hν1)).2
          rw [← hLaw, integral_map (by fun_prop) (by fun_prop)] at this
          simp only [hLn] at this
          rw [this, hKdim]
        have hUN : ∫ z, U z * N z ∂γ = 0 := by
          have hneg : γ.map (LinearIsometryEquiv.neg ℝ (E := E)) = γ := stdGaussian_map _
          have h : ∫ z, U z * N z ∂(γ.map (LinearIsometryEquiv.neg ℝ (E := E))) = ∫ z, U z * N z ∂γ := by
            rw [hneg]
          rw [integral_map (by fun_prop) (by fun_prop)] at h
          have h2 : (fun z => U ((LinearIsometryEquiv.neg ℝ (E := E)) z) * N ((LinearIsometryEquiv.neg ℝ (E := E)) z))
              = fun z => -(U z * N z) := by
            funext z; simp [U, N, inner_neg_right]; left; exact norm_neg _
          rw [h2, integral_neg] at h
          linarith
        have hV : ∀ Y, (withResponse D Y).Vtt = D.Vtt := fun Y => rfl
        have hVtt : 0 ≤ D.Vtt := by rw [← ha]; positivity
        set c : ℝ := Real.sqrt D.Vtt * Real.sqrt r * (σ : ℝ)
        have hkey : ∀ s : ℝ, s ^ 2 = 1 →
            MemLp (fun z => ((σ : ℝ) * U z + (s * c) * N z) + β (Sum.inr ())) 2 γ ∧
            variance (fun z => ((σ : ℝ) * U z + (s * c) * N z) + β (Sum.inr ())) γ = v := by
          intro s hs
          have h1 : MemLp (fun z => (σ : ℝ) * U z) 2 γ := hU2.const_mul _
          have h2 : MemLp (fun z => (s * c) * N z) 2 γ := hN2.const_mul _
          refine ⟨(h1.add h2).add (memLp_const _), ?_⟩
          rw [variance_add_const (X := fun z => (σ : ℝ) * U z + (s * c) * N z)
            (by exact (h1.add h2).aestronglyMeasurable), variance_fun_add h1 h2,
            variance_const_mul, variance_const_mul, covariance_eq_sub h1 h2, variance_eq_sub hN2]
          have e1 : ∫ z, (fun z => (σ : ℝ) * U z) z ∂γ = 0 := by
            simp only [integral_const_mul, hUint, mul_zero]
          have e2 : ∫ z, ((fun z => (σ : ℝ) * U z) * fun z => (s * c) * N z) z ∂γ = 0 := by
            have : ((fun z => (σ : ℝ) * U z) * fun z => (s * c) * N z) =
                fun z => ((σ : ℝ) * (s * c)) * (U z * N z) := by
              funext z; simp only [Pi.mul_apply]; ring
            rw [this, integral_const_mul, hUN, mul_zero]
          have e3 : ∫ z, (N ^ 2) z ∂γ = ν := by simpa only [Pi.pow_apply] using hNsq
          rw [e1, e2, e3, hNint, hUvar]
          simp only [v, c]
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hVtt, Real.sq_sqrt hr.le, hs]
          ring
        have hT : Measurable T := by fun_prop
        have hEval : ∀ z, T z = WithLp.ofLp (WithLp.toLp 2 μv + (σ : ℝ) • z) := by
          intro z; rfl
        have hform : ∀ (s : ℝ) (z : E), β (Sum.inr ()) + (σ : ℝ) * U z +
            s * (Real.sqrt D.Vtt * Real.sqrt (r * ‖K.starProjection (WithLp.toLp 2 (T z))‖ ^ 2)) =
            ((σ : ℝ) * U z + (s * c) * N z) + β (Sum.inr ()) := by
          intro s z
          have : WithLp.toLp 2 (T z) = WithLp.toLp 2 μv + (σ : ℝ) • z := rfl
          rw [this, map_add, map_smul, hμK, zero_add, norm_smul, mul_pow, Real.norm_eq_abs,
            abs_of_nonneg (NNReal.coe_nonneg σ)]
          have hs : Real.sqrt (r * ((σ:ℝ) ^ 2 * ‖K.starProjection z‖ ^ 2)) =
              Real.sqrt r * ((σ:ℝ) * ‖K.starProjection z‖) := by
            rw [← mul_pow, Real.sqrt_mul hr.le, Real.sqrt_sq (by positivity)]
          rw [hs]; simp only [c, N]; ring
        have hlow : lowerEndpoint D r ∘ T =
            fun z => ((σ : ℝ) * U z + ((-1) * c) * N z) + β (Sum.inr ()) := by
          funext z
          rw [← hform]
          simp only [Function.comp, lowerEndpoint, TreatData.beta0Min, hb0, hSSE, hV]
          have : WithLp.toLp 2 (T z) = WithLp.toLp 2 μv + (σ : ℝ) • z := rfl
          rw [show (1 + r) * ‖K.starProjection (WithLp.toLp 2 (T z))‖ ^ 2 -
            ‖K.starProjection (WithLp.toLp 2 (T z))‖ ^ 2 = r * ‖K.starProjection (WithLp.toLp 2 (T z))‖ ^ 2
            by ring]
          rw [this, inner_add_right, inner_smul_right, hμa]
          simp only [U]; ring
        have hup : upperEndpoint D r ∘ T =
            fun z => ((σ : ℝ) * U z + ((1) * c) * N z) + β (Sum.inr ()) := by
          funext z
          rw [← hform]
          simp only [Function.comp, upperEndpoint, TreatData.beta0Max, hb0, hSSE, hV]
          have : WithLp.toLp 2 (T z) = WithLp.toLp 2 μv + (σ : ℝ) • z := rfl
          rw [show (1 + r) * ‖K.starProjection (WithLp.toLp 2 (T z))‖ ^ 2 -
            ‖K.starProjection (WithLp.toLp 2 (T z))‖ ^ 2 = r * ‖K.starProjection (WithLp.toLp 2 (T z))‖ ^ 2
            by ring]
          rw [this, inner_add_right, inner_smul_right, hμa]
          simp only [U]; ring
        have hlowc : Continuous (lowerEndpoint D r) := by
          have : lowerEndpoint D r = fun Y => inner ℝ a (WithLp.toLp 2 Y) - Real.sqrt D.Vtt *
              Real.sqrt ((1 + r) * ‖K.starProjection (WithLp.toLp 2 Y)‖ ^ 2 -
                ‖K.starProjection (WithLp.toLp 2 Y)‖ ^ 2) := by
            funext Y; simp only [lowerEndpoint, TreatData.beta0Min, hb0, hSSE, hV]
          rw [this]; fun_prop
        have hupc : Continuous (upperEndpoint D r) := by
          have : upperEndpoint D r = fun Y => inner ℝ a (WithLp.toLp 2 Y) + Real.sqrt D.Vtt *
              Real.sqrt ((1 + r) * ‖K.starProjection (WithLp.toLp 2 Y)‖ ^ 2 -
                ‖K.starProjection (WithLp.toLp 2 Y)‖ ^ 2) := by
            funext Y; simp only [upperEndpoint, TreatData.beta0Max, hb0, hSSE, hV]
          rw [this]; fun_prop
        obtain ⟨hm1, hv1⟩ := hkey (-1) (by norm_num)
        obtain ⟨hm2, hv2⟩ := hkey 1 (by norm_num)
        rw [hP]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [memLp_map_measure_iff hlowc.aestronglyMeasurable hT.aemeasurable, hlow]; exact hm1
        · rw [memLp_map_measure_iff hupc.aestronglyMeasurable hT.aemeasurable, hup]; exact hm2
        · rw [variance_map hlowc.aemeasurable hT.aemeasurable, hlow]; exact hv1
        · rw [variance_map hupc.aemeasurable hT.aemeasurable, hup]; exact hv2
