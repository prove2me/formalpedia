-- Prove2me | solution 1 for NoisyPrototyping.ReservationPolicy.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:08:45.707179+00:00
-- url     : https://prove2.me/submissions/8ff50071-0806-46f7-8d8b-e9d7da56c1ab

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Supplement_Gaussian

open NoisyPrototyping
open NoisyPrototyping.ReservationPolicy
open NoisyPrototyping.ReservationPolicy.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal
theorem solution {N : ℕ} (μ σ : Fin N → ℝ) (τ : Fin N → ℝ≥0∞) (w : Fin N → ℝ)
    (hσ : ∀ i, 0 < σ i) (hτ : ∀ i, τ i ≠ 0) (hw : ∀ i, 0 < w i)
    (Rstd : ℝ → ℝ) (hRstd : ∀ x : ℝ, 0 < x → IsNormalRoot x (Rstd x))
    (ord : Fin N ≃ Fin N)
    (hord : ∀ a b, a ≤ b →
      gaussianIndex Rstd (μ (ord b)) (σ (ord b)) (τ (ord b)) (w (ord b)) ≤
        gaussianIndex Rstd (μ (ord a)) (σ (ord a)) (τ (ord a)) (w (ord a))) :
    Admissible (gaussianProblem μ σ τ w)
        (fidelityPolicy (fun i m => adjustedValue (μ i) (σ i) (τ i) m) ord
          (fun i => gaussianIndex Rstd (μ i) (σ i) (τ i) (w i))) ∧
    ∀ ρ : Policy N, Admissible (gaussianProblem μ σ τ w) ρ →
      value (gaussianProblem μ σ τ w) ρ ≤
        value (gaussianProblem μ σ τ w)
          (fidelityPolicy (fun i m => adjustedValue (μ i) (σ i) (τ i) m) ord
            (fun i => gaussianIndex Rstd (μ i) (σ i) (τ i) (w i))) := by
              classical
              have G0 : ∀ (μ σ : ℝ) (τ : ℝ≥0∞), IsProbabilityMeasure (gaussianLaw μ σ τ) ∧
                  Integrable (fun z : ℝ × ℝ => z.1) (gaussianLaw μ σ τ) ∧
                  Integrable (fun z : ℝ × ℝ => z.2) (gaussianLaw μ σ τ) := by
                intro μ σ τ
                unfold gaussianLaw
                obtain ⟨v1, hv1⟩ : ∃ v1 : NNReal, (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal) = v1 := ⟨_, rfl⟩
                obtain ⟨v2, hv2⟩ : ∃ v2 : NNReal, (τ⁻¹).toNNReal ^ 2 = v2 := ⟨_, rfl⟩
                rw [hv1, hv2]
                have hφ : Measurable (fun z : ℝ × ℝ => (z.1, z.1 + z.2)) := by fun_prop
                have h1 : Integrable (fun z : ℝ × ℝ => z.1) ((gaussianReal μ v1).prod (gaussianReal 0 v2)) :=
                  ((memLp_id_gaussianReal (μ := μ) (v := v1) 1).comp_measurePreserving
                    (measurePreserving_fst (μ := gaussianReal μ v1) (ν := gaussianReal 0 v2))).integrable le_rfl
                have h2 : Integrable (fun z : ℝ × ℝ => z.2) ((gaussianReal μ v1).prod (gaussianReal 0 v2)) :=
                  ((memLp_id_gaussianReal (μ := 0) (v := v2) 1).comp_measurePreserving
                    (measurePreserving_snd (μ := gaussianReal μ v1) (ν := gaussianReal 0 v2))).integrable le_rfl
                refine ⟨Measure.isProbabilityMeasure_map hφ.aemeasurable, ?_, ?_⟩
                · rw [integrable_map_measure (by fun_prop) hφ.aemeasurable]
                  exact h1
                · rw [integrable_map_measure (by fun_prop) hφ.aemeasurable]
                  exact h1.add h2
              have G1 : ∀ (μ σ : ℝ) (τ : ℝ≥0∞) (w : ℝ) (hσ : 0 < σ) (hτ : τ ≠ 0) (hw : 0 < w)
                  (Rstd : ℝ → ℝ) (hR : ∀ x : ℝ, 0 < x → IsNormalRoot x (Rstd x)),
                  ∫ z, max (adjustedValue μ σ τ z.2 - gaussianIndex Rstd μ σ τ w) 0 ∂(gaussianLaw μ σ τ)
                    = w := by
                intro μ σ τ w hσ hτ hw Rstd hR
                set s : ℝ := invFidelity τ with hs
                set ff : ℝ := fidelityFactor σ τ with hff
                have hff1 : ff ^ 2 = 1 + (s / σ) ^ 2 := by
                  rw [hff, fidelityFactor, Real.sq_sqrt (by positivity)]
                have hffpos : 0 < ff := by
                  rw [hff, fidelityFactor]; apply Real.sqrt_pos.mpr; positivity
                set c : ℝ := σ * ff with hc
                set x : ℝ := w * ff / σ with hx
                have hxpos : 0 < x := by positivity
                set r : ℝ := Rstd x with hr
                set g : ℝ → ℝ := fun m => max (adjustedValue μ σ τ m - gaussianIndex Rstd μ σ τ w) 0 with hg
                have hgc : Continuous g := by
                  simp only [hg, adjustedValue]; fun_prop
                -- law of m
                have hlaw : Measure.map (fun x : ℝ × ℝ => x.1 + x.2)
                    ((gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩).prod (gaussianReal 0 ((τ⁻¹).toNNReal ^ 2))) =
                    Measure.map (fun z => c * z + μ) (gaussianReal 0 1) := by
                  have h1 := (gaussianReal_conv_gaussianReal (m₁ := μ) (m₂ := 0)
                    (v₁ := ⟨σ ^ 2, sq_nonneg σ⟩) (v₂ := (τ⁻¹).toNNReal ^ 2))
                  rw [Measure.conv] at h1
                  rw [h1]
                  have h2 : Measure.map (fun z => c * z + μ) (gaussianReal 0 1) =
                      Measure.map (fun x => x + μ) (Measure.map (fun x => c * x) (gaussianReal 0 1)) := by
                    rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
                  rw [h2, gaussianReal_map_const_mul, gaussianReal_map_add_const]
                  congr 1
                  · ring
                  · ext
                    change σ ^ 2 + ((τ⁻¹).toNNReal : ℝ) ^ 2 = c ^ 2 * 1
                    have : s = ((τ⁻¹).toNNReal : ℝ) := rfl
                    rw [← this, hc, mul_pow, hff1]
                    field_simp
                have hint : ∫ z, g z.2 ∂(gaussianLaw μ σ τ) = ∫ z, g (c * z + μ) ∂(gaussianReal 0 1) := by
                  have e1 : ∫ z, g z.2 ∂(gaussianLaw μ σ τ) = ∫ z, g (z.1 + z.2)
                      ∂((gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩).prod (gaussianReal 0 ((τ⁻¹).toNNReal ^ 2))) := by
                    unfold gaussianLaw
                    exact integral_map (φ := fun z : ℝ × ℝ => (z.1, z.1 + z.2)) (f := fun z : ℝ × ℝ => g z.2)
                      (by fun_prop) (hgc.comp continuous_snd).aestronglyMeasurable
                  have e2 := integral_map (φ := fun x : ℝ × ℝ => x.1 + x.2) (f := g)
                    (μ := (gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩).prod (gaussianReal 0 ((τ⁻¹).toNNReal ^ 2)))
                    (by fun_prop) hgc.aestronglyMeasurable
                  have e3 := integral_map (φ := fun z : ℝ => c * z + μ) (f := g) (μ := gaussianReal 0 1)
                    (by fun_prop) hgc.aestronglyMeasurable
                  rw [e1, ← e2, hlaw, e3]
                have hpt : ∀ z, g (c * z + μ) = σ / ff * max (z - r) 0 := by
                  intro z
                  simp only [hg, adjustedValue, gaussianIndex]
                  rw [← hff, ← hs, ← hx, ← hr]
                  have hk : 1 / (1 + (s / σ) ^ 2) = 1 / ff ^ 2 := by rw [hff1]
                  rw [hk]
                  have : μ + (c * z + μ - μ) * (1 / ff ^ 2) - (μ + σ / ff * r) = σ / ff * (z - r) := by
                    rw [hc]; field_simp; ring
                  rw [this, mul_max_of_nonneg (z - r) 0 (le_of_lt (by positivity : (0:ℝ) < σ / ff)), mul_zero]
                have hroot := hR x hxpos
                rw [IsNormalRoot] at hroot
                have hI : Integrable (fun z : ℝ => max (z - r) 0) (gaussianReal 0 1) := by
                  have := ((IsGaussian.integrable_fun_id (μ := gaussianReal 0 1)) |>.sub (integrable_const r)).sup
                    (integrable_const (0:ℝ))
                  exact this
                have hmax : (fun z : ℝ => max r z) = fun z => r + max (z - r) 0 := by
                  funext z
                  rcases le_total r z with h | h
                  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
                  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
                have hE : ∫ z, max (z - r) 0 ∂(gaussianReal 0 1) = x := by
                  rw [hmax, integral_add (integrable_const r) hI] at hroot
                  simp at hroot
                  linarith
                show ∫ z, g z.2 ∂(gaussianLaw μ σ τ) = w
                rw [hint]
                simp_rw [hpt]
                rw [integral_const_mul, hE, hx]
                field_simp
              have G2 : ∀ (μ σ : ℝ) (τ : ℝ≥0∞) (hσ : 0 < σ) (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ)
                  (hC : ∀ x, |f x| ≤ C),
                  ∫ z, f z.2 * z.1 ∂(gaussianLaw μ σ τ) =
                    ∫ z, f z.2 * adjustedValue μ σ τ z.2 ∂(gaussianLaw μ σ τ) := by
                intro μ σ τ hσ f hf C hC
                unfold gaussianLaw
                obtain ⟨v1, hv1⟩ : ∃ v1 : NNReal, (⟨σ ^ 2, sq_nonneg σ⟩ : NNReal) = v1 := ⟨_, rfl⟩
                obtain ⟨v2, hv2⟩ : ∃ v2 : NNReal, (τ⁻¹).toNNReal ^ 2 = v2 := ⟨_, rfl⟩
                have hv1r : (v1 : ℝ) = σ ^ 2 := by rw [← hv1]; rfl
                have hv2r : (v2 : ℝ) = invFidelity τ ^ 2 := by rw [← hv2]; simp [invFidelity]
                rw [hv1, hv2]
                set Q := (gaussianReal μ v1).prod (gaussianReal 0 v2) with hQ
                set k : ℝ := 1 / (1 + (invFidelity τ / σ) ^ 2) with hk
                have hkey : k * (v1 : ℝ) + k * (v2 : ℝ) = (v1 : ℝ) := by
                  rw [hv1r, hv2r, hk]
                  have : σ ^ 2 ≠ 0 := by positivity
                  field_simp
                have hφ : Measurable (fun z : ℝ × ℝ => (z.1, z.1 + z.2)) := by fun_prop
                have hmpf : MeasurePreserving Prod.fst Q (gaussianReal μ v1) := measurePreserving_fst
                have hmps : MeasurePreserving Prod.snd Q (gaussianReal 0 v2) := measurePreserving_snd
                have hm1 : MemLp (fun z : ℝ × ℝ => z.1) 2 Q :=
                  (memLp_id_gaussianReal (μ := μ) (v := v1) 2).comp_measurePreserving hmpf
                have hm2 : MemLp (fun z : ℝ × ℝ => z.2) 2 Q :=
                  (memLp_id_gaussianReal (μ := 0) (v := v2) 2).comp_measurePreserving hmps
                have hi1 : Integrable (fun z : ℝ × ℝ => z.1) Q := hm1.integrable one_le_two
                have hi2 : Integrable (fun z : ℝ × ℝ => z.2) Q := hm2.integrable one_le_two
                have hvar1 : Var[fun z : ℝ × ℝ => z.1; Q] = v1 := by
                  have := variance_map (X := id) (μ := Q) (Y := Prod.fst) aemeasurable_id
                    measurable_fst.aemeasurable
                  rw [hmpf.map_eq, variance_id_gaussianReal] at this
                  rw [this]; rfl
                have hvar2 : Var[fun z : ℝ × ℝ => z.2; Q] = v2 := by
                  have := variance_map (X := id) (μ := Q) (Y := Prod.snd) aemeasurable_id
                    measurable_snd.aemeasurable
                  rw [hmps.map_eq, variance_id_gaussianReal] at this
                  rw [this]; rfl
                have hind : IndepFun (fun z : ℝ × ℝ => z.1) (fun z : ℝ × ℝ => z.2) Q := by
                  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
                    measurable_snd.aemeasurable]
                  simp [Q]
                have hc12 : cov[fun z : ℝ × ℝ => z.1, fun z : ℝ × ℝ => z.2; Q] = 0 :=
                  hind.covariance_eq_zero hm1 hm2
                have hc21 : cov[fun z : ℝ × ℝ => z.2, fun z : ℝ × ℝ => z.1; Q] = 0 :=
                  hind.symm.covariance_eq_zero hm2 hm1
                have hc11 : cov[fun z : ℝ × ℝ => z.1, fun z : ℝ × ℝ => z.1; Q] = v1 := by
                  rw [covariance_self (by fun_prop), hvar1]
                have hc22 : cov[fun z : ℝ × ℝ => z.2, fun z : ℝ × ℝ => z.2; Q] = v2 := by
                  rw [covariance_self (by fun_prop), hvar2]
                -- the residual `Yp` and the observation `M`
                set Yp : ℝ × ℝ → ℝ := fun z => (1 - k) * z.1 - k * z.2 with hYp
                set M : ℝ × ℝ → ℝ := fun z => z.1 + z.2 with hM
                have hcov : cov[Yp, M; Q] = 0 := by
                  have e1 : Yp = (fun z : ℝ × ℝ => (1 - k) * z.1) - (fun z : ℝ × ℝ => k * z.2) := rfl
                  have e2 : M = (fun z : ℝ × ℝ => z.1) + (fun z : ℝ × ℝ => z.2) := rfl
                  rw [e1, e2, covariance_sub_left (hm1.const_mul _) (hm2.const_mul _) (hm1.add hm2),
                    covariance_add_right (hm1.const_mul _) hm1 hm2,
                    covariance_add_right (hm2.const_mul _) hm1 hm2,
                    covariance_const_mul_left, covariance_const_mul_left, covariance_const_mul_left,
                    covariance_const_mul_left, hc11, hc12, hc21, hc22]
                  linear_combination -hkey
                have hid : HasGaussianLaw id Q := ⟨by rw [Measure.map_id]; infer_instance⟩
                have hG : HasGaussianLaw (fun z => (Yp z, M z)) Q := by
                  set L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
                    ((1 - k) • ContinuousLinearMap.fst ℝ ℝ ℝ - k • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
                    (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) with hL
                  have := hid.map L
                  have hfun : (fun z => (Yp z, M z)) = ⇑L ∘ id := by
                    funext z; simp [L, Yp, M]
                  rw [hfun]; exact this
                have hYM : IndepFun M Yp Q := (hG.indepFun_of_covariance_eq_zero hcov).symm
                have hqm : Measurable (adjustedValue μ σ τ) := by unfold adjustedValue; fun_prop
                rw [integral_map (f := fun z : ℝ × ℝ => f z.2 * z.1) hφ.aemeasurable
                    ((hf.comp measurable_snd).mul measurable_fst).aestronglyMeasurable,
                  integral_map (f := fun z : ℝ × ℝ => f z.2 * adjustedValue μ σ τ z.2) hφ.aemeasurable
                    ((hf.comp measurable_snd).mul (hqm.comp measurable_snd)).aestronglyMeasurable]
                simp only
                set c : ℝ := (1 - k) * μ with hc
                have hpt : ∀ z : ℝ × ℝ, f (z.1 + z.2) * z.1 =
                    f (M z) * adjustedValue μ σ τ (M z) + f (M z) * (Yp z - c) := by
                  intro z
                  simp only [hM, hYp, hc, adjustedValue]
                  rw [← hk]
                  ring
                have hbd : ∀ᵐ z ∂Q, ‖f (M z)‖ ≤ C :=
                  Filter.Eventually.of_forall (fun z => by simpa [Real.norm_eq_abs] using hC _)
                have hfM : AEStronglyMeasurable (fun z => f (M z)) Q :=
                  (hf.comp (by fun_prop : Measurable M)).aestronglyMeasurable
                have hiq : Integrable (fun z => adjustedValue μ σ τ (M z)) Q := by
                  have := (integrable_const μ).add (((hi1.add hi2).sub (integrable_const μ)).mul_const k)
                  simpa [adjustedValue, hM, ← hk] using this
                have hiY : Integrable (fun z => Yp z - c) Q :=
                  ((hi1.const_mul _).sub (hi2.const_mul _)).sub (integrable_const c)
                simp_rw [hpt]
                rw [integral_add (hiq.bdd_mul hfM hbd) (hiY.bdd_mul hfM hbd)]
                have hfac : ∫ z, f (M z) * (Yp z - c) ∂Q = (∫ z, f (M z) ∂Q) * ∫ z, (Yp z - c) ∂Q :=
                  hYM.integral_comp_mul_comp (f := f) (g := fun y => y - c) (by fun_prop) (by fun_prop)
                    hf.aestronglyMeasurable (by fun_prop)
                have hE1 : ∫ z, z.1 ∂Q = μ := by
                  rw [integral_fun_fst (fun x : ℝ => x), integral_id_gaussianReal]; simp
                have hE2 : ∫ z, z.2 ∂Q = 0 := by
                  rw [integral_fun_snd (fun x : ℝ => x), integral_id_gaussianReal]; simp
                have hEY : ∫ z, (Yp z - c) ∂Q = 0 := by
                  simp only [hYp, hc]
                  rw [integral_sub (f := fun z : ℝ × ℝ => (1 - k) * z.1 - k * z.2)
                      ((hi1.const_mul _).sub (hi2.const_mul _)) (integrable_const _),
                    integral_sub (f := fun z : ℝ × ℝ => (1 - k) * z.1) (g := fun z : ℝ × ℝ => k * z.2)
                      (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
                    hE1, hE2]
                  simp
                rw [hfac, hEY, mul_zero, add_zero]
              have Pfub : ∀ {N : ℕ} (law : Fin N → Measure (ℝ × ℝ)) (hl : ∀ i, IsProbabilityMeasure (law i))
                  (i : Fin N) (A : (Fin N → ℝ × ℝ) → ℝ) (hA : Measurable A) (C : ℝ) (hC : ∀ ω, |A ω| ≤ C)
                  (u v : ℝ × ℝ → ℝ) (hu : Integrable u (law i)) (hv : Integrable v (law i))
                  (h : ∀ ω, ∫ x, A (Function.update ω i x) * u x ∂(law i) =
                    ∫ x, A (Function.update ω i x) * v x ∂(law i)),
                  ∫ ω, A ω * u (ω i) ∂(Measure.pi law) = ∫ ω, A ω * v (ω i) ∂(Measure.pi law) := by
                intro N law hl i A hA C hC u v hu hv h
                cases N with
                | zero => exact i.elim0
                | succ n =>
                  have hmp := measurePreserving_piFinSuccAbove law i
                  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ × ℝ) i with he
                  have hmps := hmp.symm e
                  have key : ∀ w : ℝ × ℝ → ℝ, Integrable w (law i) →
                      ∫ ω, A ω * w (ω i) ∂(Measure.pi law) =
                        ∫ y, ∫ x, A (Fin.insertNth i x y) * w x ∂(law i)
                          ∂(Measure.pi fun j => law (i.succAbove j)) := by
                    intro w hw
                    have hwi : Integrable (fun ω : Fin (n + 1) → ℝ × ℝ => w (ω i)) (Measure.pi law) :=
                      (measurePreserving_eval law i).integrable_comp_of_integrable hw
                    have hF : Integrable (fun ω : Fin (n + 1) → ℝ × ℝ => A ω * w (ω i)) (Measure.pi law) :=
                      hwi.bdd_mul hA.aestronglyMeasurable
                        (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hC ω)
                    rw [← hmps.integral_comp' (fun ω : Fin (n + 1) → ℝ × ℝ => A ω * w (ω i))]
                    have hF2 := (hmps.integrable_comp_emb e.symm.measurableEmbedding).2 hF
                    rw [integral_prod_symm (fun z => A (e.symm z) * w (e.symm z i)) hF2]
                    have hes : ∀ (x : ℝ × ℝ) (y : Fin n → ℝ × ℝ), e.symm (x, y) = Fin.insertNth i x y := by
                      intro x y
                      funext j
                      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
                    simp only [hes, Fin.insertNth_apply_same]
                  rw [key u hu, key v hv]
                  congr 1
                  funext y
                  have := h (Fin.insertNth i (0 : ℝ × ℝ) y)
                  simpa only [Fin.update_insertNth] using this
              have C1 : ∀ {N : ℕ} (S : SearchProblem N) (ρ : Policy N) (ω : Fin N → ℝ × ℝ),
                  netPayoff S ρ ω = ∑ i, ((if (run ρ ω).2 = Decision.launch i then (ω i).1 else 0) -
                    (if i ∈ (run ρ ω).1.map Prod.fst then S.cost i else 0)) := by
                intro N S ρ ω
                have hnd : ∀ k (h : History N), (h.map Prod.fst).Nodup →
                    ((runAux ρ ω k h).1.map Prod.fst).Nodup := by
                  intro k
                  induction k with
                  | zero => intro h hh; simpa [runAux] using hh
                  | succ k ih =>
                    intro h hh
                    simp only [runAux]
                    split
                    · split_ifs with hj
                      · exact hh
                      · apply ih
                        simp only [List.map_append, List.map_cons, List.map_nil]
                        exact List.Nodup.append hh (List.nodup_singleton _)
                          (by simpa [List.disjoint_singleton] using hj)
                    · split_ifs <;> exact hh
                    · exact hh
                have hN : ((run ρ ω).1.map Prod.fst).Nodup := hnd (N+1) [] (by simp)
                have hlv : ∀ d : Decision N, launchedValue ω d =
                    ∑ i, (if d = Decision.launch i then (ω i).1 else 0) := by
                  intro d
                  cases d with
                  | evaluate j => simp [launchedValue]
                  | launch j => simp [launchedValue]
                  | stopNone => simp [launchedValue]
                have hcost : ((run ρ ω).1.map (fun e => S.cost e.1)).sum =
                    ∑ i, (if i ∈ (run ρ ω).1.map Prod.fst then S.cost i else 0) := by
                  have e1 : (run ρ ω).1.map (fun e => S.cost e.1) =
                      ((run ρ ω).1.map Prod.fst).map S.cost := by simp [List.map_map, Function.comp_def]
                  rw [e1, ← List.sum_toFinset _ hN, ← Finset.sum_filter]
                  apply Finset.sum_congr _ (fun _ _ => rfl)
                  ext a; simp
                rw [Finset.sum_sub_distrib, ← hlv, ← hcost]
                rfl
              have C2 : ∀ {N : ℕ} (ρ : Policy N) (ω : Fin N → ℝ × ℝ) (i : Fin N) (x : ℝ × ℝ),
                  i ∈ (run ρ (Function.update ω i x)).1.map Prod.fst ↔ i ∈ (run ρ ω).1.map Prod.fst := by
                intro N ρ ω i x
                have hsub : ∀ (ω₀ : Fin N → ℝ × ℝ) k (h : History N), h ⊆ (runAux ρ ω₀ k h).1 := by
                  intro ω₀ k
                  induction k with
                  | zero => intro h; simp [runAux]
                  | succ k ih =>
                    intro h
                    simp only [runAux]
                    split
                    · split_ifs with hj
                      · exact List.Subset.refl _
                      · exact fun a ha => ih _ (List.mem_append_left _ ha)
                    · split_ifs <;> exact List.Subset.refl _
                    · exact List.Subset.refl _
                have key : ∀ k (h : History N), i ∉ h.map Prod.fst →
                    (i ∈ (runAux ρ (Function.update ω i x) k h).1.map Prod.fst ↔
                      i ∈ (runAux ρ ω k h).1.map Prod.fst) := by
                  intro k
                  induction k with
                  | zero => intro h _; simp [runAux]
                  | succ k ih =>
                    intro h hi
                    simp only [runAux]
                    split
                    · rename_i j _
                      by_cases hj : j ∈ h.map Prod.fst
                      · simp only [hj, if_true]
                      · simp only [hj, if_false]
                        by_cases hji : j = i
                        · subst hji
                          have m1 : ∀ (ω₀ : Fin N → ℝ × ℝ),
                              j ∈ (runAux ρ ω₀ k (h ++ [(j, (ω₀ j).2)])).1.map Prod.fst := by
                            intro ω₀
                            exact List.mem_map.2 ⟨(j, (ω₀ j).2), hsub ω₀ k _ (by simp), rfl⟩
                          exact ⟨fun _ => m1 ω, fun _ => m1 _⟩
                        · rw [Function.update_of_ne hji]
                          apply ih
                          simp [hi, Ne.symm hji]
                    · split_ifs <;> exact Iff.rfl
                    · exact Iff.rfl
                exact key (N+1) [] (by simp)
              have C3 : ∀ {N : ℕ} (ρ : Policy N) (ω ω' : Fin N → ℝ × ℝ) (h : ∀ j, (ω j).2 = (ω' j).2),
                  run ρ ω = run ρ ω' := by
                intro N ρ ω ω' h
                have key : ∀ k (h₀ : History N), runAux ρ ω k h₀ = runAux ρ ω' k h₀ := by
                  intro k
                  induction k with
                  | zero => intro h₀; simp [runAux]
                  | succ k ih =>
                    intro h₀
                    simp only [runAux]
                    split
                    · rename_i j _
                      rw [h j, ih]
                    · rfl
                    · rfl
                exact key (N+1) []
              have C4 : ∀ {N : ℕ} (ρ : Policy N) (ω : Fin N → ℝ × ℝ) (i : Fin N)
                  (h : (run ρ ω).2 = Decision.launch i), i ∈ (run ρ ω).1.map Prod.fst := by
                intro N ρ ω i h
                have key : ∀ k (h₀ : History N), (runAux ρ ω k h₀).2 = Decision.launch i →
                    i ∈ (runAux ρ ω k h₀).1.map Prod.fst := by
                  intro k
                  induction k with
                  | zero => intro h₀ hh; simp [runAux] at hh
                  | succ k ih =>
                    intro h₀ hh
                    simp only [runAux] at hh ⊢
                    split at hh
                    · rename_i j hj
                      split_ifs at hh ⊢ with hm
                      exact ih _ hh
                    · rename_i j hj
                      split_ifs at hh ⊢ with hm
                      · simp only [Decision.launch.injEq] at hh; subst hh; exact hm
                    · exact absurd hh (by simp)
                exact key (N+1) [] h
              have C5 : ∀ {N : ℕ} (ρ : Policy N)
                  (hE : ∀ (l : List (Fin N)) (d : Decision N),
                    MeasurableSet {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) = (l, d)})
                  (i : Fin N),
                  MeasurableSet {ω : Fin N → ℝ × ℝ | (run ρ ω).2 = Decision.launch i} ∧
                  MeasurableSet {ω : Fin N → ℝ × ℝ | i ∈ (run ρ ω).1.map Prod.fst} := by
                intro N ρ hE i
                have hL : ∀ l : List (Fin N),
                    MeasurableSet {ω : Fin N → ℝ × ℝ | (run ρ ω).1.map Prod.fst = l} := by
                  intro l
                  have e : {ω : Fin N → ℝ × ℝ | (run ρ ω).1.map Prod.fst = l} =
                      (⋃ j, {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) =
                        (l, Decision.evaluate j)}) ∪
                      (⋃ j, {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) =
                        (l, Decision.launch j)}) ∪
                      {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) = (l, Decision.stopNone)} := by
                    ext ω
                    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Prod.mk.injEq]
                    constructor
                    · intro hl
                      cases hd : (run ρ ω).2 with
                      | evaluate j => exact Or.inl (Or.inl ⟨j, hl, rfl⟩)
                      | launch j => exact Or.inl (Or.inr ⟨j, hl, rfl⟩)
                      | stopNone => exact Or.inr ⟨hl, rfl⟩
                    · rintro ((⟨j, hl, _⟩ | ⟨j, hl, _⟩) | ⟨hl, _⟩) <;> exact hl
                  rw [e]
                  exact ((MeasurableSet.iUnion fun j => hE l _).union
                    (MeasurableSet.iUnion fun j => hE l _)).union (hE l _)
                constructor
                · have e : {ω : Fin N → ℝ × ℝ | (run ρ ω).2 = Decision.launch i} =
                      ⋃ l : List (Fin N), {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) =
                        (l, Decision.launch i)} := by
                    ext ω
                    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Prod.mk.injEq]
                    exact ⟨fun hd => ⟨_, rfl, hd⟩, fun ⟨_, _, hd⟩ => hd⟩
                  rw [e]
                  exact MeasurableSet.iUnion fun l => hE l _
                · have e : {ω : Fin N → ℝ × ℝ | i ∈ (run ρ ω).1.map Prod.fst} =
                      ⋃ l : {l : List (Fin N) // i ∈ l},
                        {ω : Fin N → ℝ × ℝ | (run ρ ω).1.map Prod.fst = l.1} := by
                    ext ω
                    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
                    exact ⟨fun hm => ⟨⟨_, hm⟩, rfl⟩, fun ⟨l, hl⟩ => hl ▸ l.2⟩
                  rw [e]
                  exact MeasurableSet.iUnion fun l => hL l.1
              have W1 : ∀ {N : ℕ} (d : Decision N) (κ : Fin N → ℝ),
                  ∑ i, (if d = Decision.launch i then κ i else 0) ≤ Finset.univ.fold max 0 κ := by
                intro N d κ
                cases d with
                | evaluate j => simp; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
                | launch j =>
                  simp
                  exact (Finset.le_fold_max _).2 (Or.inr ⟨j, Finset.mem_univ _, le_rfl⟩)
                | stopNone => simp; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
              have W2 : ∀ {N : ℕ} (q : Fin N → ℝ → ℝ) (ord : Fin N ≃ Fin N) (R : Fin N → ℝ)
                  (hord : ∀ a b, a ≤ b → R (ord b) ≤ R (ord a)) (ω : Fin N → ℝ × ℝ),
                  ∑ i, ((if (run (fidelityPolicy q ord R) ω).2 = Decision.launch i then q i (ω i).2 else 0) -
                    (if i ∈ (run (fidelityPolicy q ord R) ω).1.map Prod.fst then max (q i (ω i).2 - R i) 0
                      else 0)) =
                    Finset.univ.fold max 0 (fun i => min (q i (ω i).2) (R i)) := by
                intro N q ord R hord ω
                classical
                set ρ := fidelityPolicy q ord R with hρ
                have hVBapp : ∀ (h : History N) (e : Fin N × ℝ), VB q (h ++ [e]) =
                    (if (VB q h).1 > q e.1 e.2 then VB q h else (q e.1 e.2, some e.1)) := by
                  intro h e
                  simp only [VB, List.foldl_append, List.foldl_cons, List.foldl_nil]
                  rfl
                have hVBinv : ∀ h : History N, 0 ≤ V q h ∧ (∀ e ∈ h, q e.1 e.2 ≤ V q h) ∧
                    (B q h = none → V q h = 0 ∧ ∀ e ∈ h, q e.1 e.2 < 0) ∧
                    (∀ b, B q h = some b → ∃ e ∈ h, e.1 = b ∧ V q h = q e.1 e.2) := by
                  intro h
                  induction h using List.reverseRecOn with
                  | nil => simp [V, B, VB]
                  | append_singleton l e ih =>
                    obtain ⟨ih0, ih1, ih2, ih3⟩ := ih
                    simp only [V, B] at ih0 ih1 ih2 ih3 ⊢
                    rw [hVBapp]
                    split_ifs with hlt
                    · refine ⟨ih0, ?_, ?_, ?_⟩
                      · intro x hx
                        rcases List.mem_append.1 hx with hx | hx
                        · exact ih1 x hx
                        · simp at hx; subst hx; exact le_of_lt hlt
                      · intro hn
                        obtain ⟨h0, h1⟩ := ih2 hn
                        refine ⟨h0, ?_⟩
                        intro x hx
                        rcases List.mem_append.1 hx with hx | hx
                        · exact h1 x hx
                        · simp at hx; subst hx; linarith
                      · intro b hb
                        obtain ⟨x, hx, h1, h2⟩ := ih3 b hb
                        exact ⟨x, List.mem_append_left _ hx, h1, h2⟩
                    · push Not at hlt
                      refine ⟨le_trans ih0 hlt, ?_, ?_, ?_⟩
                      · intro x hx
                        rcases List.mem_append.1 hx with hx | hx
                        · exact le_trans (ih1 x hx) hlt
                        · simp at hx; subst hx; exact le_refl _
                      · intro hn; simp at hn
                      · intro b hb
                        simp at hb
                        exact ⟨e, by simp, hb, rfl⟩
                set f : Fin N → Fin N × ℝ := fun a => (ord a, (ω (ord a)).2) with hf
                obtain ⟨hist, hh0, hhS⟩ : ∃ hist : ℕ → History N, hist 0 = [] ∧
                    ∀ k (hk : k < N), hist (k+1) = hist k ++ [f ⟨k, hk⟩] :=
                  ⟨fun n => Nat.rec [] (fun k acc => if hk : k < N then acc ++ [f ⟨k, hk⟩] else acc) n,
                    rfl, fun k hk => dif_pos hk⟩
                have hlen : ∀ n, n ≤ N → (hist n).length = n := by
                  intro n; induction n with
                  | zero => intro _; simp [hh0]
                  | succ k ih => intro hk; rw [hhS k (by omega)]; simp [ih (by omega)]
                have hmem : ∀ n, n ≤ N → ∀ e, e ∈ hist n ↔ ∃ a : Fin N, a.val < n ∧ e = f a := by
                  intro n; induction n with
                  | zero => intro _ e; simp [hh0]
                  | succ k ih =>
                    intro hk e
                    rw [hhS k (by omega), List.mem_append, ih (by omega), List.mem_singleton]
                    constructor
                    · rintro (⟨a, ha, rfl⟩ | rfl)
                      · exact ⟨a, by omega, rfl⟩
                      · exact ⟨⟨k, by omega⟩, by simp, rfl⟩
                    · rintro ⟨a, ha, rfl⟩
                      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | ha
                      · exact Or.inl ⟨a, ha, rfl⟩
                      · exact Or.inr (by rw [show a = ⟨k, by omega⟩ from Fin.ext ha])
                have hmemfst : ∀ n, n ≤ N → ∀ i, i ∈ (hist n).map Prod.fst ↔ (ord.symm i).val < n := by
                  intro n hn i
                  rw [List.mem_map]
                  constructor
                  · rintro ⟨e, he, rfl⟩
                    obtain ⟨a, ha, rfl⟩ := (hmem n hn e).1 he
                    simpa [hf] using ha
                  · intro h
                    exact ⟨f (ord.symm i), (hmem n hn _).2 ⟨_, h, rfl⟩, by simp [hf]⟩
                have hnext : ∀ h : History N, ρ.next h = if hn : h.length < N then
                    (if V q h < R (ord ⟨h.length, hn⟩) then Decision.evaluate (ord ⟨h.length, hn⟩)
                      else stopDecision (B q h)) else stopDecision (B q h) := fun h => rfl
                have hstopRun : ∀ k (h : History N), ρ.next h = stopDecision (B q h) →
                    runAux ρ ω (k+1) h = (h, stopDecision (B q h)) := by
                  intro k h hn
                  rw [runAux.eq_2, hn]
                  rcases hB : B q h with _ | b
                  · simp [stopDecision]
                  · obtain ⟨e, he, h1, -⟩ := (hVBinv h).2.2.2 b hB
                    have : b ∈ h.map Prod.fst := List.mem_map.2 ⟨e, he, h1⟩
                    simp [stopDecision, this]
                have hrunAux : ∀ m n, n + m = N → ∃ n', n ≤ n' ∧ n' ≤ N ∧
                    runAux ρ ω (m+1) (hist n) = (hist n', stopDecision (B q (hist n'))) ∧
                    (∀ k : Fin N, n ≤ k.val → k.val < n' → V q (hist k) < R (ord k)) ∧
                    (∀ hn : n' < N, R (ord ⟨n', hn⟩) ≤ V q (hist n')) := by
                  intro m
                  induction m with
                  | zero =>
                    intro n hn
                    refine ⟨n, le_rfl, by omega, ?_, fun k h1 h2 => by omega, fun h => by omega⟩
                    apply hstopRun
                    rw [hnext, dif_neg (by rw [hlen n (by omega)]; omega)]
                  | succ m ih =>
                    intro n hn
                    have hl := hlen n (by omega)
                    have hnN : n < N := by omega
                    have h1 : (hist n).length < N := by omega
                    have hfin : (⟨(hist n).length, h1⟩ : Fin N) = ⟨n, hnN⟩ := Fin.ext hl
                    by_cases hc : V q (hist n) < R (ord ⟨n, hnN⟩)
                    · have hnx : ρ.next (hist n) = Decision.evaluate (ord ⟨n, hnN⟩) := by
                        rw [hnext, dif_pos h1, hfin, if_pos hc]
                      have hnm : ord ⟨n, hnN⟩ ∉ (hist n).map Prod.fst := by
                        rw [hmemfst n (by omega)]; simp
                      have hstep : runAux ρ ω (m+1+1) (hist n) = runAux ρ ω (m+1) (hist (n+1)) := by
                        rw [runAux.eq_2, hnx]
                        simp only [hnm, if_false]
                        rw [hhS n hnN]
                      obtain ⟨n', h2, h3, h4, h5, h6⟩ := ih (n+1) (by omega)
                      refine ⟨n', by omega, h3, hstep.trans h4, ?_, h6⟩
                      intro k hk1 hk2
                      rcases Nat.lt_or_ge n k.val with hk | hk
                      · exact h5 k hk hk2
                      · have : k = ⟨n, hnN⟩ := Fin.ext (by simp only; omega)
                        subst this
                        exact hc
                    · have hnx : ρ.next (hist n) = stopDecision (B q (hist n)) := by
                        rw [hnext, dif_pos h1, hfin, if_neg hc]
                      refine ⟨n, le_rfl, by omega, hstopRun _ _ hnx, fun k h1 h2 => by omega, ?_⟩
                      intro h
                      push Not at hc
                      exact hc
                obtain ⟨n, -, hnN, hrun, hcont0, hstop⟩ := hrunAux N 0 (by omega)
                have hcont : ∀ k : Fin N, k.val < n → V q (hist k) < R (ord k) :=
                  fun k hk => hcont0 k (Nat.zero_le _) hk
                have hrun' : run ρ ω = (hist n, stopDecision (B q (hist n))) := by
                  simp only [run]; rw [← hh0]; exact hrun
                rw [hrun']
                simp only
                have hVn := hVBinv (hist n)
                have hVk : ∀ k, k ≤ N → ∀ a : Fin N, a.val < k → q (ord a) (ω (ord a)).2 ≤ V q (hist k) :=
                  fun k hk a ha => (hVBinv (hist k)).2.1 (f a) ((hmem k hk _).2 ⟨a, ha, rfl⟩)
                have hF1 : ∀ a : Fin N, a.val < n → stopDecision (B q (hist n)) ≠ Decision.launch (ord a) →
                    q (ord a) (ω (ord a)).2 ≤ R (ord a) := by
                  intro a ha hne
                  by_contra hgt
                  push Not at hgt
                  by_cases ha1 : a.val + 1 < n
                  · have h1 := hcont ⟨a.val+1, by omega⟩ ha1
                    have h2 : R (ord ⟨a.val+1, by omega⟩) ≤ R (ord a) :=
                      hord _ _ (by rw [Fin.le_def]; simp)
                    have h3 := hVk (a.val+1) (by omega) a (by omega)
                    simp only at h1
                    linarith
                  · have hna : n = a.val + 1 := by omega
                    have hha : hist n = hist a ++ [f a] := by rw [hna, hhS a.val a.isLt]
                    have hlt := hcont a ha
                    apply hne
                    have : B q (hist n) = some (ord a) := by
                      simp only [B]; rw [hha, hVBapp]; rw [if_neg]
                      simp only [V] at hlt
                      show ¬ ((VB q (hist a)).1 > q (ord a) (ω (ord a)).2)
                      linarith
                    rw [this]; rfl
                have hterm : ∀ i, ((if stopDecision (B q (hist n)) = Decision.launch i then q i (ω i).2 else 0) -
                    (if i ∈ (hist n).map Prod.fst then max (q i (ω i).2 - R i) 0 else 0)) =
                    (if stopDecision (B q (hist n)) = Decision.launch i then min (q i (ω i).2) (R i) else 0) := by
                  intro i
                  by_cases hd : stopDecision (B q (hist n)) = Decision.launch i
                  · have hi : i ∈ (hist n).map Prod.fst := by
                      rcases hB : B q (hist n) with _ | b
                      · rw [hB] at hd; simp [stopDecision] at hd
                      · rw [hB] at hd; simp [stopDecision] at hd; subst hd
                        obtain ⟨e, he, h1, -⟩ := hVn.2.2.2 _ hB
                        exact List.mem_map.2 ⟨e, he, h1⟩
                    rw [if_pos hd, if_pos hi, if_pos hd]
                    rcases le_total (q i (ω i).2) (R i) with h | h
                    · rw [max_eq_right (by linarith), min_eq_left h]; ring
                    · rw [max_eq_left (by linarith), min_eq_right h]; ring
                  · rw [if_neg hd, if_neg hd]
                    split_ifs with hi
                    · have ha : (ord.symm i).val < n := (hmemfst n hnN i).1 hi
                      have := hF1 (ord.symm i) ha (by simpa using hd)
                      simp only [Equiv.apply_symm_apply] at this
                      rw [max_eq_right (by linarith)]; ring
                    · ring
                rw [Finset.sum_congr rfl (fun i _ => hterm i)]
                rcases hB : B q (hist n) with _ | b
                · obtain ⟨hV0, hneg⟩ := hVn.2.2.1 hB
                  simp only [stopDecision, reduceCtorEq, if_false, Finset.sum_const_zero]
                  apply le_antisymm
                  · exact (Finset.le_fold_max _).2 (Or.inl le_rfl)
                  · refine (Finset.fold_max_le _).2 ⟨le_rfl, ?_⟩
                    intro i _
                    obtain ⟨c, rfl⟩ := ord.surjective i
                    by_cases hc : c.val < n
                    · have := hneg (f c) ((hmem n hnN _).2 ⟨c, hc, rfl⟩)
                      exact (min_le_left _ _).trans this.le
                    · have hn' : n < N := by omega
                      have h2 : R (ord c) ≤ R (ord ⟨n, hn'⟩) := hord _ _ (by rw [Fin.le_def]; simp; omega)
                      have h3 := hstop hn'
                      exact (min_le_right _ _).trans (by linarith)
                · obtain ⟨e, he, h1, hVe⟩ := hVn.2.2.2 b hB
                  obtain ⟨a, ha, rfl⟩ := (hmem n hnN e).1 he
                  simp only [hf] at h1 hVe
                  subst h1
                  simp only [stopDecision, Decision.launch.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
                  apply le_antisymm
                  · exact (Finset.le_fold_max _).2 (Or.inr ⟨ord a, Finset.mem_univ _, le_rfl⟩)
                  · refine (Finset.fold_max_le _).2 ⟨?_, ?_⟩
                    · exact le_min (hVe ▸ hVn.1) (le_of_lt (lt_of_le_of_lt (hVBinv (hist a)).1 (hcont a ha)))
                    · intro i _
                      obtain ⟨c, rfl⟩ := ord.surjective i
                      by_cases hXb : q (ord a) (ω (ord a)).2 ≤ R (ord a)
                      · rw [min_eq_left hXb]
                        by_cases hc : c.val < n
                        · exact (min_le_left _ _).trans ((hVk n hnN c hc).trans hVe.le)
                        · have hn' : n < N := by omega
                          have h2 : R (ord c) ≤ R (ord ⟨n, hn'⟩) := hord _ _ (by rw [Fin.le_def]; simp; omega)
                          have h3 := hstop hn'
                          exact (min_le_right _ _).trans (by linarith)
                      · push Not at hXb
                        rw [min_eq_right hXb.le]
                        by_cases hc : c.val < a.val
                        · have h2 := hVk a.val (by omega) c hc
                          have h3 := hcont a ha
                          exact (min_le_left _ _).trans (by linarith)
                        · exact (min_le_right _ _).trans (hord _ _ (by rw [Fin.le_def]; omega))
              have E : ∀ {N : ℕ} (q : Fin N → ℝ → ℝ) (hq : ∀ i, Measurable (q i)) (ord : Fin N ≃ Fin N)
                  (R : Fin N → ℝ) (l : List (Fin N)) (d : Decision N),
                  MeasurableSet {ω : Fin N → ℝ × ℝ | ((run (fidelityPolicy q ord R) ω).1.map Prod.fst,
                    (run (fidelityPolicy q ord R) ω).2) = (l, d)} := by
                intro N q hq ord R l d
                classical
                have hmj : ∀ j : Fin N, Measurable (fun ω : Fin N → ℝ × ℝ => q j (ω j).2) := fun j =>
                  (hq j).comp (measurable_pi_apply j).snd
                have hfold : ∀ (l0 : List (Fin N)) (f : (Fin N → ℝ × ℝ) → ℝ × Option (Fin N)),
                    Measurable (fun ω => (f ω).1) → (∀ b, MeasurableSet {ω | (f ω).2 = b}) →
                    Measurable (fun ω => ((l0.map (fun j => (j, (ω j).2))).foldl
                      (fun vb e => if vb.1 > q e.1 e.2 then vb else (q e.1 e.2, some e.1)) (f ω)).1) ∧
                    ∀ b, MeasurableSet {ω | ((l0.map (fun j => (j, (ω j).2))).foldl
                      (fun vb e => if vb.1 > q e.1 e.2 then vb else (q e.1 e.2, some e.1)) (f ω)).2 = b} := by
                  intro l0
                  induction l0 with
                  | nil => intro f h1 h2; exact ⟨h1, h2⟩
                  | cons j l ih =>
                    intro f h1 h2
                    have hm : MeasurableSet {ω | (f ω).1 > q j (ω j).2} := measurableSet_lt (hmj j) h1
                    have := ih (fun ω => if (f ω).1 > q j (ω j).2 then f ω else (q j (ω j).2, some j)) ?_ ?_
                    · simpa using this
                    · have e : (fun ω => (if (f ω).1 > q j (ω j).2 then f ω else (q j (ω j).2, some j)).1) =
                          fun ω => if (f ω).1 > q j (ω j).2 then (f ω).1 else q j (ω j).2 := by
                        funext ω; split_ifs <;> rfl
                      rw [e]
                      exact Measurable.ite hm h1 (hmj j)
                    · intro b
                      have e : {ω | (if (f ω).1 > q j (ω j).2 then f ω else (q j (ω j).2, some j)).2 = b} =
                          ({ω | (f ω).1 > q j (ω j).2} ∩ {ω | (f ω).2 = b}) ∪
                            ({ω | (f ω).1 > q j (ω j).2}ᶜ ∩ {_ω | some j = b}) := by
                        ext ω
                        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
                        split_ifs with hc <;> simp [hc]
                      rw [e]
                      exact (hm.inter (h2 b)).union (hm.compl.inter (MeasurableSet.const _))
                have hV : ∀ l0 : List (Fin N),
                    Measurable (fun ω : Fin N → ℝ × ℝ => V q (l0.map (fun j => (j, (ω j).2)))) := fun l0 =>
                  (hfold l0 (fun _ => (0, none)) measurable_const (fun _ => MeasurableSet.const _)).1
                have hB : ∀ (l0 : List (Fin N)) b,
                    MeasurableSet {ω : Fin N → ℝ × ℝ | B q (l0.map (fun j => (j, (ω j).2))) = b} := fun l0 =>
                  (hfold l0 (fun _ => (0, none)) measurable_const (fun _ => MeasurableSet.const _)).2
                have hBP : ∀ (l0 : List (Fin N)) (P : Option (Fin N) → Prop),
                    MeasurableSet {ω : Fin N → ℝ × ℝ | P (B q (l0.map (fun j => (j, (ω j).2))))} := by
                  intro l0 P
                  have e : {ω : Fin N → ℝ × ℝ | P (B q (l0.map (fun j => (j, (ω j).2))))} =
                      ⋃ b : Option (Fin N), ({ω | B q (l0.map (fun j => (j, (ω j).2))) = b} ∩ {_ω | P b}) := by
                    ext ω; simp
                  rw [e]
                  exact MeasurableSet.iUnion fun b => (hB l0 b).inter (MeasurableSet.const _)
                have hfst : ∀ (l0 : List (Fin N)) (ω : Fin N → ℝ × ℝ),
                    (l0.map (fun j => (j, (ω j).2))).map Prod.fst = l0 := by
                  intro l0 ω; induction l0 with
                  | nil => rfl
                  | cons a t ih => simp only [List.map_cons, ih]
                have hmain : ∀ (k : ℕ) (l0 : List (Fin N)) (l : List (Fin N)) (d : Decision N),
                    MeasurableSet {ω : Fin N → ℝ × ℝ |
                      ((runAux (fidelityPolicy q ord R) ω k (l0.map (fun j => (j, (ω j).2)))).1.map Prod.fst,
                        (runAux (fidelityPolicy q ord R) ω k (l0.map (fun j => (j, (ω j).2)))).2) = (l, d)} := by
                  intro k
                  induction k with
                  | zero =>
                    intro l0 l d
                    simp only [runAux, hfst]
                    exact MeasurableSet.const _
                  | succ k ih =>
                    intro l0 l d
                    let P : Option (Fin N) → Prop := fun b =>
                      (l0, (match b with
                        | some b => if b ∈ l0 then Decision.launch b else Decision.stopNone
                        | none => Decision.stopNone)) = (l, d)
                    by_cases hn : l0.length < N
                    · set j := ord ⟨l0.length, hn⟩ with hj
                      have hA : MeasurableSet {ω : Fin N → ℝ × ℝ | V q (l0.map (fun j => (j, (ω j).2))) < R j} :=
                        measurableSet_lt (hV l0) measurable_const
                      let T1 : Set (Fin N → ℝ × ℝ) := if j ∈ l0 then {_ω | (l0, Decision.stopNone) = (l, d)} else
                        {ω | ((runAux (fidelityPolicy q ord R) ω k ((l0 ++ [j]).map (fun j => (j, (ω j).2)))).1.map Prod.fst,
                          (runAux (fidelityPolicy q ord R) ω k ((l0 ++ [j]).map (fun j => (j, (ω j).2)))).2) = (l, d)}
                      have hT1 : MeasurableSet T1 := by
                        simp only [T1]; split_ifs
                        · exact MeasurableSet.const _
                        · exact ih _ l d
                      have e : {ω : Fin N → ℝ × ℝ |
                          ((runAux (fidelityPolicy q ord R) ω (k+1) (l0.map (fun j => (j, (ω j).2)))).1.map Prod.fst,
                          (runAux (fidelityPolicy q ord R) ω (k+1) (l0.map (fun j => (j, (ω j).2)))).2) = (l, d)} =
                          ({ω : Fin N → ℝ × ℝ | V q (l0.map (fun j => (j, (ω j).2))) < R j} ∩ T1) ∪
                          ({ω : Fin N → ℝ × ℝ | V q (l0.map (fun j => (j, (ω j).2))) < R j}ᶜ ∩
                            {ω : Fin N → ℝ × ℝ | P (B q (l0.map (fun j => (j, (ω j).2))))}) := by
                        ext ω
                        by_cases hv : V q (l0.map (fun j => (j, (ω j).2))) < R j
                        · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, hv,
                            true_and, not_true_eq_false, false_and, or_false]
                          have hnx : (fidelityPolicy q ord R).next (l0.map (fun j => (j, (ω j).2))) =
                              Decision.evaluate j := by
                            simp only [fidelityPolicy, List.length_map, dif_pos hn, ← hj, if_pos hv]
                          rw [runAux, hnx]
                          simp only [T1, hfst]
                          by_cases hjl : j ∈ l0
                          · simp only [hjl, if_true, hfst, Set.mem_ofPred_eq]
                          · simp only [hjl, if_false, List.map_append, List.map_cons, List.map_nil,
                              Set.mem_ofPred_eq]
                        · simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, hv,
                            false_and, not_false_eq_true, true_and, false_or]
                          have hnx : (fidelityPolicy q ord R).next (l0.map (fun j => (j, (ω j).2))) =
                              stopDecision (B q (l0.map (fun j => (j, (ω j).2)))) := by
                            simp only [fidelityPolicy, List.length_map, dif_pos hn, ← hj, if_neg hv]
                          rw [runAux, hnx]
                          rcases hb : B q (l0.map (fun j => (j, (ω j).2))) with _ | b
                          · simp [stopDecision, P, hfst]
                          · by_cases hbl : b ∈ l0
                            · simp [stopDecision, P, hfst, hbl]
                            · simp [stopDecision, P, hfst, hbl]
                      rw [e]
                      exact (hA.inter hT1).union (hA.compl.inter (hBP l0 P))
                    · have e : {ω : Fin N → ℝ × ℝ |
                          ((runAux (fidelityPolicy q ord R) ω (k+1) (l0.map (fun j => (j, (ω j).2)))).1.map Prod.fst,
                          (runAux (fidelityPolicy q ord R) ω (k+1) (l0.map (fun j => (j, (ω j).2)))).2) = (l, d)} =
                          {ω : Fin N → ℝ × ℝ | P (B q (l0.map (fun j => (j, (ω j).2))))} := by
                        ext ω
                        simp only [Set.mem_ofPred_eq]
                        have hnx : (fidelityPolicy q ord R).next (l0.map (fun j => (j, (ω j).2))) =
                            stopDecision (B q (l0.map (fun j => (j, (ω j).2)))) := by
                          simp only [fidelityPolicy, List.length_map, dif_neg hn]
                        rw [runAux, hnx]
                        rcases hb : B q (l0.map (fun j => (j, (ω j).2))) with _ | b
                        · simp [stopDecision, P, hfst]
                        · by_cases hbl : b ∈ l0
                          · simp [stopDecision, P, hfst, hbl]
                          · simp [stopDecision, P, hfst, hbl]
                      rw [e]
                      exact hBP l0 P
                exact hmain (N + 1) [] l d
              -- assembly
              set S := gaussianProblem μ σ τ w with hS
              set q : Fin N → ℝ → ℝ := fun i m => adjustedValue (μ i) (σ i) (τ i) m with hq
              set Rf : Fin N → ℝ := fun i => gaussianIndex Rstd (μ i) (σ i) (τ i) (w i) with hRf
              set π := fidelityPolicy q ord Rf with hπ
              have hlaw : ∀ i, S.law i = gaussianLaw (μ i) (σ i) (τ i) := fun i => rfl
              have hprob : ∀ i, IsProbabilityMeasure (S.law i) := fun i => (G0 _ _ _).1
              have hprob' : ∀ i, IsProbabilityMeasure (gaussianLaw (μ i) (σ i) (τ i)) := fun i => (G0 _ _ _).1
              have hqmeas : ∀ i, Measurable (q i) := by
                intro i
                simp only [hq, adjustedValue]
                fun_prop
              have hint1 : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (S.law i) := fun i => (G0 _ _ _).2.1
              have hint2 : ∀ i, Integrable (fun z : ℝ × ℝ => q i z.2) (S.law i) := by
                intro i
                have h2 := (G0 (μ i) (σ i) (τ i)).2.2
                have : (fun z : ℝ × ℝ => q i z.2) = fun z => μ i + (z.2 - μ i) *
                    (1 / (1 + (invFidelity (τ i) / σ i) ^ 2)) := rfl
                rw [this, hlaw]
                exact (integrable_const _).add ((h2.sub (integrable_const _)).mul_const _)
              have hint3 : ∀ i, Integrable (fun z : ℝ × ℝ => max (q i z.2 - Rf i) 0) (S.law i) := by
                intro i
                exact ((hint2 i).sub (integrable_const _)).sup (integrable_const _)
              have hevalint : ∀ i (g : ℝ × ℝ → ℝ), Integrable g (S.law i) →
                  Integrable (fun ω : Fin N → ℝ × ℝ => g (ω i)) S.outcomeLaw := by
                intro i g hg
                have hmp := @measurePreserving_eval _ _ _ _ S.law hprob i
                exact (hmp.integrable_comp hg.aestronglyMeasurable).2 hg
              -- Φ
              let Φ : Policy N → (Fin N → ℝ × ℝ) → ℝ := fun ρ ω =>
                ∑ i, ((if (run ρ ω).2 = Decision.launch i then q i (ω i).2 else 0) -
                  (if i ∈ (run ρ ω).1.map Prod.fst then max (q i (ω i).2 - Rf i) 0 else 0))
              have VAL : ∀ ρ : Policy N, (∀ (l : List (Fin N)) (d : Decision N),
                    MeasurableSet {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) = (l, d)}) →
                  Integrable (netPayoff S ρ) S.outcomeLaw ∧ Integrable (Φ ρ) S.outcomeLaw ∧
                    value S ρ = ∫ ω, Φ ρ ω ∂S.outcomeLaw := by
                intro ρ hE
                let a : Fin N → (Fin N → ℝ × ℝ) → ℝ := fun i ω =>
                  if (run ρ ω).2 = Decision.launch i then 1 else 0
                let b : Fin N → (Fin N → ℝ × ℝ) → ℝ := fun i ω =>
                  if i ∈ (run ρ ω).1.map Prod.fst then 1 else 0
                have ha : ∀ i, Measurable (a i) := fun i =>
                  Measurable.ite (C5 ρ hE i).1 measurable_const measurable_const
                have hb : ∀ i, Measurable (b i) := fun i =>
                  Measurable.ite (C5 ρ hE i).2 measurable_const measurable_const
                have ha1 : ∀ i ω, |a i ω| ≤ 1 := by
                  intro i ω; simp only [a]; split_ifs <;> simp
                have hb1 : ∀ i ω, |b i ω| ≤ 1 := by
                  intro i ω; simp only [b]; split_ifs <;> simp
                have hbint : ∀ i (g : ℝ × ℝ → ℝ), Integrable g (S.law i) →
                    Integrable (fun ω => b i ω * g (ω i)) S.outcomeLaw := by
                  intro i g hg
                  refine (hevalint i g hg).bdd_mul (hb i).aestronglyMeasurable (c := 1) ?_
                  exact Filter.Eventually.of_forall (fun ω => by simpa using hb1 i ω)
                have haint : ∀ i (g : ℝ × ℝ → ℝ), Integrable g (S.law i) →
                    Integrable (fun ω => a i ω * g (ω i)) S.outcomeLaw := by
                  intro i g hg
                  refine (hevalint i g hg).bdd_mul (ha i).aestronglyMeasurable (c := 1) ?_
                  exact Filter.Eventually.of_forall (fun ω => by simpa using ha1 i ω)
                have hnet : netPayoff S ρ = fun ω => ∑ i, (a i ω * (ω i).1 - b i ω * w i) := by
                  funext ω
                  rw [C1]
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  simp only [a, b]
                  split_ifs <;> simp [hS, gaussianProblem]
                have hΦ : Φ ρ = fun ω => ∑ i, (a i ω * q i (ω i).2 - b i ω * max (q i (ω i).2 - Rf i) 0) := by
                  funext ω
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  simp only [a, b]
                  split_ifs <;> simp
                have hI1 : ∀ i, Integrable (fun ω => a i ω * (ω i).1) S.outcomeLaw := fun i =>
                  haint i _ (hint1 i)
                have hI2 : ∀ i, Integrable (fun ω => b i ω * w i) S.outcomeLaw := fun i =>
                  hbint i (fun _ => w i) (integrable_const _)
                have hI3 : ∀ i, Integrable (fun ω => a i ω * q i (ω i).2) S.outcomeLaw := fun i =>
                  haint i _ (hint2 i)
                have hI4 : ∀ i, Integrable (fun ω => b i ω * max (q i (ω i).2 - Rf i) 0) S.outcomeLaw :=
                  fun i => hbint i _ (hint3 i)
                have hNint : Integrable (netPayoff S ρ) S.outcomeLaw := by
                  rw [hnet]
                  exact integrable_finset_sum _ (fun i _ => (hI1 i).sub (hI2 i))
                have hΦint : Integrable (Φ ρ) S.outcomeLaw := by
                  rw [hΦ]
                  exact integrable_finset_sum _ (fun i _ => (hI3 i).sub (hI4 i))
                refine ⟨hNint, hΦint, ?_⟩
                have hA : ∀ i, ∫ ω, a i ω * (ω i).1 ∂S.outcomeLaw = ∫ ω, a i ω * q i (ω i).2 ∂S.outcomeLaw := by
                  intro i
                  refine Pfub S.law hprob i (a i) (ha i) 1 (ha1 i) (fun z => z.1) (fun z => q i z.2)
                    (hint1 i) (hint2 i) ?_
                  intro ω
                  let f : ℝ → ℝ := fun m => a i (Function.update ω i (0, m))
                  have hfa : ∀ x : ℝ × ℝ, a i (Function.update ω i x) = f x.2 := by
                    intro x
                    simp only [f, a]
                    rw [C3 ρ (Function.update ω i x) (Function.update ω i (0, x.2))]
                    intro j
                    by_cases hj : j = i
                    · subst hj; simp
                    · simp [Function.update_of_ne hj]
                  have hfm : Measurable f := by
                    have : Measurable (fun m : ℝ => Function.update ω i ((0 : ℝ), m)) :=
                      (measurable_update ω).comp (measurable_const.prodMk measurable_id)
                    exact (ha i).comp this
                  simp_rw [hfa]
                  rw [hlaw]
                  exact G2 (μ i) (σ i) (τ i) (hσ i) f hfm 1 (fun x => ha1 i _)
                have hB : ∀ i, ∫ ω, b i ω * w i ∂S.outcomeLaw =
                    ∫ ω, b i ω * max (q i (ω i).2 - Rf i) 0 ∂S.outcomeLaw := by
                  intro i
                  refine Pfub S.law hprob i (b i) (hb i) 1 (hb1 i) (fun _ => w i)
                    (fun z => max (q i z.2 - Rf i) 0) (integrable_const _) (hint3 i) ?_
                  intro ω
                  have hc : ∀ x : ℝ × ℝ, b i (Function.update ω i x) = b i ω := by
                    intro x
                    simp only [b]
                    rw [if_congr (C2 ρ ω i x) rfl rfl]
                  simp_rw [hc]
                  rw [integral_const_mul, integral_const_mul, hlaw]
                  congr 1
                  rw [G1 (μ i) (σ i) (τ i) (w i) (hσ i) (hτ i) (hw i) Rstd hRstd]
                  simp
                unfold value
                rw [hnet, hΦ]
                simp only []
                rw [integral_finset_sum (f := fun i ω => a i ω * (ω i).1 - b i ω * w i) _
                    (fun i _ => (hI1 i).sub (hI2 i)),
                  integral_finset_sum (f := fun i ω => a i ω * q i (ω i).2 - b i ω * max (q i (ω i).2 - Rf i) 0) _
                    (fun i _ => (hI3 i).sub (hI4 i))]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [integral_sub (hI1 i) (hI2 i), integral_sub (hI3 i) (hI4 i), hA i, hB i]
              have hEπ := E q hqmeas ord Rf
              obtain ⟨hπN, hπΦ, hπV⟩ := VAL π hEπ
              have hordR : ∀ a b, a ≤ b → Rf (ord b) ≤ Rf (ord a) := hord
              refine ⟨⟨hEπ, hπN⟩, ?_⟩
              intro ρ hρ
              obtain ⟨hρN, hρΦ, hρV⟩ := VAL ρ hρ.1
              rw [hρV, hπV]
              refine integral_mono hρΦ hπΦ (fun ω => ?_)
              show Φ ρ ω ≤ Φ π ω
              have h2 : Φ π ω = Finset.univ.fold max 0 (fun i => min (q i (ω i).2) (Rf i)) :=
                W2 q ord Rf hordR ω
              rw [h2]
              refine le_trans ?_ (W1 (run ρ ω).2 (fun i => min (q i (ω i).2) (Rf i)))
              refine Finset.sum_le_sum (fun i _ => ?_)
              by_cases hl : (run ρ ω).2 = Decision.launch i
              · have hm := C4 ρ ω i hl
                rw [if_pos hl, if_pos hm, if_pos hl]
                rcases le_total (q i (ω i).2) (Rf i) with h | h
                · rw [min_eq_left h, max_eq_right (by linarith)]; simp
                · rw [min_eq_right h, max_eq_left (by linarith)]; linarith
              · rw [if_neg hl, if_neg hl]
                split_ifs <;> simp
