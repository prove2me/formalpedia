-- Prove2me | solution 1 for IsodiamVar.Simplex.Supplement.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:02.548156+00:00
-- url     : https://prove2.me/submissions/c5de778e-8a66-46f0-8561-6b1e17fff2d0

import Definitions.Def_IsodiamVar_Simplex_Supplement_Legendre
import Definitions.Def_IsodiamVar_Simplex_Supplement_Variance

open MeasureTheory

open IsodiamVar
open IsodiamVar.Simplex
open IsodiamVar.Simplex.Supplement

/-- Theorem 1.1(a),(b), p. 3. No interior assumption on the bound or global optimization.
Sphere means the distance level set, also at radius zero. -/
theorem solution {n : ℕ} (K : Set (E n)) (hK : IsCompact K)
    (μ : Measure (E n)) (hμ : InP K μ) :
    ((variance μ : EReal) ≤
      ((-(‖barycenter μ‖ ^ 2) : ℝ) : EReal) - phiBiconjugate K (barycenter μ)) ∧
    (barycenter μ ∈ interior (closedConvexHull ℝ K) →
      (((variance μ : EReal) =
          ((-(‖barycenter μ‖ ^ 2) : ℝ) : EReal) - phiBiconjugate K (barycenter μ)) ↔
        ∃ q : E n, ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
          μ (K ∩ Metric.sphere q R) = 1)) ∧
    (((∀ ν : Measure (E n), InP K ν → variance ν ≤ variance μ) ↔
      ∃ q : E n, ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
        (∀ c : E n, ∀ r : ℝ, 0 ≤ r → K ⊆ Metric.closedBall c r → R ≤ r) ∧
        μ (K ∩ Metric.sphere q R) = 1 ∧ barycenter μ = q)) ∧
    (∀ q : E n, ∀ R : ℝ, 0 ≤ R → K ⊆ Metric.closedBall q R →
      (∀ c : E n, ∀ r : ℝ, 0 ≤ r → K ⊆ Metric.closedBall c r → R ≤ r) →
      (∀ ν : Measure (E n), InP K ν → variance ν ≤ variance μ) → variance μ = R ^ 2) := by
        classical
        letI : IsProbabilityMeasure μ := hμ.1
        have hAE : ∀ (ν : Measure (E n)), InP K ν → ∀ᵐ x ∂ν, x ∈ K := by
          intro ν hν
          exact (ae_iff).2 hν.2
        have hId : ∀ (ν : Measure (E n)), InP K ν → Integrable (fun x : E n => x) ν := by
          intro ν hν
          letI : IsProbabilityMeasure ν := hν.1
          have hi := continuous_id.continuousOn.integrableOn_compact (μ := ν) hK
          rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (hAE ν hν)] at hi
        have hInt : ∀ (ν : Measure (E n)), InP K ν → ∀ f : E n → ℝ,
            Continuous f → Integrable f ν := by
          intro ν hν f hf
          letI : IsProbabilityMeasure ν := hν.1
          have hi := hf.continuousOn.integrableOn_compact (μ := ν) hK
          rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (hAE ν hν)] at hi
        have hVar : ∀ (ν : Measure (E n)), InP K ν →
            variance ν = (∫ x, ‖x‖ ^ 2 ∂ν) - ‖barycenter ν‖ ^ 2 := by
          intro ν hν
          letI : IsProbabilityMeasure ν := hν.1
          unfold variance
          simp_rw [norm_sub_sq_real]
          rw [integral_add, integral_sub, integral_const, integral_const_mul]
          · simp_rw [show ∀ x : E n, inner ℝ x (barycenter ν) = inner ℝ (barycenter ν) x from fun x => real_inner_comm _ _]
            rw [integral_inner (hId ν hν)]
            simp [barycenter, real_inner_self_eq_norm_sq]
            <;> ring
          all_goals first | apply hInt ν hν <;> fun_prop | exact integrable_const _
        have hVarNonneg : ∀ (ν : Measure (E n)), 0 ≤ variance ν := by
          intro ν
          exact integral_nonneg fun x => sq_nonneg _
        have hMoment : ∀ (ν : Measure (E n)), InP K ν → ∀ q : E n,
            (∫ x, ‖x - q‖ ^ 2 ∂ν) = variance ν + ‖barycenter ν - q‖ ^ 2 := by
          intro ν hν q
          letI : IsProbabilityMeasure ν := hν.1
          simp_rw [norm_sub_sq_real]
          rw [integral_add, integral_sub, integral_const_mul]
          · simp_rw [show ∀ x : E n, inner ℝ x q = inner ℝ q x from fun x => real_inner_comm _ _]
            rw [integral_inner (hId ν hν), integral_const, hVar ν hν]
            simp [barycenter]
            <;> ring
          all_goals first | apply hInt ν hν <;> fun_prop | exact integrable_const _
        have hBallBound : ∀ (ν : Measure (E n)), InP K ν → ∀ q : E n, ∀ R : ℝ,
            0 ≤ R → K ⊆ Metric.closedBall q R →
            variance ν + ‖barycenter ν - q‖ ^ 2 ≤ R ^ 2 := by
          intro ν hν q R hR hB
          letI : IsProbabilityMeasure ν := hν.1
          rw [← hMoment ν hν q]
          calc
            _ ≤ ∫ _ : E n, R ^ 2 ∂ν := by
              apply integral_mono_ae (hInt ν hν _ (by fun_prop)) (integrable_const _)
              filter_upwards [hAE ν hν] with x hx
              have h := hB hx
              rw [Metric.mem_closedBall, dist_eq_norm] at h
              exact pow_le_pow_left₀ (norm_nonneg _) h 2
            _ = R ^ 2 := by simp
        have hSphere : ∀ (ν : Measure (E n)), InP K ν → ∀ q : E n, ∀ R : ℝ,
            0 ≤ R → K ⊆ Metric.closedBall q R →
            (ν (K ∩ Metric.sphere q R) = 1 ↔
              variance ν + ‖barycenter ν - q‖ ^ 2 = R ^ 2) := by
          intro ν hν q R hR hB
          letI : IsProbabilityMeasure ν := hν.1
          have hle : (fun x : E n => ‖x - q‖ ^ 2) ≤ᵐ[ν] (fun _ => R ^ 2) := by
            filter_upwards [hAE ν hν] with x hx
            exact pow_le_pow_left₀ (norm_nonneg _) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hB hx) 2
          have heq : (∫ x, ‖x - q‖ ^ 2 ∂ν) = R ^ 2 ↔
              (fun x : E n => ‖x - q‖ ^ 2) =ᵐ[ν] (fun _ => R ^ 2) := by
            simpa using integral_eq_iff_of_ae_le (hInt ν hν _ (by fun_prop)) (integrable_const (R ^ 2)) hle
          have hm : MeasurableSet (K ∩ Metric.sphere q R) :=
            hK.isClosed.measurableSet.inter Metric.isClosed_sphere.measurableSet
          rw [← hMoment ν hν q, heq]
          constructor
          · intro h
            have ha : ∀ᵐ x ∂ν, x ∈ K ∩ Metric.sphere q R := by
              apply (ae_iff).2
              change ν (K ∩ Metric.sphere q R)ᶜ = 0
              rw [measure_compl hm (by finiteness), h]
              simp
            filter_upwards [ha] with x hx
            have hs : ‖x - q‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hx.2
            exact congrArg (fun t : ℝ => t ^ 2) hs
          · intro h
            have ha : ∀ᵐ x ∂ν, x ∈ K ∩ Metric.sphere q R := by
              filter_upwards [hAE ν hν, h] with x hx he
              refine ⟨hx, ?_⟩
              rw [Metric.mem_sphere, dist_eq_norm]
              nlinarith [norm_nonneg (x - q)]
            have hc : ν (K ∩ Metric.sphere q R)ᶜ = 0 := (ae_iff).1 ha
            have hh := measure_add_measure_compl hm (μ := ν)
            simpa [hc] using hh
        have hMix : ∀ (x : E n), x ∈ K → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
            let ν := ENNReal.ofReal (1-t) • μ + ENNReal.ofReal t • Measure.dirac x
            InP K ν ∧ barycenter ν = (1-t) • barycenter μ + t • x ∧
              (∫ y, ‖y - barycenter μ‖ ^ 2 ∂ν) =
                (1-t) * variance μ + t * ‖x - barycenter μ‖ ^ 2 := by
          intro x hx t ht ht1 ν
          have hn : 0 ≤ 1-t := sub_nonneg.mpr ht1
          have hp : IsProbabilityMeasure ν := by
            constructor
            simp only [ν, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
              mul_one, Measure.dirac_apply_of_mem (Set.mem_univ x)]
            rw [← ENNReal.ofReal_add hn ht]
            simp
          have hν : InP K ν := by
            refine ⟨hp, ?_⟩
            simp [ν, hμ.2, Measure.dirac_apply' x hK.isClosed.measurableSet.compl, hx]
          refine ⟨hν, ?_, ?_⟩
          · unfold barycenter
            rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac]
            · simp [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal ht]
            · exact (hId μ hμ).smul_measure (by finiteness)
            · exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)
          · rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac]
            · simp [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal ht, variance, smul_eq_mul]
            · exact (hInt μ hμ _ (by fun_prop)).smul_measure (by finiteness)
            · exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)
        have hMaxBall : (∀ ν : Measure (E n), InP K ν → variance ν ≤ variance μ) →
            K ⊆ Metric.closedBall (barycenter μ) (Real.sqrt (variance μ)) := by
          intro hmax x hx
          have hD : ‖x - barycenter μ‖ ^ 2 ≤ variance μ := by
            by_contra h
            have hg : 0 < ‖x - barycenter μ‖ ^ 2 - variance μ := by linarith
            have hpos : 0 < ‖x - barycenter μ‖ ^ 2 := by linarith [hVarNonneg μ]
            let t := (‖x - barycenter μ‖ ^ 2 - variance μ) / (2 * ‖x - barycenter μ‖ ^ 2)
            have ht : 0 < t := div_pos hg (by positivity)
            have ht1 : t ≤ 1 := by
              dsimp [t]
              apply (div_le_one (by positivity)).2
              linarith [hVarNonneg μ]
            obtain ⟨hν, hb, hm⟩ := hMix x hx t ht.le ht1
            have hh := hMoment _ hν (barycenter μ)
            rw [hm, hb] at hh
            have he : (1-t) • barycenter μ + t • x - barycenter μ = t • (x-barycenter μ) := by module
            rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow] at hh
            have hhmax := hmax _ hν
            have htEq : 2 * ‖x - barycenter μ‖ ^ 2 * t = ‖x - barycenter μ‖ ^ 2 - variance μ := by
              dsimp [t]
              exact mul_div_cancel₀ _ (by positivity : (2 * ‖x - barycenter μ‖ ^ 2) ≠ 0)
            nlinarith [mul_pos ht hg]
          rw [Metric.mem_closedBall, dist_eq_norm]
          exact (Real.le_sqrt (norm_nonneg _) (hVarNonneg μ)).2 hD
        have hGlobal : (∀ ν : Measure (E n), InP K ν → variance ν ≤ variance μ) ↔
            ∃ q : E n, ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
              (∀ c : E n, ∀ r : ℝ, 0 ≤ r → K ⊆ Metric.closedBall c r → R ≤ r) ∧
              μ (K ∩ Metric.sphere q R) = 1 ∧ barycenter μ = q := by
          constructor
          · intro hm
            have hb := hMaxBall hm
            refine ⟨barycenter μ, Real.sqrt (variance μ), Real.sqrt_nonneg _, hb, ?_, ?_, rfl⟩
            · intro c r hr hc
              have hh := hBallBound μ hμ c r hr hc
              apply (Real.sqrt_le_iff).2
              exact ⟨hr, by nlinarith [sq_nonneg ‖barycenter μ - c‖]⟩
            · apply (hSphere μ hμ _ _ (Real.sqrt_nonneg _) hb).2
              simp [Real.sq_sqrt (hVarNonneg μ)]
          · rintro ⟨q, R, hr, hb, hmin, hs, hq⟩ ν hν
            have he := (hSphere μ hμ q R hr hb).1 hs
            rw [hq, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at he
            have hh := hBallBound ν hν q R hr hb
            nlinarith [sq_nonneg ‖barycenter ν - q‖]
        have hRadius : ∀ q : E n, ∀ R : ℝ, 0 ≤ R → K ⊆ Metric.closedBall q R →
            (∀ c : E n, ∀ r : ℝ, 0 ≤ r → K ⊆ Metric.closedBall c r → R ≤ r) →
            (∀ ν : Measure (E n), InP K ν → variance ν ≤ variance μ) → variance μ = R ^ 2 := by
          intro q R hr hb hmin hm
          have hh := hmin _ _ (Real.sqrt_nonneg _) (hMaxBall hm)
          have hu := hBallBound μ hμ q R hr hb
          nlinarith [sq_nonneg ‖barycenter μ - q‖, Real.sq_sqrt (hVarNonneg μ), Real.sqrt_nonneg (variance μ)]
        have hne : K.Nonempty := (hAE μ hμ).exists
        letI : Nonempty K := hne.to_subtype
        let b := barycenter μ
        let m := ∫ x, ‖x‖ ^ 2 ∂μ
        let f : E n → E n → ℝ := fun p x => inner ℝ p (x-b) + ‖x‖ ^ 2
        have hf : ∀ p, Continuous (f p) := by intro p; dsimp [f]; fun_prop
        have hBdd : ∀ p, BddAbove (Set.range fun x : K => f p x) := by
          intro p
          have hh := (hK.image (hf p)).bddAbove
          apply hh.mono
          rintro y ⟨x, rfl⟩
          exact ⟨x, x.2, rfl⟩
        let F : E n → ℝ := fun p => ⨆ x : K, f p x
        have hFle : ∀ p x, x ∈ K → f p x ≤ F p := by
          intro p x hx
          exact le_ciSup (hBdd p) (⟨x, hx⟩ : K)
        have hFmax : ∀ p, ∃ x ∈ K, F p = f p x := by
          intro p
          obtain ⟨x, hx, hh⟩ := hK.exists_isMaxOn hne (hf p).continuousOn
          refine ⟨x, hx, le_antisymm ?_ (hFle p x hx)⟩
          exact ciSup_le fun y => hh y.2
        have hFint : ∀ p, (∫ x, f p x ∂μ) = m := by
          intro p
          dsimp [f]
          rw [integral_add (hInt μ hμ _ (by fun_prop)) (hInt μ hμ _ (by fun_prop))]
          rw [integral_inner (f := fun x : E n => x-b) ((hId μ hμ).sub (integrable_const b)) p, integral_sub (hId μ hμ) (integrable_const b)]
          simp [b, barycenter, m]
        have hmF : ∀ p, m ≤ F p := by
          intro p
          calc
            m = ∫ x, f p x ∂μ := (hFint p).symm
            _ ≤ ∫ _ : E n, F p ∂μ := by
              apply integral_mono_ae (hInt μ hμ _ (hf p)) (integrable_const _)
              filter_upwards [hAE μ hμ] with x hx
              exact hFle p x hx
            _ = F p := by simp
        have hStar : ∀ p, phiStar K p = ((F p + inner ℝ p b : ℝ) : EReal) := by
          intro p
          unfold phiStar WassersteinDRO.ConvexLossP1.conjugate
          apply le_antisymm
          · apply iSup_le
            intro x
            by_cases hx : x ∈ K
            · simp only [phi, hx, if_pos, innerSL_apply_apply, ← EReal.coe_sub, EReal.coe_le_coe_iff]
              have hh := hFle p x hx
              dsimp [f] at hh
              rw [inner_sub_right] at hh
              linarith
            · simp [phi, hx]
          · obtain ⟨x, hx, he⟩ := hFmax p
            apply le_trans _ (le_iSup (fun x : E n => ((innerSL ℝ p) x : EReal) - phi K x) x)
            simp only [phi, hx, if_pos, innerSL_apply_apply, ← EReal.coe_sub, EReal.coe_le_coe_iff]
            dsimp [f] at he
            rw [inner_sub_right] at he
            linarith
        have hBi : phiBiconjugate K b = ⨆ p : E n, ((-F p : ℝ) : EReal) := by
          unfold phiBiconjugate WassersteinDRO.ConvexLossP1.conjugate
          congr 1
          funext p
          rw [hStar, innerSL_apply_apply, ← EReal.coe_sub, real_inner_comm b p]
          congr 1
          ring
        have hBiBound : phiBiconjugate K b ≤ ((-m : ℝ) : EReal) := by
          rw [hBi]
          apply iSup_le
          intro p
          exact EReal.coe_le_coe_iff.mpr (neg_le_neg (hmF p))
        have hBound : (variance μ : EReal) ≤ ((-(‖barycenter μ‖ ^ 2) : ℝ) : EReal) - phiBiconjugate K (barycenter μ) := by
          calc
            (variance μ : EReal) = ((-(‖barycenter μ‖ ^ 2) : ℝ) : EReal) - ((-m : ℝ) : EReal) := by
              rw [← EReal.coe_sub]
              congr 1
              rw [hVar μ hμ]
              dsimp [m]
              ring
            _ ≤ _ := EReal.sub_le_sub le_rfl hBiBound
        have hMin : b ∈ interior (closedConvexHull ℝ K) → ∃ p, ∀ z, F p ≤ F z := by
          intro hb
          obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hb)
          let ε := δ / 2
          have hε : 0 < ε := by dsimp [ε]; positivity
          have hLin : ∀ p : E n, ∀ y ∈ closedConvexHull ℝ K,
              inner ℝ p y ≤ F p + inner ℝ p b := by
            intro p
            apply closedConvexHull_min
            · intro x hx
              have hh := hFle p x hx
              dsimp [f] at hh
              rw [inner_sub_right] at hh
              change inner ℝ p x ≤ F p + inner ℝ p b
              nlinarith [sq_nonneg ‖x‖]
            · exact convex_halfSpace_le (innerSL ℝ p).toLinearMap.isLinear _
            · exact isClosed_le (innerSL ℝ p).continuous continuous_const
          have hCoerc : ∀ p, ε * ‖p‖ ≤ F p := by
            intro p
            by_cases hp : p = 0
            · subst p
              have hh := hLin 0 b (interior_subset hb)
              simpa using hh
            have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
            let y := b + (ε / ‖p‖) • p
            have hdist : dist y b = ε := by
              rw [dist_eq_norm]
              dsimp [y]
              rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hε hpn)]
              exact div_mul_cancel₀ _ hpn.ne'
            have hy : y ∈ closedConvexHull ℝ K := hball (by
              rw [Metric.mem_ball, hdist]
              dsimp [ε]
              linarith)
            have hh := hLin p y hy
            dsimp [y] at hh
            rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at hh
            have he : ε / ‖p‖ * ‖p‖ ^ 2 = ε * ‖p‖ := by field_simp
            rw [he] at hh
            linarith
          have hlsc : LowerSemicontinuous F := by
            apply lowerSemicontinuous_ciSup hBdd
            intro x
            apply Continuous.lowerSemicontinuous
            dsimp [f]
            fun_prop
          have hF0 : 0 ≤ F 0 := by simpa using hCoerc 0
          obtain ⟨p, hp, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
            (s := Metric.closedBall (0 : E n) (F 0 / ε))
            ⟨0, by simp [div_nonneg hF0 hε.le]⟩ (isCompact_closedBall _ _)
            (hlsc.lowerSemicontinuousOn _)
          refine ⟨p, fun z => ?_⟩
          by_cases hz : z ∈ Metric.closedBall (0 : E n) (F 0 / ε)
          · exact hmin hz
          · have hnorm : F 0 / ε < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
            have hh := hCoerc z
            have hp0 := hmin (by simp [div_nonneg hF0 hε.le] : (0 : E n) ∈ Metric.closedBall 0 (F 0 / ε))
            have hlt : F 0 < ε * ‖z‖ := (div_lt_iff₀ hε).1 hnorm |>.trans_eq (mul_comm _ _)
            exact hp0.trans (hlt.le.trans hh)
        have hBiMin : ∀ p, (∀ z, F p ≤ F z) →
            phiBiconjugate K b = ((-F p : ℝ) : EReal) := by
          intro p hp
          rw [hBi]
          apply le_antisymm
          · exact iSup_le fun z => EReal.coe_le_coe_iff.mpr (neg_le_neg (hp z))
          · exact le_iSup (fun z : E n => ((-F z : ℝ) : EReal)) p
        have hGeom : ∀ p x : E n,
            ‖x - ((-1 / 2 : ℝ) • p)‖ ^ 2 =
              f p x + ‖((-1 / 2 : ℝ) • p)‖ ^ 2 + inner ℝ p b := by
          intro p x
          rw [norm_sub_sq_real]
          dsimp [f]
          rw [real_inner_smul_right, inner_sub_right, real_inner_comm x p]
          ring
        have hFromDual : ∀ p, F p = m → ∃ q : E n, ∃ R : ℝ,
            0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧ μ (K ∩ Metric.sphere q R) = 1 := by
          intro p hp
          let q := (-1 / 2 : ℝ) • p
          let C := F p + ‖q‖ ^ 2 + inner ℝ p b
          have hC : 0 ≤ C := by
            obtain ⟨x, hx, he⟩ := hFmax p
            have hh := hGeom p x
            change ‖x-q‖ ^ 2 = f p x + ‖q‖ ^ 2 + inner ℝ p b at hh
            dsimp [C]
            rw [he, ← hh]
            exact sq_nonneg _
          have hBall : K ⊆ Metric.closedBall q (Real.sqrt C) := by
            intro x hx
            rw [Metric.mem_closedBall, dist_eq_norm]
            apply (Real.le_sqrt (norm_nonneg _) hC).2
            rw [hGeom]
            dsimp [C, q]
            linarith [hFle p x hx]
          refine ⟨q, Real.sqrt C, Real.sqrt_nonneg _, hBall, ?_⟩
          apply (hSphere μ hμ q _ (Real.sqrt_nonneg _) hBall).2
          rw [Real.sq_sqrt hC, hVar μ hμ]
          dsimp [C, q, m]
          rw [hGeom p b]
          dsimp [f]
          simp only [sub_self, inner_zero_right, zero_add]
          rw [hp]
          dsimp [m]
          ring
        have hToDual : (∃ q : E n, ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
            μ (K ∩ Metric.sphere q R) = 1) →
            ∃ p, F p = m := by
          rintro ⟨q, R, hR, hBall, hS⟩
          let p := (-2 : ℝ) • q
          have hcalc : ∀ x, f p x = ‖x-q‖ ^ 2 - ‖q‖ ^ 2 + 2 * inner ℝ q b := by
            intro x
            dsimp [f, p]
            rw [real_inner_smul_left, inner_sub_right, norm_sub_sq_real, real_inner_comm x q]
            ring
          have hm : m = R ^ 2 - ‖q‖ ^ 2 + 2 * inner ℝ q b := by
            have hh := (hSphere μ hμ q R hR hBall).1 hS
            rw [hVar μ hμ, norm_sub_sq_real, real_inner_comm q (barycenter μ)] at hh
            dsimp [m, b]
            linarith
          refine ⟨p, le_antisymm ?_ (hmF p)⟩
          obtain ⟨x, hx, he⟩ := hFmax p
          have hh : ‖x-q‖ ^ 2 ≤ R ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (by simpa [Metric.mem_closedBall, dist_eq_norm] using hBall hx) 2
          rw [he, hcalc, hm]
          linarith
        have hEquality : b ∈ interior (closedConvexHull ℝ K) →
            (((variance μ : EReal) = ((-(‖barycenter μ‖ ^ 2) : ℝ) : EReal) - phiBiconjugate K (barycenter μ)) ↔
              ∃ q : E n, ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
                μ (K ∩ Metric.sphere q R) = 1) := by
          intro hb
          constructor
          · intro he
            obtain ⟨p, hp⟩ := hMin hb
            have hbi := hBiMin p hp
            change phiBiconjugate K (barycenter μ) = ((-F p : ℝ) : EReal) at hbi
            rw [hbi, ← EReal.coe_sub] at he
            have hr : variance μ = -‖barycenter μ‖ ^ 2 - -F p := EReal.coe_eq_coe_iff.1 he
            apply hFromDual p
            rw [hVar μ hμ] at hr
            dsimp [m]
            linarith
          · intro hs
            obtain ⟨p, hp⟩ := hToDual hs
            have hbi : phiBiconjugate K b = ((-m : ℝ) : EReal) := by
              apply le_antisymm hBiBound
              rw [hBi]
              simpa [hp] using le_iSup (fun z : E n => ((-F z : ℝ) : EReal)) p
            change phiBiconjugate K (barycenter μ) = ((-m : ℝ) : EReal) at hbi
            rw [hbi, ← EReal.coe_sub]
            congr 1
            rw [hVar μ hμ]
            dsimp [m]
            ring
        exact ⟨hBound, hEquality, hGlobal, hRadius⟩
