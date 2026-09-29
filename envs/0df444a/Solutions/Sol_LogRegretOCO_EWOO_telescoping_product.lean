-- Prove2me | solution 1 for LogRegretOCO.EWOO.telescoping_product
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T15:20:59.641003+00:00
-- url     : https://prove2.me/submissions/169fc48c-e06a-4981-aa8b-8085cda99298

import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_ewooPoint
import Definitions.Def_LogRegretOCO_EWOO_shrunkSet
import Mathlib

open MeasureTheory


namespace LogRegretOCO.EWOO

variable {n : ℕ}

lemma pow_ratio_ge (T : ℕ) : 1 / Real.exp 1 ≤ ((T : ℝ) / ((T : ℝ) + 1)) ^ T := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp; exact inv_le_one_of_one_le₀ (by linarith [Real.add_one_le_exp 1])
  · have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    have h1 : ((T : ℝ) + 1) / T = 1 + 1 / T := by field_simp
    have h2 : (1 + 1 / (T : ℝ)) ^ T ≤ Real.exp 1 := by
      calc (1 + 1 / (T : ℝ)) ^ T ≤ Real.exp (1 / T) ^ T :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (T : ℝ))]) T
        _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; field_simp
    have h3 : ((T : ℝ) / ((T : ℝ) + 1)) ^ T = 1 / (1 + 1 / (T : ℝ)) ^ T := by
      rw [← h1, div_pow, div_pow, one_div_div]
    rw [h3]
    exact one_div_le_one_div_of_le (by positivity) h2

theorem shrunk_main (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ P) (T : ℕ) :
    (∀ t, ∀ x ∈ shrunkSet P xstar T,
        ((T : ℝ) / ((T : ℝ) + 1)) * Real.exp (-α * f t xstar) ≤ Real.exp (-α * f t x)) ∧
    (∀ x ∈ shrunkSet P xstar T,
        ((T : ℝ) / ((T : ℝ) + 1)) ^ T * ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
            ≤ ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ x) ∧
          (1 / Real.exp 1) * ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
            ≤ ((T : ℝ) / ((T : ℝ) + 1)) ^ T *
                ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)) := by
  have hla0 : (0 : ℝ) ≤ (T : ℝ) / ((T : ℝ) + 1) := by positivity
  have hμ0 : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
  have hsum : (T : ℝ) / ((T : ℝ) + 1) + 1 / ((T : ℝ) + 1) = 1 := by field_simp
  have one : ∀ t, ∀ x ∈ shrunkSet P xstar T,
      ((T : ℝ) / ((T : ℝ) + 1)) * Real.exp (-α * f t xstar) ≤ Real.exp (-α * f t x) := by
    intro t x ⟨y, hy, hx⟩
    have hc := (hexp t).2 hxstar hy hla0 hμ0 hsum
    rw [← hx] at hc
    simp only [smul_eq_mul] at hc
    have : 0 ≤ 1 / ((T : ℝ) + 1) * Real.exp (-α * f t y) := by positivity
    linarith
  refine ⟨one, fun x hx => ⟨?_, ?_⟩⟩
  · have := Finset.prod_le_prod (s := Finset.Icc 1 T)
      (f := fun τ => ((T : ℝ) / ((T : ℝ) + 1)) * Real.exp (-α * f τ xstar))
      (g := fun τ => Real.exp (-α * f τ x)) (fun τ _ => by positivity) (fun τ _ => one τ x hx)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel] at this
    exact this
  · exact mul_le_mul_of_nonneg_right (pow_ratio_ge T) (Finset.prod_nonneg fun _ _ => by positivity)


lemma weight_eq (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (t : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ewooWeight α f t x = ∏ τ ∈ Finset.Ico 1 t, Real.exp (-α * f τ x) := by
  unfold ewooWeight; rw [Finset.mul_sum, Real.exp_sum]

theorem jensen_main (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (t : ℕ) :
    (∫ x in P, Real.exp (-α * f t x) * ∏ τ ∈ Finset.Ico 1 t, Real.exp (-α * f τ x)) /
        (∫ x in P, ∏ τ ∈ Finset.Ico 1 t, Real.exp (-α * f τ x))
      ≤ Real.exp (-α * f t (ewooPoint P α f t)) := by
  set W : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∏ τ ∈ Finset.Ico 1 t, Real.exp (-α * f τ x)
    with hW
  set h : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (-α * f t x) with hh
  have hPc : IsCompact P := Metric.isCompact_of_isClosed_isBounded hPclosed hPbdd
  have hPm : MeasurableSet P := hPclosed.measurableSet
  have hPfin : volume P < ⊤ := hPbdd.measure_lt_top
  have hexpc : ∀ τ, ContinuousOn (fun x => Real.exp (-α * f τ x)) P := fun τ =>
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hcont τ))
  have hWc : ContinuousOn W P := continuousOn_finset_prod _ fun τ _ => hexpc τ
  have hhc : ContinuousOn h P := hexpc t
  have hWpos : ∀ x, 0 < W x := fun x => Finset.prod_pos fun τ _ => Real.exp_pos _
  have hWi : IntegrableOn W P := hWc.integrableOn_compact hPc
  -- positivity of the normaliser
  obtain ⟨x0, hx0, hmin⟩ := hPc.exists_isMinOn hPne hWc
  have hvolpos : 0 < (volume P).toReal :=
    ENNReal.toReal_pos hPvol hPfin.ne
  have hI : 0 < ∫ x in P, W x := by
    have h1 : ∫ x in P, W x0 ≤ ∫ x in P, W x :=
      setIntegral_mono_on (integrableOn_const hPfin.ne) hWi hPm fun x hx => hmin hx
    rw [setIntegral_const, smul_eq_mul] at h1
    have : 0 < volume.real P * W x0 := mul_pos (by rw [measureReal_def]; exact hvolpos) (hWpos x0)
    linarith
  -- the weighted measure
  set ν := volume.restrict P with hν
  set μ := ν.withDensity (fun x => ENNReal.ofReal (W x)) with hμ
  have hWae : AEMeasurable (fun x => ENNReal.ofReal (W x)) ν :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hWc.aemeasurable hPm)
  have hμuniv : μ Set.univ = ENNReal.ofReal (∫ x in P, W x) := by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ofReal_integral_eq_lintegral_ofReal hWi (Filter.Eventually.of_forall fun x => (hWpos x).le)]
  haveI : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact ENNReal.ofReal_lt_top⟩
  haveI : NeZero μ := ⟨by
    intro h0
    have := congrArg (fun m : Measure _ => m Set.univ) h0
    simp only [Measure.coe_zero, Pi.zero_apply] at this
    rw [hμuniv, ENNReal.ofReal_eq_zero] at this
    linarith⟩
  have hμreal : μ.real Set.univ = ∫ x in P, W x := by
    rw [measureReal_def, hμuniv, ENNReal.toReal_ofReal hI.le]
  have hintμ : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : EuclideanSpace ℝ (Fin n) → E),
      ∫ x, g x ∂μ = ∫ x in P, W x • g x := by
    intro E _ _ g
    rw [hμ, integral_withDensity_eq_integral_toReal_smul₀ hWae
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hWpos x).le]
  have hac : μ ≪ ν := withDensity_absolutelyContinuous _ _
  have hmem : ∀ᵐ x ∂μ, x ∈ P := hac.ae_le (ae_restrict_mem hPm)
  obtain ⟨R, hR⟩ := hPbdd.exists_norm_le
  obtain ⟨C, hC⟩ := hPc.exists_bound_of_continuousOn hhc
  have hfi : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x) μ :=
    Integrable.of_bound aestronglyMeasurable_id R (by filter_upwards [hmem] with x hx using hR x hx)
  have hgi : Integrable (h ∘ fun x => x) μ :=
    Integrable.of_bound ((hhc.aestronglyMeasurable hPm).mono_ac hac) C
      (by filter_upwards [hmem] with x hx using hC x hx)
  have hJ := (hexp t).le_map_average hhc hPclosed hmem hfi hgi
  rw [average_eq, average_eq, hμreal, hintμ, hintμ] at hJ
  simp only [Function.comp, smul_eq_mul] at hJ
  have hpt : ewooPoint P α f t = (∫ x in P, W x)⁻¹ • ∫ x in P, W x • x := by
    unfold ewooPoint
    simp only [weight_eq]
    rfl
  rw [hpt]
  have e : (∫ x in P, h x * W x) / (∫ x in P, W x) = (∫ x in P, W x)⁻¹ * ∫ x in P, W x * h x := by
    rw [div_eq_inv_mul]; congr 1; congr 1; funext x; ring
  show (∫ x in P, h x * W x) / (∫ x in P, W x) ≤ h _
  rw [e]
  exact hJ


section Rest

variable (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
include hPconv hPclosed hPbdd hPne hPvol hexp hcont

lemma pos_int (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContinuousOn g P) (hgp : ∀ x, 0 < g x) :
    0 < ∫ x in P, g x := by
  have hPc : IsCompact P := Metric.isCompact_of_isClosed_isBounded hPclosed hPbdd
  have hPm : MeasurableSet P := hPclosed.measurableSet
  have hPfin : volume P < ⊤ := hPbdd.measure_lt_top
  obtain ⟨x0, hx0, hmin⟩ := hPc.exists_isMinOn hPne hg
  have h1 : ∫ x in P, g x0 ≤ ∫ x in P, g x :=
    setIntegral_mono_on (integrableOn_const hPfin.ne) (hg.integrableOn_compact hPc) hPm
      fun x hx => hmin hx
  rw [setIntegral_const, smul_eq_mul] at h1
  have : 0 < volume.real P * g x0 :=
    mul_pos (by rw [measureReal_def]; exact ENNReal.toReal_pos hPvol hPfin.ne) (hgp x0)
  linarith

lemma prod_cont (s : Finset ℕ) : ContinuousOn (fun x => ∏ τ ∈ s, Real.exp (-α * f τ x)) P :=
  continuousOn_finset_prod _ fun τ _ =>
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hcont τ))

theorem telescoping_main (t : ℕ) :
    (∫ x in P, ∏ τ ∈ Finset.Icc 1 t, Real.exp (-α * f τ x)) / (∫ _x in P, (1 : ℝ))
        ≤ ∏ τ ∈ Finset.Icc 1 t, Real.exp (-α * f τ (ewooPoint P α f τ)) ∧
      (∫ _x in P, (1 : ℝ)) = (volume P).toReal := by
  have hV : (∫ _x in P, (1 : ℝ)) = (volume P).toReal := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  refine ⟨?_, hV⟩
  have hVpos : 0 < ∫ _x in P, (1 : ℝ) := by
    have := pos_int P hPconv hPclosed hPbdd hPne hPvol α f hexp hcont (fun _ => 1)
      continuousOn_const (fun _ => one_pos)
    exact this
  induction t with
  | zero =>
    have : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
    rw [this]; simp only [Finset.prod_empty]; rw [div_self hVpos.ne']
  | succ s ih =>
    have hJ := jensen_main P hPconv hPclosed hPbdd hPne hPvol α f hexp hcont (s + 1)
    rw [Finset.Ico_add_one_right_eq_Icc] at hJ
    have e1 : ∀ x, Real.exp (-α * f (s + 1) x) * ∏ τ ∈ Finset.Icc 1 s, Real.exp (-α * f τ x) =
        ∏ τ ∈ Finset.Icc 1 (s + 1), Real.exp (-α * f τ x) := fun x => by
      rw [Finset.prod_Icc_succ_top (by omega), mul_comm]
    simp only [e1] at hJ
    have hIs : 0 < ∫ x in P, ∏ τ ∈ Finset.Icc 1 s, Real.exp (-α * f τ x) :=
      pos_int P hPconv hPclosed hPbdd hPne hPvol α f hexp hcont _
        (prod_cont P hPconv hPclosed hPbdd hPne hPvol α f hexp hcont _)
        (fun x => Finset.prod_pos fun _ _ => Real.exp_pos _)
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ s + 1)]
    set Is := ∫ x in P, ∏ τ ∈ Finset.Icc 1 s, Real.exp (-α * f τ x)
    set Is1 := ∫ x in P, ∏ τ ∈ Finset.Icc 1 (s + 1), Real.exp (-α * f τ x)
    set V := ∫ _x in P, (1 : ℝ)
    have e2 : Is1 / V = Is / V * (Is1 / Is) := by field_simp
    rw [e2]
    exact mul_le_mul ih hJ (by positivity) (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)

lemma shrunk_eq (xstar : EuclideanSpace ℝ (Fin n)) (T : ℕ) :
    shrunkSet P xstar T = AffineMap.homothety xstar (1 / ((T : ℝ) + 1)) '' P := by
  ext x
  simp only [shrunkSet, Set.mem_setOf_eq, Set.mem_image, AffineMap.homothety_apply,
    vsub_eq_sub, vadd_eq_add]
  have hT : (T : ℝ) + 1 ≠ 0 := by positivity
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [smul_sub]
    have : (T : ℝ) / (T + 1) = 1 - 1 / (T + 1) := by field_simp; ring
    rw [this, sub_smul, one_smul]; abel
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [smul_sub]
    have : (T : ℝ) / (T + 1) = 1 - 1 / (T + 1) := by field_simp; ring
    rw [this, sub_smul, one_smul]; abel

theorem product_main (T : ℕ) (hT : 1 ≤ T) (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ P) :
    (volume (shrunkSet P xstar T)).toReal / (volume P).toReal * (1 / Real.exp 1) *
          ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
        ≤ ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ (ewooPoint P α f τ)) ∧
      1 / (Real.exp 1 * ((T : ℝ) + 1) ^ n) * ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
        ≤ (volume (shrunkSet P xstar T)).toReal / (volume P).toReal * (1 / Real.exp 1) *
          ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar) := by
  have hPc : IsCompact P := Metric.isCompact_of_isClosed_isBounded hPclosed hPbdd
  have hPfin : volume P < ⊤ := hPbdd.measure_lt_top
  have hVpos : 0 < (volume P).toReal := ENNReal.toReal_pos hPvol hPfin.ne
  set c := ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar) with hc
  have hc0 : 0 ≤ c := Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hS : shrunkSet P xstar T = AffineMap.homothety xstar (1 / ((T : ℝ) + 1)) '' P :=
    shrunk_eq P hPconv hPclosed hPbdd hPne hPvol α f hexp hcont xstar T
  have hvolS : (volume (shrunkSet P xstar T)).toReal = (1 / ((T : ℝ) + 1)) ^ n * (volume P).toReal := by
    rw [hS, Measure.addHaar_image_homothety, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (by positivity)]
  refine ⟨?_, ?_⟩
  · obtain ⟨htel, hV⟩ := telescoping_main P hPconv hPclosed hPbdd hPne hPvol α f hexp hcont T
    rw [hV] at htel
    refine le_trans ?_ htel
    -- ∫_S const ≤ ∫_S prod ≤ ∫_P prod
    have hSsub : shrunkSet P xstar T ⊆ P := by
      rintro x ⟨y, hy, rfl⟩
      have := hPconv hxstar hy (by positivity : (0:ℝ) ≤ (T : ℝ) / ((T : ℝ) + 1))
        (by positivity : (0:ℝ) ≤ 1 / ((T : ℝ) + 1)) (by field_simp)
      exact this
    have hSm : MeasurableSet (shrunkSet P xstar T) := by
      rw [hS]
      exact ((hPc.image (AffineMap.homothety_continuous _ _)).isClosed).measurableSet
    have hSfin : volume (shrunkSet P xstar T) < ⊤ :=
      lt_of_le_of_lt (measure_mono hSsub) hPfin
    have hprodc := prod_cont P hPconv hPclosed hPbdd hPne hPvol α f hexp hcont (Finset.Icc 1 T)
    have hint : IntegrableOn (fun x => ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ x)) P :=
      hprodc.integrableOn_compact hPc
    have h1 : ∫ x in shrunkSet P xstar T, (1 / Real.exp 1 * c) ≤
        ∫ x in shrunkSet P xstar T, ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ x) := by
      refine setIntegral_mono_on (integrableOn_const hSfin.ne) (hint.mono_set hSsub) hSm
        fun x hx => ?_
      obtain ⟨_, h2⟩ := shrunk_main P hPconv α f hexp xstar hxstar T
      exact (h2 x hx).2.trans (h2 x hx).1
    have h2 : ∫ x in shrunkSet P xstar T, ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ x) ≤
        ∫ x in P, ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ x) :=
      setIntegral_mono_set hint
        (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
        (Filter.Eventually.of_forall hSsub)
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at h1
    have e : (volume (shrunkSet P xstar T)).toReal / (volume P).toReal * (1 / Real.exp 1) * c =
        ((volume (shrunkSet P xstar T)).toReal * (1 / Real.exp 1 * c)) / (volume P).toReal := by
      ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hVpos.le
  · rw [hvolS]
    apply le_of_eq
    rw [one_div_pow]
    field_simp

theorem regret_main (T : ℕ) (hT : 1 ≤ T) (hα : 0 < α) (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ P) :
    ∑ t ∈ Finset.Icc 1 T, (f t (ewooPoint P α f t) - f t u)
      ≤ 1 / α * n * (1 + Real.log ((T : ℝ) + 1)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hsub : ∀ a b : EuclideanSpace ℝ (Fin 0), a = b := fun a b => by
      ext i; exact i.elim0
    have : ∀ t, f t (ewooPoint P α f t) - f t u = 0 := fun t => by rw [hsub (ewooPoint P α f t) u]; ring
    simp [this]
  obtain ⟨h1, h2⟩ := product_main P hPconv hPclosed hPbdd hPne hPvol α f hexp hcont T hT u hu
  have hP := h2.trans h1
  rw [← Real.exp_sum, ← Real.exp_sum] at hP
  simp only [← Finset.mul_sum] at hP
  set A := ∑ τ ∈ Finset.Icc 1 T, f τ (ewooPoint P α f τ)
  set B := ∑ τ ∈ Finset.Icc 1 T, f τ u
  have hpos : 0 < Real.exp 1 * ((T : ℝ) + 1) ^ n := by positivity
  have e : 1 / (Real.exp 1 * ((T : ℝ) + 1) ^ n) * Real.exp (-α * B) =
      Real.exp (-α * B - 1 - n * Real.log ((T : ℝ) + 1)) := by
    rw [Real.exp_sub, Real.exp_sub, ← Real.log_pow, Real.exp_log (by positivity)]
    field_simp
  rw [e, Real.exp_le_exp] at hP
  have hsum : ∑ t ∈ Finset.Icc 1 T, (f t (ewooPoint P α f t) - f t u) = A - B := by
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log ((T : ℝ) + 1) := Real.log_nonneg (by linarith [(T.cast_nonneg : (0:ℝ) ≤ T)])
  have h3 : α * (A - B) ≤ 1 + n * Real.log ((T : ℝ) + 1) := by linarith
  have h4 : 1 + n * Real.log ((T : ℝ) + 1) ≤ n * (1 + Real.log ((T : ℝ) + 1)) := by nlinarith
  rw [show 1 / α * n * (1 + Real.log ((T : ℝ) + 1)) = (n * (1 + Real.log ((T : ℝ) + 1))) / α by ring,
    le_div_iff₀ hα]
  linarith

end Rest

end LogRegretOCO.EWOO

open LogRegretOCO.EWOO

theorem solution (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (hPclosed : IsClosed P) (hPbdd : Bornology.IsBounded P)
    (hPne : P.Nonempty) (hPvol : volume P ≠ 0)
    (α : ℝ) (hα : 0 < α) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t)) (hcont : ∀ t, ContinuousOn (f t) P)
    (t : ℕ) (ht : 1 ≤ t) :
    (∫ x in P, ∏ τ ∈ Finset.Icc 1 t, Real.exp (-α * f τ x)) / (∫ _x in P, (1 : ℝ))
        ≤ ∏ τ ∈ Finset.Icc 1 t, Real.exp (-α * f τ (ewooPoint P α f τ)) ∧
      (∫ _x in P, (1 : ℝ)) = (volume P).toReal := by
  exact telescoping_main P hPconv hPclosed hPbdd hPne hPvol α f hexp hcont t
