-- Prove2me | solution 1 for MartOT.Product.strict_convex_integral_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:29:42.639207+00:00
-- url     : https://prove2.me/submissions/f96d86ca-b0b4-434e-8bad-c8eaf96217a6

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Abs_theorem_2_6_sufficiency

open MeasureTheory Filter

namespace LC5Aux

/-- `ν^π_A = proj^y_# π|_{A×ℝ}`. -/
noncomputable def tgt (π : Measure (ℝ × ℝ)) (A : Set ℝ) : Measure ℝ :=
  (π.restrict (A ×ˢ Set.univ)).map Prod.snd

lemma integralE_of_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    MartOT.Var.integralE μ f = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h0 : ∀ x, (-(f x : EReal)).toENNReal = 0 := fun x =>
    EReal.toENNReal_of_nonpos (by rw [← EReal.coe_neg]; exact_mod_cast neg_nonpos.mpr (hf x))
  simp only [h0, lintegral_zero, EReal.real_coe_toENNReal, EReal.coe_ennreal_zero, sub_zero]

lemma integralE_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) :
    MartOT.Var.integralE μ f = ((∫⁻ x, ENNReal.ofReal (f x) ∂μ : ENNReal) : EReal) -
      ((∫⁻ x, ENNReal.ofReal (-f x) ∂μ : ENNReal) : EReal) := by
  unfold MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  simp only [← EReal.coe_neg, EReal.real_coe_toENNReal]

lemma tgt_apply (π : Measure (ℝ × ℝ)) (A : Set ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    tgt π A B = π (Prod.snd ⁻¹' B ∩ A ×ˢ Set.univ) := by
  unfold tgt
  rw [Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]

lemma tgt_mono (π : Measure (ℝ × ℝ)) {A A' : Set ℝ} (h : A ⊆ A') : tgt π A ≤ tgt π A' := by
  unfold tgt
  exact Measure.map_mono (Measure.restrict_mono (Set.prod_mono h le_rfl) le_rfl) measurable_snd

lemma tgt_le_of_plan {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)} (h : MartOT.Var.IsPlan μ ν π)
    (A : Set ℝ) : tgt π A ≤ ν := by
  rw [← h.2]; unfold tgt
  exact Measure.map_mono Measure.restrict_le_self measurable_snd

lemma isFinite_of_plan {μ ν : Measure ℝ} [IsFiniteMeasure μ] {π : Measure (ℝ × ℝ)}
    (h : MartOT.Var.IsPlan μ ν π) : IsFiniteMeasure π := by
  refine ⟨?_⟩
  have : π Set.univ = μ Set.univ := by
    rw [← h.1, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  rw [this]; exact measure_lt_top μ _

lemma inM_of_le {η ν : Measure ℝ} (h : η ≤ ν) (hν : MartOT.Var.InM ν) : MartOT.Var.InM η := by
  have := hν.1
  have : IsFiniteMeasure η := isFiniteMeasure_of_le ν h
  exact ⟨inferInstance, hν.2.mono_measure h⟩

lemma lintegral_tgt (π : Measure (ℝ × ℝ)) (A : Set ℝ) {g : ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂(tgt π A) = ∫⁻ p in A ×ˢ Set.univ, g p.2 ∂π := by
  unfold tgt; rw [lintegral_map hg measurable_snd]

lemma lintegral_tgt_iUnion (π : Measure (ℝ × ℝ)) (u : ℕ → ℝ) (hu : Monotone u)
    {g : ℝ → ENNReal} (hg : Measurable g) :
    Monotone (fun n => ∫⁻ y, g y ∂(tgt π (Set.Iic (u n)))) ∧
    ∫⁻ y, g y ∂(tgt π (⋃ n, Set.Iic (u n))) = ⨆ n, ∫⁻ y, g y ∂(tgt π (Set.Iic (u n))) := by
  refine ⟨fun m n h => lintegral_mono' (tgt_mono π (Set.Iic_subset_Iic.mpr (hu h))) le_rfl, ?_⟩
  simp only [lintegral_tgt π _ hg]
  rw [Set.iUnion_prod_const]
  apply setLIntegral_iUnion_of_directed
  intro i j
  exact ⟨max i j, Set.prod_mono (Set.Iic_subset_Iic.mpr (hu (le_max_left i j))) le_rfl,
    Set.prod_mono (Set.Iic_subset_Iic.mpr (hu (le_max_right i j))) le_rfl⟩

lemma convex_lower_bound {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ∃ C K : ℝ, ∀ x, -φ x ≤ C + K * |x| := by
  refine ⟨|φ 0|, |φ 0 - φ (-1)| + |φ 1 - φ 0|, fun x => ?_⟩
  have h0 := neg_abs_le (φ 0)
  have ha1 := abs_nonneg (φ 0 - φ (-1))
  have ha2 := abs_nonneg (φ 1 - φ 0)
  have hx0 := abs_nonneg x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h := hφ.secant_mono (a := 0) (x := x) (y := 1) trivial trivial trivial hx.ne
      (by norm_num) (by linarith)
    simp only [sub_zero, div_one] at h
    rw [div_le_iff_of_neg hx] at h
    have h1 : -(φ 1 - φ 0) * x ≤ |φ 1 - φ 0| * |x| := by
      rw [abs_of_neg hx, neg_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (neg_pos.mpr hx).le
    nlinarith
  · subst hx; simp only [abs_zero, mul_zero, add_zero]; exact neg_le_abs _
  · have h := hφ.secant_mono (a := 0) (x := -1) (y := x) trivial trivial trivial (by norm_num)
      hx.ne' (by linarith)
    have e : (φ (-1) - φ 0) / (-1 - 0) = φ 0 - φ (-1) := by ring
    rw [e, sub_zero, le_div_iff₀ hx] at h
    have h1 : -(φ 0 - φ (-1)) * x ≤ |φ 0 - φ (-1)| * |x| := by
      rw [abs_of_pos hx]
      exact mul_le_mul_of_nonneg_right (by linarith [neg_abs_le (φ 0 - φ (-1))]) hx.le
    nlinarith

lemma lintegral_neg_ne_top {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {η : Measure ℝ}
    (hη : MartOT.Var.InM η) : ∫⁻ x, ENNReal.ofReal (-φ x) ∂η ≠ ⊤ := by
  obtain ⟨C, K, hCK⟩ := convex_lower_bound hφ
  have := hη.1
  have hint : Integrable (fun x : ℝ => C + K * |x|) η :=
    (integrable_const C).add ((hη.2.abs).const_mul K)
  refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne ?_
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hCK x)

lemma ereal_sub_le_iff (a b c d : ENNReal) (hb : b ≠ ⊤) (hd : d ≠ ⊤) :
    ((a : EReal) - b ≤ (c : EReal) - d) ↔ a + d ≤ c + b := by
  lift b to NNReal using hb
  lift d to NNReal using hd
  induction a using ENNReal.recTopCoe <;> induction c using ENNReal.recTopCoe
  · simp
  · rename_i c
    simp only [EReal.coe_nnreal_eq_coe_real, EReal.coe_ennreal_top]
    simp
    rw [← EReal.coe_sub]; exact EReal.coe_ne_top _
  · simp
  · rename_i a c
    rw [← ENNReal.coe_add, ← ENNReal.coe_add, ENNReal.coe_le_coe]
    simp only [EReal.coe_nnreal_eq_coe_real]
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff, ← NNReal.coe_le_coe,
      NNReal.coe_add, NNReal.coe_add]
    constructor <;> intro h <;> linarith


lemma integrable_of_parts {ρ : Measure ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (h1 : ∫⁻ x, ENNReal.ofReal (f x) ∂ρ ≠ ⊤) (h2 : ∫⁻ x, ENNReal.ofReal (-f x) ∂ρ ≠ ⊤) :
    Integrable f ρ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hb : ∀ x, ‖f x‖ₑ ≤ ENNReal.ofReal (f x) + ENNReal.ofReal (-f x) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_total (f x) 0 with h | h
    · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -f x ≤ 0), add_zero]
  calc ∫⁻ x, ‖f x‖ₑ ∂ρ ≤ ∫⁻ x, (ENNReal.ofReal (f x) + ENNReal.ofReal (-f x)) ∂ρ :=
        lintegral_mono hb
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂ρ + ∫⁻ x, ENNReal.ofReal (-f x) ∂ρ :=
        lintegral_add_left hf.measurable.ennreal_ofReal _
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨h1.lt_top, h2.lt_top⟩

end LC5Aux

open LC5Aux in
theorem solution (η η' : Measure ℝ) (h : MartOT.Var.ConvexLE η η') (ψ : ℝ → ℝ)
    (hψ : StrictConvexOn ℝ Set.univ ψ) :
    MartOT.Var.integralE η ψ ≤ MartOT.Var.integralE η' ψ ∧
      (MartOT.Var.integralE η' ψ < ⊤ → (MartOT.Var.integralE η ψ = MartOT.Var.integralE η' ψ ↔ η = η')) := by
  have hle := h.2.2 ψ hψ.convexOn
  refine ⟨hle, fun hfin => ⟨fun heq => ?_, fun he => by rw [he]⟩⟩
  obtain ⟨π, hπ⟩ := MartOT.Abs.theorem_2_6_sufficiency η η' h
  have : IsFiniteMeasure η := h.1.1
  have : IsFiniteMeasure η' := h.2.1.1
  have hfπ : IsFiniteMeasure π := isFinite_of_plan hπ.1
  have hψc : Continuous ψ := continuousOn_univ.mp (hψ.convexOn.continuousOn isOpen_univ)
  have hN := lintegral_neg_ne_top hψ.convexOn h.1
  have hN' := lintegral_neg_ne_top hψ.convexOn h.2.1
  rw [integralE_eq, integralE_eq] at heq
  rw [integralE_eq] at hfin
  have hP' : ∫⁻ x, ENNReal.ofReal (ψ x) ∂η' ≠ ⊤ := by
    intro hP
    rw [hP] at hfin
    lift (∫⁻ x, ENNReal.ofReal (-ψ x) ∂η') to NNReal using hN' with c
    simp at hfin
  have heq2 : ∫⁻ x, ENNReal.ofReal (ψ x) ∂η + ∫⁻ x, ENNReal.ofReal (-ψ x) ∂η' =
      ∫⁻ x, ENNReal.ofReal (ψ x) ∂η' + ∫⁻ x, ENNReal.ofReal (-ψ x) ∂η :=
    le_antisymm ((ereal_sub_le_iff _ _ _ _ hN hN').mp heq.le)
      ((ereal_sub_le_iff _ _ _ _ hN' hN).mp heq.ge)
  have hP : ∫⁻ x, ENNReal.ofReal (ψ x) ∂η ≠ ⊤ := by
    intro hP
    have : ∫⁻ x, ENNReal.ofReal (ψ x) ∂η' + ∫⁻ x, ENNReal.ofReal (-ψ x) ∂η = ⊤ := by
      rw [← heq2, hP, top_add]
    exact ENNReal.add_ne_top.mpr ⟨hP', hN⟩ this
  have hiη : Integrable ψ η := integrable_of_parts hψc hP hN
  have hiη' : Integrable ψ η' := integrable_of_parts hψc hP' hN'
  have hreal : ∫ x, ψ x ∂η = ∫ x, ψ x ∂η' := by
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiη,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hiη']
    have := congrArg ENNReal.toReal heq2
    rw [ENNReal.toReal_add hP hN', ENNReal.toReal_add hP' hN] at this
    linarith
  have hi1 : Integrable (fun p : ℝ × ℝ => ψ p.1) π := by
    rw [← hπ.1.1] at hiη
    exact (integrable_map_measure hψc.aestronglyMeasurable measurable_fst.aemeasurable).mp hiη
  have hi2 : Integrable (fun p : ℝ × ℝ => ψ p.2) π := by
    rw [← hπ.1.2] at hiη'
    exact (integrable_map_measure hψc.aestronglyMeasurable measurable_snd.aemeasurable).mp hiη'
  have hzero_total : ∫ p, (ψ p.2 - ψ p.1) ∂π = 0 := by
    rw [integral_sub hi2 hi1]
    have e1 : ∫ p, ψ p.1 ∂π = ∫ x, ψ x ∂η := by
      rw [← hπ.1.1, integral_map measurable_fst.aemeasurable hψc.aestronglyMeasurable]
    have e2 : ∫ p, ψ p.2 ∂π = ∫ y, ψ y ∂η' := by
      rw [← hπ.1.2, integral_map measurable_snd.aemeasurable hψc.aestronglyMeasurable]
    rw [e1, e2, hreal, sub_self]
  have hi21 : Integrable (fun p : ℝ × ℝ => ψ p.2 - ψ p.1) π := hi2.sub hi1
  -- the subgradient
  set g : ℝ → ℝ := fun x => derivWithin ψ (Set.Ioi x) x with hg
  have hgmono : Monotone g := by
    intro x y hxy
    exact hψ.convexOn.monotoneOn_rightDeriv (by simp : x ∈ interior Set.univ)
      (by simp : y ∈ interior Set.univ) hxy
  have hgm : Measurable g := hgmono.measurable
  have hstrict : ∀ x y, x ≠ y → ψ x + g x * (y - x) < ψ y := by
    intro x y hne
    rcases lt_or_gt_of_ne hne with hxy | hxy
    · have h := hψ.rightDeriv_lt_slope (Set.mem_univ x) (Set.mem_univ y) hxy
        (hψ.convexOn.differentiableWithinAt_Ioi_of_mem_interior (by simp))
      rw [slope_def_field, lt_div_iff₀ (sub_pos.mpr hxy)] at h
      show ψ x + derivWithin ψ (Set.Ioi x) x * (y - x) < ψ y
      linarith
    · have h1 := hψ.slope_lt_leftDeriv (Set.mem_univ y) (Set.mem_univ x) hxy
        (hψ.convexOn.differentiableWithinAt_Iio_of_mem_interior (by simp))
      have h2 := hψ.convexOn.leftDeriv_le_rightDeriv_of_mem_interior (by simp : x ∈ interior Set.univ)
      have h3 := lt_of_lt_of_le h1 h2
      rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hxy)] at h3
      show ψ x + derivWithin ψ (Set.Ioi x) x * (y - x) < ψ y
      nlinarith
  let D : ℝ × ℝ → ℝ := fun p => ψ p.2 - ψ p.1 - g p.1 * (p.2 - p.1)
  have hD0 : ∀ p, 0 ≤ D p := by
    intro p
    by_cases hp : p.1 = p.2
    · simp [D, hp]
    · have := hstrict p.1 p.2 hp; simp only [D]; linarith
  have hDm : Measurable D :=
    ((hψc.measurable.comp measurable_snd).sub (hψc.measurable.comp measurable_fst)).sub
      ((hgm.comp measurable_fst).mul (measurable_snd.sub measurable_fst))
  let E : ℕ → Set ℝ := fun M => {x | |g x| ≤ M}
  have hEm : ∀ M, MeasurableSet (E M) := fun M => measurableSet_le hgm.abs measurable_const
  have hmono : Monotone (fun M : ℕ => E M ×ˢ (Set.univ : Set ℝ)) := by
    intro m n hmn
    refine Set.prod_mono (fun x hx => ?_) le_rfl
    show |g x| ≤ (n:ℝ)
    exact le_trans hx (by exact_mod_cast hmn)
  have hU : (⋃ M : ℕ, E M ×ˢ (Set.univ : Set ℝ)) = Set.univ := by
    ext ⟨x, y⟩
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_univ, and_true, iff_true, E,
      Set.mem_ofPred_eq]
    exact exists_nat_ge |g x|
  have ha : ∀ M : ℕ, ∫⁻ p in E M ×ˢ Set.univ, ENNReal.ofReal (D p) ∂π =
      ENNReal.ofReal (∫ p in E M ×ˢ Set.univ, (ψ p.2 - ψ p.1) ∂π) := by
    intro M
    let ρ : ℝ → ℝ := (E M).indicator g
    have hρm : Measurable ρ := hgm.indicator (hEm M)
    have hρb : ∀ x, |ρ x| ≤ M := by
      intro x; simp only [ρ, Set.indicator]
      split_ifs with hx
      · exact hx
      · simp
    let hh : ℝ × ℝ → ℝ := fun p => ρ p.1 * (p.2 - p.1)
    have hint : Integrable hh π := by
      refine hπ.2.1.bdd_mul (c := M) (hρm.comp measurable_fst).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun p => by
        simpa [Real.norm_eq_abs] using hρb p.1
    have hzero : ∫ p, hh p ∂π = 0 := hπ.2.2 ρ hρm ⟨M, hρb⟩
    have hS : MeasurableSet (E M ×ˢ (Set.univ : Set ℝ)) := (hEm M).prod MeasurableSet.univ
    have hEq : Set.EqOn (fun p => (ψ p.2 - ψ p.1) - hh p) D (E M ×ˢ Set.univ) := by
      intro p hp
      have hρ : ρ p.1 = g p.1 := Set.indicator_of_mem hp.1 g
      simp only [D, hh, hρ]
    have hiD : IntegrableOn D (E M ×ˢ Set.univ) π :=
      (hi21.sub hint).integrableOn.congr_fun hEq hS
    rw [← ofReal_integral_eq_lintegral_ofReal hiD (Eventually.of_forall hD0)]
    congr 1
    rw [← setIntegral_congr_fun hS hEq, integral_sub hi21.integrableOn hint.integrableOn]
    have : ∫ p in E M ×ˢ Set.univ, hh p ∂π = 0 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hzero
      · intro p hp
        have hp1 : p.1 ∉ E M := fun h1 => hp ⟨h1, Set.mem_univ _⟩
        simp [hh, ρ, Set.indicator_of_notMem hp1]
    rw [this, sub_zero]
  have hlimit : Tendsto (fun M : ℕ => ∫ p in E M ×ˢ Set.univ, (ψ p.2 - ψ p.1) ∂π) atTop
      (nhds (∫ p, (ψ p.2 - ψ p.1) ∂π)) := by
    have := tendsto_setIntegral_of_monotone (μ := π) (f := fun p : ℝ × ℝ => ψ p.2 - ψ p.1)
      (fun M => (hEm M).prod MeasurableSet.univ) hmono hi21.integrableOn
    rwa [hU, Measure.restrict_univ] at this
  have hlin : ∫⁻ p, ENNReal.ofReal (D p) ∂π = 0 := by
    have hmonoL : Monotone (fun M : ℕ => ∫⁻ p in E M ×ˢ Set.univ, ENNReal.ofReal (D p) ∂π) :=
      fun m n hmn => lintegral_mono_set (hmono hmn)
    have h1 : ∫⁻ p, ENNReal.ofReal (D p) ∂π =
        ⨆ M : ℕ, ∫⁻ p in E M ×ˢ Set.univ, ENNReal.ofReal (D p) ∂π := by
      rw [← setLIntegral_iUnion_of_directed _ hmono.directed_le, hU, Measure.restrict_univ]
    have h2 : Tendsto (fun M : ℕ => ∫⁻ p in E M ×ˢ Set.univ, ENNReal.ofReal (D p) ∂π) atTop
        (nhds 0) := by
      simp_rw [ha]
      rw [← ENNReal.ofReal_zero, ← hzero_total]
      exact (ENNReal.continuous_ofReal.tendsto _).comp hlimit
    rw [h1]; exact tendsto_nhds_unique (tendsto_atTop_iSup hmonoL) h2
  have hDae := (lintegral_eq_zero_iff hDm.ennreal_ofReal).mp hlin
  have hdiag : ∀ᵐ p ∂π, p.1 = p.2 := by
    filter_upwards [hDae] with p hp
    by_contra hne
    have := hstrict p.1 p.2 hne
    have hpos : 0 < D p := by simp only [D]; linarith
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hp
    linarith
  ext B hB
  rw [← hπ.1.1, ← hπ.1.2, Measure.map_apply measurable_fst hB, Measure.map_apply measurable_snd hB]
  apply measure_congr
  filter_upwards [hdiag] with p hp
  show (p.1 ∈ B) = (p.2 ∈ B)
  rw [hp]
