-- Prove2me | solution 1 for MartOT.Product.theorem_4_18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T05:33:27.850588+00:00
-- url     : https://prove2.me/submissions/3c9000d2-7a1c-467b-baf9-5026dcc80900
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Curtain_theorem_4_18

open MeasureTheory

namespace LC5Scale

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


variable {a : ENNReal}

lemma fin_smul {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] (ha : a ≠ ⊤) :
    IsFiniteMeasure (a • μ) :=
  ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ha.lt_top (measure_lt_top _ _)⟩

lemma inM_smul (ha : a ≠ ⊤) {μ : Measure ℝ} (h : MartOT.Var.InM μ) : MartOT.Var.InM (a • μ) := by
  have := h.1
  exact ⟨fin_smul μ ha, h.2.smul_measure ha⟩

lemma smul_le' {X : Type*} [MeasurableSpace X] {η ν : Measure X} (h : η ≤ ν) : a • η ≤ a • ν :=
  Measure.le_iff'.mpr fun s => by
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
    all_goals exact Measure.le_iff'.mp h s

lemma inv_smul_cancel' {X : Type*} [MeasurableSpace X] (ha0 : a ≠ 0) (ha : a ≠ ⊤) (ρ : Measure X) :
    a⁻¹ • a • ρ = ρ := by
  rw [smul_smul, ENNReal.inv_mul_cancel ha0 ha, one_smul]

lemma smul_inv_cancel' {X : Type*} [MeasurableSpace X] (ha0 : a ≠ 0) (ha : a ≠ ⊤) (ρ : Measure X) :
    a • a⁻¹ • ρ = ρ := by
  rw [smul_smul, ENNReal.mul_inv_cancel ha0 ha, one_smul]

lemma convexLE_smul (ha : a ≠ ⊤) {μ η : Measure ℝ} (h : MartOT.Var.ConvexLE μ η) :
    MartOT.Var.ConvexLE (a • μ) (a • η) := by
  refine ⟨inM_smul ha h.1, inM_smul ha h.2.1, fun φ hφ => ?_⟩
  have h1 := h.2.2 φ hφ
  have hN := lintegral_neg_ne_top hφ h.1
  have hN' := lintegral_neg_ne_top hφ h.2.1
  rw [integralE_eq, integralE_eq] at h1 ⊢
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [ereal_sub_le_iff _ _ _ _ (ENNReal.mul_ne_top ha hN) (ENNReal.mul_ne_top ha hN')]
  rw [ereal_sub_le_iff _ _ _ _ hN hN'] at h1
  rw [← mul_add, ← mul_add]
  gcongr

lemma shadow_smul (ha0 : a ≠ 0) (ha : a ≠ ⊤) {ν μ η : Measure ℝ} (h : MartOT.Var.IsShadow ν μ η) :
    MartOT.Var.IsShadow (a • ν) (a • μ) (a • η) := by
  refine ⟨smul_le' h.1, convexLE_smul ha h.2.1, fun η' h1 h2 => ?_⟩
  have hinvt : a⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr ha0
  have h3 : a⁻¹ • η' ≤ ν := by
    have := smul_le' (a := a⁻¹) h1; rwa [inv_smul_cancel' ha0 ha] at this
  have h4 : MartOT.Var.ConvexLE μ (a⁻¹ • η') := by
    have := convexLE_smul hinvt h2; rwa [inv_smul_cancel' ha0 ha] at this
  have := convexLE_smul ha (h.2.2 _ h3 h4)
  rwa [smul_inv_cancel' ha0 ha] at this

lemma lc_smul (ha0 : a ≠ 0) (ha : a ≠ ⊤) {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (h : MartOT.Var.IsLeftCurtain μ ν π) : MartOT.Var.IsLeftCurtain (a • μ) (a • ν) (a • π) := by
  have := h.1
  refine ⟨fin_smul π ha, fun x => ⟨?_, ?_⟩⟩
  · rw [Measure.restrict_smul, Measure.map_smul, (h.2 x).1, Measure.restrict_smul]
  · have := shadow_smul ha0 ha (h.2 x).2
    unfold MartOT.Var.targetUpTo at *
    simp only [Measure.restrict_smul, Measure.map_smul] at this ⊢
    exact this

lemma mart_smul (ha : a ≠ ⊤) {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (h : MartOT.Var.IsMartingalePlan μ ν π) : MartOT.Var.IsMartingalePlan (a • μ) (a • ν) (a • π) := by
  refine ⟨⟨by rw [Measure.map_smul, h.1.1], by rw [Measure.map_smul, h.1.2]⟩,
    h.2.1.smul_measure ha, fun ρ hρ hb => ?_⟩
  rw [integral_smul_measure, h.2.2 ρ hρ hb, smul_zero]

lemma convexLE_zero : MartOT.Var.ConvexLE 0 0 :=
  ⟨⟨inferInstance, integrable_zero_measure⟩, ⟨inferInstance, integrable_zero_measure⟩,
    fun _ _ => le_rfl⟩

lemma mass_eq {μ ν : Measure ℝ} (h : MartOT.Var.ConvexLE μ ν) : ν Set.univ = μ Set.univ := by
  have := h.1.1
  have := h.2.1.1
  have hc1 : ConvexOn ℝ Set.univ (fun _ : ℝ => (1:ℝ)) := convexOn_const _ convex_univ
  have hc2 : ConvexOn ℝ Set.univ (fun _ : ℝ => (-1:ℝ)) := convexOn_const _ convex_univ
  have h1 := h.2.2 _ hc1
  have h2 := h.2.2 _ hc2
  rw [integralE_eq, integralE_eq] at h1 h2
  simp only [neg_neg, ENNReal.ofReal_one, lintegral_const, one_mul, Measure.restrict_univ,
    ENNReal.ofReal_of_nonpos (by norm_num : (-1:ℝ) ≤ 0), zero_mul, lintegral_zero] at h1 h2
  rw [ereal_sub_le_iff _ _ _ _ (by simp) (by simp)] at h1
  rw [ereal_sub_le_iff _ _ _ _ (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  simp only [add_zero, zero_add] at h1 h2
  exact le_antisymm h2 h1

end LC5Scale

open LC5Scale in
theorem solution (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) :
    (∃! π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π) ∧
      ∀ π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π → MartOT.Var.IsMartingalePlan μ ν π := by
  have := hμν.1.1
  have := hμν.2.1.1
  have hmass := mass_eq hμν
  by_cases hm : μ Set.univ = 0
  · have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.mp hm
    have hν0 : ν = 0 := Measure.measure_univ_eq_zero.mp (hmass ▸ hm)
    subst hμ0 hν0
    have key : ∀ π, MartOT.Var.IsLeftCurtain 0 0 π → π = 0 := by
      intro π hπ
      have hx : ∀ x : ℝ, π (Set.Iic x ×ˢ Set.univ) = 0 := by
        intro x
        have := congrArg (fun m : Measure ℝ => m Set.univ) (hπ.2 x).1
        simp only [Measure.restrict_zero, Measure.coe_zero, Pi.zero_apply] at this
        rwa [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
          Measure.restrict_apply_univ] at this
      apply Measure.measure_univ_eq_zero.mp
      have hU : (Set.univ : Set (ℝ × ℝ)) = ⋃ n : ℕ, Set.Iic (n:ℝ) ×ˢ Set.univ := by
        ext ⟨x, y⟩
        simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_prod, Set.mem_Iic, and_true, true_iff]
        exact exists_nat_ge x
      rw [hU]
      exact measure_iUnion_null fun n => hx n
    have lc0 : MartOT.Var.IsLeftCurtain 0 0 0 := by
      refine ⟨inferInstance, fun x => ⟨by simp, ?_⟩⟩
      have e : MartOT.Var.targetUpTo 0 x = 0 := by unfold MartOT.Var.targetUpTo; simp
      rw [e, Measure.restrict_zero]
      exact ⟨le_rfl, convexLE_zero, fun η' h1 _ => by rw [le_antisymm h1 (Measure.zero_le _)]; exact convexLE_zero⟩
    refine ⟨⟨0, lc0, fun π hπ => key π hπ⟩, fun π hπ => ?_⟩
    rw [key π hπ]
    exact ⟨⟨by simp, by simp⟩, integrable_zero_measure, fun ρ _ _ => integral_zero_measure _⟩
  · set m := μ Set.univ with hmdef
    have hmt : m ≠ ⊤ := measure_ne_top μ _
    have ha0 : m⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmt
    have hat : m⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hm
    have hP1 : IsProbabilityMeasure (m⁻¹ • μ) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.inv_mul_cancel hm hmt⟩
    have hP2 : IsProbabilityMeasure (m⁻¹ • ν) :=
      ⟨by rw [Measure.smul_apply, smul_eq_mul, hmass]; exact ENNReal.inv_mul_cancel hm hmt⟩
    obtain ⟨⟨π1, h1, huniq⟩, hmart⟩ :=
      MartOT.Curtain.theorem_4_18 (m⁻¹ • μ) (m⁻¹ • ν) (convexLE_smul hat hμν)
    have e : ∀ {X : Type} [MeasurableSpace X] (ρ : Measure X), m • m⁻¹ • ρ = ρ := by
      intro X _ ρ
      rw [smul_smul, ENNReal.mul_inv_cancel hm hmt, one_smul]
    have e' : ∀ {X : Type} [MeasurableSpace X] (ρ : Measure X), m⁻¹ • m • ρ = ρ := by
      intro X _ ρ
      rw [smul_smul, ENNReal.inv_mul_cancel hm hmt, one_smul]
    refine ⟨⟨m • π1, ?_, fun π hπ => ?_⟩, fun π hπ => ?_⟩
    · have := lc_smul hm hmt h1; rwa [e, e] at this
    · have h2 := lc_smul ha0 hat hπ
      have := huniq _ h2
      rw [← this, e]
    · have h2 := lc_smul ha0 hat hπ
      have h3 := mart_smul hmt (hmart _ h2).2
      rwa [e, e, e] at h3
