-- Prove2me | solution 1 for MultistageStochastic.avar_dual_representation
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:10:07.726986+00:00
-- url     : https://prove2.me/submissions/a6cd5eb4-dfbf-4e19-86f5-46fe4aed0999

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion

open MeasureTheory
open scoped ENNReal

namespace AvarCexA338

open MultistageStochastic

/-- Two-point probability space: `false` has mass 1/4, `true` has mass 3/4. -/
noncomputable def Pb : Measure Bool :=
  ENNReal.ofReal (1/4) • Measure.dirac false + ENNReal.ofReal (3/4) • Measure.dirac true

theorem quarter_add : ENNReal.ofReal (1/4) + ENNReal.ofReal (3/4) = 1 := by
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

theorem Pb_le (f : Bool → ℝ) (y : ℝ) :
    Pb {ω | f ω ≤ y} = (if f false ≤ y then ENNReal.ofReal (1/4) else 0)
      + (if f true ≤ y then ENNReal.ofReal (3/4) else 0) := by
  unfold Pb
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply,
    Measure.dirac_apply, smul_eq_mul, smul_eq_mul]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  split_ifs <;> simp

instance : IsProbabilityMeasure Pb := ⟨by
  have := Pb_le (fun _ => 0) 0
  simp only [le_refl, if_true, quarter_add] at this
  simpa using this⟩

theorem Pb_false : Pb {false} = ENNReal.ofReal (1/4) := by
  unfold Pb
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply,
    Measure.dirac_apply, smul_eq_mul, smul_eq_mul]
  simp

theorem Pb_true : Pb {true} = ENNReal.ofReal (3/4) := by
  unfold Pb
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply,
    Measure.dirac_apply, smul_eq_mul, smul_eq_mul]
  simp

theorem var_eq (f : Bool → ℝ) (hf : f false ≤ f true) {p : ℝ} (hp : 1/4 < p) (hp1 : p ≤ 1) :
    valueAtRisk Pb f p = f true := by
  unfold valueAtRisk
  have hS : {y : ℝ | ENNReal.ofReal p ≤ Pb {ω | f ω ≤ y}} = Set.Ici (f true) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_Ici, Pb_le]
    constructor
    · intro h
      by_contra hy
      push_neg at hy
      rw [if_neg (not_le.mpr hy)] at h
      split_ifs at h with h1
      · rw [add_zero, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h
        linarith
      · rw [add_zero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h
        linarith
    · intro hy
      rw [if_pos (le_trans hf hy), if_pos hy, quarter_add]
      exact ENNReal.ofReal_le_one.mpr hp1
  rw [hS, csInf_Ici]

theorem ess_le (f : Bool → ℝ) {c : ℝ} (h : essSupBook Pb f ≤ c) : f true ≤ c := by
  unfold essSupBook at h
  by_contra hc
  push_neg at hc
  have hy : (c + f true) / 2 ∈ {y : ℝ | Pb {ω | f ω ≤ y} < 1} := by
    simp only [Set.mem_setOf_eq, Pb_le]
    rw [if_neg (by linarith : ¬ f true ≤ (c + f true) / 2), add_zero]
    split_ifs
    · rw [ENNReal.ofReal_lt_one]; norm_num
    · exact zero_lt_one
  have hb : BddAbove {y : ℝ | Pb {ω | f ω ≤ y} < 1} := by
    refine ⟨max (f false) (f true), fun z hz => ?_⟩
    by_contra hz'
    push_neg at hz'
    simp only [Set.mem_setOf_eq, Pb_le] at hz
    rw [if_pos (by linarith [le_max_left (f false) (f true)]),
      if_pos (by linarith [le_max_right (f false) (f true)]), quarter_add] at hz
    exact lt_irrefl _ hz
  have := le_csSup hb hy
  linarith

theorem ess_eq_le (f : Bool → ℝ) (hf : f false ≤ f true) : essSupBook Pb f ≤ f true := by
  unfold essSupBook
  apply csSup_le
  · refine ⟨f false - 1, ?_⟩
    simp only [Set.mem_setOf_eq, Pb_le]
    rw [if_neg (by linarith), if_neg (by linarith)]
    simp
  · intro z hz
    by_contra hz'
    push_neg at hz'
    simp only [Set.mem_setOf_eq, Pb_le] at hz
    rw [if_pos (by linarith), if_pos (by linarith), quarter_add] at hz
    exact lt_irrefl _ hz

theorem int_eq (f : Bool → ℝ) : ∫ ω, f ω ∂Pb = 1/4 * f false + 3/4 * f true := by
  rw [integral_fintype Integrable.of_finite]
  simp only [Fintype.sum_bool, smul_eq_mul, measureReal_def, Pb_false, Pb_true]
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
  ring

/-- The loss `Y`: `-1` on the light point, `0` on the heavy point. -/
noncomputable def Yb : Bool → ℝ := fun b => if b then 0 else -1

/-- The density `Z`: `-2` on the light point, `2` on the heavy point. -/
noncomputable def Zb : Bool → ℝ := fun b => if b then 2 else -2

theorem avar_Y : averageValueAtRisk Pb Yb (1/2) = 0 := by
  unfold averageValueAtRisk
  rw [if_neg (by norm_num)]
  have : ∫ p in Set.Ioo (1/2 : ℝ) 1, valueAtRisk Pb Yb p = ∫ p in Set.Ioo (1/2 : ℝ) 1, (0 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro p hp
    rw [var_eq Yb (by simp [Yb]) (by linarith [hp.1]) hp.2.le]
    simp [Yb]
  rw [this]; simp

theorem avar_Z (p : ℝ) (hp : 1/2 ≤ p) (hp1 : p ≤ 1) :
    averageValueAtRisk Pb Zb p ≤ (1 - 1/2)⁻¹ := by
  unfold averageValueAtRisk
  split_ifs with h
  · have := ess_eq_le Zb (by norm_num [Zb])
    simp [Zb] at this ⊢
    norm_num at this ⊢
    linarith
  · have hlt : p < 1 := lt_of_le_of_ne hp1 h
    have : ∫ q in Set.Ioo p 1, valueAtRisk Pb Zb q = ∫ q in Set.Ioo p 1, (2 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro q hq
      rw [var_eq Zb (by norm_num [Zb]) (by linarith [hq.1]) hq.2.le]
      simp [Zb]
    rw [this, setIntegral_const, Real.volume_real_Ioo_of_le hlt.le, smul_eq_mul]
    have h1 : (1 - p) ≠ 0 := by linarith
    rw [← mul_assoc, inv_mul_cancel₀ h1]
    norm_num

end AvarCexA338

open MeasureTheory MultistageStochastic AvarCexA338 in
theorem solution : ¬ (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : MemLinfty P Y) (α : ℝ) (hα : 0 ≤ α),
    (α < 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
            ∀ p : ℝ, α ≤ p → p ≤ 1 → averageValueAtRisk P Z p ≤ (1 - α)⁻¹},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) ∧
    (α < 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
            ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ (1 - α)⁻¹},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) ∧
    (α = 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P)) := by
  intro h
  have hY : MemLinfty Pb Yb :=
    ⟨measurable_of_finite _, 1, Filter.Eventually.of_forall (fun b => by cases b <;> simp [Yb])⟩
  have h1 := (h Pb Yb hY (1/2) (by norm_num)).1 (by norm_num)
  rw [avar_Y] at h1
  let Z0 : {Z : Bool → ℝ // Integrable Z Pb ∧ ∫ ω, Z ω ∂Pb = 1 ∧
      ∀ p : ℝ, 1/2 ≤ p → p ≤ 1 → averageValueAtRisk Pb Z p ≤ (1 - 1/2)⁻¹} :=
    ⟨Zb, Integrable.of_finite, by rw [int_eq]; simp [Zb]; norm_num, avar_Z⟩
  have hbdd : BddAbove (Set.range fun Z : {Z : Bool → ℝ // Integrable Z Pb ∧ ∫ ω, Z ω ∂Pb = 1 ∧
      ∀ p : ℝ, 1/2 ≤ p → p ≤ 1 → averageValueAtRisk Pb Z p ≤ (1 - 1/2)⁻¹} =>
        ∫ ω, Yb ω * (Z : Bool → ℝ) ω ∂Pb) := by
    refine ⟨1/2, ?_⟩
    rintro _ ⟨Z, rfl⟩
    have hc := Z.2.2.2 1 (by norm_num) le_rfl
    unfold averageValueAtRisk at hc
    rw [if_pos rfl] at hc
    have ht := ess_le _ hc
    have hm := Z.2.2.1
    rw [int_eq] at hm
    simp only
    rw [int_eq]
    simp [Yb]
    norm_num at ht
    linarith
  have hle := le_ciSup hbdd Z0
  rw [← h1] at hle
  have : ∫ ω, Yb ω * (Z0 : Bool → ℝ) ω ∂Pb = 1/2 := by
    rw [int_eq]; simp [Yb, Z0, Zb]; norm_num
  linarith
