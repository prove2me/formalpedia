-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.nonempty_weights
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:52:12.768801+00:00
-- url     : https://prove2.me/submissions/01131ef0-2ffe-410d-b386-068fcbbf0fa7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_CurvatureFamilyNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
theorem _root_.solution (X : Data E r) (h : Shape X) : Nonempty (Weights X) := by
  obtain ⟨T, hT1, hT2, hT3, hT4, hT5⟩ : ∃ T : ℕ,
      (nd X + 2) * (2 * (4 * X.Ψ.card * r + 2)) + 2 * r ≤ T ∧ 40 * (nd X + 2) ≤ T ∧
      11 * nd X ^ 2 ≤ T ∧ bb X < T ∧ bb X ^ 2 * Crh X + bb X < T := by
    obtain ⟨n, hn⟩ := exists_nat_gt (bb X)
    obtain ⟨m, hm⟩ := exists_nat_gt (bb X ^ 2 * Crh X + bb X)
    refine ⟨(nd X + 2) * (2 * (4 * X.Ψ.card * r + 2)) + 2 * r + 40 * (nd X + 2) + 11 * nd X ^ 2 + n + m,
      by omega, by omega, by omega, hn.trans_le (by exact_mod_cast (by omega)),
      hm.trans_le (by exact_mod_cast (by omega))⟩
  have hp := h.p0_pos
  have hq := h.witt
  have hr := h.r_ge
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hg : (0 : ℝ) < g0 r := by
    have : 0 < g0 r := by simp only [g0, g0half]; omega
    exact_mod_cast this
  set A : ℝ := (T : ℝ) * g0 r with hA
  set B : ℝ := (g0 r : ℝ) * X.Ψ.card * (X.p0 : ℝ) ^ 3 * RR X ^ 2 with hB
  have hA0 : 0 < A := by positivity
  have hB0 : 0 ≤ B := by positivity
  let Tp : ℤ := T + nd X + 2
  let g : ℤ := Tp + 2 * r
  let aW : Wt X.Ψ r := fun _ a =>
    if (a : ℕ) < X.p0 then -(2 * (T : ℤ)) - g * (a : ℕ) else 2 * T + g * ((r : ℤ) - 1 - (a : ℕ))
  let s : Wt X.Ψ r := fun _ a =>
    if (a : ℕ) < X.p0 then 2 * ((a : ℕ) : ℤ) else
      ((nd X : ℤ) + 2) * (2 * ((4 * X.Ψ.card * r + 2 : ℕ) : ℤ)) + 2 * r - 2 * ((r : ℤ) - 1 - (a : ℕ))
  have hTp : (0 : ℤ) < T + nd X + 2 := by positivity
  have hgap : ∀ τ a b, IsGap X a b → aW τ a - aW τ b = g ∧ s τ a - s τ b = -2 := by
    rintro τ a b ⟨h1, h2⟩
    have e : ((b : ℕ) : ℤ) = (a : ℕ) + 1 := by omega
    by_cases ha : (a : ℕ) < X.p0
    · have hb : (b : ℕ) < X.p0 := by omega
      simp only [aW, s, if_pos ha, if_pos hb, e]
      constructor <;> ring
    · have hb : ¬ (b : ℕ) < X.p0 := by omega
      simp only [aW, s, if_neg ha, if_neg hb, e]
      constructor <;> ring
  have hplus : ∀ τ (a : Fin r), (a : ℕ) + 1 = r → aW τ a = 2 * T ∧
      s τ a = ((nd X : ℤ) + 2) * (2 * ((4 * X.Ψ.card * r + 2 : ℕ) : ℤ)) + 2 * r := by
    intro τ a ha
    have e : ((a : ℕ) : ℤ) = r - 1 := by omega
    have hb : ¬ (a : ℕ) < X.p0 := by omega
    simp only [aW, s, if_neg hb, e]
    constructor <;> ring
  have hminus : ∀ τ (a : Fin r), (a : ℕ) = 0 → aW τ a = -(2 * T) ∧ s τ a = 0 := by
    intro τ a ha
    have hb : (a : ℕ) < X.p0 := by omega
    simp only [aW, s, if_pos hb]
    rw [ha]
    constructor <;> simp
  have hD : (0 : ℝ) ≤ nd X := by positivity
  refine ⟨{
    shape := h, T := T, i := 1, c := 1 / (A + B), hW := 4 * X.Ψ.card * r + 2, hF := 4 * X.Ψ.card * r + 2
    aK := fun τ a => Tp * aW τ a + s τ a, aW := aW
    i_pos := one_pos, c_pos := by positivity, T_cols := hT1, T_forty := hT2, T_sq := hT3
    cols_lo := by apply le_of_eq; ring
    cols_hi := le_rfl
    Tcg := ?_, cRR := ?_, b_cut := by linarith, b_onto := by nlinarith
    gap_big := ?_, plus_big := ?_, minus_big := ?_, gap_div := ?_, plus_div := ?_, minus_div := ?_ }⟩
  · have : (T : ℝ) * (1 / (A + B)) * g0 r = A / (A + B) := by rw [hA]; ring
    rw [this, div_le_one (by positivity)]; linarith
  · rw [← hB, mul_one_div, div_le_one (by positivity)]; linarith
  · intro τ a b hab
    obtain ⟨h1, h2⟩ := hgap τ a b hab
    apply le_of_eq
    simp only [Tp, g] at h1 ⊢
    linear_combination (-((T : ℤ) + nd X + 2)) * h1 - h2
  · intro τ a ha
    obtain ⟨h1, h2⟩ := hplus τ a ha
    simp only [h1, h2, Tp]
    have : (0 : ℤ) ≤ ((nd X : ℤ) + 2) * (2 * ((4 * X.Ψ.card * r + 2 : ℕ) : ℤ)) + 2 * r := by positivity
    have : (0 : ℤ) ≤ (T : ℤ) * (nd X + 2) := by positivity
    nlinarith
  · intro τ a ha
    obtain ⟨h1, h2⟩ := hminus τ a ha
    simp only [h1, h2, Tp]
    have : (0 : ℤ) ≤ (T : ℤ) * (nd X + 2) := by positivity
    nlinarith
  · intro τ a b hab
    obtain ⟨h1, h2⟩ := hgap τ a b hab
    have : Tp * aW τ a + s τ a - (Tp * aW τ b + s τ b) + 2 -
        ((T : ℤ) + nd X + 2) * (aW τ a - aW τ b) = 0 := by
      simp only [Tp]; linear_combination h2
    rw [this]; exact ⟨le_rfl, hTp⟩
  · intro τ a ha
    obtain ⟨h1, h2⟩ := hplus τ a ha
    have : Tp * aW τ a + s τ a - ((T : ℤ) + nd X + 2) * aW τ a -
        ((nd X : ℤ) + 2) * (2 * ((4 * X.Ψ.card * r + 2 : ℕ) : ℤ)) - 2 * r = 0 := by
      simp only [Tp]; linear_combination h2
    rw [this]; exact ⟨le_rfl, hTp⟩
  · intro τ a ha
    obtain ⟨h1, h2⟩ := hminus τ a ha
    have : -(Tp * aW τ a + s τ a) - ((T : ℤ) + nd X + 2) * (-aW τ a) = 0 := by
      simp only [Tp]; linear_combination -h2
    rw [this]; exact ⟨le_rfl, hTp⟩
end GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm
