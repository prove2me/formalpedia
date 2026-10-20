-- Prove2me | solution 2 for OAI.SingleFold.HeightWindow.square_window
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:27:14.654991+00:00
-- url     : https://prove2.me/submissions/c23ff3ba-db50-4b53-82f9-9f5b607cb95f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/HeightGrowth.lean:L233-L277
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.HeightWindow.square_window. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion

-- ---- from OAI.NumberTheory.SingleFold.HeightGrowth ----
namespace OAI

namespace SingleFold.GrowthEstimate
open Filter
open scoped Topology

variable {W : ℕ → ℕ} {a c : ℝ}

end SingleFold.GrowthEstimate

namespace SingleFold.HeightWindow

lemma index_separation {k r : ℕ} (h : r ≠ k ^ 2) :
    1 ≤ |(k : ℝ) ^ 2 - (r : ℝ)| := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have : (r : ℝ) + 1 ≤ (k : ℝ) ^ 2 := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (k : ℝ) ^ 2 + 1 ≤ (r : ℝ) := by exact_mod_cast hgt
    rw [abs_of_nonpos (by linarith)]
    linarith

lemma separated_window {a c K e : ℝ} {k r : ℕ}
    (hc : 0 ≤ c) (hK : 6 * c < K) (ha : K < 2 * a - 6 * c)
    (he : |e| ≤ 6 * c) :
    |2 * a * ((k : ℝ) ^ 2 - (r : ℝ)) + e| ≤ K ↔ r = k ^ 2 := by
  have ha0 : 0 < a := by linarith
  constructor
  · intro hwin
    by_contra hne
    have hsep := index_separation hne
    have htri := abs_add_le ((2 * a * ((k : ℝ) ^ 2 - (r : ℝ))) + e) (-e)
    have hb : |2 * a * ((k : ℝ) ^ 2 - (r : ℝ))| ≤ K + 6 * c := by
      calc
        |2 * a * ((k : ℝ) ^ 2 - (r : ℝ))| =
            |(2 * a * ((k : ℝ) ^ 2 - (r : ℝ)) + e) + -e| := by congr 1; ring
        _ ≤ |2 * a * ((k : ℝ) ^ 2 - (r : ℝ)) + e| + |-e| := htri
        _ ≤ K + 6 * c := by rw [abs_neg]; linarith
    rw [abs_mul, abs_of_pos (show 0 < 2 * a by positivity)] at hb
    nlinarith
  · intro h
    subst r
    simp only [Nat.cast_pow, sub_self, mul_zero, zero_add]
    exact he.trans hK.le

lemma multiplicative_window {L D K : ℝ} (hL : 0 < L) (hD : 0 < D) (hK : 0 < K) :
    (L ≤ K * D ∧ D ≤ K * L) ↔ |Real.log L - Real.log D| ≤ Real.log K := by
  rw [abs_sub_le_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    have h₁' := Real.log_le_log hL h₁
    have h₂' := Real.log_le_log hD h₂
    rw [Real.log_mul hK.ne' hD.ne'] at h₁'
    rw [Real.log_mul hK.ne' hL.ne'] at h₂'
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor
    · apply (Real.log_le_log_iff hL (mul_pos hK hD)).mp
      rw [Real.log_mul hK.ne' hD.ne']
      linarith
    · apply (Real.log_le_log_iff hD (mul_pos hK hL)).mp
      rw [Real.log_mul hK.ne' hL.ne']
      linarith

theorem square_window {W : ℕ → ℕ} {a c : ℝ} {κ k r : ℕ}
    (hW : ∀ j, 0 < W j)
    (happrox : ∀ j, 1 ≤ j → |Real.log (W j : ℝ) - a * (j : ℝ) ^ 2| ≤ c)
    (hc : 0 ≤ c) (hκ : 0 < κ) (h₁ : 6 * c < Real.log κ)
    (h₂ : Real.log κ < 2 * a - 6 * c) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    (W (2 * k) * W r * W 1 ≤ κ * (W k ^ 2 * W (r + 1)) ∧
      W k ^ 2 * W (r + 1) ≤ κ * (W (2 * k) * W r * W 1)) ↔ r = k ^ 2 := by
  have pos (j : ℕ) : (0 : ℝ) < W j := by exact_mod_cast hW j
  let L : ℝ := (W (2 * k) : ℝ) * W r * W 1
  let D : ℝ := (W k : ℝ) ^ 2 * W (r + 1)
  have hL : 0 < L := mul_pos (mul_pos (pos _) (pos _)) (pos _)
  have hD : 0 < D := mul_pos (pow_pos (pos _) _) (pos _)
  have prod_iff :
      (W (2 * k) * W r * W 1 ≤ κ * (W k ^ 2 * W (r + 1)) ∧
        W k ^ 2 * W (r + 1) ≤ κ * (W (2 * k) * W r * W 1)) ↔
      (L ≤ (κ : ℝ) * D ∧ D ≤ (κ : ℝ) * L) := by
    dsimp [L, D]
    constructor <;> rintro ⟨h, h'⟩
    · exact ⟨by exact_mod_cast h, by exact_mod_cast h'⟩
    · exact ⟨by exact_mod_cast h, by exact_mod_cast h'⟩
  rw [prod_iff, multiplicative_window hL hD (by exact_mod_cast hκ)]
  let err (j : ℕ) := Real.log (W j : ℝ) - a * (j : ℝ) ^ 2
  have herr (j : ℕ) (hj : 1 ≤ j) : -c ≤ err j ∧ err j ≤ c :=
    abs_le.mp (happrox j hj)
  have herr2k := herr (2 * k) (by omega)
  have herrr := herr r hr
  have herr1 := herr 1 (by omega)
  have herrk := herr k hk
  have herrr1 := herr (r + 1) (by omega)
  let e := err (2 * k) + err r + err 1 - 2 * err k - err (r + 1)
  have he : |e| ≤ 6 * c := by
    apply abs_le.mpr
    dsimp [e]
    constructor <;> linarith [herr2k.1, herr2k.2, herrr.1, herrr.2,
      herr1.1, herr1.2, herrk.1, herrk.2, herrr1.1, herrr1.2]
  have formula : Real.log L - Real.log D =
      2 * a * ((k : ℝ) ^ 2 - (r : ℝ)) + e := by
    dsimp [L, D, e, err]
    rw [Real.log_mul (mul_pos (pos _) (pos _)).ne' (pos _).ne',
      Real.log_mul (pos _).ne' (pos _).ne',
      Real.log_mul (pow_pos (pos _) _).ne' (pos _).ne', Real.log_pow]
    push_cast
    ring
  rw [formula]
  exact separated_window hc h₁ h₂ he

end SingleFold.HeightWindow

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.HeightWindow


theorem solution : type_of% @_root_.OAI.SingleFold.HeightWindow.square_window := @_root_.OAI.SingleFold.HeightWindow.square_window
