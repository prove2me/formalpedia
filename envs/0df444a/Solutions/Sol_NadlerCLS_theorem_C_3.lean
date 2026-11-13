-- Prove2me | solution 1 for NadlerCLS.theorem_C_3
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-12T19:57:04.60002+00:00
-- url     : https://prove2.me/submissions/dd7cfe7f-0972-4398-a3db-530a90bff06d

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_coSearch
import Definitions.Def_NadlerCLS_holderSearch
import Theorems.Thm_NadlerCLS_t_le_n_mul_rpow
import Theorems.Thm_NadlerCLS_scaleLam_polyTime
import Theorems.Thm_NadlerCLS_encCO_injective
import Theorems.Thm_CookPvsNP_polyTimeComputable_pairSnd

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace NadlerCLS.C3

/-- The ℓ₁ distance is nonnegative. -/
theorem l1_nonneg {n : ℕ} (x y : Fin n → ℝ) : 0 ≤ l1 x y :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Two points of the cube `[0, 1]ⁿ` are at ℓ₁ distance at most `n`. -/
theorem l1_le_dim {n : ℕ} (x y : Fin n → ℝ) (hx : InCube x) (hy : InCube y) :
    l1 x y ≤ n := by
  unfold l1
  calc ∑ i, |x i - y i| ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => by
          rw [abs_le]
          constructor <;> linarith [(hx i).1, (hx i).2, (hy i).1, (hy i).2])
    _ = n := by simp

/-- A Lipschitz bound with constant `lam` at distance `d ∈ [0, n]` follows from a β-Hölder bound
with any constant `lam' ≥ n * lam`: `lam * d ≤ lam' * d ^ β`. -/
theorem lip_le_holder (n : ℕ) (hn : 1 ≤ n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (lam lam' d : ℝ) (hlam : 0 < lam) (hlam' : (n : ℝ) * lam ≤ lam') (hd0 : 0 ≤ d)
    (hdn : d ≤ n) : lam * d ≤ lam' * d ^ β := by
  rcases hd0.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow hβ0.ne']
    simp
  · have h1 : d ≤ (n : ℝ) * d ^ β := NadlerCLS.t_le_n_mul_rpow n hn β hβ0 hβ1 d h hdn
    have h2 : 0 ≤ d ^ β := Real.rpow_nonneg h.le β
    calc lam * d ≤ lam * ((n : ℝ) * d ^ β) := mul_le_mul_of_nonneg_left h1 hlam.le
      _ = ((n : ℝ) * lam) * d ^ β := by ring
      _ ≤ lam' * d ^ β := mul_le_mul_of_nonneg_right hlam' h2

end NadlerCLS.C3

open NadlerCLS in
theorem solution (n : ℕ) (hn : 1 ≤ n) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    SearchReduces (coSearch n) (holderSearch n β) := by
  obtain ⟨F, hF, hFenc⟩ := NadlerCLS.scaleLam_polyTime n
  obtain ⟨g, hg, hgpair⟩ := CookPvsNP.polyTimeComputable_pairSnd Bool Bool
  have hβ0' : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ0
  have hβ1' : (β : ℝ) ≤ 1 := by exact_mod_cast hβ1
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  refine ⟨F, g, hF, hg, ?_⟩
  rintro s ⟨I, hI, rfl⟩
  obtain ⟨lam', hlam', hFI⟩ := hFenc I hI
  have hlamQ : (0 : ℚ) < I.lam := hI.2.2.2
  have hI' : ({ f := I.f, p := I.p, δ := I.δ, lam := lam' } : COInstance n).Valid :=
    ⟨hI.1, hI.2.1, hI.2.2.1, lt_of_lt_of_le (mul_pos hnpos hlamQ) hlam'⟩
  refine ⟨⟨_, hI', hFI.symm⟩, ?_⟩
  intro t ht
  rw [hgpair]
  obtain ⟨J, -, hJenc, hans⟩ := ht
  obtain rfl : J = { f := I.f, p := I.p, δ := I.δ, lam := lam' } :=
    NadlerCLS.encCO_injective n (hJenc.trans hFI)
  have hlam : (0 : ℝ) < (I.lam : ℝ) := by exact_mod_cast hlamQ
  have hlam'R : (n : ℝ) * (I.lam : ℝ) ≤ (lam' : ℝ) := by exact_mod_cast hlam'
  refine ⟨I, hI, rfl, ?_⟩
  rcases hans with ⟨x, rfl, hx, h1⟩ | ⟨x, y, rfl, hx, hy, h2⟩ | ⟨x, y, rfl, hx, hy, h3⟩
  · exact Or.inl ⟨x, rfl, hx, h1⟩
  · refine Or.inr (Or.inl ⟨x, y, rfl, hx, hy, ?_⟩)
    have key := C3.lip_le_holder n hn β hβ0' hβ1' I.lam lam' (l1 (rpt x) (rpt y)) hlam hlam'R
      (C3.l1_nonneg _ _) (C3.l1_le_dim _ _ hx hy)
    exact lt_of_le_of_lt key h2
  · refine Or.inr (Or.inr ⟨x, y, rfl, hx, hy, ?_⟩)
    have key := C3.lip_le_holder n hn β hβ0' hβ1' I.lam lam' (l1 (rpt x) (rpt y)) hlam hlam'R
      (C3.l1_nonneg _ _) (C3.l1_le_dim _ _ hx hy)
    exact lt_of_le_of_lt key h3
