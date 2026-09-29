-- Prove2me | solution 1 for MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/938adc06-3fd4-5993-aa81-7fbf2ce8fbf0

import Mathlib
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_Nat_macaulayPow_lt_macaulayPow_of_lt
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GotzmannB29

theorem lt_of_lt {n : ℕ} {K : Type} [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (H : ℕ → ℕ) (g : ℕ) (hg : 1 ≤ g) (hH : ∀ e, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (d : ℕ) (hd : g ≤ d) (hlt : Module.finrank K (piece J d) < H d) :
    ∀ e, d ≤ e → Module.finrank K (piece J e) < H e := by
  intro e hde
  induction e with
  | zero =>
    obtain rfl : d = 0 := by omega
    exact hlt
  | succ e ih =>
    rcases Nat.lt_or_ge e d with h | h
    · obtain rfl : d = e + 1 := by omega
      exact hlt
    · calc Module.finrank K (piece J (e + 1)) ≤ Nat.macaulayPow e (Module.finrank K (piece J e)) :=
            MvPolynomial.finrank_piece_succ_le_macaulayPow n e (by omega) K J hJ
        _ < Nat.macaulayPow e (H e) := Nat.macaulayPow_lt_macaulayPow_of_lt (by omega) (ih h)
        _ = H (e + 1) := (hH e (by omega)).symm

theorem le_finrank_piece {n : ℕ} {K : Type} [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (H : ℕ → ℕ) (g : ℕ) (hg : 1 ≤ g) (hH : ∀ e, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (hev : ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → Module.finrank K (piece J e) = H e)
    (d : ℕ) (hd : g ≤ d) : H d ≤ Module.finrank K (piece J d) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨D₀, hD₀⟩ := hev
  have := lt_of_lt J hJ H g hg hH d hd hlt (max d D₀) (le_max_left _ _)
  rw [hD₀ _ (le_max_right _ _)] at this
  exact lt_irrefl _ this

end GotzmannB29

open GotzmannB29 in
theorem solution
    (n g : ℕ) (hg : 1 ≤ g) (H : ℕ → ℕ)
    (hH : ∀ e : ℕ, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (hev : ∃ D : ℕ, ∀ e : ℕ, D ≤ e → Module.finrank K (piece J e) = H e) :
    ∀ d : ℕ, g ≤ d → H d ≤ Module.finrank K (piece J d) := by
  intro d hd
  exact GotzmannB29.le_finrank_piece J hJ H g hg hH hev d hd

end S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq
end P2MW
export P2MW.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq (solution)
