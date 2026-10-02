-- Prove2me | solution 1 for MooreFoelner.not_eventually_folnerFunction_le_towerExp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T02:31:45.67402+00:00
-- url     : https://prove2.me/submissions/ced34d21-3fb2-4085-9610-f8187adec5d8

import Theorems.Thm_MooreFoelner_exists_const_forall_isFolnerSet_towerExp_le_card
import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, §5 end (group Goal): Claim 5.14, Theorem 1.1 and its "in particular", and the
F-amenability reference goal
-/

namespace MooreFoelner.Dev.Goal

open Classical CannonFloydParry MooreFoelner

/-! ## Generic facts about (weighted) Følner sets -/

theorem isFolnerSet_mono {G : Type*} [Group G] {Γ A : Finset G} {ε ε' : ℝ}
    (h : IsFolnerSet Γ A ε) (hle : ε ≤ ε') : IsFolnerSet Γ A ε' :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _))

/-! ## Trees -/

/-! ## The tower function -/

open ThompsonAmenability in
theorem towerExp_succ (p m : ℕ) : towerExp (p + 1) m = 2 ^ towerExp p m := rfl

open ThompsonAmenability in
theorem towerExp_strictMono (p : ℕ) : StrictMono (towerExp p) := by
  induction p with
  | zero => exact strictMono_id
  | succ p ih =>
    intro a b hab
    simp only [towerExp_succ]
    exact Nat.pow_lt_pow_right (by norm_num) (ih hab)

open ThompsonAmenability in
theorem towerExp_add (p q m : ℕ) : towerExp (p + q) m = towerExp p (towerExp q m) := by
  induction p with
  | zero => simp [towerExp]
  | succ p ih => rw [Nat.succ_add, towerExp_succ, ih, towerExp_succ]

open ThompsonAmenability in
theorem le_towerExp (q : ℕ) : q ≤ towerExp q 0 := by
  induction q with
  | zero => simp [towerExp]
  | succ q ih =>
    rw [towerExp_succ]
    exact lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) ih)

/-! ## Claim 5.14 -/

end MooreFoelner.Dev.Goal

namespace MooreFoelner

open Classical CannonFloydParry
open MooreFoelner.Dev.Goal

end MooreFoelner

/-! ## Word length along a chain, and the generators `x₀, x₁` -/

namespace MooreFoelner.Dev.Goal

open Classical CannonFloydParry MooreFoelner

end MooreFoelner.Dev.Goal

namespace MooreFoelner

open Classical CannonFloydParry
open MooreFoelner.Dev.Goal

end MooreFoelner

namespace ThompsonAmenability

end ThompsonAmenability
end

open MooreFoelner in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Goal in
open Classical CannonFloydParry MooreFoelner in
open Classical CannonFloydParry in
open MooreFoelner.Dev.Goal in
theorem solution (Γ : Finset MooreF)
    (hsymm : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hgen : Subgroup.closure (Γ : Set MooreF) = ⊤) (p : ℕ) :
    ¬ ∃ N : ℕ, ∀ n ≥ N, folnerFunction Γ n ≤ (ThompsonAmenability.towerExp p n : ℕ∞) := by
  rintro ⟨N, hN⟩
  obtain ⟨C, hC, h29⟩ := exists_const_forall_isFolnerSet_towerExp_le_card Γ hsymm hgen
  set c : ℕ := ⌈C⌉₊ with hc
  have hc2 : 2 ≤ c := by
    have : 1 < c := Nat.lt_ceil.mpr (by exact_mod_cast hC)
    omega
  have hCc : C ≤ c := Nat.le_ceil C
  obtain ⟨r, hrN, hr⟩ : ∃ r, N ≤ r ∧ c * (p + r + 2) < 2 ^ r := by
    set k := c * (p + 2) + 2 * c + N + 1 with hk
    refine ⟨2 * k, by omega, ?_⟩
    have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h2 : (k + 1) * (k + 1) ≤ 2 ^ (2 * k) := by
      rw [two_mul, pow_add]; exact Nat.mul_le_mul h1 h1
    have hk' : c * (p + 2) + 2 * c + 1 ≤ k := by omega
    have h4 : k * (c * (p + 2) + 2 * c + 1) ≤ k * k := Nat.mul_le_mul_left k hk'
    have h5 : c * (p + 2) ≤ k * (c * (p + 2)) := Nat.le_mul_of_pos_left _ (by omega)
    have h3 : c * (p + 2 * k + 2) < (k + 1) * (k + 1) := by nlinarith
    omega
  set m := p + (r + 2) with hm
  set n := c ^ m with hn
  have hnN : N ≤ n := by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ m ≤ c ^ m := Nat.pow_le_pow_left hc2 m
    omega
  have hbig : n < ThompsonAmenability.towerExp (r + 2) 0 := by
    have h1 : c ^ m ≤ (2 ^ c) ^ m := Nat.pow_le_pow_left Nat.lt_two_pow_self.le m
    have h2 : c * m < 2 ^ r := by rw [hm]; convert hr using 2; ring
    have h3 : 2 ^ (c * m) < 2 ^ 2 ^ r := Nat.pow_lt_pow_right (by norm_num) h2
    have h4 : 2 ^ 2 ^ r ≤ ThompsonAmenability.towerExp (r + 2) 0 := by
      rw [towerExp_succ, towerExp_succ]
      exact Nat.pow_le_pow_right (by norm_num)
        (Nat.pow_le_pow_right (by norm_num) (le_towerExp r))
    rw [← pow_mul] at h1
    omega
  have key : ∀ A : Finset MooreF, IsFolnerSet Γ A (1 / (n : ℝ)) →
      ThompsonAmenability.towerExp p n + 1 ≤ A.card := by
    intro A hA
    have hA' : IsFolnerSet Γ A (C ^ (-(m : ℤ))) := by
      refine isFolnerSet_mono hA ?_
      rw [zpow_neg, zpow_natCast, one_div]
      apply inv_anti₀ (pow_pos (by linarith) _)
      rw [hn]
      push_cast
      exact pow_le_pow_left₀ (by linarith) hCc m
    have h := h29 m A hA'
    have := towerExp_strictMono p hbig
    rw [hm, towerExp_add] at h
    omega
  have hge : ((ThompsonAmenability.towerExp p n + 1 : ℕ) : ℕ∞) ≤ folnerFunction Γ n := by
    unfold folnerFunction
    exact le_iInf₂ (fun A hA => by exact_mod_cast key A hA)
  have h := le_trans hge (hN n hnN)
  have : ThompsonAmenability.towerExp p n + 1 ≤ ThompsonAmenability.towerExp p n := by
    exact_mod_cast h
  omega
