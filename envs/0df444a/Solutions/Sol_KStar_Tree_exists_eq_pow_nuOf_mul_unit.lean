-- Prove2me | solution 1 for KStar.Tree.exists_eq_pow_nuOf_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:36.946395+00:00
-- url     : https://prove2.me/submissions/59cfdf64-90c1-418e-b349-80226cf21c4a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuInf
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_CyclotomicTotient_NuBasic
import Theorems.Thm_KStar_Tree_pow_nuOf_dvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace KStar.Tree
variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)
private theorem isUnit_of_not_dvd {c : ℤ_[l]} (hc : ¬ (l : ℤ_[l]) ∣ c) : IsUnit c := by
  rw [PadicInt.isUnit_iff]
  exact le_antisymm (PadicInt.norm_le_one c)
    (not_lt.1 fun h => hc ((PadicInt.norm_lt_one_iff_dvd c).1 h))
private theorem nuOf_mem (h : ∃ g, ε g ^ n ≠ 1) :
    ∃ g, ¬ (l : ℤ_[l]) ^ (nuOf l ε n + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 := by
  obtain ⟨g, hg⟩ := h
  have hx : ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h1
    apply hg
    ext
    simpa using h1
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨u, v, hxv⟩ : ∃ (u : ℤ_[l]ˣ) (v : ℕ), ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = u * (l : ℤ_[l]) ^ v :=
    ⟨_, _, PadicInt.unitCoeff_spec hx⟩
  have hne : {k | ∃ g, ¬ (l : ℤ_[l]) ^ (k + 1) ∣ ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1}.Nonempty := by
    refine ⟨v, g, ?_⟩
    intro hd
    rw [hxv, pow_succ, mul_comm (u : ℤ_[l])] at hd
    have hlu : (l : ℤ_[l]) ∣ u := (mul_dvd_mul_iff_left (pow_ne_zero v hl0)).1 hd
    have hlunit : IsUnit (l : ℤ_[l]) := isUnit_of_dvd_unit hlu u.isUnit
    have h1 := (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l])).2 dvd_rfl
    rw [PadicInt.isUnit_iff] at hlunit
    linarith
  exact Nat.sInf_mem hne
end KStar.Tree
end

set_option autoImplicit false
open KStar KStar.Tree
variable {Γ : Type} [Group Γ] (l : ℕ) [Fact l.Prime] (ε : Γ →* ℤ_[l]ˣ) (n : ℕ)
namespace KStar.Tree
theorem _root_.solution (h : ∃ g, ε g ^ n ≠ 1) :
    ∃ (g : Γ) (u : ℤ_[l]ˣ), ((ε g : ℤ_[l]ˣ) : ℤ_[l]) ^ n - 1 = (l : ℤ_[l]) ^ nuOf l ε n * u := by
  obtain ⟨g, hg⟩ := nuOf_mem l ε n h
  obtain ⟨c, hc⟩ := pow_nuOf_dvd l ε n g
  refine ⟨g, (isUnit_of_not_dvd l (c := c) ?_).unit, ?_⟩
  · rintro ⟨d, rfl⟩
    exact hg ⟨d, by rw [hc]; ring⟩
  · rw [IsUnit.unit_spec]
    exact hc
end KStar.Tree
