-- Prove2me | solution 1 for GlobalTheory.BadShare.exists_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:33:32.697801+00:00
-- url     : https://prove2.me/submissions/57cd5ce7-6821-44ad-9e23-8b821fc14e79

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare
theorem _root_.solution (d : ℕ) (hd : d ≠ 0) : ∃ P : (ZMod g)[X], P.Monic ∧ Irreducible P ∧ P.natDegree = d ∧
    ∀ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∀ n : ℕ, x ^ n = 1 ↔ g ^ d - 1 ∣ n := by
  haveI : Fintype (GaloisField g d) := Fintype.ofFinite _
  obtain ⟨α, hα⟩ := IsCyclic.exists_monoid_generator (α := (GaloisField g d)ˣ)
  have hi : IsIntegral (ZMod g) (α : GaloisField g d) := Algebra.IsIntegral.isIntegral _
  have hord : orderOf α = g ^ d - 1 := by
    rw [orderOf_eq_card_of_forall_mem_powers hα, Nat.card_units, GaloisField.card g d hd]
  have htop : IntermediateField.adjoin (ZMod g) {(α : GaloisField g d)} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_cases hx : x = 0
    · rw [hx]; exact zero_mem _
    · obtain ⟨n, hn⟩ := hα (Units.mk0 x hx)
      have : x = (α : GaloisField g d) ^ n := by simpa using (congrArg Units.val hn).symm
      rw [this]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self _ _) n
  refine ⟨minpoly (ZMod g) (α : GaloisField g d), minpoly.monic hi, minpoly.irreducible hi, ?_, ?_⟩
  · rw [(Field.primitive_element_iff_minpoly_natDegree_eq _ _).1 htop, GaloisField.finrank g hd]
  · intro x hx n
    have h1 := minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hi) (mem_aroots.1 hx).2 (minpoly.monic hi)
    have h2 : x ^ n = 1 ↔ minpoly (ZMod g) x ∣ X ^ n - 1 := by
      rw [minpoly.dvd_iff]; simp [sub_eq_zero]
    rw [h2, ← h1, minpoly.dvd_iff, ← hord, orderOf_dvd_iff_pow_eq_one]
    simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    rw [← Units.val_pow_eq_pow_val, Units.val_eq_one]
end GlobalTheory.BadShare
