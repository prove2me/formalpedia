-- Prove2me | solution 1 for GlobalTheory.Models.exists_prime_gt_neg_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:06.483848+00:00
-- url     : https://prove2.me/submissions/ab99de57-c70b-4641-a92b-18a8bccac5be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmGeneratorSqQuadraticEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoprimeLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory GlobalTheory.Models
namespace GlobalTheory.Models
theorem _root_.solution (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3) (b : ℕ) :
    ∃ n : ℕ, b < n ∧ n.Prime ∧ Odd n ∧ ¬ IsSquare (-(d : ZMod n)) := by
  haveI : NeZero (4 * d) := ⟨by have := hd.pos; omega⟩
  obtain ⟨n, hn, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * d) (a := -1) isUnit_one.neg (max b d)
  have hdvd : 4 * d ∣ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hmod]; ring
  have h4 : n % 4 = 3 := by
    have : 4 ∣ n + 1 := Dvd.dvd.trans (Dvd.intro _ rfl) hdvd
    omega
  have hdn : (n : ZMod d) = -1 := by
    have : d ∣ n + 1 := Dvd.dvd.trans (Dvd.intro_left _ rfl) hdvd
    rw [← ZMod.natCast_eq_zero_iff] at this
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hlt : d < n := lt_of_le_of_lt (le_max_right _ _) hn
  haveI : Fact n.Prime := ⟨hp⟩
  haveI : Fact d.Prime := ⟨hd⟩
  refine ⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hp, by rw [Nat.odd_iff]; omega, ?_⟩
  have h1 : IsSquare (d : ZMod n) := by
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 hd4 hlt.ne', hdn,
      ZMod.exists_sq_eq_neg_one_iff]
    simp [hd4]
  have h0 : (d : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hd.pos hlt
  intro h2
  have h3 : IsSquare (-1 : ZMod n) := by
    have := h2.div h1
    rwa [neg_div, div_self h0] at this
  rw [ZMod.exists_sq_eq_neg_one_iff] at h3
  exact h3 h4
end GlobalTheory.Models
