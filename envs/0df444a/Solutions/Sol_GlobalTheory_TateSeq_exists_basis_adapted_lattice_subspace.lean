-- Prove2me | solution 1 for GlobalTheory.TateSeq.exists_basis_adapted_lattice_subspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:35.393778+00:00
-- url     : https://prove2.me/submissions/2f2f9d68-56f0-4274-88f8-4a07b528a8d0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TateSeq
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.TateSeq
theorem _root_.solution (l r : ℕ) [Fact l.Prime] (V : Type) [AddCommGroup V]
    [Module (ZMod l) V] (hc : Nat.card V = l ^ r) :
    ∃ b : Fin r → V,
      (∀ a : Fin r → ℤ, ∑ i, a i • b i = 0 → ∀ i, (l : ℤ) ∣ a i) ∧
      (∀ y : V, ∃ a : Fin r → ℤ, ∑ i, a i • b i = y) := by
  have hp : l.Prime := Fact.out
  haveI : NeZero l := ⟨hp.ne_zero⟩
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.ne_zero)
  letI := Fintype.ofFinite V

  have hdim : Module.finrank (ZMod l) V = r := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod l) (V := V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hc] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  let B := Module.finBasisOfFinrankEq (ZMod l) V hdim
  refine ⟨fun i => B i, ?_, ?_⟩
  ·
    intro a ha i
    have h2 : ∑ j, (a j : ZMod l) • B j = 0 := by
      simpa only [Int.cast_smul_eq_zsmul] using ha
    have h3 := Fintype.linearIndependent_iff.mp B.linearIndependent _ h2 i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h3
  ·
    intro y
    refine ⟨fun i => ((B.repr y i).val : ℤ), ?_⟩
    conv_rhs => rw [← B.sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul (ZMod l)]
    simp
end GlobalTheory.TateSeq
