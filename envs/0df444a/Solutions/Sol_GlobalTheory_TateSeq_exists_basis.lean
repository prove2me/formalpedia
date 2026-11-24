-- Prove2me | solution 1 for GlobalTheory.TateSeq.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:40:14.612797+00:00
-- url     : https://prove2.me/submissions/338c3e77-e67a-49a2-9693-3e8c356d9fcd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Theorems.Thm_GlobalTheory_TateSeq_exists_basis_adapted_lattice_subspace

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
theorem _root_.solution (l r : ℕ) [Fact l.Prime]
    (h : Nat.card {x : M // l • x = 0} = l ^ r) :
    ∃ b : Fin r → M, (∀ i, l • b i = 0) ∧
      (∀ a : Fin r → ℤ, ∑ i, a i • b i = 0 → ∀ i, (l : ℤ) ∣ a i) ∧
      (∀ y : M, l • y = 0 → ∃ a : Fin r → ℤ, ∑ i, a i • b i = y) := by
  have hc : Nat.card (tors M l) = l ^ r := h
  obtain ⟨b, h1, h2⟩ := @exists_basis_adapted_lattice_subspace l r _ (tors M l) _
    (AddCommGroup.zmodModule (fun x => Subtype.ext x.2)) hc
  refine ⟨fun i => (b i).1, fun i => (b i).2, ?_, ?_⟩
  · intro a ha
    refine h1 a (Subtype.ext ?_)
    simpa using ha
  · intro y hy
    obtain ⟨a, ha⟩ := h2 ⟨y, hy⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
end GlobalTheory.TateSeq
