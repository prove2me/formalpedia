-- Prove2me | solution 1 for LocalConjugacy.Proof.QuaternionCohomology.cohomology_card
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:30:22.908983+00:00
-- url     : https://prove2.me/submissions/091119b8-ea83-4628-9386-a2fa7386330b

import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
import Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
import Definitions.Def_LocalConjugacy_Proof_ComplementSupersolvable
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction
import Definitions.Def_LocalConjugacy_Proof_QuaternionComplements
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_QuaternionExample_cocycle_eq_candidate

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

/-!
The `Q₈ ⋊ S₃` obstruction from the introduction. We use Mathlib's quaternion
and dihedral groups, with `S₃ = DihedralGroup 3`. The action rotates `i,j,k`
and sends `(i,j,k)` to `(-j,-i,-k)` under a reflection.
All finite checks use kernel-checked `decide`, never `native_decide`.
-/

namespace LocalConjugacy.QuaternionExample




open QuaternionGroup







set_option maxRecDepth 10000
set_option maxHeartbeats 0



















private theorem not_equivalent : ¬ Equivalent (fun _ => 1) signCocycle := by decide







private theorem candidate_classification : ∀ a b : Q, IsCocycle (candidate a b) →
    Equivalent (candidate a b) (fun _ => 1) ∨
    Equivalent (candidate a b) signCocycle := by decide



/-- There are exactly two cohomology classes, represented by `1` and sign. -/
private theorem exactly_two_classes :
    IsCocycle (fun _ => 1) ∧ IsCocycle signCocycle ∧
    ¬ Equivalent (fun _ => 1) signCocycle ∧
    (∀ f : S → Q, IsCocycle f →
      Equivalent f (fun _ => 1) ∨ Equivalent f signCocycle) := by
  refine ⟨by decide, sign_isCocycle, not_equivalent, ?_⟩
  intro f hf
  rw [cocycle_eq_candidate f hf]
  apply candidate_classification
  rwa [← cocycle_eq_candidate f hf]





end LocalConjugacy.QuaternionExample

end LocalConjugacy.Proof

end

section


/-!
The finite cohomology assertions for the quaternion counterexample. The original
cocycle calculation is promoted to the actual quotient H¹. A small subgroup
classification proves vanishing on every proper subgroup, hence every Sylow.
-/
namespace LocalConjugacy.Proof.QuaternionCohomology
open LocalConjugacy.QuaternionExample
set_option maxRecDepth 20000
set_option maxHeartbeats 0




/-- The representative classification gives exactly two quotient classes. -/
private theorem cohomology_card_preparedProof : Nat.card (FiniteH1 action) = 2 := by
  apply Nat.card_eq_two_iff.mpr
  refine ⟨Quotient.mk _ identityCocycle, Quotient.mk _ nontrivialCocycle, ?_, ?_⟩
  · intro h
    exact not_equivalent (Quotient.exact h)
  · apply Set.eq_univ_of_forall
    intro c
    induction c using Quotient.inductionOn with
    | h f =>
      rcases exactly_two_classes.2.2.2 f.val f.property with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl (Quotient.sound h))
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (Quotient.sound h)))









end LocalConjugacy.Proof.QuaternionCohomology

end

theorem solution :
@Eq.{1} Nat
  (Nat.card.{0}
    (@LocalConjugacy.FiniteH1.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.action))
  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) :=
  @LocalConjugacy.Proof.QuaternionCohomology.cohomology_card_preparedProof
