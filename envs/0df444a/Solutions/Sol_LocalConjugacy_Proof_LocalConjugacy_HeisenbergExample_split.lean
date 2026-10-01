-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.split
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:32:35.708967+00:00
-- url     : https://prove2.me/submissions/0a425bd7-26ee-46a5-a6ee-6f5e8316020a

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

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

/-!
The imprimitive wreath product `C₃ wr S₃`, of order 162, acting on nine
points. Its normal Heisenberg subgroup is the kernel of the base-sum/sign
map to `C₃ × C₂`. The chosen cyclic complement translates block zero and
interchanges the other two blocks. Its Sylow subgroups have disjoint fixed
point sets. This is the second example in the manuscript.
-/

namespace LocalConjugacy.HeisenbergExample








set_option maxRecDepth 10000
set_option maxHeartbeats 0





























private theorem projection_section : ∀ z : C3 × C2, projection (sectionMap z) = z := by decide




private theorem split_preparedProof : Splits N J := by
  refine ⟨inferInstance, ?_, ?_⟩
  · intro g
    refine ⟨g * (sectionMap (projection g))⁻¹, ?_, sectionMap (projection g), ?_, ?_⟩
    · change projection (g * (sectionMap (projection g))⁻¹) = 1
      rw [map_mul, map_inv, projection_section]
      exact mul_inv_cancel (projection g)
    · exact ⟨projection g, rfl⟩
    · simp
  · apply le_antisymm _ bot_le
    intro g hg
    obtain ⟨z, rfl⟩ := hg.2
    have hz : z = 1 := (projection_section z).symm.trans hg.1
    simp [hz]





































































end LocalConjugacy.HeisenbergExample

end LocalConjugacy.Proof

end

theorem solution :
@LocalConjugacy.Proof.LocalConjugacy.Splits.{0} LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.G
  (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.B
    LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.S
    (@Pi.group.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (fun (a : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
        LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.C3)
      fun (i : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
      @Multiplicative.group.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@AddGroupWithOne.toAddGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  Nat.fact_prime_three))))))
    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.action)
  LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.N LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.J :=
  @LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.split_preparedProof
