-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.cocycle_eq_candidate
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:37:34.549259+00:00
-- url     : https://prove2.me/submissions/f25a0212-d70c-476e-bf61-e03f40fadb40

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
The `Q₈ ⋊ S₃` obstruction from the introduction. We use Mathlib's quaternion
and dihedral groups, with `S₃ = DihedralGroup 3`. The action rotates `i,j,k`
and sends `(i,j,k)` to `(-j,-i,-k)` under a reflection.
All finite checks use kernel-checked `decide`, never `native_decide`.
-/

namespace LocalConjugacy.QuaternionExample




open QuaternionGroup







set_option maxRecDepth 10000
set_option maxHeartbeats 0





























private theorem cocycle_eq_candidate_preparedProof (f : S → Q) (hf : IsCocycle f) :
    f = candidate (f (.r 1)) (f (.sr 0)) := by
  have h1 : f 1 = 1 := by
    have h := hf 1 1
    rw [one_mul, act_one] at h
    exact (mul_eq_left.mp h.symm)
  have hr2 : f (.r 2) = f (.r 1) * act (.r 1) (f (.r 1)) := hf (.r 1) (.r 1)
  have hs0 := hf (.sr 0) (.r 0)
  have hs1 := hf (.sr 0) (.r 1)
  have hs2 := hf (.sr 0) (.r 2)
  change f (.sr 0) = f (.sr 0) * act (.sr 0) (f 1) at hs0
  rw [h1] at hs0
  rw [hr2] at hs2
  funext s
  rcases s with i | i <;> fin_cases i <;>
    first | exact h1 | rfl | exact hr2 | exact hs0 | exact hs1 | exact hs2







end LocalConjugacy.QuaternionExample

end LocalConjugacy.Proof

end

theorem solution :
∀
  (f :
    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S → LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q)
  (hf : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.IsCocycle f),
  @Eq.{1}
    (LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S → LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q)
    f
    (LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.candidate
      (f
        (@DihedralGroup.r (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
            (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Nat.fact_prime_three))))))))))
      (f
        (@DihedralGroup.sr (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
            (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@Semifield.toDivisionSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Nat.fact_prime_three))))))))))) :=
  @LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.cocycle_eq_candidate_preparedProof
