-- Prove2me | solution 1 for LocalConjugacy.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T18:01:30.732328+00:00
-- url     : https://prove2.me/submissions/06b88332-e392-450c-91f8-f00edc502516

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_lemma_1_2_of_pronilpotent
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_lemma_1_2_of_prosupersolvable
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_primaryRestriction_bijective

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

section Algebra
variable {G F : Type*} [Group G] [Group F]





end Algebra

section Topology
variable {G F : Type*} [Group G] [Group F]
  [TopologicalSpace G] [TopologicalSpace F] [DiscreteTopology F]

/-- A continuous discrete quotient of a pronilpotent group is nilpotent. -/
private theorem nilpotent_of_pronilpotent_surjective (hG : Pronilpotent G)
    (f : G →* F) (hf : Continuous f) (hs : Function.Surjective f) : Group.IsNilpotent F := by
  let U : OpenNormalSubgroup G :=
    { toSubgroup := f.ker
      isOpen' := hf.isOpen_preimage _ (isOpen_discrete {1}) }
  letI := hG U
  exact Group.nilpotent_of_surjective (QuotientGroup.kerLift f)
    (QuotientGroup.lift_surjective_of_surjective _ f hs le_rfl)





end Topology

section Discrete
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

private theorem pronilpotent_iff_nilpotent : Pronilpotent G ↔ Group.IsNilpotent G := by
  constructor
  · intro h
    exact nilpotent_of_pronilpotent_surjective h (MonoidHom.id G) continuous_id Function.surjective_id
  · intro h
    letI := h
    intro U
    infer_instance



end Discrete
end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy



variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- Lemma 1.2, including both branches of the manuscript's disjunction. -/
private theorem primary_decomposition [Profinite J] [Profinite N] [DiscreteTopology N] [Finite N]
    [ContinuousSMul J N] (hN : Pronilpotent N)
    (hcase : Prosupersolvable (ActionProduct J N) ∨ Pronilpotent J)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    PrimaryDecomposition (N := N) P := by
  rcases hcase with hG | hJ
  · exact lemma_1_2_of_prosupersolvable hN hG P hP
  · exact lemma_1_2_of_pronilpotent hN hJ P hP

end LocalConjugacy

end LocalConjugacy.Proof

end

section




namespace LocalConjugacy.Proof

/-! The numbered cohomology statements, expressed on the actual quotient `H¹`.
The representative-level arguments supply the proofs, without changing the
restriction maps or weakening surjectivity to separate local extension claims. -/

namespace LocalConjugacy

section QuotientMaps
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]





end QuotientMaps

section Numbered
variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [TopologicalSpace N] [MulDistribMulAction J N]

/-- Lemma 1.2 (`lem:loc_conj`). For finite nilpotent coefficients, simultaneous
restriction bijects `H¹(J,N)` with the product of the stable Sylow classes.
The canonical restrictions preserve the distinguished class. -/
private theorem lemma_1_2 [Profinite J] [DiscreteTopology N] [Finite N] [Group.IsNilpotent N]
    [ContinuousSMul J N]
    (hcase : Prosupersolvable (ActionProduct J N) ∨ Pronilpotent J)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    Function.Bijective (primaryRestriction (N := N) P) := by
  letI : Profinite N := ⟨⟩
  exact primaryRestriction_bijective P
    (primary_decomposition (pronilpotent_iff_nilpotent.mpr inferInstance) hcase P hP)



end Numbered
end LocalConjugacy

end LocalConjugacy.Proof

end

section


/-!
Proofs of the eleven numbered results in the public draft. Each statement is
copied at Lean syntax offsets from the submitted target. The proofs invoke the
ported arguments through proved interface conversions; the pointed cohomology
claims include preservation of the identity class explicitly.
-/
universe u v
open LocalConjugacy



/-- The exact draft statement, proved by the corresponding ported paper argument. -/
private theorem LocalConjugacy.lemma_1_2_preparedProof {J : ProfiniteGrp.{u}} {N : Type v} [Group N]
    [TopologicalSpace N] [MulDistribMulAction J N] [DiscreteTopology N] [Finite N] [Group.IsNilpotent N]
    [ContinuousSMul J N]
    (hcase : Prosupersolvable (ActionProduct J N) ∨ Pronilpotent J)
    (P : PrimeDivisor J → Subgroup J) (hP : ∀ p, IsSylowPro p.val.val ⊤ (P p)) :
    Function.Bijective (primaryRestriction (N := N) P) ∧
      (primaryRestriction (N := N) P) default = default := by
  exact ⟨Proof.LocalConjugacy.lemma_1_2 hcase P hP,
    primaryRestriction_distinguished P⟩



















end

universe u v

theorem solution :
∀ {J : ProfiniteGrp.{u}} {N : Type v} [inst : Group.{v} N] [inst_1 : TopologicalSpace.{v} N]
  [inst_2 :
    @MulDistribMulAction.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      N
      (@DivInvMonoid.toMonoid.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (@Group.toDivInvMonoid.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          (ProfiniteGrp.group.{u} J)))
      (@DivInvMonoid.toMonoid.{v} N (@Group.toDivInvMonoid.{v} N inst))]
  [@DiscreteTopology.{v} N inst_1] [Finite.{v + 1} N] [@Group.IsNilpotent.{v} N inst]
  [@ContinuousSMul.{u, v}
      (TopCat.carrier.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      N
      (@SemigroupAction.toSMul.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N
        (@Monoid.toSemigroup.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          (@DivInvMonoid.toMonoid.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (@Group.toDivInvMonoid.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))))
        (@MulAction.toSemigroupAction.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N
          (@DivInvMonoid.toMonoid.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (@Group.toDivInvMonoid.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J)))
          (@MulDistribMulAction.toMulAction.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N
            (@DivInvMonoid.toMonoid.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (@Group.toDivInvMonoid.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J)))
            (@DivInvMonoid.toMonoid.{v} N (@Group.toDivInvMonoid.{v} N inst)) inst_2)))
      (TopCat.str.{u}
        (@CompHausLike.toTop.{u}
          (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
          (ProfiniteGrp.toProfinite.{u} J)))
      inst_1]
  (hcase :
    Or
      (@LocalConjugacy.Prosupersolvable.{max v u}
        (@LocalConjugacy.ActionProduct.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N (ProfiniteGrp.group.{u} J) inst inst_2)
        (@SemidirectProduct.instGroup.{v, u} N
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          inst (ProfiniteGrp.group.{u} J)
          (@MulDistribMulAction.toMulAut.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N (ProfiniteGrp.group.{u} J) (@DivInvMonoid.toMonoid.{v} N (@Group.toDivInvMonoid.{v} N inst)) inst_2))
        (@LocalConjugacy.Proof.LocalConjugacy.semidirectTopology.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N (ProfiniteGrp.group.{u} J) inst
          (TopCat.str.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          inst_1
          (@MulDistribMulAction.toMulAut.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N (ProfiniteGrp.group.{u} J) (@DivInvMonoid.toMonoid.{v} N (@Group.toDivInvMonoid.{v} N inst)) inst_2)))
      (@LocalConjugacy.Pronilpotent.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (ProfiniteGrp.group.{u} J)
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))))
  (P :
    @LocalConjugacy.PrimeDivisor.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (ProfiniteGrp.group.{u} J)
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J))) →
      @Subgroup.{u}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (ProfiniteGrp.group.{u} J))
  (hP :
    ∀
      (p :
        @LocalConjugacy.PrimeDivisor.{u}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          (ProfiniteGrp.group.{u} J)
          (TopCat.str.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))),
      @LocalConjugacy.IsSylowPro.{u}
        (@Subtype.val.{1} Nat (fun (p : Nat) => Nat.Prime p)
          (@Subtype.val.{1} Nat.Primes
            (fun (p : Nat.Primes) =>
              @Exists.{u + 1}
                (@OpenNormalSubgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J)
                  (TopCat.str.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J))))
                fun
                  (U :
                    @OpenNormalSubgroup.{u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (ProfiniteGrp.group.{u} J)
                      (TopCat.str.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))) =>
                @Dvd.dvd.{0} Nat Nat.instDvd (@Subtype.val.{1} Nat (fun (p : Nat) => Nat.Prime p) p)
                  (Nat.card.{u}
                    (@HasQuotient.Quotient.{u, u}
                      (TopCat.carrier.{u}
                        (@CompHausLike.toTop.{u}
                          (fun (X : TopCat.{u}) =>
                            @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                          (ProfiniteGrp.toProfinite.{u} J)))
                      (@Subgroup.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J))
                      (@QuotientGroup.instHasQuotientSubgroup.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J))
                      (@OpenSubgroup.toSubgroup.{u}
                        (TopCat.carrier.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (ProfiniteGrp.group.{u} J)
                        (TopCat.str.{u}
                          (@CompHausLike.toTop.{u}
                            (fun (X : TopCat.{u}) =>
                              @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                            (ProfiniteGrp.toProfinite.{u} J)))
                        (@OpenNormalSubgroup.toOpenSubgroup.{u}
                          (TopCat.carrier.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          (ProfiniteGrp.group.{u} J)
                          (TopCat.str.{u}
                            (@CompHausLike.toTop.{u}
                              (fun (X : TopCat.{u}) =>
                                @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                              (ProfiniteGrp.toProfinite.{u} J)))
                          U)))))
            p))
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (ProfiniteGrp.group.{u} J)
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        (@Top.top.{u}
          (@Subgroup.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J))
          (@Subgroup.instTop.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J)))
        (P p)),
  And
    (@Function.Bijective.{max (u + 1) (v + 1), max (u + 1) (v + 1)}
      (@LocalConjugacy.H1.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2
        (@Top.top.{u}
          (@Subgroup.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J))
          (@Subgroup.instTop.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J))))
      ((p :
          @LocalConjugacy.PrimeDivisor.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J)
            (TopCat.str.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))) →
        @LocalConjugacy.InvariantH1.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N (ProfiniteGrp.group.{u} J) inst
          (TopCat.str.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          inst_1 inst_2
          (@Top.top.{u}
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@Subgroup.instTop.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J)))
          (P p))
      (@LocalConjugacy.primaryRestriction.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2 P))
    (@Eq.{max (u + 1) (v + 1)}
      ((p :
          @LocalConjugacy.PrimeDivisor.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J)
            (TopCat.str.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))) →
        @LocalConjugacy.InvariantH1.{u, v}
          (TopCat.carrier.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          N (ProfiniteGrp.group.{u} J) inst
          (TopCat.str.{u}
            (@CompHausLike.toTop.{u}
              (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
              (ProfiniteGrp.toProfinite.{u} J)))
          inst_1 inst_2
          (@Top.top.{u}
            (@Subgroup.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J))
            (@Subgroup.instTop.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J)))
          (P p))
      (@LocalConjugacy.primaryRestriction.{u, v}
        (TopCat.carrier.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        N (ProfiniteGrp.group.{u} J) inst
        (TopCat.str.{u}
          (@CompHausLike.toTop.{u}
            (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
            (ProfiniteGrp.toProfinite.{u} J)))
        inst_1 inst_2 P
        (@Inhabited.default.{max (u + 1) (v + 1)}
          (@LocalConjugacy.H1.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N (ProfiniteGrp.group.{u} J) inst
            (TopCat.str.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            inst_1 inst_2
            (@Top.top.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@Subgroup.instTop.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))))
          (@LocalConjugacy.instInhabitedH1.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N (ProfiniteGrp.group.{u} J) inst
            (TopCat.str.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            inst_1 inst_2
            (@Top.top.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@Subgroup.instTop.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))))))
      (@Inhabited.default.{max (u + 1) (v + 1)}
        ((p :
            @LocalConjugacy.PrimeDivisor.{u}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              (ProfiniteGrp.group.{u} J)
              (TopCat.str.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))) →
          @LocalConjugacy.InvariantH1.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N (ProfiniteGrp.group.{u} J) inst
            (TopCat.str.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            inst_1 inst_2
            (@Top.top.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@Subgroup.instTop.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J)))
            (P p))
        (@Pi.instInhabited.{1, max (u + 1) (v + 1)}
          (@LocalConjugacy.PrimeDivisor.{u}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            (ProfiniteGrp.group.{u} J)
            (TopCat.str.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J))))
          (fun
              (p :
                @LocalConjugacy.PrimeDivisor.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J)
                  (TopCat.str.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))) =>
            @LocalConjugacy.InvariantH1.{u, v}
              (TopCat.carrier.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              N (ProfiniteGrp.group.{u} J) inst
              (TopCat.str.{u}
                (@CompHausLike.toTop.{u}
                  (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                  (ProfiniteGrp.toProfinite.{u} J)))
              inst_1 inst_2
              (@Top.top.{u}
                (@Subgroup.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J))
                (@Subgroup.instTop.{u}
                  (TopCat.carrier.{u}
                    (@CompHausLike.toTop.{u}
                      (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                      (ProfiniteGrp.toProfinite.{u} J)))
                  (ProfiniteGrp.group.{u} J)))
              (P p))
          fun
            (a :
              @LocalConjugacy.PrimeDivisor.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J)
                (TopCat.str.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))) =>
          @LocalConjugacy.invariantH1Inhabited.{u, v}
            (TopCat.carrier.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            N (ProfiniteGrp.group.{u} J) inst
            (TopCat.str.{u}
              (@CompHausLike.toTop.{u}
                (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                (ProfiniteGrp.toProfinite.{u} J)))
            inst_1 inst_2
            (@Top.top.{u}
              (@Subgroup.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J))
              (@Subgroup.instTop.{u}
                (TopCat.carrier.{u}
                  (@CompHausLike.toTop.{u}
                    (fun (X : TopCat.{u}) => @TotallyDisconnectedSpace.{u} (TopCat.carrier.{u} X) (TopCat.str.{u} X))
                    (ProfiniteGrp.toProfinite.{u} J)))
                (ProfiniteGrp.group.{u} J)))
            (P a)))) :=
  @LocalConjugacy.lemma_1_2_preparedProof
