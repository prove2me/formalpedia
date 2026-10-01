-- Prove2me | solution 1 for LocalConjugacy.counterexample_heisenberg
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:34:10.844705+00:00
-- url     : https://prove2.me/submissions/67c2b6c0-c268-4c05-91d6-48147d64dcea

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_HeisenbergExample_locally_contains
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_HeisenbergExample_split
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_HeisenbergExample_supersolvable_G

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section


/-!
The mission uses Mathlib's standard public interfaces.  These elementary bridges
connect them to the equivalent internal interfaces of the existing proof corpus.
Every conversion is proved; no extra assumption is added to a paper statement.
-/
namespace LocalConjugacy



/-- Surjectivity of the unique-product map supplies a setwise supplement. -/
private theorem supplement_of_complement {G : Type*} [Group G] {N H : Subgroup G}
    (h : N.IsComplement' H) : Supplements N H := by
  intro g
  obtain ⟨⟨n, x⟩, he⟩ := h.2 g
  exact ⟨n, n.property, x, x.property, he⟩

/-- The two formulations of an internal semidirect product are equivalent:
unique factorization is exactly existence together with trivial intersection. -/
private theorem splits_iff_internal {G : Type*} [Group G] (N J : Subgroup G) :
    Splits N J ↔ Proof.LocalConjugacy.Splits N J := by
  constructor
  · rintro ⟨hn, hc⟩
    exact ⟨hn, supplement_of_complement hc, hc.disjoint.eq_bot⟩
  · rintro ⟨hn, hs, hd⟩
    refine ⟨hn, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (disjoint_iff.mpr hd) ?_⟩
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨n, hn, j, hj, he⟩ := hs g
    exact ⟨n, hn, j, hj, he⟩

/-- Normality inside N says that conjugation by each element of N preserves
its intersection with H.  The subtype formulation keeps the ambient group clear. -/
private theorem intersectionNormal_iff_internal {G : Type*} [Group G] (N H : Subgroup G) :
    IntersectionNormal N H ↔ Proof.LocalConjugacy.IntersectionNormal N H := by
  constructor
  · intro h n hn d hd
    exact h.conj_mem ⟨d, hd.1⟩ hd ⟨n, hn⟩
  · intro h
    constructor
    intro d hd n
    exact h n n.property d hd





end LocalConjugacy

end

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy

variable {G Ω : Type*} [Group G] [MulAction G Ω]

/-- The geometric step in Corollary 1.4 and Proposition 4.2. -/
private theorem fixedPoint_of_conjugate_le_stabilizer (J : Subgroup G) (x : Ω)
    (g : G) (h : conjugate g J ≤ MulAction.stabilizer G x) :
    HasFixedPoint (Ω := Ω) J := by
  refine ⟨g⁻¹ • x, ?_⟩
  intro j hj
  have hf : (g * j * g⁻¹) • x = x := h (Subgroup.mem_map_of_mem _ hj)
  have ht := congrArg (fun y : Ω => g⁻¹ • y) hf
  simpa [mul_smul] using ht









end LocalConjugacy

end LocalConjugacy.Proof

end

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




































private theorem card_N : Fintype.card N = 27 := by decide

private theorem nilpotent_N : Group.IsNilpotent N := by
  apply (IsPGroup.of_card (p := 3) (n := 3) ?_).isNilpotent
  simpa [Nat.card_eq_fintype_card] using card_N










private theorem card_H : Fintype.card H = 18 := by decide











private theorem no_common_fixed : ¬ ∃ x : Ω, c • x = x ∧ t • x = x := by decide

private theorem no_J_fixed : ¬ HasFixedPoint (Ω := Ω) J := by
  rintro ⟨x, hx⟩
  apply no_common_fixed
  exact ⟨x, hx c ⟨_, rfl⟩, hx t ⟨_, rfl⟩⟩



private theorem intersection_not_normal : ¬ IntersectionNormal N H := by
  change ¬ ∀ n : G, n ∈ N → ∀ d : G, (d ∈ N ∧ d ∈ H) →
    (n * d * n⁻¹ ∈ N ∧ n * d * n⁻¹ ∈ H)
  decide























private theorem not_contains : ¬ ∃ g : G, conjugate g J ≤ H := by
  rintro ⟨g, hg⟩
  exact no_J_fixed (fixedPoint_of_conjugate_le_stabilizer J ((0, 1) : Ω) g hg)





private theorem pronilpotent_J : Pronilpotent J := by
  let := cyclic_J
  let : CommGroup J := IsCyclic.commGroup
  intro U
  infer_instance






end LocalConjugacy.HeisenbergExample

end LocalConjugacy.Proof

end

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


/-! The second counterexample with all concrete group identifications included. -/
open LocalConjugacy
open LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- The explicit nine-point wreath action gives the exact counterexample in the draft. -/
private theorem LocalConjugacy.counterexample_heisenberg_preparedProof :
    ∃ (G : ProfiniteGrp.{0}) (N J H : Subgroup G),
      -- All concrete group identifications in the source are part of the target.
      Finite G ∧ Nonempty (G ≃* WreathC3S3) ∧
      Nonempty (N ≃* Heisenberg3) ∧
      Nonempty (J ≃* Multiplicative (ZMod 6)) ∧
      Nonempty (H ≃* C3 × S3) ∧
      Nat.card G = 162 ∧ Nat.card N = 27 ∧ Nat.card J = 6 ∧ Nat.card H = 18 ∧
      -- N and J form the specified internal semidirect product.
      Splits N J ∧ Group.IsNilpotent N ∧ Group.IsNilpotent J ∧ Supersolvable G ∧
      IsClosed (N : Set G) ∧ IsClosed (J : Set G) ∧ IsClosed (H : Set G) ∧
      -- The local inclusion test succeeds, but global inclusion fails.
      LocallyContains H J ∧ (¬ ∃ g : G, conjugate g J ≤ H) ∧
      ¬ IntersectionNormal N H := by
  -- Reuse the constructed finite group and its three explicit subgroups.
  refine ⟨ProfiniteGrp.of G, N, J, H, inferInstance,
    ⟨Proof.wreathEquiv⟩, ⟨Proof.heisenbergEquiv⟩, ⟨Proof.cyclicSixEquiv⟩,
    ⟨Proof.stabilizerProductEquiv⟩, ?_, ?_, ?_, ?_,
    (splits_iff_internal N J).mpr split, nilpotent_N, ?_, supersolvable_G,
    isClosed_discrete _, isClosed_discrete _, isClosed_discrete _,
    locally_contains, not_contains, ?_⟩
  · -- The wreath-product coordinates have 27 times 6 elements.
    rw [Nat.card_eq_fintype_card]
    decide
  · simpa [Nat.card_eq_fintype_card] using card_N
  · simpa [Nat.card_eq_fintype_card] using card_J
  · simpa [Nat.card_eq_fintype_card] using card_H
  · -- In a finite group, pronilpotence is ordinary nilpotence.
    exact Proof.LocalConjugacy.pronilpotent_iff_nilpotent.mp pronilpotent_J
  · -- Transfer the explicit failure of invariance to Mathlib's normality predicate.
    exact fun h => intersection_not_normal ((intersectionNormal_iff_internal N H).mp h)

end

theorem solution :
@Exists.{2} ProfiniteGrp.{0} fun (G : ProfiniteGrp.{0}) =>
  @Exists.{1}
    (@Subgroup.{0}
      (TopCat.carrier.{0}
        (@CompHausLike.toTop.{0}
          (fun (X : TopCat.{0}) => @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
          (ProfiniteGrp.toProfinite.{0} G)))
      (ProfiniteGrp.group.{0} G))
    fun
      (N :
        @Subgroup.{0}
          (TopCat.carrier.{0}
            (@CompHausLike.toTop.{0}
              (fun (X : TopCat.{0}) => @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
              (ProfiniteGrp.toProfinite.{0} G)))
          (ProfiniteGrp.group.{0} G)) =>
    @Exists.{1}
      (@Subgroup.{0}
        (TopCat.carrier.{0}
          (@CompHausLike.toTop.{0}
            (fun (X : TopCat.{0}) => @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
            (ProfiniteGrp.toProfinite.{0} G)))
        (ProfiniteGrp.group.{0} G))
      fun
        (J :
          @Subgroup.{0}
            (TopCat.carrier.{0}
              (@CompHausLike.toTop.{0}
                (fun (X : TopCat.{0}) => @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                (ProfiniteGrp.toProfinite.{0} G)))
            (ProfiniteGrp.group.{0} G)) =>
      @Exists.{1}
        (@Subgroup.{0}
          (TopCat.carrier.{0}
            (@CompHausLike.toTop.{0}
              (fun (X : TopCat.{0}) => @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
              (ProfiniteGrp.toProfinite.{0} G)))
          (ProfiniteGrp.group.{0} G))
        fun
          (H :
            @Subgroup.{0}
              (TopCat.carrier.{0}
                (@CompHausLike.toTop.{0}
                  (fun (X : TopCat.{0}) => @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                  (ProfiniteGrp.toProfinite.{0} G)))
              (ProfiniteGrp.group.{0} G)) =>
        And
          (Finite.{1}
            (TopCat.carrier.{0}
              (@CompHausLike.toTop.{0}
                (fun (X : TopCat.{0}) => @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                (ProfiniteGrp.toProfinite.{0} G))))
          (And
            (Nonempty.{1}
              (@MulEquiv.{0, 0}
                (TopCat.carrier.{0}
                  (@CompHausLike.toTop.{0}
                    (fun (X : TopCat.{0}) => @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                    (ProfiniteGrp.toProfinite.{0} G)))
                LocalConjugacy.WreathC3S3
                (@MulOne.toMul.{0}
                  (TopCat.carrier.{0}
                    (@CompHausLike.toTop.{0}
                      (fun (X : TopCat.{0}) => @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                      (ProfiniteGrp.toProfinite.{0} G)))
                  (@MulOneClass.toMulOne.{0}
                    (TopCat.carrier.{0}
                      (@CompHausLike.toTop.{0}
                        (fun (X : TopCat.{0}) =>
                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                        (ProfiniteGrp.toProfinite.{0} G)))
                    (@Monoid.toMulOneClass.{0}
                      (TopCat.carrier.{0}
                        (@CompHausLike.toTop.{0}
                          (fun (X : TopCat.{0}) =>
                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                          (ProfiniteGrp.toProfinite.{0} G)))
                      (@DivInvMonoid.toMonoid.{0}
                        (TopCat.carrier.{0}
                          (@CompHausLike.toTop.{0}
                            (fun (X : TopCat.{0}) =>
                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                            (ProfiniteGrp.toProfinite.{0} G)))
                        (@Group.toDivInvMonoid.{0}
                          (TopCat.carrier.{0}
                            (@CompHausLike.toTop.{0}
                              (fun (X : TopCat.{0}) =>
                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                              (ProfiniteGrp.toProfinite.{0} G)))
                          (ProfiniteGrp.group.{0} G))))))
                (@SemidirectProduct.instMul.{0, 0} LocalConjugacy.WreathBase LocalConjugacy.S3
                  (@Pi.group.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => LocalConjugacy.C3)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
                    @Multiplicative.group.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@AddGroupWithOne.toAddGroup.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@Ring.toAddGroupWithOne.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@Field.toDivisionRing.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                Nat.fact_prime_three))))))
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  LocalConjugacy.wreathAction)))
            (And
              (Nonempty.{1}
                (@MulEquiv.{0, 0}
                  (@Subtype.{1}
                    (TopCat.carrier.{0}
                      (@CompHausLike.toTop.{0}
                        (fun (X : TopCat.{0}) =>
                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                        (ProfiniteGrp.toProfinite.{0} G)))
                    fun
                      (x :
                        TopCat.carrier.{0}
                          (@CompHausLike.toTop.{0}
                            (fun (X : TopCat.{0}) =>
                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                            (ProfiniteGrp.toProfinite.{0} G))) =>
                    @Membership.mem.{0, 0}
                      (TopCat.carrier.{0}
                        (@CompHausLike.toTop.{0}
                          (fun (X : TopCat.{0}) =>
                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                          (ProfiniteGrp.toProfinite.{0} G)))
                      (@Subgroup.{0}
                        (TopCat.carrier.{0}
                          (@CompHausLike.toTop.{0}
                            (fun (X : TopCat.{0}) =>
                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                            (ProfiniteGrp.toProfinite.{0} G)))
                        (ProfiniteGrp.group.{0} G))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0}
                          (TopCat.carrier.{0}
                            (@CompHausLike.toTop.{0}
                              (fun (X : TopCat.{0}) =>
                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                              (ProfiniteGrp.toProfinite.{0} G)))
                          (ProfiniteGrp.group.{0} G))
                        (TopCat.carrier.{0}
                          (@CompHausLike.toTop.{0}
                            (fun (X : TopCat.{0}) =>
                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                            (ProfiniteGrp.toProfinite.{0} G)))
                        (@Subgroup.instSetLike.{0}
                          (TopCat.carrier.{0}
                            (@CompHausLike.toTop.{0}
                              (fun (X : TopCat.{0}) =>
                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                              (ProfiniteGrp.toProfinite.{0} G)))
                          (ProfiniteGrp.group.{0} G)))
                      N x)
                  LocalConjugacy.Heisenberg3
                  (@Subgroup.mul.{0}
                    (TopCat.carrier.{0}
                      (@CompHausLike.toTop.{0}
                        (fun (X : TopCat.{0}) =>
                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                        (ProfiniteGrp.toProfinite.{0} G)))
                    (ProfiniteGrp.group.{0} G) N)
                  LocalConjugacy.heisenbergMul))
              (And
                (Nonempty.{1}
                  (@MulEquiv.{0, 0}
                    (@Subtype.{1}
                      (TopCat.carrier.{0}
                        (@CompHausLike.toTop.{0}
                          (fun (X : TopCat.{0}) =>
                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                          (ProfiniteGrp.toProfinite.{0} G)))
                      fun
                        (x :
                          TopCat.carrier.{0}
                            (@CompHausLike.toTop.{0}
                              (fun (X : TopCat.{0}) =>
                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                              (ProfiniteGrp.toProfinite.{0} G))) =>
                      @Membership.mem.{0, 0}
                        (TopCat.carrier.{0}
                          (@CompHausLike.toTop.{0}
                            (fun (X : TopCat.{0}) =>
                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                            (ProfiniteGrp.toProfinite.{0} G)))
                        (@Subgroup.{0}
                          (TopCat.carrier.{0}
                            (@CompHausLike.toTop.{0}
                              (fun (X : TopCat.{0}) =>
                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                              (ProfiniteGrp.toProfinite.{0} G)))
                          (ProfiniteGrp.group.{0} G))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0}
                            (TopCat.carrier.{0}
                              (@CompHausLike.toTop.{0}
                                (fun (X : TopCat.{0}) =>
                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                (ProfiniteGrp.toProfinite.{0} G)))
                            (ProfiniteGrp.group.{0} G))
                          (TopCat.carrier.{0}
                            (@CompHausLike.toTop.{0}
                              (fun (X : TopCat.{0}) =>
                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                              (ProfiniteGrp.toProfinite.{0} G)))
                          (@Subgroup.instSetLike.{0}
                            (TopCat.carrier.{0}
                              (@CompHausLike.toTop.{0}
                                (fun (X : TopCat.{0}) =>
                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                (ProfiniteGrp.toProfinite.{0} G)))
                            (ProfiniteGrp.group.{0} G)))
                        J x)
                    (Multiplicative.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                    (@Subgroup.mul.{0}
                      (TopCat.carrier.{0}
                        (@CompHausLike.toTop.{0}
                          (fun (X : TopCat.{0}) =>
                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                          (ProfiniteGrp.toProfinite.{0} G)))
                      (ProfiniteGrp.group.{0} G) J)
                    (@Multiplicative.mul.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (@Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                        (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                          (@CommSemiring.toSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                            (@CommRing.toCommSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))))
                (And
                  (Nonempty.{1}
                    (@MulEquiv.{0, 0}
                      (@Subtype.{1}
                        (TopCat.carrier.{0}
                          (@CompHausLike.toTop.{0}
                            (fun (X : TopCat.{0}) =>
                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                            (ProfiniteGrp.toProfinite.{0} G)))
                        fun
                          (x :
                            TopCat.carrier.{0}
                              (@CompHausLike.toTop.{0}
                                (fun (X : TopCat.{0}) =>
                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                (ProfiniteGrp.toProfinite.{0} G))) =>
                        @Membership.mem.{0, 0}
                          (TopCat.carrier.{0}
                            (@CompHausLike.toTop.{0}
                              (fun (X : TopCat.{0}) =>
                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                              (ProfiniteGrp.toProfinite.{0} G)))
                          (@Subgroup.{0}
                            (TopCat.carrier.{0}
                              (@CompHausLike.toTop.{0}
                                (fun (X : TopCat.{0}) =>
                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                (ProfiniteGrp.toProfinite.{0} G)))
                            (ProfiniteGrp.group.{0} G))
                          (@SetLike.instMembership.{0, 0}
                            (@Subgroup.{0}
                              (TopCat.carrier.{0}
                                (@CompHausLike.toTop.{0}
                                  (fun (X : TopCat.{0}) =>
                                    @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                  (ProfiniteGrp.toProfinite.{0} G)))
                              (ProfiniteGrp.group.{0} G))
                            (TopCat.carrier.{0}
                              (@CompHausLike.toTop.{0}
                                (fun (X : TopCat.{0}) =>
                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                (ProfiniteGrp.toProfinite.{0} G)))
                            (@Subgroup.instSetLike.{0}
                              (TopCat.carrier.{0}
                                (@CompHausLike.toTop.{0}
                                  (fun (X : TopCat.{0}) =>
                                    @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                  (ProfiniteGrp.toProfinite.{0} G)))
                              (ProfiniteGrp.group.{0} G)))
                          H x)
                      (Prod.{0, 0} LocalConjugacy.C3 LocalConjugacy.S3)
                      (@Subgroup.mul.{0}
                        (TopCat.carrier.{0}
                          (@CompHausLike.toTop.{0}
                            (fun (X : TopCat.{0}) =>
                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                            (ProfiniteGrp.toProfinite.{0} G)))
                        (ProfiniteGrp.group.{0} G) H)
                      (@Prod.instMul.{0, 0} LocalConjugacy.C3 LocalConjugacy.S3
                        (@Multiplicative.mul.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (@Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (@instDistribOfSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (@DivisionSemiring.toSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (@Semifield.toDivisionSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (@Field.toSemifield.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                    (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      Nat.fact_prime_three)))))))
                        (@Equiv.Perm.instMul.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
                  (And
                    (@Eq.{1} Nat
                      (Nat.card.{0}
                        (TopCat.carrier.{0}
                          (@CompHausLike.toTop.{0}
                            (fun (X : TopCat.{0}) =>
                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                            (ProfiniteGrp.toProfinite.{0} G))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                    (And
                      (@Eq.{1} Nat
                        (Nat.card.{0}
                          (@Subtype.{1}
                            (TopCat.carrier.{0}
                              (@CompHausLike.toTop.{0}
                                (fun (X : TopCat.{0}) =>
                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                (ProfiniteGrp.toProfinite.{0} G)))
                            fun
                              (x :
                                TopCat.carrier.{0}
                                  (@CompHausLike.toTop.{0}
                                    (fun (X : TopCat.{0}) =>
                                      @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                    (ProfiniteGrp.toProfinite.{0} G))) =>
                            @Membership.mem.{0, 0}
                              (TopCat.carrier.{0}
                                (@CompHausLike.toTop.{0}
                                  (fun (X : TopCat.{0}) =>
                                    @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                  (ProfiniteGrp.toProfinite.{0} G)))
                              (@Subgroup.{0}
                                (TopCat.carrier.{0}
                                  (@CompHausLike.toTop.{0}
                                    (fun (X : TopCat.{0}) =>
                                      @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                    (ProfiniteGrp.toProfinite.{0} G)))
                                (ProfiniteGrp.group.{0} G))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0}
                                  (TopCat.carrier.{0}
                                    (@CompHausLike.toTop.{0}
                                      (fun (X : TopCat.{0}) =>
                                        @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                      (ProfiniteGrp.toProfinite.{0} G)))
                                  (ProfiniteGrp.group.{0} G))
                                (TopCat.carrier.{0}
                                  (@CompHausLike.toTop.{0}
                                    (fun (X : TopCat.{0}) =>
                                      @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                    (ProfiniteGrp.toProfinite.{0} G)))
                                (@Subgroup.instSetLike.{0}
                                  (TopCat.carrier.{0}
                                    (@CompHausLike.toTop.{0}
                                      (fun (X : TopCat.{0}) =>
                                        @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                      (ProfiniteGrp.toProfinite.{0} G)))
                                  (ProfiniteGrp.group.{0} G)))
                              N x))
                        (@OfNat.ofNat.{0} Nat (nat_lit 27) (instOfNatNat (nat_lit 27))))
                      (And
                        (@Eq.{1} Nat
                          (Nat.card.{0}
                            (@Subtype.{1}
                              (TopCat.carrier.{0}
                                (@CompHausLike.toTop.{0}
                                  (fun (X : TopCat.{0}) =>
                                    @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                  (ProfiniteGrp.toProfinite.{0} G)))
                              fun
                                (x :
                                  TopCat.carrier.{0}
                                    (@CompHausLike.toTop.{0}
                                      (fun (X : TopCat.{0}) =>
                                        @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                      (ProfiniteGrp.toProfinite.{0} G))) =>
                              @Membership.mem.{0, 0}
                                (TopCat.carrier.{0}
                                  (@CompHausLike.toTop.{0}
                                    (fun (X : TopCat.{0}) =>
                                      @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                    (ProfiniteGrp.toProfinite.{0} G)))
                                (@Subgroup.{0}
                                  (TopCat.carrier.{0}
                                    (@CompHausLike.toTop.{0}
                                      (fun (X : TopCat.{0}) =>
                                        @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                      (ProfiniteGrp.toProfinite.{0} G)))
                                  (ProfiniteGrp.group.{0} G))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0}
                                    (TopCat.carrier.{0}
                                      (@CompHausLike.toTop.{0}
                                        (fun (X : TopCat.{0}) =>
                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                        (ProfiniteGrp.toProfinite.{0} G)))
                                    (ProfiniteGrp.group.{0} G))
                                  (TopCat.carrier.{0}
                                    (@CompHausLike.toTop.{0}
                                      (fun (X : TopCat.{0}) =>
                                        @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                      (ProfiniteGrp.toProfinite.{0} G)))
                                  (@Subgroup.instSetLike.{0}
                                    (TopCat.carrier.{0}
                                      (@CompHausLike.toTop.{0}
                                        (fun (X : TopCat.{0}) =>
                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                        (ProfiniteGrp.toProfinite.{0} G)))
                                    (ProfiniteGrp.group.{0} G)))
                                J x))
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                        (And
                          (@Eq.{1} Nat
                            (Nat.card.{0}
                              (@Subtype.{1}
                                (TopCat.carrier.{0}
                                  (@CompHausLike.toTop.{0}
                                    (fun (X : TopCat.{0}) =>
                                      @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                    (ProfiniteGrp.toProfinite.{0} G)))
                                fun
                                  (x :
                                    TopCat.carrier.{0}
                                      (@CompHausLike.toTop.{0}
                                        (fun (X : TopCat.{0}) =>
                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                        (ProfiniteGrp.toProfinite.{0} G))) =>
                                @Membership.mem.{0, 0}
                                  (TopCat.carrier.{0}
                                    (@CompHausLike.toTop.{0}
                                      (fun (X : TopCat.{0}) =>
                                        @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                      (ProfiniteGrp.toProfinite.{0} G)))
                                  (@Subgroup.{0}
                                    (TopCat.carrier.{0}
                                      (@CompHausLike.toTop.{0}
                                        (fun (X : TopCat.{0}) =>
                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                        (ProfiniteGrp.toProfinite.{0} G)))
                                    (ProfiniteGrp.group.{0} G))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0}
                                      (TopCat.carrier.{0}
                                        (@CompHausLike.toTop.{0}
                                          (fun (X : TopCat.{0}) =>
                                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                          (ProfiniteGrp.toProfinite.{0} G)))
                                      (ProfiniteGrp.group.{0} G))
                                    (TopCat.carrier.{0}
                                      (@CompHausLike.toTop.{0}
                                        (fun (X : TopCat.{0}) =>
                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                        (ProfiniteGrp.toProfinite.{0} G)))
                                    (@Subgroup.instSetLike.{0}
                                      (TopCat.carrier.{0}
                                        (@CompHausLike.toTop.{0}
                                          (fun (X : TopCat.{0}) =>
                                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                          (ProfiniteGrp.toProfinite.{0} G)))
                                      (ProfiniteGrp.group.{0} G)))
                                  H x))
                            (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
                          (And
                            (@LocalConjugacy.Splits.{0}
                              (TopCat.carrier.{0}
                                (@CompHausLike.toTop.{0}
                                  (fun (X : TopCat.{0}) =>
                                    @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                  (ProfiniteGrp.toProfinite.{0} G)))
                              (ProfiniteGrp.group.{0} G) N J)
                            (And
                              (@Group.IsNilpotent.{0}
                                (@Subtype.{1}
                                  (TopCat.carrier.{0}
                                    (@CompHausLike.toTop.{0}
                                      (fun (X : TopCat.{0}) =>
                                        @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                      (ProfiniteGrp.toProfinite.{0} G)))
                                  fun
                                    (x :
                                      TopCat.carrier.{0}
                                        (@CompHausLike.toTop.{0}
                                          (fun (X : TopCat.{0}) =>
                                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                          (ProfiniteGrp.toProfinite.{0} G))) =>
                                  @Membership.mem.{0, 0}
                                    (TopCat.carrier.{0}
                                      (@CompHausLike.toTop.{0}
                                        (fun (X : TopCat.{0}) =>
                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                        (ProfiniteGrp.toProfinite.{0} G)))
                                    (@Subgroup.{0}
                                      (TopCat.carrier.{0}
                                        (@CompHausLike.toTop.{0}
                                          (fun (X : TopCat.{0}) =>
                                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                          (ProfiniteGrp.toProfinite.{0} G)))
                                      (ProfiniteGrp.group.{0} G))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0}
                                        (TopCat.carrier.{0}
                                          (@CompHausLike.toTop.{0}
                                            (fun (X : TopCat.{0}) =>
                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                            (ProfiniteGrp.toProfinite.{0} G)))
                                        (ProfiniteGrp.group.{0} G))
                                      (TopCat.carrier.{0}
                                        (@CompHausLike.toTop.{0}
                                          (fun (X : TopCat.{0}) =>
                                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                          (ProfiniteGrp.toProfinite.{0} G)))
                                      (@Subgroup.instSetLike.{0}
                                        (TopCat.carrier.{0}
                                          (@CompHausLike.toTop.{0}
                                            (fun (X : TopCat.{0}) =>
                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                            (ProfiniteGrp.toProfinite.{0} G)))
                                        (ProfiniteGrp.group.{0} G)))
                                    N x)
                                (@Subgroup.toGroup.{0}
                                  (TopCat.carrier.{0}
                                    (@CompHausLike.toTop.{0}
                                      (fun (X : TopCat.{0}) =>
                                        @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                      (ProfiniteGrp.toProfinite.{0} G)))
                                  (ProfiniteGrp.group.{0} G) N))
                              (And
                                (@Group.IsNilpotent.{0}
                                  (@Subtype.{1}
                                    (TopCat.carrier.{0}
                                      (@CompHausLike.toTop.{0}
                                        (fun (X : TopCat.{0}) =>
                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                        (ProfiniteGrp.toProfinite.{0} G)))
                                    fun
                                      (x :
                                        TopCat.carrier.{0}
                                          (@CompHausLike.toTop.{0}
                                            (fun (X : TopCat.{0}) =>
                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                            (ProfiniteGrp.toProfinite.{0} G))) =>
                                    @Membership.mem.{0, 0}
                                      (TopCat.carrier.{0}
                                        (@CompHausLike.toTop.{0}
                                          (fun (X : TopCat.{0}) =>
                                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                          (ProfiniteGrp.toProfinite.{0} G)))
                                      (@Subgroup.{0}
                                        (TopCat.carrier.{0}
                                          (@CompHausLike.toTop.{0}
                                            (fun (X : TopCat.{0}) =>
                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                            (ProfiniteGrp.toProfinite.{0} G)))
                                        (ProfiniteGrp.group.{0} G))
                                      (@SetLike.instMembership.{0, 0}
                                        (@Subgroup.{0}
                                          (TopCat.carrier.{0}
                                            (@CompHausLike.toTop.{0}
                                              (fun (X : TopCat.{0}) =>
                                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                              (ProfiniteGrp.toProfinite.{0} G)))
                                          (ProfiniteGrp.group.{0} G))
                                        (TopCat.carrier.{0}
                                          (@CompHausLike.toTop.{0}
                                            (fun (X : TopCat.{0}) =>
                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                            (ProfiniteGrp.toProfinite.{0} G)))
                                        (@Subgroup.instSetLike.{0}
                                          (TopCat.carrier.{0}
                                            (@CompHausLike.toTop.{0}
                                              (fun (X : TopCat.{0}) =>
                                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                              (ProfiniteGrp.toProfinite.{0} G)))
                                          (ProfiniteGrp.group.{0} G)))
                                      J x)
                                  (@Subgroup.toGroup.{0}
                                    (TopCat.carrier.{0}
                                      (@CompHausLike.toTop.{0}
                                        (fun (X : TopCat.{0}) =>
                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                        (ProfiniteGrp.toProfinite.{0} G)))
                                    (ProfiniteGrp.group.{0} G) J))
                                (And
                                  (@LocalConjugacy.Supersolvable.{0}
                                    (TopCat.carrier.{0}
                                      (@CompHausLike.toTop.{0}
                                        (fun (X : TopCat.{0}) =>
                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                        (ProfiniteGrp.toProfinite.{0} G)))
                                    (ProfiniteGrp.group.{0} G))
                                  (And
                                    (@IsClosed.{0}
                                      (TopCat.carrier.{0}
                                        (@CompHausLike.toTop.{0}
                                          (fun (X : TopCat.{0}) =>
                                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                          (ProfiniteGrp.toProfinite.{0} G)))
                                      (TopCat.str.{0}
                                        (@CompHausLike.toTop.{0}
                                          (fun (X : TopCat.{0}) =>
                                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                          (ProfiniteGrp.toProfinite.{0} G)))
                                      (@SetLike.coe.{0, 0}
                                        (@Subgroup.{0}
                                          (TopCat.carrier.{0}
                                            (@CompHausLike.toTop.{0}
                                              (fun (X : TopCat.{0}) =>
                                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                              (ProfiniteGrp.toProfinite.{0} G)))
                                          (ProfiniteGrp.group.{0} G))
                                        (TopCat.carrier.{0}
                                          (@CompHausLike.toTop.{0}
                                            (fun (X : TopCat.{0}) =>
                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                            (ProfiniteGrp.toProfinite.{0} G)))
                                        (@Subgroup.instSetLike.{0}
                                          (TopCat.carrier.{0}
                                            (@CompHausLike.toTop.{0}
                                              (fun (X : TopCat.{0}) =>
                                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                              (ProfiniteGrp.toProfinite.{0} G)))
                                          (ProfiniteGrp.group.{0} G))
                                        N))
                                    (And
                                      (@IsClosed.{0}
                                        (TopCat.carrier.{0}
                                          (@CompHausLike.toTop.{0}
                                            (fun (X : TopCat.{0}) =>
                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                            (ProfiniteGrp.toProfinite.{0} G)))
                                        (TopCat.str.{0}
                                          (@CompHausLike.toTop.{0}
                                            (fun (X : TopCat.{0}) =>
                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                            (ProfiniteGrp.toProfinite.{0} G)))
                                        (@SetLike.coe.{0, 0}
                                          (@Subgroup.{0}
                                            (TopCat.carrier.{0}
                                              (@CompHausLike.toTop.{0}
                                                (fun (X : TopCat.{0}) =>
                                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                    (TopCat.str.{0} X))
                                                (ProfiniteGrp.toProfinite.{0} G)))
                                            (ProfiniteGrp.group.{0} G))
                                          (TopCat.carrier.{0}
                                            (@CompHausLike.toTop.{0}
                                              (fun (X : TopCat.{0}) =>
                                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                              (ProfiniteGrp.toProfinite.{0} G)))
                                          (@Subgroup.instSetLike.{0}
                                            (TopCat.carrier.{0}
                                              (@CompHausLike.toTop.{0}
                                                (fun (X : TopCat.{0}) =>
                                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                    (TopCat.str.{0} X))
                                                (ProfiniteGrp.toProfinite.{0} G)))
                                            (ProfiniteGrp.group.{0} G))
                                          J))
                                      (And
                                        (@IsClosed.{0}
                                          (TopCat.carrier.{0}
                                            (@CompHausLike.toTop.{0}
                                              (fun (X : TopCat.{0}) =>
                                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                              (ProfiniteGrp.toProfinite.{0} G)))
                                          (TopCat.str.{0}
                                            (@CompHausLike.toTop.{0}
                                              (fun (X : TopCat.{0}) =>
                                                @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X) (TopCat.str.{0} X))
                                              (ProfiniteGrp.toProfinite.{0} G)))
                                          (@SetLike.coe.{0, 0}
                                            (@Subgroup.{0}
                                              (TopCat.carrier.{0}
                                                (@CompHausLike.toTop.{0}
                                                  (fun (X : TopCat.{0}) =>
                                                    @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                      (TopCat.str.{0} X))
                                                  (ProfiniteGrp.toProfinite.{0} G)))
                                              (ProfiniteGrp.group.{0} G))
                                            (TopCat.carrier.{0}
                                              (@CompHausLike.toTop.{0}
                                                (fun (X : TopCat.{0}) =>
                                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                    (TopCat.str.{0} X))
                                                (ProfiniteGrp.toProfinite.{0} G)))
                                            (@Subgroup.instSetLike.{0}
                                              (TopCat.carrier.{0}
                                                (@CompHausLike.toTop.{0}
                                                  (fun (X : TopCat.{0}) =>
                                                    @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                      (TopCat.str.{0} X))
                                                  (ProfiniteGrp.toProfinite.{0} G)))
                                              (ProfiniteGrp.group.{0} G))
                                            H))
                                        (And
                                          (@LocalConjugacy.LocallyContains.{0}
                                            (TopCat.carrier.{0}
                                              (@CompHausLike.toTop.{0}
                                                (fun (X : TopCat.{0}) =>
                                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                    (TopCat.str.{0} X))
                                                (ProfiniteGrp.toProfinite.{0} G)))
                                            (ProfiniteGrp.group.{0} G)
                                            (TopCat.str.{0}
                                              (@CompHausLike.toTop.{0}
                                                (fun (X : TopCat.{0}) =>
                                                  @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                    (TopCat.str.{0} X))
                                                (ProfiniteGrp.toProfinite.{0} G)))
                                            H J)
                                          (And
                                            (Not
                                              (@Exists.{1}
                                                (TopCat.carrier.{0}
                                                  (@CompHausLike.toTop.{0}
                                                    (fun (X : TopCat.{0}) =>
                                                      @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                        (TopCat.str.{0} X))
                                                    (ProfiniteGrp.toProfinite.{0} G)))
                                                fun
                                                  (g :
                                                    TopCat.carrier.{0}
                                                      (@CompHausLike.toTop.{0}
                                                        (fun (X : TopCat.{0}) =>
                                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                            (TopCat.str.{0} X))
                                                        (ProfiniteGrp.toProfinite.{0} G))) =>
                                                @LE.le.{0}
                                                  (@Subgroup.{0}
                                                    (TopCat.carrier.{0}
                                                      (@CompHausLike.toTop.{0}
                                                        (fun (X : TopCat.{0}) =>
                                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                            (TopCat.str.{0} X))
                                                        (ProfiniteGrp.toProfinite.{0} G)))
                                                    (ProfiniteGrp.group.{0} G))
                                                  (@Preorder.toLE.{0}
                                                    (@Subgroup.{0}
                                                      (TopCat.carrier.{0}
                                                        (@CompHausLike.toTop.{0}
                                                          (fun (X : TopCat.{0}) =>
                                                            @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                              (TopCat.str.{0} X))
                                                          (ProfiniteGrp.toProfinite.{0} G)))
                                                      (ProfiniteGrp.group.{0} G))
                                                    (@PartialOrder.toPreorder.{0}
                                                      (@Subgroup.{0}
                                                        (TopCat.carrier.{0}
                                                          (@CompHausLike.toTop.{0}
                                                            (fun (X : TopCat.{0}) =>
                                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                                (TopCat.str.{0} X))
                                                            (ProfiniteGrp.toProfinite.{0} G)))
                                                        (ProfiniteGrp.group.{0} G))
                                                      (@Subgroup.instPartialOrder.{0}
                                                        (TopCat.carrier.{0}
                                                          (@CompHausLike.toTop.{0}
                                                            (fun (X : TopCat.{0}) =>
                                                              @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                                (TopCat.str.{0} X))
                                                            (ProfiniteGrp.toProfinite.{0} G)))
                                                        (ProfiniteGrp.group.{0} G))))
                                                  (@LocalConjugacy.conjugate.{0}
                                                    (TopCat.carrier.{0}
                                                      (@CompHausLike.toTop.{0}
                                                        (fun (X : TopCat.{0}) =>
                                                          @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                            (TopCat.str.{0} X))
                                                        (ProfiniteGrp.toProfinite.{0} G)))
                                                    (ProfiniteGrp.group.{0} G) g J)
                                                  H))
                                            (Not
                                              (@LocalConjugacy.IntersectionNormal.{0}
                                                (TopCat.carrier.{0}
                                                  (@CompHausLike.toTop.{0}
                                                    (fun (X : TopCat.{0}) =>
                                                      @TotallyDisconnectedSpace.{0} (TopCat.carrier.{0} X)
                                                        (TopCat.str.{0} X))
                                                    (ProfiniteGrp.toProfinite.{0} G)))
                                                (ProfiniteGrp.group.{0} G) N H))))))))))))))))))) :=
  @LocalConjugacy.counterexample_heisenberg_preparedProof
