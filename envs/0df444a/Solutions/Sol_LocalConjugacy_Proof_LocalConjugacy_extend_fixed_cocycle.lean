-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.extend_fixed_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:49:30.125169+00:00
-- url     : https://prove2.me/submissions/ac53c7db-d5c0-4d06-887f-5d2303b2da05

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

namespace LocalConjugacy

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [IsTopologicalGroup N]
  [MulDistribMulAction J N] [ContinuousSMul J N]

/-- Extend a cocycle on a closed normal subgroup by making it trivial on a
closed supplement. Fixedness and triviality on the intersection are exactly
the compatibility conditions for this construction. -/
private theorem extend_fixed_cocycle_preparedProof (K Q : Subgroup J) [K.Normal]
    (hK : IsClosed (K : Set J)) (hQ : IsClosed (Q : Set J)) (hs : Supplements K Q)
    (f : Cocycle (N := N) K)
    (hfix : ∀ q : Q, twistCocycle f q = f)
    (htriv : ∀ (x : J) (_ : x ∈ Q) (hx : x ∈ K), f.toFun ⟨x, hx⟩ = 1) :
    ∃ F : Cocycle (N := N) (⊤ : Subgroup J), restrictCocycle le_top F = f := by
  classical
  have hs' := hs
  choose a ha b hb he using hs'
  let F : J → N := fun j => f.toFun ⟨a j, ha j⟩
  have hval (x : K) (q : Q) : F ((x : J) * q) = f.toFun x := by
    let j : J := (x : J) * q
    let d : K := ⟨(x : J)⁻¹ * a j, K.mul_mem (K.inv_mem x.property) (ha j)⟩
    have hd : (d : J) ∈ Q := by
      have hd' : (x : J)⁻¹ * a j = (q : J) * (b j)⁻¹ := by
        have hh := he j
        change a j * b j = (x : J) * q at hh
        calc
          (x : J)⁻¹ * a j = (x : J)⁻¹ * (a j * b j) * (b j)⁻¹ := by group
          _ = (q : J) * (b j)⁻¹ := by rw [hh]; group
      rw [show (d : J) = (x : J)⁻¹ * a j from rfl, hd']
      exact Q.mul_mem q.property (Q.inv_mem (hb j))
    have hx : (⟨a j, ha j⟩ : K) = x * d := by apply Subtype.ext; dsimp [d]; group
    change f.toFun ⟨a j, ha j⟩ = f.toFun x
    rw [hx, f.map_mul, htriv d hd d.property, smul_one, mul_one]
  have hconj (q : Q) (y : K) :
      f.toFun ⟨(q : J) * y * (q : J)⁻¹,
        (inferInstance : K.Normal).conj_mem y y.property q⟩ = (q : J) • f.toFun y := by
    have hh := congrArg (fun g : Cocycle (N := N) K =>
      g.toFun ⟨(q : J) * y * (q : J)⁻¹,
        (inferInstance : K.Normal).conj_mem y y.property q⟩) (hfix q)
    change (q : J) • f.toFun ⟨(q : J)⁻¹ * ((q : J) * y * (q : J)⁻¹) * q, _⟩ = _ at hh
    have hz : (q : J)⁻¹ * ((q : J) * y * (q : J)⁻¹) * q = y := by group
    simpa only [hz] using hh.symm
  have hmul (j k : J) : F (j * k) = F j * (j • F k) := by
    obtain ⟨x, hx, q, hq, rfl⟩ := hs j
    obtain ⟨y, hy, r, hr, rfl⟩ := hs k
    let z : K := ⟨q * y * q⁻¹, (inferInstance : K.Normal).conj_mem y hy q⟩
    have hm : x * q * (y * r) = (x * (q * y * q⁻¹)) * (q * r) := by group
    rw [hm]
    change F (↑((⟨x, hx⟩ : K) * z) * ↑((⟨q, hq⟩ : Q) * ⟨r, hr⟩)) = _
    rw [hval (⟨x, hx⟩ * z) (⟨q, hq⟩ * ⟨r, hr⟩), f.map_mul]
    dsimp only [z, Subgroup.coe_mk]
    rw [hconj ⟨q, hq⟩ ⟨y, hy⟩, hval ⟨x, hx⟩ ⟨q, hq⟩, hval ⟨y, hy⟩ ⟨r, hr⟩]
    exact congrArg (fun t => f.toFun ⟨x, hx⟩ * t) (mul_smul x q (f.toFun ⟨y, hy⟩)).symm
  letI := profinite_closed_subgroup K hK
  letI := profinite_closed_subgroup Q hQ
  let m : K × Q → J := fun t => (t.1 : J) * t.2
  have hm : Continuous m := (continuous_subtype_val.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)
  have hms : Function.Surjective m := by
    intro j
    obtain ⟨x, hx, q, hq, he⟩ := hs j
    exact ⟨(⟨x, hx⟩, ⟨q, hq⟩), he⟩
  have hcont : Continuous F := hm.isClosedMap.isQuotientMap hm hms |>.continuous_iff.mpr (by
    change Continuous (fun t : K × Q => F ((t.1 : J) * t.2))
    exact (f.continuous_toFun.comp (continuous_fst : Continuous (Prod.fst : K × Q → K))).congr
      (fun t => (hval t.1 t.2).symm))
  let F' : Cocycle (N := N) (⊤ : Subgroup J) :=
    { toFun := fun j => F j
      continuous_toFun := hcont.comp continuous_subtype_val
      map_mul := fun j k => hmul j k }
  refine ⟨F', Cocycle.ext fun x => ?_⟩
  change F x = f.toFun x
  simpa only [Subgroup.coe_one, mul_one] using hval x 1

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@IsTopologicalGroup.{u_2} N inst_4 inst_1]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [inst_7 :
    @ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  (K Q : @Subgroup.{u_1} J inst) [inst_8 : @Subgroup.Normal.{u_1} J inst K]
  (hK :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) K))
  (hQ :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) Q))
  (hs : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} J inst K Q)
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K)
  (hfix :
    ∀
      (q :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x),
      @Eq.{max (u_1 + 1) (u_2 + 1)}
        (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K)
        (@LocalConjugacy.Proof.LocalConjugacy.twistCocycle.{u_1, u_2} J N inst inst_1 inst_2
          (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} J inst inst_2 inst_3) inst_4 inst_6
          inst_7 K inst_8 f
          (@Subtype.val.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q
                x)
            q))
        f)
  (htriv :
    ∀ (x : J),
      @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x →
        ∀
          (hx :
            @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K x),
          @Eq.{u_2 + 1} N
            (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K f
              (@Subtype.mk.{u_1 + 1} J
                (fun (x : J) =>
                  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                    K x)
                x hx))
            (@OfNat.ofNat.{u_2} N (nat_lit 1)
              (@One.toOfNat1.{u_2} N
                (@InvOneClass.toOne.{u_2} N
                  (@DivInvOneMonoid.toInvOneClass.{u_2} N
                    (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1))))))),
  @Exists.{max (u_1 + 1) (u_2 + 1)}
    (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
    fun
      (F :
        @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
          (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))) =>
    @Eq.{max (u_1 + 1) (u_2 + 1)}
      (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K)
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
          (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))))
        (@le_top.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
              (@Subgroup.instCompleteLattice.{u_1} J inst)))
          K)
        F)
      f :=
  @LocalConjugacy.Proof.LocalConjugacy.extend_fixed_cocycle_preparedProof
