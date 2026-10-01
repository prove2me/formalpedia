-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.extend_cocycle_to_open_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T17:02:32.264641+00:00
-- url     : https://prove2.me/submissions/af2df35e-b9cf-4701-a8fa-df23faecb530

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
import Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_cocycle_neighborhood_kernel

/-! Kernel-checked proof and its local helpers, retaining their original scopes. -/

section




namespace LocalConjugacy.Proof

namespace LocalConjugacy
open scoped Pointwise

variable {J N : Type*} [Group J] [Group N]
  [TopologicalSpace J] [Profinite J] [TopologicalSpace N] [DiscreteTopology N]
  [MulDistribMulAction J N] [ContinuousSMul J N]



/-- Every continuous cocycle on a closed subgroup extends to an open subgroup
containing it. Only discreteness of the coefficients is needed. -/
private theorem extend_cocycle_to_open_subgroup_preparedProof (H : Subgroup J)
    (hH : IsClosed (H : Set J)) (f : Cocycle (N := N) H) :
    ∃ (V : Subgroup J) (hHV : H ≤ V), IsOpen (V : Set J) ∧
      ∃ F : Cocycle (N := N) V, restrictCocycle hHV F = f := by
  classical
  obtain ⟨U, hfix, htriv⟩ := exists_cocycle_neighborhood_kernel H hH f
  let V := H ⊔ U.toSubgroup
  have hHV : H ≤ V := le_sup_left
  have hUV : U.toSubgroup ≤ V := le_sup_right
  have hex (v : V) : ∃ x : H, ∃ u : U, (x : J) * u = v := by
    have hv : (v : J) ∈ (H : Set J) * (U.toSubgroup : Set J) := by
      rw [← Subgroup.mul_normal]
      exact v.property
    obtain ⟨x, hx, u, hu, he⟩ := hv
    exact ⟨⟨x, hx⟩, ⟨u, hu⟩, he⟩
  choose a b hab using hex
  let F : V → N := fun v => f.toFun (a v)
  let m : H × U → V := fun t =>
    ⟨(t.1 : J) * t.2, V.mul_mem (hHV t.1.property) (hUV t.2.property)⟩
  have hval (x : H) (u : U) : F (m (x, u)) = f.toFun x := by
    let v := m (x, u)
    let d : H := x⁻¹ * a v
    have hd : (d : J) ∈ U := by
      have he : (d : J) = (u : J) * (b v : J)⁻¹ := by
        have hh := hab v
        change (a v : J) * b v = (x : J) * u at hh
        change (x : J)⁻¹ * a v = (u : J) * (b v : J)⁻¹
        calc
          (x : J)⁻¹ * a v = (x : J)⁻¹ * ((a v : J) * b v) * (b v : J)⁻¹ := by group
          _ = (u : J) * (b v : J)⁻¹ := by rw [hh]; group
      rw [he]
      exact U.toSubgroup.mul_mem u.property (U.toSubgroup.inv_mem (b v).property)
    have he : a v = x * d := by dsimp [d]; group
    change f.toFun (a v) = f.toFun x
    rw [he, f.map_mul, htriv d hd, smul_one, mul_one]
  have hmul (v w : V) : F (v * w) = F v * ((v : J) • F w) := by
    let t : U := ⟨(a w : J)⁻¹ * b v * a w * b w,
      U.toSubgroup.mul_mem
        (by
          simpa using (inferInstance : U.toSubgroup.Normal).conj_mem
            (b v) (b v).property (a w : J)⁻¹) (b w).property⟩
    have he : v * w = m (a v * a w, t) := by
      apply Subtype.ext
      change (v : J) * w = ((a v : J) * a w) *
        ((a w : J)⁻¹ * b v * a w * b w)
      rw [← hab v, ← hab w]
      group
    rw [he, hval, f.map_mul]
    change f.toFun (a v) * ((a v : J) • f.toFun (a w)) =
      f.toFun (a v) * ((v : J) • f.toFun (a w))
    rw [← hab v, mul_smul, hfix (b v) (b v).property]
  letI := profinite_closed_subgroup H hH
  letI := profinite_closed_subgroup U.toSubgroup U.isClosed
  have hm : Continuous m :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have hms : Function.Surjective m := by
    intro v
    exact ⟨(a v, b v), Subtype.ext (hab v)⟩
  have hc : Continuous F := hm.isClosedMap.isQuotientMap hm hms |>.continuous_iff.mpr (by
    exact (f.continuous_toFun.comp continuous_fst).congr (fun t => (hval t.1 t.2).symm))
  refine ⟨V, hHV, Subgroup.isOpen_mono hUV U.isOpen,
    ⟨{ toFun := F, continuous_toFun := hc, map_mul := hmul }, ?_⟩⟩
  apply Cocycle.ext
  intro x
  change F ⟨(x : J), hHV x.property⟩ = f.toFun x
  simpa only [m, Subgroup.coe_one, mul_one] using hval x 1

end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  (H : @Subgroup.{u_1} J inst)
  (hH :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (V : @Subgroup.{u_1} J inst) =>
    @Exists.{0}
      (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
        H V)
      fun
        (hHV :
          @LE.le.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            H V) =>
      And
        (@IsOpen.{u_1} J inst_2
          (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) V))
        (@Exists.{max (u_1 + 1) (u_2 + 1)}
          (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 V)
          fun (F : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 V) =>
          @Eq.{max (u_1 + 1) (u_2 + 1)}
            (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H)
            (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H V
              hHV F)
            f) :=
  @LocalConjugacy.Proof.LocalConjugacy.extend_cocycle_to_open_subgroup_preparedProof
