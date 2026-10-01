-- Prove2me | solution 1 for LocalConjugacy.Proof.LocalConjugacy.cyclic_step_comap
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-30T16:52:47.242218+00:00
-- url     : https://prove2.me/submissions/bf48b76e-a184-4a35-bc43-1160587f8a3d

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

private theorem cyclic_step_comap_preparedProof {G H : Type*} [Group G] [Group H]
    (f : H →* G) (A B : Subgroup G) [A.Normal] (g : G)
    (hB : B = A ⊔ Subgroup.zpowers g) :
    ∃ h : H, B.comap f = A.comap f ⊔ Subgroup.zpowers h := by
  let π := QuotientGroup.mk' A
  let φ := π.comp f
  let T := B.comap f
  have hA : A ≤ B := hB ▸ le_sup_left
  have hBmap : B.map π = Subgroup.zpowers (π g) := by
    rw [hB, Subgroup.map_sup, MonoidHom.map_zpowers]
    have he : A.map π = ⊥ := by
      exact (Subgroup.map_eq_bot_iff A).mpr (le_of_eq (QuotientGroup.ker_mk' A).symm)
    rw [he, bot_sup_eq]
  have hle : T.map φ ≤ B.map π := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map_of_mem π hx
  letI : IsCyclic (B.map π) := hBmap ▸ inferInstance
  letI : IsCyclic (T.map φ) := Subgroup.isCyclic_of_le hle
  obtain ⟨y, hy⟩ := (T.map φ).isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hymem : y ∈ T.map φ := hy ▸ Subgroup.mem_zpowers y
  obtain ⟨h, hh, rfl⟩ := hymem
  refine ⟨h, ?_⟩
  have hker : φ.ker = A.comap f := by
    change (π.comp f).ker = _
    rw [← MonoidHom.comap_ker, show π.ker = A from QuotientGroup.ker_mk' A]
  have hmap : (A.comap f ⊔ Subgroup.zpowers h).map φ = T.map φ := by
    rw [Subgroup.map_sup, ← hker, Subgroup.map_ker_self, bot_sup_eq,
      MonoidHom.map_zpowers, hy]
  have hleft : (T.map φ).comap φ = T :=
    Subgroup.comap_map_eq_self (hker ▸ Subgroup.comap_mono hA)
  have hright : ((A.comap f ⊔ Subgroup.zpowers h).map φ).comap φ =
      A.comap f ⊔ Subgroup.zpowers h := Subgroup.comap_map_eq_self (hker ▸ le_sup_left)
  exact hleft.symm.trans ((congrArg (Subgroup.comap φ) hmap).symm.trans hright)







universe u







end LocalConjugacy

end LocalConjugacy.Proof

end

universe u_1 u_2

theorem solution :
∀ {G : Type u_1} {H : Type u_2} [inst : Group.{u_1} G] [inst_1 : Group.{u_2} H]
  (f :
    @MonoidHom.{u_2, u_1} H G
      (@MulOneClass.toMulOne.{u_2} H
        (@Monoid.toMulOneClass.{u_2} H (@DivInvMonoid.toMonoid.{u_2} H (@Group.toDivInvMonoid.{u_2} H inst_1))))
      (@MulOneClass.toMulOne.{u_1} G
        (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))))
  (A B : @Subgroup.{u_1} G inst) [@Subgroup.Normal.{u_1} G inst A] (g : G)
  (hB :
    @Eq.{u_1 + 1} (@Subgroup.{u_1} G inst) B
      (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
        (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
          (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
            (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
              (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                (@Subgroup.instCompleteLattice.{u_1} G inst)))))
        A (@Subgroup.zpowers.{u_1} G inst g))),
  @Exists.{u_2 + 1} H fun (h : H) =>
    @Eq.{u_2 + 1} (@Subgroup.{u_2} H inst_1) (@Subgroup.comap.{u_2, u_1} H inst_1 G inst f B)
      (@Max.max.{u_2} (@Subgroup.{u_2} H inst_1)
        (@SemilatticeSup.toMax.{u_2} (@Subgroup.{u_2} H inst_1)
          (@Lattice.toSemilatticeSup.{u_2} (@Subgroup.{u_2} H inst_1)
            (@ConditionallyCompleteLattice.toLattice.{u_2} (@Subgroup.{u_2} H inst_1)
              (@CompleteLattice.toConditionallyCompleteLattice.{u_2} (@Subgroup.{u_2} H inst_1)
                (@Subgroup.instCompleteLattice.{u_2} H inst_1)))))
        (@Subgroup.comap.{u_2, u_1} H inst_1 G inst f A) (@Subgroup.zpowers.{u_2} H inst_1 h)) :=
  @LocalConjugacy.Proof.LocalConjugacy.cyclic_step_comap_preparedProof
