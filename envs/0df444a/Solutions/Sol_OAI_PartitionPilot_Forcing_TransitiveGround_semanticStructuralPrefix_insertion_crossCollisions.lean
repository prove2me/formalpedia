-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_insertion_crossCollisions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:33:14.004978+00:00
-- url     : https://prove2.me/submissions/1a149e5c-cbb1-4417-a9a0-ec5e1139ad18

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P010
import Definitions.Def_OAIQ253P011
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_aligned_cut_tests_at_larger_cut
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_assignmentClassRequest_mem
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralTrace_storedPreparation_request_bounds
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_structuralAssignment_prepared_insertion_collision

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_StageOneDataBoundLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u

theorem mem_stageOneDataBounds (A I T S L mu X r anchors tuples z : ZFSet.{u}) :
    z ∈ stageOneDataBounds A I T S L mu X r anchors tuples ↔
      ∃ v ∈ A, ∃ D ∈ L, ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T, ∃ E ∈ L,
        ∃ fu ∈ S, ∃ fw ∈ S, z = ZFSet.pair v D ∧ v = stageOneAssignment i u w ∧
          ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
          ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
          RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D := by
  rw [stageOneDataBounds, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨v,hv,D,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨hv,hD⟩,
      v,hv,D,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩

theorem pair_mem_stageOneDataBounds (A I T S L mu X r anchors tuples v D : ZFSet.{u}) :
    ZFSet.pair v D ∈ stageOneDataBounds A I T S L mu X r anchors tuples ↔
      v ∈ A ∧ D ∈ L ∧ ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T, ∃ E ∈ L, ∃ fu ∈ S, ∃ fw ∈ S,
        v = stageOneAssignment i u w ∧ ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
        ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
        RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D := by
  rw [mem_stageOneDataBounds]
  constructor
  · rintro ⟨v',hv,D',hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective equal
    exact ⟨hv,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rest⟩
  · rintro ⟨hv,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rest⟩
    exact ⟨v,hv,D,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rfl,rest⟩

end

open SetRealization
universe u

theorem stageOneDataBounds_assignment_entry (A I T S L mu X r anchors tuples i u w D : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) D ∈ stageOneDataBounds A I T S L mu X r anchors tuples ↔
      stageOneAssignment i u w ∈ A ∧ D ∈ L ∧ i ∈ I ∧ u ∈ T ∧ w ∈ T ∧
      ∃ E ∈ L, ∃ fu ∈ S, ∃ fw ∈ S,
        ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
        ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
        RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D := by
  rw [pair_mem_stageOneDataBounds]
  constructor
  · rintro ⟨member,hD,i',hi,u',hu,w',hw,E,hE,fu,hfu,fw,hfw,equal,rest⟩
    obtain ⟨rfl,rfl,rfl⟩ := (stageOneAssignment_eq_iff i u w i' u' w').1 equal
    exact ⟨member,hD,hi,hu,hw,E,hE,fu,hfu,fw,hfw,rest⟩
  · rintro ⟨member,hD,hi,hu,hw,E,hE,fu,hfu,fw,hfw,rest⟩
    exact ⟨member,hD,i,hi,u,hu,w,hw,E,hE,fu,hfu,fw,hfw,rfl,rest⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionClosure
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundCountable_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets) (nonempty : R.Nonempty)
    (small : M.groundEmbeddable R ZFSet.omega) :
    ∃ g ∈ M.sets, ZFSet.IsFunc ZFSet.omega R g ∧
      ∀ p ∈ R, ∃ n ∈ ZFSet.omega, ZFSet.pair n p ∈ g :=
  M.groundEmbeddable_enumeration pairing unions powers separation hR
    (M.omega_mem separation infinite) nonempty small

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})






theorem groundCountable_family_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets)
    (countR : M.groundEmbeddable R ZFSet.omega)
    (small : ∀ p ∈ R, M.groundEmbeddable p ZFSet.omega) :
    M.groundEmbeddable (⋃₀ R) ZFSet.omega := by
  classical
  by_cases nonempty : R.Nonempty
  · obtain ⟨g, hg, enumeration, onto⟩ :=
      M.groundCountable_enumeration pairing unions powers separation infinite hR nonempty countR
    exact M.countable_enumerated_union pairing unions powers separation infinite choice
      hR (M.union_mem unions hR) hg enumeration onto
      (fun p hp _ hz => ZFSet.mem_sUnion.2 ⟨p, hp, hz⟩) small
  · have empty : R = ∅ := by
      apply ZFSet.ext
      intro p
      exact ⟨fun hp => False.elim (nonempty ⟨p, hp⟩), fun hp => False.elim (ZFSet.notMem_empty p hp)⟩
    rw [empty, ZFSet.sUnion_empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨R, hR⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FixedTopCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace MeetOrderCode

theorem eq_canonicalMeetGraph {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ) :
    μ = canonicalMeetGraph L r := by
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨a, ha, z, _, rfl⟩ := ZFSet.mem_prod.1 (code.operation.1 hv)
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 ha
    exact (pair_mem_canonicalMeetGraph L r x y z).2 (code.pair_iff.1 hv)
  · intro hv
    obtain ⟨x, hx, y, hy, z, hz, rfl, h⟩ := (mem_canonicalMeetGraph L r v).1 hv
    exact code.pair_iff.2 ⟨hx, hy, hz, h⟩

end MeetOrderCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem mem_assignmentOnIndices (B T A z : ZFSet.{u}) :
    z ∈ assignmentOnIndices B T A ↔ z ∈ A ∧ z ∈ stageOneAssignments B T :=
  ZFSet.mem_sep

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem supportedEqualityCertificateBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.supportedEqualityCertificateBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation (M.groundPower_mem powers hNodes)
    (M.prod_mem pairing unions powers separation
      (M.groundSmallSubsets_mem powers separation hNodes omega)
      (M.groundRelations_mem pairing unions powers separation hNodes hN))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem synchronizedEnumerationBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) : M.synchronizedEnumerationBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation
    (M.groundRelations_mem pairing unions powers separation omega hNodes)
    (M.groundRelations_mem pairing unions powers separation omega hN)

end TransitiveGround

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem certificateProfileGraph_function {J nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k) :
    ZFSet.IsFunc J (M.groundPower nodes) (M.certificateProfileGraph J nodes W k) :=
  relationCompose_function_of_subset function
    (productFirst_function (M.groundPower nodes)
      (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes W)))
    (fun _ member => member)

theorem pair_mem_certificateProfileGraph {J nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (z F : ZFSet.{u}) :
    ZFSet.pair z F ∈ M.certificateProfileGraph J nodes W k ↔
      ∃ B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k := by
  rw [certificateProfileGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, value, _, edge, projection⟩
    obtain ⟨profile, hp, tail, ht, equal⟩ := (mem_productFirst _ _ _).1 projection
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨B, hB, f, hf, rfl⟩ := ZFSet.mem_prod.1 ht
    exact ⟨B, f, edge⟩
  · rintro ⟨B, f, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have fields := ZFSet.pair_mem_prod.1 bounds.2
    exact ⟨bounds.1, fields.1, _, bounds.2, edge,
      (mem_productFirst _ _ _).2 ⟨F, fields.1, _, fields.2, rfl⟩⟩

theorem mem_certificateProfileImage {J nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (F : ZFSet.{u}) :
    F ∈ M.certificateProfileImage J nodes W k ↔
      ∃ z B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k := by
  rw [certificateProfileImage, mem_relationImage]
  constructor
  · rintro ⟨_, z, _, edge⟩
    obtain ⟨B, f, selected⟩ := (M.pair_mem_certificateProfileGraph function z F).1 edge
    exact ⟨z, B, f, selected⟩
  · rintro ⟨z, B, f, edge⟩
    have projected := (M.pair_mem_certificateProfileGraph function z F).2 ⟨B, f, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 ((M.certificateProfileGraph_function function).1 projected)
    exact ⟨bounds.2, z, bounds.1, projected⟩

theorem certificateProfileGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J nodes W k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hW : W ∈ M.sets) (hk : k ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.certificateProfileGraph J nodes W k ∈ M.sets := by
  have hProfiles := M.groundPower_mem powers hNodes
  have hTail := M.prod_mem pairing unions powers separation
    (M.groundSmallSubsets_mem powers separation hNodes omega)
    (M.groundRelations_mem pairing unions powers separation hNodes hW)
  exact M.relationCompose_mem pairing unions powers separation hJ
    (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega)
    hProfiles hk (M.productFirst_mem pairing unions powers separation hProfiles hTail)

theorem certificateProfileImage_mem_small
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J nodes W k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hW : W ∈ M.sets) (hk : k ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (smallJ : M.groundEmbeddable J ZFSet.omega) :
    M.certificateProfileImage J nodes W k ∈ M.sets ∧
      M.groundEmbeddable (M.certificateProfileImage J nodes W k) ZFSet.omega := by
  have graph := M.certificateProfileGraph_mem pairing unions powers separation hJ hNodes hW hk omega
  have profiles := M.groundPower_mem powers hNodes
  exact ⟨M.relationImage_mem separation hJ profiles graph,
    M.groundEmbeddable_function_image pairing unions powers separation choice hJ profiles omega
      graph (M.certificateProfileGraph_function function) smallJ⟩

theorem certificateProfileImage_meetFilter
    {P order q nodes nodeOrder meet N visibility top omega J W k enumerations : ZFSet.{u}}
    (family : PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top omega J
      (M.supportedEqualityCertificateBound nodes W) (M.synchronizedEnumerationBound nodes W)
      k enumerations) {F : ZFSet.{u}}
    (member : F ∈ M.certificateProfileImage J nodes W k) :
    MeetFilterCode nodes nodeOrder meet F := by
  obtain ⟨z, B, f, edge⟩ := (M.mem_certificateProfileImage family.1 F).1 member
  have hz := (ZFSet.pair_mem_prod.1 (family.1.1 edge)).1
  obtain ⟨value, enumerated, _unique⟩ := family.2.1.2 z hz
  have bounds := (ZFSet.pair_mem_prod.1 (family.2.1.1 enumerated)).2
  obtain ⟨e, _he, names, _hn, rfl⟩ := ZFSet.mem_prod.1 bounds
  exact (family.2.2 z F B f e names edge enumerated).1

theorem certificateProfileImage_eq_of_domain_subset {J D nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (subset : J ⊆ D) :
    M.certificateProfileImage D nodes W k = M.certificateProfileImage J nodes W k := by
  apply ZFSet.ext
  intro F
  simp only [certificateProfileImage, certificateProfileGraph, mem_relationImage,
    pair_mem_relationCompose]
  constructor
  · rintro ⟨hF, z, _hzD, _, _, c, hc, edge, projected⟩
    have hz := (ZFSet.pair_mem_prod.1 (function.1 edge)).1
    exact ⟨hF, z, hz, hz, hF, c, hc, edge, projected⟩
  · rintro ⟨hF, z, hz, _, _, c, hc, edge, projected⟩
    exact ⟨hF, z, subset hz, subset hz, hF, c, hc, edge, projected⟩

theorem mem_certificateProfileImageFamily (nodes W z : ZFSet.{u}) :
    z ∈ M.certificateProfileImageFamily nodes W ↔
      ∃ k ∈ M.groundRelations W (M.supportedEqualityCertificateBound nodes W),
        z = ZFSet.pair k (M.certificateProfileImage W nodes W k) := by
  rw [certificateProfileImageFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨k, equal⟩
    exact ⟨k.val, k.property, equal.symm⟩
  · rintro ⟨k, hk, equal⟩
    exact ⟨⟨k, hk⟩, equal.symm⟩

theorem pair_mem_certificateProfileImageFamily (nodes W k image : ZFSet.{u}) :
    ZFSet.pair k image ∈ M.certificateProfileImageFamily nodes W ↔
      k ∈ M.groundRelations W (M.supportedEqualityCertificateBound nodes W) ∧
        image = M.certificateProfileImage W nodes W k := by
  rw [M.mem_certificateProfileImageFamily]
  constructor
  · rintro ⟨r, hr, equal⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hr, value⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem certificateProfileImageFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {nodes W : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hW : W ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.certificateProfileImageFamily nodes W ∈ M.sets := by
  let C := M.supportedEqualityCertificateBound nodes W
  let PF := M.groundPower nodes
  let projection := productFirst PF
    (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes W))
  have hC := M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega
  have hPF := M.groundPower_mem powers hNodes
  have hProjection := M.productFirst_mem pairing unions powers separation hPF
    (M.prod_mem pairing unions powers separation
      (M.groundSmallSubsets_mem powers separation hNodes omega)
      (M.groundRelations_mem pairing unions powers separation hNodes hW))
  let defined := profileImageDefinition M pairing unions powers separation
  change defined.graph (extend W (extend C (extend PF (extend projection Fin.elim0))))
    (M.groundRelations W C) ∈ M.sets
  exact defined.graph_mem pairing separation collection _
    (Fin.cases hW (Fin.cases hC (Fin.cases hPF (Fin.cases hProjection (fun j => Fin.elim0 j)))))
    (M.groundRelations_mem pairing unions powers separation hW hC)

theorem certificateProfileImageFamily_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes W : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hW : W ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    ZFSet.IsFunc (M.groundRelations W (M.supportedEqualityCertificateBound nodes W))
      (M.groundPower (M.groundPower nodes)) (M.certificateProfileImageFamily nodes W) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := (M.mem_certificateProfileImageFamily nodes W z).1 hz
    have groundK := ((M.mem_groundRelations _ _ k).1 hk).1
    have groundGraph := M.certificateProfileGraph_mem pairing unions powers separation
      hW hNodes hW groundK omega
    have groundImage := M.relationImage_mem separation hW (M.groundPower_mem powers hNodes)
      groundGraph
    exact ZFSet.pair_mem_prod.2 ⟨hk, (M.mem_groundPower _ _).2
      ⟨groundImage, fun F member => (mem_relationImage _ _ _ F).1 member |>.1⟩⟩
  · intro k hk
    exact ⟨M.certificateProfileImage W nodes W k,
      (M.pair_mem_certificateProfileImageFamily nodes W k _).2 ⟨hk, rfl⟩,
      fun image edge => ((M.pair_mem_certificateProfileImageFamily nodes W k image).1 edge).2⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNicePreparationWitnessBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_preparationWitnessBound (nodes T Q r k enumerations : ZFSet.{u}) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q ↔
      r ∈ Q ∧ k ∈ M.groundRelations (M.groundRelations T Q)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q)) ∧
      enumerations ∈ M.groundRelations (M.groundRelations T Q)
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) := by
  simp only [preparationWitnessBound, ZFSet.pair_mem_prod]

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundVaryingPreparationRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_storedPreparationRelation
    (Q upperOrder nodes T levels alpha meet : ZFSet.{u}) (fields : Fin 15 → ZFSet.{u})
    (p y : ZFSet.{u}) :
    ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T levels alpha meet fields ↔
    p ∈ Q ∧ y ∈ M.preparationWitnessBound nodes T Q ∧
      M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
        meet ZFSet.omega (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) fields p y := by
  rw [storedPreparationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hp, hy⟩, p', y', eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hp, hy, code⟩
  · rintro ⟨hp, hy, code⟩
    exact ⟨⟨hp, hy⟩, p, y, rfl, code⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationCode_pair_iff (packed Q upperOrder nodes T levels omega C E alpha p y : ZFSet.{u}) :
    M.VaryingPreparationCode packed Q upperOrder nodes T levels omega C E
      (ZFSet.pair (ZFSet.pair alpha p) y) ↔
    ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
        (canonicalMeetGraph (fields 10) (fields 11)) omega C E fields p y := by
  constructor
  · rintro ⟨alpha', p', y', fields, equal, rest⟩
    obtain ⟨input, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 input
    exact ⟨fields, rest⟩
  · rintro ⟨fields, rest⟩
    exact ⟨alpha, p, y, fields, rfl, rest⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_varyingPreparationRelation
    (stages packed Q upperOrder nodes T alpha p y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T ↔
    alpha ∈ stages ∧ p ∈ Q ∧ y ∈ M.preparationWitnessBound nodes T Q ∧
      ∃ fields : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
        fields 6 = T ∧ fields 10 = nodes ∧
        MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
        M.StoredPreparationCode upperOrder
          (rowAssignmentCutGraph Q (fields 7) (refinementDataHistoryLevels stages packed T) alpha)
          (canonicalMeetGraph (fields 10) (fields 11)) ZFSet.omega
          (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
          (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) fields p y := by
  simp only [varyingPreparationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod,
    M.varyingPreparationCode_pair_iff, and_assoc]

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveRowNameActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)
variable {T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M c.carrier T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "pres" => SetMembers.presentation Q
local notation "liftName" => M.refinementHistoryRowNameLift c run ordinal carrier
variable {G : Type v} [Group G] [PartialOrder R]
variable [PartialOrder (SetMembers (M.refinementHistoryForcing c.carrier T stages history))]
variable (a : PosetAction G R)
variable (e : PosetAction G (SetMembers (M.refinementHistoryForcing c.carrier T stages history)))
variable (image : G → ZFSet.{u} → ZFSet.{u})
variable (coordinates : ∀ (g : G)
  (q : SetMembers (M.refinementHistoryForcing c.carrier T stages history)) (row : R) (A : ZFSet.{u}),
  SetMembers.raw q = ZFSet.pair (c.encode row) A →
  SetMembers.raw (e.iso g q) = ZFSet.pair (c.encode (a.iso g row)) (image g A))
variable (emptyImage : ∀ g, image g ∅ = ∅)
include run ordinal carrier coordinates emptyImage

theorem refinementHistoryRowNameLift_stabilizer (tau : Name c.pairEmpty) :
    e.stabilizer (pres) (liftName tau) = a.stabilizer c.pairEmpty tau := by
  apply Subgroup.ext
  intro g
  change e.act (pres) g (liftName tau) = liftName tau ↔ a.act c.pairEmpty g tau = tau
  rw [M.refinementHistoryRowNameLift_act c run ordinal carrier a e image coordinates emptyImage]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [M.refinementHistoryRowNameLift_val c run ordinal carrier] using codes
  · intro equal
    exact congrArg liftName equal

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStageTwoNamePositionSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace PosetAction
open SetRealization
universe u
variable {G P Q L : Type u} [Group G] [PartialOrder P] [PartialOrder Q] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (e : PosetAction G Q) (t : Presentation Q)
variable (liftName : Name s → Name t)
variable (codes : ∀ τ, (liftName τ).val = τ.val)
variable (stabilizers : ∀ τ, e.stabilizer t (liftName τ) = a.stabilizer s τ)
include codes stabilizers

theorem positionSupport_of_codeLift (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (b : Presentation L) (d : PosetAction G L) (S mu X tuples : ZFSet.{u}) (D : L)
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ f ∈ S, ∀ τ : Name s, ZFSet.pair f τ.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s τ) :
    ∀ f ∈ S, ∀ τ : Name t, ZFSet.pair f τ.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ e.stabilizer t τ := by
  intro f hf τ entry bound
  let lower : Name s := ⟨τ.val, valid τ.val (range f τ.val entry)⟩
  have same : liftName lower = τ := Subtype.ext (codes lower)
  rw [← same, stabilizers]
  exact support f hf lower entry bound

end PosetAction

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralDataSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace

theorem semanticStructuralAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    (act).actionGraph (SetMembers.presentation Q) t = rawGraph := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  unfold semanticStructuralAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem semanticStructuralAction_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    ∀ (g : G) (p : SetMembers Q) (r : R) (A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((act).iso g p) = ZFSet.pair (c.encode (a.iso g r))
        (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  intro g p r A code
  have edge := ((act).triple_mem_actionGraph (SetMembers.presentation Q) t g p ((act).iso g p)).2 rfl
  rw [M.semanticStructuralAction_graph] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw ((act).iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c
    (M.structuralForcingCarrier_shape c.carrier t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history)
    (SetMembers.raw_mem ((act).iso g p))
  rw [code, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q _ _ g r q A D).1 edge
  rw [target, row, data]
  rfl

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAssignmentLabelDomainTotality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_stageSystem :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    RefinementStageSystem M act lower t b d base directed alpha T T2 := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have hGraph : (act).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    have ground := M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh omega
    unfold structuralForcingCarrier at ground
    rw [M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset] at ground
    exact ground
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1
    closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  exact M.recursiveRefinementStageSystem c a t b d base directed T T2 alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal pairing unions powers separation collection
    carrier rowOrderGround group nodes nodeOrder nodeMaps supports hT hT2 hAlpha hLowerPacked
    omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 rowTop topMem topRows
    act image coordinates emptyImage hGraph

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundStoredVisitCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationRelation_of_stored
    (stages packed Q upperOrder nodes T alpha p y meet : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet)
    (entry : ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T := by
  obtain ⟨hp, hy, code⟩ := (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
    (refinementDataHistoryLevels stages packed T) alpha meet fields p y).1 entry
  have equal := meetCode.eq_canonicalMeetGraph
  exact (M.pair_mem_varyingPreparationRelation stages packed Q upperOrder nodes T alpha p y).2
    ⟨hAlpha, hp, hy, fields, stored, terms, nodeCarrier, equal ▸ meetCode, equal ▸ code⟩

theorem varyingPreparationRelation_fiber_iff
    (stages packed Q upperOrder nodes T alpha p y meet dataBound : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u})
    (function : ZFSet.IsFunc stages dataBound packed) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
        M.varyingPreparationRelation stages packed Q upperOrder nodes T ↔
      ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T
        (refinementDataHistoryLevels stages packed T) alpha meet fields := by
  constructor
  · intro entry
    obtain ⟨_, hp, hy, other, otherStored, _terms, _nodes, _meet, code⟩ :=
      (M.pair_mem_varyingPreparationRelation stages packed Q upperOrder nodes T alpha p y).1 entry
    obtain ⟨_, _, unique⟩ := function.2 alpha hAlpha
    have same : other = fields := refinementFormulaDataCode_injective
      ((unique _ otherStored).trans (unique _ stored).symm)
    subst other
    exact (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields p y).2
      ⟨hp, hy, meetCode.eq_canonicalMeetGraph.symm ▸ code⟩
  · exact M.varyingPreparationRelation_of_stored stages packed Q upperOrder nodes T alpha p y meet
      fields hAlpha stored terms nodeCarrier meetCode





theorem varyingPreparation_visit_certificates
    (stages packed Q upperOrder nodes T alpha row A r payload meet dataBound : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u})
    (function : ZFSet.IsFunc stages dataBound packed) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet)
    (entry : ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row A)) (ZFSet.pair r payload) ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T) :
    ∃ k enumerations q, payload = ZFSet.pair k enumerations ∧
      k ∈ M.sets ∧ enumerations ∈ M.sets ∧ r ∈ Q ∧ q ∈ fields 7 ∧
      ZFSet.pair r (ZFSet.pair row A) ∈ upperOrder ∧
      ZFSet.pair r q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages packed T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        meet (fields 14) (fields 13) (fields 9) ZFSet.omega
        (M.storedPreparationRequests A fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations := by
  have fixed := (M.varyingPreparationRelation_fiber_iff stages packed Q upperOrder nodes T
    alpha (ZFSet.pair row A) (ZFSet.pair r payload) meet dataBound fields function hAlpha
    stored terms nodeCarrier meetCode).1 entry
  obtain ⟨_, bounded, oldRow, oldA, output, k, enumerations, q, input, value, below, cut, family⟩ :=
    (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields
      (ZFSet.pair row A) (ZFSet.pair r payload)).1 fixed
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 input
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 value
  obtain ⟨hr, hk, he⟩ := (M.mem_preparationWitnessBound nodes T Q r k enumerations).1 bounded
  have hq := (ZFSet.pair_mem_prod.1
    ((mem_rowAssignmentCutGraph _ _ _ _ _).1 cut).1).2
  exact ⟨k, enumerations, q, rfl,
    ((M.mem_groundRelations _ _ k).1 hk).1,
    ((M.mem_groundRelations _ _ enumerations).1 he).1, hr, hq, below, cut, family⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRetainedPreparationSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_retainedPreparationSelections (A L R p levels x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.retainedPreparationSelections A L R p levels ↔
      x ∈ A ∧ y ∈ L ∧ ∃ alpha row sourceA tail,
        y = ZFSet.pair alpha (ZFSet.pair (ZFSet.pair row sourceA) tail) ∧
        ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row sourceA)) (ZFSet.pair p tail) ∈ R ∧
        sourceA ⊆ A ∧ x ∈ sourceA ∧ ZFSet.pair x alpha ∈ levels := by
  rw [retainedPreparationSelections, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, x', alpha, row, sourceA, tail, equal, rest⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hy, alpha, row, sourceA, tail, value, rest⟩
  · rintro ⟨hx, hy, alpha, row, sourceA, tail, equal, rest⟩
    exact ⟨⟨hx, hy⟩, x, alpha, row, sourceA, tail, congrArg (ZFSet.pair x) equal, rest⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparedWitnessSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem preparedWitnessSelection_entry
    {rows T stages packed nodes p A x alpha sourceRow sourceA k enumerations : ZFSet.{u}}
    (data : RefinementDataHistory stages packed T)
    (entry : ZFSet.pair x (ZFSet.pair alpha
      (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈
      M.preparedWitnessSelections rows T stages packed nodes p A) :
    let Q := M.refinementHistoryForcing rows T stages packed
    alpha ∈ stages ∧ ZFSet.pair sourceRow sourceA ∈ Q ∧ sourceA ⊆ A ∧
      k ∈ M.sets ∧ enumerations ∈ M.sets ∧
    ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      x ∈ assignmentOnIndices (fields 0) T sourceA ∧
    ∃ q ∈ fields 7,
      ZFSet.pair p q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages packed T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
        ZFSet.omega (M.storedPreparationRequests sourceA fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations := by
  let Q := M.refinementHistoryForcing rows T stages packed
  obtain ⟨_, _, alpha', row', sourceA', tail, equal, visit, sourceSubset, inSource, level⟩ :=
    (M.pair_mem_retainedPreparationSelections _ _ _ _ _ _ _).1 entry
  obtain ⟨rfl, outputEq⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨sourceEq, rfl⟩ := ZFSet.pair_inj.1 outputEq
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 sourceEq
  obtain ⟨ha, sourceCondition, bounded, fields, stored, terms, nodeCarrier, meet, _raw⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed Q (ZFSet.prod Q Q) nodes T
      alpha (ZFSet.pair sourceRow sourceA) (ZFSet.pair p (ZFSet.pair k enumerations))).1 visit
  obtain ⟨k', enums', q, value, hk, he, _hp, hq, _below, cut, family⟩ :=
    M.varyingPreparation_visit_certificates stages packed Q (ZFSet.prod Q Q) nodes T alpha
      sourceRow sourceA p (ZFSet.pair k enumerations) _ _ fields data.function.to_isFunc ha
      stored terms nodeCarrier meet visit
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 value
  refine ⟨ha, sourceCondition, sourceSubset, hk, he, fields, stored, terms, nodeCarrier,
    meet, ?_, q, hq, cut, family⟩
  apply (mem_assignmentOnIndices (fields 0) T sourceA x).2
  refine ⟨inSource, ?_⟩
  obtain ⟨I, indexEntry, shape⟩ := (pair_mem_refinementHistoryAssignmentLevels
    data.index_function data.index_literal T x alpha).1 level
  have actual := (refinementDataHistoryField_entry data.function fields stored 0 (fields 0)).2 rfl
  have same : I = fields 0 := data.index_function.unique indexEntry actual
  exact same ▸ shape

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedCopyCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_preparationEnvironment (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed) :
    StoredPreparationEnvironment M fields := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have exactStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same : fields = M.refinementLevelFormulaData act lower b d alpha T T2 valid :=
    refinementFormulaDataCode_injective ((run).carriers.data.function.unique stored exactStored)
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have members : ∀ j, fields j ∈ M.sets := M.refinementFormulaDataCode_fields_mem fields
    (M.transitive (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion stored))
  refine ⟨?_, members, ?_, ?_⟩
  · rw [same]
    exact lower.conditionOrder_code
  · rw [same]
    intro z hz
    exact Name.isName_of_subset valid ((M.mem_groundRelations T lower.carrier z).1 hz).2
  · rw [same]
    intro v V entry _
    obtain ⟨i, equal⟩ := (M.mem_niceVisibilityGraph act lower b T d.principalFix
      (ZFSet.pair v V)).1 entry
    have value := (ZFSet.pair_inj.1 equal).2
    rw [value]
    exact (M.niceVisibilityName act lower T (d.principalFix i)).property

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_PreparedWitnessCertificateGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem preparedWitnessCertificateGraph_function (stages Q K E : ZFSet.{u}) :
    ZFSet.IsFunc (ZFSet.prod stages (ZFSet.prod Q (ZFSet.prod K E))) K
      (preparedWitnessCertificateGraph stages Q K E) :=
  relationCompose_function_of_subset
    (relationCompose_function_of_subset (productSecond_function _ _) (productSecond_function _ _)
      (fun _ h => h)) (productFirst_function _ _) (fun _ h => h)

theorem pair_mem_preparedWitnessCertificateGraph (stages Q K E y k : ZFSet.{u}) :
    ZFSet.pair y k ∈ preparedWitnessCertificateGraph stages Q K E ↔
      k ∈ K ∧ ∃ alpha ∈ stages, ∃ source ∈ Q, ∃ enumerations ∈ E,
        y = ZFSet.pair alpha (ZFSet.pair source (ZFSet.pair k enumerations)) := by
  rw [preparedWitnessCertificateGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, hk, tail, _, first, projected⟩
    obtain ⟨k', _, enums, he, equal⟩ := (mem_productFirst _ _ _).1 projected
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨_, _, output, _, first, second⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨source, hsource, tail', _, equal⟩ := (mem_productSecond _ _ _).1 second
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨alpha, ha, output', _, equal⟩ := (mem_productSecond _ _ _).1 first
    obtain ⟨value, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hk, alpha, ha, source, hsource, enums, he, value⟩
  · rintro ⟨hk, alpha, ha, source, hs, enums, he, rfl⟩
    have ht := ZFSet.pair_mem_prod.2 ⟨hk, he⟩
    have ho := ZFSet.pair_mem_prod.2 ⟨hs, ht⟩
    have hy := ZFSet.pair_mem_prod.2 ⟨ha, ho⟩
    exact ⟨hy, hk, _, ht,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hy, ht, _, ho,
        (mem_productSecond _ _ _).2 ⟨alpha, ha, _, ho, rfl⟩,
        (mem_productSecond _ _ _).2 ⟨source, hs, _, ht, rfl⟩⟩,
      (mem_productFirst _ _ _).2 ⟨k, hk, enums, he, rfl⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem preparedWitnessCertificateGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages Q K E : ZFSet.{u}} (hStages : stages ∈ M.sets) (hQ : Q ∈ M.sets)
    (hK : K ∈ M.sets) (hE : E ∈ M.sets) :
    preparedWitnessCertificateGraph stages Q K E ∈ M.sets := by
  have ht := M.prod_mem pairing unions powers separation hK hE
  have ho := M.prod_mem pairing unions powers separation hQ ht
  have hL := M.prod_mem pairing unions powers separation hStages ho
  exact M.relationCompose_mem pairing unions powers separation hL ht hK
    (M.relationCompose_mem pairing unions powers separation hL ho ht
      (M.productSecond_mem pairing unions powers separation hStages ho)
      (M.productSecond_mem pairing unions powers separation hQ ht))
    (M.productFirst_mem pairing unions powers separation hK hE)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedSelectionProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
open scoped ZFSet
universe u
variable (M : TransitiveGround.{u})

theorem preparedSelectionProfiles_ground_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows T stages packed nodes nodeOrder p A selections : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hT : T ∈ M.sets) (hStages : stages ∈ M.sets)
    (hPacked : packed ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (data : RefinementDataHistory stages packed T)
    (selected : selections ⊆ M.preparedWitnessSelections rows T stages packed nodes p A)
    (whole : relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound nodes T (M.refinementHistoryForcing rows T stages packed))) selections ∈ M.sets)
    (small : M.groundEmbeddable (relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound nodes T (M.refinementHistoryForcing rows T stages packed))) selections) ZFSet.omega)
    (localData : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
      fields 10 = nodes ∧ fields 11 = nodeOrder ∧
      fields 14 ⊆ M.groundRelations T (M.refinementHistoryForcing rows T stages packed) ∧
      ∀ sourceRow sourceA,
        ZFSet.pair sourceRow sourceA ∈ M.refinementHistoryForcing rows T stages packed →
        M.storedPreparationRequests sourceA fields ∈ M.sets ∧
        M.groundEmbeddable (M.storedPreparationRequests sourceA fields) ZFSet.omega) :
    let Q := M.refinementHistoryForcing rows T stages packed
    let Profiles := M.preparedSelectionProfiles A stages Q nodes T selections
    Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
      (∀ F ∈ Profiles, MeetFilterCode nodes nodeOrder (canonicalMeetGraph nodes nodeOrder) F) ∧
      ∀ x alpha sourceRow sourceA k enumerations z F B f,
        ZFSet.pair x (ZFSet.pair alpha
          (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈ selections →
        ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k → F ∈ Profiles := by
  let Q := M.refinementHistoryForcing rows T stages packed
  let W := M.groundRelations T Q
  let K := M.groundRelations W (M.supportedEqualityCertificateBound nodes W)
  let E := M.groundRelations W (M.synchronizedEnumerationBound nodes W)
  let L := ZFSet.prod stages (M.preparationWitnessBound nodes T Q)
  let witnesses := relationImage A L selections
  let projection := preparedWitnessCertificateGraph stages Q K E
  let certificates := relationImage witnesses K projection
  let images := relationImage certificates (M.groundPower (M.groundPower nodes))
    (M.certificateProfileImageFamily nodes W)
  have omega := M.omega_mem separation infinite
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hPacked omega
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  have hK := M.groundRelations_mem pairing unions powers separation hW
    (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega)
  have hE := M.groundRelations_mem pairing unions powers separation hW
    (M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega)
  have hProjection := M.preparedWitnessCertificateGraph_mem pairing unions powers separation hStages hQ hK hE
  have hCertificates := M.relationImage_mem separation whole hK hProjection
  have smallCertificates := M.groundEmbeddable_function_image pairing unions powers separation choice
    whole hK omega hProjection (preparedWitnessCertificateGraph_function stages Q K E) small
  have hFamily := M.certificateProfileImageFamily_mem pairing unions powers separation collection hNodes hW omega
  have hImageBound := M.groundPower_mem powers (M.groundPower_mem powers hNodes)
  have familyFunction := M.certificateProfileImageFamily_function pairing unions powers separation hNodes hW omega
  have hImages := M.relationImage_mem separation hCertificates hImageBound hFamily
  have smallImages := M.groundEmbeddable_function_image pairing unions powers separation choice
    hCertificates hImageBound omega hFamily familyFunction smallCertificates
  have certificateData (k : ZFSet.{u}) (member : k ∈ certificates) :
      ∃ J, J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧ J ⊆ W ∧
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k ∧
        ∀ F ∈ M.certificateProfileImage J nodes W k,
          MeetFilterCode nodes nodeOrder (canonicalMeetGraph nodes nodeOrder) F := by
    obtain ⟨_, y, hy, projected⟩ := (mem_relationImage _ _ _ _).1 member
    obtain ⟨_, x, _hx, edge⟩ := (mem_relationImage _ _ _ _).1 hy
    obtain ⟨_, alpha, _ha, source, hs, enumerations, _he, rfl⟩ :=
      (pair_mem_preparedWitnessCertificateGraph stages Q K E y k).1 projected
    obtain ⟨sourceRow, _, sourceA, _, rfl⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T stages packed hs)
    obtain ⟨_, sourceCondition, _, _, _, fields, stored, _terms, nodeCarrier, _meet,
      _assignment, q, _hq, _cut, family⟩ := M.preparedWitnessSelection_entry data (selected edge)
    obtain ⟨_nodes, orderEq, nameBound, requests⟩ := localData alpha fields stored
    obtain ⟨hJ, smallJ⟩ := requests sourceRow sourceA sourceCondition
    have Jbound : M.storedPreparationRequests sourceA fields ⊆ W := by
      intro z hz
      apply nameBound
      rcases ZFSet.mem_union.1 hz with left | right
      · exact (mem_relationImage _ _ _ _).1 left |>.1
      · exact (mem_relationImage _ _ _ _).1 right |>.1
    refine ⟨_, hJ, smallJ, Jbound, family.1, ?_⟩
    intro F hF
    have aligned := family
    rw [nodeCarrier, orderEq] at aligned
    exact M.certificateProfileImage_meetFilter aligned hF
  have imagesSmall (image : ZFSet.{u}) (member : image ∈ images) :
      M.groundEmbeddable image ZFSet.omega := by
    obtain ⟨_, k, hk, edge⟩ := (mem_relationImage _ _ _ _).1 member
    obtain ⟨_, rfl⟩ := (M.pair_mem_certificateProfileImageFamily nodes W k image).1 edge
    obtain ⟨J, hJ, smallJ, Jbound, function, _filters⟩ := certificateData k hk
    rw [M.certificateProfileImage_eq_of_domain_subset function Jbound]
    exact (M.certificateProfileImage_mem_small pairing unions powers separation choice hJ hNodes hW
      (((M.mem_groundRelations _ _ k).1 ((mem_relationImage _ _ _ _).1 hk).1).1)
      omega function smallJ).2
  change (⋃₀ images) ∈ M.sets ∧ M.groundEmbeddable (⋃₀ images) ZFSet.omega ∧ _
  refine ⟨M.union_mem unions hImages,
    M.groundCountable_family_union pairing unions powers separation infinite choice hImages smallImages imagesSmall,
    ?_, ?_⟩
  · intro F member
    obtain ⟨image, hi, hF⟩ := ZFSet.mem_sUnion.1 member
    obtain ⟨_, k, hk, edge⟩ := (mem_relationImage _ _ _ _).1 hi
    obtain ⟨_, rfl⟩ := (M.pair_mem_certificateProfileImageFamily nodes W k image).1 edge
    obtain ⟨J, _, _, Jbound, function, filters⟩ := certificateData k hk
    apply filters F
    exact M.certificateProfileImage_eq_of_domain_subset function Jbound ▸ hF
  · intro x alpha sourceRow sourceA k enumerations z F B f edge certificate
    have selectedEdge := selected edge
    dsimp only [preparedWitnessSelections, retainedPreparationSelections] at selectedEdge
    have bounded := (ZFSet.mem_sep.1 selectedEdge).1
    have pairBounds := ZFSet.pair_mem_prod.1 bounded
    have yBound := ZFSet.pair_mem_prod.1 pairBounds.2
    have outputBound := ZFSet.pair_mem_prod.1 yBound.2
    have tailBound := ZFSet.pair_mem_prod.1 outputBound.2
    have hk : k ∈ certificates := (mem_relationImage _ _ _ _).2 ⟨tailBound.1,
      _, (mem_relationImage _ _ _ _).2 ⟨pairBounds.2, x, pairBounds.1, edge⟩,
      (pair_mem_preparedWitnessCertificateGraph stages Q K E _ k).2
        ⟨tailBound.1, alpha, yBound.1, _, outputBound.1, enumerations, tailBound.2, rfl⟩⟩
    obtain ⟨J, _, _, Jbound, function, _⟩ := certificateData k hk
    have familyEdge := (M.pair_mem_certificateProfileImageFamily nodes W k _).2 ⟨tailBound.1, rfl⟩
    have imageBound := (ZFSet.pair_mem_prod.1 (familyFunction.1 familyEdge)).2
    refine ZFSet.mem_sUnion.2 ⟨_, (mem_relationImage _ _ _ _).2 ⟨imageBound, k, hk, familyEdge⟩, ?_⟩
    rw [M.certificateProfileImage_eq_of_domain_subset function Jbound]
    exact (M.mem_certificateProfileImage function F).2 ⟨z, B, f, certificate⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedCopyUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
private theorem selectedFamilyCertificate_p1
    (M : TransitiveGround.{u})
    {P order q nodes nodeOrder meet N visibility top omega J W k enumerations z : ZFSet.{u}}
    (family : PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top
      omega J (M.supportedEqualityCertificateBound nodes W)
      (M.synchronizedEnumerationBound nodes W) k enumerations)
    (member : z ∈ J) :
    ∃ F B f e names, F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
      e ∈ M.sets ∧ names ∈ M.sets ∧
      ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
      ZFSet.pair z (ZFSet.pair e names) ∈ enumerations ∧
      PreparedCertificateCode M P order q nodes nodeOrder meet N visibility top omega z F B f e names := by
  obtain ⟨value, edge, _unique⟩ := family.1.2 z member
  have bounded := (ZFSet.pair_mem_prod.1 (family.1.1 edge)).2
  obtain ⟨F, hF, tail, hTail, rfl⟩ := ZFSet.mem_prod.1 bounded
  obtain ⟨B, hB, f, hf, rfl⟩ := ZFSet.mem_prod.1 hTail
  obtain ⟨value, enumerated, _unique⟩ := family.2.1.2 z member
  have bounded := (ZFSet.pair_mem_prod.1 (family.2.1.1 enumerated)).2
  obtain ⟨e, he, names, hn, rfl⟩ := ZFSet.mem_prod.1 bounded
  exact ⟨F, B, f, e, names, ((M.mem_groundPower nodes F).1 hF).1,
    ((M.mem_groundSmallSubsets nodes ZFSet.omega B).1 hB).1,
    ((M.mem_groundRelations nodes W f).1 hf).1,
    ((M.mem_groundRelations ZFSet.omega nodes e).1 he).1,
    ((M.mem_groundRelations ZFSet.omega W names).1 hn).1, edge, enumerated,
    family.2.2 z F B f e names edge enumerated⟩

variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

local notation "upperQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "levels" => refinementDataHistoryLevels stages packed T
local notation "image" => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace

theorem semanticStructuralPrefix_insertion_crossCollisions_oai
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r row : R) (A largerA selections : ZFSet.{u}) (h : G) (D K V : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (selectionFunction : ZFSet.IsFunc A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections)
    (selected : selections ⊆ M.preparedWitnessSelections c.carrier T stages packed b.carrier
      (ZFSet.pair (c.encode r) A) A)
    (whole : relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections ∈ M.sets)
    (smallWhole : M.groundEmbeddable (relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections) ZFSet.omega)
    (below : row ≤ r) (belowH : row ≤ a.iso h r)
    (sourceSubset : A ⊆ largerA) (imageSubset : image (t.encode h) A ⊆ largerA)
    (fixed : h ∈ d.principalFix V) (cap : d.iso h D ≤ K)
    (anchorGood : ∀ idx u w E,
      stageOneAssignment idx u w ∈ A →
      ZFSet.pair idx E ∈ refinementIndexFieldGraph I b.carrier 2 →
      ZFSet.pair E (b.encode K) ∈ b.conditionOrder →
      ZFSet.pair E (b.encode V) ∈ b.conditionOrder)
    (profileGood : ∀ F ∈ M.preparedSelectionProfiles A stages upperQ b.carrier T selections,
      b.encode V ∉ F → b.encode K ∉ F) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    (∀ z ∈ image (t.encode h) A, ZFSet.pair z (b.encode (d.iso h D)) ∈
      stageOneDataBounds (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples) →
    ZFSet.pair (c.encode row) (assignmentCut levels alpha largerA) ∈ Q →
    stageOneRawCrossCollisions M fields A (image (t.encode h) A)
      (ZFSet.pair (c.encode row) (assignmentCut levels alpha largerA)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  dsimp only
  intro movedData validCut
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have canonicalStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have environment := M.semanticStructuralPrefix_preparationEnvironment c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member fields canonicalStored
  have hQ : lower.carrier ∈ M.sets := environment.ground 7
  have orderGround : lower.conditionOrder ∈ M.sets := environment.ground 8
  obtain ⟨stage, stored⟩ := trace.1.total member
  have sameStage := (trace.2 alpha member stage stored).trans
    (M.semanticStructuralPrefix_stageCode c a t b d base directed T T2 rowTop pairing unions powers
      separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps
      supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows
      hh ordinal trace hAlpha cutOrdinal subset)
  have exactStored : ZFSet.pair alpha
      (forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t))
      ∈ history := sameStage ▸ stored
  let localImage := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, localImage g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  have liftedSupport (Z : L) := a.positionSupport_of_codeLift c.pairEmpty act lower
    (M.refinementHistoryRowNameLift c ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier)
    (M.refinementHistoryRowNameLift_val c ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier)
    (M.refinementHistoryRowNameLift_stabilizer c ((run).carriers.restrict cutOrdinal subset) cutOrdinal
      carrier a act localImage coordinates emptyImage)
    T valid1 b d S mu positions tuples Z range (support Z)
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have profileFacts := M.preparedSelectionProfiles_ground_countable pairing unions powers separation collection
    infinite choice carrier hT hs hPacked nodes (run).carriers.data selected whole smallWhole
    (M.semanticStructuralTrace_storedPreparation_request_bounds c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace infinite choice)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let upper : SetMembers upperQ := SetMembers.ofMem _ source
  have upperCode : SetMembers.raw upper = ZFSet.pair (c.encode r) A := SetMembers.raw_ofMem _ _
  have actionCode (j : G) := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace j upper r A upperCode
  have sourceAct : ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A) ∈ upperQ :=
    actionCode h ▸ SetMembers.raw_mem ((upperAct).iso h upper)
  have imageOne : image (t.encode 1) A = A := by
    have equal := actionCode 1
    simp only [(upperAct).one, a.one, upperCode] at equal
    exact (ZFSet.pair_inj.1 equal).2.symm
  let qStrong : SetMembers Q := SetMembers.ofMem _ validCut
  have strongCode : lower.encode qStrong = ZFSet.pair (c.encode row)
      (assignmentCut levels alpha largerA) := SetMembers.raw_ofMem _ _
  intro sharedIdx hi rawU hu rawNewU hNewU rawW hw rawNewW hNewW original newMember
  have bound := movedData _ newMember
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ := M.exists_niceRefinementIndex_fields act lower b d
    alpha T T2 valid system.valid2 hi
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let x := stageOneAssignment idx rawU rawW
  let u : (M.nameDomain lower).names := ⟨⟨rawU, valid rawU hu⟩, M.transitive hT hu⟩
  let w : (M.nameDomain lower).names := ⟨⟨rawW, valid rawW hw⟩, M.transitive hT hw⟩
  let newU : (M.nameDomain lower).names := ⟨⟨rawNewU, valid rawNewU hNewU⟩, M.transitive hT hNewU⟩
  let newW : (M.nameDomain lower).names := ⟨⟨rawNewW, valid rawNewW hNewW⟩, M.transitive hT hNewW⟩
  obtain ⟨y, selectionEdge, _⟩ := selectionFunction.2 x original
  have valueBound := (ZFSet.pair_mem_prod.1 (selectionFunction.1 selectionEdge)).2
  obtain ⟨beta, _hBeta, output, ho, rfl⟩ := ZFSet.mem_prod.1 valueBound
  obtain ⟨sourceCondition, hSource, tail, ht, rfl⟩ := ZFSet.mem_prod.1 ho
  obtain ⟨sourceRow, _hSourceRow, sourceA, _hSourceA, rfl⟩ :=
    ZFSet.mem_prod.1 (M.refinementHistoryForcing_shape c.carrier T stages packed hSource)
  obtain ⟨k, _hkBound, enumerations, _heBound, rfl⟩ := ZFSet.mem_prod.1 ht
  obtain ⟨hBeta, sourceCondition, _sourceSubset, _hk, _he, other, otherStored,
      terms, _nodeCarrier, _meet, selectedAssignment, rawq, hq, cut, family⟩ :=
    M.preparedWitnessSelection_entry (run).carriers.data (selected selectionEdge)
  have inSource := (mem_assignmentOnIndices (other 0) T sourceA x).1 selectedAssignment
  have indexOther := (stageOneAssignment_mem_assignments (other 0) T idx rawU rawW).1 inSource.2
  have alphaEdge := (run).carriers.data.coverage alpha member fields canonicalStored idx hi rawU hu rawW hw
  have betaEdge := (run).carriers.data.coverage beta hBeta other otherStored idx indexOther.1
    rawU (terms.symm ▸ hu) rawW (terms.symm ▸ hw)
  have sameStage : beta = alpha := by
    have fn := (run).carriers.data.levels_function
    have hx := (ZFSet.pair_mem_prod.1 (fn.1 alphaEdge)).1
    obtain ⟨_, _, unique⟩ := fn.2 x hx
    exact (unique _ betaEdge).trans (unique _ alphaEdge).symm
  subst beta
  have sameFields : other = fields := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique otherStored canonicalStored)
  subst other
  obtain ⟨qOriginal, rfl⟩ := (lower.mem_carrier rawq).1 hq
  let cls := M.stageOneClassName lower pairing unions powers separation collection hQ orderGround hT valid
  have certificate (side : Fin 2) :
      ∃ F B f e names,
        ZFSet.pair ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain lower).names) side).val.val
          (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
        PreparedCertificateCode M lower.carrier lower.conditionOrder (lower.encode qOriginal)
          b.carrier b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder)
          (M.groundRelations T lower.carrier) (M.niceVisibilityGraph act lower b T d.principalFix)
          (lower.encode ⊤) ZFSet.omega
          ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain lower).names) side).val.val F B f e names := by
    have facts := M.semanticStructuralPrefix_assignmentClassRequest_mem c a t b d base directed
      T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
      group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
      symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice
      sourceCondition C E U Rf Rc hi u.val w.val hu hw inSource.1 side
    obtain ⟨F, B, f, e, names, _hF, _hB, _hf, _he, _hn, kEdge, _enumEdge, code⟩ :=
      selectedFamilyCertificate_p1 M family facts.1
    have nameEq : ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain lower).names) side).val.val =
        (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u.val (fun _ => w.val) side)).val := by
      exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) side
    exact ⟨F, B, f, e, names, nameEq.symm ▸ kEdge, nameEq.symm ▸ code⟩
  obtain ⟨F0, B0, f0, e0, names0, edge0, code0⟩ := certificate 0
  obtain ⟨F1, B1, f1, e1, names1, edge1, code1⟩ := certificate 1
  have profile0 := profileFacts.2.2.2 x alpha sourceRow sourceA k enumerations _ F0 B0 f0 selectionEdge edge0
  have profile1 := profileFacts.2.2.2 x alpha sourceRow sourceA k enumerations _ F1 B1 f1 selectionEdge edge1
  have testFacts := M.semanticStructuralPrefix_aligned_cut_tests_at_larger_cut c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
    r (a.iso h r) row A (image (t.encode h) A) largerA h 1 source sourceAct belowH le_rfl
    (by simpa only [a.one] using below) (fun _ hx => hx)
    (by simpa only [imageOne] using sourceSubset) imageSubset qOriginal qStrong cut strongCode
  have anchorEdge : ZFSet.pair idx (b.encode E) ∈ refinementIndexFieldGraph I b.carrier 2 := by
    obtain ⟨_, _, _, _, _, rawE, _, _, _, _, _, edge, _⟩ :=
      (stageOneDataBounds_assignment_entry (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples idx rawNewU rawNewW (b.encode (d.iso h D))).1 bound
    have same : rawE = b.encode E :=
      ((refinementIndexFieldGraph_entry I b.carrier ![alpha, b.encode C, b.encode E,
        U.val.val, Rf.val.val, Rc.val.val] 2 rawE).1 edge).2.2
    exact same ▸ edge
  have avoid : E ≤ K → E ≤ V := fun le =>
    (b.pair_mem_conditionOrder E V).1
      (anchorGood idx rawU rawW (b.encode E) original anchorEdge
        ((b.pair_mem_conditionOrder E K).2 le))
  have collisions := M.structuralAssignment_prepared_insertion_collision act lower t b d base directed
    alpha T T2 system pairing unions powers separation collection hQ orderGround group nodes supports hAlpha hT
    small trace.1 exactStored I S mu positions tuples A liftedSupport h D K V C E U Rf Rc u w newU newW
    hi hu hw hNewU hNewW qOriginal qStrong
    (by simpa only [(act).one] using testFacts.2.2.1) testFacts.2.2.2 fixed cap avoid
    ![F0, F1] ![B0, B1] ![f0, f1] ![e0, e1] ![names0, names1]
    (Fin.cases (profileGood F0 profile0)
      (Fin.cases (profileGood F1 profile1) (fun j => Fin.elim0 j)))
    original bound testFacts.1 testFacts.2.1
    (Fin.cases code0 (Fin.cases code1 (fun j => Fin.elim0 j)))
  rw [strongCode] at collisions
  exact collisions.2

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_insertion_crossCollisions_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_insertion_crossCollisions_oai.{u}
