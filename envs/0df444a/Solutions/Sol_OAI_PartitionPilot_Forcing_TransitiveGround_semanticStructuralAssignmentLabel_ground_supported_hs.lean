-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_ground_supported_hs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:29:05.640333+00:00
-- url     : https://prove2.me/submissions/19e415aa-15e4-45c5-be48-82dacab9fd9d

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
import Definitions.Def_OAIQ253P011
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralAssignmentLabel_supported_hs

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NonemptyTupleFields
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementIndexCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {level C E U Rf Rc : ZFSet.{u}} (hl : level ∈ M.sets) (hC : C ∈ M.sets)
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hf : Rf ∈ M.sets) (hc : Rc ∈ M.sets) :
    refinementIndexCode level C E U Rf Rc ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 5 _
    (Fin.cases hl (Fin.cases hC (Fin.cases hE (Fin.cases hU
      (Fin.cases hf (Fin.cases hc (fun j => Fin.elim0 j)))))))

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NamePresentationEquivalences
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
universe u
variable {P : Type u} (s : Presentation P)

theorem encode_intoSet (B : ZFSet.{u}) (sub : s.carrier ⊆ B) (p : P) :
    (SetMembers.presentation B).encode (s.intoSet B sub p) = s.encode p :=
  SetMembers.raw_ofMem _ _

end PartitionPilot.SetRealization.Presentation

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementAssignmentLabelNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} [PartialOrder P] [OrderTop P]
variable {s : Presentation P} (upper : Presentation Q) (incl : P → Q) (one : Q)

theorem entry_refinementAssignmentLabel (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (Rf Rc : Name s)
    (sigma : Name upper) (p : Q) :
    Entry sigma (refinementAssignmentLabel upper incl one T valid idx Rf Rc) p ↔
      ∃ v w : Name s, v.val ∈ T ∧ w.val ∈ T ∧
        (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A) ∧
        orderedPair one (rename upper incl (refinementClass T valid Rc v))
          (rename upper incl (refinementClass T valid Rf w)) = sigma := by
  rw [refinementAssignmentLabel, entry_assemble]
  constructor
  · rintro ⟨a, equal, condition⟩
    refine ⟨⟨a.val.1.1.val, valid _ a.val.1.1.property⟩,
      ⟨a.val.1.2.val, valid _ a.val.1.2.property⟩,
      a.val.1.1.property, a.val.1.2.property, ?_, equal⟩
    exact condition ▸ a.property
  · rintro ⟨v, w, hv, hw, literal, equal⟩
    exact ⟨⟨((⟨v.val, hv⟩, ⟨w.val, hw⟩), p), literal⟩, equal, rfl⟩

end PartitionPilot.Forcing.Name

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCompleteProjectionAtomicTruth
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u}

theorem rename_between_mem (s : Presentation P) (t : Presentation Q)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) : (Name.rename t f τ).val ∈ M.sets := by
  let U := s.carrier ∪ t.carrier
  let D := ZFSet.sep (fun x => x ∉ s.carrier) U
  let F := s.graph t f
  let G := F ∪ identityFunctionGraph D
  have subS : s.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inl hx)
  have subT : t.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inr hx)
  have hU : U ∈ M.sets := M.binary_union_mem pairing unions hs ht
  have hD : D ∈ M.sets := M.bounded_separation_mem separation (.neg (.mem 0 1))
    (extend s.carrier Fin.elim0) (Fin.cases hs (fun i => Fin.elim0 i)) hU
  have hG : G ∈ M.sets := M.binary_union_mem pairing unions hf
    (M.identityFunctionGraph_mem pairing unions powers separation hD)
  have ff := s.graph_isFunc t f
  have full : ZFSet.IsFunc U U G := by
    constructor
    · intro z hz
      rcases ZFSet.mem_union.1 hz with old | identity
      · obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (ff.1 old)
        exact ZFSet.mem_prod.2 ⟨x, subS hx, y, subT hy, eq⟩
      · obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph D z).1 identity
        exact ZFSet.pair_mem_prod.2 ⟨(ZFSet.mem_sep.1 hx).1, (ZFSet.mem_sep.1 hx).1⟩
    · intro x hx
      by_cases source : x ∈ s.carrier
      · obtain ⟨y, entry, unique⟩ := ff.2 x source
        refine ⟨y, ZFSet.mem_union.2 (Or.inl entry), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact unique z old
        · exact False.elim ((ZFSet.mem_sep.1
            ((pair_mem_identityFunctionGraph D x z).1 identity).2).2 source)
      · refine ⟨x, ZFSet.mem_union.2 (Or.inr
          ((pair_mem_identityFunctionGraph D x x).2 ⟨rfl, ZFSet.mem_sep.2 ⟨hx, source⟩⟩)), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact False.elim (source (ZFSet.pair_mem_prod.1 (ff.1 old)).1)
        · exact ((pair_mem_identityFunctionGraph D x z).1 identity).1.symm
  let u := SetMembers.presentation U
  let es := s.intoSet U subS
  let et := t.intoSet U subT
  let h := u.decodeFunction u G full
  have commute (p : P) : h (es p) = et (f p) := by
    apply (u.decodeFunction_iff u G full (es p) (et (f p))).2
    rw [s.encode_intoSet U subS, t.encode_intoSet U subT]
    exact ZFSet.mem_union.2 (Or.inl ((s.pair_mem_graph t f p (f p)).2 rfl))
  have sourceCode := Name.rename_val_of_encode u es (s.encode_intoSet U subS) τ
  have ground := M.rename_mem u pairing unions powers separation collection hU h
    ((u.graph_decodeFunction u G full).symm ▸ hG)
    (Name.rename u es τ) (sourceCode ▸ hτ)
  have equation : Name.rename u h (Name.rename u es τ) =
      Name.rename u et (Name.rename t f τ) := by
    rw [Name.rename_comp, Name.rename_comp]
    apply congrArg (fun k => Name.rename u k τ)
    funext p
    exact commute p
  rw [equation, Name.rename_val_of_encode u et (t.encode_intoSet U subT)] at ground
  exact ground

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RenamedPairNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u}

theorem exists_uniformRename_between (s : Presentation P) (t : Presentation Q)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets) :
    ∃ G ∈ M.sets,
      G = s.graph t f ∪ identityFunctionGraph
        (ZFSet.sep (fun x => x ∉ s.carrier) (s.carrier ∪ t.carrier)) ∧
      ∀ (σ : Name s) (τ : Name t), σ.val ∈ M.sets → τ.val ∈ M.sets →
        (Realize M.sets uniformRenameFormula
          (extend σ.val (extend τ.val (extend (s.carrier ∪ t.carrier) (extend G Fin.elim0)))) ↔
          Name.rename t f σ = τ) := by
  let U := s.carrier ∪ t.carrier
  let D := ZFSet.sep (fun x => x ∉ s.carrier) U
  let F := s.graph t f
  let G := F ∪ identityFunctionGraph D
  have subS : s.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inl hx)
  have subT : t.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inr hx)
  have hU : U ∈ M.sets := M.binary_union_mem pairing unions hs ht
  have hD : D ∈ M.sets := M.bounded_separation_mem separation (.neg (.mem 0 1))
    (extend s.carrier Fin.elim0) (Fin.cases hs (fun i => Fin.elim0 i)) hU
  have hG : G ∈ M.sets := M.binary_union_mem pairing unions hf
    (M.identityFunctionGraph_mem pairing unions powers separation hD)
  have ff := s.graph_isFunc t f
  have full : ZFSet.IsFunc U U G := by
    constructor
    · intro z hz
      rcases ZFSet.mem_union.1 hz with old | identity
      · obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (ff.1 old)
        exact ZFSet.mem_prod.2 ⟨x, subS hx, y, subT hy, eq⟩
      · obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph D z).1 identity
        exact ZFSet.pair_mem_prod.2 ⟨(ZFSet.mem_sep.1 hx).1, (ZFSet.mem_sep.1 hx).1⟩
    · intro x hx
      by_cases source : x ∈ s.carrier
      · obtain ⟨y, entry, unique⟩ := ff.2 x source
        refine ⟨y, ZFSet.mem_union.2 (Or.inl entry), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact unique z old
        · exact False.elim ((ZFSet.mem_sep.1
            ((pair_mem_identityFunctionGraph D x z).1 identity).2).2 source)
      · refine ⟨x, ZFSet.mem_union.2 (Or.inr
          ((pair_mem_identityFunctionGraph D x x).2 ⟨rfl, ZFSet.mem_sep.2 ⟨hx, source⟩⟩)), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact False.elim (source (ZFSet.pair_mem_prod.1 (ff.1 old)).1)
        · exact ((pair_mem_identityFunctionGraph D x z).1 identity).1.symm
  let u := SetMembers.presentation U
  let es := s.intoSet U subS
  let et := t.intoSet U subT
  let h := u.decodeFunction u G full
  have commute (p : P) : h (es p) = et (f p) := by
    apply (u.decodeFunction_iff u G full (es p) (et (f p))).2
    rw [s.encode_intoSet U subS, t.encode_intoSet U subT]
    exact ZFSet.mem_union.2 (Or.inl ((s.pair_mem_graph t f p (f p)).2 rfl))
  refine ⟨G, hG, rfl, ?_⟩
  intro σ τ hσ hτ
  have sourceCode := Name.rename_val_of_encode u es (s.encode_intoSet U subS) σ
  have targetCode := Name.rename_val_of_encode u et (t.encode_intoSet U subT) τ
  have graph : u.graph u h = G := u.graph_decodeFunction u G full
  have exactFormula := M.realize_uniformRenameFormula u pairing unions powers separation collection hU h
    (graph ▸ hG) (Name.rename u es σ) (Name.rename u et τ)
    (sourceCode ▸ hσ) (targetCode ▸ hτ)
  change Realize M.sets uniformRenameFormula
    (extend (Name.rename u es σ).val (extend (Name.rename u et τ).val
      (extend U (extend (u.graph u h) Fin.elim0)))) ↔ _ at exactFormula
  rw [sourceCode, targetCode, graph] at exactFormula
  refine exactFormula.trans ?_
  have equation : Name.rename u h (Name.rename u es σ) =
      Name.rename u et (Name.rename t f σ) := by
    rw [Name.rename_comp, Name.rename_comp]
    apply congrArg (fun k => Name.rename u k σ)
    funext p
    exact commute p
  rw [equation]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [Name.rename_val_of_encode u et (t.encode_intoSet U subT)] using codes
  · intro equal
    exact congrArg (Name.rename u et) equal

end PartitionPilot.Forcing.TransitiveGround

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u} (s : Presentation P) (t : Presentation Q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem renameFamilyGraph_mem (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ x ∈ T, IsName s x) :
    Name.renameFamilyGraph t f T valid ∈ M.sets := by
  obtain ⟨G, hG, _, recognizes⟩ := M.exists_uniformRename_between s t
    pairing unions powers separation collection hs ht f hf
  let U := s.carrier ∪ t.carrier
  let params := extend t.carrier (extend U (extend G Fin.elim0))
  have hU : U ∈ M.sets := M.binary_union_mem pairing unions hs ht
  have meaning (σ : Name s) (hσ : σ.val ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets renamedNameFamilyPairFormula (extend σ.val (extend z params)) ↔
        z = ZFSet.pair σ.val (Name.rename t f σ).val := by
    rw [renamedNameFamilyPairFormula, realize_ex]
    constructor
    · rintro ⟨v, hv, named, renamed, pair⟩
      rw [realize_domainApplication, map_extend, map_empty] at named
      have validV : IsName t v :=
        (M.realize_uniformNameFormula t pairing unions powers separation collection ht v hv).1 named
      rw [realize_binaryApplication, map_extend, map_extend, map_empty] at renamed
      have eq := (recognizes σ ⟨v, validV⟩ hσ hv).1 renamed
      have pairEq := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hσ hv).1 pair
      exact (congrArg Subtype.val eq).symm ▸ pairEq
    · intro equal
      have hv := M.rename_between_mem s t pairing unions powers separation collection hs ht f hf σ hσ
      refine ⟨(Name.rename t f σ).val, hv, ?_, ?_, ?_⟩
      · rw [realize_domainApplication, map_extend, map_empty]
        exact (M.realize_uniformNameFormula t pairing unions powers separation collection ht _ hv).2
          (Name.rename t f σ).property
      · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
        exact (recognizes σ (Name.rename t f σ) hσ hv).2 rfl
      · exact (M.realize_orderedPairFormula pairing 2 1 0 _ hz hσ hv).2 equal
  apply M.definable_image_mem separation collection renamedNameFamilyPairFormula params
    (Fin.cases ht (Fin.cases hU (Fin.cases hG (fun i => Fin.elim0 i)))) hT
  · intro z hz
    obtain ⟨σ, hσ, rfl⟩ := (Name.mem_renameFamilyGraph t f T valid z).1 hz
    exact M.orderedPair_mem pairing (M.transitive hT hσ)
      (M.rename_between_mem s t pairing unions powers separation collection hs ht f hf σ (M.transitive hT hσ))
  · intro z hz
    rw [Name.mem_renameFamilyGraph]
    constructor
    · rintro ⟨σ, hσ, eq⟩
      exact ⟨σ.val, hσ, (meaning σ (M.transitive hT hσ) z hz).2 eq⟩
    · rintro ⟨x, hx, rel⟩
      exact ⟨⟨x, valid x hx⟩, hx, (meaning ⟨x, valid x hx⟩ (M.transitive hT hx) z hz).1 rel⟩
  · intro x hx y hy z hz first second
    exact ((meaning ⟨x, valid x hx⟩ (M.transitive hT hx) y hy).1 first).trans
      ((meaning ⟨x, valid x hx⟩ (M.transitive hT hx) z hz).1 second).symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRefinementLiftedClassGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u} [PartialOrder P] [OrderTop P]
variable (lower : Presentation P) (upper : Presentation Q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem exists_refinementLiftedClassGraph
    (lowerGround : lower.carrier ∈ M.sets) (upperGround : upper.carrier ∈ M.sets)
    (lowerOrder : lower.conditionOrder ∈ M.sets)
    (incl : P → Q) (inclGround : lower.graph upper incl ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName lower z)
    (R : Name lower) (hR : R.val ∈ M.sets) :
    ∃ graph ∈ M.sets, ∀ (v : Name lower) (y : ZFSet.{u}),
      ZFSet.pair v.val y ∈ graph ↔ v.val ∈ T ∧
        y = (Name.rename upper incl (Name.refinementClass T valid R v)).val := by
  let classesGraph := Name.refinementClassGraph T valid R T valid
  have hClassesGraph : classesGraph ∈ M.sets :=
    M.refinementClassGraph_mem lower pairing unions powers separation collection
      lowerGround lowerOrder hT hT valid valid R hR
  let classes := functionGraphRange T classesGraph
  have hClasses : classes ∈ M.sets :=
    M.functionGraphRange_mem unions separation hT hClassesGraph
  have validClasses : ∀ z ∈ classes, IsName lower z := by
    intro z hz
    obtain ⟨v, hv, entry⟩ := (mem_functionGraphRange T classesGraph z).1 hz
    let name : Name lower := ⟨v, valid v hv⟩
    have equal := ((Name.pair_mem_refinementClassGraph T valid R T valid name z).1 entry).2
    exact equal.symm ▸ (Name.refinementClass T valid R name).property
  let renamings := Name.renameFamilyGraph upper incl classes validClasses
  have hRenamings : renamings ∈ M.sets :=
    M.renameFamilyGraph_mem lower upper pairing unions powers separation collection
      lowerGround upperGround incl inclGround classes hClasses validClasses
  let lifted := functionGraphRange classes renamings
  have hLifted : lifted ∈ M.sets :=
    M.functionGraphRange_mem unions separation hClasses hRenamings
  refine ⟨relationCompose T classes lifted classesGraph renamings,
    M.relationCompose_mem pairing unions powers separation hT hClasses hLifted hClassesGraph hRenamings, ?_⟩
  intro v y
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨hv, _hy, z, hz, first, second⟩
    have equal := ((Name.pair_mem_refinementClassGraph T valid R T valid v z).1 first).2
    subst z
    exact ⟨hv, ((Name.pair_mem_renameFamilyGraph upper incl classes validClasses
      (Name.refinementClass T valid R v) y).1 second).2⟩
  · rintro ⟨hv, rfl⟩
    have first : ZFSet.pair v.val (Name.refinementClass T valid R v).val ∈ classesGraph :=
      (Name.pair_mem_refinementClassGraph T valid R T valid v _).2 ⟨hv, rfl⟩
    have member : (Name.refinementClass T valid R v).val ∈ classes :=
      (mem_functionGraphRange T classesGraph _).2 ⟨v.val, hv, first⟩
    have second : ZFSet.pair (Name.refinementClass T valid R v).val
        (Name.rename upper incl (Name.refinementClass T valid R v)).val ∈ renamings :=
      (Name.pair_mem_renameFamilyGraph upper incl classes validClasses
        (Name.refinementClass T valid R v) _).2 ⟨member, rfl⟩
    exact ⟨hv, (mem_functionGraphRange classes renamings _).2
      ⟨_, member, second⟩, _, member, first, second⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRowCompleteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace RecursiveRefinementOrderHistory
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history alpha : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha)
variable (subset : alpha ⊆ stages)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "L" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
local notation "sU" => SetMembers.presentation U
local notation "sL" => SetMembers.presentation L

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)

variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (top : ZFSet.{u}) (topMem : top ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row top ∈ rowOrder)
variable (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
    ∀ A lower stronger, stageOneRawTests M d A lower →
      ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
local notation "inc" => run.inclusionFunction ordinal cutOrdinal subset pairing unions powers separation infinite choice
  hStages hHistory hT hAlpha hRows top topMem topRows mono

theorem inclusionFunction_graph : (sL).graph sU inc = identityFunctionGraph L := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph, mem_identityFunctionGraph]
  have code := run.inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
    hStages hHistory hT hAlpha hRows top topMem topRows mono
  constructor
  · rintro ⟨x, rfl⟩
    change ∃ y ∈ L, ZFSet.pair (SetMembers.raw x) (SetMembers.raw (inc x)) = ZFSet.pair y y
    rw [code x]
    exact ⟨SetMembers.raw x, SetMembers.raw_mem x, rfl⟩
  · rintro ⟨x, member, rfl⟩
    let q := SetMembers.ofMem x member
    refine ⟨q, ?_⟩
    change ZFSet.pair (SetMembers.raw q) (SetMembers.raw (inc q)) = ZFSet.pair x x
    rw [code q, SetMembers.raw_ofMem]

include pairing unions powers separation hStages hHistory hT hAlpha hRows in
theorem inclusionFunction_graph_mem (omega : ZFSet.omega ∈ M.sets) :
    (sL).graph sU inc ∈ M.sets := by
  rw [run.inclusionFunction_graph]
  exact M.identityFunctionGraph_mem pairing unions powers separation
    (M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hHistory) omega)

end RecursiveRefinementOrderHistory

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRefinementAssignmentLabelEntries
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P Q : Type u} [PartialOrder P] [OrderTop P]
variable {s : Presentation P} (upper : Presentation Q) (incl : P → Q) (one : Q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem refinementAssignmentLabel_mem_of_graphs
    (hUpper : upper.carrier ∈ M.sets) (hOne : upper.encode one ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (idx : ZFSet.{u}) (hIdx : idx ∈ M.sets) (Rf Rc : Name s)
    (Gc Gf : ZFSet.{u}) (hGc : Gc ∈ M.sets) (hGf : Gf ∈ M.sets)
    (coarse : ∀ (v : Name s) y, ZFSet.pair v.val y ∈ Gc ↔ v.val ∈ T ∧
      y = (Name.rename upper incl (Name.refinementClass T valid Rc v)).val)
    (fine : ∀ (w : Name s) y, ZFSet.pair w.val y ∈ Gf ↔ w.val ∈ T ∧
      y = (Name.rename upper incl (Name.refinementClass T valid Rf w)).val) :
    (Name.refinementAssignmentLabel upper incl one T valid idx Rf Rc).val ∈ M.sets := by
  let cv (v : Name s) := Name.rename upper incl (Name.refinementClass T valid Rc v)
  let fw (w : Name s) := Name.rename upper incl (Name.refinementClass T valid Rf w)
  let label := Name.refinementAssignmentLabel upper incl one T valid idx Rf Rc
  let X := functionGraphRange T Gc
  let Y := functionGraphRange T Gf
  have hX := M.functionGraphRange_mem unions separation hT hGc
  have hY := M.functionGraphRange_mem unions separation hT hGf
  have cvX (v : Name s) (hv : v.val ∈ T) : (cv v).val ∈ X :=
    (mem_functionGraphRange T Gc _).2 ⟨v.val, hv, (coarse v _).2 ⟨hv, rfl⟩⟩
  have fwY (w : Name s) (hw : w.val ∈ T) : (fw w).val ∈ Y :=
    (mem_functionGraphRange T Gf _).2 ⟨w.val, hw, (fine w _).2 ⟨hw, rfl⟩⟩
  let bound := ZFSet.prod (orderedPairNameFamily (upper.encode one) X Y) upper.carrier
  have hBound : bound ∈ M.sets := M.prod_mem pairing unions powers separation
    (M.orderedPairNameFamily_mem pairing unions powers separation hOne hX hY) hUpper
  have bounded : label.val ⊆ bound := by
    intro z hz
    obtain ⟨sigma, p, rfl⟩ := Name.entries_cover label hz
    obtain ⟨v, w, hv, hw, _, rfl⟩ :=
      (Name.entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc sigma p).1 hz
    apply ZFSet.pair_mem_prod.2
    refine ⟨?_, upper.encode_mem p⟩
    exact (mem_orderedPairNameFamily _ X Y _).2
      ⟨(cv v).val, cvX v hv, (fw w).val, fwY w hw, Name.orderedPair_code one (cv v) (fw w)⟩
  let params : Fin 6 → ZFSet.{u} := ![T, Gc, Gf, upper.carrier, idx, upper.encode one]
  have paramsGround : ∀ j, params j ∈ M.sets :=
    Fin.cases hT (Fin.cases hGc (Fin.cases hGf (Fin.cases hUpper
      (Fin.cases hIdx (Fin.cases hOne (fun j => Fin.elim0 j))))))
  have recognized (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets labelEntryFormula (extend z params) ↔ z ∈ label.val := by
    let env := extend z params
    have envGround : ∀ j, env j ∈ M.sets := Fin.cases hz paramsGround
    have body (fields : Fin 10 → ZFSet.{u}) (hg : ∀ j, fields j ∈ M.sets) :
        Realize M.sets
          (.conj (.mem 0 11) (.conj (.mem 1 11) (.conj (.mem 2 14)
          (.conj (orderedPairFormula 2 3 4) (.conj (orderedPairFormula 8 0 1)
          (.conj (orderedPairFormula 9 15 8) (.conj (.mem 9 4)
          (.conj (pairMembershipFormula 0 5 12) (.conj (pairMembershipFormula 1 6 13)
          (.conj (orderedPairNameCodeFormula 7 5 6 16) (orderedPairFormula 10 7 2)))))))))))
          (extendMany 10 fields env) ↔
        fields 0 ∈ T ∧ fields 1 ∈ T ∧ fields 2 ∈ upper.carrier ∧
        fields 2 = ZFSet.pair (fields 3) (fields 4) ∧
        fields 8 = ZFSet.pair (fields 0) (fields 1) ∧
        fields 9 = ZFSet.pair idx (fields 8) ∧ fields 9 ∈ fields 4 ∧
        ZFSet.pair (fields 0) (fields 5) ∈ Gc ∧
        ZFSet.pair (fields 1) (fields 6) ∈ Gf ∧
        fields 7 = orderedPairNameCode (upper.encode one) (fields 5) (fields 6) ∧
        z = ZFSet.pair (fields 7) (fields 2) := by
      have all := extendMany_members 10 fields env hg envGround
      simp only [Realize]
      rw [M.realize_orderedPairFormula pairing 2 3 4 _ (all _) (all _) (all _),
        M.realize_orderedPairFormula pairing 8 0 1 _ (all _) (all _) (all _),
        M.realize_orderedPairFormula pairing 9 15 8 _ (all _) (all _) (all _),
        M.realize_pairMembershipFormula pairing 0 5 12 _ (all _) (all _) (all _),
        M.realize_pairMembershipFormula pairing 1 6 13 _ (all _) (all _) (all _),
        M.realize_orderedPairNameCodeFormula pairing 7 5 6 16 _ all,
        M.realize_orderedPairFormula pairing 10 7 2 _ (all _) (all _) (all _)]
      rfl
    rw [labelEntryFormula, realize_exBlock]
    constructor
    · rintro ⟨fields, hg, holds⟩
      obtain ⟨hv, hw, hp, pCode, vwCode, tripleCode, old, gc, gf, pairCode, entryCode⟩ :=
        (body fields hg).1 holds
      let v : Name s := ⟨fields 0, valid _ hv⟩
      let w : Name s := ⟨fields 1, valid _ hw⟩
      obtain ⟨p, pEq⟩ := (upper.mem_carrier _).1 hp
      have cvEq := ((coarse v _).1 gc).2
      have fwEq := ((fine w _).1 gf).2
      have literal : stageOneAssignment idx v.val w.val ∈ fields 4 := by
        rw [tripleCode, vwCode] at old
        exact old
      have named : fields 7 = (Name.orderedPair one (cv v) (fw w)).val := by
        rw [pairCode, cvEq, fwEq]
        exact (Name.orderedPair_code one (cv v) (fw w)).symm
      rw [entryCode, named, ← pEq]
      exact (Name.entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc _ p).2
        ⟨v, w, hv, hw, ⟨fields 3, fields 4, pEq.trans pCode, literal⟩, rfl⟩
    · intro member
      obtain ⟨sigma, p, rfl⟩ := Name.entries_cover label member
      obtain ⟨v, w, hv, hw, ⟨row, A, pCode, old⟩, rfl⟩ :=
        (Name.entry_refinementAssignmentLabel upper incl one T valid idx Rf Rc sigma p).1 member
      have hp := M.transitive hUpper (upper.encode_mem p)
      have hpCode : ZFSet.pair row A ∈ M.sets := pCode ▸ hp
      have hrow := M.pair_left hpCode
      have hA := M.pair_right hpCode
      have hvM := M.transitive hT hv
      have hwM := M.transitive hT hw
      have hcv := M.transitive hX (cvX v hv)
      have hfw := M.transitive hY (fwY w hw)
      have hpair : (Name.orderedPair one (cv v) (fw w)).val ∈ M.sets := by
        rw [Name.orderedPair_code]
        exact M.orderedPairNameCode_mem pairing hOne hcv hfw
      let fields : Fin 10 → ZFSet.{u} := ![v.val, w.val, upper.encode p, row, A,
        (cv v).val, (fw w).val, (Name.orderedPair one (cv v) (fw w)).val,
        ZFSet.pair v.val w.val, stageOneAssignment idx v.val w.val]
      have hg : ∀ j, fields j ∈ M.sets :=
        Fin.cases hvM (Fin.cases hwM (Fin.cases hp (Fin.cases hrow (Fin.cases hA
          (Fin.cases hcv (Fin.cases hfw (Fin.cases hpair
            (Fin.cases (M.orderedPair_mem pairing hvM hwM)
              (Fin.cases (M.transitive hA old) (fun j => Fin.elim0 j))))))))))
      exact ⟨fields, hg, (body fields hg).2
        ⟨hv, hw, upper.encode_mem p, pCode, rfl, rfl, old,
          (coarse v _).2 ⟨hv, rfl⟩, (fine w _).2 ⟨hw, rfl⟩,
          Name.orderedPair_code one (cv v) (fw w), rfl⟩⟩
  have selected := M.separation_mem separation labelEntryFormula params paramsGround hBound
  have equal : ZFSet.sep (fun z => Realize M.sets labelEntryFormula (extend z params)) bound = label.val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun h => (recognized z (M.transitive hBound h.1)).1 h.2,
      fun h => ⟨bounded h, (recognized z (M.transitive hBound (bounded h))).2 h⟩⟩
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRefinementAssignmentLabelNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u} [PartialOrder P] [OrderTop P]
variable (lower : Presentation P) (upper : Presentation Q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem refinementAssignmentLabel_mem
    (lowerGround : lower.carrier ∈ M.sets) (upperGround : upper.carrier ∈ M.sets)
    (lowerOrder : lower.conditionOrder ∈ M.sets)
    (incl : P → Q) (inclGround : lower.graph upper incl ∈ M.sets) (one : Q)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName lower z)
    (idx : ZFSet.{u}) (hIdx : idx ∈ M.sets)
    (Rf Rc : Name lower) (hRf : Rf.val ∈ M.sets) (hRc : Rc.val ∈ M.sets) :
    (Name.refinementAssignmentLabel upper incl one T valid idx Rf Rc).val ∈ M.sets := by
  obtain ⟨Gc, hGc, coarse⟩ := M.exists_refinementLiftedClassGraph lower upper
    pairing unions powers separation collection lowerGround upperGround lowerOrder
    incl inclGround T hT valid Rc hRc
  obtain ⟨Gf, hGf, fine⟩ := M.exists_refinementLiftedClassGraph lower upper
    pairing unions powers separation collection lowerGround upperGround lowerOrder
    incl inclGround T hT valid Rf hRf
  exact M.refinementAssignmentLabel_mem_of_graphs upper incl one pairing unions powers separation
    upperGround (M.transitive upperGround (upper.encode_mem one)) hT valid idx hIdx Rf Rc
    Gc Gf hGc hGf coarse fine

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
open SetRealization SetFormula Compression.RecursiveMaps
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
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace member
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "inc" => RecursiveRefinementOrderHistory.inclusionFunction run ordinal cutOrdinal subset
  pairing unions powers separation infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono

theorem semanticStructuralAssignmentLabel_ground_supported_hs_oai :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      (run).carriers ordinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let upper := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices lowerAct lower b d alpha T T2 valid →
      let label := Name.refinementAssignmentLabel upper inc ⊤ T valid
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) Rf Rc
      label.val ∈ M.sets ∧ d.principalFix E ≤ (upperAct).stabilizer upper label ∧
        HereditarilySymmetric upperAct upper (d.principalSupportFamily base directed) label := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  let upper := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have lowerGround : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hAlpha hLowerPacked omega
  have upperGround : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hs hPacked omega
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha hLowerPacked omega
  have inclusionGround : lower.graph upper inc ∈ M.sets :=
    (run).inclusionFunction_graph_mem ordinal cutOrdinal subset pairing unions powers separation
      hs hPacked hT hAlpha carrier infinite choice rowTop topMem topRows mono omega
  dsimp only
  intro C E U Rf Rc index
  have hIdx := M.refinementIndexCode_mem pairing hAlpha
    (M.transitive nodes (b.encode_mem C)) (M.transitive nodes (b.encode_mem E))
    U.property Rf.property Rc.property
  refine ⟨M.refinementAssignmentLabel_mem lower upper pairing unions powers separation collection
    lowerGround upperGround lowerOrder inc inclusionGround ⊤ T hT valid _ hIdx
    Rf.val Rc.val Rf.property Rc.property, ?_⟩
  exact M.semanticStructuralAssignmentLabel_supported_hs c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice C E U Rf Rc index

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_ground_supported_hs_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_ground_supported_hs_oai.{u}
