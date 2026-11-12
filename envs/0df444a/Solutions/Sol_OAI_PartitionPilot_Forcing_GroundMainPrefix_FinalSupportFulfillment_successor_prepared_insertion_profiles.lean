-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.successor_prepared_insertion_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:33:05.504602+00:00
-- url     : https://prove2.me/submissions/6182b10b-5f98-40ec-b622-665cdc9a61bb

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_augmented_profile_family
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_support_prepared_strengthening
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_augmentedClassRequests

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProductActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section



namespace PartitionPilot.SetRealization.Presentation

universe u
variable {I : Type u} [Bot I]

theorem mem_nonbottom_carrier (s : Presentation I) (z : ZFSet.{u}) :
    z ∈ s.nonbottom.carrier ↔ z ∈ s.carrier ∧ z ≠ s.encode ⊥ := by
  change z ∈ ZFSet.sep (fun w => w ≠ s.encode ⊥) s.carrier ↔ _
  exact ZFSet.mem_sep

end PartitionPilot.SetRealization.Presentation

end


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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RowPositionBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace BoundedFormula

theorem truth_rowPositionSequenceAtFormula {n} (L r I delta f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowPositionSequenceAtFormula L r I delta f) env ↔
      RowPositionSequenceAt (env L) (env r) (env I) (env delta) (env f) := by
  simp only [rowPositionSequenceAtFormula, Truth, truth_functionFormula,
    truth_exMem, truth_imp, truth_pairMembershipFormula]
  change (ZFSet.IsFunc (env delta) (env I) (env f) ∧
    ∃ D ∈ env L, ∀ a ∈ env delta, ∀ x ∈ env I,
      ZFSet.pair a x ∈ env f → ZFSet.pair x D ∈ env r) ↔ _
  constructor
  · rintro ⟨function, D, hD, bounds⟩
    refine ⟨function, D, hD, ?_⟩
    intro a x entry
    have shape := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact bounds a shape.1 x shape.2 entry
  · rintro ⟨function, D, hD, bounds⟩
    exact ⟨function, D, hD, fun a _ x _ entry => bounds a x entry⟩

theorem truth_rowPositionSequenceFormula {n} (L r I mu f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowPositionSequenceFormula L r I mu f) env ↔
      RowPositionSequenceCode (env L) (env r) (env I) (env mu) (env f) := by
  simp only [rowPositionSequenceFormula, truth_disj, truth_exMem, truth_rowPositionSequenceAtFormula]
  change (RowPositionSequenceAt (env L) (env r) (env I) (env mu) (env f) ∨
    ∃ delta ∈ env mu, RowPositionSequenceAt (env L) (env r) (env I) delta (env f)) ↔ _
  constructor
  · rintro (whole | ⟨delta, hdelta, code⟩)
    · exact ⟨env mu, ZFSet.mem_insert _ _, whole⟩
    · exact ⟨delta, ZFSet.mem_insert_of_mem _ hdelta, code⟩
  · rintro ⟨delta, hdelta, code⟩
    rcases ZFSet.mem_insert_iff.1 hdelta with equal | hdelta
    · exact Or.inl (equal ▸ code)
    · exact Or.inr ⟨delta, hdelta, code⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowPositionSequences_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {L r I mu : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hmu : mu ∈ M.sets) : M.rowPositionSequences L r I mu ∈ M.sets := by
  let formula : BoundedFormula 5 := BoundedFormula.rowPositionSequenceFormula 1 2 3 4 0
  let params := extend L (extend r (extend I (extend mu Fin.elim0)))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hL (Fin.cases hr (Fin.cases hI (Fin.cases hmu (fun i => Fin.elim0 i))))
  have ground := M.bounded_separation_mem separation formula params members
    (M.groundRelations_mem pairing unions powers separation hmu hI)
  have equal : ZFSet.sep (fun f => BoundedFormula.Truth formula (extend f params))
      (M.groundRelations mu I) = M.rowPositionSequences L r I mu := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_sep, rowPositionSequences, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_rowPositionSequenceFormula 1 2 3 4 0 _)
  exact equal ▸ ground

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula

theorem truth_rowPositionBoundFormula {n} (mu I r f D : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (rowPositionBoundFormula mu I r f D) env ↔
      RowPositionBound (env mu) (env I) (env r) (env f) (env D) := by
  simp only [rowPositionBoundFormula, Truth, truth_relationBetweenFormula, truth_imp,
    truth_pairMembershipFormula]
  change (env f ⊆ ZFSet.prod (env mu) (env I) ∧ ∀ a ∈ env mu, ∀ x ∈ env I,
    ZFSet.pair a x ∈ env f → ZFSet.pair x (env D) ∈ env r) ↔ _
  constructor
  · rintro ⟨shape,bound⟩
    refine ⟨shape,fun a x entry => ?_⟩
    have fields := ZFSet.pair_mem_prod.1 (shape entry)
    exact bound a fields.1 x fields.2 entry
  · rintro ⟨shape,bound⟩
    exact ⟨shape,fun a _ x _ entry => bound a x entry⟩

end BoundedFormula

theorem RowPositionBound.mono {L : Type u} [Preorder L] (s : Presentation L)
    {mu I f : ZFSet.{u}} {D E : L}
    (bound : RowPositionBound mu I s.conditionOrder f (s.encode D)) (le : D ≤ E) :
    RowPositionBound mu I s.conditionOrder f (s.encode E) := by
  refine ⟨bound.1,fun a x entry => ?_⟩
  have lower := bound.2 a x entry
  have hx : x ∈ s.carrier :=
    (ZFSet.pair_mem_prod.1 ((s.product s).subset_carrier (fun z => z.1 ≤ z.2) lower)).1
  obtain ⟨x,rfl⟩ := (s.mem_carrier x).1 hx
  exact (s.pair_mem_conditionOrder x E).2 (le_trans ((s.pair_mem_conditionOrder x D).1 lower) le)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowPositionSequence_bound {L r I mu f : ZFSet.{u}}
    (member : f ∈ M.rowPositionSequences L r I mu) :
    ∃ D ∈ L, RowPositionBound mu I r f D := by
  have data := ZFSet.mem_sep.1 member
  have shape := ((M.mem_groundRelations mu I f).1 data.1).2
  obtain ⟨delta,_,_,D,hD,bound⟩ := data.2
  exact ⟨D,hD,shape,bound⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

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

namespace BoundedFormula

theorem truth_stageOneDataBoundEntryFormula {n} (z A I T S L mu X r anchors tuples : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (stageOneDataBoundEntryFormula z A I T S L mu X r anchors tuples) env ↔
      ∃ v ∈ env A, ∃ D ∈ env L, ∃ i ∈ env I, ∃ u ∈ env T, ∃ w ∈ env T, ∃ E ∈ env L,
        ∃ fu ∈ env S, ∃ fw ∈ env S, env z = ZFSet.pair v D ∧ v = stageOneAssignment i u w ∧
          ZFSet.pair i E ∈ env anchors ∧ ZFSet.pair E D ∈ env r ∧
          ZFSet.pair fu u ∈ env tuples ∧ ZFSet.pair fw w ∈ env tuples ∧
          RowPositionBound (env mu) (env X) (env r) fu D ∧
          RowPositionBound (env mu) (env X) (env r) fw D := by
  simp only [stageOneDataBoundEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_stageOneAssignmentFormula, truth_pairMembershipFormula, truth_rowPositionBoundFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem stageOneDataBounds_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A I T S L mu X r anchors tuples : ZFSet.{u}}
    (hA : A ∈ M.sets) (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hS : S ∈ M.sets)
    (hL : L ∈ M.sets) (hmu : mu ∈ M.sets) (hX : X ∈ M.sets) (hr : r ∈ M.sets)
    (hAnchors : anchors ∈ M.sets) (hTuples : tuples ∈ M.sets) :
    stageOneDataBounds A I T S L mu X r anchors tuples ∈ M.sets := by
  let params : Fin 10 → ZFSet.{u} := ![A,I,T,S,L,mu,X,r,anchors,tuples]
  have members : ∀ j, params j ∈ M.sets := Fin.cases hA (Fin.cases hI (Fin.cases hT
    (Fin.cases hS (Fin.cases hL (Fin.cases hmu (Fin.cases hX (Fin.cases hr
      (Fin.cases hAnchors (Fin.cases hTuples (fun j => Fin.elim0 j))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.stageOneDataBoundEntryFormula 0 1 2 3 4 5 6 7 8 9 10) params members
    (M.prod_mem pairing unions powers separation hA hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.stageOneDataBoundEntryFormula 0 1 2 3 4 5 6 7 8 9 10) (extend z params))
      (ZFSet.prod A L) = stageOneDataBounds A I T S L mu X r anchors tuples := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, stageOneDataBounds, ZFSet.mem_sep,
      BoundedFormula.truth_stageOneDataBoundEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

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

theorem stageOneDataBounds_mono {L : Type u} [Preorder L] (b : Presentation L)
    {A I T S mu X anchors tuples v : ZFSet.{u}} {D E : L}
    (member : ZFSet.pair v (b.encode D) ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples) (le : D ≤ E) :
    ZFSet.pair v (b.encode E) ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples := by
  obtain ⟨hv,_,i,hi,u,hu,w,hw,anchor,hAnchor,fu,hfu,fw,hfw,equal,edge,below,tupleU,tupleW,boundU,boundW⟩ :=
    (pair_mem_stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples v (b.encode D)).1 member
  obtain ⟨anchor,rfl⟩ := (b.mem_carrier anchor).1 hAnchor
  exact (pair_mem_stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples v (b.encode E)).2
    ⟨hv,b.encode_mem E,i,hi,u,hu,w,hw,b.encode anchor,b.encode_mem anchor,fu,hfu,fw,hfw,equal,edge,
      (b.pair_mem_conditionOrder anchor E).2 (le_trans ((b.pair_mem_conditionOrder anchor D).1 below) le),
      tupleU,tupleW,boundU.mono b le,boundW.mono b le⟩

theorem stageOneDataBounds_total {L : Type u} [Preorder L] (b : Presentation L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    {A I T S mu X anchors tuples : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments I T) (anchorFunction : ZFSet.IsFunc I b.carrier anchors)
    (provenance : ∀ u ∈ T, ∃ f ∈ S, ZFSet.pair f u ∈ tuples)
    (positionBounds : ∀ f ∈ S, ∃ D : L, RowPositionBound mu X b.conditionOrder f (b.encode D)) :
    ∀ v ∈ A, ∃ D ∈ b.carrier, ZFSet.pair v D ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples := by
  intro v hv
  obtain ⟨i,hi,u,hu,w,hw,rfl⟩ := (mem_stageOneAssignments I T v).1 (subset hv)
  obtain ⟨anchor,edge,_⟩ := anchorFunction.2 i hi
  have hAnchor := (ZFSet.pair_mem_prod.1 (anchorFunction.1 edge)).2
  obtain ⟨anchor,rfl⟩ := (b.mem_carrier anchor).1 hAnchor
  obtain ⟨fu,hfu,tupleU⟩ := provenance u hu
  obtain ⟨fw,hfw,tupleW⟩ := provenance w hw
  obtain ⟨Du,boundU⟩ := positionBounds fu hfu
  obtain ⟨Dw,boundW⟩ := positionBounds fw hfw
  obtain ⟨middle,anchorBelow,uBelow⟩ := directed anchor Du
  obtain ⟨D,middleBelow,wBelow⟩ := directed middle Dw
  refine ⟨b.encode D,b.encode_mem D,?_⟩
  exact (stageOneDataBounds_assignment_entry A I T S b.carrier mu X b.conditionOrder anchors tuples
    i u w (b.encode D)).2
    ⟨hv,b.encode_mem D,hi,hu,hw,b.encode anchor,b.encode_mem anchor,fu,hfu,fw,hfw,edge,
      (b.pair_mem_conditionOrder anchor D).2 (le_trans anchorBelow middleBelow),tupleU,tupleW,
      boundU.mono b (le_trans uBelow middleBelow),boundW.mono b wBelow⟩

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



namespace PartitionPilot.Forcing

open SetRealization
universe u

theorem groundSequenceUnion_extends {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) (n : Nat) :
    SetMembers.raw (seq n) ⊆ groundSequenceUnion seq :=
  fun _ hz => (mem_groundSequenceUnion seq _).2 ⟨n, hz⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem descending_function_union_partial (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      Antitone seq → PartialFunctionCode X Y (groundSequenceUnion seq) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq decreasing
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq z).1 hz
    exact (M.smallFunction_raw_properties X Y ZFSet.omega (seq n)).2.1.shape hn
  · intro x y z xy xz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq _).1 xy
    obtain ⟨m, hm⟩ := (mem_groundSequenceUnion seq _).1 xz
    have code := (M.smallFunction_raw_properties X Y ZFSet.omega (seq (max n m))).2.1
    exact code.unique x y z
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_left n m)) hn)
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_right n m)) hm)

theorem descending_function_union_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        groundSequenceUnion seq ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  obtain ⟨ground, small⟩ := M.countable_union_of_sequence_graph pairing unions powers separation infinite choice
    hQ (M.prod_mem pairing unions powers separation hX hY) graph
    (natPresentation.graph_isFunc (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega))
      (fun n => seq n.down))
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.1.shape)
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.2)
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨ground, M.descending_function_union_partial X Y seq decreasing, small⟩

theorem countable_function_lower_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        ∃ p, SetMembers.raw p = groundSequenceUnion seq ∧ ∀ n, p ≤ seq n := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have member := M.descending_function_union_mem pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  let p := SetMembers.ofMem (groundSequenceUnion seq) member
  have raw : SetMembers.raw p = groundSequenceUnion seq := SetMembers.raw_ofMem _ _
  refine ⟨p, raw, fun n => (M.smallFunction_le_iff X Y ZFSet.omega p (seq n)).2 ?_⟩
  rw [raw]
  exact groundSequenceUnion_extends seq n

theorem countable_function_internally_closed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    InternallyCountablyClosed M (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  obtain ⟨p, _, lower⟩ := M.countable_function_lower_bound pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  exact ⟨p, lower⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowDistinguishing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem mem_rowCoordinateDomain (I C Y p x : ZFSet.{u}) :
    x ∈ rowCoordinateDomain I C Y p ↔
      x ∈ ZFSet.prod I C ∧ ∃ y ∈ Y, ZFSet.pair x y ∈ p := by
  rw [rowCoordinateDomain, mem_relationImage]
  constructor
  · rintro ⟨hx, z, hz, rel⟩
    obtain ⟨a, _, y, hy, eq⟩ := (mem_productFirst (ZFSet.prod I C) Y _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    refine ⟨hx, y, hy, ?_⟩
    rw [entries.2]
    exact entries.1 ▸ hz
  · rintro ⟨hx, y, hy, entry⟩
    exact ⟨hx, ZFSet.pair x y, entry,
      (mem_productFirst (ZFSet.prod I C) Y _).2 ⟨x, hx, y, hy, rfl⟩⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem rowCoordinateDomain_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) : rowCoordinateDomain I C Y p ∈ M.sets := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  exact M.relationImage_mem separation hp coordinates
    (M.productFirst_mem pairing unions powers separation coordinates hY)

theorem rowCoordinateDomain_groundEmbeddable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) : M.groundEmbeddable (rowCoordinateDomain I C Y p) N := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  exact M.groundEmbeddable_function_image pairing unions powers separation choice hp coordinates hN
    (M.productFirst_mem pairing unions powers separation coordinates hY)
    (productFirst_function (ZFSet.prod I C) Y) small

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBinaryRowNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem entry_binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u})
    (σ : Name (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name.Entry σ (M.binaryRowName I C one i) p ↔ ∃ c ∈ C,
      Name.check (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c = σ ∧
      ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈ SetMembers.raw p := by
  rw [binaryRowName, Name.entry_assemble]
  constructor
  · rintro ⟨z, eq, rfl⟩
    exact ⟨SetMembers.raw z.val.1, SetMembers.raw_mem z.val.1, eq, z.property⟩
  · rintro ⟨c, hc, eq, assigned⟩
    refine ⟨⟨(SetMembers.ofMem c hc, p), ?_⟩, ?_, rfl⟩
    · simpa only [SetMembers.raw_ofMem] using assigned
    · simpa only [SetMembers.raw_ofMem] using eq

theorem mem_binaryRowName_code (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i z : ZFSet.{u}) :
    z ∈ (M.binaryRowName I C one i).val ↔ ∃ c ∈ C,
      ∃ p ∈ M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega,
        z = ZFSet.pair (Name.check (SetMembers.presentation
          (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c).val p ∧
        ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈ p := by
  constructor
  · intro hz
    obtain ⟨σ, p, eq⟩ := Name.entries_cover (M.binaryRowName I C one i) hz
    change z = ZFSet.pair σ.val (SetMembers.raw p) at eq
    have entry : Name.Entry σ (M.binaryRowName I C one i) p := by
      change ZFSet.pair σ.val (SetMembers.raw p) ∈ (M.binaryRowName I C one i).val
      rw [← eq]
      exact hz
    obtain ⟨c, hc, child, assigned⟩ := (M.entry_binaryRowName I C one i σ p).1 entry
    refine ⟨c, hc, SetMembers.raw p, SetMembers.raw_mem p, ?_, assigned⟩
    rw [child]
    exact eq
  · rintro ⟨c, hc, p, hp, eq, assigned⟩
    have entry := (M.entry_binaryRowName I C one i _ (SetMembers.ofMem p hp)).2
      ⟨c, hc, rfl, by simpa only [SetMembers.raw_ofMem] using assigned⟩
    change ZFSet.pair (Name.check (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c).val
        (SetMembers.raw (SetMembers.ofMem p hp)) ∈ (M.binaryRowName I C one i).val at entry
    rw [SetMembers.raw_ofMem] at entry
    exact eq.symm ▸ entry

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBinaryRowNameCodes
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
variable (M : TransitiveGround.{u})

theorem realize_binaryRowEntryFormula (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hC : C ∈ M.sets)
    (hQ : M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega ∈ M.sets)
    (hi : i ∈ M.sets) (hbit : (natSetCode 1 : ZFSet.{u}) ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets (binaryRowEntryFormula 0 1 2 3 4 5)
      (extend z (extend C (extend
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
          (extend i (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))))) ↔
      z ∈ (M.binaryRowName I C one i).val := by
  let Q := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let s := SetMembers.presentation Q
  have hone : s.encode one ∈ M.sets := M.transitive hQ (SetMembers.raw_mem one)
  have children (c : ZFSet.{u}) (hc : c ∈ C) : (Name.check s one c).val ∈ M.sets :=
    M.check_mem s one pairing unions powers separation collection hone c (M.transitive hC hc)
  have assignment (c p w : ZFSet.{u}) (hc : c ∈ M.sets) (hp : p ∈ M.sets) (hw : w ∈ M.sets) :
      Realize M.sets (BoundedFormula.tripleMembershipFormula 6 2 8 1).toFormula
        (extend w (extend p (extend c (extend z (extend C (extend Q
          (extend i (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0))))))))) ↔
        ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈ p :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hw (Fin.cases hp (Fin.cases hc (Fin.cases hz (Fin.cases hC
        (Fin.cases hQ (Fin.cases hi (Fin.cases hone (Fin.cases hbit (fun j => Fin.elim0 j))))))))))).trans
      (BoundedFormula.truth_tripleMembershipFormula 6 2 8 1 _)
  rw [binaryRowEntryFormula, realize_ex]
  constructor
  · rintro ⟨c, hcM, rest⟩
    obtain ⟨p, hpM, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨w, hwM, hc, hp, checked, assigned, shape⟩ := (realize_ex M.sets _ _).1 rest
    rw [realize_binaryApplication, map_extend, map_empty] at checked
    have eq := (M.realize_uniformCheckFormula s one pairing unions powers separation collection
      hone c w hcM hwM).1 checked
    have pair := (M.realize_orderedPairFormula pairing 3 0 1 _ hz hwM hpM).1 shape
    apply (M.mem_binaryRowName_code I C one i z).2
    exact ⟨c, hc, p, hp,
      pair.trans (congrArg (fun v => ZFSet.pair v p) eq), (assignment c p w hcM hpM hwM).1 assigned⟩
  · intro member
    obtain ⟨c, hc, p, hp, shape, assigned⟩ := (M.mem_binaryRowName_code I C one i z).1 member
    have hcM := M.transitive hC hc
    have hpM := M.transitive hQ hp
    refine ⟨c, hcM, ?_⟩
    rw [realize_ex]
    refine ⟨p, hpM, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.check s one c).val, children c hc, hc, hp, ?_, ?_, ?_⟩
    · rw [realize_binaryApplication, map_extend, map_empty]
      exact (M.realize_uniformCheckFormula s one pairing unions powers separation collection
        hone c _ hcM (children c hc)).2 rfl
    · exact (assignment c p _ hcM hpM (children c hc)).2 assigned
    · exact (M.realize_orderedPairFormula pairing 3 0 1 _ hz (children c hc) hpM).2 shape

theorem binaryRowName_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u}) (hi : i ∈ M.sets) : (M.binaryRowName I C one i).val ∈ M.sets := by
  let Q := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let s := SetMembers.presentation Q
  have hQ : Q ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone : s.encode one ∈ M.sets := M.transitive hQ (SetMembers.raw_mem one)
  have hcheck := M.check_mem s one pairing unions powers separation collection hone C hC
  have childBound (c : ZFSet.{u}) (hc : c ∈ C) :
      (Name.check s one c).val ∈ ZFSet.sUnion (ZFSet.sUnion (Name.check s one C).val) :=
    Name.child_mem_doubleUnion ((Name.entry_check one C (Name.check s one c) one).2 ⟨c, hc, rfl, rfl⟩)
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers
    (M.union_mem unions (M.union_mem unions hcheck)) hQ
  have bound : (M.binaryRowName I C one i).val ⊆ B := by
    intro z hz
    obtain ⟨c, hc, p, hp, eq, _⟩ := (M.mem_binaryRowName_code I C one i z).1 hz
    exact eq.symm ▸ pairBound _ (childBound c hc) p hp
  let params := extend C (extend Q (extend i (extend (SetMembers.raw one)
    (extend (natSetCode 1) Fin.elim0))))
  have hbit := M.natSetCode_mem separation infinite 1
  have selected := M.separation_mem separation (binaryRowEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hC (Fin.cases hQ (Fin.cases hi (Fin.cases hone
      (Fin.cases hbit (fun j => Fin.elim0 j)))))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets (binaryRowEntryFormula 0 1 2 3 4 5)
      (extend z params)) B = (M.binaryRowName I C one i).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selected

theorem realize_binaryRowCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i w : ZFSet.{u}) (hi : i ∈ M.sets) (hw : w ∈ M.sets) :
    Realize M.sets binaryRowCodeFormula (extend i (extend w (extend C (extend
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
        (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))))) ↔
      w = (M.binaryRowName I C one i).val := by
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hname := M.binaryRowName_mem pairing unions powers separation collection infinite hI hC one i hi
  have hbit := M.natSetCode_mem separation infinite 1
  rw [binaryRowCodeFormula]
  constructor
  · intro spec
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      have hzM := M.transitive hw hz
      have rel := (realize_imp M.sets _ _ _).1 (spec z hzM).1 hz
      rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
        map_extend, map_empty] at rel
      exact (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z hzM).1 rel
    · intro hz
      have hzM := M.transitive hname hz
      apply (realize_imp M.sets _ _ _).1 (spec z hzM).2
      rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
        map_extend, map_empty]
      exact (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z hzM).2 hz
  · intro eq z hzM
    constructor
    · apply (realize_imp M.sets _ _ _).2
      intro hz
      rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
        map_extend, map_empty]
      exact (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z hzM).2 (eq ▸ hz)
    · apply (realize_imp M.sets _ _ _).2
      intro rel
      rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
        map_extend, map_empty] at rel
      exact eq.symm ▸ (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z hzM).1 rel

theorem exists_binaryRowName_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    ∃ W ∈ M.sets, ∀ i ∈ I, (M.binaryRowName I C one i).val ∈ W := by
  let Q := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  have hQ : Q ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone := M.transitive hQ (SetMembers.raw_mem one)
  let params := extend C (extend Q (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hC (Fin.cases hQ
    (Fin.cases hone (Fin.cases (M.natSetCode_mem separation infinite 1) (fun j => Fin.elim0 j))))
  have witnesses : ∀ i ∈ I, ∃ w ∈ M.sets,
      Realize M.sets binaryRowCodeFormula (extend i (extend w params)) := by
    intro i hi
    have hiM := M.transitive hI hi
    have hname := M.binaryRowName_mem pairing unions powers separation collection infinite hI hC one i hiM
    exact ⟨(M.binaryRowName I C one i).val, hname,
      (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
        hI hC one i _ hiM hname).2 rfl⟩
  obtain ⟨W, hW, covers⟩ := M.collection_witness collection binaryRowCodeFormula params members hI witnesses
  refine ⟨W, hW, ?_⟩
  intro i hi
  obtain ⟨w, hw, code⟩ := covers i hi
  have eq := (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
    hI hC one i w (M.transitive hI hi) (M.transitive hW hw)).1 code
  exact eq ▸ hw

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableRelationSelections
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation infinite choice

theorem exists_countableRelationSelection {A L R : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (hR : R ∈ M.sets)
    (smallA : M.groundEmbeddable A ZFSet.omega)
    (total : ∀ x ∈ A, ∃ y ∈ L, ZFSet.pair x y ∈ R) :
    ∃ f ∈ M.sets, ZFSet.IsFunc A L f ∧ f ⊆ R ∧
      relationImage A L f ∈ M.sets ∧ M.groundEmbeddable (relationImage A L f) ZFSet.omega := by
  obtain ⟨f,hf,function,selected⟩ := M.uniformize_relation pairing unions powers separation choice hA hL hR total
  exact ⟨f,hf,function,selected,M.relationImage_mem separation hA hL hf,
    M.groundEmbeddable_function_image pairing unions powers separation choice hA hL
      (M.omega_mem separation infinite) hf function smallA⟩

theorem exists_countableNodeSelection {A L R used extra : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (hR : R ∈ M.sets)
    (smallA : M.groundEmbeddable A ZFSet.omega)
    (total : ∀ x ∈ A, ∃ y ∈ L, ZFSet.pair x y ∈ R)
    (hUsed : used ∈ M.sets) (hExtra : extra ∈ M.sets)
    (usedSubset : used ⊆ L) (extraSubset : extra ⊆ L)
    (smallUsed : M.groundEmbeddable used ZFSet.omega)
    (smallExtra : M.groundEmbeddable extra ZFSet.omega) :
    ∃ f ∈ M.sets, ∃ W ∈ M.sets,
      ZFSet.IsFunc A L f ∧ f ⊆ R ∧
      W = (relationImage A L f ∪ used) ∪ extra ∧
      W ⊆ L ∧ M.groundEmbeddable W ZFSet.omega ∧
      (∀ x y, ZFSet.pair x y ∈ f → y ∈ W) ∧ used ⊆ W ∧ extra ⊆ W := by
  obtain ⟨f,hf,function,selected,hImage,smallImage⟩ :=
    M.exists_countableRelationSelection pairing unions powers separation infinite choice hA hL hR smallA total
  have hBoth := M.binary_union_mem pairing unions hImage hUsed
  have smallBoth := M.groundCountable_binary_union pairing unions powers separation infinite choice
    hImage hUsed smallImage smallUsed
  let W := (relationImage A L f ∪ used) ∪ extra
  have hW : W ∈ M.sets := M.binary_union_mem pairing unions hBoth hExtra
  have smallW : M.groundEmbeddable W ZFSet.omega :=
    M.groundCountable_binary_union pairing unions powers separation infinite choice hBoth hExtra smallBoth smallExtra
  refine ⟨f,hf,W,hW,function,selected,rfl,?_,smallW,?_,?_,?_⟩
  · intro y hy
    rcases ZFSet.mem_union.1 hy with both | additional
    · rcases ZFSet.mem_union.1 both with image | old
      · exact ((mem_relationImage A L f y).1 image).1
      · exact usedSubset old
    · exact extraSubset additional
  · intro x y entry
    have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inl
      ((mem_relationImage A L f y).2 ⟨bounds.2,x,bounds.1,entry⟩))))
  · intro y hy
    exact ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inr hy)))
  · intro y hy
    exact ZFSet.mem_union.2 (Or.inr hy)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCoinitialOperations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem mem_copyPullback (A L e F x : ZFSet.{u}) :
    x ∈ copyPullback A L e F ↔
      x ∈ A ∧ ∃ y ∈ F, y ∈ L ∧ ZFSet.pair x y ∈ e := by
  rw [copyPullback, mem_relationImage]
  constructor
  · rintro ⟨hx, y, hy, rel⟩
    exact ⟨hx, y, hy, ((pair_mem_relationConverse A L e x y).1 rel).2⟩
  · rintro ⟨hx, y, hy, hyL, rel⟩
    exact ⟨hx, y, hy, (pair_mem_relationConverse A L e x y).2 ⟨hx, hyL, rel⟩⟩

theorem relationImage_copyPullback {A L e : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e) (F : ZFSet.{u}) :
    relationImage (copyPullback A L e F) L e = F ∩ relationImage A L e := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, ZFSet.mem_inter, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, rel⟩
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    have equal : y = z := (unique y rel).trans (unique z relz).symm
    exact ⟨equal ▸ hz, hy, x, hxA, rel⟩
  · rintro ⟨hyF, hy, x, hx, rel⟩
    exact ⟨hy, x, (mem_copyPullback A L e F x).2 ⟨hx, y, hyF, hy, rel⟩, rel⟩

theorem CoinitialBelowCode.copy {A L e sourceOrder targetOrder F target B : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : CoinitialBelowCode sourceOrder (copyPullback A L e F) target B) :
    CoinitialBelowCode targetOrder F (relationImage target L e) (relationImage B L e) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage B L e y).1 hy
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 (basis.1 hx)
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    exact (unique y rel).trans (unique z relz).symm ▸ hz
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage target L e y).1 hy
    obtain ⟨b, hb, below⟩ := basis.2 x hx
    have hbA := ((mem_copyPullback A L e F b).1 (basis.1 hb)).1
    obtain ⟨b', relb, _⟩ := func.2 b hbA
    have hbL := (ZFSet.pair_mem_prod.1 (func.1 relb)).2
    exact ⟨b', (mem_relationImage B L e b').2 ⟨hbL, b, hb, relb⟩,
      monotone b x b' y below relb rel⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem copyPullback_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A L e F : ZFSet.{u}} (hA : A ∈ M.sets) (hL : L ∈ M.sets)
    (he : e ∈ M.sets) (hF : F ∈ M.sets) : copyPullback A L e F ∈ M.sets :=
  M.relationImage_mem separation hF hA
    (M.relationConverse_mem pairing unions powers separation hA hL he)

theorem internalCountableBelow_copy
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F target : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F) target) :
    M.InternalCountableBelow targetOrder F (relationImage target L e) := by
  obtain ⟨B, hB, small, coinitial⟩ := basis
  have subset : B ⊆ A := fun x hx => ((mem_copyPullback A L e F x).1 (coinitial.1 hx)).1
  exact ⟨relationImage B L e, M.relationImage_mem separation hB hL he,
    M.groundEmbeddable_image pairing unions powers separation hB hL
      (M.omega_mem separation infinite) he code subset small,
    coinitial.copy code.function monotone⟩

theorem internalCountableBelow_copy_pullback
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F)
      (copyPullback A L e F)) :
    M.InternalCountableBelow targetOrder F (F ∩ relationImage A L e) := by
  rw [← relationImage_copyPullback code.function F]
  exact M.internalCountableBelow_copy pairing unions powers separation infinite hL he code monotone basis

end TransitiveGround






theorem pair_mem_basisChoiceRelation (I W order target parts i B : ZFSet.{u}) :
    ZFSet.pair i B ∈ basisChoiceRelation I W order target parts ↔
      i ∈ I ∧ B ∈ W ∧ FiberCoveredCode order target parts i B := by
  rw [basisChoiceRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, A, hA, eq, covers⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hj, hA, covers⟩
  · rintro ⟨hi, hB, covers⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hB⟩, i, hi, B, hB, rfl, covers⟩

namespace BoundedFormula

open SetFormula

theorem truth_fiberCoveredFormula {n} (order target parts i B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fiberCoveredFormula order target parts i B) env ↔
      FiberCoveredCode (env order) (env target) (env parts) (env i) (env B) := by
  simp only [fiberCoveredFormula, Truth, truth_imp, truth_exMem, truth_pairMembershipFormula]
  rfl

theorem truth_basisChoiceEntryFormula {n} (z I W order target parts : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (basisChoiceEntryFormula z I W order target parts) env ↔
      ∃ i ∈ env I, ∃ B ∈ env W, env z = ZFSet.pair i B ∧
        FiberCoveredCode (env order) (env target) (env parts) i B := by
  simp only [basisChoiceEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_fiberCoveredFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem basisChoiceRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W order target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hW : W ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets) :
    basisChoiceRelation I W order target parts ∈ M.sets := by
  let params := extend I (extend W (extend order (extend target (extend parts Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hOrder (Fin.cases hTarget (Fin.cases hParts
      (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hI hW)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) (extend z params)) (ZFSet.prod I W) =
      basisChoiceRelation I W order target parts := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, basisChoiceRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_basisChoiceEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem internalCountableBelow_indexed_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I order F target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hOrder : order ∈ M.sets)
    (hF : F ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets)
    (smallI : M.groundEmbeddable I ZFSet.omega)
    (cover : ∀ x ∈ target, ∃ i ∈ I, ZFSet.pair i x ∈ parts)
    (localBases : ∀ i ∈ I, M.InternalCountableBelow order F (relationFiber target parts i)) :
    M.InternalCountableBelow order F target := by
  have hO := M.omega_mem separation infinite
  let W := M.groundSmallSubsets F ZFSet.omega
  have hW : W ∈ M.sets := M.groundSmallSubsets_mem powers separation hF hO
  have choices := M.basisChoiceRelation_mem pairing unions powers separation hI hW hOrder hTarget hParts
  have total (i : ZFSet.{u}) (hi : i ∈ I) :
      ∃ B ∈ W, ZFSet.pair i B ∈ basisChoiceRelation I W order target parts := by
    obtain ⟨B, hB, smallB, positive, below⟩ := localBases i hi
    have hBW : B ∈ W := (M.mem_groundSmallSubsets F ZFSet.omega B).2 ⟨hB, positive, smallB⟩
    exact ⟨B, hBW, (pair_mem_basisChoiceRelation I W order target parts i B).2
      ⟨hi, hBW, fun x hx rel => below x ((mem_relationFiber target parts i x).2 ⟨hx, rel⟩)⟩⟩
  obtain ⟨g, hg, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hI hW choices total
  let family := relationImage I W g
  have hFamily : family ∈ M.sets := M.relationImage_mem separation hI hW hg
  have smallFamily : M.groundEmbeddable family ZFSet.omega :=
    M.groundEmbeddable_function_image pairing unions powers separation choice hI hW hO hg func smallI
  have candidates (B : ZFSet.{u}) (hB : B ∈ family) : B ∈ W :=
    ((mem_relationImage I W g B).1 hB).1
  have smallBasis (B : ZFSet.{u}) (hB : B ∈ family) : M.groundEmbeddable B ZFSet.omega :=
    ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.2
  refine ⟨family.sUnion, M.union_mem unions hFamily,
    M.groundCountable_family_union pairing unions powers separation infinite choice
      hFamily smallFamily smallBasis, ?_, ?_⟩
  · intro x hx
    obtain ⟨B, hB, xB⟩ := ZFSet.mem_sUnion.1 hx
    exact ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.1 xB
  · intro x hx
    obtain ⟨i, hi, ix⟩ := cover x hx
    obtain ⟨B, chosen, _⟩ := func.2 i hi
    have spec := (pair_mem_basisChoiceRelation I W order target parts i B).1 (selected chosen)
    obtain ⟨b, hb, lower⟩ := spec.2.2 x hx ix
    have hB : B ∈ family := (mem_relationImage I W g B).2 ⟨spec.2.1, i, hi, chosen⟩
    exact ⟨b, ZFSet.mem_sUnion.2 ⟨B, hB, hb⟩, lower⟩

end TransitiveGround

end



namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem InternalCountableBelow.mono {order F target smaller : ZFSet.{u}}
    (basis : M.InternalCountableBelow order F target) (subset : smaller ⊆ target) :
    M.InternalCountableBelow order F smaller := by
  obtain ⟨B, hB, small, positive, below⟩ := basis
  exact ⟨B, hB, small, positive, fun x hx => below x (subset hx)⟩

theorem internalCountableBelow_empty (inhabited : M.sets.Nonempty) (order F : ZFSet.{u}) :
    M.InternalCountableBelow order F ∅ := by
  exact ⟨∅, M.empty_mem inhabited, M.empty_groundEmbeddable ZFSet.omega inhabited,
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx),
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx)⟩

theorem internalCountableBelow_of_countable {order F target : ZFSet.{u}}
    (hTarget : target ∈ M.sets) (small : M.groundEmbeddable target ZFSet.omega)
    (positive : target ⊆ F) (refl : ∀ x ∈ target, ZFSet.pair x x ∈ order) :
    M.InternalCountableBelow order F target :=
  ⟨target, hTarget, small, positive, fun x hx => ⟨x, hx, refl x hx⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologicalBasis
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem mem_birthEssentialSet (F T r birth x : ZFSet.{u}) :
    x ∈ birthEssentialSet F T r birth ↔ x ∈ F ∧
      ∀ y ∈ F, ∀ a ∈ T, ∀ b ∈ T,
        ZFSet.pair y x ∈ r → ZFSet.pair y a ∈ birth → ZFSet.pair x b ∈ birth → a ∉ b :=
  ZFSet.mem_sep

theorem birthEssentialSet_subset (F T r birth : ZFSet.{u}) :
    birthEssentialSet F T r birth ⊆ F := fun _ hx => (ZFSet.mem_sep.1 hx).1

theorem mem_essentialBirthIndices (F T r birth t : ZFSet.{u}) :
    t ∈ essentialBirthIndices F T r birth ↔ t ∈ T ∧
      ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair x t ∈ birth :=
  mem_relationImage _ _ _ _

theorem positive_above_birthEssential {L F T r birth : ZFSet.{u}}
    (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (refl : ∀ x ∈ L, ZFSet.pair x x ∈ r)
    (trans : ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
      ZFSet.pair x y ∈ r → ZFSet.pair y z ∈ r → ZFSet.pair x z ∈ r)
    {x : ZFSet.{u}} (positive : x ∈ F) :
    ∃ y ∈ birthEssentialSet F T r birth, ZFSet.pair y x ∈ r := by
  let S : Set ZFSet.{u} := {t | ∃ y ∈ F, ZFSet.pair y x ∈ r ∧ ZFSet.pair y t ∈ birth}
  obtain ⟨t, xt, _⟩ := born.2 x (subset positive)
  have inhabited : S.Nonempty := ⟨t, x, positive, refl x (subset positive), xt⟩
  obtain ⟨t, ⟨y, hy, below, yt⟩, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨y, (mem_birthEssentialSet F T r birth y).2 ⟨hy, ?_⟩, below⟩
  intro z hz a _ b _ zy za yb earlier
  obtain ⟨_, _, unique⟩ := born.2 y (subset hy)
  have eq : b = t := (unique b yb).trans (unique t yt).symm
  have aS : a ∈ S := ⟨z, hz, trans z (subset hz) y (subset hy) x (subset positive) zy below, za⟩
  exact minimal a aS (eq ▸ earlier)

namespace BoundedFormula

open SetFormula

theorem truth_birthEssentialFormula {n} (x f t r birth : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (birthEssentialFormula x f t r birth) env ↔
      ∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
        ZFSet.pair y (env x) ∈ env r → ZFSet.pair y a ∈ env birth →
          ZFSet.pair (env x) b ∈ env birth → a ∉ b := by
  simp only [birthEssentialFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change (∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
    ZFSet.pair y (env x) ∈ env r ∧ ZFSet.pair y a ∈ env birth ∧
      ZFSet.pair (env x) b ∈ env birth → a ∉ b) ↔ _
  constructor
  · intro h y hy a ha b hb below bornY bornX
    exact h y hy a ha b hb ⟨below, bornY, bornX⟩
  · intro h y hy a ha b hb premises
    exact h y hy a ha b hb premises.1 premises.2.1 premises.2.2

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem birthEssentialSet_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    birthEssentialSet F T r birth ∈ M.sets := by
  let params := extend F (extend T (extend r (extend birth Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.birthEssentialFormula 0 1 2 3 4) params
    (Fin.cases hF (Fin.cases hT (Fin.cases hr (Fin.cases hBirth (fun j => Fin.elim0 j))))) hF
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.birthEssentialFormula 0 1 2 3 4) (extend x params)) F =
      birthEssentialSet F T r birth := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_birthEssentialSet]
    exact and_congr Iff.rfl (BoundedFormula.truth_birthEssentialFormula 0 1 2 3 4 _)
  exact eq ▸ selected

theorem essentialBirthIndices_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    essentialBirthIndices F T r birth ∈ M.sets :=
  M.relationImage_mem separation (M.birthEssentialSet_mem separation hF hT hr hBirth) hT hBirth

theorem exists_essentialBirthRepresentatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    ∃ g ∈ M.sets,
      ZFSet.IsFunc (essentialBirthIndices F T r birth) (birthEssentialSet F T r birth) g ∧
      g ⊆ relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth ∧
      ∀ t ∈ essentialBirthIndices F T r birth,
        ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair t x ∈ g ∧ ZFSet.pair x t ∈ birth := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hConverse := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have total : ∀ t ∈ S, ∃ x ∈ E, ZFSet.pair t x ∈ relationConverse E S birth := by
    intro t ht
    obtain ⟨_, x, hx, born⟩ := (mem_essentialBirthIndices F T r birth t).1 ht
    exact ⟨x, hx, (pair_mem_relationConverse E S birth x t).2 ⟨hx, ht, born⟩⟩
  obtain ⟨g, hg, function, restricted⟩ :=
    M.uniformize_relation pairing unions powers separation choice hS hE hConverse total
  refine ⟨g, hg, function, restricted, ?_⟩
  intro t ht
  obtain ⟨x, chosen, _⟩ := function.2 t ht
  have spec := (pair_mem_relationConverse E S birth x t).1 (restricted chosen)
  exact ⟨x, spec.1, chosen, spec.2.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem internal_countable_basis_of_birth_layers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (order : PartialOrderCode L r) (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (small : M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    M.InternalCountableBelow r F F := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  let parts := relationConverse E S birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hParts : parts ∈ M.sets := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have cover (x : ZFSet.{u}) (hx : x ∈ E) : ∃ t ∈ S, ZFSet.pair t x ∈ parts := by
    obtain ⟨t, xt, _⟩ := born.2 x (subset (birthEssentialSet_subset F T r birth hx))
    have htT := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
    have htS : t ∈ S := (mem_essentialBirthIndices F T r birth t).2 ⟨htT, x, hx, xt⟩
    exact ⟨t, htS, (pair_mem_relationConverse E S birth x t).2 ⟨hx, htS, xt⟩⟩
  obtain ⟨B, hB, smallB, positive, below⟩ := M.internalCountableBelow_indexed_union
    pairing unions powers separation infinite choice hS hr hF hE hParts small cover localBases
  refine ⟨B, hB, smallB, positive, ?_⟩
  intro x hx
  obtain ⟨y, hy, yx⟩ := positive_above_birthEssential subset born order.refl order.trans hx
  obtain ⟨b, hb, byLower⟩ := below y hy
  exact ⟨b, hb, order.trans b (subset (positive hb)) y
    (subset (birthEssentialSet_subset F T r birth hy)) x (subset hx) byLower yx⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNaturalFamilyShift
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem mem_heightColumnFiber (S C Q h c i : ZFSet.{u}) :
    i ∈ heightColumnFiber S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ ∃ q ∈ Q, ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnFiber, mem_relationImage]
  constructor
  · rintro ⟨hi, v, hv, vi⟩
    obtain ⟨a, ha, q, hq, rfl⟩ := ZFSet.mem_prod.1 hv
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    have rel := (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).1 vi
    exact ⟨hi, (ZFSet.pair_mem_prod.1 rel.2.1).1, q, hq, rel.2.2⟩
  · rintro ⟨hi, hc, q, hq, iq⟩
    exact ⟨hi, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hq⟩,
      (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).2
        ⟨hi, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq⟩⟩

theorem pair_mem_heightColumnGraph (S C Q h c i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ heightColumnGraph S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ q ∈ Q ∧ ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨hi, hq, v, hv, iv, vq⟩
    obtain ⟨a, ha, b, _, eq⟩ := (mem_productSecond {c} Q (ZFSet.pair v q)).1 vq
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hi, (ZFSet.pair_mem_prod.1 hv).1, hq, iv⟩
  · rintro ⟨hi, hc, hq, iq⟩
    exact ⟨hi, hq, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq,
      (mem_productSecond {c} Q _).2 ⟨c, ZFSet.mem_singleton.2 rfl, q, hq, rfl⟩⟩

theorem heightColumnGraph_injection {S C Q h : ZFSet.{u}}
    (height : InjectionCode S (ZFSet.prod C Q) h) (c : ZFSet.{u}) :
    InjectionCode (heightColumnFiber S C Q h c) Q (heightColumnGraph S C Q h c) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have shape : z ∈ ZFSet.prod S Q := (ZFSet.mem_sep.1
      (show z ∈ relationCompose S (ZFSet.prod C Q) Q h (productSecond {c} Q) from hz)).1
    obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 shape
    obtain ⟨_, hc, _, iq⟩ := (pair_mem_heightColumnGraph S C Q h c i q).1 hz
    exact ZFSet.pair_mem_prod.2
      ⟨(mem_heightColumnFiber S C Q h c i).2 ⟨hi, hc, q, hq, iq⟩, hq⟩
  · intro i hi
    obtain ⟨hiS, hc, q, hq, iq⟩ := (mem_heightColumnFiber S C Q h c i).1 hi
    refine ⟨q, (pair_mem_heightColumnGraph S C Q h c i q).2 ⟨hiS, hc, hq, iq⟩, ?_⟩
    intro r ir
    have irh := (pair_mem_heightColumnGraph S C Q h c i r).1 ir
    obtain ⟨v, _, unique⟩ := height.function.2 i hiS
    exact (ZFSet.pair_inj.1 ((unique _ irh.2.2.2).trans (unique _ iq).symm)).2
  · intro i j q iq jq
    exact height.injective i j (ZFSet.pair c q)
      ((pair_mem_heightColumnGraph S C Q h c i q).1 iq).2.2.2
      ((pair_mem_heightColumnGraph S C Q h c j q).1 jq).2.2.2

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightColumnFiber_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnFiber S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationImage_mem separation
    (M.prod_mem pairing unions powers separation singleton hQ) hS
    (M.relationConverse_mem pairing unions powers separation hS
      (M.prod_mem pairing unions powers separation hC hQ) hh)

theorem heightColumnGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnGraph S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationCompose_mem pairing unions powers separation hS
    (M.prod_mem pairing unions powers separation hC hQ) hQ hh
    (M.productSecond_mem pairing unions powers separation singleton hQ)

theorem groundEmbeddable_heightColumnFiber
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c N : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) (hN : N ∈ M.sets)
    (height : InjectionCode S (ZFSet.prod C Q) h) (small : M.groundEmbeddable Q N) :
    M.groundEmbeddable (heightColumnFiber S C Q h c) N := by
  obtain ⟨f, hf, code⟩ := small
  exact ⟨relationCompose (heightColumnFiber S C Q h c) Q N (heightColumnGraph S C Q h c) f,
    M.relationCompose_mem pairing unions powers separation
      (M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh hc) hQ hN
      (M.heightColumnGraph_mem pairing unions powers separation hS hC hQ hh hc) hf,
    (heightColumnGraph_injection height c).compose code⟩

end TransitiveGround

end



section

open SetRealization
universe u

theorem ordinalSubset_has_least {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    {S : Set ZFSet.{u}} (subset : ∀ i ∈ S, i ∈ T) (inhabited : S.Nonempty) :
    ∃ i ∈ S, ∀ j ∈ S, i = j ∨ i ∈ j := by
  obtain ⟨i, hi, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨i, hi, ?_⟩
  intro j hj
  rcases ordinalSetProperty_mem_compare ordinal (subset i hi) (subset j hj) with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact False.elim (minimal j hj h)

theorem mem_ordinalIndexTail (S i j : ZFSet.{u}) :
    j ∈ ordinalIndexTail S i ↔ j ∈ S ∧ (i = j ∨ i ∈ j) := ZFSet.mem_sep

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem ordinalIndexTail_mem (separation : SeparationSchema M.sets)
    {S i : ZFSet.{u}} (hS : S ∈ M.sets) (hi : i ∈ M.sets) :
    ordinalIndexTail S i ∈ M.sets := by
  have selected := M.bounded_separation_mem separation (.disj (.equal 1 0) (.mem 1 0))
    (extend i Fin.elim0) (Fin.cases hi (fun j => Fin.elim0 j)) hS
  simpa only [BoundedFormula.truth_disj, BoundedFormula.Truth, extend, Fin.cases_zero,
    show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ, ordinalIndexTail] using selected

theorem groundCountable_descending_heights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S T C Q h : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (subset : S ⊆ T)
    (ordinal : ordinalSetProperty T) (height : InjectionCode S (ZFSet.prod C Q) h)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (antitone : ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d r,
      ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d r) ∈ h →
        d = c ∨ d ∈ c) :
    M.groundEmbeddable S ZFSet.omega := by
  classical
  have hOmega := M.omega_mem separation infinite
  have tails : ∀ c, ∀ i ∈ S, ∀ q, ZFSet.pair i (ZFSet.pair c q) ∈ h →
      M.groundEmbeddable (ordinalIndexTail S i) ZFSet.omega := by
    intro c
    induction c using ZFSet.inductionOn with
    | h c ih =>
      intro i hi q iq
      have hc := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iq)).2).1
      have groundTail := M.ordinalIndexTail_mem separation hS (M.transitive hS hi)
      have groundFiber := M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh
        (M.transitive hC hc)
      have smallFiber := M.groundEmbeddable_heightColumnFiber pairing unions powers separation
        hS hC hQ hh (M.transitive hC hc) hOmega height smallQ
      have columnBelow (k : ZFSet.{u}) (hk : k ∈ S) (later : i = k ∨ i ∈ k)
          (d r : ZFSet.{u}) (kr : ZFSet.pair k (ZFSet.pair d r) ∈ h) : d = c ∨ d ∈ c := by
        rcases later with rfl | later
        · obtain ⟨_, _, unique⟩ := height.function.2 i hi
          exact Or.inl (ZFSet.pair_inj.1 ((unique _ kr).trans (unique _ iq).symm)).1
        · exact antitone i hi k hk later c q d r iq kr
      let lower : Set ZFSet.{u} := {j | j ∈ S ∧ (i = j ∨ i ∈ j) ∧
        ∃ d r, d ∈ c ∧ ZFSet.pair j (ZFSet.pair d r) ∈ h}
      by_cases inhabited : lower.Nonempty
      · obtain ⟨j, hj, minimal⟩ := ordinalSubset_has_least ordinal
          (fun k hk => subset hk.1) inhabited
        obtain ⟨hjS, _, d, r, dc, jr⟩ := hj
        have smallLater := ih d dc j hjS r jr
        have smallUnion := M.groundCountable_binary_union pairing unions powers separation
          infinite choice groundFiber (M.ordinalIndexTail_mem separation hS (M.transitive hS hjS))
          smallFiber smallLater
        apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallUnion
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact ZFSet.mem_union.2 (Or.inl
            ((mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩))
        · have klower : k ∈ lower := ⟨hkS, later, e, s, less, kv⟩
          exact ZFSet.mem_union.2 (Or.inr
            ((mem_ordinalIndexTail S j k).2 ⟨hkS, minimal k klower⟩))
      · apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallFiber
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact (mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩
        · exact False.elim (inhabited ⟨k, hkS, later, e, s, less, kv⟩)
  by_cases inhabited : (S.toSet).Nonempty
  · obtain ⟨i, hi, minimal⟩ := ordinalSubset_has_least ordinal (fun _ hx => subset hx) inhabited
    obtain ⟨v, iv, _⟩ := height.function.2 i hi
    obtain ⟨c, _, q, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iv)).2
    exact M.groundEmbeddable_restrict separation hS hOmega
      (fun j hj => (mem_ordinalIndexTail S i j).2 ⟨hj, minimal j hj⟩) (tails c i hi q iv)
  · have empty : S = ∅ := by
      apply ZFSet.ext
      intro x
      exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
        fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    rw [empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨S, hS⟩

end TransitiveGround






theorem essentialHeightComposite_strict {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt)
    {i j c q d v : ZFSet.{u}} (earlier : i ∈ j)
    (first : ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
    (second : ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height) :
    d ∈ c ∨ (d = c ∧ ZFSet.pair v q ∈ qlt) := by
  obtain ⟨_, _, x, hx, ix, xheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
  obtain ⟨_, _, y, hy, jy, yheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
  have xi := (pair_mem_relationConverse E S birth x i).1 (representatives ix)
  have yj := (pair_mem_relationConverse E S birth y j).1 (representatives jy)
  exact descent x hx y hy i j c q d v xi.2.2 yj.2.2 earlier xheight yheight

theorem essentialHeightComposite_antitone {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt) :
    ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d v,
      ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
      ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
        d = c ∨ d ∈ c := by
  intro i _ j _ earlier c q d v first second
  exact (essentialHeightComposite_strict representatives descent earlier first second).elim
    Or.inr (fun h => Or.inl h.1)

theorem essentialHeightComposite_injection {L S T E C Q birth reps height qlt : ZFSet.{u}}
    (stages : S ⊆ T) (ordinal : ordinalSetProperty T)
    (representatives : ZFSet.IsFunc S E reps)
    (chosenBirths : reps ⊆ relationConverse E S birth)
    (points : E ⊆ L) (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent E birth height qlt) :
    InjectionCode S (ZFSet.prod C Q) (relationCompose S E (ZFSet.prod C Q) reps height) := by
  have function := relationCompose_function_of_subset representatives heights points
  refine ⟨function, ?_⟩
  intro i j z first second
  have iShape := ZFSet.pair_mem_prod.1 (function.1 first)
  have jShape := ZFSet.pair_mem_prod.1 (function.1 second)
  obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 iShape.2
  have notEarlier (a b : ZFSet.{u})
      (aHeight : ZFSet.pair a (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
      (bHeight : ZFSet.pair b (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height) : a ∉ b := by
    intro earlier
    rcases essentialHeightComposite_strict chosenBirths descent earlier aHeight bHeight with h | h
    · exact ZFSet.mem_irrefl c h
    · exact irreflexive q hq h.2
  have eqI := ordinalSetProperty_eq_code_rank i (ordinalSetProperty_member ordinal (stages iShape.1))
  have eqJ := ordinalSetProperty_eq_code_rank j (ordinalSetProperty_member ordinal (stages jShape.1))
  rcases lt_trichotomy (ZFSet.rank i) (ZFSet.rank j) with earlier | equal | later
  · have ij : i ∈ j := by rw [eqI, eqJ, mem_ordinalCode_iff]; exact earlier
    exact False.elim (notEarlier i j first second ij)
  · exact eqI.trans ((congrArg ordinalCode equal).trans eqJ.symm)
  · have ji : j ∈ i := by rw [eqJ, eqI, mem_ordinalCode_iff]; exact later
    exact False.elim (notEarlier j i second first ji)

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_essentialBirthHeights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    ∃ h ∈ M.sets,
      InjectionCode (essentialBirthIndices F T r birth) (ZFSet.prod C Q) h ∧
      (∀ i ∈ essentialBirthIndices F T r birth, ∀ j ∈ essentialBirthIndices F T r birth,
        i ∈ j → ∀ c q d v,
          ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d v) ∈ h →
            d = c ∨ d ∈ c) ∧
      ∀ i z, ZFSet.pair i z ∈ h → ∃ x ∈ birthEssentialSet F T r birth,
        ZFSet.pair x i ∈ birth ∧ ZFSet.pair x z ∈ height := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS := M.essentialBirthIndices_mem separation hF hT hr hBirth
  obtain ⟨reps, hReps, function, chosen, _⟩ :=
    M.exists_essentialBirthRepresentatives pairing unions powers separation choice hF hT hr hBirth
  let h := relationCompose S E (ZFSet.prod C Q) reps height
  have ground : h ∈ M.sets := M.relationCompose_mem pairing unions powers separation hS hE
    (M.prod_mem pairing unions powers separation hC hQ) hReps hHeight
  have subset : S ⊆ T := fun _ hi => (mem_essentialBirthIndices F T r birth _).1 hi |>.1
  have points : E ⊆ L := fun _ hx => positive (birthEssentialSet_subset F T r birth hx)
  refine ⟨h, ground, essentialHeightComposite_injection subset ordinal function chosen points heights
    irreflexive descent, essentialHeightComposite_antitone chosen descent, ?_⟩
  intro i z hiz
  obtain ⟨_, _, x, hx, ix, xz⟩ := (pair_mem_relationCompose S E (ZFSet.prod C Q) reps height i z).1 hiz
  exact ⟨x, hx, ((pair_mem_relationConverse E S birth x i).1 (chosen ix)).2.2, xz⟩

theorem essentialBirthIndices_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega := by
  obtain ⟨h, hh, injection, antitone, _⟩ := M.exists_essentialBirthHeights pairing unions powers
    separation choice hF hT hr hBirth hC hQ hHeight positive ordinal heights irreflexive descent
  exact M.groundCountable_descending_heights pairing unions powers separation infinite choice
    (M.essentialBirthIndices_mem separation hF hT hr hBirth) hC hQ hh
    (fun _ hi => ((mem_essentialBirthIndices F T r birth _).1 hi).1)
    ordinal injection smallQ antitone

end TransitiveGround

end



open SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageFromCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem birthEssential_below_earlier {L F T r μ birth x y a b : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (essential : x ∈ birthEssentialSet F T r birth) (positive : y ∈ F)
    (bornY : ZFSet.pair y a ∈ birth) (bornX : ZFSet.pair x b ∈ birth)
    (earlier : a ∈ b) : ZFSet.pair x y ∈ r ∧ x ≠ y := by
  classical
  have hx := (mem_birthEssentialSet F T r birth x).1 essential
  have xL := filter.subset hx.1
  have yL := filter.subset positive
  have bT := (ZFSet.pair_mem_prod.1 (born.1 bornX)).2
  have lower : ZFSet.pair x y ∈ r := by
    by_contra notLower
    obtain ⟨z, meetXY, _⟩ := meet.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨xL, yL⟩)
    have zL := (ZFSet.pair_mem_prod.1 (meet.operation.1 meetXY)).2
    obtain ⟨c, bornZ, _⟩ := born.2 z zL
    have cT := (ZFSet.pair_mem_prod.1 (born.1 bornZ)).2
    exact hx.2 z (filter.closed_meet x hx.1 y positive z meetXY) c cT b bT
      (meet.lower_left x y z meetXY) bornZ bornX
      (oldMeet x y z a b c bornY bornX earlier notLower meetXY bornZ)
  refine ⟨lower, ?_⟩
  intro equal
  subst y
  obtain ⟨t, _, unique⟩ := born.2 x xL
  have sameBirth : a = b := (unique a bornY).trans (unique b bornX).symm
  exact ZFSet.mem_irrefl b (sameBirth ▸ earlier)

theorem essentialHeightDescent_of_chronological_laws
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt) :
    EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt := by
  intro x hx y hy i j c q d v bornX bornY earlier heightX heightY
  have lower := birthEssential_below_earlier meet filter born oldMeet hy
    (birthEssentialSet_subset F T r birth hx) bornX bornY earlier
  exact strictHeight.strict y (filter.subset (birthEssentialSet_subset F T r birth hy))
    x (filter.subset (birthEssentialSet_subset F T r birth hx)) d v c q
    lower.1 lower.2 heightY heightX

end



section

universe u v

theorem mem_essentialBirthFiber (F T r birth t x : ZFSet.{u}) :
    x ∈ essentialBirthFiber F T r birth t ↔
      x ∈ birthEssentialSet F T r birth ∧ t ∈ T ∧ ZFSet.pair x t ∈ birth := by
  rw [essentialBirthFiber, mem_relationFiber, pair_mem_relationConverse]
  constructor
  · rintro ⟨hx, _, ht, born⟩
    exact ⟨hx, ((mem_essentialBirthIndices F T r birth t).1 ht).1, born⟩
  · rintro ⟨hx, ht, born⟩
    exact ⟨hx, hx, (mem_essentialBirthIndices F T r birth t).2 ⟨ht, x, hx, born⟩, born⟩

theorem essentialBirthFiber_subset (F T r birth t : ZFSet.{u}) :
    essentialBirthFiber F T r birth t ⊆ birthEssentialSet F T r birth :=
  fun _ hx => ((mem_essentialBirthFiber F T r birth t _).1 hx).1

theorem birthEssentials_no_oldBridge {L F T r μ birth t x y : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (hx : x ∈ birthEssentialSet F T r birth) (hy : y ∈ birthEssentialSet F T r birth)
    (xt : ZFSet.pair x t ∈ birth) (yt : ZFSet.pair y t ∈ birth) :
    ¬ OldBridgeCode L r μ birth t x y := by
  have xE := (mem_birthEssentialSet F T r birth x).1 hx
  have yE := (mem_birthEssentialSet F T r birth y).1 hy
  have ht := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
  intro bridge
  rcases bridge with ⟨z, a, meetXY, za, old⟩ | ⟨z, hz, a, za, old, intermediate⟩
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    exact xE.2 z (filter.closed_meet x xE.1 y yE.1 z meetXY) a ha t ht
      (meet.lower_left x y z meetXY) za xt old
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    rcases intermediate with ⟨xz, zy⟩ | ⟨yz, zx⟩
    · exact yE.2 z (filter.upward x xE.1 z hz xz) a ha t ht zy za yt old
    · exact xE.2 z (filter.upward y yE.1 z hz yz) a ha t ht zx za xt old

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem essentialBirthFiber_mem (separation : SeparationSchema M.sets)
    {F T r birth t : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) (ht : t ∈ M.sets) :
    essentialBirthFiber F T r birth t ∈ M.sets := by
  let E := birthEssentialSet F T r birth
  let params := extend t (extend T (extend birth Fin.elim0))
  let φ : BoundedFormula 4 := .conj (.mem 1 2) (BoundedFormula.pairMembershipFormula 0 1 3)
  have selected := M.bounded_separation_mem separation φ params
    (Fin.cases ht (Fin.cases hT (Fin.cases hBirth (fun j => Fin.elim0 j))))
    (M.birthEssentialSet_mem separation hF hT hr hBirth)
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth φ (extend x params)) E =
      essentialBirthFiber F T r birth t := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_essentialBirthFiber]
    exact and_congr Iff.rfl
      (and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 0 1 3 _))
  exact eq ▸ selected

end TransitiveGround

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFilterCopies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem meetFilter_copyPullback {A L rA rL μA μL e F : ZFSet.{u}}
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (nonempty : (copyPullback A L e F).Nonempty) :
    MeetFilterCode A rA μA (copyPullback A L e F) where
  subset := fun x hx => ((mem_copyPullback A L e F x).1 hx).1
  nonempty := nonempty
  upward := by
    intro x hx y hy lower
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨y', yy', _⟩ := embedding.injection.function.2 y hy
    have hyL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 yy')).2
    have hyF := target.upward x' hxF y' hyL (embedding.monotone x y x' y' lower xx' yy')
    exact (mem_copyPullback A L e F y).2 ⟨hy, y', hyF, hyL, yy'⟩
  closed_meet := by
    intro x hx y hy z meetXY
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨_, y', hyF, _, yy'⟩ := (mem_copyPullback A L e F y).1 hy
    have hzA := (ZFSet.pair_mem_prod.1 (source.operation.1 meetXY)).2
    obtain ⟨z', zz', _⟩ := embedding.injection.function.2 z hzA
    have hzL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 zz')).2
    have hzF := target.closed_meet x' hxF y' hyF z'
      (embedding.map_meet x y z x' y' z' meetXY xx' yy' zz')
    exact (mem_copyPullback A L e F z).2 ⟨hzA, z', hzF, hzL, zz'⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem internalCountableBelow_copy_of_all_filters
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L rA rL μA μL e F : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (he : e ∈ M.sets) (hF : F ∈ M.sets)
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (earlier : ∀ P ∈ M.sets, MeetFilterCode A rA μA P → M.InternalCountableBelow rA P P) :
    M.InternalCountableBelow rL F (F ∩ relationImage A L e) := by
  classical
  by_cases nonempty : (copyPullback A L e F).Nonempty
  · have pullbackMember := M.copyPullback_mem pairing unions powers separation hA hL he hF
    have pullbackFilter := meetFilter_copyPullback source target embedding nonempty
    exact M.internalCountableBelow_copy_pullback pairing unions powers separation infinite hL he
      embedding.injection embedding.monotone
      (earlier (copyPullback A L e F) pullbackMember pullbackFilter)
  · refine ⟨∅, M.empty_mem ⟨F, hF⟩, M.empty_groundEmbeddable ZFSet.omega ⟨F, hF⟩,
      ZFSet.empty_subset F, ?_⟩
    intro x hx
    obtain ⟨hxF, image⟩ := ZFSet.mem_inter.1 hx
    obtain ⟨hxL, y, hyA, yx⟩ := (mem_relationImage A L e x).1 image
    exact False.elim (nonempty ⟨y,
      (mem_copyPullback A L e F y).2 ⟨hyA, x, hxF, hxL, yx⟩⟩)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOutsideRowNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

universe u

theorem mem_rowUsedRows (I C Y p i : ZFSet.{u}) :
    i ∈ rowUsedRows I C Y p ↔
      i ∈ I ∧ ∃ c ∈ C, ∃ y ∈ Y, ZFSet.pair (ZFSet.pair i c) y ∈ p := by
  rw [rowUsedRows, mem_relationImage]
  constructor
  · rintro ⟨hi, x, hx, rel⟩
    obtain ⟨j, _, c, hc, eq⟩ := (mem_productFirst I C _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    obtain ⟨_, y, hy, entry⟩ := (mem_rowCoordinateDomain I C Y p x).1 hx
    rw [entries.1, ← entries.2] at entry
    exact ⟨hi, c, hc, y, hy, entry⟩
  · rintro ⟨hi, c, hc, y, hy, entry⟩
    exact ⟨hi, ZFSet.pair i c,
      (mem_rowCoordinateDomain I C Y p _).2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hc⟩, y, hy, entry⟩,
      (mem_productFirst I C _).2 ⟨i, hi, c, hc, rfl⟩⟩

theorem rowUsedRows_subset (I C Y p : ZFSet.{u}) : rowUsedRows I C Y p ⊆ I :=
  fun i hi => ((mem_rowUsedRows I C Y p i).1 hi).1

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem rowUsedRows_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) : rowUsedRows I C Y p ∈ M.sets :=
  M.relationImage_mem separation
    (M.rowCoordinateDomain_mem pairing unions powers separation hI hC hY hp) hI
    (M.productFirst_mem pairing unions powers separation hI hC)

theorem rowUsedRows_groundEmbeddable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) : M.groundEmbeddable (rowUsedRows I C Y p) N :=
  M.groundEmbeddable_function_image pairing unions powers separation choice
    (M.rowCoordinateDomain_mem pairing unions powers separation hI hC hY hp) hI hN
    (M.productFirst_mem pairing unions powers separation hI hC) (productFirst_function I C)
    (M.rowCoordinateDomain_groundEmbeddable pairing unions powers separation choice hI hC hY hp hN small)

theorem countablePartialFunctions_rowSupport
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hp : p ∈ M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega) :
    rowUsedRows I C Y p ∈ M.sets ∧ M.groundEmbeddable (rowUsedRows I C Y p) ZFSet.omega := by
  obtain ⟨ground, _, small⟩ := (M.mem_smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega p).1 hp
  exact ⟨M.rowUsedRows_mem pairing unions powers separation hI hC hY ground,
    M.rowUsedRows_groundEmbeddable pairing unions powers separation choice
      hI hC hY ground (M.omega_mem separation infinite) small⟩

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundOrdinalPartitionInjectionAssembly
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pair_mem_definableRelation {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A B x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.definableRelation φ params A B ↔
      x ∈ A ∧ y ∈ B ∧ Realize M.sets φ (extend x (extend y params)) := by
  rw [definableRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, equal, relation⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, relation⟩
  · rintro ⟨hx, hy, relation⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, relation⟩

theorem realize_definableRelationEntryFormula {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets (definableRelationEntryFormula φ) (extend z (extend A (extend B params))) ↔
      ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair x y ∧ Realize M.sets φ (extend x (extend y params)) := by
  simp only [definableRelationEntryFormula, realize_ex, Realize]
  constructor
  · rintro ⟨x, hx, inA, y, hy, inB, pair, relation⟩
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hy (Fin.cases hx (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    have exactPair := (BoundedFormula.truth_orderedPairFormula 2 1 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ ground).1 pair)
    exact ⟨x, inA, y, inB, exactPair, (realize_binaryApplication M.sets φ _ _ _ _).1 relation⟩
  · rintro ⟨x, hx, y, hy, pair, relation⟩
    have hxM := M.transitive hA hx
    have hyM := M.transitive hB hy
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases hxM (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    exact ⟨x, hxM, hx, y, hyM, hy,
      (BoundedFormula.realize_toFormula M _ _ ground).2
        ((BoundedFormula.truth_orderedPairFormula 2 1 0 _).2 pair),
      (realize_binaryApplication M.sets φ _ _ _ _).2 relation⟩

theorem definableRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    M.definableRelation φ params A B ∈ M.sets := by
  have hProd := M.prod_mem pairing unions powers separation hA hB
  have selected := M.separation_mem separation (definableRelationEntryFormula φ)
    (extend A (extend B params)) (Fin.cases hA (Fin.cases hB members)) hProd
  have equal : ZFSet.sep (fun z => Realize M.sets (definableRelationEntryFormula φ)
      (extend z (extend A (extend B params)))) (ZFSet.prod A B) = M.definableRelation φ params A B := by
    apply ZFSet.ext
    intro z
    rw [definableRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_definableRelationEntryFormula φ params members hA hB z (M.transitive hProd hz)
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSelectedSupportTupleFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (z : ZFSet.{u}) : z ∈ M.binaryRowNameGraph I C one ↔
      ∃ i ∈ I, z = ZFSet.pair i (M.binaryRowName I C one i).val := by
  rw [binaryRowNameGraph, ZFSet.mem_range]
  exact ⟨fun ⟨i, eq⟩ => ⟨i.val, i.property, eq.symm⟩,
    fun ⟨i, hi, eq⟩ => ⟨⟨i, hi⟩, eq.symm⟩⟩

theorem pair_mem_binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i x : ZFSet.{u}) : ZFSet.pair i x ∈ M.binaryRowNameGraph I C one ↔
      i ∈ I ∧ x = (M.binaryRowName I C one i).val := by
  rw [M.mem_binaryRowNameGraph I C one]
  constructor
  · rintro ⟨j, hj, eq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem binaryRowNameGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    M.binaryRowNameGraph I C one ∈ M.sets := by
  obtain ⟨W, hW, bounds⟩ := M.exists_binaryRowName_bound pairing unions powers separation collection infinite hI hC one
  let Q := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  have hQ : Q ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  let params := extend C (extend Q (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hC (Fin.cases hQ
    (Fin.cases (M.transitive hQ (SetMembers.raw_mem one))
      (Fin.cases (M.natSetCode_mem separation infinite 1) (fun j => Fin.elim0 j))))
  have grounded := M.definableRelation_mem pairing unions powers separation binaryRowCodeFormula params members hI hW
  have equal : M.definableRelation binaryRowCodeFormula params I W = M.binaryRowNameGraph I C one := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨i, hi, x, hx, rfl, formula⟩ := (ZFSet.mem_sep.1 hz).2
      have eq := (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
        hI hC one i x (M.transitive hI hi) (M.transitive hW hx)).1 formula
      exact (M.pair_mem_binaryRowNameGraph I C one i x).2 ⟨hi, eq⟩
    · intro hz
      obtain ⟨i, hi, rfl⟩ := (M.mem_binaryRowNameGraph I C one z).1 hz
      exact (M.pair_mem_definableRelation binaryRowCodeFormula params I W i _).2
        ⟨hi, bounds i hi, (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
          hI hC one i _ (M.transitive hI hi) (M.transitive hW (bounds i hi))).2 rfl⟩
  exact equal ▸ grounded

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem pair_mem_rowTupleFamily (one mu I W rows S f z : ZFSet.{u}) :
    ZFSet.pair f z ∈ rowTupleFamily one mu I W rows S ↔
      f ∈ S ∧ z = rowTupleCode one mu I W rows f := by
  rw [rowTupleFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨g, eq⟩
    obtain ⟨input, output⟩ := ZFSet.pair_inj.1 eq
    exact ⟨input ▸ g.property, output.symm.trans (congrArg (rowTupleCode one mu I W rows) input)⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem rowTupleFamily_mem {one mu I W rows S : ZFSet.{u}}
    (hone : one ∈ M.sets) (hmu : mu ∈ M.sets) (hI : I ∈ M.sets)
    (hW : W ∈ M.sets) (hrows : rows ∈ M.sets) (hS : S ∈ M.sets) :
    rowTupleFamily one mu I W rows S ∈ M.sets :=
  (M.definable_rowTupleCode pairing unions powers separation collection).graph_mem pairing separation collection
    (extend one (extend mu (extend I (extend W (extend rows Fin.elim0)))))
    (Fin.cases hone (Fin.cases hmu (Fin.cases hI (Fin.cases hW
      (Fin.cases hrows (fun j => Fin.elim0 j)))))) hS

end TransitiveGround





end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem mem_rowTupleTerms (one mu I W rows S z : ZFSet.{u}) :
    z ∈ rowTupleTerms one mu I W rows S ↔
      ∃ f ∈ S, z = rowTupleCode one mu I W rows f := by
  rw [rowTupleTerms, mem_functionGraphRange]
  constructor
  · rintro ⟨f, hf, entry⟩
    exact ⟨f, hf, ((pair_mem_rowTupleFamily one mu I W rows S f z).1 entry).2⟩
  · rintro ⟨f, hf, equal⟩
    exact ⟨f, hf, (pair_mem_rowTupleFamily one mu I W rows S f z).2 ⟨hf, equal⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowTupleTerms_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {one mu I W rows S : ZFSet.{u}} (hS : S ∈ M.sets)
    (family : rowTupleFamily one mu I W rows S ∈ M.sets) :
    rowTupleTerms one mu I W rows S ∈ M.sets :=
  M.functionGraphRange_mem unions separation hS family

end TransitiveGround

end PartitionPilot.Forcing



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

theorem renamedFamily_mem (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ x ∈ T, IsName s x) :
    Name.renamedFamily t f T valid ∈ M.sets :=
  M.functionGraphRange_mem unions separation hT
    (M.renameFamilyGraph_mem s t pairing unions powers separation collection hs ht f hf T hT valid)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {P : Type u} (s : Presentation P)

theorem pairEmpty_forwardGraph :
    s.graph s.pairEmpty id = pairedGraph s.carrier s.carrier {∅}
      (identityFunctionGraph s.carrier) (constantFamilyGraph s.carrier ∅) := by
  apply ZFSet.ext
  intro z
  rw [s.mem_graph, mem_pairedGraph]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨s.encode p, s.encode_mem p, s.encode p, s.encode_mem p,
      ∅, ZFSet.mem_singleton.2 rfl, rfl,
      (pair_mem_identityFunctionGraph _ _ _).2 ⟨rfl, s.encode_mem p⟩,
      (pair_mem_constantFamilyGraph _ _ _ _).2 ⟨s.encode_mem p, rfl⟩⟩
  · rintro ⟨x, hx, y, _, e, _, rfl, identity, constant⟩
    have xy := ((pair_mem_identityFunctionGraph _ _ _).1 identity).1
    have empty := ((pair_mem_constantFamilyGraph _ _ _ _).1 constant).2
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    subst y
    subst e
    exact ⟨p, rfl⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {P : Type u} (s : Presentation P)
include pairing unions powers separation

theorem pairEmpty_carrier_mem (hs : s.carrier ∈ M.sets) : s.pairEmpty.carrier ∈ M.sets := by
  have empty := M.empty_mem ⟨s.carrier, hs⟩
  have single : ({∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing empty empty
  exact M.prod_mem pairing unions powers separation hs single

theorem pairEmpty_forwardGraph_mem (hs : s.carrier ∈ M.sets) : s.graph s.pairEmpty id ∈ M.sets := by
  rw [s.pairEmpty_forwardGraph]
  have empty := M.empty_mem ⟨s.carrier, hs⟩
  have single : ({∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing empty empty
  exact M.pairedGraph_mem pairing unions powers separation hs hs single
    (M.identityFunctionGraph_mem pairing unions powers separation hs)
    (M.constantFamilyGraph_mem pairing unions powers separation hs empty)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {P : Type u} (c : Presentation P)
variable (one mu I W rows S : ZFSet.{u})
variable (valid : ∀ z ∈ (rowTupleTerms one mu I W rows S), IsName c z)

include valid

theorem pair_mem_liftedRowTupleFamily (f z : ZFSet.{u}) :
    ZFSet.pair f z ∈ (liftedRowTupleFamily c one mu I W rows S valid) ↔
      f ∈ S ∧ ∃ τ : Name c, τ.val = rowTupleCode one mu I W rows f ∧
        z = (Name.rename c.pairEmpty id τ).val := by
  rw [liftedRowTupleFamily, pair_mem_relationCompose]
  constructor
  · rintro ⟨hf, _, x, hx, tuple, rename⟩
    let τ : Name c := ⟨x, valid x hx⟩
    exact ⟨hf, τ, ((pair_mem_rowTupleFamily one mu I W rows S f x).1 tuple).2,
      ((Name.pair_mem_renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid τ z).1 rename).2⟩
  · rintro ⟨hf, τ, tuple, equal⟩
    have member : τ.val ∈ (rowTupleTerms one mu I W rows S) := (mem_rowTupleTerms one mu I W rows S τ.val).2 ⟨f, hf, tuple⟩
    have target : z ∈ (Name.renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid) := (Name.mem_renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid z).2
      ⟨τ, member, equal⟩
    exact ⟨hf, target, τ.val, member,
      (pair_mem_rowTupleFamily one mu I W rows S f τ.val).2 ⟨hf, tuple⟩,
      (Name.pair_mem_renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid τ z).2 ⟨member, equal⟩⟩

theorem liftedRowTupleFamily_surjective :
    ∀ z ∈ (Name.renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid), ∃ f ∈ S, ZFSet.pair f z ∈ (liftedRowTupleFamily c one mu I W rows S valid) := by
  intro z hz
  obtain ⟨τ, member, equal⟩ := (Name.mem_renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid z).1 hz
  obtain ⟨f, hf, tuple⟩ := (mem_rowTupleTerms one mu I W rows S τ.val).1 member
  exact ⟨f, hf, (pair_mem_liftedRowTupleFamily c one mu I W rows S valid f z).2
    ⟨hf, τ, tuple, equal⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem liftedRowTupleFamily_mem (carrier : c.carrier ∈ M.sets)
    (hone : one ∈ M.sets) (hmu : mu ∈ M.sets) (hI : I ∈ M.sets)
    (hW : W ∈ M.sets) (hrows : rows ∈ M.sets) (hS : S ∈ M.sets) :
    (liftedRowTupleFamily c one mu I W rows S valid) ∈ M.sets := by
  have tuples := M.rowTupleFamily_mem pairing unions powers separation collection hone hmu hI hW hrows hS
  have terms := M.rowTupleTerms_mem unions separation hS tuples
  have target := M.pairEmpty_carrier_mem pairing unions powers separation c carrier
  have forward := M.pairEmpty_forwardGraph_mem pairing unions powers separation c carrier
  have rename := M.renameFamilyGraph_mem c c.pairEmpty pairing unions powers separation collection
    carrier target id forward (rowTupleTerms one mu I W rows S) terms valid
  have liftedGround := M.renamedFamily_mem c c.pairEmpty pairing unions powers separation collection
    carrier target id forward (rowTupleTerms one mu I W rows S) terms valid
  exact M.relationCompose_mem pairing unions powers separation hS terms liftedGround tuples rename

omit c one mu I W rows S valid in
theorem binaryLiftedRowTupleFamily_mem (infinite : Realize M.sets infinity Fin.elim0)
    {L r I C mu : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph I C one
    let S := M.rowPositionSequences L r I mu
    ∀ valid : ∀ z ∈ rowTupleTerms (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S, IsName c z,
      liftedRowTupleFamily c (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S valid ∈ M.sets := by
  intro c rows S valid
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have groundRows := M.binaryRowNameGraph_mem pairing unions powers separation collection infinite hI hC one
  exact liftedRowTupleFamily_mem c (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S valid M
    pairing unions powers separation collection carrier (M.transitive carrier (SetMembers.raw_mem one))
    hmu hI (M.union_mem unions (M.union_mem unions groundRows)) groundRows
    (M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GrowthLayerSourceCongruence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

namespace CodedGrowthLayer

open SetFormula

theorem internal_countable_essentials
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L F T r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hL : L ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (ht : t ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (earlier : ∀ s ∈ t, Space s ∈ M.sets ∧
      MeetOrderCode (Space s) (sourceOrder s) (sourceMeet s) ∧
      ∀ P ∈ M.sets, MeetFilterCode (Space s) (sourceOrder s) (sourceMeet s) P →
        M.InternalCountableBelow (sourceOrder s) P P) :
    M.InternalCountableBelow r F (essentialBirthFiber F T r birth t) := by
  classical
  have groundFiber := M.essentialBirthFiber_mem separation hF hT hr hBirth ht
  have positive : essentialBirthFiber F T r birth t ⊆ F :=
    fun _ hx => birthEssentialSet_subset F T r birth
      (essentialBirthFiber_subset F T r birth t hx)
  have points : essentialBirthFiber F T r birth t ⊆ L := fun _ hx => filter.subset (positive hx)
  cases layer with
  | countablePoints D _ small cover =>
    have subset : essentialBirthFiber F T r birth t ⊆ D := by
      intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    have countableFiber := M.groundEmbeddable_restrict separation groundFiber
      (M.omega_mem separation infinite) subset small
    exact M.internalCountableBelow_of_countable groundFiber countableFiber positive
      (fun x hx => meet.order.refl x (points hx))
  | copies I parts groundI small groundParts index e previous groundCopy embedding cover inCopy =>
    apply M.internalCountableBelow_indexed_union pairing unions powers separation infinite choice
      groundI hr hF groundFiber groundParts small
    · intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    · intro i hi
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i hi)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i hi) hF source filter (embedding i hi) sourceBases
      apply basis.mono
      intro x hx
      obtain ⟨hxFiber, part⟩ := (mem_relationFiber (essentialBirthFiber F T r birth t) parts i x).1 hx
      exact ZFSet.mem_inter.2 ⟨positive hxFiber, inCopy i hi x (points hxFiber) part⟩
  | separated I index e previous groundCopy embedding component cover separated =>
    by_cases inhabited : (essentialBirthFiber F T r birth t).Nonempty
    · obtain ⟨x, hx⟩ := inhabited
      let representative : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨x, points hx, ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2⟩
      let i := component representative
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i) hF source filter (embedding i) sourceBases
      apply basis.mono
      intro y hy
      let current : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨y, points hy, ((mem_essentialBirthFiber F T r birth t y).1 hy).2.2⟩
      have same : component current = i := by
        by_contra different
        exact birthEssentials_no_oldBridge meet filter born
          (essentialBirthFiber_subset F T r birth t hy)
          (essentialBirthFiber_subset F T r birth t hx)
          current.property.2 representative.property.2 (separated current representative different)
      have inside := cover current
      rw [same] at inside
      exact ZFSet.mem_inter.2 ⟨positive hy, inside⟩
    · have empty : essentialBirthFiber F T r birth t = ∅ := by
        apply ZFSet.ext
        intro x
        exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
          fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
      rw [empty]
      exact M.internalCountableBelow_empty ⟨F, hF⟩ r F

end CodedGrowthLayer

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GeneratedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot
universe u
variable {α : Type u} (P : MeetOrder α) (A : α → Prop)

theorem generatedMeetPredicate_least (F : Compression.MeetFilter P)
    (contains : ∀ a, A a → F.mem a) {x : α} (hx : generatedMeetPredicate P A x) : F.mem x := by
  obtain ⟨a, ha, b, path, lower⟩ := hx
  have hb : F.mem b := by
    clear lower
    induction path with
    | refl => exact contains a ha
    | tail path step ih =>
      obtain ⟨c, hc, rfl⟩ := step
      exact F.closed_meet ih (contains c hc)
  exact F.upward hb lower

end PartitionPilot

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMeetGeneratorSteps
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

theorem pair_mem_meetGeneratorSteps (P μ A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ meetGeneratorSteps P μ A ↔
      x ∈ P ∧ y ∈ P ∧ ∃ a ∈ A, ZFSet.pair (ZFSet.pair x a) y ∈ μ := by
  rw [meetGeneratorSteps, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, y', hy, a, ha, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hy, a, ha, entry⟩
  · rintro ⟨hx, hy, a, ha, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, a, ha, rfl, entry⟩

theorem MeetOrderCode.meetGeneratorSteps_iff {P r μ A : ZFSet.{u}}
    (code : MeetOrderCode P r μ) (subset : A ⊆ P) (x y : SetMembers P) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ meetGeneratorSteps P μ A ↔
      meetGeneratorStep code.toSmallMeetOrder (fun a => SetMembers.raw a ∈ A) x y := by
  rw [pair_mem_meetGeneratorSteps]
  constructor
  · rintro ⟨_, _, a, ha, entry⟩
    refine ⟨SetMembers.ofMem a (subset ha), ?_, ?_⟩
    · simpa only [SetMembers.raw_ofMem] using ha
    · apply Eq.symm
      apply (code.toSmallMeetOrder_meet_eq_iff _ _ _).2
      simpa only [SetMembers.raw_ofMem] using entry
  · rintro ⟨a, ha, equal⟩
    exact ⟨SetMembers.raw_mem x, SetMembers.raw_mem y, SetMembers.raw a, ha,
      (code.toSmallMeetOrder_meet_eq_iff _ _ _).1 equal.symm⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundTestedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions separation infinite

theorem generatedMeetFilter_small_iff {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) (x : SetMembers P) :
    SetMembers.raw x ∈ M.generatedMeetFilter P r μ A ↔
      generatedMeetPredicate code.toSmallMeetOrder (fun a => SetMembers.raw a ∈ A) x := by
  have paths := M.pair_mem_finitePathClosure pairing unions separation infinite
    (SetMembers.presentation P) (meetGeneratorStep code.toSmallMeetOrder
      (fun a => SetMembers.raw a ∈ A)) (code.meetGeneratorSteps_iff subset) hP
  rw [generatedMeetFilter, mem_relationImage]
  constructor
  · rintro ⟨_, b, hb, lower⟩
    obtain ⟨hbP, a, ha, path⟩ := (mem_relationImage _ _ _ b).1 hb
    let a' := SetMembers.ofMem a (subset ha)
    let b' := SetMembers.ofMem b hbP
    have path' : ZFSet.pair (SetMembers.raw a') (SetMembers.raw b') ∈
        M.finitePathClosure P (meetGeneratorSteps P μ A) := by
      simpa only [a', b', SetMembers.raw_ofMem] using path
    refine ⟨a', ?_, b', (paths a' b').1 path', ?_⟩
    · simpa only [a', SetMembers.raw_ofMem] using ha
    · change ZFSet.pair (SetMembers.raw b') (SetMembers.raw x) ∈ r
      simpa only [b', SetMembers.raw_ofMem] using lower
  · rintro ⟨a, ha, b, path, lower⟩
    exact ⟨SetMembers.raw_mem x, SetMembers.raw b,
      (mem_relationImage _ _ _ _).2 ⟨SetMembers.raw_mem b, SetMembers.raw a, ha,
        (paths a b).2 path⟩, lower⟩

theorem generatedMeetFilter_contains {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) :
    A ⊆ M.generatedMeetFilter P r μ A := by
  intro x hx
  have member := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset
    (SetMembers.ofMem x (subset hx))).2
      (generatedMeetPredicate_contains code.toSmallMeetOrder _
        (by simpa only [SetMembers.raw_ofMem] using hx))
  simpa only [SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_filter {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) (nonempty : A.Nonempty) :
    MeetFilterCode P r μ (M.generatedMeetFilter P r μ A) := by
  have exactMem := M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset
  have typedNonempty : ∃ a : SetMembers P, SetMembers.raw a ∈ A := by
    obtain ⟨a, ha⟩ := nonempty
    exact ⟨SetMembers.ofMem a (subset ha), by
      simpa only [SetMembers.raw_ofMem] using (show a ∈ A from ha)⟩
  let typed := PartitionPilot.generatedMeetFilter code.toSmallMeetOrder
    (fun a => SetMembers.raw a ∈ A) typedNonempty
  have bounded : M.generatedMeetFilter P r μ A ⊆ P :=
    fun x hx => ((mem_relationImage _ _ _ x).1 hx).1
  refine ⟨bounded, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty
    exact ⟨a, M.generatedMeetFilter_contains pairing unions separation infinite hP code subset ha⟩
  · intro x hx y hy lower
    let x' := SetMembers.ofMem x (bounded hx)
    let y' := SetMembers.ofMem y hy
    have hx' : typed.mem x' := (exactMem x').1 (by simpa only [x', SetMembers.raw_ofMem] using hx)
    have lower' : code.toSmallMeetOrder.le x' y' := by
      change ZFSet.pair (SetMembers.raw x') (SetMembers.raw y') ∈ r
      simpa only [x', y', SetMembers.raw_ofMem] using lower
    have member := (exactMem y').2 (typed.upward hx' lower')
    simpa only [y', SetMembers.raw_ofMem] using member
  · intro x hx y hy z entry
    have hz := (ZFSet.pair_mem_prod.1 (code.operation.1 entry)).2
    let x' := SetMembers.ofMem x (bounded hx)
    let y' := SetMembers.ofMem y (bounded hy)
    let z' := SetMembers.ofMem z hz
    have hx' : typed.mem x' := (exactMem x').1 (by simpa only [x', SetMembers.raw_ofMem] using hx)
    have hy' : typed.mem y' := (exactMem y').1 (by simpa only [y', SetMembers.raw_ofMem] using hy)
    have equal : code.toSmallMeetOrder.meet x' y' = z' :=
      (code.toSmallMeetOrder_meet_eq_iff x' y' z').2
        (by simpa only [x', y', z', SetMembers.raw_ofMem] using entry)
    have member := (exactMem z').2 (equal ▸ typed.closed_meet hx' hy')
    simpa only [z', SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_least {P r μ A F : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P)
    (filter : MeetFilterCode P r μ F) (contains : A ⊆ F) :
    M.generatedMeetFilter P r μ A ⊆ F := by
  let typed : Compression.MeetFilter code.toSmallMeetOrder := {
    mem := fun x => SetMembers.raw x ∈ F
    nonempty := by
      obtain ⟨x, hx⟩ := filter.nonempty
      exact ⟨SetMembers.ofMem x (filter.subset hx), by
        simpa only [SetMembers.raw_ofMem] using (show x ∈ F from hx)⟩
    upward := fun {x y} hx lower => filter.upward _ hx _ (SetMembers.raw_mem y) lower
    closed_meet := fun {x y} hx hy => filter.closed_meet _ hx _ hy _ (code.smallMeet_entry x y) }
  intro x hx
  have hxP := ((mem_relationImage _ _ _ x).1 hx).1
  let x' := SetMembers.ofMem x hxP
  have predicate := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset x').1
    (by simpa only [x', SetMembers.raw_ofMem] using hx)
  have member := generatedMeetPredicate_least code.toSmallMeetOrder _ typed
    (fun a ha => contains ha) predicate
  simpa only [typed, x', SetMembers.raw_ofMem] using member

end TransitiveGround

universe u

theorem mem_testedMeetFilter (F r e x : ZFSet.{u}) :
    x ∈ testedMeetFilter F r e ↔ x ∈ F ∧ ZFSet.pair e x ∈ r := by
  rw [testedMeetFilter, mem_relationImage]
  constructor
  · rintro ⟨hx, a, ha, edge⟩
    exact ⟨hx, (ZFSet.mem_singleton.1 ha) ▸ edge⟩
  · rintro ⟨hx, edge⟩
    exact ⟨hx, e, ZFSet.mem_singleton.2 rfl, edge⟩

theorem testedMeetFilter_filter {L r meet F e : ZFSet.{u}}
    (code : MeetOrderCode L r meet) (filter : MeetFilterCode L r meet F)
    (he : e ∈ L)
    (directed : ∀ x ∈ L, ∀ y ∈ L, ∃ z ∈ L, ZFSet.pair x z ∈ r ∧ ZFSet.pair y z ∈ r) :
    MeetFilterCode L r meet (testedMeetFilter F r e) := by
  refine ⟨fun x hx => filter.subset ((mem_testedMeetFilter F r e x).1 hx).1, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := filter.nonempty
    obtain ⟨z, hz, xz, ez⟩ := directed x (filter.subset hx) e he
    exact ⟨z, (mem_testedMeetFilter F r e z).2 ⟨filter.upward x hx z hz xz, ez⟩⟩
  · intro x hx y hy xy
    have parts := (mem_testedMeetFilter F r e x).1 hx
    exact (mem_testedMeetFilter F r e y).2
      ⟨filter.upward x parts.1 y hy xy, code.order.trans e he x (filter.subset parts.1) y hy parts.2 xy⟩
  · intro x hx y hy z entry
    have px := (mem_testedMeetFilter F r e x).1 hx
    have py := (mem_testedMeetFilter F r e y).1 hy
    exact (mem_testedMeetFilter F r e z).2
      ⟨filter.closed_meet x px.1 y py.1 z entry, code.greatest x y z e he entry px.2 py.2⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem testedMeetFilter_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (separation : SeparationSchema M.sets)
    {F r e : ZFSet.{u}} (hF : F ∈ M.sets) (hr : r ∈ M.sets) (he : e ∈ M.sets) :
    testedMeetFilter F r e ∈ M.sets :=
  M.relationImage_mem separation
    (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing he he) hF hr

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality
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

theorem internal_chronological_coinitiality
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (ordinal : ordinalSetProperty T)
    (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets,
      InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
        ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ r := by
  have descent := essentialHeightDescent_of_chronological_laws meet filter born oldMeet strictHeight
  have small := M.essentialBirthIndices_countable pairing unions powers separation infinite choice
    hF hT hr hBirth hC hQ hHeight filter.subset ordinal strictHeight.function smallQ irreflexive descent
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    M.internal_countable_basis_of_birth_layers pairing unions powers separation infinite choice
      hF hT hr hBirth meet.order filter.subset born small localBases
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalHistory

variable {M : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

theorem all_filters_internal_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt) :
    ∀ cutoff ∈ T, ∀ F ∈ M.sets,
      MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F →
        M.InternalCountableBelow (history.order cutoff) F F := by
  intro cutoff
  induction cutoff using ZFSet.inductionOn with
  | h cutoff ih =>
    intro hc F hF filter
    have localBases : ∀ t ∈ essentialBirthIndices F T (history.order cutoff) (history.birth cutoff),
        M.InternalCountableBelow (history.order cutoff) F
          (essentialBirthFiber F T (history.order cutoff) (history.birth cutoff) t) := by
      intro t ht
      obtain ⟨htT, x, hx, xt⟩ :=
        (mem_essentialBirthIndices F T (history.order cutoff) (history.birth cutoff) t).1 ht
      have bounded := history.birth_bound cutoff hc x
        (filter.subset (birthEssentialSet_subset F T (history.order cutoff) (history.birth cutoff) hx)) t xt
      apply (history.layer cutoff hc t htT bounded).internal_countable_essentials
        pairing unions powers separation infinite choice (history.space_mem cutoff hc)
        (history.order_mem cutoff hc) (history.birth_mem cutoff hc) hF hT (M.transitive hT htT)
        (history.meet_order cutoff hc) filter (history.birth_function cutoff hc)
      intro s hs
      have hsT : s ∈ T := ordinal.1 t htT s hs
      have before : s ∈ cutoff := bounded.elim
        (fun equal => equal ▸ hs) (fun earlier => ordinal.2 cutoff hc t earlier s hs)
      exact ⟨history.space_mem s hsT, history.meet_order s hsT, ih s before hsT⟩
    obtain ⟨B, hB, f, hf, injection, positive, below⟩ :=
      M.internal_chronological_coinitiality pairing unions powers separation infinite choice
        hF hT (history.order_mem cutoff hc) (history.birth_mem cutoff hc)
        hC hQ (history.height_mem cutoff hc) (history.meet_order cutoff hc) filter
        (history.birth_function cutoff hc) ordinal (history.old_meet cutoff hc)
        (history.strict_height cutoff hc) smallQ irreflexive localBases
    exact ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩

theorem exists_internal_basis
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ M.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff := by
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    history.all_filters_internal_countable pairing unions powers separation infinite choice
      hT hC hQ ordinal smallQ irreflexive cutoff hc F hF filter
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end GroundChronologicalHistory





end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologicalHistory

open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

theorem exists_extension_basis
    (includes : M.sets ⊆ N.sets)
    (pairing : Realize N.sets SetFormula.pairing Fin.elim0)
    (unions : Realize N.sets SetFormula.union Fin.elim0)
    (powers : Realize N.sets powerSet Fin.elim0) (separation : SeparationSchema N.sets)
    (infinite : Realize N.sets SetFormula.infinity Fin.elim0)
    (choice : Realize N.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ N.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff :=
  (history.of_inclusion includes).exists_internal_basis pairing unions powers separation infinite
    choice (includes hT) (includes hC) (includes hQ) ordinal
    (M.groundEmbeddable_of_inclusion N includes smallQ) irreflexive hc hF filter

end PartitionPilot.Forcing.GroundChronologicalHistory



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyFieldAppend
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (newValues : Fin 5 → ZFSet.{u}) (ground : ∀ j, newValues j ∈ M.sets)

theorem appendTime_value_at (j : Fin 5) :
    (fields.appendTime pairing unions newValues ground).value j T = newValues j := by
  apply GroundChronologyFields.value_eq_of_entry
  exact ZFSet.mem_insert _ _

end PartitionPilot.Forcing.GroundChronologyFields

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalSeparatedActors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem decoded_countable_bound
    (bounds : ∀ X ∈ M.sets, X ⊆ geometry.carrier → M.groundEmbeddable X ZFSet.omega →
      ∃ b ∈ geometry.carrier, ∀ x ∈ X, ZFSet.pair x b ∈ geometry.order) :
    letI := geometry.meet.order.toPartialOrder
    ∀ X ∈ M.sets, X ⊆ (SetMembers.presentation geometry.carrier).carrier →
      M.groundEmbeddable X ZFSet.omega →
      ∃ b : SetMembers geometry.carrier, ∀ x : SetMembers geometry.carrier,
        (SetMembers.presentation geometry.carrier).encode x ∈ X → x ≤ b := by
  let := geometry.meet.order.toPartialOrder
  intro X hX subset countable
  obtain ⟨b, hb, bound⟩ := bounds X hX subset countable
  refine ⟨SetMembers.ofMem b hb, ?_⟩
  intro x hx
  change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (SetMembers.ofMem b hb)) ∈ geometry.order
  rw [SetMembers.raw_ofMem]
  exact bound _ hx

end GroundMainFinalGeometry

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitChronologyCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitChronologyFields_terminal (j : Fin 5) :
    run.limitChronologyFields.value j run.cutoffLimit = run.limitTerminalFields j :=
  run.limitPriorFields.appendTime_value_at pairing unions run.limitTerminalFields run.limitTerminalFields_ground j

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalChronology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

namespace FinalChronology
variable {run} {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)

theorem history_values (s : ZFSet.{u}) :
    chronology.serial.toHistory.space s = run.limitChronologyFields.value 0 s ∧
    chronology.serial.toHistory.order s = run.limitChronologyFields.value 1 s ∧
    chronology.serial.toHistory.meetGraph s = run.limitChronologyFields.value 2 s ∧
    chronology.serial.toHistory.birth s = run.limitChronologyFields.value 3 s ∧
    chronology.serial.toHistory.height s = run.limitChronologyFields.value 4 s :=
  ⟨chronology.values 0 s, chronology.values 1 s, chronology.values 2 s,
    chronology.values 3 s, chronology.values 4 s⟩

theorem terminal_values (i₀ : I) :
    chronology.serial.toHistory.space run.cutoffLimit = (run.finalGeometry i₀).carrier ∧
    chronology.serial.toHistory.order run.cutoffLimit = (run.finalGeometry i₀).order ∧
    chronology.serial.toHistory.meetGraph run.cutoffLimit = (run.finalGeometry i₀).meetGraph ∧
    chronology.serial.toHistory.birth run.cutoffLimit = (run.finalGeometry i₀).birth ∧
    chronology.serial.toHistory.height run.cutoffLimit = (run.finalGeometry i₀).height := by
  obtain ⟨space, order, meet, birth, height⟩ := chronology.history_values run.cutoffLimit
  exact ⟨space.trans (run.limitChronologyFields_terminal 0),
    order.trans (run.limitChronologyFields_terminal 1), meet.trans (run.limitChronologyFields_terminal 2),
    birth.trans (run.limitChronologyFields_terminal 3), height.trans (run.limitChronologyFields_terminal 4)⟩

end FinalChronology

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalExtensionBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalChronology
open SetFormula
universe u v
variable {M N : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem exists_extension_basis (i₀ : I)
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ (run.finalGeometry i₀).order := by
  have terminal := chronology.terminal_values i₀
  have atTerminal : MeetFilterCode (chronology.serial.toHistory.space run.cutoffLimit)
      (chronology.serial.toHistory.order run.cutoffLimit)
      (chronology.serial.toHistory.meetGraph run.cutoffLimit) F := by
    simpa only [terminal.1, terminal.2.1, terminal.2.2.1] using filter
  have basis := chronology.serial.toHistory.exists_extension_basis includes pairingN unionsN powersN
    separationN infiniteN choiceN
    (M.insert_mem pairing unions run.cutoffLimit_ground run.cutoffLimit_ground)
    (run.finalGeometry i₀).columns_ground (run.finalGeometry i₀).coordinates_ground
    chronology.serial.ordinal smallD irreflexive (ZFSet.mem_insert run.cutoffLimit run.cutoffLimit)
    hF atTerminal
  simpa only [terminal.2.1] using basis

end PartitionPilot.Forcing.GroundMainPrefix.FinalChronology

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
include fulfilled

theorem tested_filter_generators
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F e : ZFSet.{u}} (hF : F ∈ M.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F)
    (he : e ∈ (run.finalGeometry i₀).carrier) :
    let geometry := run.finalGeometry i₀
    let tested := testedMeetFilter F geometry.order e
    tested ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph tested ∧
    (∀ x ∈ tested, ZFSet.pair e x ∈ geometry.order) ∧
    ∃ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega ∧ B.Nonempty ∧ B ⊆ tested ∧
      (∀ x ∈ tested, ∃ b ∈ B, ZFSet.pair b x ∈ geometry.order) ∧
      M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph B = tested := by
  let geometry := run.finalGeometry i₀
  let tested := testedMeetFilter F geometry.order e
  have ground : tested ∈ M.sets := M.testedMeetFilter_mem pairing separation hF
    geometry.order_ground (M.transitive geometry.carrier_ground he)
  have testedFilter : MeetFilterCode geometry.carrier geometry.order geometry.meetGraph tested :=
    testedMeetFilter_filter geometry.meet filter he fulfilled.directed
  obtain ⟨B, hB, f, hf, injective, contained, coinitial⟩ :=
    fulfilled.chronology.exists_extension_basis i₀ (N := M) (fun _ hx => hx)
      pairing unions powers separation infinite choice smallD irreflexive ground testedFilter
  have nonempty : B.Nonempty := by
    obtain ⟨x, hx⟩ := testedFilter.nonempty
    obtain ⟨b, hb, _⟩ := coinitial x hx
    exact ⟨b, hb⟩
  have inNodes : B ⊆ geometry.carrier := fun _ hb => testedFilter.subset (contained hb)
  have generatedFilter := M.generatedMeetFilter_filter pairing unions separation infinite
    geometry.carrier_ground geometry.meet inNodes nonempty
  have generators := M.generatedMeetFilter_contains pairing unions separation infinite
    geometry.carrier_ground geometry.meet inNodes
  refine ⟨ground, testedFilter, fun x hx => (mem_testedMeetFilter F geometry.order e x).1 hx |>.2,
    B, hB, ⟨f, hf, injective⟩, nonempty, contained, coinitial, ?_⟩
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    exact M.generatedMeetFilter_least pairing unions separation infinite geometry.carrier_ground
      geometry.meet inNodes testedFilter contained hx
  · intro hx
    obtain ⟨b, hb, bx⟩ := coinitial x hx
    exact generatedFilter.upward b (generators hb) x (testedFilter.subset hx) bx

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticRepresentedDomainEasyCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open scoped ZFSet
universe u
private theorem decoded_property_congr
    {G R : Type u} [Group G] [PartialOrder R]
    (M : TransitiveGround.{u}) (c : Presentation R) (t : Presentation G)
    (T alpha rowGraph packed1 packed2 assignments1 assignments2 action1 action2 : ZFSet.{u})
    (packedEq : packed1 = packed2) (assignmentsEq : assignments1 = assignments2)
    (actionEq : action1 = action2)
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop)
    (code1 : letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1
      let Q1 := M.refinementHistoryForcing c.carrier T alpha packed1
      PosetActionCode t.carrier Q1 ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
        (SetMembers.presentation Q1).conditionOrder
        (rawRowAssignmentActionGraph t.carrier Q1 c.carrier (⋃₀ ⋃₀ Q1) assignments1 rowGraph action1))
    (code2 : letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2
      let Q2 := M.refinementHistoryForcing c.carrier T alpha packed2
      PosetActionCode t.carrier Q2 ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
        (SetMembers.presentation Q2).conditionOrder
        (rawRowAssignmentActionGraph t.carrier Q2 c.carrier (⋃₀ ⋃₀ Q2) assignments2 rowGraph action2)) :
    Property (M.refinementHistoryForcing c.carrier T alpha packed1)
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1)
      (letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1
       code1.toPresentedPosetAction t (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha packed1))) ↔
    Property (M.refinementHistoryForcing c.carrier T alpha packed2)
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2)
      (letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2
       code2.toPresentedPosetAction t (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha packed2))) := by
  subst packed2
  subst assignments2
  subst action2
  rfl

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

variable {stages history alpha : ZFSet.{u}} (hh : history ∈ M.sets)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_restricted_property
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop) :
    Property
      (M.refinementHistoryForcing c.carrier T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha (graphRestriction alpha history)))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha (graphRestriction alpha history)))
      (M.semanticStructuralAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
        cutOrdinal (trace.restrict cutOrdinal subset)) ↔
    Property Q (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked)
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset) := by
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  unfold semanticStructuralAction semanticStructuralPrefixAction
  exact decoded_property_congr M c t T alpha (a.actionGraph c t) _ _ _ _ _ _ packedEq
    (M.structuralAssignments_history_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 alpha history)
    (M.structuralAssignmentActionGraph_history_restrict t.carrier b.carrier b.conditionOrder
      (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history)
    Property _ _

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open scoped ZFSet
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

variable {stages history alpha : ZFSet.{u}} (hh : history ∈ M.sets)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_subhistory_property
    {gamma : ZFSet.{u}} (hGamma : gamma ∈ M.sets) (gammaOrdinal : ordinalSetProperty gamma)
    (alphaGamma : alpha ⊆ gamma) (gammaSubset : gamma ⊆ stages)
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop) :
    let historyGamma := graphRestriction gamma history
    let hhGamma := M.graphRestriction_mem unions separation hGamma hh
    let traceGamma := trace.restrict gammaOrdinal gammaSubset
    let packedGamma := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 gamma historyGamma
    Property (M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packedGamma))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packedGamma))
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hhGamma traceGamma hAlpha cutOrdinal alphaGamma) ↔
    Property Q (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked)
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset) := by
  dsimp only
  have inner := M.semanticStructuralPrefixAction_restricted_property c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows (M.graphRestriction_mem unions separation hGamma hh)
    (trace.restrict gammaOrdinal gammaSubset) hAlpha cutOrdinal alphaGamma Property
  have outer := M.semanticStructuralPrefixAction_restricted_property c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset Property
  let Step := fun level prior stage => stage =
    M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 level prior
  let Applied := fun (h : ZFSet.{u}) (ground : h ∈ M.sets)
      (tr : OrdinalRecursionTrace Step alpha h) =>
    Property (M.refinementHistoryForcing c.carrier T alpha
      (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 alpha h))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha h))
      (M.semanticStructuralAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hAlpha ground cutOrdinal tr)
  have congruent (h1 h2 : ZFSet.{u}) (equal : h1 = h2)
      (ground1 : h1 ∈ M.sets) (ground2 : h2 ∈ M.sets)
      (trace1 : OrdinalRecursionTrace Step alpha h1) (trace2 : OrdinalRecursionTrace Step alpha h2) :
      Applied h1 ground1 trace1 ↔ Applied h2 ground2 trace2 := by
    subst h2
    rfl
  have aligned := congruent _ _ (graphRestriction_restrict alphaGamma)
    (M.graphRestriction_mem unions separation hAlpha (M.graphRestriction_mem unions separation hGamma hh))
    (M.graphRestriction_mem unions separation hAlpha hh)
    ((trace.restrict gammaOrdinal gammaSubset).restrict cutOrdinal alphaGamma)
    (trace.restrict cutOrdinal subset)
  exact inner.symm.trans (aligned.trans outer)

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_StageTwoSupportData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [Preorder L] (b : Presentation L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation infinite choice

theorem exists_stageOneDataBound {A I T S mu X anchors tuples used extra : ZFSet.{u}}
    (hA : A ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (whole : stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples ∈ M.sets)
    (smallA : M.groundEmbeddable A ZFSet.omega)
    (total : ∀ z ∈ A, ∃ E ∈ b.carrier, ZFSet.pair z E ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples)
    (hUsed : used ∈ M.sets) (hExtra : extra ∈ M.sets)
    (usedSubset : used ⊆ b.carrier) (extraSubset : extra ⊆ b.carrier)
    (smallUsed : M.groundEmbeddable used ZFSet.omega)
    (smallExtra : M.groundEmbeddable extra ZFSet.omega)
    (countable_bound : ∀ W ∈ M.sets, W ⊆ b.carrier → M.groundEmbeddable W ZFSet.omega →
      ∃ D : L, ∀ x : L, b.encode x ∈ W → x ≤ D) :
    ∃ D : L, ∃ f ∈ M.sets, ∃ W ∈ M.sets,
      ZFSet.IsFunc A b.carrier f ∧
      f ⊆ stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples ∧
      W = (relationImage A b.carrier f ∪ used) ∪ extra ∧
      W ⊆ b.carrier ∧ M.groundEmbeddable W ZFSet.omega ∧
      (∀ x : L, b.encode x ∈ W → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (b.encode D) ∈
        stageOneDataBounds A I T S b.carrier mu X b.conditionOrder anchors tuples) ∧
      (∀ x : L, b.encode x ∈ used → x ≤ D) ∧
      (∀ x : L, b.encode x ∈ extra → x ≤ D) := by
  obtain ⟨f,hf,W,hW,function,selected,equal,subset,small,included,usedIn,extraIn⟩ :=
    M.exists_countableNodeSelection pairing unions powers separation infinite choice
      hA nodes whole smallA total hUsed hExtra usedSubset extraSubset smallUsed smallExtra
  obtain ⟨D,bound⟩ := countable_bound W hW subset small
  refine ⟨D,f,hf,W,hW,function,selected,equal,subset,small,bound,?_,?_,?_⟩
  · intro z hz
    obtain ⟨E,entry,_⟩ := function.2 z hz
    have hE := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    obtain ⟨E,rfl⟩ := (b.mem_carrier E).1 hE
    exact stageOneDataBounds_mono b (selected entry) (bound E (included z (b.encode E) entry))
  · intro x hx
    exact bound x (usedIn hx)
  · intro x hx
    exact bound x (extraIn hx)

end TransitiveGround

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBinaryRowRecordedPreparationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowDataSelection {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (I anchors : ZFSet.{u}),
      I ∈ M.sets → anchors ∈ M.sets → ZFSet.IsFunc I s.carrier anchors →
    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      A ∈ M.groundSmallSubsets (stageOneAssignments I lifted) ZFSet.omega →
    ∀ (extra : ZFSet.{u}), extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L, ∃ f ∈ M.sets, ∃ W ∈ M.sets,
      ZFSet.IsFunc A s.carrier f ∧
      f ⊆ stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∧
      W = (relationImage A s.carrier f ∪
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p)) ∪ extra ∧
      W ⊆ s.carrier ∧ M.groundEmbeddable W ZFSet.omega ∧
      (∀ x : L, s.encode x ∈ W → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) := by
  intro c rows S T valid lifted tuples hLifted I anchors hI hAnchors anchorFunction p A member extra hExtra extraSubset smallExtra
  have nonbottom := M.nonbottom_carrier_mem s separation hL
  have hS := M.rowPositionSequences_mem pairing unions powers separation hL order nonbottom hmu
  have hTuples := M.binaryLiftedRowTupleFamily_mem pairing unions powers separation collection infinite
    hL order nonbottom hC hmu one valid
  obtain ⟨hA,subset,smallA⟩ := (M.mem_groundSmallSubsets (stageOneAssignments I lifted) ZFSet.omega A).1 member
  have whole := M.stageOneDataBounds_mem pairing unions powers separation hA hI hLifted hS hL
    hmu nonbottom order hAnchors hTuples
  have total := stageOneDataBounds_total s directed subset anchorFunction
    (liftedRowTupleFamily_surjective c (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid)
    (fun f hf => by
      obtain ⟨D,hD,bound⟩ := M.rowPositionSequence_bound hf
      obtain ⟨D,rfl⟩ := (s.mem_carrier D).1 hD
      exact ⟨D,bound⟩)
  obtain ⟨hUsed,smallUsed⟩ := M.countablePartialFunctions_rowSupport pairing unions powers separation
    infinite choice nonbottom hC (M.natSetCode_mem separation infinite 2) (SetMembers.raw_mem p)
  have usedSubset : rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) ⊆ s.carrier := by
    intro x hx
    exact ((s.mem_nonbottom_carrier x).1 (rowUsedRows_subset _ _ _ _ hx)).1
  exact M.exists_stageOneDataBound s pairing unions powers separation infinite choice hA hL whole smallA total
    hUsed hExtra usedSubset extraSubset smallUsed smallExtra countable_bound

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder basis T T2 stages history : ZFSet.{u})
local notation "I" => refinementDataHistoryIndices stages
  (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)

theorem structuralIndex_anchor_fields {x : ZFSet.{u}} (member : x ∈ I) :
    ∃ v : Fin 6 → ZFSet.{u}, x = nonemptyTupleCode 5 v ∧ v 2 ∈ nodes := by
  obtain ⟨level, _hl, data, entry, hx⟩ := (mem_refinementDataHistoryIndices _ _ _).1 member
  obtain ⟨_, P, order, top, action, _stored, rfl⟩ :=
    M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
  obtain ⟨v, equal, bounds⟩ := M.refinementIndices_fields _ _ _ _ _ _ _ _ _ _ _ hx
  exact ⟨v, equal, bounds 2⟩

theorem structuralIndexAnchors_function :
    ZFSet.IsFunc I nodes (refinementIndexFieldGraph I nodes 2) :=
  refinementIndexFieldGraph_function I nodes 2
    (fun _ member => M.structuralIndex_anchor_fields G nodes nodeOrder basis T T2 stages history member)

include M in
 theorem structuralIndexAnchorData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hb : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hs : stages ∈ M.sets) (hh : history ∈ M.sets) :
    I ∈ M.sets ∧ refinementIndexFieldGraph I nodes 2 ∈ M.sets ∧
      ZFSet.IsFunc I nodes (refinementIndexFieldGraph I nodes 2) := by
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have indices := M.refinementDataHistoryIndices_mem pairing unions powers separation hs packed
  exact ⟨indices, M.refinementIndexFieldGraph_mem pairing unions powers separation indices hn 2,
    M.structuralIndexAnchors_function G nodes nodeOrder basis T T2 stages history⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowStructuralDataSelection {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (G basis T2 stages history : ZFSet.{u}),
      G ∈ M.sets → basis ∈ M.sets → T2 ∈ M.sets → stages ∈ M.sets → history ∈ M.sets →
    let I := refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G s.carrier s.conditionOrder basis lifted T2 stages history)
    let anchors := refinementIndexFieldGraph I s.carrier 2

    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      A ∈ M.groundSmallSubsets (stageOneAssignments I lifted) ZFSet.omega →
    ∀ (extra : ZFSet.{u}), extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L, ∃ f ∈ M.sets, ∃ W ∈ M.sets,
      ZFSet.IsFunc A s.carrier f ∧
      f ⊆ stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∧
      W = (relationImage A s.carrier f ∪
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p)) ∪ extra ∧
      W ⊆ s.carrier ∧ M.groundEmbeddable W ZFSet.omega ∧
      (∀ x : L, s.encode x ∈ W → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) := by
  intro c rows S T valid lifted tuples hLifted G basis T2 stages history hG hb hT2 hs hh I anchors
    p A member extra hExtra extraSubset extraSmall
  obtain ⟨indexGround, anchorGround, anchorFunction⟩ :=
    M.structuralIndexAnchorData G s.carrier s.conditionOrder basis lifted T2 stages history
      pairing unions powers separation collection hG hL order hb hLifted hT2 hs hh
  exact M.binaryRowDataSelection s C pairing unions powers separation collection infinite choice
    hL order hC directed countable_bound hmu one valid hLifted I anchors indexGround anchorGround
    anchorFunction p A member extra hExtra extraSubset extraSmall

theorem binaryRowStructuralConditionDataBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (G basis T2 stages history : ZFSet.{u}),
      G ∈ M.sets → basis ∈ M.sets → T2 ∈ M.sets → stages ∈ M.sets → history ∈ M.sets →
    let I := refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G s.carrier s.conditionOrder basis lifted T2 stages history)
    let anchors := refinementIndexFieldGraph I s.carrier 2

    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      ZFSet.pair (c.encode p) A ∈
        M.structuralForcingCarrier c.carrier G s.carrier s.conditionOrder basis lifted T2 stages history →
    ∀ (extra : ZFSet.{u}), extra ∈ M.sets → extra ⊆ s.carrier →
      M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L,
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) := by
  intro c rows S T valid lifted tuples hLifted G basis T2 stages history hG hb hT2 hs hh I anchors
    p A member extra hExtra extraSubset extraSmall
  have candidate := (M.mem_refinementHistoryForcing c.carrier lifted stages
    (M.structuralRefinementHistory G s.carrier s.conditionOrder basis lifted T2 stages history)
    (ZFSet.pair (c.encode p) A)).1 member |>.1
  have small := (ZFSet.pair_mem_prod.1 candidate).2
  obtain ⟨D, _f, _hf, _W, _hW, _function, _selected, _equal, _subset, _small, _bound,
      bounds, usedBound, extraBound⟩ :=
    M.binaryRowStructuralDataSelection s C pairing unions powers separation collection infinite choice
      hL order hC directed countable_bound hmu one valid hLifted G basis T2 stages history
      hG hb hT2 hs hh p A small extra hExtra extraSubset extraSmall
  exact ⟨D, usedBound, bounds, extraBound⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBinaryRowNameSupportBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include pairing unions powers separation collection infinite choice hL order hC directed countable_bound

theorem binaryRowStructuralCondition_nameSupportBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C one
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode one) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let tuples := liftedRowTupleFamily c (c.encode one) mu s.nonbottom.carrier
      (ZFSet.sUnion (ZFSet.sUnion rows)) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (G basis T2 stages history : ZFSet.{u}),
      G ∈ M.sets → basis ∈ M.sets → T2 ∈ M.sets → stages ∈ M.sets → history ∈ M.sets →
    let I := refinementDataHistoryIndices stages
      (M.structuralRefinementHistory G s.carrier s.conditionOrder basis lifted T2 stages history)
    let anchors := refinementIndexFieldGraph I s.carrier 2

    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      ZFSet.pair (c.encode p) A ∈
        M.structuralForcingCarrier c.carrier G s.carrier s.conditionOrder basis lifted T2 stages history →
    ∀ {G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
      (lower : Presentation P) (action : PosetAction G P) (nodeAction : PosetAction G L)
      (base : L) (names : Fin 2 → Name lower),
      (∀ i, HereditarilySymmetric action lower (nodeAction.principalSupportFamily base directed) (names i)) →
    ∀ E : L, ∃ D : L,
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      E ≤ D ∧ ∀ i, nodeAction.principalFix D ≤ action.stabilizer lower (names i) := by
  intro c rows S T valid lifted tuples hLifted Gcode basis T2 stages history
    hG hb hT2 hs hh I anchors row A member G P instG instP instTop lower action nodeAction base names symmetric E
  obtain ⟨first, firstSupport⟩ := (symmetric 0).symmetric
  obtain ⟨second, secondSupport⟩ := (symmetric 1).symmetric
  obtain ⟨common, firstBelow, secondBelow⟩ := directed first second
  let extra : ZFSet.{u} := {s.encode E, s.encode common}
  have hE := M.transitive hL (s.encode_mem E)
  have hCommon := M.transitive hL (s.encode_mem common)
  have extraGround : extra ∈ M.sets := M.unorderedPair_mem pairing hE hCommon
  have extraSubset : extra ⊆ s.carrier := by
    intro x hx
    rcases ZFSet.mem_pair.1 hx with rfl | rfl
    · exact s.encode_mem E
    · exact s.encode_mem common
  have extraSmall : M.groundEmbeddable extra ZFSet.omega :=
    M.unorderedPair_countable pairing unions powers separation infinite hE hCommon
  obtain ⟨D, rowBound, assignmentBound, extraBound⟩ :=
    M.binaryRowStructuralConditionDataBound s C pairing unions powers separation collection
      infinite choice hL order hC directed countable_bound hmu one valid hLifted
      Gcode basis T2 stages history hG hb hT2 hs hh row A member extra extraGround extraSubset extraSmall
  have commonBelow : common ≤ D := extraBound common (ZFSet.mem_pair.2 (Or.inr rfl))
  have atCommon : ∀ i : Fin 2, nodeAction.principalFix common ≤ action.stabilizer lower (names i) :=
    Fin.cases ((nodeAction.principalFix_antitone firstBelow).trans firstSupport)
      (Fin.cases ((nodeAction.principalFix_antitone secondBelow).trans secondSupport) (fun j => Fin.elim0 j))
  exact ⟨D, rowBound, assignmentBound, extraBound E (ZFSet.mem_pair.2 (Or.inl rfl)),
    fun i => (nodeAction.principalFix_antitone commonBelow).trans (atCommon i)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparedWitnessSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem StoredSupportPreparedConditionCode.forget
    {M : TransitiveGround.{u}} {rows T stages history nodes p S : ZFSet.{u}}
    (prepared : StoredSupportPreparedConditionCode M rows T stages history nodes p S) :
    StoredPreparedConditionCode M rows T stages history nodes p := by
  intro row A equal x member
  obtain ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meet, environment,
    sourceRow, sourceA, hSourceA, source, subset, selected,
    k, hk, enumerations, he, q, hq, cut, family, _supportBound⟩ := prepared row A equal x member
  exact ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meet, environment,
    sourceRow, sourceA, hSourceA, source, subset, selected,
    k, hk, enumerations, he, q, hq, cut, family⟩

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalPreparedPrefixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem prepared_prefix_term_bound
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let prefixIndices := refinementDataHistoryIndices alpha lowerPacked
      let prefixAnchors := refinementIndexFieldGraph prefixIndices s.carrier 2
      let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
      ∀ (E : SetMembers geometry.carrier) (u : (M.nameDomain lower).names), u.val.val ∈ lifted →
      ∀ q0 : SetMembers Q,
      ∃ r : SetMembers Q, r ≤ q0 ∧
      ∃ (rowR : SetMembers c.carrier) (lowerA : ZFSet.{u}),
        lower.encode r = ZFSet.pair (c.encode rowR) lowerA ∧
        StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier (lower.encode r) ∧
      ∃ D0 : SetMembers geometry.carrier, E ≤ D0 ∧
        a.principalFix D0 ≤ localAct.stabilizer lower u.val ∧
        (∀ i : SetMembers geometry.carrier, s.encode i ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw rowR) → i ≤ D0) ∧
        (∀ z ∈ lowerA, ZFSet.pair z (s.encode D0) ∈
          stageOneDataBounds lowerA prefixIndices lifted S s.carrier mu s.nonbottom.carrier
            s.conditionOrder prefixAnchors tuples) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  intro alpha member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
  let subset := (And.left stagesOrdinal) alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  let lower := SetMembers.presentation Q
  let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset
  intro E u hu q0
  have packedEq := (M.structuralRefinementHistory_history_restrict b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared alpha history).trans
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared subset)
  have preparedResult : GroundSupportPreparedStrengtheningResult M c lifted alpha lowerPacked
      s.carrier (lower.encode q0) := by
    have actual := fulfilled.structural_support_prepared_strengthening
      collection infinite choice small smallD irreflexive columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      alpha (graphRestriction alpha history) hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
      cutOrdinal (trace.restrict cutOrdinal subset)
    dsimp only at actual
    rw [packedEq] at actual
    exact actual (lower.encode q0) (lower.encode_mem q0)
  obtain ⟨rawR, rawMember, belowQ0, supportsR, _hSupportsR, _supportsSubset, _smallSupports, prepared⟩ :=
    preparedResult
  let r : SetMembers Q := SetMembers.ofMem rawR rawMember
  have encodedR : lower.encode r = rawR := SetMembers.raw_ofMem rawR rawMember
  have rBelowQ0 : r ≤ q0 := by
    apply (lower.pair_mem_conditionOrder r q0).1
    rw [M.refinementHistoryDecodedOrder_eq]
    rw [encodedR]
    exact belowQ0
  obtain ⟨rawRow, rowMember, lowerA, _, rawCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier lifted alpha lowerPacked rawMember)
  let rowR := SetMembers.ofMem rawRow rowMember
  have rCode : lower.encode r = ZFSet.pair (c.encode rowR) lowerA :=
    encodedR.trans (rawCode.trans (congrArg (fun z => ZFSet.pair z lowerA)
      (SetMembers.raw_ofMem rawRow rowMember).symm))
  have preparedAt : StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier
      (lower.encode r) := encodedR.symm ▸ prepared.forget
  have countableBound : ∀ Z ∈ M.sets, Z ⊆ s.carrier → M.groundEmbeddable Z ZFSet.omega →
      ∃ X : SetMembers geometry.carrier, ∀ z : SetMembers geometry.carrier, s.encode z ∈ Z → z ≤ X :=
    geometry.decoded_countable_bound
      (fun Z hZ subset countable => (fulfilled.countable_localization Z hZ subset countable).2)
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation infinite choice
    coordinates two
  obtain ⟨_lowerGround, _lowerOrder, _maps, _lowerClosed, _terms, children⟩ :=
    M.semanticStructuralPrefix_preparation_inputs c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace member infinite choice rowClosed
  have restrictedMember : ZFSet.pair (c.encode rowR) lowerA ∈
      M.structuralForcingCarrier c.carrier b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared alpha (graphRestriction alpha history) := by
    change ZFSet.pair (c.encode rowR) lowerA ∈ M.refinementHistoryForcing c.carrier lifted alpha _
    rw [packedEq]
    exact rCode ▸ lower.encode_mem r
  obtain ⟨D0, rowBound, dataBound, eBelow, nameSupport⟩ :=
    M.binaryRowStructuralCondition_nameSupportBound s columns pairing unions powers separation collection
      infinite choice hL order hColumns directed countableBound hmu ⊤ valid hLifted b.carrier
      (supportBasisCode s b a.principalFix) squared alpha (graphRestriction alpha history)
      hG supports hSquared hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
      rowR lowerA restrictedMember lower localAct a ⊥ ![u.val, u.val]
      (fun i => Fin.cases (children u.val hu)
        (Fin.cases (children u.val hu) (fun j => Fin.elim0 j)) i) E
  rw [packedEq] at dataBound
  exact ⟨r, rBelowQ0, rowR, lowerA, rCode, preparedAt, D0, eBelow, nameSupport 0, rowBound, dataBound⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalPreparedInsertionProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)






theorem prepared_augmented_profiles
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let localValid := M.refinementHistoryRowNameFamily_valid c
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted stages packed →
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      ∀ r0 : SetMembers Q,
      let J := M.fixedIndexAugmentedRequests localAct lower s a alpha lifted squared localValid idx A Rc.val u.val
      let N := M.niceSupportNameCodes localAct lower lifted a.principalFix
      let Profiles (k : ZFSet.{u}) := M.certificateProfileImage J s.carrier N k
      let prefixIndices := refinementDataHistoryIndices alpha lowerPacked
      let prefixAnchors := refinementIndexFieldGraph prefixIndices s.carrier 2
      let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
      J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
      ∃ k ∈ M.sets, ZFSet.IsFunc J (M.supportedEqualityCertificateBound s.carrier N) k ∧
        Profiles k ∈ M.sets ∧ M.groundEmbeddable (Profiles k) ZFSet.omega ∧
        (∀ F ∈ Profiles k, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
      ∃ Pb basis representatives,
        ZFSet.pair (Name.refinementClass lifted localValid Rc.val u.val).val
          (ZFSet.pair Pb (ZFSet.pair basis representatives)) ∈ k ∧ Pb ∈ Profiles k ∧
      ∃ generators ∈ M.sets, M.groundEmbeddable generators ZFSet.omega ∧ generators.Nonempty ∧
        generators ⊆ testedMeetFilter Pb geometry.order (s.encode E) ∧
        M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators =
          testedMeetFilter Pb geometry.order (s.encode E) ∧
      ∃ r : SetMembers Q, r ≤ r0 ∧
      ∃ (rowR : SetMembers c.carrier) (lowerA : ZFSet.{u}),
        lower.encode r = ZFSet.pair (c.encode rowR) lowerA ∧
        StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier (lower.encode r) ∧
      ∃ D0 : SetMembers geometry.carrier, E ≤ D0 ∧
        a.principalFix D0 ≤ localAct.stabilizer lower u.val ∧
        (∀ i : SetMembers geometry.carrier, s.encode i ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw rowR) → i ≤ D0) ∧
        (∀ z ∈ lowerA, ZFSet.pair z (s.encode D0) ∈
          stageOneDataBounds lowerA prefixIndices lifted S s.carrier mu s.nonbottom.carrier
            s.conditionOrder prefixAnchors tuples) ∧
        M.DecidesVisibilityProfile localAct lower s a.principalFix lifted Pb
          (Name.refinementClass lifted localValid Rc.val u.val) r ∧
        (∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
          ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
          F ∈ Profiles k ∧ M.DecidesVisibilityProfile localAct lower s a.principalFix lifted F z.val r) ∧
        ∀ v w : (M.nameDomain lower).names, v.val.val ∈ lifted → w.val.val ∈ lifted →
          stageOneAssignment idx v.val.val w.val.val ∈ A →
          ∃ F B f, ZFSet.pair (Name.refinementClass lifted localValid Rf.val w.val).val
            (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ F ∈ Profiles k ∧
            M.DecidesVisibilityProfile localAct lower s a.principalFix lifted F
              (Name.refinementClass lifted localValid Rf.val w.val) r := by
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed
    alpha member hAlpha cutOrdinal subset lowerPacked Q
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  intro historyRun
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  intro lower localAct localValid row A condition V E U Rf Rc u idx inI hu r0 J N
    Profiles prefixIndices prefixAnchors tuples
  obtain ⟨hJ, smallJ, validJ, H, _coded, _ordinary, k, hk, function, _selected,
      q0, _hq0, q0Below, profilesGround, profilesSmall, profileFilters, decisions⟩ :=
    fulfilled.augmented_profile_family collection infinite choice small smallD irreflexive
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace alpha member
      row A condition V E U Rf Rc u inI hu r0
  have coarseMember : (Name.refinementClass lifted localValid Rc.val u.val).val ∈ J :=
    ZFSet.mem_insert _ _
  let coarse : (M.nameDomain lower).names :=
    ⟨Name.refinementClass lifted localValid Rc.val u.val, M.transitive hJ coarseMember⟩
  obtain ⟨coarseValue, coarseEdge, _coarseUnique⟩ := function.2 coarse.val.val coarseMember
  have coarseBound := (ZFSet.pair_mem_prod.1 (function.1 coarseEdge)).2
  obtain ⟨Pb, _hPb, tail, hTail, rfl⟩ := ZFSet.mem_prod.1 coarseBound
  obtain ⟨basis, _hBasis, representatives, _hRepresentatives, rfl⟩ := ZFSet.mem_prod.1 hTail
  have coarseChosen := decisions coarse Pb basis representatives coarseEdge
  have PbGround := M.transitive profilesGround coarseChosen.1
  obtain ⟨_testedGround, _testedFilter, _testedAbove, generators, hGenerators,
      smallGenerators, nonemptyGenerators, generatorsSubset, _coinitial, generated⟩ :=
    fulfilled.tested_filter_generators infinite choice smallD irreflexive PbGround
      (profileFilters Pb coarseChosen.1) (s.encode_mem E)
  obtain ⟨r, rBelowQ0, rowR, lowerA, rCode, preparedAt, D0, eBelow, nameSupport, rowBound, dataBound⟩ :=
    fulfilled.prepared_prefix_term_bound collection infinite choice small smallD irreflexive
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace alpha member E u hu q0
  have decisionsAt : ∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
      ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      F ∈ M.certificateProfileImage J s.carrier N k ∧
        M.DecidesVisibilityProfile localAct lower s a.principalFix lifted F z.val r := by
    intro z F B f edge
    have chosen := decisions z F B f edge
    refine ⟨chosen.1, fun v => ⟨?_, ?_⟩⟩
    · intro yes
      exact Name.forcesMem_mono ((chosen.2.2.1 v).1 yes) rBelowQ0
    · intro no p pr
      exact (chosen.2.2.1 v).2 no p (pr.trans rBelowQ0)
  refine ⟨hJ, smallJ, k, hk, function, profilesGround, profilesSmall, profileFilters,
    Pb, basis, representatives, coarseEdge, coarseChosen.1, generators, hGenerators,
    smallGenerators, nonemptyGenerators, generatorsSubset, generated, r, rBelowQ0.trans q0Below,
    rowR, lowerA, rCode, preparedAt, D0, eBelow, nameSupport, rowBound, dataBound,
    (decisionsAt coarse Pb basis representatives coarseEdge).2, decisionsAt, ?_⟩
  intro v w hv hw old
  obtain ⟨_, _, _, _, _, _, _, _, exactJ⟩ :=
    M.semanticStructuralPrefix_augmentedClassRequests c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace member infinite choice condition V E U Rf Rc u inI hu
  have fineMember : (Name.refinementClass lifted localValid Rf.val w.val).val ∈ J :=
    (exactJ _).2 (Or.inr ⟨v.val, w.val, hv, hw, old, rfl⟩)
  let fine : (M.nameDomain lower).names :=
    ⟨Name.refinementClass lifted localValid Rf.val w.val, M.transitive hJ fineMember⟩
  obtain ⟨value, edge, _unique⟩ := function.2 fine.val.val fineMember
  have bound := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
  obtain ⟨F, _hF, tail, hTail, rfl⟩ := ZFSet.mem_prod.1 bound
  obtain ⟨B, _hB, f, _hf, rfl⟩ := ZFSet.mem_prod.1 hTail
  exact ⟨F, B, f, edge, decisionsAt fine F B f edge⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalSuccessorPreparedProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem successor_prepared_insertion_profiles_oai
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let localValid := M.refinementHistoryRowNameFamily_valid c
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) (graphRestriction (insert alpha alpha) packed) →
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      ∀ r0 : SetMembers Q,
      let J := M.fixedIndexAugmentedRequests localAct lower s a alpha lifted squared localValid idx A Rc.val u.val
      let N := M.niceSupportNameCodes localAct lower lifted a.principalFix
      let Profiles (k : ZFSet.{u}) := M.certificateProfileImage J s.carrier N k
      let prefixIndices := refinementDataHistoryIndices alpha lowerPacked
      let prefixAnchors := refinementIndexFieldGraph prefixIndices s.carrier 2
      let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
      J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
      ∃ k ∈ M.sets, ZFSet.IsFunc J (M.supportedEqualityCertificateBound s.carrier N) k ∧
        Profiles k ∈ M.sets ∧ M.groundEmbeddable (Profiles k) ZFSet.omega ∧
        (∀ F ∈ Profiles k, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
      ∃ Pb basis representatives,
        ZFSet.pair (Name.refinementClass lifted localValid Rc.val u.val).val
          (ZFSet.pair Pb (ZFSet.pair basis representatives)) ∈ k ∧ Pb ∈ Profiles k ∧
      ∃ generators ∈ M.sets, M.groundEmbeddable generators ZFSet.omega ∧ generators.Nonempty ∧
        generators ⊆ testedMeetFilter Pb geometry.order (s.encode E) ∧
        M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators =
          testedMeetFilter Pb geometry.order (s.encode E) ∧
      ∃ r : SetMembers Q, r ≤ r0 ∧
      ∃ (rowR : SetMembers c.carrier) (lowerA : ZFSet.{u}),
        lower.encode r = ZFSet.pair (c.encode rowR) lowerA ∧
        StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier (lower.encode r) ∧
      ∃ D0 : SetMembers geometry.carrier, E ≤ D0 ∧
        a.principalFix D0 ≤ localAct.stabilizer lower u.val ∧
        (∀ i : SetMembers geometry.carrier, s.encode i ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw rowR) → i ≤ D0) ∧
        (∀ z ∈ lowerA, ZFSet.pair z (s.encode D0) ∈
          stageOneDataBounds lowerA prefixIndices lifted S s.carrier mu s.nonbottom.carrier
            s.conditionOrder prefixAnchors tuples) ∧
        M.DecidesVisibilityProfile localAct lower s a.principalFix lifted Pb
          (Name.refinementClass lifted localValid Rc.val u.val) r ∧
        (∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
          ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
          F ∈ Profiles k ∧ M.DecidesVisibilityProfile localAct lower s a.principalFix lifted F z.val r) ∧
        ∀ v w : (M.nameDomain lower).names, v.val.val ∈ lifted → w.val.val ∈ lifted →
          stageOneAssignment idx v.val.val w.val.val ∈ A →
          ∃ F B f, ZFSet.pair (Name.refinementClass lifted localValid Rf.val w.val).val
            (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ F ∈ Profiles k ∧
            M.DecidesVisibilityProfile localAct lower s a.principalFix lifted F
              (Name.refinementClass lifted localValid Rf.val w.val) r := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  intro alpha member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
  let subset := (And.left stagesOrdinal) alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  let lower := SetMembers.presentation Q
  let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let localValid := M.refinementHistoryRowNameFamily_valid c
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
  let gamma := insert alpha alpha
  have hGamma : gamma ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have gammaOrdinal : ordinalSetProperty gamma := ordinalSetProperty_succ cutOrdinal
  have alphaGamma : alpha ⊆ gamma := fun _ hx => ZFSet.mem_insert_of_mem _ hx
  have gammaSubset : gamma ⊆ stages := by
    intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact member
    · exact subset x old
  let historyGamma := graphRestriction gamma history
  have hhGamma : historyGamma ∈ M.sets := M.graphRestriction_mem unions separation hGamma hh
  have traceGamma := trace.restrict gammaOrdinal gammaSubset
  let packedGamma := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared gamma historyGamma
  have packedGammaEq : packedGamma = graphRestriction gamma packed :=
    (M.structuralRefinementHistory_history_restrict b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared gamma history).trans
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared gammaSubset)
  have lowerPackedEq : graphRestriction alpha packedGamma = lowerPacked := by
    rw [packedGammaEq, graphRestriction_restrict alphaGamma]
  let Property : ∀ (domainSet : ZFSet.{u}) (orderQ : PartialOrder (SetMembers domainSet)),
      @PosetAction (SetMembers geometry.actors) _ (SetMembers domainSet) orderQ → Prop :=
    fun domainSet orderQ actionQ =>
      letI := orderQ
      ∀ topQ : OrderTop (SetMembers domainSet),
      letI := topQ
      let lower := SetMembers.presentation domainSet
      ∀ localValid : ∀ z ∈ lifted, IsName lower z,
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) (graphRestriction (insert alpha alpha) packed) →
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices actionQ lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      ∀ r0 : SetMembers domainSet,
      let J := M.fixedIndexAugmentedRequests actionQ lower s a alpha lifted squared localValid idx A Rc.val u.val
      let N := M.niceSupportNameCodes actionQ lower lifted a.principalFix
      let Profiles (k : ZFSet.{u}) := M.certificateProfileImage J s.carrier N k
      let prefixIndices := refinementDataHistoryIndices alpha lowerPacked
      let prefixAnchors := refinementIndexFieldGraph prefixIndices s.carrier 2
      let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
      J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
      ∃ k ∈ M.sets, ZFSet.IsFunc J (M.supportedEqualityCertificateBound s.carrier N) k ∧
        Profiles k ∈ M.sets ∧ M.groundEmbeddable (Profiles k) ZFSet.omega ∧
        (∀ F ∈ Profiles k, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
      ∃ Pb basis representatives,
        ZFSet.pair (Name.refinementClass lifted localValid Rc.val u.val).val
          (ZFSet.pair Pb (ZFSet.pair basis representatives)) ∈ k ∧ Pb ∈ Profiles k ∧
      ∃ generators ∈ M.sets, M.groundEmbeddable generators ZFSet.omega ∧ generators.Nonempty ∧
        generators ⊆ testedMeetFilter Pb geometry.order (s.encode E) ∧
        M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators =
          testedMeetFilter Pb geometry.order (s.encode E) ∧
      ∃ r : SetMembers domainSet, r ≤ r0 ∧
      ∃ (rowR : SetMembers c.carrier) (lowerA : ZFSet.{u}),
        lower.encode r = ZFSet.pair (c.encode rowR) lowerA ∧
        StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier (lower.encode r) ∧
      ∃ D0 : SetMembers geometry.carrier, E ≤ D0 ∧
        a.principalFix D0 ≤ actionQ.stabilizer lower u.val ∧
        (∀ i : SetMembers geometry.carrier, s.encode i ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw rowR) → i ≤ D0) ∧
        (∀ z ∈ lowerA, ZFSet.pair z (s.encode D0) ∈
          stageOneDataBounds lowerA prefixIndices lifted S s.carrier mu s.nonbottom.carrier
            s.conditionOrder prefixAnchors tuples) ∧
        M.DecidesVisibilityProfile actionQ lower s a.principalFix lifted Pb
          (Name.refinementClass lifted localValid Rc.val u.val) r ∧
        (∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
          ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
          F ∈ Profiles k ∧ M.DecidesVisibilityProfile actionQ lower s a.principalFix lifted F z.val r) ∧
        ∀ v w : (M.nameDomain lower).names, v.val.val ∈ lifted → w.val.val ∈ lifted →
          stageOneAssignment idx v.val.val w.val.val ∈ A →
          ∃ F B f, ZFSet.pair (Name.refinementClass lifted localValid Rf.val w.val).val
            (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ F ∈ Profiles k ∧
            M.DecidesVisibilityProfile actionQ lower s a.principalFix lifted F
              (Name.refinementClass lifted localValid Rf.val w.val) r
  let QGamma := M.refinementHistoryForcing c.carrier lifted alpha (graphRestriction alpha packedGamma)
  let gammaOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha
    (graphRestriction alpha packedGamma)
  let runGamma := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared gammaOrdinal traceGamma
  let topGamma := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha
    (graphRestriction alpha packedGamma) (runGamma.carriers.restrict cutOrdinal alphaGamma)
    cutOrdinal carrier (c.encode ⊤) topMem topRows
  let validGamma := M.refinementHistoryRowNameFamily_valid c
    (runGamma.carriers.restrict cutOrdinal alphaGamma) cutOrdinal carrier lifted valid1
  let actionGamma := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hhGamma traceGamma hAlpha cutOrdinal alphaGamma
  have inside : Property QGamma gammaOrder actionGamma := by
    intro topQ
    have topEq : topQ = topGamma := Subsingleton.elim _ _
    subst topQ
    dsimp only
    intro validQ
    have validEq : validQ = validGamma := Subsingleton.elim _ _
    subst validQ
    intro row A condition V E U Rf Rc u inI hu r0
    have conditionGamma : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted gamma packedGamma := by
      rw [packedGammaEq]
      exact condition
    obtain ⟨hJ, smallJ, k, hk, function, profilesGround, profilesSmall, filters,
      Pb, basis, representatives, coarseEdge, coarseMember, generators, hGenerators,
      smallGenerators, nonemptyGenerators, generatorsSubset, generated, r, below,
      rowR, lowerA, rCode, prepared, D0, eBelow, nameSupport, rowBound, dataBound,
      coarseDecision, decisions, oldProfiles⟩ :=
      fulfilled.prepared_augmented_profiles collection infinite choice small smallD irreflexive
        columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
        children1 children2 gamma historyGamma hGamma hhGamma gammaOrdinal traceGamma
        alpha (ZFSet.mem_insert _ _) row A conditionGamma V E U Rf Rc u inI hu r0
    have preparedParent : StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier
        ((SetMembers.presentation QGamma).encode r) := by
      have transfer (raw : ZFSet.{u}) :
          StoredPreparedConditionCode M c.carrier lifted alpha (graphRestriction alpha packedGamma) s.carrier raw →
          StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier raw := by
        rw [lowerPackedEq]
        exact id
      exact transfer _ prepared
    rw [lowerPackedEq] at dataBound
    exact ⟨hJ, smallJ, k, hk, function, profilesGround, profilesSmall, filters,
      Pb, basis, representatives, coarseEdge, coarseMember, generators, hGenerators,
      smallGenerators, nonemptyGenerators, generatorsSubset, generated, r, below,
      rowR, lowerA, rCode, preparedParent, D0, eBelow, nameSupport, rowBound, dataBound,
      coarseDecision, decisions, oldProfiles⟩
  have outside := (M.semanticStructuralPrefixAction_subhistory_property c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset hGamma gammaOrdinal alphaGamma gammaSubset Property).1 inside
  exact outside inferInstance localValid

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.successor_prepared_insertion_profiles_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.successor_prepared_insertion_profiles_oai.{u, v}
