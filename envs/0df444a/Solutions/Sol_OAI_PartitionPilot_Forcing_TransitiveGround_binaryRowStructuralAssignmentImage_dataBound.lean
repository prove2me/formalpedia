-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowStructuralAssignmentImage_dataBound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:17:13.872191+00:00
-- url     : https://prove2.me/submissions/40406560-3eb7-4e97-ad39-5533d51e694f

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

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u v
variable {P Q R : Type u} {s : Presentation P}

theorem rename_check (t : Presentation Q) (f : P → Q) (one : P) (x : ZFSet.{u}) :
    rename t f (check s one x) = check t (f one) x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [check, rename_assemble, check]
    apply congrArg (fun names : x → Name t => assemble names (fun _ => f one))
    funext y
    exact ih y.val y.property

theorem rename_check_fixed (f : P → P) (one : P) (fixed : f one = one) (x : ZFSet.{u}) :
    rename s f (check s one x) = check s one x := by
  rw [rename_check, fixed]

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v

namespace PosetAction
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_check [OrderTop P] (g : G) (x : ZFSet.{u}) :
    a.act s g (Name.check s ⊤ x) = Name.check s ⊤ x :=
  Name.rename_check_fixed (a.iso g) ⊤ (a.iso g).map_top x

end PosetAction
end PartitionPilot.Forcing



end OAI
end

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

theorem nonbottom_encode (s : Presentation I) (x : {x : I // x ≠ ⊥}) :
    s.nonbottom.encode x = s.encode x.val := rfl

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.PosetAction

universe u v
variable {G : Type v} [Group G] {I : Type u} [PartialOrder I] [OrderBot I]

theorem nonbottom_iso_val (a : PosetAction G I) (g : G) (x : {x : I // x ≠ ⊥}) :
    (a.nonbottom.iso g x).val = a.iso g x.val := rfl

end PartitionPilot.Forcing.PosetAction

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

namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u v
variable {P : Type u} {G : Type v} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s t : Presentation P)

theorem act_presentationEquiv (g : G) (τ : Name s) :
    a.act t g (Name.presentationEquiv s t τ) = Name.presentationEquiv s t (a.act s g τ) := by
  change Name.rename t (a.iso g) (Name.rename t id τ) =
    Name.rename t id (Name.rename s (a.iso g) τ)
  rw [Name.rename_comp, Name.rename_comp]
  rfl

end PartitionPilot.Forcing.PosetAction

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_IndexedTupleNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace Name

theorem check_code_eq {P : Type u} (s : Presentation P) (one : P) (x : ZFSet.{u}) :
    (check s one x).val = checkNameCode (s.encode one) x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    change z ∈ (check s one x).val ↔ z ∈ (check (checkCodePresentation (s.encode one)) ⟨()⟩ x).val
    rw [mem_check_code, mem_check_code]
    apply exists_congr
    intro y
    apply and_congr_right
    intro hy
    rw [ih y hy]
    rfl

end Name

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} {s : Presentation P}

theorem rename_indexedTuple (t : Presentation Q) (f : P → Q) (one : P)
    (I : ZFSet.{u}) (names : I.toSet → Name s) :
    rename t f (indexedTuple one I names) =
      indexedTuple (f one) I (fun i => rename t f (names i)) := by
  rw [indexedTuple, rename_assemble, indexedTuple]
  apply congrArg (fun ns : I → Name t => assemble ns (fun _ => f one))
  funext i
  rw [rename_orderedPair, rename_check]

theorem act_indexedTuple {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (g : G) (I : ZFSet.{u}) (names : I.toSet → Name s) :
    a.act s g (indexedTuple ⊤ I names) = indexedTuple ⊤ I (fun i => a.act s g (names i)) := by
  change rename s (a.iso g) _ = _
  rw [rename_indexedTuple, (a.iso g).map_top]
  rfl

end PartitionPilot.Forcing.Name

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

theorem rowPositionSequence_length {mu delta : ZFSet.{u}}
    (ordinal : ordinalSetProperty mu) (length : delta ∈ insert mu mu) :
    ordinalSetProperty delta ∧ delta ⊆ mu := by
  rcases ZFSet.mem_insert_iff.1 length with rfl | member
  · exact ⟨ordinal, fun _ hx => hx⟩
  · exact ⟨ordinalSetProperty_member ordinal member, fun a ha => ordinal.1 delta member a ha⟩

theorem RowPositionSequenceCode.shape {L r I mu f : ZFSet.{u}}
    (code : RowPositionSequenceCode L r I mu f) (ordinal : ordinalSetProperty mu) :
    f ⊆ ZFSet.prod mu I := by
  obtain ⟨delta, length, function, _⟩ := code
  intro z hz
  obtain ⟨a, ha, x, hx, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨(rowPositionSequence_length ordinal length).2 ha, hx⟩

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

theorem mem_rowPositionSequences {L r I mu f : ZFSet.{u}} (ordinal : ordinalSetProperty mu) :
    f ∈ M.rowPositionSequences L r I mu ↔ f ∈ M.sets ∧ RowPositionSequenceCode L r I mu f := by
  rw [rowPositionSequences, ZFSet.mem_sep, M.mem_groundRelations]
  exact ⟨fun ⟨ground, code⟩ => ⟨ground.1, code⟩,
    fun ⟨ground, code⟩ => ⟨⟨ground, code.shape ordinal⟩, code⟩⟩

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

theorem rowPositionSequence_data {L r I mu f : ZFSet.{u}}
    (hL : L ∈ M.sets) (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu)
    (member : f ∈ M.rowPositionSequences L r I mu) :
    f ∈ M.sets ∧ ∃ delta ∈ M.sets, ordinalSetProperty delta ∧ delta ⊆ mu ∧
      ZFSet.IsFunc delta I f ∧ ∃ D ∈ L, D ∈ M.sets ∧
        ∀ a x, ZFSet.pair a x ∈ f → ZFSet.pair x D ∈ r := by
  obtain ⟨ground, delta, length, function, D, hD, bounds⟩ :=
    (M.mem_rowPositionSequences ordinal).1 member
  have hdelta : delta ∈ M.sets := (ZFSet.mem_insert_iff.1 length).elim
    (fun equal => equal ▸ hmu) (M.transitive hmu)
  have ordBound := rowPositionSequence_length ordinal length
  exact ⟨ground, delta, hdelta, ordBound.1, ordBound.2, function,
    D, hD, M.transitive hL hD, bounds⟩

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

end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFlatSuccessorFullActionGraph
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y G : Type u} [Group G] [PartialOrder X]
variable (a : PosetAction G X) (s : Presentation X) (t : Presentation Y) (b : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {N : ZFSet.{u}} (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
variable (hG : b.carrier ∈ M.sets) (hN : N ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)

theorem smallFunctionAction_entry (g : G) (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N))
    (x : X) (y : Y) :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    ZFSet.pair (s.encode (a.iso g x)) (t.encode y) ∈
      SetMembers.raw ((M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph).iso g p) ↔
        ZFSet.pair (s.encode x) (t.encode y) ∈ SetMembers.raw p := by
  let := M.smallFunctionOrder s.carrier t.carrier N
  rw [raw_smallFunctionAction, pair_mem_graphRename]
  change ZFSet.pair (s.encode ((a.iso g).toEquiv.symm ((a.iso g).toEquiv x))) (t.encode y) ∈ _ ↔ _
  rw [(a.iso g).toEquiv.symm_apply_apply]

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {L G : Type u} [PartialOrder L] [OrderBot L] [Group G]

theorem pair_mem_rowPositionSequenceAction (a : PosetAction G L) (s : Presentation L)
    (g : G) (mu f i : ZFSet.{u}) (x : {x : L // x ≠ ⊥}) :
    ZFSet.pair i (s.encode (a.iso g x.val)) ∈ rowPositionSequenceAction a s g mu f ↔
      i ∈ mu ∧ ZFSet.pair i (s.encode x.val) ∈ f := by
  rw [rowPositionSequenceAction, pair_mem_relationCompose]
  constructor
  · rintro ⟨hi, _, y, hy, entry, moved⟩
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
    have equal := (s.nonbottom.pair_mem_graph s.nonbottom (a.nonbottom.iso g)
      y (a.nonbottom.iso g x)).1 moved
    have same := (a.nonbottom.iso g).injective equal
    exact ⟨hi, same ▸ entry⟩
  · rintro ⟨hi, entry⟩
    exact ⟨hi, s.nonbottom.encode_mem (a.nonbottom.iso g x), s.encode x.val,
      s.nonbottom.encode_mem x, entry,
      (s.nonbottom.pair_mem_graph s.nonbottom (a.nonbottom.iso g) x _).2 rfl⟩

theorem rowPositionSequenceAction_function (a : PosetAction G L) (s : Presentation L)
    (g : G) {mu delta f : ZFSet.{u}} (subset : delta ⊆ mu)
    (function : ZFSet.IsFunc delta s.nonbottom.carrier f) :
    ZFSet.IsFunc delta s.nonbottom.carrier (rowPositionSequenceAction a s g mu f) := by
  constructor
  · intro z hz
    obtain ⟨i, _, y, _, x, hx, rfl, entry, _⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨(ZFSet.pair_mem_prod.1 (function.1 entry)).1, hx⟩
  · intro i hi
    obtain ⟨x, entry, unique⟩ := function.2 i hi
    obtain ⟨x, rfl⟩ := (s.nonbottom.mem_carrier x).1
      (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    refine ⟨s.encode (a.iso g x.val),
      (pair_mem_rowPositionSequenceAction a s g mu f i x).2 ⟨subset hi, entry⟩, ?_⟩
    intro y hy
    have hyI := ((pair_mem_relationCompose _ _ _ _ _ i y).1 hy).2.1
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hyI
    let old := (a.nonbottom.iso g).symm y
    have target : a.nonbottom.iso g old = y := (a.nonbottom.iso g).apply_symm_apply y
    have original : ZFSet.pair i (s.encode old.val) ∈ f := by
      apply ((pair_mem_rowPositionSequenceAction a s g mu f i old).1 ?_).2
      simpa only [← PosetAction.nonbottom_iso_val, target, Presentation.nonbottom_encode] using hy
    have same : old = x := s.nonbottom.injective (unique _ original)
    exact congrArg s.nonbottom.encode ((congrArg (a.nonbottom.iso g) same).symm.trans target).symm

theorem rowPositionSequenceAction_code (a : PosetAction G L) (s : Presentation L)
    (g : G) {mu f : ZFSet.{u}} (ordinal : ordinalSetProperty mu)
    (code : RowPositionSequenceCode s.carrier s.conditionOrder s.nonbottom.carrier mu f) :
    RowPositionSequenceCode s.carrier s.conditionOrder s.nonbottom.carrier mu
      (rowPositionSequenceAction a s g mu f) := by
  obtain ⟨delta, length, function, d, hd, bounds⟩ := code
  have subset := (rowPositionSequence_length ordinal length).2
  obtain ⟨D, rfl⟩ := (s.mem_carrier d).1 hd
  have movedFunction := rowPositionSequenceAction_function a s g subset function
  refine ⟨delta, length, movedFunction, s.encode (a.iso g D), s.encode_mem _, ?_⟩
  intro i x entry
  obtain ⟨_, _, y, hy, original, moved⟩ := (pair_mem_relationCompose _ _ _ _ _ i x).1 entry
  obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
  obtain ⟨v, hv⟩ := (s.nonbottom.mem_graph s.nonbottom (a.nonbottom.iso g) _).1 moved
  obtain ⟨same, value⟩ := ZFSet.pair_inj.1 hv
  have equal : v = y := s.nonbottom.injective same
  have lower := (s.pair_mem_conditionOrder y.val D).1 (bounds i _ original)
  have result := (s.pair_mem_conditionOrder (a.iso g y.val) (a.iso g D)).2 ((a.iso g).monotone lower)
  rw [equal] at value
  exact value ▸ result

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowPositionSequenceAction_mem (a : PosetAction G L) (s : Presentation L) (b : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hL : s.carrier ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (graph : a.actionGraph s b ∈ M.sets) {mu f : ZFSet.{u}}
    (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) (g : G)
    (member : f ∈ M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu) :
    rowPositionSequenceAction a s g mu f ∈
      M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu := by
  obtain ⟨hf, code⟩ := (M.mem_rowPositionSequences ordinal).1 member
  have hI := M.nonbottom_carrier_mem s separation hL
  have ha := M.nonbottom_actionGraph_mem a s b separation hL hG graph
  have actionSection := M.actionGraph_section_mem a.nonbottom s.nonbottom b pairing unions powers
    separation hI ha g (M.transitive hG (b.encode_mem g))
  exact (M.mem_rowPositionSequences ordinal).2
    ⟨M.relationCompose_mem pairing unions powers separation hmu hI hI hf actionSection,
      rowPositionSequenceAction_code a s g ordinal code⟩

end TransitiveGround

end PartitionPilot.Forcing

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

open SetRealization
universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowAction_entry :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers
      (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}) (c : SetMembers C) (k : Fin 2),
      ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) (SetMembers.raw c)) (natSetCode k.val) ∈
        SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p) ↔
      ZFSet.pair (ZFSet.pair (s.encode i.val) (SetMembers.raw c)) (natSetCode k.val) ∈
        SetMembers.raw p := by
  let := columnOrder C
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i c k
  exact M.smallFunctionAction_entry (a.rowCoordinates C) (rowCoordinatePresentation s C)
    (natInitialPresentation 2) b pairing unions powers separation
    (M.rowCoordinate_carrier_mem s C pairing unions powers separation hL hC)
    (M.natSetCode_mem separation infinite 2) hG (M.omega_mem separation infinite)
    (M.rowCoordinate_graph_mem a s b C pairing unions powers separation hL hC hG graph)
    g p (i, c) (ULift.up k)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowName_action (g : G) (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowName s C hL i) =
      M.internalRowName s C hL (a.nonbottom.iso g i) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val)) =
    M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode (a.iso g i.val))
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename c (act.iso g)
    (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val))) q ↔ _
  rw [Name.entry_rename, M.entry_binaryRowName]
  constructor
  · rintro ⟨ν, p, entry, eq, rfl⟩
    obtain ⟨x, hx, rfl, hp⟩ := (M.entry_binaryRowName s.nonbottom.carrier C ⊤
      (s.encode i.val) ν p).1 entry
    refine ⟨x, hx, (act.act_check c g x).symm.trans eq, ?_⟩
    have moved := M.internalRowAction_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i (SetMembers.ofMem x hx) (1 : Fin 2)
    simp only [SetMembers.raw_ofMem] at moved
    exact moved.2 hp
  · rintro ⟨x, hx, rfl, hq⟩
    let p := (act.iso g).symm q
    have pq : act.iso g p = q := (act.iso g).apply_symm_apply q
    have moved := M.internalRowAction_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i (SetMembers.ofMem x hx) (1 : Fin 2)
    simp only [SetMembers.raw_ofMem] at moved
    have hp : ZFSet.pair (ZFSet.pair (s.encode i.val) x) (natSetCode 1) ∈
        SetMembers.raw p := by
      apply moved.1
      change ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) x) (natSetCode 1) ∈
        SetMembers.raw (act.iso g p)
      rw [pq]
      exact hq
    exact ⟨Name.check c ⊤ x, p,
      (M.entry_binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val) _ p).2
        ⟨x, hx, rfl, hp⟩, act.act_check c g x, pq⟩

end PartitionPilot.Forcing.TransitiveGround



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
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowTupleName_action (g : G) (δ : ZFSet.{u})
    (positions : δ.toSet → {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowTupleName s C hL δ positions) =
      M.internalRowTupleName s C hL δ (fun i => a.nonbottom.iso g (positions i)) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (Name.indexedTuple ⊤ δ _) = Name.indexedTuple ⊤ δ _
  rw [Name.act_indexedTuple]
  apply congrArg (Name.indexedTuple ⊤ δ)
  funext i
  exact M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph g (positions i)

end PartitionPilot.Forcing.TransitiveGround



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





namespace Name
theorem mem_indexedTuple_code {P : Type u} {s : Presentation P} (one : P)
    (δ : ZFSet.{u}) (names : δ.toSet → Name s) (z : ZFSet.{u}) :
    z ∈ (indexedTuple one δ names).val ↔ ∃ i : δ.toSet,
      z = ZFSet.pair (orderedPairNameCode (s.encode one) (check s one i.val).val (names i).val)
        (s.encode one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  simp only [orderedPair_code]
  exact exists_congr (fun _ => eq_comm)

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem binaryRowTupleCode_eq {I C mu δ f : ZFSet.{u}}
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (function : FunctionGraphOn δ f) (subset : δ ⊆ mu)
    (range : ∀ i, function.value i ∈ I) :
    let rows := M.binaryRowNameGraph I C one
    rowTupleCode (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows f =
      (Name.indexedTuple one δ (fun i => M.binaryRowName I C one (function.value i))).val := by
  dsimp only
  apply ZFSet.ext
  intro z
  rw [rowTupleCode, mem_indexedGraphNameCode, Name.mem_indexedTuple_code]
  constructor
  · rintro ⟨i, _, v, entry, equal⟩
    obtain ⟨_, _, x, hx, old, row⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    have hi := function.pair_source old
    have value := function.value_eq_of_entry ⟨i, hi⟩ old
    have rowValue := ((M.pair_mem_binaryRowNameGraph I C one x v).1 row).2
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [Name.check_code_eq, value]
    exact rowValue ▸ equal
  · rintro ⟨i, equal⟩
    have row := (M.pair_mem_binaryRowNameGraph I C one (function.value i) _).2 ⟨range i, rfl⟩
    refine ⟨i.val, subset i.property, (M.binaryRowName I C one (function.value i)).val,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨subset i.property, pair_second_mem_doubleUnion row, function.value i, range i,
          function.value_entry i, row⟩, ?_⟩
    rwa [Name.check_code_eq] at equal

theorem internalRowTupleCode_eq {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (C : ZFSet.{u}) (hL : s.carrier ∈ M.sets)
    {mu δ f : ZFSet.{u}} (function : FunctionGraphOn δ f) (subset : δ ⊆ mu)
    (positions : δ.toSet → {i : L // i ≠ ⊥})
    (values : ∀ i, function.value i = s.encode (positions i).val) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    rowTupleCode (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows f = (M.internalRowTupleName s C hL δ positions).val := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  have range (i : δ.toSet) : function.value i ∈ s.nonbottom.carrier := by
    rw [values i]
    exact s.nonbottom.encode_mem (positions i)
  have eq := M.binaryRowTupleCode_eq (C := C) ⊤ function subset range
  dsimp only at eq
  have names : (fun i => M.binaryRowName s.nonbottom.carrier C ⊤ (function.value i)) =
      (fun i => M.internalRowName s C hL (positions i)) := by
    funext i
    rw [values i]
    rfl
  exact eq.trans (congrArg Subtype.val (congrArg (Name.indexedTuple ⊤ δ) names))

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRowTermSetNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L]

theorem rowPositionSequence_decode (s : Presentation L)
    (hL : s.carrier ∈ M.sets) {mu f : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu)
    (member : f ∈ M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu) :
    f ∈ M.sets ∧ ∃ δ ∈ M.sets, ordinalSetProperty δ ∧ δ ⊆ mu ∧
      ∃ function : FunctionGraphOn δ f, ∃ positions : δ.toSet → {i : L // i ≠ ⊥},
        ∃ D : L, (∀ i, function.value i = s.encode (positions i).val) ∧
          ∀ i, (positions i).val ≤ D := by
  obtain ⟨hf, δ, hδ, ordδ, subδ, fn, d, hd, _, bounds⟩ :=
    M.rowPositionSequence_data hL hmu ordinal member
  let function : FunctionGraphOn δ f := ⟨s.nonbottom.carrier, fn⟩
  have range (i : δ.toSet) : function.value i ∈ s.nonbottom.carrier :=
    (ZFSet.pair_mem_prod.1 (fn.1 (function.value_entry i))).2
  have each (i : δ.toSet) : ∃ x : {i : L // i ≠ ⊥}, s.encode x.val = function.value i :=
    (s.nonbottom.mem_carrier (function.value i)).1 (range i)
  let positions (i : δ.toSet) : {i : L // i ≠ ⊥} := Classical.choose (each i)
  have values (i : δ.toSet) : function.value i = s.encode (positions i).val :=
    (Classical.choose_spec (each i)).symm
  obtain ⟨D, rfl⟩ := (s.mem_carrier d).1 hd
  refine ⟨hf, δ, hδ, ordδ, subδ, function, positions, D, values, ?_⟩
  intro i
  have bound := bounds i.val (function.value i) (function.value_entry i)
  rw [values i] at bound
  exact (s.pair_mem_conditionOrder (positions i).val D).1 bound

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem binaryRowTupleCode_action {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    ∀ (g : G) (f : ZFSet.{u}) (τ : Name c), f ∈ S →
      τ.val = rowTupleCode (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows f →
      rowPositionSequenceAction a s g mu f ∈ S ∧
        (act.act c g τ).val = rowTupleCode (c.encode ⊤) mu s.nonbottom.carrier
          (⋃₀ ⋃₀ rows) rows (rowPositionSequenceAction a s g mu f) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  dsimp only
  intro g f τ hf equal
  obtain ⟨_, δ, _, _, subset, function, positions, _, values, _⟩ :=
    M.rowPositionSequence_decode s hL hmu ordinal hf
  have original : ZFSet.IsFunc δ s.nonbottom.carrier f := by
    refine ⟨?_, function.to_isFunc.2⟩
    intro z hz
    obtain ⟨i, hi, y, rfl⟩ := function.shape z hz
    have value := (function.value_eq_of_entry ⟨i, hi⟩ hz).symm.trans (values ⟨i, hi⟩)
    exact ZFSet.pair_mem_prod.2 ⟨hi, value.symm ▸ s.nonbottom.encode_mem (positions ⟨i, hi⟩)⟩
  let moved := rowPositionSequenceAction a s g mu f
  have hmoved := M.rowPositionSequenceAction_mem a s b pairing unions powers separation
    hL hG graph hmu ordinal g hf
  let movedFunction : FunctionGraphOn δ moved :=
    ⟨s.nonbottom.carrier, rowPositionSequenceAction_function a s g subset original⟩
  have movedValues (i : δ.toSet) :
      movedFunction.value i = s.encode (a.nonbottom.iso g (positions i)).val := by
    apply movedFunction.value_eq_of_entry
    apply (pair_mem_rowPositionSequenceAction a s g mu f i.val (positions i)).2
    refine ⟨subset i.property, ?_⟩
    rw [← values i]
    exact function.value_entry i
  have actual : τ = M.internalRowTupleName s C hL δ positions :=
    Subtype.ext (equal.trans (M.internalRowTupleCode_eq s C hL function subset positions values))
  refine ⟨hmoved, ?_⟩
  rw [actual, M.internalRowTupleName_action a s b C pairing unions powers separation infinite
    hL hC hG graph]
  exact (M.internalRowTupleCode_eq s C hL movedFunction subset
    (fun i => a.nonbottom.iso g (positions i)) movedValues).symm

theorem binaryLiftedRowTupleFamily_action {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ (valid : ∀ z ∈ T, IsName c z) (g : G) (f : ZFSet.{u}) (τ : Name c.pairEmpty),
      ZFSet.pair f τ.val ∈ liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
        (⋃₀ ⋃₀ rows) rows S valid →
      ZFSet.pair (rowPositionSequenceAction a s g mu f) (act.act c.pairEmpty g τ).val ∈
        liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
          (⋃₀ ⋃₀ rows) rows S valid := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid g f τ entry
  obtain ⟨hf, σ, source, lifted⟩ := (pair_mem_liftedRowTupleFamily c (c.encode ⊤) mu
    s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid f τ.val).1 entry
  have moved := M.binaryRowTupleCode_action a s b C pairing unions powers separation infinite
    hL hC hG graph hmu ordinal g f σ hf source
  have same : τ = Name.presentationEquiv c c.pairEmpty σ := Subtype.ext lifted
  apply (pair_mem_liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
    (⋃₀ ⋃₀ rows) rows S valid _ _).2
  refine ⟨moved.1, act.act c g σ, moved.2, ?_⟩
  rw [same, act.act_presentationEquiv]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_StructuralPreparationSourceImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

variable (G nodes nodeOrder basis T T2 : ZFSet.{u})

theorem structuralAssignmentActionGraph_branch_entry
    (nodeAction : ZFSet.{u}) {stages history level P order top action x : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (member : x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T)
    (g y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history ↔
        g ∈ G ∧ ZFSet.pair x y ∈ M.rawStageRefinementAssignmentActionGraph g P order top action
          G nodes nodeOrder nodeAction basis T T2 level := by
  rw [M.pair_mem_structuralAssignmentActionGraph]
  constructor
  · rintro ⟨hg, other, _ho, P', order', top', action', stored', edge⟩
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P' order' top' action'
        G nodes nodeOrder nodeAction basis T T2 other edge)
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :=
      M.structuralAssignment_branch_unique G nodes nodeOrder basis T T2 function stored stored' member bounds.1
    exact ⟨hg, edge⟩
  · rintro ⟨hg, edge⟩
    exact ⟨hg, level, function.pair_source stored, P, order, top, action, stored, edge⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable {G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}}
variable (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
variable (hna : nodeAction ∈ M.sets) (hb : basis ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)

include pairing unions powers separation collection hG hn hno hna hb hT hT2 hs hh in
theorem structuralAssignmentImage_mem {g A : ZFSet.{u}} (hg : g ∈ M.sets) (hA : A ∈ M.sets) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g A ∈ M.sets := by
  have hJ := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![G,nodes,nodeOrder,basis,T,T2,stages,history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb (Fin.cases hT
      (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact M.relationImage_mem separation hA hJ
    (M.structuralAssignmentSection_mem pairing unions powers separation collection
      hG hn hno hna hb hT hT2 hs hh hg)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
variable {stages history level P order top action : ZFSet.{u}}
variable (function : FunctionGraphOn stages history)
variable (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
include function stored

theorem structuralAssignmentActionGraph_branch_iff {g x y : ZFSet.{u}}
    (edge : ZFSet.pair (ZFSet.pair g x) y ∈
      M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history) :
    x ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T ↔
    y ∈ stageOneAssignments
      (M.rawRefinementFormulaData P order top action G nodes nodeOrder basis T T2 level 0) T := by
  constructor
  · intro member
    have branch := (M.structuralAssignmentActionGraph_branch_entry G nodes nodeOrder basis T T2
      nodeAction function stored member g y).1 edge |>.2
    exact (ZFSet.pair_mem_prod.1 (M.rawStageRefinementAssignmentActionGraph_branch_bound
      g P order top action G nodes nodeOrder nodeAction basis T T2 level branch)).2
  · intro member
    obtain ⟨_, other, _, P', order', top', action', stored', branch⟩ :=
      (M.pair_mem_structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2
        stages history g x y).1 edge
    have bounds := ZFSet.pair_mem_prod.1
      (M.rawStageRefinementAssignmentActionGraph_branch_bound g P' order' top' action'
        G nodes nodeOrder nodeAction basis T T2 other branch)
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := M.structuralAssignment_branch_unique
      G nodes nodeOrder basis T T2 function stored stored' member bounds.2
    exact bounds.1

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (level T T2 : ZFSet.{u})
variable (system : RefinementStageSystem M a s t b d base directed level T T2)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
include system pairing unions powers separation collection carrier order group nodes supports hLevel hT

theorem structuralAssignmentImage_decode
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (h : G) (A sharedIdx rawU rawW : ZFSet.{u})
    (index : sharedIdx ∈ M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : rawU ∈ T) (hw : rawW ∈ T)
    (member : stageOneAssignment sharedIdx rawU rawW ∈
      M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) A) :
    ∃ (C E : L) (U Rf Rc u w : (M.nameDomain s).names),
      refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices a s b d level T T2 system.valid1 ∧
      u.val.val ∈ T ∧ w.val.val ∈ T ∧
      stageOneAssignment
        (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val ∈ A ∧
      sharedIdx = refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
        (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val ∧
      rawU = (a.act s h u.val).val ∧ rawW = (a.act s h w.val).val ∧
      ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
        (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val)) (stageOneAssignment sharedIdx rawU rawW) ∈
        M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history := by
  obtain ⟨x, source, edge⟩ := (M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
    (t.encode h) A _).1 member
  have dataEq := M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps level T T2 system.valid1 system.valid2
  have target : stageOneAssignment sharedIdx rawU rawW ∈ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
        t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level 0) T := by
    rw [dataEq]
    exact (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨index, hu, hw⟩
  have branchMember := (M.structuralAssignmentActionGraph_branch_iff t.carrier b.carrier
    b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
    function stored edge).2 target
  have original := branchMember
  rw [dataEq] at original
  obtain ⟨idx, hi, originalU, hOriginalU, originalW, hOriginalW, rfl⟩ :=
    (mem_stageOneAssignments _ _ x).1 original
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T T2 system.valid1 system.valid2 hi
  let u : (M.nameDomain s).names :=
    ⟨⟨originalU, system.valid1 originalU hOriginalU⟩, M.transitive hT hOriginalU⟩
  let w : (M.nameDomain s).names :=
    ⟨⟨originalW, system.valid1 originalW hOriginalW⟩, M.transitive hT hOriginalW⟩
  have branch := ((M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored
    branchMember (t.encode h) (stageOneAssignment sharedIdx rawU rawW)).1 edge).2
  rw [M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers separation collection
    carrier group nodes order system.inputs.condition_maps system.inputs.node_maps supports level T T2
    hLevel hT system.valid1 system.valid2 system.inputs.terms_closed system.inputs.pairs_closed
    system.inputs.family_ground system.indices.index_ground h] at branch
  have moved := (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1
    system.valid2 system.inputs.terms_closed t pairing unions powers separation collection carrier
    order system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
    h C E U Rf Rc u.val w.val hi hOriginalU hOriginalW _).1 branch
  obtain ⟨sameIndex, sameU, sameW⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 moved
  exact ⟨C, E, U, Rf, Rc, u, w, hi, hOriginalU, hOriginalW, source,
    sameIndex, sameU, sameW, edge⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedLargerCutTests
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
open scoped ZFSet
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_index_mem_history :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ z ∈ M.niceRefinementIndices act lower b d alpha T T2 valid,
      z ∈ refinementDataHistoryIndices stages packed := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
  dsimp only
  intro z hz
  exact (mem_refinementDataHistoryIndices stages packed z).2
    ⟨alpha, member, M.refinementLevelFormulaData act lower b d alpha T T2 valid, entry, hz⟩

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementDataBoundActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {L G : Type u} [PartialOrder L] [OrderBot L] [Group G]

theorem RowPositionBound.action (a : PosetAction G L) (s : Presentation L) (g : G)
    {mu f : ZFSet.{u}} {D : L}
    (bound : RowPositionBound mu s.nonbottom.carrier s.conditionOrder f (s.encode D)) :
    RowPositionBound mu s.nonbottom.carrier s.conditionOrder
      (rowPositionSequenceAction a s g mu f) (s.encode (a.iso g D)) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi, _, _, x, hx, rfl, _, _⟩ :=
      (mem_relationCompose _ _ _ _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hi, hx⟩
  · intro i x entry
    obtain ⟨_, _, y, hy, original, moved⟩ :=
      (pair_mem_relationCompose _ _ _ _ _ i x).1 entry
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
    obtain ⟨v, hv⟩ := (s.nonbottom.mem_graph s.nonbottom (a.nonbottom.iso g) _).1 moved
    obtain ⟨same, value⟩ := ZFSet.pair_inj.1 hv
    have equal : v = y := s.nonbottom.injective same
    have lower := (s.pair_mem_conditionOrder y.val D).1 (bound.2 i _ original)
    have result := (s.pair_mem_conditionOrder (a.iso g y.val) (a.iso g D)).2
      ((a.iso g).monotone lower)
    rw [equal] at value
    exact value ▸ result

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

theorem refinementDataBound_act
    (I T S mu tuples A movedA level : ZFSet.{u}) (g : G) (C E D : L)
    (U Rf Rc u w : Name s)
    (tupleAction : ∀ f ∈ S, ∀ tau : Name s, ZFSet.pair f tau.val ∈ tuples →
      rowPositionSequenceAction d b g mu f ∈ S ∧
      ZFSet.pair (rowPositionSequenceAction d b g mu f) (a.act s g tau).val ∈ tuples)
    (bound : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val Rf.val Rc.val) u.val w.val)
      (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu b.nonbottom.carrier b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (movedMember : stageOneAssignment
      (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
        (a.act s g U).val (a.act s g Rf).val (a.act s g Rc).val)
      (a.act s g u).val (a.act s g w).val ∈ movedA)
    (movedIndex : refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U).val (a.act s g Rf).val (a.act s g Rc).val ∈ I)
    (movedU : (a.act s g u).val ∈ T) (movedW : (a.act s g w).val ∈ T) :
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
        (a.act s g U).val (a.act s g Rf).val (a.act s g Rc).val)
      (a.act s g u).val (a.act s g w).val) (b.encode (d.iso g D)) ∈
      stageOneDataBounds movedA I T S b.carrier mu b.nonbottom.carrier b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples := by
  obtain ⟨_, _, _, _, _, rawE, _, fu, hfu, fw, hfw, anchor, lower,
      tupleU, tupleW, boundU, boundW⟩ :=
    (stageOneDataBounds_assignment_entry A I T S b.carrier mu b.nonbottom.carrier
      b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples _ u.val w.val (b.encode D)).1 bound
  have same : rawE = b.encode E :=
    ((refinementIndexFieldGraph_entry I b.carrier
      ![level, b.encode C, b.encode E, U.val, Rf.val, Rc.val] 2 rawE).1 anchor).2.2
  subst rawE
  obtain ⟨hfuMoved, tupleUMoved⟩ := tupleAction fu hfu u tupleU
  obtain ⟨hfwMoved, tupleWMoved⟩ := tupleAction fw hfw w tupleW
  refine (stageOneDataBounds_assignment_entry movedA I T S b.carrier mu b.nonbottom.carrier
    b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples _ _ _ _).2
    ⟨movedMember, b.encode_mem _, movedIndex, movedU, movedW,
      b.encode (d.iso g E), b.encode_mem _, rowPositionSequenceAction d b g mu fu, hfuMoved,
      rowPositionSequenceAction d b g mu fw, hfwMoved, ?_, ?_,
      tupleUMoved, tupleWMoved, boundU.action d b g, boundW.action d b g⟩
  · exact (refinementIndexFieldGraph_entry I b.carrier
      ![level, b.encode (d.iso g C), b.encode (d.iso g E),
        (a.act s g U).val, (a.act s g Rf).val, (a.act s g Rc).val] 2 _).2
      ⟨movedIndex, b.encode_mem _, rfl⟩
  · exact (b.pair_mem_conditionOrder (d.iso g E) (d.iso g D)).2
      ((d.iso g).monotone ((b.pair_mem_conditionOrder E D).1 lower))

end PartitionPilot.Forcing

end

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

theorem semanticStructuralPrefix_assignmentImage_decode :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    ∀ (h : G) (A sharedIdx rawU rawW : ZFSet.{u}), sharedIdx ∈ fields 0 →
      rawU ∈ T → rawW ∈ T →
      stageOneAssignment sharedIdx rawU rawW ∈
        M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) A →
    ∃ (C E : L) (U Rf Rc u w : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ fields 0 ∧
      u.val.val ∈ T ∧ w.val.val ∈ T ∧
      stageOneAssignment
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val ∈ A ∧
      sharedIdx = refinementIndexCode alpha (b.encode (d.iso h C)) (b.encode (d.iso h E))
        ((act).act lower h U.val).val ((act).act lower h Rf.val).val ((act).act lower h Rc.val).val ∧
      rawU = ((act).act lower h u.val).val ∧ rawW = ((act).act lower h w.val).val ∧
      ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val)) (stageOneAssignment sharedIdx rawU rawW) ∈
        M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have orderGround : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  obtain ⟨stage, stored⟩ := trace.1.total member
  have same := (trace.2 alpha member stage stored).trans
    (M.semanticStructuralPrefix_stageCode c a t b d base directed T T2 rowTop pairing unions powers
      separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps
      supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows
      hh ordinal trace hAlpha cutOrdinal subset)
  have exactStored : ZFSet.pair alpha
      (forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t))
      ∈ history := same ▸ stored
  dsimp only
  intro h A sharedIdx rawU rawW index hu hw imageMember
  exact M.structuralAssignmentImage_decode act lower t b d base directed alpha T T2 system
    pairing unions powers separation collection hQ orderGround group nodes supports hAlpha hT
    trace.1 exactStored h A sharedIdx rawU rawW index hu hw imageMember

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L] [OrderBot L]
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

theorem semanticStructuralAssignmentImage_dataBound
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (S mu tuples : ZFSet.{u}) (hS : S ∈ M.sets) (hmu : mu ∈ M.sets)
    (hTuples : tuples ∈ M.sets)
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (tupleAction : ∀ g f, f ∈ S → ∀ tau : Name c.pairEmpty,
      ZFSet.pair f tau.val ∈ tuples →
      rowPositionSequenceAction d b g mu f ∈ S ∧
      ZFSet.pair (rowPositionSequenceAction d b g mu f) (a.act c.pairEmpty g tau).val ∈ tuples) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let I := refinementDataHistoryIndices stages packed
    let anchors := refinementIndexFieldGraph I b.carrier 2
    ∀ (g : G) (D : L) (A : ZFSet.{u}), A ∈ M.sets →
      (∀ z ∈ A, ZFSet.pair z (b.encode D) ∈
        stageOneDataBounds A I T S b.carrier mu b.nonbottom.carrier b.conditionOrder anchors tuples) →
    let movedA := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A
    movedA ∈ M.sets ∧
      stageOneDataBounds movedA I T S b.carrier mu b.nonbottom.carrier b.conditionOrder anchors tuples ∈ M.sets ∧
      ∀ z ∈ movedA, ZFSet.pair z (b.encode (d.iso g D)) ∈
        stageOneDataBounds movedA I T S b.carrier mu b.nonbottom.carrier b.conditionOrder anchors tuples := by
  intro packed I anchors g D A hA bound movedA
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hI := M.refinementDataHistoryIndices_mem pairing unions powers separation hs hPacked
  have hMoved := M.structuralAssignmentImage_mem pairing unions powers separation collection
    group nodes nodeOrder nodeAction supports hT hT2 hs hh (M.transitive group (t.encode_mem g)) hA
  refine ⟨hMoved, M.stageOneDataBounds_mem pairing unions powers separation hMoved hI hT hS nodes hmu
    (M.nonbottom_carrier_mem b separation nodes) nodeOrder
    (M.refinementIndexFieldGraph_mem pairing unions powers separation hI nodes 2) hTuples, ?_⟩
  intro z hz
  obtain ⟨x, hx, edge⟩ := (M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A z).1 hz
  obtain ⟨_, alpha, member, rawP, rawOrder, rawTop, rawAction, stored, branch⟩ :=
    (M.pair_mem_structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) x z).1 edge
  have targetBranch := (ZFSet.pair_mem_prod.1
    (M.rawStageRefinementAssignmentActionGraph_branch_bound (t.encode g) rawP rawOrder rawTop rawAction
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
      T T2 alpha branch)).2
  obtain ⟨idx, idxRaw, rawU, hu, rawW, hw, rfl⟩ := (mem_stageOneAssignments _ _ z).1 targetBranch
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have hAlpha := M.transitive hs member
  have cutOrdinal := ordinalSetProperty_member ordinal member
  have subset := (And.left ordinal) alpha member
  let restricted := run.carriers.restrict cutOrdinal subset
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    restricted cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed))
  let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let valid := M.refinementHistoryRowNameFamily_valid c restricted cutOrdinal carrier T valid1
  have actualEntry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have rawEntry : ZFSet.pair alpha (refinementFormulaDataCode
      (M.rawRefinementFormulaData rawP rawOrder rawTop rawAction t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 alpha)) ∈ packed :=
    (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
      ⟨member, rawP, rawOrder, rawTop, rawAction, stored, rfl⟩
  have sameData : M.rawRefinementFormulaData rawP rawOrder rawTop rawAction t.carrier b.carrier
      b.conditionOrder (supportBasisCode b t d.principalFix) T T2 alpha =
      M.refinementLevelFormulaData act lower b d alpha T T2 valid :=
    refinementFormulaDataCode_injective (run.carriers.data.function.unique rawEntry actualEntry)
  have idxNice : idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid := by
    rw [sameData] at idxRaw
    exact idxRaw
  obtain ⟨C, E, U, Rf, Rc, u, w, _sourceIndex, _sourceU, _sourceW, source,
      sameIndex, sameU, sameW, _sourceEdge⟩ :=
    M.semanticStructuralPrefix_assignmentImage_decode c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member g A idx rawU rawW idxNice hu hw hz
  have idxWhole := M.semanticStructuralPrefix_index_mem_history c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member idx idxNice
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  have tupleMoved : ∀ f ∈ S, ∀ tau : Name lower, ZFSet.pair f tau.val ∈ tuples →
      rowPositionSequenceAction d b g mu f ∈ S ∧
      ZFSet.pair (rowPositionSequenceAction d b g mu f) (act.act lower g tau).val ∈ tuples := by
    intro f hf tau entry
    let original : Name c.pairEmpty := ⟨tau.val, valid1 tau.val (range f tau.val entry)⟩
    have same : M.refinementHistoryRowNameLift c restricted cutOrdinal carrier original = tau :=
      Subtype.ext (M.refinementHistoryRowNameLift_val c restricted cutOrdinal carrier original)
    have moved := tupleAction g f hf original entry
    refine ⟨moved.1, ?_⟩
    rw [← same, M.refinementHistoryRowNameLift_act c restricted cutOrdinal carrier
      a act image coordinates emptyImage, M.refinementHistoryRowNameLift_val]
    exact moved.2
  have result := refinementDataBound_act act lower b d I T S mu tuples A movedA alpha g C E D
    U.val Rf.val Rc.val u.val w.val tupleMoved (bound _ source)
    (by rwa [← sameIndex, ← sameU, ← sameW])
    (by rwa [← sameIndex]) (by rwa [← sameU]) (by rwa [← sameW])
  rw [sameIndex, sameU, sameW]
  exact result

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBinaryRowStructuralDataBoundActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

include collection order nodeMaps supports

theorem binaryRowStructuralAssignmentImage_dataBound_oai {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (muOrdinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
      (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
      (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
      (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
      (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
      (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
      (_stagesOrdinal : ordinalSetProperty stages)
      (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let _carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let _forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let _forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let _omega := M.omega_mem separation infinite
    let _topMem := c.encode_mem ⊤
    let _topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared stages history
    let I := refinementDataHistoryIndices stages packed
    let anchors := refinementIndexFieldGraph I s.carrier 2
    ∀ (g : G) (D : L) (A : ZFSet.{u}), A ∈ M.sets →
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈ stageOneDataBounds A I lifted S s.carrier mu
        s.nonbottom.carrier s.conditionOrder anchors tuples) →
    let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode g) A
    movedA ∈ M.sets ∧
      stageOneDataBounds movedA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∈ M.sets ∧
      ∀ z ∈ movedA, ZFSet.pair z (s.encode (a.iso g D)) ∈
        stageOneDataBounds movedA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace coordinates two carrier forcingOrder
    forcingAction omega topMem topRows packed I anchors
  have hNonbottom := M.nonbottom_carrier_mem s separation hL
  have hS := M.rowPositionSequences_mem pairing unions powers separation hL order hNonbottom hmu
  have hTuples := M.binaryLiftedRowTupleFamily_mem pairing unions powers separation collection
    infinite hL order hNonbottom hC hmu ⊤ valid
  exact M.semanticStructuralAssignmentImage_dataBound c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace S mu tuples hS hmu hTuples
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun g f hf tau entry => ⟨M.rowPositionSequenceAction_mem a s b pairing unions powers separation
      hL hG graph hmu muOrdinal g hf,
      M.binaryLiftedRowTupleFamily_action a s b C pairing unions powers separation infinite
        hL hC hG graph hmu muOrdinal valid g f tau entry⟩)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowStructuralAssignmentImage_dataBound_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.binaryRowStructuralAssignmentImage_dataBound_oai.{u}
