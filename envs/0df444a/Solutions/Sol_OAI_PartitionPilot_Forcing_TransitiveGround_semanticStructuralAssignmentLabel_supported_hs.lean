-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_supported_hs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:29:38.260497+00:00
-- url     : https://prove2.me/submissions/232dea76-d99a-42c4-abe0-84a318b926a8

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralAssignment_occurrence_fixed_index

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps
universe u v w
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

namespace HereditarilySymmetric
variable {a : PosetAction G P} {s : Presentation P} {F : NormalSubgroupFamily G}

theorem assemble {α : Type w} [Small.{u} α] (names : α → Name s) (conditions : α → P)
    (sym : F.mem (a.stabilizer s (Name.assemble names conditions)))
    (children : ∀ i, HereditarilySymmetric a s F (names i)) :
    HereditarilySymmetric a s F (Name.assemble names conditions) := by
  refine HereditarilySymmetric.mk sym ?_
  intro σ p entry
  obtain ⟨i, rfl, _⟩ := (Name.entry_assemble names conditions σ p).1 entry
  exact children i

theorem assemble_common [OrderTop P] {α : Type w} [Small.{u} α]
    (names : α → Name s) (children : ∀ i, HereditarilySymmetric a s F (names i))
    (K : Subgroup G) (hK : F.mem K) (fixed : ∀ g ∈ K, ∀ i, a.act s g (names i) = names i) :
    HereditarilySymmetric a s F (Name.assemble names (fun _ => ⊤)) := by
  apply assemble names (fun _ => ⊤) _ children
  apply F.upward hK
  intro g hg
  change Name.rename s (a.iso g) (Name.assemble names (fun _ => ⊤)) = _
  rw [Name.rename_assemble]
  have top : a.iso g ⊤ = ⊤ := (a.iso g).map_top
  simp only [top]
  apply congrArg (fun ns : α → Name s => Name.assemble ns (fun _ => ⊤))
  funext i
  exact fixed g hg i

theorem singleton [OrderTop P] {τ : Name s} (h : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.singleton ⊤ τ) :=
  assemble_common (fun _ : Unit => τ) (fun _ => h) (a.stabilizer s τ) h.symmetric
    (fun _ fixed _ => fixed)

theorem unorderedPair [OrderTop P] {σ τ : Name s}
    (hσ : HereditarilySymmetric a s F σ) (hτ : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.unorderedPair ⊤ σ τ) := by
  apply assemble_common (fun b : Bool => if b then σ else τ)
    (fun b => by cases b; exact hτ; exact hσ)
    (a.stabilizer s σ ⊓ a.stabilizer s τ) (F.inf hσ.symmetric hτ.symmetric)
  intro g fixed b
  cases b
  · exact fixed.2
  · exact fixed.1

theorem orderedPair [OrderTop P] {σ τ : Name s}
    (hσ : HereditarilySymmetric a s F σ) (hτ : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.orderedPair ⊤ σ τ) :=
  hσ.singleton.unorderedPair (hσ.unorderedPair hτ)

end HereditarilySymmetric
end PartitionPilot.Forcing


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
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

variable {G : Type v} [Group G] (a : PosetAction G P)

theorem refinementClass_support (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (R w : Name s) (K : Subgroup G)
    (relation : K ≤ a.stabilizer s R) (representative : K ≤ a.stabilizer s w) :
    K ≤ a.stabilizer s (refinementClass T valid R w) := by
  intro g hg
  change a.act s g _ = _
  rw [act_refinementClass a T valid closed, relation hg, representative hg]

theorem refinementClass_hs (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (children : ∀ z : Name s, z.val ∈ T → HereditarilySymmetric a s F z)
    (R w : Name s) (K : Subgroup G) (member : F.mem K)
    (relation : K ≤ a.stabilizer s R) (representative : K ≤ a.stabilizer s w) :
    HereditarilySymmetric a s F (refinementClass T valid R w) :=
  HereditarilySymmetric.mk
    (F.upward member (refinementClass_support a T valid closed R w K relation representative))
    (fun z p entry => children z ((entry_refinementClass T valid R w z p).1 entry).1)

end PartitionPilot.Forcing.Name



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundRefinementQuotientNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
include closed

theorem refinementClass_hs_of_hs (F : NormalSubgroupFamily G)
    (children : ∀ w : Name s, w.val ∈ T → HereditarilySymmetric a s F w)
    (R w : Name s) (relation : HereditarilySymmetric a s F R)
    (representative : HereditarilySymmetric a s F w) :
    HereditarilySymmetric a s F (refinementClass T valid R w) :=
  refinementClass_hs a F T valid closed children R w
    (a.stabilizer s R ⊓ a.stabilizer s w) (F.inf relation.symmetric representative.symmetric)
    (fun _ hg => hg.1) (fun _ hg => hg.2)

end PartitionPilot.Forcing.Name



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
variable (G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralAssignmentImage_domain_restrict {stages earlier history : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (subset : earlier ⊆ stages) (g A : ZFSet.{u}) :
    M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 earlier history g A =
      M.structuralAssignmentImage G nodes nodeOrder nodeAction basis T T2 stages history g
        (ZFSet.sep (fun x => x ∈ M.structuralAssignments G nodes nodeOrder basis T T2 earlier history) A) := by
  apply ZFSet.ext
  intro y
  rw [M.structuralAssignmentImage_entry, M.structuralAssignmentImage_entry]
  constructor
  · rintro ⟨x, hx, edge⟩
    obtain ⟨whole, source⟩ :=
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).1 edge
    exact ⟨x, ZFSet.mem_sep.2 ⟨hx, source⟩, whole⟩
  · rintro ⟨x, hx, edge⟩
    obtain ⟨member, source⟩ := ZFSet.mem_sep.1 hx
    exact ⟨x, member,
      (M.structuralAssignmentActionGraph_prefix_entry G nodes nodeOrder nodeAction basis T T2 function subset g x y).2
        ⟨edge, source⟩⟩

end PartitionPilot.Forcing.TransitiveGround



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralCutActions
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
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace hAlpha cutOrdinal subset

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

theorem semanticStructuralInclusion_equivariant :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (g : G) (p : SetMembers LQ), (upperAct).iso g (inc p) = inc ((lowerAct).iso g p) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro g p
  obtain ⟨r, A, _, code⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier T alpha (graphRestriction alpha packed)) (SetMembers.raw_mem p)
  have includeCode := (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation
    infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono
  have member := code ▸ SetMembers.raw_mem p
  have data := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
    ((M.mem_refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed) _).1 member).1).2.2.1
  have fixedCut := (run).carriers.data.prefix_assignments_cut subset data
  have equalImage := M.structuralAssignmentImage_domain_restrict t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 trace.1 subset (t.encode g) A
  rw [← M.structuralAssignments_cut_eq t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 subset, fixedCut] at equalImage
  apply SetMembers.raw_injective Q
  rw [M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace g (inc p) r A
      ((includeCode p).trans code),
    includeCode ((lowerAct).iso g p),
    M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset g p r A code]
  exact congrArg (ZFSet.pair (c.encode (a.iso g r))) equalImage.symm

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementAssignmentLabelActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} [PartialOrder P] [OrderTop P]
variable [PartialOrder Q] [OrderTop Q] {G : Type v} [Group G]
variable (a : PosetAction G P) (e : PosetAction G Q)
variable (s : Presentation P) (upper : Presentation Q) (incl : P → Q)
variable (equivariant : ∀ g p, incl (a.iso g p) = e.iso g (incl p))
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)

include equivariant closed

theorem act_refinementAssignmentLabel (g : G) (idx movedIdx : ZFSet.{u})
    (Rf Rc : Name s)
    (occurrences : ∀ (v w : Name s) (p : Q) (_hv : v.val ∈ T) (_hw : w.val ∈ T),
      (∃ row A, upper.encode (e.iso g p) = ZFSet.pair row A ∧
        stageOneAssignment movedIdx (a.act s g v).val (a.act s g w).val ∈ A) ↔
      (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A)) :
    e.act upper g (refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc) =
      refinementAssignmentLabel upper incl ⊤ T valid movedIdx (a.act s g Rf) (a.act s g Rc) := by
  have paired (v w : Name s) :
      e.act upper g (orderedPair ⊤ (rename upper incl (refinementClass T valid Rc v))
        (rename upper incl (refinementClass T valid Rf w))) =
      orderedPair ⊤ (rename upper incl (refinementClass T valid (a.act s g Rc) (a.act s g v)))
        (rename upper incl (refinementClass T valid (a.act s g Rf) (a.act s g w))) := by
    change rename upper (e.iso g) _ = _
    rw [rename_orderedPair, (e.iso g).map_top]
    change orderedPair ⊤ (e.act upper g _) (e.act upper g _) = _
    rw [a.act_rename_of_equivariant e s upper incl equivariant,
      a.act_rename_of_equivariant e s upper incl equivariant,
      act_refinementClass a T valid closed, act_refinementClass a T valid closed]
  apply ext
  intro sigma p
  obtain ⟨sigma, rfl⟩ := (e.nameEquiv upper g).surjective sigma
  obtain ⟨p, rfl⟩ := (e.iso g).surjective p
  change Entry (e.act upper g sigma)
      (e.act upper g (refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc)) (e.iso g p) ↔
    Entry (e.act upper g sigma)
      (refinementAssignmentLabel upper incl ⊤ T valid movedIdx (a.act s g Rf) (a.act s g Rc)) (e.iso g p)
  rw [e.entry_act, entry_refinementAssignmentLabel, entry_refinementAssignmentLabel]
  constructor
  · rintro ⟨v, w, hv, hw, literal, equal⟩
    refine ⟨a.act s g v, a.act s g w, closed g v hv, closed g w hw,
      (occurrences v w p hv hw).2 literal, ?_⟩
    exact (paired v w).symm.trans (congrArg (e.act upper g) equal)
  · rintro ⟨v, w, hv, hw, literal, equal⟩
    let oldV := a.act s g⁻¹ v
    let oldW := a.act s g⁻¹ w
    have oldVmem : oldV.val ∈ T := closed g⁻¹ v hv
    have oldWmem : oldW.val ∈ T := closed g⁻¹ w hw
    have vEq : a.act s g oldV = v := a.act_inv_right s g v
    have wEq : a.act s g oldW = w := a.act_inv_right s g w
    have oldLiteral := (occurrences oldV oldW p oldVmem oldWmem).1
      (by rw [vEq, wEq]; exact literal)
    refine ⟨oldV, oldW, oldVmem, oldWmem, oldLiteral, ?_⟩
    apply (e.nameEquiv upper g).injective
    change e.act upper g _ = e.act upper g sigma
    rw [paired, vEq, wEq]
    exact equal

theorem refinementAssignmentLabel_support (idx : ZFSet.{u}) (Rf Rc : Name s)
    (K : Subgroup G)
    (occurrences : ∀ g ∈ K, ∀ (v w : Name s) (p : Q) (_hv : v.val ∈ T) (_hw : w.val ∈ T),
      (∃ row A, upper.encode (e.iso g p) = ZFSet.pair row A ∧
        stageOneAssignment idx (a.act s g v).val (a.act s g w).val ∈ A) ↔
      (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A))
    (fine : K ≤ a.stabilizer s Rf) (coarse : K ≤ a.stabilizer s Rc) :
    K ≤ e.stabilizer upper (refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc) := by
  intro g hg
  change e.act upper g _ = _
  rw [act_refinementAssignmentLabel a e s upper incl equivariant T valid closed
    g idx idx Rf Rc (occurrences g hg), fine hg, coarse hg]

theorem refinementAssignmentLabel_hs (F : NormalSubgroupFamily G)
    (children : ∀ z : Name s, z.val ∈ T → HereditarilySymmetric a s F z)
    (idx : ZFSet.{u}) (Rf Rc : Name s) (K : Subgroup G) (member : F.mem K)
    (occurrences : ∀ g ∈ K, ∀ (v w : Name s) (p : Q) (_hv : v.val ∈ T) (_hw : w.val ∈ T),
      (∃ row A, upper.encode (e.iso g p) = ZFSet.pair row A ∧
        stageOneAssignment idx (a.act s g v).val (a.act s g w).val ∈ A) ↔
      (∃ row A, upper.encode p = ZFSet.pair row A ∧ stageOneAssignment idx v.val w.val ∈ A))
    (fine : K ≤ a.stabilizer s Rf) (coarse : K ≤ a.stabilizer s Rc)
    (fineHS : HereditarilySymmetric a s F Rf) (coarseHS : HereditarilySymmetric a s F Rc) :
    HereditarilySymmetric e upper F
      (refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc) := by
  refine HereditarilySymmetric.mk
    (F.upward member (refinementAssignmentLabel_support a e s upper incl equivariant T valid closed
      idx Rf Rc K occurrences fine coarse)) ?_
  intro sigma p entry
  obtain ⟨v, w, hv, hw, _literal, rfl⟩ :=
    (entry_refinementAssignmentLabel upper incl ⊤ T valid idx Rf Rc sigma p).1 entry
  exact ((refinementClass_hs_of_hs a T valid closed F children Rc v coarseHS (children v hv)).rename
    e upper incl equivariant).orderedPair
      ((refinementClass_hs_of_hs a T valid closed F children Rf w fineHS (children w hw)).rename
        e upper incl equivariant)

end PartitionPilot.Forcing.Name

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

theorem semanticStructuralAssignmentLabel_supported_hs_oai :
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
      d.principalFix E ≤ (upperAct).stabilizer upper label ∧
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
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have equivariant : ∀ g p, inc ((lowerAct).iso g p) = (upperAct).iso g (inc p) := fun g p =>
    (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm
  dsimp only
  intro C E U Rf Rc index
  obtain ⟨less, _domainCandidate, fineCandidate, coarseCandidate, _forced⟩ :=
    (system.indices.typed_entries C E U Rf Rc).1 index
  have fine : d.principalFix E ≤ (lowerAct).stabilizer lower Rf.val :=
    (d.principalFix_antitone less.le).trans
      ((M.name_mem_niceNameCandidates lowerAct lower T2 (d.principalFix C) Rf.val).1 fineCandidate).2.2
  have coarse : d.principalFix E ≤ (lowerAct).stabilizer lower Rc.val :=
    (d.principalFix_antitone less.le).trans
      ((M.name_mem_niceNameCandidates lowerAct lower T2 (d.principalFix C) Rc.val).1 coarseCandidate).2.2
  have occurrences := fun g (hg : g ∈ d.principalFix E) (v w : Name lower) (p : SetMembers Q)
      (hv : v.val ∈ T) (hw : w.val ∈ T) =>
    M.semanticStructuralAssignment_occurrence_fixed_index c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member g C E U Rf Rc v w index hv hw hg p
  refine ⟨Name.refinementAssignmentLabel_support lowerAct upperAct lower upper inc equivariant
    T valid system.inputs.terms_closed _ Rf.val Rc.val (d.principalFix E) occurrences fine coarse, ?_⟩
  exact Name.refinementAssignmentLabel_hs lowerAct upperAct lower upper inc equivariant T valid
    system.inputs.terms_closed (d.principalSupportFamily base directed) system.terms_hs _ Rf.val Rc.val
    (d.principalFix E) ⟨E, le_rfl⟩ occurrences fine coarse
    (system.second.candidate_hs C Rf.val fineCandidate) (system.second.candidate_hs C Rc.val coarseCandidate)

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_supported_hs_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralAssignmentLabel_supported_hs_oai.{u}
