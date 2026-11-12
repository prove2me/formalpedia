-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralCrossStagePower_hs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:31:39.000963+00:00
-- url     : https://prove2.me/submissions/b8a366f9-95f5-47d6-9a9e-fc216fe17c78

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_FinitePrincipalNameSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower)
variable (inclusion : Lower → Upper) (J : ZFSet.{u}) (tau : Name s)

theorem pair_mem_crossStageMembershipCode (sigma : Name t) (p : Lower) :
    ZFSet.pair sigma.val (t.encode p) ∈ crossStageMembershipCode s t inclusion J tau ↔
      sigma.val ∈ J ∧ ForcesMem (inclusion p) (rename s inclusion sigma) tau := by
  change (_ ∈ ZFSet.sep _ _) ↔ _
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨bound, nu, q, equal, forced⟩
    obtain ⟨names, conditions⟩ := ZFSet.pair_inj.1 equal
    have sameName : sigma = nu := Subtype.ext names
    have sameCondition : p = q := t.injective conditions
    exact ⟨(ZFSet.pair_mem_prod.1 bound).1, sameName.symm ▸ sameCondition.symm ▸ forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨member, t.encode_mem p⟩, sigma, p, rfl, forced⟩

theorem entry_crossStageMembershipName (valid : ∀ z ∈ J, IsName t z)
    (sigma : Name t) (p : Lower) :
    Entry sigma (crossStageMembershipName s t inclusion J valid tau) p ↔
      sigma.val ∈ J ∧ ForcesMem (inclusion p) (rename s inclusion sigma) tau :=
  pair_mem_crossStageMembershipCode s t inclusion J tau sigma p

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_PairFamilyEvaluation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} {s : Presentation P}

variable {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

theorem orderedPairNameFamily_hs {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z)
    (childrenX : ∀ τ : Name s, τ.val ∈ X → HereditarilySymmetric a s F τ)
    (childrenY : ∀ τ : Name s, τ.val ∈ Y → HereditarilySymmetric a s F τ) :
    ∀ τ : Name s, τ.val ∈ orderedPairNameFamily (s.encode ⊤) X Y →
      HereditarilySymmetric a s F τ := by
  intro τ hτ
  obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y τ.val).1 hτ
  let σ : Name s := ⟨x, validX x hx⟩
  let ν : Name s := ⟨y, validY y hy⟩
  have same : τ = Name.orderedPair ⊤ σ ν :=
    Subtype.ext (equal.trans (Name.orderedPair_code ⊤ σ ν).symm)
  rw [same]
  exact (childrenX σ hx).orderedPair (childrenY ν hy)

theorem orderedPairNameFamily_closed {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z)
    (closedX : ∀ g (τ : Name s), τ.val ∈ X → (a.act s g τ).val ∈ X)
    (closedY : ∀ g (τ : Name s), τ.val ∈ Y → (a.act s g τ).val ∈ Y) :
    ∀ g (τ : Name s), τ.val ∈ orderedPairNameFamily (s.encode ⊤) X Y →
      (a.act s g τ).val ∈ orderedPairNameFamily (s.encode ⊤) X Y := by
  intro g τ hτ
  obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y τ.val).1 hτ
  let σ : Name s := ⟨x, validX x hx⟩
  let ν : Name s := ⟨y, validY y hy⟩
  have same : τ = Name.orderedPair ⊤ σ ν :=
    Subtype.ext (equal.trans (Name.orderedPair_code ⊤ σ ν).symm)
  have acted : a.act s g τ = Name.orderedPair ⊤ (a.act s g σ) (a.act s g ν) := by
    rw [same]
    change Name.rename s (a.iso g) _ = _
    rw [Name.rename_orderedPair, (a.iso g).map_top]
    rfl
  exact (mem_orderedPairNameFamily _ X Y _).2
    ⟨(a.act s g σ).val, closedX g σ hx, (a.act s g ν).val, closedY g ν hy,
      (congrArg Subtype.val acted).trans (Name.orderedPair_code ⊤ _ _)⟩

theorem iteratedPairNameFamily_hs {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) (n : Nat) :
    ∀ τ : Name s, τ.val ∈ iteratedPairNameFamily (s.encode ⊤) T n →
      HereditarilySymmetric a s F τ := by
  induction n with
  | zero => exact children
  | succ n ih =>
    exact orderedPairNameFamily_hs a F
      (iteratedPairNameFamily_valid ⊤ valid n) valid ih children

theorem iteratedPairNameFamily_closed {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T) (n : Nat) :
    ∀ g (τ : Name s), τ.val ∈ iteratedPairNameFamily (s.encode ⊤) T n →
      (a.act s g τ).val ∈ iteratedPairNameFamily (s.encode ⊤) T n := by
  induction n with
  | zero => exact closed
  | succ n ih =>
    exact orderedPairNameFamily_closed a
      (iteratedPairNameFamily_valid ⊤ valid n) valid ih closed

end PartitionPilot.Forcing



end

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

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
include hs hh ordinal trace

variable {alpha : ZFSet.{u}} (hAlpha : alpha ∈ M.sets)
variable (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hAlpha cutOrdinal subset

omit hs in
theorem semanticStructuralPrefixPower_family (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    let X := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    ∃ _valid : ∀ z ∈ X, IsName (SetMembers.presentation LQ) z,
      X ∈ M.sets ∧
      (∀ g (tau : Name (SetMembers.presentation LQ)), tau.val ∈ X →
        ((lowerAct).act (SetMembers.presentation LQ) g tau).val ∈ X) ∧
      (∀ tau : Name (SetMembers.presentation LQ), tau.val ∈ X →
        HereditarilySymmetric lowerAct (SetMembers.presentation LQ)
          (d.principalSupportFamily base directed) tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨valid, closed, symmetric⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a lowerAct image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  have topEq := M.refinementHistoryDecodedTop_eq c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  have validPower := iteratedPairNameFamily_valid ⊤ valid n
  have closedPower := iteratedPairNameFamily_closed lowerAct valid closed n
  have symmetricPower := iteratedPairNameFamily_hs lowerAct
    (d.principalSupportFamily base directed) valid symmetric n
  rw [topEq] at validPower closedPower symmetricPower
  exact ⟨validPower, M.iteratedPairNameFamily_mem pairing unions powers separation
    (M.orderedPair_mem pairing (M.transitive carrier topMem) (M.empty_mem ⟨T, hT⟩)) hT n,
    closedPower, symmetricPower⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_CrossStageMembershipNameActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable {G : Type v} [Group G]
variable (upper : PosetAction G P) (lower : PosetAction G Q)
variable (s : Presentation P) (t : Presentation Q) (inclusion : Q → P)
variable (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName t z)
variable (equivariant : ∀ g p, inclusion (lower.iso g p) = upper.iso g (inclusion p))
variable (closed : ∀ g (sigma : Name t), sigma.val ∈ J → (lower.act t g sigma).val ∈ J)
include equivariant closed

theorem crossStageMembershipName_act (g : G) (tau : Name s) :
    lower.act t g (crossStageMembershipName s t inclusion J valid tau) =
      crossStageMembershipName s t inclusion J valid (upper.act s g tau) := by
  apply Name.ext
  intro sigma p
  obtain ⟨sigma, rfl⟩ := (lower.nameEquiv t g).surjective sigma
  obtain ⟨p, rfl⟩ := (lower.iso g).surjective p
  change Entry (lower.act t g sigma)
    (lower.act t g (crossStageMembershipName s t inclusion J valid tau)) (lower.iso g p) ↔
    Entry (lower.act t g sigma)
      (crossStageMembershipName s t inclusion J valid (upper.act s g tau)) (lower.iso g p)
  rw [lower.entry_act, entry_crossStageMembershipName, entry_crossStageMembershipName]
  have member : (lower.act t g sigma).val ∈ J ↔ sigma.val ∈ J := by
    constructor
    · intro h
      have back := closed g⁻¹ (lower.act t g sigma) h
      simpa only [lower.act_inv_left] using back
    · exact closed g sigma
  rw [member, equivariant,
    ← lower.act_rename_of_equivariant upper t s inclusion equivariant,
    upper.forcesMem_act_iff]

theorem crossStageMembershipName_stabilizer (tau : Name s) :
    upper.stabilizer s tau ≤
      lower.stabilizer t (crossStageMembershipName s t inclusion J valid tau) := by
  intro g fixed
  change upper.act s g tau = tau at fixed
  change lower.act t g (crossStageMembershipName s t inclusion J valid tau) = _
  rw [crossStageMembershipName_act upper lower s t inclusion J valid equivariant closed, fixed]

theorem crossStageMembershipName_nice (K : Subgroup G) (tau : Name s)
    (supported : K ≤ upper.stabilizer s tau) :
    NiceNameCode lower t J K (crossStageMembershipName s t inclusion J valid tau).val := by
  apply (niceNameCode_iff lower t _).2
  exact ⟨crossStageMembershipCode_subset s t inclusion J tau,
    supported.trans (crossStageMembershipName_stabilizer upper lower s t inclusion J valid
      equivariant closed tau)⟩

theorem crossStageMembershipName_hs (F : NormalSubgroupFamily G) (K : Subgroup G)
    (member : F.mem K)
    (children : ∀ sigma : Name t, sigma.val ∈ J → HereditarilySymmetric lower t F sigma)
    (tau : Name s) (supported : K ≤ upper.stabilizer s tau) :
    HereditarilySymmetric lower t F (crossStageMembershipName s t inclusion J valid tau) := by
  exact niceNameCode_hs lower t F member children
    (crossStageMembershipName_nice upper lower s t inclusion J valid equivariant closed
      K tau supported)

end PartitionPilot.Forcing.Name

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralRefinementNormalization
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

theorem semanticStructuralCrossStageName_nice :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName (SetMembers.presentation LQ) z),
      (∀ g (sigma : Name (SetMembers.presentation LQ)), sigma.val ∈ J →
        ((lowerAct).act (SetMembers.presentation LQ) g sigma).val ∈ J) →
      ∀ (K : Subgroup G) (tau : Name (SetMembers.presentation Q)),
        K ≤ (upperAct).stabilizer (SetMembers.presentation Q) tau →
        NiceNameCode lowerAct (SetMembers.presentation LQ) J K
          (Name.crossStageMembershipName (SetMembers.presentation Q)
            (SetMembers.presentation LQ) inc J valid tau).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro J valid closed K tau supported
  exact Name.crossStageMembershipName_nice upperAct lowerAct (SetMembers.presentation Q)
    (SetMembers.presentation LQ) inc J valid (fun g p => (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm) closed K tau supported

theorem semanticStructuralCrossStagePower_hs_oai :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (n : Nat) (K : Subgroup G), (d.principalSupportFamily base directed).mem K →
      ∀ tau : Name (SetMembers.presentation Q),
        K ≤ (upperAct).stabilizer (SetMembers.presentation Q) tau →
        let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
        ∃ valid : ∀ z ∈ J, IsName (SetMembers.presentation LQ) z,
          J ∈ M.sets ∧
          NiceNameCode lowerAct (SetMembers.presentation LQ) J K
            (Name.crossStageMembershipName (SetMembers.presentation Q)
              (SetMembers.presentation LQ) inc J valid tau).val ∧
          HereditarilySymmetric lowerAct (SetMembers.presentation LQ)
            (d.principalSupportFamily base directed)
            (Name.crossStageMembershipName (SetMembers.presentation Q)
              (SetMembers.presentation LQ) inc J valid tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro n K member tau supported
  obtain ⟨valid, ground, closed, children⟩ := M.semanticStructuralPrefixPower_family
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset n
  refine ⟨valid, ground, ?_, ?_⟩
  · exact M.semanticStructuralCrossStageName_nice c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice
      _ valid closed K tau supported
  · exact Name.crossStageMembershipName_hs upperAct lowerAct (SetMembers.presentation Q)
      (SetMembers.presentation LQ) inc _ valid (fun g p => (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm) closed
      (d.principalSupportFamily base directed) K member children tau supported

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralCrossStagePower_hs_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralCrossStagePower_hs_oai.{u}
