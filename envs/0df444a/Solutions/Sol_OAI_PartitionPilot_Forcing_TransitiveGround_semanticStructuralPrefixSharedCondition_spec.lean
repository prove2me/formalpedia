-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixSharedCondition_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:30:38.85887+00:00
-- url     : https://prove2.me/submissions/995f60b0-7fd1-4a02-8889-760385223abf

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSharedConditionalNames
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

namespace Name
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem entry_sharedConditionName (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (sigma : Name s) (p : P) :
    Entry sigma (sharedConditionName D phi env i T valid) p ↔
      sigma.val ∈ T ∧ ∃ h : sigma ∈ D.names,
        Forces D (sharedConditionFormula phi i) (extend ⟨sigma, h⟩ env) p := by
  rw [sharedConditionName, entry_separationName]
  constructor
  · rintro ⟨r, entry, _, forced⟩
    exact ⟨((entry_familySet ⊤ T valid sigma r).1 entry).1, forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨⊤, (entry_familySet ⊤ T valid sigma ⊤).2 ⟨member, rfl⟩, le_top, forced⟩

theorem sharedConditionName_subset (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) :
    (sharedConditionName D phi env i T valid).val ⊆ ZFSet.prod T s.carrier := by
  intro z member
  obtain ⟨sigma, p, rfl⟩ := entries_cover (sharedConditionName D phi env i T valid) member
  exact ZFSet.pair_mem_prod.2
    ⟨((entry_sharedConditionName D phi env i T valid sigma p).1 member).1, s.encode_mem p⟩

end Name
end

namespace Name
open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)
variable (D : NameDomain s)
variable (closed : ∀ g sigma, sigma ∈ D.names → a.act s g sigma ∈ D.names)
variable {n : Nat} (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
variable (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName s z)
variable (terms : ∀ g (sigma : Name s), sigma.val ∈ J → (a.act s g sigma).val ∈ J)
include closed terms

theorem sharedConditionName_act (g : G) :
    a.act s g (sharedConditionName D phi env i J valid) =
      sharedConditionName D phi (a.actAssignment s D closed g env) i J valid := by
  unfold sharedConditionName
  rw [a.act_separationName s D closed, act_familySet a J valid terms]

theorem sharedConditionName_nice (K : Subgroup G)
    (fixed : ∀ j, K ≤ a.stabilizer s (env j).val) :
    NiceNameCode a s J K (sharedConditionName D phi env i J valid).val := by
  apply (niceNameCode_iff a s _).2
  refine ⟨sharedConditionName_subset D phi env i J valid, ?_⟩
  intro g hg
  change a.act s g (sharedConditionName D phi env i J valid) = _
  rw [sharedConditionName_act a D closed phi env i J valid terms]
  have equal : a.actAssignment s D closed g env = env := by
    funext j
    apply Subtype.ext
    exact fixed j hg
  rw [equal]

theorem sharedConditionName_hs (K : Subgroup G)
    (fixed : ∀ j, K ≤ a.stabilizer s (env j).val)
    (F : NormalSubgroupFamily G) (member : F.mem K)
    (children : ∀ sigma : Name s, sigma.val ∈ J → HereditarilySymmetric a s F sigma) :
    HereditarilySymmetric a s F (sharedConditionName D phi env i J valid) :=
  niceNameCode_hs a s F member children
    (sharedConditionName_nice a D closed phi env i J valid terms K fixed)

end Name

namespace TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem sharedConditionName_spec {G : Type u} [Group G]
    (a : PosetAction G P) (t : Presentation G)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {n : Nat} (phi : SetFormula n) (env : Assignment (M.nameDomain s) n) (i : Fin n)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ z ∈ J, IsName s z)
    (terms : ∀ g (sigma : Name s), sigma.val ∈ J → (a.act s g sigma).val ∈ J)
    (K : Subgroup G) (fixed : ∀ j, K ≤ a.stabilizer s (env j).val)
    (F : NormalSubgroupFamily G) (member : F.mem K)
    (children : ∀ sigma : Name s, sigma.val ∈ J → HereditarilySymmetric a s F sigma) :
    (Name.sharedConditionName (M.nameDomain s) phi env i J valid).val ∈ M.sets ∧
      NiceNameCode a s J K (Name.sharedConditionName (M.nameDomain s) phi env i J valid).val ∧
      HereditarilySymmetric a s F (Name.sharedConditionName (M.nameDomain s) phi env i J valid) := by
  have closed : ∀ g sigma, sigma ∈ (M.nameDomain s).names →
      a.act s g sigma ∈ (M.nameDomain s).names :=
    fun g sigma h => M.act_mem s a t pairing unions powers separation collection carrier maps g sigma h
  exact ⟨M.sharedConditionName_mem s pairing unions powers separation collection carrier order phi env i hJ valid,
    Name.sharedConditionName_nice a (M.nameDomain s) closed phi env i J valid terms K fixed,
    Name.sharedConditionName_hs a (M.nameDomain s) closed phi env i J valid terms K fixed F member children⟩

end TransitiveGround

end PartitionPilot.Forcing

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
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hAlpha cutOrdinal subset

theorem semanticStructuralPrefixSharedCondition_spec_oai (m : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T m
    ∃ valid : ∀ z ∈ J, IsName lower z,
      J ∈ M.sets ∧ ∀ (n : Nat) (phi : SetFormula n)
        (env : Assignment (M.nameDomain lower) n) (i : Fin n) (K : Subgroup G),
        (d.principalSupportFamily base directed).mem K →
        (∀ j, K ≤ (lowerAct).stabilizer lower (env j).val) →
        (Name.sharedConditionName (M.nameDomain lower) phi env i J valid).val ∈ M.sets ∧
        NiceNameCode lowerAct lower J K
          (Name.sharedConditionName (M.nameDomain lower) phi env i J valid).val ∧
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
          (Name.sharedConditionName (M.nameDomain lower) phi env i J valid) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  have hRestricted := M.graphRestriction_mem unions separation hAlpha hPacked
  have hQ : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha hRestricted omega
  have hOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha hRestricted omega
  have hGraph : (lowerAct).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    have ground := M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh omega
    unfold structuralForcingCarrier at ground
    rw [M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset] at ground
    exact ground
  have maps := M.conditionMapFamily_mem_of_actionGraph lowerAct lower t pairing unions powers separation
    collection hQ group hGraph
  obtain ⟨valid, hJ, terms, children⟩ := M.semanticStructuralPrefixPower_family
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset m
  refine ⟨valid, hJ, ?_⟩
  intro n phi env i K member fixed
  exact M.sharedConditionName_spec lower pairing unions powers separation collection hQ hOrder
    lowerAct t maps phi env i hJ valid terms K fixed
    (d.principalSupportFamily base directed) member children

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixSharedCondition_spec_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixSharedCondition_spec_oai.{u}
