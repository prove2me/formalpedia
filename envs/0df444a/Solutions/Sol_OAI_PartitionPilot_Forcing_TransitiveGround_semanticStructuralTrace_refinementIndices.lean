-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementIndices
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:36:55.624068+00:00
-- url     : https://prove2.me/submissions/301114ad-2d93-44d9-aee6-f650ea668335

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralTrace_commonRefinementNames

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

theorem eval_rename (t : Presentation Q) (f : P → Q) (H : Set Q) (τ : Name s) :
    eval H (rename t f τ) = eval {p | f p ∈ H} τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ZFSet.ext
    intro x
    rw [mem_eval, mem_eval]
    constructor
    · rintro ⟨ν, q, h, hq, eq⟩
      obtain ⟨σ, p, hp, rfl, rfl⟩ := (entry_rename t f τ ν q).1 h
      exact ⟨σ, p, hp, hq, (ih σ p hp).symm.trans eq⟩
    · rintro ⟨σ, p, hp, hq, eq⟩
      exact ⟨rename t f σ, f p,
        (entry_rename t f τ _ _).2 ⟨σ, p, hp, rfl, rfl⟩,
        hq, (ih σ p hp).trans eq⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Compression.RecursiveMaps.NormalSubgroupFamily

universe u
variable {G : Type u} [Group G]

theorem fin_iInf (F : NormalSubgroupFamily G) {n : Nat}
    (K : Fin n → Subgroup G) (hK : ∀ i, F.mem (K i)) : F.mem (⨅ i, K i) := by
  induction n with
  | zero =>
    apply F.upward F.top
    apply le_iInf
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    have split : (⨅ i, K i) = K 0 ⊓ ⨅ i : Fin n, K i.succ := by
      apply le_antisymm
      · exact le_inf (iInf_le K 0) (le_iInf (fun i => iInf_le K i.succ))
      · apply le_iInf
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact inf_le_left
        · exact le_trans inf_le_right (iInf_le (fun j : Fin n => K j.succ) j)
    rw [split]
    exact F.inf (hK 0) (ih (fun i => K i.succ) (fun i => hK i.succ))

end PartitionPilot.Compression.RecursiveMaps.NormalSubgroupFamily



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



namespace PartitionPilot.Forcing.PosetAction

open Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u
variable {G I : Type u} [Group G] [PartialOrder I] (a : PosetAction G I)

theorem principalSupportFamily_basis (C : I) (directed : ∀ C D : I, ∃ E, C ≤ E ∧ D ≤ E)
    (H : Subgroup G) : (a.principalSupportFamily C directed).mem H ↔ ∃ D, a.principalFix D ≤ H := Iff.rfl

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v

theorem exists_commonPrincipalNameSupport {G L : Type u} [Group G] [PartialOrder L]
    {P : Type v} [PartialOrder P] (a : PosetAction G P) (s : Presentation P)
    (d : PosetAction G L) (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    {n : Nat} (tau : Fin n → Name s)
    (symmetric : ∀ i, (d.principalSupportFamily base directed).mem (a.stabilizer s (tau i))) :
    ∃ C : L, base ≤ C ∧ ∀ i, d.principalFix C ≤ a.stabilizer s (tau i) := by
  have allSupported := (d.principalSupportFamily base directed).fin_iInf
    (fun i => a.stabilizer s (tau i)) symmetric
  obtain ⟨B, bound⟩ := (d.principalSupportFamily_basis base directed _).1 allSupported
  obtain ⟨C, hBase, hB⟩ := directed base B
  refine ⟨C, hBase, fun i => ?_⟩
  exact (d.principalFix_antitone hB).trans (bound.trans (iInf_le _ i))

end PartitionPilot.Forcing.Name



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
universe u

theorem iteratedPairNameFamily_zero (one T : ZFSet.{u}) :
    iteratedPairNameFamily one T 0 = T := rfl

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceNameNormalization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {Upper Lower : Type u}

theorem rename_familySet_of_encode (s : Presentation Upper) (t : Presentation Lower)
    (inclusion : Lower → Upper) (codes : ∀ p, s.encode (inclusion p) = t.encode p)
    (upperOne : Upper) (lowerOne : Lower) (sameTop : s.encode upperOne = t.encode lowerOne)
    (T : ZFSet.{u}) (validUpper : ∀ z ∈ T, IsName s z)
    (validLower : ∀ z ∈ T, IsName t z) :
    rename s inclusion (familySet lowerOne T validLower) = familySet upperOne T validUpper := by
  apply Subtype.ext
  rw [rename_val_of_encode s inclusion codes, familySet_code, familySet_code, sameTop]

theorem eval_familySet_crossStage (s : Presentation Upper) (t : Presentation Lower)
    (inclusion : Lower → Upper) (codes : ∀ p, s.encode (inclusion p) = t.encode p)
    (upperOne : Upper) (lowerOne : Lower) (sameTop : s.encode upperOne = t.encode lowerOne)
    (T : ZFSet.{u}) (validUpper : ∀ z ∈ T, IsName s z)
    (validLower : ∀ z ∈ T, IsName t z) (H : Set Upper) :
    eval H (familySet upperOne T validUpper) =
      eval {p | inclusion p ∈ H} (familySet lowerOne T validLower) := by
  rw [← rename_familySet_of_encode s t inclusion codes upperOne lowerOne sameTop T validUpper validLower]
  exact eval_rename s inclusion H _

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNiceRefinementVisibility
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u

theorem normalizedRefinementIndex_mem
    (M : TransitiveGround.{u})
    {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
    (a : PosetAction G P) (s : Presentation P)
    (b : Presentation L) (d : PosetAction G L)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (level T1 T2 : ZFSet.{u}) (valid : ∀ z ∈ T1, IsName s z)
    (C E : L) (normalized : Assignment (M.nameDomain s) 4)
    (last : (normalized 3).val = Name.familySet ⊤ T1 valid)
    (strict : C < E)
    (niceU : NiceNameCode a s T1 (d.principalFix C) (normalized 0).val.val)
    (niceRf : NiceNameCode a s T2 (d.principalFix C) (normalized 1).val.val)
    (niceRc : NiceNameCode a s T2 (d.principalFix C) (normalized 2).val.val)
    (forced : Forces (M.nameDomain s)
      BoundedFormula.refinementValidityFormula.toFormula normalized ⊤) :
    refinementIndexCode level (b.encode C) (b.encode E)
      (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
        M.niceRefinementIndices a s b d level T1 T2 valid := by
  have familyGround : (Name.familySet ⊤ T1 valid).val ∈ M.sets := by
    rw [← last]
    exact (normalized 3).property
  have lastName : normalized 3 = ⟨Name.familySet ⊤ T1 valid, familyGround⟩ :=
    Subtype.ext last
  have normalizedEq : normalized =
      extend (normalized 0) (extend (normalized 1) (extend (normalized 2)
        (extend ⟨Name.familySet ⊤ T1 valid, familyGround⟩ Fin.elim0))) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases lastName (fun j => Fin.elim0 j)))) i
  apply (M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation
    collection carrier order level T1 T2 valid familyGround C E
      (normalized 0) (normalized 1) (normalized 2)).2
  refine ⟨strict, ?_, ?_, ?_, normalizedEq ▸ forced⟩
  · exact (M.mem_niceNameCandidates a s T1 (d.principalFix C) _).2
      ⟨(normalized 0).property, niceU⟩
  · exact (M.mem_niceNameCandidates a s T2 (d.principalFix C) _).2
      ⟨(normalized 1).property, niceRf⟩
  · exact (M.mem_niceNameCandidates a s T2 (d.principalFix C) _).2
      ⟨(normalized 2).property, niceRc⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralFamilyEvaluation
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
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
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

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem ordinal trace
local notation "projection" => M.semanticStructuralTrace_completeProjection c a t b d base directed
  T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
  nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
  symmetric1 symmetric2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralPowerFamily_eval_prefix (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      (run).carriers ordinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers ordinal carrier J
      (by
        obtain ⟨p, rfl⟩ := (c.mem_carrier rowTop).1 topMem
        exact iteratedPairNameFamily_valid p valid1 n)
    let validLower := (termData n).2 alpha cutOrdinal subset
    ∀ H : ConditionFilter (SetMembers Q),
      Name.eval {p | H.mem p} (Name.familySet ⊤ J validUpper) =
        Name.eval {p | ((projection).projectedFilter H).mem p} (Name.familySet ⊤ J validLower) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation LQ
  have unchanged : ∀ p, upper.encode (inc p) = lower.encode p :=
    (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hs hPacked hT hAlpha carrier rowTop topMem topRows mono
  have equalTop : upper.encode ⊤ = lower.encode ⊤ := by
    rw [M.refinementHistoryDecodedTop_eq, M.refinementHistoryDecodedTop_eq]
  dsimp only
  intro H
  exact Name.eval_familySet_crossStage upper lower inc unchanged ⊤ ⊤ equalTop _ _ _ {p | H.mem p}

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralFinalRefinements
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

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_finalRefinementNames (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
      (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
      (And.left (And.left standard)) carrier T valid1
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          ∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
    (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
  let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
    (And.left (And.left standard)) carrier T valid1
  dsimp only
  intro tau
  obtain ⟨beta, hBeta, result⟩ := M.semanticStructuralTrace_commonRefinementNames
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT small tau
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  dsimp only at result
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported, preserved⟩ := result
  refine ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported, ?_⟩
  intro H upperGeneric lowerCoded lowerGeneric originalValid
  apply preserved H upperGeneric lowerCoded lowerGeneric
  have sameUniverse := M.semanticStructuralPowerFamily_eval_prefix
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset
    infinite choice 0 H
  simp only [iteratedPairNameFamily_zero] at sameUniverse
  rw [← sameUniverse]
  exact originalValid

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralSymmetricRefinementOutputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet




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

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_refinementIndices_oai (small : M.sets.Countable)
    (square : T2 = orderedPairNameFamily (ZFSet.pair rowTop ∅) T T)
    (growth : ∀ C : L, ∃ E, C < E) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
      (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
      (And.left (And.left standard)) carrier T valid1
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      (∀ i, HereditarilySymmetric upperAct (SetMembers.presentation Q)
        (d.principalSupportFamily base directed) (tau i).val) →
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∃ C E : L, base ≤ C ∧ C < E ∧
          (∀ i, d.principalFix C ≤ (upperAct).stabilizer upper (tau i).val) ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            M.niceRefinementIndices lowerAct lower b d beta T T2 validT ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          ∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
    (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
  dsimp only
  intro tau symmetric
  obtain ⟨beta, hBeta, result⟩ := M.semanticStructuralTrace_finalRefinementNames
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT small tau
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
  let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  dsimp only at result
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported, preserved⟩ := result
  obtain ⟨C, baseC, fixes⟩ := Name.exists_commonPrincipalNameSupport upperAct upper d base directed
    (fun i => (tau i).val) (fun i => (symmetric i).symmetric)
  obtain ⟨E, strict⟩ := growth C
  have member : (d.principalSupportFamily base directed).mem (d.principalFix C) :=
    (d.principalSupportFamily_basis base directed _).2 ⟨C, le_rfl⟩
  have nice := fun i => (supported (d.principalFix C) member fixes i).1
  have hLower : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have family : (normalized 3).val = Name.familySet ⊤ T ((termData 0).2 beta cutOrdinal subset) := by
    rw [normalizedLast]
    exact last
  have niceU : NiceNameCode lowerAct lower T (d.principalFix C) (normalized 0).val.val := by
    have niceZero := nice 0
    simp only [Matrix.cons_val_zero, iteratedPairNameFamily_zero] at niceZero
    exact niceZero
  have onePower : iteratedPairNameFamily (ZFSet.pair rowTop ∅) T 1 = T2 := square.symm
  have niceRf : NiceNameCode lowerAct lower T2 (d.principalFix C) (normalized 1).val.val := by
    exact (congrArg (fun S => NiceNameCode lowerAct lower S (d.principalFix C)
      (normalized 1).val.val) onePower).mp (nice 1)
  have niceRc : NiceNameCode lowerAct lower T2 (d.principalFix C) (normalized 2).val.val := by
    exact (congrArg (fun S => NiceNameCode lowerAct lower S (d.principalFix C)
      (normalized 2).val.val) onePower).mp (nice 2)
  have index := M.normalizedRefinementIndex_mem lowerAct lower b d pairing unions powers separation
    collection hLower hOrder beta T T2 ((termData 0).2 beta cutOrdinal subset)
    C E normalized family strict niceU niceRf niceRc forced
  exact ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, preserved⟩

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementIndices_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementIndices_oai.{u}
