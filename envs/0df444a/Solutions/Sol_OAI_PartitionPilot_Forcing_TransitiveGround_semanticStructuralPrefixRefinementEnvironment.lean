-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementEnvironment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:31:41.975852+00:00
-- url     : https://prove2.me/submissions/2c3a9629-40ed-43b7-ba7e-866289bfe5bb

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CrossStageMembershipFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower) (inclusion : Lower → Upper)

theorem realize_crossStageMembershipEntryFormula
    (unchanged : ∀ p, s.encode (inclusion p) = t.encode p)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (upperGround : s.carrier ∈ M.sets) (upperOrderGround : s.conditionOrder ∈ M.sets)
    (lowerGround : t.carrier ∈ M.sets)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ u ∈ J, IsName t u)
    (tau : Name s) (hTau : tau.val ∈ M.sets)
    {n : Nat} (zi ji li ui oi ti : Fin n) (env : Fin n → ZFSet.{u})
    (hz : env zi ∈ M.sets) (hj : env ji = J) (hl : env li = t.carrier)
    (hu : env ui = s.carrier) (ho : env oi = s.conditionOrder) (ht : env ti = tau.val) :
    Realize M.sets (crossStageMembershipEntryFormula zi ji li ui oi ti) env ↔
      ∃ sigma : Name t, sigma.val ∈ J ∧ ∃ p : Lower,
        env zi = ZFSet.pair sigma.val (t.encode p) ∧
          Name.ForcesMem (inclusion p) (Name.rename s inclusion sigma) tau := by
  rw [crossStageMembershipEntryFormula, exConditions, realize_ex]
  constructor
  · rintro ⟨u, uGround, member, body⟩
    change u ∈ env ji at member
    rw [hj] at member
    let sigma : Name t := ⟨u, valid u member⟩
    obtain ⟨p, shape, forced⟩ :=
      (M.realize_exConditions t li.succ _ (extend u env) lowerGround hl).1 body
    have hp := M.transitive lowerGround (t.encode_mem p)
    have code := Name.rename_val_of_encode s inclusion unchanged sigma
    have liftGround : (Name.rename s inclusion sigma).val ∈ M.sets := code.symm ▸ uGround
    let names : Assignment (M.nameDomain s) 2 :=
      extend ⟨Name.rename s inclusion sigma, liftGround⟩ (extend ⟨tau, hTau⟩ Fin.elim0)
    have pair := (M.realize_orderedPairFormula pairing zi.succ.succ 1 0
      (extend (t.encode p) (extend u env)) hz uGround hp).1 shape
    have atom := (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      upperGround upperOrderGround (0 : Fin 2) 1 (.mem 0 1)
      (extend ui.succ.succ (extend oi.succ.succ Fin.elim0)) 0
      (extend 1 (extend ti.succ.succ Fin.elim0)) _ hu ho (inclusion p) names (unchanged p).symm
      (Fin.cases code.symm (Fin.cases ht (fun i => Fin.elim0 i)))).1 forced
    exact ⟨sigma, member, p, pair, atom⟩
  · rintro ⟨sigma, member, p, pair, forced⟩
    have hs := M.transitive hJ member
    have hp := M.transitive lowerGround (t.encode_mem p)
    have code := Name.rename_val_of_encode s inclusion unchanged sigma
    have liftGround : (Name.rename s inclusion sigma).val ∈ M.sets := code.symm ▸ hs
    let names : Assignment (M.nameDomain s) 2 :=
      extend ⟨Name.rename s inclusion sigma, liftGround⟩ (extend ⟨tau, hTau⟩ Fin.elim0)
    refine ⟨sigma.val, hs, ?_, ?_⟩
    · change sigma.val ∈ env ji
      exact hj.symm ▸ member
    · apply (M.realize_exConditions t li.succ _ (extend sigma.val env) lowerGround hl).2
      refine ⟨p, ?_, ?_⟩
      · exact (M.realize_orderedPairFormula pairing zi.succ.succ 1 0
          (extend (t.encode p) (extend sigma.val env)) hz hs hp).2 pair
      · exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
          upperGround upperOrderGround (0 : Fin 2) 1 (.mem 0 1)
          (extend ui.succ.succ (extend oi.succ.succ Fin.elim0)) 0
          (extend 1 (extend ti.succ.succ Fin.elim0)) _ hu ho (inclusion p) names (unchanged p).symm
          (Fin.cases code.symm (Fin.cases ht (fun i => Fin.elim0 i)))).2 forced

end TransitiveGround
end PartitionPilot.Forcing

end

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

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower) (inclusion : Lower → Upper)
variable (unchanged : ∀ p, s.encode (inclusion p) = t.encode p)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (upperGround : s.carrier ∈ M.sets) (upperOrderGround : s.conditionOrder ∈ M.sets)
variable (lowerGround : t.carrier ∈ M.sets)
variable {J : ZFSet.{u}} (hJ : J ∈ M.sets) (valid : ∀ u ∈ J, IsName t u)
variable (tau : Name s) (hTau : tau.val ∈ M.sets)
include unchanged pairing unions powers separation collection upperGround upperOrderGround lowerGround hJ valid hTau

theorem crossStageMembershipCode_eq_selection :
    Name.crossStageMembershipCode s t inclusion J tau =
      ZFSet.sep (fun z => Realize M.sets (crossStageMembershipEntryFormula 0 1 2 3 4 5)
        (extend z ![J, t.carrier, s.carrier, s.conditionOrder, tau.val])) (ZFSet.prod J t.carrier) := by
  have productGround := M.prod_mem pairing unions powers separation hJ lowerGround
  have recognize (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets (crossStageMembershipEntryFormula 0 1 2 3 4 5)
        (extend z ![J, t.carrier, s.carrier, s.conditionOrder, tau.val]) ↔
      z ∈ Name.crossStageMembershipCode s t inclusion J tau := by
    rw [M.realize_crossStageMembershipEntryFormula s t inclusion unchanged
      pairing unions powers separation collection upperGround upperOrderGround lowerGround hJ valid tau hTau
      0 1 2 3 4 5 _ hz rfl rfl rfl rfl rfl]
    constructor
    · rintro ⟨sigma, member, p, rfl, forced⟩
      exact (Name.pair_mem_crossStageMembershipCode s t inclusion J tau sigma p).2 ⟨member, forced⟩
    · intro member
      obtain ⟨bound, sigma, p, rfl, forced⟩ := ZFSet.mem_sep.1 member
      exact ⟨sigma, (ZFSet.pair_mem_prod.1 bound).1, p, rfl, forced⟩
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sep]
  constructor
  · intro member
    have bound := Name.crossStageMembershipCode_subset s t inclusion J tau member
    exact ⟨bound, (recognize z (M.transitive productGround bound)).2 member⟩
  · rintro ⟨bound, formula⟩
    exact (recognize z (M.transitive productGround bound)).1 formula

theorem crossStageMembershipCode_mem :
    Name.crossStageMembershipCode s t inclusion J tau ∈ M.sets := by
  rw [M.crossStageMembershipCode_eq_selection s t inclusion unchanged pairing unions powers
    separation collection upperGround upperOrderGround lowerGround hJ valid tau hTau]
  exact M.separation_mem separation (crossStageMembershipEntryFormula 0 1 2 3 4 5)
    ![J, t.carrier, s.carrier, s.conditionOrder, tau.val]
    (Fin.cases hJ (Fin.cases lowerGround (Fin.cases upperGround
      (Fin.cases upperOrderGround (Fin.cases hTau (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hJ lowerGround)

theorem crossStageMembershipName_mem :
    (Name.crossStageMembershipName s t inclusion J valid tau).val ∈ M.sets :=
  M.crossStageMembershipCode_mem s t inclusion unchanged pairing unions powers separation collection
    upperGround upperOrderGround lowerGround hJ valid tau hTau

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

theorem semanticStructuralPrefixMembershipName_ground (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    let valid := (termData n).2 alpha cutOrdinal subset
    let upper := SetMembers.presentation Q
    let lower := SetMembers.presentation LQ
    ∀ tau : (M.nameDomain upper).names,
      (Name.crossStageMembershipName upper lower inc J valid tau.val).val ∈ M.sets := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
  let valid := (termData n).2 alpha cutOrdinal subset
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation LQ
  have unchanged : ∀ p : SetMembers LQ, upper.encode (inc p) = lower.encode p :=
    (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hs hPacked hT hAlpha carrier rowTop topMem topRows mono
  have hRestricted := M.graphRestriction_mem unions separation hAlpha hPacked
  have hQ : upper.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hLQ : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha hRestricted omega
  have upperOrder : upper.conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed
  have hUpperOrder : upper.conditionOrder ∈ M.sets := by
    rw [upperOrder]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hs hPacked omega
  dsimp only
  intro tau
  exact M.crossStageMembershipName_mem upper lower inc unchanged pairing unions powers separation
    collection hQ hUpperOrder hLQ (termData n).1 valid tau.val tau.property

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

theorem semanticStructuralPrefixRefinementEnvironment_oai (degrees : Fin 3 → Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let upper := SetMembers.presentation Q
    let lower := SetMembers.presentation LQ
    let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
    let valid := fun i => (termData (degrees i)).2 alpha cutOrdinal subset
    let validT := (termData 0).2 alpha cutOrdinal subset
    ∀ tau : Fin 3 → (M.nameDomain upper).names,
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation LQ
  let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
  let valid := fun i => (termData (degrees i)).2 alpha cutOrdinal subset
  let validT := (termData 0).2 alpha cutOrdinal subset
  dsimp only
  intro tau
  have ground : ∀ i : Fin 3,
      (Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val).val ∈ M.sets :=
    fun i => M.semanticStructuralPrefixMembershipName_ground c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice (degrees i) (tau i)
  let names : Fin 3 → (M.nameDomain lower).names := fun i =>
    ⟨Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val, ground i⟩
  have hLower : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hFamily := M.familySet_mem lower ⊤ pairing unions powers separation hT
    (M.transitive hLower (lower.encode_mem ⊤)) validT
  refine ⟨![names 0, names 1, names 2, ⟨Name.familySet ⊤ T validT, hFamily⟩], ?_, rfl⟩
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementEnvironment_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefixRefinementEnvironment_oai.{u}
