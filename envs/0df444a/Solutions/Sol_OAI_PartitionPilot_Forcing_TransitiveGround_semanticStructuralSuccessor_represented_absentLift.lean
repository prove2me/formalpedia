-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_absentLift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:35:22.908131+00:00
-- url     : https://prove2.me/submissions/d5debaf5-e28a-4706-bf05-1896bdbecc83

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralSuccessor_insert_absentLift

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowAssignmentCuts
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
variable (M : TransitiveGround.{u})

theorem realize_rowAssignmentCutFormula {n : Nat} (z levels alpha : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (rowAssignmentCutFormula z levels alpha) env ↔
      ∃ row A, env z = ZFSet.pair (ZFSet.pair row A)
        (ZFSet.pair row (assignmentCut (env levels) (env alpha) A)) := by
  rw [rowAssignmentCutFormula, realize_exBlock]
  have actual (f : Fin 5 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (SetFormula.rowAssignmentCutBody z levels alpha).toFormula
        (extendMany 5 f env) ↔
      env z = ZFSet.pair (f 3) (f 4) ∧ f 3 = ZFSet.pair (f 0) (f 1) ∧
        f 4 = ZFSet.pair (f 0) (f 2) ∧
          f 2 = assignmentCut (env levels) (env alpha) (f 1) := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members)]
    simp only [SetFormula.rowAssignmentCutBody, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_assignmentCutFormula,
      extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨equal, upper, lower, cut⟩ := (actual f ground).1 body
    rw [upper, lower, cut] at equal
    exact ⟨f 0, f 1, equal⟩
  · rintro ⟨row, A, equal⟩
    have pairGround := equal ▸ members z
    have upper := M.pair_left pairGround
    have lower := M.pair_right pairGround
    let cut := assignmentCut (env levels) (env alpha) A
    let f : Fin 5 → ZFSet.{u} := ![row, A, cut, ZFSet.pair row A, ZFSet.pair row cut]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases (M.pair_left upper) (Fin.cases (M.pair_right upper)
        (Fin.cases (M.pair_right lower) (Fin.cases upper
          (Fin.cases lower (fun j => Fin.elim0 j)))))
    exact ⟨f, ground, (actual f ground).2 ⟨equal, rfl, rfl, rfl⟩⟩

theorem rowAssignmentCutGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {upper lower levels alpha : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLower : lower ∈ M.sets)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) :
    rowAssignmentCutGraph upper lower levels alpha ∈ M.sets := by
  let params : Fin 2 → ZFSet.{u} := ![levels, alpha]
  have ground : ∀ j, params j ∈ M.sets :=
    Fin.cases hLevels (Fin.cases hAlpha (fun j => Fin.elim0 j))
  have bound := M.prod_mem pairing unions powers separation hUpper hLower
  have selected := M.separation_mem separation (rowAssignmentCutFormula 0 1 2) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (rowAssignmentCutFormula 0 1 2) (extend z params))
      (ZFSet.prod upper lower) = rowAssignmentCutGraph upper lower levels alpha := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_rowAssignmentCutGraph]
    apply and_congr_right
    intro hz
    exact M.realize_rowAssignmentCutFormula 0 1 2 (extend z params)
      (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRepresentedDomainConditions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

private theorem realize_representedReuseFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (A q P order T idx cu classes : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (representedReuseFormula A q P order T idx cu classes) env ↔
      ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
        stageOneAssignment (env idx) v w ∈ env A ∧
        ZFSet.pair v z ∈ env classes ∧
        stageOneRawForces M (env P) (env order) (env q)
          (.equal 0 1 : SetFormula 2) ![env cu, z] := by
  rw [representedReuseFormula, realize_exBlock]
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (.mem (prefixIndex n 3 0) (suffixIndex n 3 T))
        (.conj (.mem (prefixIndex n 3 1) (suffixIndex n 3 T))
          (.conj (tripleMembershipFormula (suffixIndex n 3 idx) (prefixIndex n 3 0)
            (prefixIndex n 3 1) (suffixIndex n 3 A))
            (.conj (pairMembershipFormula (prefixIndex n 3 0) (prefixIndex n 3 2)
              (suffixIndex n 3 classes))
              (stageOneForcingAt (.equal 0 1 : SetFormula 2) (suffixIndex n 3 q)
                (suffixIndex n 3 P) (suffixIndex n 3 order)
                ![suffixIndex n 3 cu, prefixIndex n 3 2]))))) (extendMany 3 f env) ↔
      f 0 ∈ env T ∧ f 1 ∈ env T ∧
      stageOneAssignment (env idx) (f 0) (f 1) ∈ env A ∧
      ZFSet.pair (f 0) (f 2) ∈ env classes ∧
      stageOneRawForces M (env P) (env order) (env q)
        (.equal 0 1 : SetFormula 2) ![env cu, f 2] := by
    have allGround := extendMany_members 3 f env ground members
    simp only [Realize]
    rw [M.realize_tripleMembershipFormula pairing _ _ _ _ _
      (allGround _) (allGround _) (allGround _) (allGround _),
      M.realize_pairMembershipFormula pairing _ _ _ _ (allGround _) (allGround _) (allGround _),
      M.realize_stageOneForcingAt]
    have values (x y : Fin (n + 3)) :
        (fun j : Fin 2 => extendMany 3 f env (![x, y] j)) =
          ![extendMany 3 f env x, extendMany 3 f env y] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [values]
    simp only [extendMany_prefix, extendMany_suffix, stageOneAssignment]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨hv, hw, literal, entry, forced⟩ := (actual f ground).1 body
    exact ⟨f 0, hv, f 1, hw, f 2, literal, entry, forced⟩
  · rintro ⟨v, hv, w, hw, z, literal, entry, forced⟩
    have ground : ∀ j, (![v, w, z] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members T) hv) (Fin.cases (M.transitive (members T) hw)
        (Fin.cases (M.pair_right (M.transitive (members classes) entry)) (fun j => Fin.elim0 j)))
    exact ⟨![v, w, z], ground, (actual ![v, w, z] ground).2 ⟨hv, hw, literal, entry, forced⟩⟩

private theorem realize_representedEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (p P order cut T idx u U cu classes : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (representedEntryFormula p P order cut T idx u U cu classes) env ↔
      ∃ row A q, env p = ZFSet.pair row A ∧ ZFSet.pair (env p) q ∈ env cut ∧
        (stageOneRawForces M (env P) (env order) q
          (.neg (.mem 0 1) : SetFormula 2) ![env u, env U] ∨
        (stageOneRawForces M (env P) (env order) q (.mem 0 1 : SetFormula 2) ![env u, env U] ∧
          ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
            stageOneAssignment (env idx) v w ∈ A ∧ ZFSet.pair v z ∈ env classes ∧
            stageOneRawForces M (env P) (env order) q
              (.equal 0 1 : SetFormula 2) ![env cu, z])) := by
  rw [representedEntryFormula, realize_exBlock]
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (BoundedFormula.orderedPairFormula (suffixIndex n 3 p)
        (prefixIndex n 3 0) (prefixIndex n 3 1)).toFormula
        (.conj (pairMembershipFormula (suffixIndex n 3 p) (prefixIndex n 3 2) (suffixIndex n 3 cut))
          (disj (stageOneForcingAt (.neg (.mem 0 1) : SetFormula 2) (prefixIndex n 3 2)
            (suffixIndex n 3 P) (suffixIndex n 3 order) ![suffixIndex n 3 u, suffixIndex n 3 U])
            (.conj (stageOneForcingAt (.mem 0 1 : SetFormula 2) (prefixIndex n 3 2)
              (suffixIndex n 3 P) (suffixIndex n 3 order) ![suffixIndex n 3 u, suffixIndex n 3 U])
              (representedReuseFormula (prefixIndex n 3 1) (prefixIndex n 3 2)
                (suffixIndex n 3 P) (suffixIndex n 3 order) (suffixIndex n 3 T)
                (suffixIndex n 3 idx) (suffixIndex n 3 cu) (suffixIndex n 3 classes))))))
        (extendMany 3 f env) ↔
      env p = ZFSet.pair (f 0) (f 1) ∧ ZFSet.pair (env p) (f 2) ∈ env cut ∧
        (stageOneRawForces M (env P) (env order) (f 2)
          (.neg (.mem 0 1) : SetFormula 2) ![env u, env U] ∨
        (stageOneRawForces M (env P) (env order) (f 2) (.mem 0 1 : SetFormula 2) ![env u, env U] ∧
          ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
            stageOneAssignment (env idx) v w ∈ f 1 ∧ ZFSet.pair v z ∈ env classes ∧
            stageOneRawForces M (env P) (env order) (f 2)
              (.equal 0 1 : SetFormula 2) ![env cu, z])) := by
    have allGround := extendMany_members 3 f env ground members
    rw [Realize, BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.truth_orderedPairFormula, Realize,
      M.realize_pairMembershipFormula pairing _ _ _ _ (allGround _) (allGround _) (allGround _),
      realize_disj, M.realize_stageOneForcingAt, Realize, M.realize_stageOneForcingAt,
      realize_representedReuseFormula M pairing _ _ _ _ _ _ _ _ _ allGround]
    have values (x y : Fin (n + 3)) :
        (fun j : Fin 2 => extendMany 3 f env (![x, y] j)) =
          ![extendMany 3 f env x, extendMany 3 f env y] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [values]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    exact ⟨f 0, f 1, f 2, (actual f ground).1 body⟩
  · rintro ⟨row, A, q, shape, cutEntry, code⟩
    have ground : ∀ j, (![row, A, q] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.pair_left (shape ▸ members p)) (Fin.cases (M.pair_right (shape ▸ members p))
        (Fin.cases (M.pair_right (M.transitive (members cut) cutEntry)) (fun j => Fin.elim0 j)))
    exact ⟨![row, A, q], ground, (actual ![row, A, q] ground).2 ⟨shape, cutEntry, code⟩⟩

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
private theorem representedParams_ground {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) :
    ∀ j, (![s.carrier, s.conditionOrder, rowAssignmentCutGraph upper s.carrier levels alpha,
      T, idx, u.val.val, U.val.val, (Name.refinementClass T valid Rc.val u.val).val,
      Name.refinementClassGraph T valid Rc.val T valid] : Fin 9 → ZFSet.{u}) j ∈ M.sets :=
  Fin.cases carrier (Fin.cases order
    (Fin.cases (M.rowAssignmentCutGraph_mem pairing unions powers separation hUpper carrier hLevels hAlpha)
      (Fin.cases hT (Fin.cases hIdx (Fin.cases u.property (Fin.cases U.property
        (Fin.cases (M.refinementClass_mem s pairing unions powers separation collection carrier order
          hT valid Rc.val u.val Rc.property u.property)
          (Fin.cases (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
            hT hT valid valid Rc.val Rc.property) (fun j => Fin.elim0 j)))))))))

include pairing unions powers separation collection carrier order in
theorem representedDomainConditions_mem {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) :
    M.representedDomainConditions s upper levels alpha T valid idx U Rc u ∈ M.sets :=
  M.separation_mem separation (representedEntryFormula 0 1 2 3 4 5 6 7 8 9) _
    (representedParams_ground M s pairing unions powers separation collection carrier order
      hUpper hLevels hAlpha hT valid hIdx U Rc u) hUpper

include pairing unions powers separation collection carrier order in
theorem pair_mem_representedDomainConditions {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) (row A : ZFSet.{u}) (q : P)
    (cut : s.encode q = ZFSet.pair row (assignmentCut levels alpha A)) :
    ZFSet.pair row A ∈ M.representedDomainConditions s upper levels alpha T valid idx U Rc u ↔
      ZFSet.pair row A ∈ upper ∧
      ((∀ r : P, r ≤ q → ¬ Name.ForcesMem r u.val U.val) ∨
        (Name.ForcesMem q u.val U.val ∧ ∃ v w : Name s,
          v.val ∈ T ∧ w.val ∈ T ∧ stageOneAssignment idx v.val w.val ∈ A ∧
          Name.ForcesEq q (Name.refinementClass T valid Rc.val u.val)
            (Name.refinementClass T valid Rc.val v))) := by
  let params : Fin 9 → ZFSet.{u} := ![s.carrier, s.conditionOrder,
    rowAssignmentCutGraph upper s.carrier levels alpha, T, idx, u.val.val, U.val.val,
    (Name.refinementClass T valid Rc.val u.val).val, Name.refinementClassGraph T valid Rc.val T valid]
  have paramsGround := representedParams_ground M s pairing unions powers separation collection carrier order
    hUpper hLevels hAlpha hT valid hIdx U Rc u
  have raw (phi : SetFormula 2) (x y : (M.nameDomain s).names) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi ![x.val.val, y.val.val] ↔
        Forces (M.nameDomain s) phi ![x, y] q := by
    have fields : (fun j : Fin 2 => (![x, y] j).val.val) = ![x.val.val, y.val.val] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    have result := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order phi q ![x, y]
    rw [fields] at result
    exact result
  let className (v : (M.nameDomain s).names) : (M.nameDomain s).names :=
    ⟨Name.refinementClass T valid Rc.val v.val,
      M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid
        Rc.val v.val Rc.property v.property⟩
  rw [representedDomainConditions, ZFSet.mem_sep]
  change (ZFSet.pair row A ∈ upper ∧ Realize M.sets (representedEntryFormula 0 1 2 3 4 5 6 7 8 9)
    (extend (ZFSet.pair row A) params)) ↔ _
  apply and_congr_right
  intro member
  rw [realize_representedEntryFormula M pairing _ _ _ _ _ _ _ _ _ _ _
    (Fin.cases (M.transitive hUpper member) paramsGround)]
  change (∃ row' A' q', ZFSet.pair row A = ZFSet.pair row' A' ∧
    ZFSet.pair (ZFSet.pair row A) q' ∈ rowAssignmentCutGraph upper s.carrier levels alpha ∧
    (stageOneRawForces M s.carrier s.conditionOrder q' (.neg (.mem 0 1) : SetFormula 2) ![u.val.val, U.val.val] ∨
      (stageOneRawForces M s.carrier s.conditionOrder q' (.mem 0 1 : SetFormula 2) ![u.val.val, U.val.val] ∧
        ∃ v ∈ T, ∃ w ∈ T, ∃ z, stageOneAssignment idx v w ∈ A' ∧
          ZFSet.pair v z ∈ Name.refinementClassGraph T valid Rc.val T valid ∧
          stageOneRawForces M s.carrier s.conditionOrder q' (.equal 0 1 : SetFormula 2)
            ![(className u).val.val, z]))) ↔ _
  constructor
  · rintro ⟨row', A', q', same, entry, branch⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 same
    have equal := ((pair_mem_rowAssignmentCutGraph upper s.carrier levels alpha row A q').1 entry).2.2
    have eq : q' = s.encode q := equal.trans cut.symm
    rw [eq] at branch
    rcases branch with inactive | ⟨active, v, hv, w, hw, z, literal, classEntry, equal⟩
    · exact Or.inl ((raw (.neg (.mem 0 1)) u U).1 inactive)
    · let vName : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
      have classEqual := (Name.pair_mem_refinementClassGraph T valid Rc.val T valid vName.val z).1 classEntry |>.2
      rw [classEqual] at equal
      exact Or.inr ⟨(raw (.mem 0 1) u U).1 active, vName.val, ⟨w, valid w hw⟩,
        hv, hw, literal, (raw (.equal 0 1) (className u) (className vName)).1 equal⟩
  · intro branch
    refine ⟨row, A, s.encode q, rfl,
      (pair_mem_rowAssignmentCutGraph upper s.carrier levels alpha row A (s.encode q)).2
        ⟨member, s.encode_mem q, cut⟩, ?_⟩
    rcases branch with inactive | ⟨active, v, w, hv, hw, literal, equal⟩
    · exact Or.inl ((raw (.neg (.mem 0 1)) u U).2 inactive)
    · let vName : (M.nameDomain s).names := ⟨v, M.transitive hT hv⟩
      exact Or.inr ⟨(raw (.mem 0 1) u U).2 active, v.val, hv, w.val, hw,
        (className vName).val.val, literal,
        (Name.pair_mem_refinementClassGraph T valid Rc.val T valid v _).2 ⟨hv, rfl⟩,
        (raw (.equal 0 1) (className u) (className vName)).2 equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticRepresentedDomainAbsentLift
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

local notation "next" => graphRestriction (insert alpha alpha) packed
local notation "upper" => M.refinementHistoryForcing c.carrier T (insert alpha alpha) next
local notation "levels" => refinementDataHistoryLevels (insert alpha alpha) next T
local notation "packedGround" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "lowerGround" => M.refinementHistoryForcing_mem pairing unions powers separation
  carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega
local notation "orderGround" => M.refinementHistoryOrder_mem pairing unions powers separation
  carrier rowOrderGround hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega

theorem semanticStructuralSuccessor_represented_absentLift_oai
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable)
    {row A : ZFSet.{u}} (condition : ZFSet.pair row A ∈ upper) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
    let lowerOrder : lower.conditionOrder ∈ M.sets := by
      rw [M.refinementHistoryDecodedOrder_eq]
      exact orderGround
    let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
    let vis := M.stageOneVisibilityName lower valid act b d base directed system.first

    ∀ (meet : L → L → L),
      (∀ (H : ConditionFilter (SetMembers Q)), H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v z : L) (x y : (M.nameDomain lower).names),
          d.principalFix v ≤ (act).stabilizer lower x.val →
          d.principalFix z ≤ (act).stabilizer lower y.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) x.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau.val ∧
            d.principalFix (meet v z) ≤ (act).stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∀ (C E K : L) (U Rf Rc u w : (M.nameDomain lower).names) (F : ZFSet.{u}),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid →
      u.val.val ∈ T → w.val.val ∈ T →
      ∀ pCut q : SetMembers Q,
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → q ≤ pCut →
      Name.ForcesMem q u.val U.val → Name.ForcesMem q w.val U.val →
      (∀ v : L, b.encode v ∈ testedMeetFilter F b.conditionOrder (b.encode E) → K ≤ v) →
      (∀ v : L, E ≤ v → b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) → meet K v = C) →
      M.DecidesVisibilityProfile act lower b d.principalFix T F (cls Rc u).val q →
      Name.ForcesMem q (cls Rf w).val (vis K).val →
      (∀ p, p ≤ q → ¬ Name.ForcesMem p (cls Rf w).val (vis C).val) →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rc u).val (cls Rc v).val) ∧
        ∃ profile, M.DecidesVisibilityProfile act lower b d.principalFix T profile (cls Rf z).val q ∧
          (b.encode C ∉ profile → b.encode K ∉ profile)) →
      M.representedDomainConditions lower upper levels alpha T valid idx U Rc u ∈ M.sets ∧
      ∃ lowerRow lowerA : ZFSet.{u}, lower.encode q = ZFSet.pair lowerRow lowerA ∧
        let spliced := assignmentSplice levels alpha lowerA A
        let inserted := insert (stageOneAssignment idx u.val.val w.val.val) spliced
        ZFSet.pair lowerRow inserted ∈ upper ∧
        ZFSet.pair (ZFSet.pair lowerRow inserted) (ZFSet.pair row A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next ∧
        A ⊆ inserted ∧ stageOneAssignment idx u.val.val w.val.val ∈ inserted ∧
        ZFSet.pair lowerRow (assignmentCut levels alpha inserted) = lower.encode q ∧
        Name.ForcesEq q (cls Rc u).val (cls Rc u).val ∧
        ZFSet.pair lowerRow inserted ∈ M.representedDomainConditions lower upper levels alpha T valid
          idx U Rc u := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact orderGround
  let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
  let vis := M.stageOneVisibilityName lower valid act b d base directed system.first
  dsimp only
  intro meet descent C E K U Rf Rc u w F idx hu hw pCut q cutCode qp
    activeU activeW capPositive capNegative decisions capVisible nonvisible oldProfiles
  obtain ⟨lowerRow, lowerA, qCode, insertedCondition, insertedBelow, retained,
      insertedLiteral, exactCut, selfEqual⟩ :=
    M.semanticStructuralSuccessor_insert_absentLift c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice small condition
      meet descent C E K U Rf Rc u w F idx hu hw pCut q cutCode qp
      activeU activeW capPositive capNegative decisions capVisible nonvisible oldProfiles
  have nextGround : insert alpha alpha ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have packedNextGround : next ∈ M.sets := M.graphRestriction_mem unions separation nextGround packedGround
  have upperGround : upper ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT nextGround packedNextGround omega
  have levelsGround : levels ∈ M.sets :=
    M.refinementDataHistoryLevels_mem pairing unions powers separation nextGround packedNextGround hT
  have indexGround := M.refinementIndexCode_mem pairing hAlpha
    (M.transitive nodes (b.encode_mem C)) (M.transitive nodes (b.encode_mem E))
    U.property Rf.property Rc.property
  refine ⟨M.representedDomainConditions_mem lower pairing unions powers separation collection
    lowerGround lowerOrder upperGround levelsGround hAlpha hT valid indexGround U Rc u,
    lowerRow, lowerA, qCode, insertedCondition, insertedBelow, retained, insertedLiteral,
    exactCut, selfEqual, ?_⟩
  exact (M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerGround lowerOrder upperGround levelsGround hAlpha hT valid indexGround U Rc u lowerRow
    _ q exactCut.symm).2
    ⟨insertedCondition, Or.inr ⟨activeU, u.val, w.val, hu, hw, insertedLiteral, selfEqual⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_absentLift_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_absentLift_oai.{u}
