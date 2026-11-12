-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementOutputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:37:52.475256+00:00
-- url     : https://prove2.me/submissions/9654056f-34f1-43b0-bc5f-b5a80a653b79

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralTrace_storedRefinementIndices

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_EvaluatedDomains
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace Name

open SetRealization
universe u v
variable {P : Type u} {s : Presentation P}

theorem mem_eval_assemble (H : Set P) {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) (x : ZFSet.{u}) :
    x ∈ eval H (assemble names conditions) ↔
      ∃ i, conditions i ∈ H ∧ eval H (names i) = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨i, rfl, rfl⟩ := (entry_assemble names conditions σ p).1 entry
    exact ⟨i, hp, eq⟩
  · rintro ⟨i, hp, eq⟩
    exact ⟨names i, conditions i,
      (entry_assemble names conditions _ _).2 ⟨i, rfl, rfl⟩, hp, eq⟩

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem eval_singleton (H : Set P) (one : P) (hone : one ∈ H) (σ : Name s) :
    eval H (singleton one σ) = {eval H σ} := by
  apply ZFSet.ext
  intro x
  rw [singleton, mem_eval_assemble, ZFSet.mem_singleton]
  constructor
  · rintro ⟨_, _, eq⟩
    exact eq.symm
  · intro eq
    exact ⟨(), hone, eq.symm⟩

theorem eval_unorderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (unorderedPair one σ τ) = {eval H σ, eval H τ} := by
  apply ZFSet.ext
  intro x
  rw [unorderedPair, mem_eval_assemble, ZFSet.mem_pair]
  constructor
  · rintro ⟨b, _, eq⟩
    cases b with
    | false => exact Or.inr eq.symm
    | true => exact Or.inl eq.symm
  · rintro (eq | eq)
    · exact ⟨true, hone, eq.symm⟩
    · exact ⟨false, hone, eq.symm⟩

theorem eval_orderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (orderedPair one σ τ) = ZFSet.pair (eval H σ) (eval H τ) := by
  rw [orderedPair, eval_unorderedPair H one hone,
    eval_singleton H one hone, eval_unorderedPair H one hone]
  rfl

end Name



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

theorem eval_refinementClass (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (R w : Name s)
    (hR : R ∈ D.names)
    (pairs : ∀ z : Name s, z.val ∈ T → orderedPair ⊤ z w ∈ D.names) :
    eval {p | H.mem p} (refinementClass T valid R w) =
      equivalenceClass (eval {p | H.mem p} (familySet ⊤ T valid))
        (eval {p | H.mem p} R) (eval {p | H.mem p} w) := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, mem_equivalenceClass]
  constructor
  · rintro ⟨z, p, entry, hp, rfl⟩
    obtain ⟨member, forced⟩ := (entry_refinementClass T valid R w z p).1 entry
    have related := forcesMem_sound D H generic (pairs z member) hR hp forced
    rw [eval_orderedPair {p | H.mem p} ⊤ H.top_mem z w] at related
    exact ⟨(mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid _).2 ⟨z, member, rfl⟩, related⟩
  · rintro ⟨member, related⟩
    obtain ⟨z, hz, rfl⟩ := (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).1 member
    have named : eval {p | H.mem p} (orderedPair ⊤ z w) ∈ eval {p | H.mem p} R := by
      rw [eval_orderedPair {p | H.mem p} ⊤ H.top_mem z w]
      exact related
    obtain ⟨p, hp, forced⟩ := (eval_mem_iff_forcesMem D H generic (pairs z hz) hR).1 named
    exact ⟨z, p, (entry_refinementClass T valid R w z p).2 ⟨hz, forced⟩, hp, rfl⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing carrier in
theorem eval_refinementClass {T : ZFSet.{u}} (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) (hR : R.val ∈ M.sets) (hw : w.val ∈ M.sets)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    Name.eval {p | H.mem p} (Name.refinementClass T valid R w) =
      equivalenceClass (Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
        (Name.eval {p | H.mem p} R) (Name.eval {p | H.mem p} w) := by
  apply Name.eval_refinementClass (M.nameDomain s) H (fun E hE dense => generic E (Or.inl hE) dense)
    T valid R w hR
  intro z hz
  change (Name.orderedPair ⊤ z w).val ∈ M.sets
  rw [Name.orderedPair_code]
  exact M.orderedPairNameCode_mem pairing (M.transitive carrier (s.encode_mem ⊤))
    (M.transitive hT hz) hw

end TransitiveGround
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RefinementValidityCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

theorem truth_equivalenceRelationFormula {n} (S R : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (equivalenceRelationFormula S R) env ↔ EquivalenceRelationCode (env S) (env R) := by
  simp only [equivalenceRelationFormula, Truth, truth_relationBetweenFormula,
    truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, refl, symm, trans⟩
    refine ⟨shape, refl, ?_, ?_⟩
    · intro x y xy
      obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (shape xy)
      exact symm x hx y hy xy
    · intro x y z xy yz
      obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (shape xy)
      have hz := (ZFSet.pair_mem_prod.1 (shape yz)).2
      exact trans x hx y hy z hz ⟨xy, yz⟩
  · intro relation
    exact ⟨relation.shape, relation.refl,
      fun x _ y _ xy => relation.symm x y xy,
      fun x _ y _ z _ h => relation.trans x y z h.1 h.2⟩

theorem truth_refinementValidityFormula (env : Fin 4 → ZFSet.{u}) :
    Truth refinementValidityFormula env ↔
      RefinementValidityCode (env 3) (env 0) (env 1) (env 2) := by
  simp only [refinementValidityFormula, Truth, truth_subsetFormula,
    truth_equivalenceRelationFormula, RefinementValidityCode]

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_refinementValidityFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets BoundedFormula.refinementValidityFormula.toFormula env ↔
      RefinementValidityCode (env 3) (env 0) (env 1) (env 2) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_refinementValidityFormula env)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ActiveNameImageSymmetry
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem mem_eval_activeImage (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image : Name s → Name s) (hU : U ∈ D.names)
    (terms : ∀ w : Name s, w.val ∈ T → w ∈ D.names) (x : ZFSet.{u}) :
    x ∈ eval {p | H.mem p} (activeImage T valid U image) ↔
      ∃ w : Name s, w.val ∈ T ∧ eval {p | H.mem p} w ∈ eval {p | H.mem p} U ∧
        eval {p | H.mem p} (image w) = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, equal⟩
    obtain ⟨w, hw, forced, rfl⟩ := (entry_activeImage T valid U image σ p).1 entry
    exact ⟨w, hw, forcesMem_sound D H generic (terms w hw) hU hp forced, equal⟩
  · rintro ⟨w, hw, active, equal⟩
    obtain ⟨p, hp, forced⟩ := (eval_mem_iff_forcesMem D H generic (terms w hw) hU).1 active
    exact ⟨image w, p, (entry_activeImage T valid U image (image w) p).2
      ⟨w, hw, forced, rfl⟩, hp, equal⟩

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


namespace PartitionPilot.Forcing

universe u

theorem refinementQuotientMap_subset (U Rf Rc : ZFSet.{u}) :
    refinementQuotientMap U Rf Rc ⊆
      ZFSet.prod (equivalenceClasses U Rf) (equivalenceClasses U Rc) := by
  intro z hz
  rw [refinementQuotientMap, relationCompose, ZFSet.mem_sep] at hz
  exact hz.1

theorem pair_mem_refinementQuotientMap (U Rf Rc C D : ZFSet.{u}) :
    ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc ↔
      ∃ x ∈ U, C = equivalenceClass U Rf x ∧ D = equivalenceClass U Rc x := by
  rw [refinementQuotientMap, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, x, hx, first, second⟩
    exact ⟨x, hx,
      ((pair_mem_equivalenceClassifier U Rf x C).1
        ((pair_mem_relationConverse _ _ _ x C).1 first).2.2).2,
      ((pair_mem_equivalenceClassifier U Rc x D).1 second).2⟩
  · rintro ⟨x, hx, rfl, rfl⟩
    have hf := equivalenceClass_mem (E := Rf) hx
    have hc := equivalenceClass_mem (E := Rc) hx
    exact ⟨hf, hc, x, hx, (pair_mem_relationConverse _ _ _ x _).2
      ⟨hx, hf, (pair_mem_equivalenceClassifier U Rf x _).2 ⟨hx, rfl⟩⟩,
      (pair_mem_equivalenceClassifier U Rc x _).2 ⟨hx, rfl⟩⟩

theorem mem_refinementQuotientMap (U Rf Rc z : ZFSet.{u}) :
    z ∈ refinementQuotientMap U Rf Rc ↔
      ∃ x ∈ U, z = ZFSet.pair (equivalenceClass U Rf x) (equivalenceClass U Rc x) := by
  constructor
  · intro hz
    obtain ⟨C, _, D, _, rfl⟩ := ZFSet.mem_prod.1 (refinementQuotientMap_subset U Rf Rc hz)
    obtain ⟨x, hx, rfl, rfl⟩ := (pair_mem_refinementQuotientMap U Rf Rc C D).1 hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (pair_mem_refinementQuotientMap U Rf Rc _ _).2 ⟨x, hx, rfl, rfl⟩

theorem refinementQuotientMap_class_entry {U Rf Rc x : ZFSet.{u}} (hx : x ∈ U) :
    ZFSet.pair (equivalenceClass U Rf x) (equivalenceClass U Rc x) ∈
      refinementQuotientMap U Rf Rc :=
  (pair_mem_refinementQuotientMap U Rf Rc _ _).2 ⟨x, hx, rfl, rfl⟩

theorem refinementQuotientMap_value_iff {U Rf Rc x D : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) (hx : x ∈ U) :
    ZFSet.pair (equivalenceClass U Rf x) D ∈ refinementQuotientMap U Rf Rc ↔
      D = equivalenceClass U Rc x := by
  constructor
  · intro entry
    obtain ⟨y, hy, equal, rfl⟩ :=
      (pair_mem_refinementQuotientMap U Rf Rc _ D).1 entry
    exact ((coarse.class_eq_iff hx hy).2
      (refinement ((fine.class_eq_iff hx hy).1 equal))).symm
  · rintro rfl
    exact refinementQuotientMap_class_entry hx

theorem refinementQuotientMap_function {U Rf Rc : ZFSet.{u}}
    (fine : EquivalenceRelationCode U Rf) (coarse : EquivalenceRelationCode U Rc)
    (refinement : Rf ⊆ Rc) :
    ZFSet.IsFunc (equivalenceClasses U Rf) (equivalenceClasses U Rc)
      (refinementQuotientMap U Rf Rc) := by
  refine ⟨refinementQuotientMap_subset U Rf Rc, ?_⟩
  intro C hC
  obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses U Rf C).1 hC
  exact ⟨equivalenceClass U Rc x, refinementQuotientMap_class_entry hx,
    fun D entry => (refinementQuotientMap_value_iff fine coarse refinement hx).1 entry⟩

theorem refinementQuotientMap_onto {U Rf Rc D : ZFSet.{u}}
    (hD : D ∈ equivalenceClasses U Rc) :
    ∃ C ∈ equivalenceClasses U Rf, ZFSet.pair C D ∈ refinementQuotientMap U Rf Rc := by
  obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses U Rc D).1 hD
  exact ⟨equivalenceClass U Rf x, equivalenceClass_mem hx,
    refinementQuotientMap_class_entry hx⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem equivalenceClass_eq_of_carrier_subset {T U R : ZFSet.{u}}
    (subset : U ⊆ T) (shape : R ⊆ ZFSet.prod U U) (x : ZFSet.{u}) :
    equivalenceClass T R x = equivalenceClass U R x := by
  apply ZFSet.ext
  intro y
  rw [mem_equivalenceClass, mem_equivalenceClass]
  exact ⟨fun h => ⟨(ZFSet.pair_mem_prod.1 (shape h.2)).1, h.2⟩,
    fun h => ⟨subset h.1, h.2⟩⟩

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

theorem eval_refinementQuotient (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (U R : Name s)
    (hU : U ∈ D.names) (hR : R ∈ D.names)
    (terms : ∀ w : Name s, w.val ∈ T → w ∈ D.names)
    (pairs : ∀ z w : Name s, z.val ∈ T → w.val ∈ T → orderedPair ⊤ z w ∈ D.names)
    (subset : eval {p | H.mem p} U ⊆ eval {p | H.mem p} (familySet ⊤ T valid))
    (shape : eval {p | H.mem p} R ⊆ ZFSet.prod (eval {p | H.mem p} U) (eval {p | H.mem p} U)) :
    eval {p | H.mem p} (refinementQuotient T valid U R) =
      equivalenceClasses (eval {p | H.mem p} U) (eval {p | H.mem p} R) := by
  have value (w : Name s) (hw : w.val ∈ T) :=
    (eval_refinementClass D H generic T valid R w hR (fun z hz => pairs z w hz hw)).trans
      (equivalenceClass_eq_of_carrier_subset subset shape (eval {p | H.mem p} w))
  apply ZFSet.ext
  intro C
  rw [refinementQuotient, mem_eval_activeImage D H generic T valid U _ hU terms,
    mem_equivalenceClasses]
  constructor
  · rintro ⟨w, hw, active, equal⟩
    exact ⟨eval {p | H.mem p} w, active, equal.symm.trans (value w hw)⟩
  · rintro ⟨x, hx, equal⟩
    obtain ⟨w, hw, rfl⟩ :=
      (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).1 (subset hx)
    exact ⟨w, hw, hx, (value w hw).trans equal.symm⟩

theorem eval_refinementNaturalMap (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D))
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s)
    (hU : U ∈ D.names) (hRf : Rf ∈ D.names) (hRc : Rc ∈ D.names)
    (terms : ∀ w : Name s, w.val ∈ T → w ∈ D.names)
    (pairs : ∀ z w : Name s, z.val ∈ T → w.val ∈ T → orderedPair ⊤ z w ∈ D.names)
    (subset : eval {p | H.mem p} U ⊆ eval {p | H.mem p} (familySet ⊤ T valid))
    (fine : eval {p | H.mem p} Rf ⊆ ZFSet.prod (eval {p | H.mem p} U) (eval {p | H.mem p} U))
    (coarse : eval {p | H.mem p} Rc ⊆ ZFSet.prod (eval {p | H.mem p} U) (eval {p | H.mem p} U)) :
    eval {p | H.mem p} (refinementNaturalMap T valid U Rf Rc) =
      refinementQuotientMap (eval {p | H.mem p} U) (eval {p | H.mem p} Rf) (eval {p | H.mem p} Rc) := by
  have value (w : Name s) (hw : w.val ∈ T) :
      eval {p | H.mem p} (orderedPair ⊤ (refinementClass T valid Rf w) (refinementClass T valid Rc w)) =
      ZFSet.pair (equivalenceClass (eval {p | H.mem p} U) (eval {p | H.mem p} Rf) (eval {p | H.mem p} w))
        (equivalenceClass (eval {p | H.mem p} U) (eval {p | H.mem p} Rc) (eval {p | H.mem p} w)) := by
    rw [eval_orderedPair {p | H.mem p} ⊤ H.top_mem,
      eval_refinementClass D H generic T valid Rf w hRf (fun z hz => pairs z w hz hw),
      eval_refinementClass D H generic T valid Rc w hRc (fun z hz => pairs z w hz hw),
      equivalenceClass_eq_of_carrier_subset subset fine,
      equivalenceClass_eq_of_carrier_subset subset coarse]
  apply ZFSet.ext
  intro z
  rw [refinementNaturalMap, mem_eval_activeImage D H generic T valid U _ hU terms,
    mem_refinementQuotientMap]
  constructor
  · rintro ⟨w, hw, active, equal⟩
    exact ⟨eval {p | H.mem p} w, active, equal.symm.trans (value w hw)⟩
  · rintro ⟨x, hx, equal⟩
    obtain ⟨w, hw, rfl⟩ :=
      (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).1 (subset hx)
    exact ⟨w, hw, hx, (value w hw).trans equal.symm⟩

end Name

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRefinementValidityForcing
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
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem refinementValidity_eval (env : Assignment (M.nameDomain s) 4)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula env p) :
    RefinementValidityCode
      (Name.eval {q | H.mem q} (env 3).val) (Name.eval {q | H.mem q} (env 0).val)
      (Name.eval {q | H.mem q} (env 1).val) (Name.eval {q | H.mem q} (env 2).val) := by
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  have truth := forces_sound (M.nameDomain s) H generic _ env hp forced
  exact (evaluated.realize_refinementValidityFormula
    (evalAssignment {q | H.mem q} env) (fun j => ⟨env j, rfl⟩)).1 truth

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNormalizedRefinementOutputs
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

theorem equivalenceClass_empty_of_not_mem {U R x : ZFSet.{u}}
    (shape : R ⊆ ZFSet.prod U U) (inactive : x ∉ U) : equivalenceClass U R x = ∅ := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    exact False.elim (inactive (ZFSet.pair_mem_prod.1 (shape (mem_equivalenceClass U R x y |>.1 hy).2)).2)
  · exact False.elim ∘ ZFSet.notMem_empty y

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem refinementObjects_eval
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (hFamily : (Name.familySet ⊤ T valid).val ∈ M.sets)
    (U Rf Rc : (M.nameDomain s).names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (forced : Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula
      (M.refinementNameEnv s T valid hFamily U Rf Rc) p) :
    RefinementObjectValues {q | H.mem q} T valid U.val Rf.val Rc.val := by
  have validity : RefinementValidityCode (Name.eval {q | H.mem q} (Name.familySet ⊤ T valid))
      (Name.eval {q | H.mem q} U.val) (Name.eval {q | H.mem q} Rf.val) (Name.eval {q | H.mem q} Rc.val) :=
    M.refinementValidity_eval s (M.refinementNameEnv s T valid hFamily U Rf Rc) H generic hp forced
  have atomic : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE dense => generic E (Or.inl hE) dense
  have terms (w : Name s) (hw : w.val ∈ T) : w ∈ (M.nameDomain s).names := M.transitive hT hw
  have pairs (z w : Name s) (hz : z.val ∈ T) (hw : w.val ∈ T) :
      Name.orderedPair ⊤ z w ∈ (M.nameDomain s).names := by
    change (Name.orderedPair ⊤ z w).val ∈ M.sets
    rw [Name.orderedPair_code]
    exact M.orderedPairNameCode_mem pairing (M.transitive carrier (s.encode_mem ⊤))
      (M.transitive hT hz) (M.transitive hT hw)
  have fineClass (w : Name s) (hw : w.val ∈ T) :=
    (M.eval_refinementClass s pairing carrier hT valid Rf.val w Rf.property (M.transitive hT hw) H generic).trans
      (equivalenceClass_eq_of_carrier_subset validity.1 validity.2.1.shape (Name.eval {q | H.mem q} w))
  have coarseClass (w : Name s) (hw : w.val ∈ T) :=
    (M.eval_refinementClass s pairing carrier hT valid Rc.val w Rc.property (M.transitive hT hw) H generic).trans
      (equivalenceClass_eq_of_carrier_subset validity.1 validity.2.2.1.shape (Name.eval {q | H.mem q} w))
  have fineQuotient := Name.eval_refinementQuotient (M.nameDomain s) H atomic T valid U.val Rf.val
    U.property Rf.property terms pairs validity.1 validity.2.1.shape
  have coarseQuotient := Name.eval_refinementQuotient (M.nameDomain s) H atomic T valid U.val Rc.val
    U.property Rc.property terms pairs validity.1 validity.2.2.1.shape
  have naturalMap := Name.eval_refinementNaturalMap (M.nameDomain s) H atomic T valid U.val Rf.val Rc.val
    U.property Rf.property Rc.property terms pairs validity.1 validity.2.1.shape validity.2.2.1.shape
  refine ⟨validity, fineClass, coarseClass, fineQuotient, coarseQuotient, naturalMap, ?_, ?_, ?_⟩
  · rw [fineQuotient, coarseQuotient, naturalMap]
    exact refinementQuotientMap_function validity.2.1 validity.2.2.1 validity.2.2.2
  · intro C hC
    rw [coarseQuotient] at hC
    obtain ⟨D, hD, entry⟩ := refinementQuotientMap_onto (Rf := Name.eval {q | H.mem q} Rf.val) hC
    exact ⟨D, fineQuotient.symm ▸ hD, naturalMap.symm ▸ entry⟩
  · intro w hw inactive
    rw [fineClass w hw, coarseClass w hw]
    exact ⟨equivalenceClass_empty_of_not_mem validity.2.1.shape inactive,
      equivalenceClass_empty_of_not_mem validity.2.2.1.shape inactive⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u

theorem normalizedRefinementOutputs
    (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
    (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (normalized : Assignment (M.nameDomain s) 4)
    (last : (normalized 3).val = Name.familySet ⊤ T valid)
    (forced : Forces (M.nameDomain s)
      BoundedFormula.refinementValidityFormula.toFormula normalized ⊤) :
    (Name.refinementQuotient T valid (normalized 0).val (normalized 1).val).val ∈ M.sets ∧
    (Name.refinementQuotient T valid (normalized 0).val (normalized 2).val).val ∈ M.sets ∧
    (Name.refinementNaturalMap T valid (normalized 0).val (normalized 1).val
      (normalized 2).val).val ∈ M.sets ∧
    ∀ H : ConditionFilter P, H.GenericFor (formulaFamily (M.nameDomain s)) →
      RefinementObjectValues {p | H.mem p} T valid
        (normalized 0).val (normalized 1).val (normalized 2).val := by
  have familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets := by
    rw [← last]
    exact (normalized 3).property
  have lastName : normalized 3 = ⟨Name.familySet ⊤ T valid, familyGround⟩ := Subtype.ext last
  have sameEnv : normalized = M.refinementNameEnv s T valid familyGround
      (normalized 0) (normalized 1) (normalized 2) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases lastName (fun j => Fin.elim0 j)))) i
  refine ⟨M.refinementQuotient_mem s pairing unions powers separation collection carrier order
      hT valid _ _ (normalized 0).property (normalized 1).property,
    M.refinementQuotient_mem s pairing unions powers separation collection carrier order
      hT valid _ _ (normalized 0).property (normalized 2).property,
    M.refinementNaturalMap_mem s pairing unions powers separation collection carrier order
      hT valid _ _ _ (normalized 0).property (normalized 1).property (normalized 2).property, ?_⟩
  intro H generic
  exact M.refinementObjects_eval s pairing carrier hT valid familyGround
    (normalized 0) (normalized 1) (normalized 2) H generic H.top_mem (sameEnv ▸ forced)

end PartitionPilot.Forcing.TransitiveGround

end

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

theorem semanticStructuralTrace_refinementOutputs_oai (small : M.sets.Countable)
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
          ZFSet.pair beta (M.niceRefinementIndices lowerAct lower b d beta T T2 validT) ∈
            refinementDataHistoryField K packed 0 ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            refinementDataHistoryIndices K packed ∧
          (Name.refinementQuotient T validT (normalized 0).val (normalized 1).val).val ∈ M.sets ∧
          (Name.refinementQuotient T validT (normalized 0).val (normalized 2).val).val ∈ M.sets ∧
          (Name.refinementNaturalMap T validT (normalized 0).val (normalized 1).val
            (normalized 2).val).val ∈ M.sets ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          (∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val) ∧
          RefinementObjectValues {p | (projection.projectedFilter H).mem p} T validT
            (normalized 0).val (normalized 1).val (normalized 2).val ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementQuotient T validT (normalized 0).val (normalized 1).val) =
            equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 1).val) ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementQuotient T validT (normalized 0).val (normalized 2).val) =
            equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 2).val) ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementNaturalMap T validT (normalized 0).val (normalized 1).val (normalized 2).val) =
            refinementQuotientMap (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 1).val) (Name.eval {p | H.mem p} (tau 2).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
    (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
  dsimp only
  intro tau symmetric
  obtain ⟨beta, hBeta, result⟩ := M.semanticStructuralTrace_storedRefinementIndices
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT small
    square growth tau symmetric
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
  dsimp only at result
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, stored, attained, preserved⟩ := result
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
  obtain ⟨fineGround, coarseGround, mapGround, outputValues⟩ := M.normalizedRefinementOutputs
    lower pairing unions powers separation collection hLower hOrder T hT
    ((termData 0).2 beta cutOrdinal subset) normalized family forced
  refine ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, stored, attained, fineGround, coarseGround, mapGround, ?_⟩
  intro H upperGeneric lowerCoded lowerGeneric originalValid
  have same := preserved H upperGeneric lowerCoded lowerGeneric originalValid
  have values := outputValues _ lowerGeneric
  refine ⟨same, values, ?_, ?_, ?_⟩
  · exact values.fine_quotient.trans (congrArg₂ equivalenceClasses (same 0) (same 1))
  · exact values.coarse_quotient.trans (congrArg₂ equivalenceClasses (same 0) (same 2))
  · exact values.natural_map.trans
      ((congrArg₂ (fun U R => refinementQuotientMap U R _) (same 0) (same 1)).trans
        (congrArg (refinementQuotientMap _ _) (same 2)))

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementOutputs_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralTrace_refinementOutputs_oai.{u}
