-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_augmentedClassRequests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:33:12.796385+00:00
-- url     : https://prove2.me/submissions/00f0d9dd-232f-42dd-bf42-e8774be3d166

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
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem eval_subset_familySet_of_code_subset (H : ConditionFilter P)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (tau : Name s)
    (shape : tau.val ⊆ ZFSet.prod T s.carrier) :
    eval {p | H.mem p} tau ⊆ eval {p | H.mem p} (familySet ⊤ T valid) := by
  intro x member
  obtain ⟨sigma, p, entry, _, value⟩ := (mem_eval {p | H.mem p} tau x).1 member
  have term : sigma.val ∈ T := (ZFSet.pair_mem_prod.1 (shape entry)).1
  exact (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).2
    ⟨sigma, term, value⟩

end PartitionPilot.Forcing.Name



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



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
include closed

theorem act_refinementQuotient (g : G) (U R : Name s) :
    a.act s g (refinementQuotient T valid U R) =
      refinementQuotient T valid (a.act s g U) (a.act s g R) := by
  apply act_activeImage a T valid closed g U
  intro w _
  exact act_refinementClass a T valid closed g R w

theorem refinementQuotient_support (U R : Name s) (K : Subgroup G)
    (activity : K ≤ a.stabilizer s U) (relation : K ≤ a.stabilizer s R) :
    K ≤ a.stabilizer s (refinementQuotient T valid U R) := by
  intro g hg
  change a.act s g _ = _
  rw [act_refinementQuotient a T valid closed, activity hg, relation hg]

theorem refinementNaturalMap_support (U Rf Rc : Name s) (K : Subgroup G)
    (activity : K ≤ a.stabilizer s U) (fine : K ≤ a.stabilizer s Rf)
    (coarse : K ≤ a.stabilizer s Rc) :
    K ≤ a.stabilizer s (refinementNaturalMap T valid U Rf Rc) := by
  intro g hg
  change a.act s g _ = _
  rw [act_refinementNaturalMap a T valid closed, activity hg, fine hg, coarse hg]

theorem refinementClass_hs_of_hs (F : NormalSubgroupFamily G)
    (children : ∀ w : Name s, w.val ∈ T → HereditarilySymmetric a s F w)
    (R w : Name s) (relation : HereditarilySymmetric a s F R)
    (representative : HereditarilySymmetric a s F w) :
    HereditarilySymmetric a s F (refinementClass T valid R w) :=
  refinementClass_hs a F T valid closed children R w
    (a.stabilizer s R ⊓ a.stabilizer s w) (F.inf relation.symmetric representative.symmetric)
    (fun _ hg => hg.1) (fun _ hg => hg.2)

theorem refinementQuotient_hs (F : NormalSubgroupFamily G)
    (children : ∀ w : Name s, w.val ∈ T → HereditarilySymmetric a s F w)
    (U R : Name s) (activity : HereditarilySymmetric a s F U)
    (relation : HereditarilySymmetric a s F R) :
    HereditarilySymmetric a s F (refinementQuotient T valid U R) := by
  refine HereditarilySymmetric.mk
    (F.upward (F.inf activity.symmetric relation.symmetric)
      (refinementQuotient_support a T valid closed U R
        (a.stabilizer s U ⊓ a.stabilizer s R) (fun _ hg => hg.1) (fun _ hg => hg.2))) ?_
  intro σ p entry
  obtain ⟨w, hw, _, rfl⟩ := (entry_refinementQuotient T valid U R σ p).1 entry
  exact refinementClass_hs_of_hs a T valid closed F children R w relation (children w hw)

theorem refinementNaturalMap_hs (F : NormalSubgroupFamily G)
    (children : ∀ w : Name s, w.val ∈ T → HereditarilySymmetric a s F w)
    (U Rf Rc : Name s) (activity : HereditarilySymmetric a s F U)
    (fine : HereditarilySymmetric a s F Rf) (coarse : HereditarilySymmetric a s F Rc) :
    HereditarilySymmetric a s F (refinementNaturalMap T valid U Rf Rc) := by
  refine HereditarilySymmetric.mk
    (F.upward (F.inf activity.symmetric (F.inf fine.symmetric coarse.symmetric))
      (refinementNaturalMap_support a T valid closed U Rf Rc
        (a.stabilizer s U ⊓ (a.stabilizer s Rf ⊓ a.stabilizer s Rc))
        (fun _ hg => hg.1) (fun _ hg => hg.2.1) (fun _ hg => hg.2.2))) ?_
  intro σ p entry
  obtain ⟨w, hw, _, rfl⟩ := (entry_refinementNaturalMap T valid U Rf Rc σ p).1 entry
  exact (refinementClass_hs_of_hs a T valid closed F children Rf w fine (children w hw)).orderedPair
    (refinementClass_hs_of_hs a T valid closed F children Rc w coarse (children w hw))

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundAssignmentClassGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem assignmentClassGraph_mem (side : Fin 2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A field T P order top : ZFSet.{u}}
    (hA : A ∈ M.sets) (hField : field ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (hOrder : order ∈ M.sets) (hTop : top ∈ M.sets) :
    M.assignmentClassGraph side A field T P order top ∈ M.sets :=
  M.separation_mem separation (assignmentClassGraphFormula side) _
    (Fin.cases hA (Fin.cases hField (Fin.cases hT (Fin.cases hP
      (Fin.cases hOrder (Fin.cases hTop (fun j => Fin.elim0 j)))))))
    (M.prod_mem pairing unions powers separation hA
      (M.groundRelations_mem pairing unions powers separation hT hP))

private theorem realize_assignmentClassGraphFormula (side : Fin 2)
    (env : Fin 7 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (assignmentClassGraphFormula side) env ↔
      ∃ w : Fin 6 → ZFSet.{u}, (∀ j, w j ∈ M.sets) ∧
        w 0 ∈ env 1 ∧ env 0 = ZFSet.pair (w 0) (w 1) ∧
        w 0 = stageOneAssignment (w 2) (w 3) (w 4) ∧
        ZFSet.pair (w 2) (w 5) ∈ env 2 ∧
        Realize M.sets refinementClassCodeFormula
          ![w 1, env 3, w 5, Fin.cases (w 3) (fun _ => w 4) side,
            env 4, env 5, env 6] := by
  rw [assignmentClassGraphFormula, realize_exBlock]
  apply exists_congr
  intro w
  apply and_congr_right
  intro ground
  have args : (fun j : Fin 7 => extendMany 6 w env
      (![prefixIndex 7 6 1, suffixIndex 7 6 3, prefixIndex 7 6 5,
        Fin.cases (prefixIndex 7 6 3) (fun _ => prefixIndex 7 6 4) side,
        suffixIndex 7 6 4, suffixIndex 7 6 5, suffixIndex 7 6 6] j)) =
      ![w 1, env 3, w 5, Fin.cases (w 3) (fun _ => w 4) side, env 4, env 5, env 6] := by
    funext j
    refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases ?_
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
    exact Fin.cases rfl (fun _ => rfl) side
  simp only [Realize, BoundedFormula.realize_toFormula M _ _
    (extendMany_members 6 w env ground members), BoundedFormula.truth_orderedPairFormula,
    BoundedFormula.truth_stageOneAssignmentFormula, BoundedFormula.truth_pairMembershipFormula,
    extendMany_prefix, extendMany_suffix, realize_reindex, args]

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem assignmentClassGraph_entry (side : Fin 2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {A field T : ZFSet.{u}} (hA : A ∈ M.sets) (hField : field ∈ M.sets) (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R u w : Name s)
    (hR : R.val ∈ M.sets) (hu : u.val ∈ M.sets) (hw : w.val ∈ M.sets)
    {i : ZFSet.{u}} (member : stageOneAssignment i u.val w.val ∈ A)
    (lookup : ∀ z, ZFSet.pair i z ∈ field ↔ z = R.val) (y : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u.val w.val) y ∈
      M.assignmentClassGraph side A field T s.carrier s.conditionOrder (s.encode ⊤) ↔
      y = (Name.refinementClass T valid R (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)).val := by
  have hTop := M.transitive carrier (s.encode_mem ⊤)
  have hAssignment := M.transitive hA member
  have hi := M.pair_left hAssignment
  have hBound := M.groundRelations_mem pairing unions powers separation hT carrier
  have hRepresentative : (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side).val ∈ M.sets :=
    Fin.cases hu (fun _ => hw) side
  have representative : (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side).val =
      Fin.cases (motive := fun _ => ZFSet.{u}) u.val (fun _ => w.val) side := Fin.cases rfl (fun _ => rfl) side
  let params : Fin 6 → ZFSet.{u} := ![A, field, T, s.carrier, s.conditionOrder, s.encode ⊤]
  have hp : ∀ j, params j ∈ M.sets := Fin.cases hA (Fin.cases hField (Fin.cases hT
    (Fin.cases carrier (Fin.cases order (Fin.cases hTop (fun j => Fin.elim0 j))))))
  rw [assignmentClassGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨_, hyB⟩, recognized⟩
    have hy := M.transitive hBound hyB
    obtain ⟨v, ground, _, equal, triple, relation, output⟩ :=
      (M.realize_assignmentClassGraphFormula side (extend _ params)
        (Fin.cases (M.orderedPair_mem pairing hAssignment hy) hp)).1 recognized
    obtain ⟨key, value⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨idx, first, second⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 (key.trans triple)
    have rel : v 5 = R.val := (lookup _).1 (idx.symm ▸ relation)
    dsimp only [params, extend, Matrix.cons_val_zero, Matrix.cons_val_succ] at output
    rw [← value, rel, ← first, ← second, ← representative] at output
    exact (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid R _ hR hRepresentative y hy).1 output
  · intro equal
    subst y
    have named := M.refinementClass_mem s pairing unions powers separation collection carrier order
      hT valid R _ hR hRepresentative
    have bound := (M.mem_groundRelations T s.carrier _).2
      ⟨named, Name.refinementClass_subset T valid R _⟩
    refine ⟨⟨member, bound⟩, ?_⟩
    apply (M.realize_assignmentClassGraphFormula side (extend _ params)
      (Fin.cases (M.orderedPair_mem pairing hAssignment named) hp)).2
    refine ⟨![stageOneAssignment i u.val w.val,
      (Name.refinementClass T valid R (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)).val, i, u.val, w.val, R.val],
      Fin.cases hAssignment (Fin.cases named (Fin.cases hi (Fin.cases hu
        (Fin.cases hw (Fin.cases hR (fun j => Fin.elim0 j)))))), member, rfl, rfl,
      (lookup _).2 rfl, ?_⟩
    have realizing := (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid R _ hR hRepresentative _ named).2 rfl
    rw [representative] at realizing
    exact realizing

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



end

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



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

namespace TransitiveGround
variable (M : TransitiveGround.{u}) (a : PosetAction G P) (s : Presentation P)
variable (b : Presentation L) (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem niceRefinementObjects
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {level T1 T2 : ZFSet.{u}} {valid1 : ∀ z ∈ T1, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
    (hl : level ∈ M.sets) (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (closed : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
    (children : ∀ w : Name s, w.val ∈ T1 →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) w)
    (first : NiceNameSystem M a s b d base directed T1 valid1)
    (second : NiceNameSystem M a s b d base directed T2 valid2) :
    NiceRefinementIndexSystem M a s b d level T1 T2 valid1 valid2 ∧
      ∀ C E (U Rf Rc : (M.nameDomain s).names),
        refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
          M.niceRefinementIndices a s b d level T1 T2 valid1 →
        RefinementObjectSystem M a s (d.principalSupportFamily base directed) (d.principalFix C)
          T1 valid1 U.val Rf.val Rc.val := by
  have indices := M.niceRefinementIndexSystem a s b d pairing unions powers separation collection
    hl hT1 hT2 carrier order nodes nodeOrder first second
  refine ⟨indices, ?_⟩
  intro C E U Rf Rc entry
  obtain ⟨_, hU, hRf, hRc, forced⟩ := (indices.typed_entries C E U Rf Rc).1 entry
  have supportedU := ((M.name_mem_niceNameCandidates a s T1 (d.principalFix C) U.val).1 hU).2.2
  have supportedRf := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rf.val).1 hRf).2.2
  have supportedRc := ((M.name_mem_niceNameCandidates a s T2 (d.principalFix C) Rc.val).1 hRc).2.2
  have hsU := first.candidate_hs C U.val hU
  have hsRf := second.candidate_hs C Rf.val hRf
  have hsRc := second.candidate_hs C Rc.val hRc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨M.refinementQuotient_mem s pairing unions powers separation collection carrier order
        hT1 valid1 U.val Rf.val U.property Rf.property,
      M.refinementQuotient_mem s pairing unions powers separation collection carrier order
        hT1 valid1 U.val Rc.val U.property Rc.property,
      M.refinementNaturalMap_mem s pairing unions powers separation collection carrier order
        hT1 valid1 U.val Rf.val Rc.val U.property Rf.property Rc.property⟩
  · exact ⟨Name.refinementQuotient_support a T1 valid1 closed U.val Rf.val _ supportedU supportedRf,
      Name.refinementQuotient_support a T1 valid1 closed U.val Rc.val _ supportedU supportedRc,
      Name.refinementNaturalMap_support a T1 valid1 closed U.val Rf.val Rc.val _ supportedU supportedRf supportedRc⟩
  · exact ⟨Name.refinementQuotient_hs a T1 valid1 closed _ children U.val Rf.val hsU hsRf,
      Name.refinementQuotient_hs a T1 valid1 closed _ children U.val Rc.val hsU hsRc,
      Name.refinementNaturalMap_hs a T1 valid1 closed _ children U.val Rf.val Rc.val hsU hsRf hsRc⟩
  · intro w hw
    exact ⟨M.refinementClass_mem s pairing unions powers separation collection carrier order
        hT1 valid1 Rf.val w Rf.property (M.transitive hT1 hw),
      M.refinementClass_mem s pairing unions powers separation collection carrier order
        hT1 valid1 Rc.val w Rc.property (M.transitive hT1 hw),
      Name.refinementClass_hs_of_hs a T1 valid1 closed _ children Rf.val w hsRf (children w hw),
      Name.refinementClass_hs_of_hs a T1 valid1 closed _ children Rc.val w hsRc (children w hw)⟩
  · exact ⟨M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
        hT1 hT1 valid1 valid1 Rf.val Rf.property,
      M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
        hT1 hT1 valid1 valid1 Rc.val Rc.property,
      M.refinementPairClassGraph_mem s pairing unions powers separation collection carrier order
        hT1 hT1 valid1 valid1 Rf.val Rc.val Rf.property Rc.property⟩
  · intro H generic
    exact M.refinementObjects_eval s pairing carrier hT1 valid1 indices.family_ground
      U Rf Rc H generic H.top_mem forced

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNiceAssignmentClassFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (members : ∀ j : Fin 15, (M.refinementLevelFormulaData a s b d level T T2 valid) j ∈ M.sets)
include pairing unions powers separation collection members

theorem niceAssignmentClassGraphs_entry {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (idx : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (u w : Name s) (hu : u.val ∈ T) (hw : w.val ∈ T)
    (member : stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val ∈ A) (side : Fin 2) (y : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val) y ∈ M.niceAssignmentClassGraphs a s b d level T T2 valid A side ↔
      y = (Name.refinementClass T valid
        (Fin.cases (motive := fun _ => Name s) Rc.val (fun _ => Rf.val) side)
        (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)).val := by
  have hT : T ∈ M.sets := members 6
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT (members 9) valid
  obtain ⟨_, _, hf, hc, _⟩ := (M.niceRefinementIndex_mem_iff a s b d pairing unions powers
    separation collection carrier order level T T2 valid family C E U Rf Rc).1 idx
  have fine := M.niceNameCandidates_subset a s T2 (d.principalFix C) hf
  have coarse := M.niceNameCandidates_subset a s T2 (d.principalFix C) hc
  have lookup (j : Fin 6) (R : Name s) (bound : R.val ∈ M.groundRelations T2 s.carrier)
      (value : (![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val] j) = R.val) :
      ∀ z, ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) z ∈
        refinementIndexFieldGraph I (M.groundRelations T2 s.carrier) j ↔ z = R.val := by
    intro z
    rw [refinementIndexCode, refinementIndexFieldGraph_entry, value]
    exact ⟨fun h => h.2.2, fun eq => ⟨idx, eq.symm ▸ bound, eq⟩⟩
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) side
  · dsimp only [niceAssignmentClassGraphs, Fin.cases_zero]
    exact M.assignmentClassGraph_entry s 0 pairing unions powers separation collection carrier order
      hA (members 5) hT valid Rc.val u w Rc.property (M.transitive hT hu) (M.transitive hT hw)
      member (lookup 5 Rc.val coarse rfl) y
  · dsimp only [niceAssignmentClassGraphs, Fin.cases_succ]
    exact M.assignmentClassGraph_entry s 1 pairing unions powers separation collection carrier order
      hA (members 4) hT valid Rf.val u w Rf.property (M.transitive hT hu) (M.transitive hT hw)
      member (lookup 4 Rf.val fine rfl) y

theorem niceAssignmentClassRequests
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (valid2 : ∀ z ∈ T2, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (children : ∀ z : Name s, z.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) z)
    (secondChildren : ∀ z : Name s, z.val ∈ T2 →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) z)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (shape : A ⊆ stageOneAssignments I T)
    (small : M.groundEmbeddable A ZFSet.omega) :
    let graphs := M.niceAssignmentClassGraphs a s b d level T T2 valid A
    let bound := M.groundRelations T s.carrier
    let J := relationImage A bound (graphs 0) ∪ relationImage A bound (graphs 1)
    (∀ side, graphs side ∈ M.sets ∧ ZFSet.IsFunc A bound (graphs side)) ∧
    J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
    (∀ z ∈ J, IsName s z) ∧
    ∀ z : Name s, z.val ∈ J →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
      ∀ H : ConditionFilter P, Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := by
  let graphs := M.niceAssignmentClassGraphs a s b d level T T2 valid A
  let bound := M.groundRelations T s.carrier
  have hT : T ∈ M.sets := members 6
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have hb := M.groundRelations_mem pairing unions powers separation hT carrier
  have hOmega := M.omega_mem separation infinite
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT (members 9) valid
  have request (side : Fin 2) (x : ZFSet.{u}) (hx : x ∈ A) :
      ∃ z : Name s, z.val ∈ bound ∧
        HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
        z.val ⊆ ZFSet.prod T s.carrier ∧
        ∀ y, ZFSet.pair x y ∈ graphs side ↔ y = z.val := by
    obtain ⟨i, hi, rawU, hu, rawW, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 (shape hx)
    obtain ⟨C, E, U, Rf, Rc, rfl⟩ := M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
    let u : Name s := ⟨rawU, valid rawU hu⟩
    let w : Name s := ⟨rawW, valid rawW hw⟩
    obtain ⟨_, _, hf, hc, _⟩ := (M.niceRefinementIndex_mem_iff a s b d pairing unions powers
      separation collection carrier order level T T2 valid family C E U Rf Rc).1 hi
    have fineHS := niceNameCode_principal_hs a s d base C directed secondChildren
      ((M.mem_niceNameCandidates a s T2 (d.principalFix C) Rf.val.val).1 hf).2
    have coarseHS := niceNameCode_principal_hs a s d base C directed secondChildren
      ((M.mem_niceNameCandidates a s T2 (d.principalFix C) Rc.val.val).1 hc).2
    have result (R : (M.nameDomain s).names) (z : Name s) (hz : z.val ∈ T)
        (hs : HereditarilySymmetric a s (d.principalSupportFamily base directed) R.val) :
        (Name.refinementClass T valid R.val z).val ∈ bound ∧
        HereditarilySymmetric a s (d.principalSupportFamily base directed)
          (Name.refinementClass T valid R.val z) ∧
        (Name.refinementClass T valid R.val z).val ⊆ ZFSet.prod T s.carrier :=
      ⟨(M.mem_groundRelations T s.carrier _).2
          ⟨M.refinementClass_mem s pairing unions powers separation collection carrier order
            hT valid R.val z R.property (M.transitive hT hz), Name.refinementClass_subset T valid R.val z⟩,
        Name.refinementClass_hs_of_hs a T valid closed _ children R.val z hs (children z hz),
        Name.refinementClass_subset T valid R.val z⟩
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) side
    · exact ⟨Name.refinementClass T valid Rc.val u, (result Rc u hu coarseHS).1,
        (result Rc u hu coarseHS).2.1, (result Rc u hu coarseHS).2.2,
        M.niceAssignmentClassGraphs_entry a s b d level T T2 valid pairing unions powers separation
          collection members hA C E U Rf Rc hi u w hu hw hx 0⟩
    · exact ⟨Name.refinementClass T valid Rf.val w, (result Rf w hw fineHS).1,
        (result Rf w hw fineHS).2.1, (result Rf w hw fineHS).2.2,
        M.niceAssignmentClassGraphs_entry a s b d level T T2 valid pairing unions powers separation
          collection members hA C E U Rf Rc hi u w hu hw hx 1⟩
  have grounds (side : Fin 2) : graphs side ∈ M.sets :=
    M.assignmentClassGraph_mem side pairing unions powers separation hA
      (members (Fin.cases 5 (fun _ => 4) side)) hT carrier order (members 9)
  have functions (side : Fin 2) : ZFSet.IsFunc A bound (graphs side) := by
    refine ⟨?_, ?_⟩
    · intro x h
      unfold graphs niceAssignmentClassGraphs assignmentClassGraph at h
      exact (ZFSet.mem_sep.1 h).1
    · intro x hx
      obtain ⟨z, _, _, _, entries⟩ := request side x hx
      exact ⟨z.val, (entries _).2 rfl, fun y h => (entries y).1 h⟩
  have imageGround (side : Fin 2) := M.relationImage_mem separation hA hb (grounds side)
  have imageSmall (side : Fin 2) := M.groundEmbeddable_function_image pairing unions powers
    separation choice hA hb hOmega (grounds side) (functions side) small
  have imageFacts (side : Fin 2) (y : ZFSet.{u})
      (member : y ∈ relationImage A bound (graphs side)) :
      ∃ z : Name s, y = z.val ∧ HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
        z.val ⊆ ZFSet.prod T s.carrier := by
    obtain ⟨_, x, hx, edge⟩ := (mem_relationImage A bound (graphs side) y).1 member
    obtain ⟨z, _, symmetric, subset, entries⟩ := request side x hx
    exact ⟨z, (entries y).1 edge, symmetric, subset⟩
  have allFacts (y : ZFSet.{u}) (member : y ∈ relationImage A bound (graphs 0) ∪
      relationImage A bound (graphs 1)) :
      ∃ z : Name s, y = z.val ∧ HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
        z.val ⊆ ZFSet.prod T s.carrier :=
    (ZFSet.mem_union.1 member).elim (imageFacts 0 y) (imageFacts 1 y)
  refine ⟨fun side => ⟨grounds side, functions side⟩,
    M.binary_union_mem pairing unions (imageGround 0) (imageGround 1),
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      (imageGround 0) (imageGround 1) (imageSmall 0) (imageSmall 1), ?_, ?_⟩
  · intro y member
    obtain ⟨z, rfl, _, _⟩ := allFacts y member
    exact z.property
  · intro z member
    obtain ⟨w, equal, symmetric, subset⟩ := allFacts z.val member
    have same : z = w := Subtype.ext equal
    subst w
    exact ⟨symmetric, fun H => Name.eval_subset_familySet_of_code_subset H T valid z subset⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem mem_assignmentOnIndices (B T A z : ZFSet.{u}) :
    z ∈ assignmentOnIndices B T A ↔ z ∈ A ∧ z ∈ stageOneAssignments B T :=
  ZFSet.mem_sep

theorem assignmentOnIndices_entry (B T A t u w : ZFSet.{u}) :
    stageOneAssignment t u w ∈ assignmentOnIndices B T A ↔
      stageOneAssignment t u w ∈ A ∧ t ∈ B ∧ u ∈ T ∧ w ∈ T := by
  rw [mem_assignmentOnIndices, stageOneAssignment_mem_assignments]

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem assignmentOnIndices_mem {B T A : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentOnIndices B T A ∈ M.sets :=
  M.bounded_separation_mem separation (.mem 0 1)
    (extend (stageOneAssignments B T) Fin.elim0)
    (Fin.cases (M.stageOneAssignments_mem pairing unions powers separation hB hT)
      (fun i => Fin.elim0 i)) hA

theorem assignmentOnIndices_small {B T A N : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets)
    (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentOnIndices B T A) N :=
  M.groundEmbeddable_restrict separation
    (M.assignmentOnIndices_mem pairing unions powers separation hB hT hA) hN
    (fun _ hz => (mem_assignmentOnIndices B T A _).1 hz |>.1) small

theorem assignmentOnIndices_candidate {rows I T B row A : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (member : ZFSet.pair row A ∈ M.stageOneCandidateBound rows I T) :
    ZFSet.pair row (assignmentOnIndices B T A) ∈ M.stageOneCandidateBound rows B T := by
  obtain ⟨hr, hA, _, small⟩ := (M.pair_mem_stageOneCandidateBound rows I T row A).1 member
  exact (M.pair_mem_stageOneCandidateBound rows B T row _).2
    ⟨hr, M.assignmentOnIndices_mem pairing unions powers separation hB hT hA,
      fun _ hz => (mem_assignmentOnIndices B T A _).1 hz |>.2,
      M.assignmentOnIndices_small pairing unions powers separation hB hT hA omega small⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedIndexAssignmentSlices
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

theorem mem_fixedIndexAssignmentPairs (idx T A v w : ZFSet.{u}) :
    ZFSet.pair v w ∈ fixedIndexAssignmentPairs idx T A ↔
      v ∈ T ∧ w ∈ T ∧ stageOneAssignment idx v w ∈ A := by
  rw [fixedIndexAssignmentPairs, mem_relationImage]
  constructor
  · rintro ⟨bound, x, hx, edge⟩
    obtain ⟨i, hi, pair, _, equal⟩ := (mem_productSecond _ _ _).1 edge
    have ei : i = idx := ZFSet.mem_singleton.1 hi
    obtain ⟨ex, ep⟩ := ZFSet.pair_inj.1 equal
    subst i
    subst pair
    exact ⟨(ZFSet.pair_mem_prod.1 bound).1, (ZFSet.pair_mem_prod.1 bound).2,
      ex ▸ (mem_assignmentOnIndices _ _ _ _).1 hx |>.1⟩
  · rintro ⟨hv, hw, old⟩
    have bounds := ZFSet.pair_mem_prod.2 ⟨hv, hw⟩
    exact ⟨bounds, stageOneAssignment idx v w,
      (assignmentOnIndices_entry _ _ _ _ _ _).2 ⟨old, ZFSet.mem_singleton.2 rfl, hv, hw⟩,
      (mem_productSecond _ _ _).2 ⟨idx, ZFSet.mem_singleton.2 rfl, _, bounds, rfl⟩⟩

theorem fixedIndexAssignmentClassGraph_entry (idx T A B graph v w y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair v w) y ∈ fixedIndexAssignmentClassGraph idx T A B graph ↔
      v ∈ T ∧ w ∈ T ∧ stageOneAssignment idx v w ∈ A ∧ y ∈ B ∧
        ZFSet.pair (stageOneAssignment idx v w) y ∈ graph := by
  rw [fixedIndexAssignmentClassGraph, pair_mem_relationCompose, mem_fixedIndexAssignmentPairs]
  constructor
  · rintro ⟨⟨hv, hw, old⟩, hy, x, _, inverse, edge⟩
    have projection := ((pair_mem_relationConverse _ _ _ x (ZFSet.pair v w)).1 inverse).2.2
    obtain ⟨i, hi, pair, _, equal⟩ := (mem_productSecond _ _ _).1 projection
    have ei : i = idx := ZFSet.mem_singleton.1 hi
    obtain ⟨ex, ep⟩ := ZFSet.pair_inj.1 equal
    subst i
    subst pair
    subst x
    exact ⟨hv, hw, old, hy, edge⟩
  · rintro ⟨hv, hw, old, hy, edge⟩
    have bound := ZFSet.pair_mem_prod.2 ⟨hv, hw⟩
    have triple := (stageOneAssignment_mem_assignments {idx} T idx v w).2
      ⟨ZFSet.mem_singleton.2 rfl, hv, hw⟩
    exact ⟨⟨hv, hw, old⟩, hy, _, triple,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨triple, bound,
        (mem_productSecond _ _ _).2 ⟨idx, ZFSet.mem_singleton.2 rfl, _, bound, rfl⟩⟩, edge⟩

theorem fixedIndexAssignmentClassGraph_function {idx T A B graph D : ZFSet.{u}}
    (function : ZFSet.IsFunc D B graph)
    (covered : ∀ v ∈ T, ∀ w ∈ T, stageOneAssignment idx v w ∈ A →
      stageOneAssignment idx v w ∈ D) :
    ZFSet.IsFunc (fixedIndexAssignmentPairs idx T A) B
      (fixedIndexAssignmentClassGraph idx T A B graph) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    unfold fixedIndexAssignmentClassGraph relationCompose at hz
    exact (ZFSet.mem_sep.1 hz).1
  · intro pair member
    have pairBound := (mem_relationImage _ _ _ pair).1 member |>.1
    obtain ⟨v, hv, w, hw, rfl⟩ := ZFSet.mem_prod.1 pairBound
    have old := (mem_fixedIndexAssignmentPairs idx T A v w).1 member |>.2.2
    obtain ⟨y, edge, unique⟩ := function.2 _ (covered v hv w hw old)
    have hy := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
    exact ⟨y, (fixedIndexAssignmentClassGraph_entry _ _ _ _ _ _ _ _).2 ⟨hv, hw, old, hy, edge⟩,
      fun z hz => unique z ((fixedIndexAssignmentClassGraph_entry _ _ _ _ _ _ _ _).1 hz).2.2.2.2⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem fixedIndexAssignmentPairs_mem_small
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {idx T A N : ZFSet.{u}} (hIdx : idx ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    fixedIndexAssignmentPairs idx T A ∈ M.sets ∧
      M.groundEmbeddable (fixedIndexAssignmentPairs idx T A) N := by
  have singleton : ({idx} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hIdx hIdx
  have slice := M.assignmentOnIndices_mem pairing unions powers separation singleton hT hA
  have sliceSmall := M.assignmentOnIndices_small pairing unions powers separation singleton hT hA hN small
  have bound := M.prod_mem pairing unions powers separation hT hT
  have graph := M.productSecond_mem pairing unions powers separation singleton bound
  exact ⟨M.relationImage_mem separation slice bound graph,
    M.groundEmbeddable_function_image pairing unions powers separation choice slice bound hN
      graph (productSecond_function {idx} (ZFSet.prod T T)) sliceSmall⟩

theorem fixedIndexAssignmentClassGraph_mem
    {idx T A B graph : ZFSet.{u}} (hIdx : idx ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hGraph : graph ∈ M.sets) :
    fixedIndexAssignmentClassGraph idx T A B graph ∈ M.sets := by
  have singleton : ({idx} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hIdx hIdx
  have pairs := M.prod_mem pairing unions powers separation hT hT
  have slice := M.assignmentOnIndices_mem pairing unions powers separation singleton hT hA
  have projection := M.productSecond_mem pairing unions powers separation singleton pairs
  have domain := M.relationImage_mem separation slice pairs projection
  have triples := M.stageOneAssignments_mem pairing unions powers separation singleton hT
  exact M.relationCompose_mem pairing unions powers separation domain triples hB
    (M.relationConverse_mem pairing unions powers separation triples pairs projection) hGraph

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAugmentedClassRequests
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

theorem semanticStructuralPrefix_assignmentClassRequests
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let I := M.niceRefinementIndices act lower b d alpha T T2 valid
    let selected := assignmentOnIndices I T A
    let graphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid selected
    let bound := M.groundRelations T lower.carrier
    let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
    selected ∈ M.sets ∧ M.groundEmbeddable selected ZFSet.omega ∧
    (∀ side, graphs side ∈ M.sets ∧ ZFSet.IsFunc selected bound (graphs side)) ∧
    J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
    (∀ z ∈ J, IsName lower z) ∧
    (∀ z : Name lower, z.val ∈ J →
      HereditarilySymmetric act lower (d.principalSupportFamily base directed) z ∧
      ∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
    (∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names)
      (_idx : refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ I)
      (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∀ (side : Fin 2) y, ZFSet.pair (stageOneAssignment
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val w.val) y ∈ graphs side ↔
        y = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let I := M.niceRefinementIndices act lower b d alpha T T2 valid
  let selected := assignmentOnIndices I T A
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have fields : ∀ j, M.refinementLevelFormulaData act lower b d alpha T T2 valid j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem _ (M.transitive
      (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion entry))
  have candidate := ((M.mem_refinementHistoryForcing c.carrier T stages packed _).1 condition).1
  have selectedCandidate := M.assignmentOnIndices_candidate pairing unions powers separation
    (fields 0) hT omega candidate
  obtain ⟨_, hSelected, selectedShape, selectedSmall⟩ :=
    (M.pair_mem_stageOneCandidateBound c.carrier I T row selected).1 selectedCandidate
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨_, closed, children⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  obtain ⟨validSecond, _, secondChildren⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T2 valid2 closed2 symmetric2
  obtain ⟨graphs, hJ, smallJ, validJ, facts⟩ := M.niceAssignmentClassRequests act lower b d alpha T T2 valid
    pairing unions powers separation collection fields infinite choice base directed validSecond closed
    children secondChildren hSelected selectedShape selectedSmall
  refine ⟨hSelected, selectedSmall, graphs, hJ, smallJ, validJ, facts, ?_⟩
  intro C E U Rf Rc idx u w hu hw inA side y
  have inSelected : stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ selected :=
    (mem_assignmentOnIndices I T A _).2 ⟨inA,
      (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨idx, hu, hw⟩⟩
  exact M.niceAssignmentClassGraphs_entry act lower b d alpha T T2 valid pairing unions powers
    separation collection fields hSelected C E U Rf Rc idx u w hu hw inSelected side y

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

theorem semanticStructuralPrefix_fixedIndexClassFamilies
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let I := M.niceRefinementIndices act lower b d alpha T T2 valid
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
    let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    idx ∈ I →
    let oldPairs := fixedIndexAssignmentPairs idx T A
    let bound := M.groundRelations T lower.carrier
    let originalGraphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid
      (assignmentOnIndices I T A)
    let graphs := fun side => fixedIndexAssignmentClassGraph idx T A bound (originalGraphs side)
    let images := fun side => relationImage oldPairs bound (graphs side)
    oldPairs ∈ M.sets ∧ M.groundEmbeddable oldPairs ZFSet.omega ∧
    ∀ side : Fin 2, graphs side ∈ M.sets ∧ ZFSet.IsFunc oldPairs bound (graphs side) ∧
      images side ∈ M.sets ∧ M.groundEmbeddable (images side) ZFSet.omega ∧
      (∀ z ∈ images side, IsName lower z) ∧
      (∀ z, z ∈ images side ↔ ∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
        stageOneAssignment idx v.val w.val ∈ A ∧
        z = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) v (fun _ => w) side)).val) ∧
      (∀ (v w : Name lower), v.val ∈ T → w.val ∈ T →
        stageOneAssignment idx v.val w.val ∈ A → ∀ z,
        ZFSet.pair (ZFSet.pair v.val w.val) z ∈ graphs side ↔
        z = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) v (fun _ => w) side)).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let I := M.niceRefinementIndices act lower b d alpha T T2 valid
  dsimp only
  intro C E U Rf Rc inI
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let oldPairs := fixedIndexAssignmentPairs idx T A
  let bound := M.groundRelations T lower.carrier
  let selected := assignmentOnIndices I T A
  let originalGraphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid selected
  let graphs := fun side => fixedIndexAssignmentClassGraph idx T A bound (originalGraphs side)
  let images := fun side => relationImage oldPairs bound (graphs side)
  obtain ⟨_, _, original, _, _, validImages, _, entries⟩ :=
    M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice condition
  have candidate := ((M.mem_refinementHistoryForcing c.carrier T stages packed _).1 condition).1
  obtain ⟨_, hA, _, smallA⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  have hIdx : idx ∈ M.sets := M.refinementIndexCode_mem pairing hAlpha
    (M.transitive nodes (b.encode_mem C)) (M.transitive nodes (b.encode_mem E))
    U.property Rf.property Rc.property
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hBound := M.groundRelations_mem pairing unions powers separation hT hQ
  obtain ⟨hPairs, smallPairs⟩ := M.fixedIndexAssignmentPairs_mem_small pairing unions powers separation
    choice hIdx hT hA omega smallA
  have covered (v : ZFSet.{u}) (hv : v ∈ T) (w : ZFSet.{u}) (hw : w ∈ T)
      (old : stageOneAssignment idx v w ∈ A) : stageOneAssignment idx v w ∈ selected :=
    (assignmentOnIndices_entry _ _ _ _ _ _).2 ⟨old, inI, hv, hw⟩
  refine ⟨hPairs, smallPairs, ?_⟩
  intro side
  have graphGround : graphs side ∈ M.sets := M.fixedIndexAssignmentClassGraph_mem pairing unions powers
    separation hIdx hT hA hBound (original side).1
  have function : ZFSet.IsFunc oldPairs bound (graphs side) :=
    fixedIndexAssignmentClassGraph_function (original side).2 covered
  have exactEntry (v w : Name lower) (hv : v.val ∈ T) (hw : w.val ∈ T)
      (old : stageOneAssignment idx v.val w.val ∈ A) (z : ZFSet.{u}) :
      ZFSet.pair (ZFSet.pair v.val w.val) z ∈ graphs side ↔
        z = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) v (fun _ => w) side)).val := by
    rw [fixedIndexAssignmentClassGraph_entry]
    have entry := entries C E U Rf Rc inI v w hv hw old side z
    constructor
    · intro edge
      exact entry.1 edge.2.2.2.2
    · intro equal
      have edge := entry.2 equal
      exact ⟨hv, hw, old, (ZFSet.pair_mem_prod.1 ((original side).2.1 edge)).2, edge⟩
  have imageSubset : images side ⊆ relationImage selected bound (originalGraphs side) := by
    intro z hz
    obtain ⟨hy, pair, hp, edge⟩ := (mem_relationImage _ _ _ z).1 hz
    have pb := (mem_relationImage _ _ _ pair).1 hp |>.1
    obtain ⟨v, hv, w, hw, rfl⟩ := ZFSet.mem_prod.1 pb
    have fields := (fixedIndexAssignmentClassGraph_entry _ _ _ _ _ _ _ _).1 edge
    exact (mem_relationImage _ _ _ z).2 ⟨hy, _, covered v hv w hw fields.2.2.1, fields.2.2.2.2⟩
  refine ⟨graphGround, function, M.relationImage_mem separation hPairs hBound graphGround,
    M.groundEmbeddable_function_image pairing unions powers separation choice hPairs hBound omega
      graphGround function smallPairs, ?_, ?_, exactEntry⟩
  · intro z hz
    apply validImages z
    have liftImage : ∀ side : Fin 2, ∀ z, z ∈ relationImage selected bound (originalGraphs side) →
        z ∈ relationImage selected bound (originalGraphs 0) ∪ relationImage selected bound (originalGraphs 1) :=
      Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inl hz))
        (Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inr hz)) (fun j => Fin.elim0 j))
    exact liftImage side z (imageSubset hz)
  · intro z
    constructor
    · intro hz
      obtain ⟨_, pair, hp, edge⟩ := (mem_relationImage _ _ _ z).1 hz
      have pb := (mem_relationImage _ _ _ pair).1 hp |>.1
      obtain ⟨v, hv, w, hw, rfl⟩ := ZFSet.mem_prod.1 pb
      have old := (mem_fixedIndexAssignmentPairs idx T A v w).1 hp |>.2.2
      let vName : Name lower := ⟨v, valid v hv⟩
      let wName : Name lower := ⟨w, valid w hw⟩
      exact ⟨vName, wName, hv, hw, old, (exactEntry vName wName hv hw old z).1 edge⟩
    · rintro ⟨v, w, hv, hw, old, equal⟩
      have edge := (exactEntry v w hv hw old z).2 equal
      exact (mem_relationImage _ _ _ z).2
        ⟨(ZFSet.pair_mem_prod.1 (function.1 edge)).2, ZFSet.pair v.val w.val,
          (mem_fixedIndexAssignmentPairs _ _ _ _ _).2 ⟨hv, hw, old⟩, edge⟩

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

theorem semanticStructuralPrefix_augmentedClassRequests_oai
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc u : (M.nameDomain lower).names),
    let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid → u.val.val ∈ T →
    let oldFine := M.fixedIndexOldFineClassImage act lower b d alpha T T2 valid idx A
    let J := M.fixedIndexAugmentedRequests act lower b d alpha T T2 valid idx A Rc.val u.val
    oldFine ∈ M.sets ∧ M.groundEmbeddable oldFine ZFSet.omega ∧
    J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
    (∀ z ∈ J, IsName lower z) ∧ J ⊆ M.groundRelations T lower.carrier ∧
    (∀ z : Name lower, z.val ∈ J →
      HereditarilySymmetric act lower (d.principalSupportFamily base directed) z ∧
      (∃ V : L, d.principalFix V ≤ (act).stabilizer lower z) ∧
      z.val ⊆ ZFSet.prod T lower.carrier ∧
      ∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
    (∀ z, z ∈ oldFine ↔ ∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
      stageOneAssignment idx v.val w.val ∈ A ∧ z = (Name.refinementClass T valid Rf.val w).val) ∧
    (∀ z, z ∈ J ↔ z = (Name.refinementClass T valid Rc.val u.val).val ∨
      ∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
        stageOneAssignment idx v.val w.val ∈ A ∧ z = (Name.refinementClass T valid Rf.val w).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  dsimp only
  intro C E U Rf Rc u idx hu
  let index := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let oldFine := M.fixedIndexOldFineClassImage act lower b d alpha T T2 valid index A
  let J := M.fixedIndexAugmentedRequests act lower b d alpha T T2 valid index A Rc.val u.val
  obtain ⟨_, _, families⟩ := M.semanticStructuralPrefix_fixedIndexClassFamilies c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice condition C E U Rf Rc idx
  obtain ⟨_, _, oldGround, oldSmall, _, oldEntry, _⟩ := families 1
  have exactOld (z : ZFSet.{u}) : z ∈ oldFine ↔ ∃ v w : Name lower,
      v.val ∈ T ∧ w.val ∈ T ∧ stageOneAssignment index v.val w.val ∈ A ∧
        z = (Name.refinementClass T valid Rf.val w).val := oldEntry z
  have system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hLower : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have objects := (M.niceRefinementObjects act lower b d base directed pairing unions powers separation
    collection hAlpha hT hT2 hLower lowerOrder nodes nodeOrder system.inputs.terms_closed
    system.terms_hs system.first system.second).2 C E U Rf Rc idx
  have coarseGround := (objects.classes u.val hu).2.1
  have coarseHS := (objects.classes u.val hu).2.2.2
  have jGround : J ∈ M.sets := M.insert_mem pairing unions coarseGround oldGround
  have jSmall : M.groundEmbeddable J ZFSet.omega :=
    M.groundEmbeddable_insert pairing unions powers separation infinite oldGround coarseGround oldSmall
  have exactJ (z : ZFSet.{u}) : z ∈ J ↔
      z = (Name.refinementClass T valid Rc.val u.val).val ∨ ∃ v w : Name lower,
        v.val ∈ T ∧ w.val ∈ T ∧ stageOneAssignment index v.val w.val ∈ A ∧
          z = (Name.refinementClass T valid Rf.val w).val := by
    change z ∈ insert (Name.refinementClass T valid Rc.val u.val).val oldFine ↔ _
    rw [ZFSet.mem_insert_iff, exactOld]
  have classFacts (z : ZFSet.{u}) (hz : z ∈ J) :
      ∃ name : Name lower, z = name.val ∧
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) name ∧
        name.val ⊆ ZFSet.prod T lower.carrier := by
    rcases (exactJ z).1 hz with equal | ⟨v, w, _hv, hw, _old, equal⟩
    · exact ⟨Name.refinementClass T valid Rc.val u.val, equal, coarseHS,
        Name.refinementClass_subset T valid Rc.val u.val⟩
    · exact ⟨Name.refinementClass T valid Rf.val w, equal, (objects.classes w hw).2.2.1,
        Name.refinementClass_subset T valid Rf.val w⟩
  refine ⟨oldGround, oldSmall, jGround, jSmall, ?_, ?_, ?_, exactOld, exactJ⟩
  · intro z hz
    obtain ⟨name, rfl, _, _⟩ := classFacts z hz
    exact name.property
  · intro z hz
    obtain ⟨name, rfl, _, bound⟩ := classFacts z hz
    exact (M.mem_groundRelations T lower.carrier name.val).2 ⟨M.transitive jGround hz, bound⟩
  · intro z hz
    obtain ⟨name, equal, hsName, bound⟩ := classFacts z.val hz
    have same : z = name := Subtype.ext equal
    subst name
    exact ⟨hsName, hsName.symmetric, bound,
      fun H => Name.eval_subset_familySet_of_code_subset H T valid z bound⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_augmentedClassRequests_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_augmentedClassRequests_oai.{u}
