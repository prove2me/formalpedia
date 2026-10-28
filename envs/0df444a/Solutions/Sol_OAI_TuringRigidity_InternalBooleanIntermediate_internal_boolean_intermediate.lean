-- Prove2me | solution 1 for OAI.TuringRigidity.InternalBooleanIntermediate.internal_boolean_intermediate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:03:21.497802+00:00
-- url     : https://prove2.me/submissions/0f449c0a-d0b1-4e86-ab62-f28d16e6d74c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericFilterName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

theorem val_genericFilterName (p : ZFSet.{u}) [Top (Conditions p)]
    (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    (genericFilterName p).val G = genericFilterSet p G := by
  apply ZFSet.ext; intro x
  simp only [genericFilterName,Name.mem_val,Name.val_check G hG,mem_genericFilterSet,id_eq]

theorem eval_filterCodeFormula (z p f r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    filterCodeFormula.Eval (cons z (cons p (cons f (cons r e)))) ↔
      ∃ x ∈ p, ∃ v ∈ r, ZFSet.pair x v ∈ f ∧ z = ZFSet.pair v x := by
  simp only [filterCodeFormula,Formula.Eval,Formula.eval_pairMem,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem mem_filterCode (p f z : ZFSet.{u}) :
    z ∈ filterCode p f ↔ ∃ x ∈ p, ∃ v, ZFSet.pair x v ∈ f ∧ z = ZFSet.pair v x := by
  rw [filterCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,hx,v,_,hv,hz⟩; exact ⟨x,hx,v,hv,hz⟩
  · rintro ⟨x,hx,v,hv,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,x,hx,rfl⟩,x,hx,v,hr,hv,rfl⟩

theorem filterCode_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {p f : ZFSet.{u}} (hp : p ∈ M) (hf : f ∈ M) : filterCode p f ∈ M := by
  have hr := iterUnion_mem M hM hU hf 2
  let e := cons p (cons f (cons (iterUnion 2 f) (fun _ => p)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hp
    rcases i with _|i; exact hf
    rcases i with _|i; exact hr
    exact hp
  have hs := sep_mem M hM hS filterCodeFormula e he
    (product_mem M hM hP hU hPow hS hr hp)
  have heq : ZFSet.sep (fun z => filterCodeFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) p) = filterCode p f := by
    apply ZFSet.ext; intro z
    simp only [filterCode,ZFSet.mem_sep]
    exact and_congr_right (fun _ => eval_filterCodeFormula z p f _ _)
  exact heq ▸ hs

theorem encode_genericFilterName (p d r f : ZFSet.{u}) [Top (Conditions p)]
    (hsub : p ⊆ d) (hf : CheckGraph d r f (label p ⊤)) :
    (genericFilterName p).encode (label p) = filterCode p f := by
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,mem_filterCode]
  constructor
  · rintro ⟨q,hq⟩
    have hx := hsub (label_mem p q)
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 (label p q) hx
    have he := hf.correct _ hx v hv hfv
    refine ⟨label p q,label_mem p q,v,hfv,?_⟩
    simpa only [genericFilterName,id_eq,encode_check,he] using hq.symm
  · rintro ⟨x,hx,v,hfv,hz⟩
    obtain ⟨q,rfl⟩ := label_surjective p hx
    have hfr : FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
    have he := hf.correct _ (hsub hx) v (hfr.value_mem hfv) hfv
    exact ⟨q,by simpa only [genericFilterName,id_eq,encode_check,he] using hz.symm⟩

theorem genericFilterName_mem (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) : genericFilterName p ∈ names M p := by
  obtain ⟨d,hdM,hd,hpd⟩ := internal_transitive_container M hM hP hU hS hR hI hp
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label p ⊤) hM hP hU hPow hS hR
    hdM hqM (hM p hp _ (label_mem p ⊤)) hd hq p hpd
  have hsub : p ⊆ hull d q p := fun x hx =>
    hull_transitive d q p hd p (self_mem_hull d q hpd) x hx
  change (genericFilterName p).encode (label p) ∈ M
  rw [encode_genericFilterName p _ _ f hsub hfg]
  exact filterCode_mem M hM hP hU hPow hS hp hf

theorem genericFilterSet_mem_extension (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    genericFilterSet p G ∈ genericExtensionSet M p G :=
  (mem_extensionSet M p G _).mpr ⟨genericFilterName p,
    genericFilterName_mem M p hM hP hU hPow hS hR hI hp,val_genericFilterName p G hG⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFunctionOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem mem_orbitGraph (a : ℕ → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ orbitGraph a ↔ ∃ n, z = ZFSet.pair (natSet n) (a n) := by
  rw [orbitGraph,ZFSet.mem_range]
  exact ⟨fun ⟨n,hn⟩ => ⟨n,hn.symm⟩,fun ⟨n,hn⟩ => ⟨n,hn.symm⟩⟩

theorem orbitGraph_pair (a : ℕ → ZFSet.{u}) (n : ℕ) (x : ZFSet.{u}) :
    ZFSet.pair (natSet n) x ∈ orbitGraph a ↔ x = a n := by
  rw [mem_orbitGraph]
  constructor
  · rintro ⟨m,he⟩
    obtain ⟨hn,hx⟩ := ZFSet.pair_inj.mp he
    have hnm := natSet_injective hn
    exact hnm.symm ▸ hx
  · intro h; exact ⟨n,congrArg (ZFSet.pair (natSet n)) h⟩

theorem orbitGraph_function (d : ZFSet.{u}) (a : ℕ → ZFSet.{u}) (ha : ∀ n, a n ∈ d) :
    TransitiveNameModel.FunctionGraph ZFSet.omega d (orbitGraph a) := by
  constructor
  · intro z hz
    obtain ⟨n,rfl⟩ := (mem_orbitGraph a z).mp hz
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,a n,ha n,rfl⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨a n,ha n,(orbitGraph_pair a n _).mpr rfl,fun y _ hy => (orbitGraph_pair a n y).mp hy⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenInternalDecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenInternalDecision
open Set TransitiveNameModel BoundedSetTheory CohenAntichainStages CohenGroundPoset
open CohenConditionCode CohenSymmetry CohenCoordinates

theorem decision_mem (M c U E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (hE : E ∈ M) : decision c U E ∈ M := by
  let e := cons U (fun _ => E)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hU; exact hE
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.disj (.existsMem 2 (.subset 0 1)) (.allMem 1 (.neg (.subset 1 0)))) e he hc
  simpa only [decision,Formula.eval_disj,Formula.eval_allMem,Formula.Eval,
    Formula.eval_subset,cons_zero,cons_succ,e] using hs

end TuringRigidity.CohenInternalDecision

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealGeneratedPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RealGeneratedPart
open Set CountableForcing RegularCompletion
universe u
variable {P : Type u} [Preorder P]

theorem decision_dense (N : ℕ → Set P) (n : ℕ) : Dense (decision N n) := by
  classical
  intro p
  by_cases h : ∃ q, q ≤ p ∧ q ∈ tagLower (N n)
  · obtain ⟨q,hqp,hq⟩ := h
    exact ⟨q,hqp,Or.inl hq⟩
  · exact ⟨p,le_rfl,Or.inr ((mem_compl _ p).mpr (fun q hqp hq => h ⟨q,hqp,hq⟩))⟩

theorem bit_hit_iff (N : ℕ → Set P) (G : GenericFilter P)
    (hG : GenericFor (decision N) G) (n : ℕ) :
    (∃ p ∈ G.carrier, p ∈ (bit N n : LowerSet P)) ↔ n ∈ value N G := by
  constructor
  · rintro ⟨p,hp,hpbit⟩
    obtain ⟨q,hq,hqdec⟩ := hG n
    rcases hqdec with ⟨r,hr,hqr⟩ | hqneg
    · exact ⟨r,G.upper hqr hq,hr⟩
    · obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
      have hrbit : r ∈ (bit N n : LowerSet P) := (bit N n : LowerSet P).lower hrp hpbit
      have hrneg := ((tagLower (N n))ᶜ).lower hrq hqneg
      exact False.elim ((mem_compl ((tagLower (N n))ᶜ) r).mp hrbit r le_rfl hrneg)
  · rintro ⟨p,hp,hpN⟩
    exact ⟨p,hp,(show tagLower (N n) ≤ ((bit N n : LowerSet P)) from le_compl_compl)
      ⟨p,hpN,le_rfl⟩⟩

end TuringRigidity.RealGeneratedPart

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularOperations
open Set TransitiveNameModel BoundedSetTheory RegularCompletion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem join_mem (M c F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hF : F ∈ M) : supCode c F ∈ M :=
  regular_mem M c _ hM hT hc (union_mem M hM hT.union hF)

end TuringRigidity.InternalRegularOperations

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularAlgebra
open Set TransitiveNameModel BoundedSetTheory RegularCompletion InternalRegularOperations
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem isCode_iff (c U : ZFSet.{0}) : IsCode c U ↔
    U ⊆ c ∧ ∀ p ∈ c, p ∈ U ↔ ∀ q ∈ c, p ⊆ q → ∃ r ∈ U, q ⊆ r := by
  constructor
  · rintro ⟨hUc,hU⟩
    refine ⟨hUc,fun p hp => ?_⟩
    have h := mem_regular c U p
    rw [hU] at h
    exact h.trans (and_iff_right hp)
  · rintro ⟨hUc,hU⟩
    refine ⟨hUc,ZFSet.ext (fun p => ?_)⟩
    rw [mem_regular]
    exact ⟨fun h => (hU p h.1).mpr h.2,fun h => ⟨hUc h,(hU p (hUc h)).mp h⟩⟩

theorem codeFormula_spec (c U : ℕ) (e : ℕ → ZFSet.{0}) :
    (codeFormula c U).Eval e ↔ IsCode (e c) (e U) := by
  rw [isCode_iff]
  simp only [codeFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_imp,cons_zero,cons_succ]

theorem internal_algebra (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) : ∃ B ∈ M, ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hc
  let B := Q.sep (IsCode c)
  have hB : B ∈ M := by
    have hs := sep_mem M hM hT.separation.finitePrefix.bounded
      (codeFormula 1 0) (fun _ => c) (fun _ => hc) hQ
    simpa only [codeFormula_spec,cons_zero,cons_succ] using hs
  refine ⟨B,hB,fun U => ?_⟩
  change (U ∈ Q.sep (IsCode c)) ↔ _
  rw [ZFSet.mem_sep,hQdef]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2⟩⟩

theorem internal_complement (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    {U : ZFSet.{0}} (hU : U ∈ B) : neg c U ∈ B :=
  (hB _).mpr ⟨neg_mem M c U hM hT hc ((hB U).mp hU).1,neg_isCode c U ((hB U).mp hU).2⟩

theorem internal_join (M c B F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) (hF : F ∈ M) :
    supCode c F ∈ B :=
  (hB _).mpr ⟨join_mem M c F hM hT hc hF,join_isCode c F⟩

end TuringRigidity.InternalRegularAlgebra

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanSyntax
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra

theorem supFormula_spec (c F V : ℕ) (e : ℕ → ZFSet.{0}) :
    (supFormula c F V).Eval e ↔ e V = supCode (e c) (e F) := by
  simp only [supFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_imp,cons_zero,cons_succ]
  have hu (q : ZFSet.{0}) : (∃ U ∈ e F, ∃ r ∈ U, q ⊆ r) ↔
      ∃ r ∈ ZFSet.sUnion (e F), q ⊆ r := by
    constructor
    · rintro ⟨U,hU,r,hr,hqr⟩; exact ⟨r,ZFSet.mem_sUnion.mpr ⟨U,hU,hr⟩,hqr⟩
    · rintro ⟨r,hr,hqr⟩; obtain ⟨U,hU,hr⟩ := ZFSet.mem_sUnion.mp hr
      exact ⟨U,hU,r,hr,hqr⟩
  simp only [hu]
  constructor
  · rintro ⟨hVc,hV⟩
    apply ZFSet.ext
    intro p
    rw [supCode,mem_regular]
    exact ⟨fun h => ⟨hVc h,(hV p (hVc h)).mp h⟩,fun h => (hV p h.1).mpr h.2⟩
  · intro h
    rw [h]
    refine ⟨(join_isCode _ _).1,fun p hp => ?_⟩
    exact (mem_regular _ _ p).trans (and_iff_right hp)

theorem closedFormula_spec (c B Q A : ℕ) (e : ℕ → ZFSet.{0}) :
    (closedFormula c B Q A).Eval e ↔ Closed (e c) (e B) (e Q) (e A) := by
  simp only [closedFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_imp,negFormula_spec,supFormula_spec,cons_zero,cons_succ,Closed]
  simp only [exists_eq_right]

theorem candidates_mem (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) :
    candidates c B Q S ∈ M := by
  let e := cons c (cons B (cons Q (fun _ => S)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact hc; exact hB; exact hQ; exact hS
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.conj (.subset 4 0) (closedFormula 1 2 3 0)) e he hQ
  simpa only [candidates,Formula.Eval,Formula.eval_subset,closedFormula_spec,
    cons_zero,cons_succ,e] using hs

end TuringRigidity.InternalBooleanSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalGeneratedAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalGeneratedAlgebra
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanSyntax

theorem generated_mem (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) :
    generated c B Q S ∈ M := by
  have hk := candidates_mem M c B Q S hM hT hc hB hQ hS
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.allMem 1 (.member 1 0)) (fun _ => candidates c B Q S) (fun _ => hk) hB
  simpa only [generated,Formula.eval_allMem,Formula.Eval,cons_zero,cons_succ] using hs

theorem generated_subset (c B Q S : ZFSet.{0}) : generated c B Q S ⊆ B :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem seeds_subset (c B Q S : ZFSet.{0}) (hS : S ⊆ B) : S ⊆ generated c B Q S := by
  intro U hU
  refine ZFSet.mem_sep.mpr ⟨hS hU,fun A hA => ?_⟩
  exact (ZFSet.mem_sep.mp hA).2.1 hU

theorem generated_le (c B Q S A : ZFSet.{0}) (hA : A ∈ Q)
    (hS : S ⊆ A) (hc : Closed c B Q A) : generated c B Q S ⊆ A := by
  intro U hU
  exact (ZFSet.mem_sep.mp hU).2 A (ZFSet.mem_sep.mpr ⟨hA,hS,hc⟩)

theorem algebra_closed (M c B Q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) : Closed c B Q B := by
  refine ⟨fun _ h => h,fun U hU => internal_complement M c B hM hT hc hB hU,?_⟩
  intro F hF _
  exact internal_join M c B F hM hT hc hB ((hQ F).mp hF).1

theorem generated_closed (c B Q S : ZFSet.{0}) (hB : Closed c B Q B) :
    Closed c B Q (generated c B Q S) := by
  refine ⟨generated_subset c B Q S,?_,?_⟩
  · intro U hU
    obtain ⟨hUB,hU⟩ := ZFSet.mem_sep.mp hU
    refine ZFSet.mem_sep.mpr ⟨hB.2.1 U hUB,fun A hA => ?_⟩
    exact (ZFSet.mem_sep.mp hA).2.2.2.1 U (hU A hA)
  · intro F hF hFS
    refine ZFSet.mem_sep.mpr ⟨hB.2.2 F hF (fun U hU => generated_subset c B Q S (hFS hU)),?_⟩
    intro A hA
    apply (ZFSet.mem_sep.mp hA).2.2.2.2 F hF
    intro U hU
    exact (ZFSet.mem_sep.mp (hFS hU)).2 A hA

end TuringRigidity.InternalGeneratedAlgebra

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanProjection
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanSyntax InternalGeneratedAlgebra

theorem project_le_iff (c A U V : ZFSet.{0}) (hUc : U ⊆ c) (hV : V ∈ A) :
    project c A U ⊆ V ↔ U ⊆ V := by
  constructor
  · intro h p hp; exact h (subset_project c A U hUc hp)
  · intro h; exact inf_subset c _ (ZFSet.mem_sep.mpr ⟨hV,h⟩)

theorem project_nonempty (c A U : ZFSet.{0}) (hUc : U ⊆ c) (hU : U ≠ ∅) : project c A U ≠ ∅ := by
  intro hp
  apply hU
  apply ZFSet.ext
  intro p
  constructor
  · intro h
    have hx := subset_project c A U hUc h
    rw [hp] at hx
    exact hx
  · exact fun h => False.elim (ZFSet.notMem_empty p h)

end TuringRigidity.InternalBooleanProjection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNaturalCheckSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalNaturalCheckSequence
open TransitiveNameModel BoundedSetTheory

theorem natural_check_sequence (M t : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ht : t ∈ M) : orbitGraph (fun n => checkedCode t (natSet n)) ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨d,hdM,hd,hωd⟩ := internal_transitive_container M hM hT.pairing hT.union hS
    hT.replacement.finitePrefix hT.infinity hω
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hT.powerSet hdM
  obtain ⟨g,hgM,hg⟩ := internal_checkGraph M d q t hM hT.pairing hT.union hT.powerSet hS
    hT.replacement.finitePrefix hdM hqM ht hd hq ZFSet.omega hωd
  let r := iterUnion 2 g
  have hrM : r ∈ M := iterUnion_mem M hM hT.union hgM 2
  have hn (n : ℕ) : natSet n ∈ hull d q ZFSet.omega :=
    hull_transitive d q ZFSet.omega hd _ (self_mem_hull d q hωd) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  have hpair (n : ℕ) (v : ZFSet.{0}) :
      ZFSet.pair (natSet n) v ∈ g ↔ v = checkedCode t (natSet n) := by
    rw [hg.mem_iff]
    constructor
    · rintro ⟨w,_,hp⟩
      obtain ⟨he,hv⟩ := ZFSet.pair_inj.mp hp
      exact he.symm ▸ hv
    · intro hv
      exact ⟨natSet n,hn n,congrArg (ZFSet.pair (natSet n)) hv⟩
  have hv (n : ℕ) : checkedCode t (natSet n) ∈ r :=
    second_mem_doubleUnion ((hpair n _).mpr rfl)
  let e := cons ZFSet.omega (cons r (fun _ => g))
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (.pairMem 1 0 5)))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hω; exact hrM; exact hgM
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      z ∈ orbitGraph (fun n => checkedCode t (natSet n)) := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,v,_,hz,hnv⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      exact (mem_orbitGraph _ z).mpr ⟨n,by rw [hz,(hpair n v).mp hnv]⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph _ z).mp hz
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,_,hv n,rfl,(hpair n _).mpr rfl⟩
  have hh := sep_mem M hM hS φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hrM)
  have heq : (ZFSet.prod ZFSet.omega r).sep (fun z => φ.Eval (cons z e)) =
      orbitGraph (fun n => checkedCode t (natSet n)) := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function r _ hv).1 z hz),hz⟩⟩
  exact heq ▸ hh

end TuringRigidity.InternalNaturalCheckSequence

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNiceName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalNiceName
open TransitiveNameModel BoundedSetTheory RecursiveNames CountableForcing
variable {c : ZFSet.{0}} [Top (Conditions c)]

theorem mem_encode_nice (E : ℕ → ZFSet.{0}) (z : ZFSet.{0}) :
    z ∈ (nice E : Name (Conditions c)).encode (label c) ↔
      ∃ n, ∃ p : Conditions c, label c p ∈ E n ∧
        z = ZFSet.pair (checkedCode (label c ⊤) (natSet n)) (label c p) := by
  simp only [nice,Name.encode,ZFSet.mem_range,encode_check]
  exact ⟨fun ⟨⟨n,p,hp⟩,hz⟩ => ⟨n,p,hp,hz.symm⟩,
    fun ⟨n,p,hp,hz⟩ => ⟨⟨n,p,hp⟩,hz.symm⟩⟩

theorem nice_internal (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hEgraph : orbitGraph E ∈ M) :
    (nice E : Name (Conditions c)).encode (label c) ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  have hEQ : ∀ n, E n ∈ Q := fun n => (hQ _).mpr (hE n)
  let B := orbitGraph (fun n => checkedCode (label c ⊤) (natSet n))
  have hBM : B ∈ M := InternalNaturalCheckSequence.natural_check_sequence M _ hM hT
    (hM c hc _ (label_mem c ⊤))
  let r := iterUnion 2 B
  have hrM := iterUnion_mem M hM hT.union hBM 2
  have hr (n : ℕ) : checkedCode (label c ⊤) (natSet n) ∈ r :=
    second_mem_doubleUnion ((orbitGraph_pair _ n _).mpr rfl)
  let e := cons ZFSet.omega (cons Q (cons r (cons c (cons B (fun _ => orbitGraph E)))))
  let φ : BoundedSetTheory.Formula := .existsMem 1 (.existsMem 3 (.existsMem 5 (.existsMem 7
    (.conj (.orderedPair 4 1 0) (.conj (.pairMem 3 1 9)
      (.conj (.pairMem 3 2 10) (.member 0 2)))))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact hω; exact hQM; exact hrM; exact hc; exact hBM; exact hEgraph
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      z ∈ (nice E : Name (Conditions c)).encode (label c) := by
    simp only [φ,BoundedSetTheory.Formula.Eval,BoundedSetTheory.Formula.eval_orderedPair,BoundedSetTheory.Formula.eval_pairMem,cons_zero,cons_succ,e]
    rw [mem_encode_nice]
    constructor
    · rintro ⟨n,hn,H,_,v,_,p,hp,hz,hnv,hnH,hpH⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨p,rfl⟩ := label_surjective c hp
      have hv := (orbitGraph_pair _ n v).mp hnv
      have hH := (orbitGraph_pair E n H).mp hnH
      exact ⟨n,p,hH ▸ hpH,by rw [hz,hv]⟩
    · rintro ⟨n,p,hp,rfl⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,hEQ n,_,hr n,_,label_mem c p,rfl,
        (orbitGraph_pair _ n _).mpr rfl,(orbitGraph_pair E n _).mpr rfl,hp⟩
  have hs := sep_mem M hM hS φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hrM hc)
  have heq : (ZFSet.prod r c).sep (fun z => φ.Eval (cons z e)) =
      (nice E : Name (Conditions c)).encode (label c) := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    refine ⟨And.right,fun hz => ⟨?_,hz⟩⟩
    obtain ⟨n,p,_,rfl⟩ := (mem_encode_nice E z).mp hz
    exact ZFSet.mem_prod.mpr ⟨_,hr n,_,label_mem c p,rfl⟩
  exact heq ▸ hs

theorem mem_val_nice (E : ℕ → ZFSet.{0}) (G : Set (Conditions c)) (hG : ⊤ ∈ G)
    (x : ZFSet.{0}) : x ∈ (nice E : Name (Conditions c)).val G ↔
      ∃ n, ∃ p ∈ G, label c p ∈ E n ∧ natSet n = x := by
  rw [nice,Name.mem_val]
  simp only [Name.val_check _ hG]
  exact ⟨fun ⟨⟨n,p,hp⟩,hpG,hx⟩ => ⟨n,p,hpG,hp,hx⟩,
    fun ⟨n,p,hpG,hp,hx⟩ => ⟨⟨n,p,hp⟩,hpG,hx⟩⟩

end TuringRigidity.InternalNiceName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRealQuotient
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRealQuotient
open Set CountableForcing TransitiveNameModel BoundedSetTheory RecursiveNames
open RegularCompletion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem label_below (c U : ZFSet.{0}) (hUc : U ⊆ c) (p : Conditions c) :
    label c p ∈ CohenInternalDecision.below c U ↔
      p ∈ RealGeneratedPart.tagLower {q | label c q ∈ U} := by
  rw [CohenInternalDecision.below,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,hq,hqp⟩
    obtain ⟨q,rfl⟩ := label_surjective c (hUc hq)
    exact ⟨q,hq,hqp⟩
  · rintro ⟨q,hq,hpq⟩
    exact ⟨label_mem c p,label c q,hq,hpq⟩

theorem label_decision (c : ZFSet.{0}) (E : ℕ → ZFSet.{0})
    (hEc : ∀ n, E n ⊆ c) (n : ℕ) (p : Conditions c) :
    label c p ∈ CohenInternalDecision.decision c (CohenInternalDecision.below c (E n)) (E n) ↔
      p ∈ RealGeneratedPart.decision (tags c E) n := by
  rw [CohenInternalDecision.decision,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,hp | hp⟩
    · obtain ⟨q,hq,hqp⟩ := hp
      obtain ⟨q,rfl⟩ := label_surjective c (hEc n hq)
      exact Or.inl ⟨q,hq,hqp⟩
    · apply Or.inr
      apply (mem_compl _ p).mpr
      intro q hqp hq
      exact hp (label c q) ((label_below c (E n) (hEc n) q).mpr hq) hqp
  · intro hp
    refine ⟨label_mem c p,?_⟩
    rcases hp with ⟨q,hq,hpq⟩ | hp
    · exact Or.inl ⟨label c q,hq,hpq⟩
    · apply Or.inr
      intro q hq hpq
      obtain ⟨q,rfl⟩ := label_surjective c (ZFSet.mem_sep.mp hq).1
      exact (mem_compl _ p).mp hp q hpq ((label_below c (E n) (hEc n) q).mp hq)

theorem ground_generic_decisions (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    GenericFor (RealGeneratedPart.decision (tags c E)) G := by
  intro n
  let D := CohenInternalDecision.decision c (CohenInternalDecision.below c (E n)) (E n)
  have hDM : D ∈ M := CohenInternalDecision.decision_mem M c _ _ hM hT hc
    (CohenInternalDecision.below_mem M c _ hM hT hc (hE n).1) (hE n).1
  have hd : Dense {p : Conditions c | label c p ∈ D} := by
    intro p
    obtain ⟨q,hqp,hq⟩ := RealGeneratedPart.decision_dense (tags c E) n p
    exact ⟨q,hqp,(label_decision c E (fun n => (hE n).2) n q).mpr hq⟩
  obtain ⟨p,hp,hpD⟩ := hG D hDM hd
  exact ⟨p,hp,(label_decision c E (fun n => (hE n).2) n p).mp hpD⟩

theorem nice_value_iff {c : ZFSet.{0}} [Top (Conditions c)]
    (E : ℕ → ZFSet.{0}) (G : GenericFilter (Conditions c)) (hTop : ⊤ ∈ G.carrier) (n : ℕ) :
    natSet n ∈ (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ↔
      n ∈ RealGeneratedPart.value (tags c E) G := by
  rw [InternalNiceName.mem_val_nice E G.carrier hTop]
  constructor
  · rintro ⟨m,p,hp,hpE,hmn⟩
    have he := natSet_injective hmn
    subst m
    exact ⟨p,hp,hpE⟩
  · rintro ⟨p,hp,hpE⟩
    exact ⟨n,p,hp,hpE,rfl⟩

end TuringRigidity.InternalRealQuotient

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanBits
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanBits
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanSyntax InternalGeneratedAlgebra
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem bitFormula_spec (c E V : ℕ) (e : ℕ → ZFSet.{0}) :
    (bitFormula c E V).Eval e ↔ e V = bitCode (e c) (e E) := by
  simp only [bitFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_imp,cons_zero,cons_succ]
  have hb (q : ZFSet.{0}) :
      (∃ r ∈ e c, q ⊆ r ∧ ∃ s ∈ e E, s ⊆ r) ↔
      ∃ r ∈ CohenInternalDecision.below (e c) (e E), q ⊆ r := by
    simp only [CohenInternalDecision.below,ZFSet.mem_sep]
    constructor
    · rintro ⟨r,hr,hqr,hs⟩; exact ⟨r,⟨hr,hs⟩,hqr⟩
    · rintro ⟨r,⟨hr,hs⟩,hqr⟩; exact ⟨r,hr,hqr,hs⟩
  simp only [hb]
  constructor
  · rintro ⟨hVc,hV⟩
    apply ZFSet.ext
    intro p
    rw [bitCode,mem_regular]
    exact ⟨fun h => ⟨hVc h,(hV p (hVc h)).mp h⟩,fun h => (hV p h.1).mpr h.2⟩
  · intro h
    rw [h]
    exact ⟨(regular_isCode _ _).1,fun p hp => (mem_regular _ _ p).trans (and_iff_right hp)⟩

theorem seeds_mem (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M) : seeds c B E ∈ M := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hc
  have hω := sourceT_omega_mem M hM hT
  let e := cons c (cons ZFSet.omega (cons Q (fun _ => orbitGraph E)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact hc; exact hω; exact hQ; exact hgraph
  let φ : Formula := .existsMem 2 (.existsMem 4 (.conj (.pairMem 1 0 6) (bitFormula 3 0 2)))
  have hφ (U : ZFSet.{0}) : φ.Eval (cons U e) ↔ ∃ n, U = bitCode c (E n) := by
    simp only [φ,Formula.Eval,Formula.eval_pairMem,bitFormula_spec,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,W,_,hp,hU⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hw := (orbitGraph_pair E n W).mp hp
      exact ⟨n,hw ▸ hU⟩
    · rintro ⟨n,hU⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,(hQdef _).mpr (hE n),
        (orbitGraph_pair E n _).mpr rfl,hU⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he hB
  simpa only [hφ,seeds] using hs

theorem bit_mem_seeds (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M) (n : ℕ) : bitCode c (E n) ∈ seeds c B E :=
  ZFSet.mem_sep.mpr ⟨(hB _).mpr ⟨bitCode_mem M c _ hM hT hc (hE n),regular_isCode c _⟩,n,rfl⟩

theorem interpret_bit (c : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ⊆ c) (n : ℕ) :
    interpret c (bitCode c (E n)) (regular_isCode c _) =
      RealGeneratedPart.bit (InternalRealQuotient.tags c E) n := by
  have hl : Lower c (CohenInternalDecision.below c (E n)) := by
    intro p hp q hq hpq
    obtain ⟨_,r,hr,hrp⟩ := ZFSet.mem_sep.mp hp
    exact ZFSet.mem_sep.mpr ⟨hq,r,hr,fun z hz => hpq (hrp hz)⟩
  have he : decode c (CohenInternalDecision.below c (E n)) hl =
      RealGeneratedPart.tagLower (InternalRealQuotient.tags c E n) := by
    apply SetLike.ext
    intro p
    exact InternalRealQuotient.label_below c (E n) (hE n) p
  apply Heyting.Regular.coe_injective
  change decode c (regular c (CohenInternalDecision.below c (E n))) (neg_lower c _) = _
  have hd := decode_regular c (CohenInternalDecision.below c (E n))
    (fun _ h => (ZFSet.mem_sep.mp h).1) hl
  apply hd.trans
  rw [he]
  rfl

theorem internal_bit_generated_part (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (hgraph : orbitGraph E ∈ M) :
    ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
      (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
      (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
      A = generated c B Q (seeds c B E) ∧ Closed c B Q A ∧
      (∀ n, bitCode c (E n) ∈ A) ∧
      ∀ A' ∈ Q, (∀ n, bitCode c (E n) ∈ A') → Closed c B Q A' → A ⊆ A' := by
  obtain ⟨B,hBM,hB⟩ := internal_algebra M c hM hT hc
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hBM
  have hS := seeds_mem M c B hM hT hc hBM E hE hgraph
  have hSB : seeds c B E ⊆ B := fun _ h => (ZFSet.mem_sep.mp h).1
  have hA := generated_mem M c B Q _ hM hT hc hBM hQM hS
  refine ⟨B,hBM,Q,hQM,generated c B Q (seeds c B E),hA,hB,hQ,rfl,
    generated_closed c B Q _ (algebra_closed M c B Q hM hT hc hB hQ),?_,?_⟩
  · intro n
    exact seeds_subset c B Q _ hSB (bit_mem_seeds M c B hM hT hc hB E (fun n => (hE n).1) n)
  · intro A' hA' hb hclosed
    apply generated_le c B Q _ A' hA' _ hclosed
    intro U hU
    obtain ⟨_,n,rfl⟩ := ZFSet.mem_sep.mp hU
    exact hb n

end TuringRigidity.InternalBooleanBits

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem hit_bit_iff (M c : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hTop : ⊤ ∈ G.carrier) (n : ℕ) :
    Hit G (bitCode c (E n)) ↔
      natSet n ∈ (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier := by
  have he := InternalBooleanBits.interpret_bit c E (fun n => (hE n).2) n
  have hv : Hit G (bitCode c (E n)) ↔
      ∃ p ∈ G.carrier, p ∈ (RealGeneratedPart.bit (InternalRealQuotient.tags c E) n : LowerSet (Conditions c)) := by
    change (∃ p ∈ G.carrier, p ∈ (interpret c (bitCode c (E n)) (regular_isCode c _) : LowerSet (Conditions c))) ↔ _
    rw [he]
  rw [hv,RealGeneratedPart.bit_hit_iff _ G
    (InternalRealQuotient.ground_generic_decisions M c hM hT hc E hE G hG)]
  exact (InternalRealQuotient.nice_value_iff E G hTop n).symm

end TuringRigidity.InternalBooleanGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanGraph
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanSyntax InternalBooleanProjection

theorem inclusionOrder_mem (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) : inclusionOrder A ∈ M := by
  have hp := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hA
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.subset 1 0))))
    (fun _ => A) (fun _ => hA) hp
  simpa only [inclusionOrder,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,
    cons_zero,cons_succ] using hs

theorem pair_inclusionOrder (A U V : ZFSet.{0}) : ZFSet.pair U V ∈ inclusionOrder A ↔
    U ∈ A ∧ V ∈ A ∧ U ⊆ V := by
  rw [inclusionOrder,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,U',hU,V',hV,he,hp⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hU,hV,hp⟩
  · rintro ⟨hU,hV,hp⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨U,hU,V,hV,rfl⟩,U,hU,V,hV,rfl,hp⟩

end TuringRigidity.InternalBooleanGraph

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanDense
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanDense
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem basicCode_le_iff (c p U : ZFSet.{0}) (hp : p ∈ c) (hU : IsCode c U) :
    basicCode c p ⊆ U ↔ p ∈ U := by
  constructor
  · intro h; exact h (mem_basicCode c p hp)
  · intro hpU
    apply (regular_le_iff c _ U (fun _ h => (ZFSet.mem_sep.mp h).1) (below_lower c {p}) hU).mpr
    intro q hq
    obtain ⟨hqc,r,hr,hrq⟩ := ZFSet.mem_sep.mp hq
    have hrp := ZFSet.mem_singleton.mp hr
    subst r
    exact code_lower c U hU p hpU q hqc hrq

theorem dense_preimage (M c B Q A D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (hD : DenseCodes A D) : Dense {p : Conditions c | label c p ∈ ZFSet.sUnion D} := by
  classical
  intro p
  let b := basicCode c (label c p)
  have hbM : b ∈ M := basicCode_mem M c _ hM hT hc (label_mem c p)
  have hbc : IsCode c b := regular_isCode c _
  have hpb : label c p ∈ b := mem_basicCode c _ (label_mem c p)
  have hb0 : b ≠ ∅ := fun h => ZFSet.notMem_empty _ (h ▸ hpb)
  have hPA := project_mem_part M c B Q A b hM hT hc hBM hAM hbM hB hQ hA
  obtain ⟨V,hVD,hVA,hV0,hVP⟩ := hD _ hPA (project_nonempty c A b hbc.1 hb0)
  have hVc := ((hB V).mp (hA.1 hVA)).2
  have hex : ∃ q ∈ V, label c p ⊆ q := by
    by_contra hn
    have hpN : label c p ∈ neg c V := ZFSet.mem_sep.mpr
      ⟨label_mem c p,fun q hq hpq => hn ⟨q,hq,hpq⟩⟩
    have hbN : b ⊆ neg c V := (basicCode_le_iff c _ _ (label_mem c p) (neg_isCode c V hVc)).mpr hpN
    have hPN := (project_le_iff c A b _ hbc.1 (hA.2.1 V hVA)).mpr hbN
    apply hV0
    apply ZFSet.ext
    intro q
    constructor
    · intro hq
      have hqN := hPN (hVP hq)
      exact False.elim ((ZFSet.mem_sep.mp hqN).2 q hq (fun _ h => h))
    · exact fun h => False.elim (ZFSet.notMem_empty q h)
  obtain ⟨q,hq,hpq⟩ := hex
  obtain ⟨q,rfl⟩ := label_surjective c (hVc.1 hq)
  exact ⟨q,hpq,ZFSet.mem_sUnion.mpr ⟨V,hVD,hq⟩⟩

theorem ground_meets_dense_codes (M c B Q A D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M) (hDM : D ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (hD : DenseCodes A D) (G : GenericFilter (Conditions c))
    (hG : AtomicForcing.GroundGeneric M G) : ∃ U ∈ D, Hit G U := by
  obtain ⟨p,hp,hpD⟩ := hG (ZFSet.sUnion D) (union_mem M hM hT.union hDM)
    (dense_preimage M c B Q A D hM hT hc hBM hAM hB hQ hA hD)
  obtain ⟨U,hU,hpU⟩ := ZFSet.mem_sUnion.mp hpD
  exact ⟨U,hU,p,hp,hpU⟩

end TuringRigidity.InternalBooleanDense

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalProjectedGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalProjectedGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric InternalBooleanDense
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem positive_mem (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) : positive A ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 0 (.equal 0 0)) (fun _ => A) (fun _ => hA) hA
  have he : A.sep (fun U => (Formula.existsMem 0 (.equal 0 0)).Eval (cons U (fun _ => A))) = positive A := by
    apply ZFSet.ext
    intro U
    simp only [positive,ZFSet.mem_sep,Formula.Eval,cons_zero]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨p,hp,_⟩ h0
      exact ZFSet.notMem_empty p (h0 ▸ hp)
    · intro hn
      obtain h0 | ⟨p,hp⟩ := ZFSet.eq_empty_or_nonempty U
      · exact False.elim (hn h0)
      · exact ⟨p,hp,True.intro⟩
  exact he ▸ hs

attribute [local instance] codeOrder codePreorder

theorem projected_ground_generic (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (projected M c B Q A hM hT hc hBM hAM hB hQ hA G) := by
  intro D hDM hD
  let D' := (positive A).sep (fun U => U ∈ D)
  have hD'M : D' ∈ M := by
    have hs := sep_mem M hM hT.separation.finitePrefix.bounded
      (.member 0 1) (fun _ => D) (fun _ => hDM) (positive_mem M A hM hT hAM)
    simpa only [D',Formula.Eval,cons_zero,cons_succ] using hs
  have hd : DenseCodes A D' := by
    intro U hUA hU0
    obtain ⟨p,hp⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hUA,hU0⟩)
    obtain ⟨q,hqp,hqD⟩ := hD p
    refine ⟨label (positive A) q,ZFSet.mem_sep.mpr ⟨label_mem _ q,hqD⟩,
      (label_info A q).1,(label_info A q).2,?_⟩
    change label (positive A) q ⊆ label (positive A) p at hqp
    rwa [hp] at hqp
  obtain ⟨U,hUD,hUG⟩ := ground_meets_dense_codes M c B Q A D' hM hT hc hBM hAM hD'M hB hQ hA hd G hG
  obtain ⟨hUp,hUD⟩ := ZFSet.mem_sep.mp hUD
  obtain ⟨p,hp⟩ := label_surjective (positive A) hUp
  exact ⟨p,(show Hit G (label (positive A) p) from hp.symm ▸ hUG),hp.symm ▸ hUD⟩

theorem projected_order_code (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) :
    InternalBooleanGraph.inclusionOrder (positive A) ∈ M ∧
      ∀ p q : Conditions (positive A),
        ZFSet.pair (label (positive A) p) (label (positive A) q) ∈
          InternalBooleanGraph.inclusionOrder (positive A) ↔ p ≤ q := by
  refine ⟨InternalBooleanGraph.inclusionOrder_mem M _ hM hT (positive_mem M A hM hT hA),?_⟩
  intro p q
  rw [InternalBooleanGraph.pair_inclusionOrder]
  exact ⟨fun h => h.2.2,fun h => ⟨label_mem _ p,label_mem _ q,h⟩⟩

end TuringRigidity.InternalProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSameNameGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSameNameGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder InternalBooleanSyntax
open InternalGeneratedAlgebra InternalBooleanProjection InternalBooleanGeneric InternalBooleanDense
open InternalBooleanBits InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem projected_bit_iff (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (hbits : ∀ n, bitCode c (E n) ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hTop : ⊤ ∈ G.carrier) (n : ℕ) :
    (∃ q ∈ (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier,
      label (positive A) q = bitCode c (E n)) ↔
        natSet n ∈ (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier := by
  rw [← hit_bit_iff M c hM hT hc E hE G hG hTop n]
  constructor
  · rintro ⟨q,hq,he⟩
    change Hit G (label (positive A) q) at hq
    rwa [he] at hq
  · intro h
    obtain ⟨p,hp,hpb⟩ := h
    have hn : bitCode c (E n) ≠ ∅ := fun h0 => ZFSet.notMem_empty _ (h0 ▸ hpb)
    obtain ⟨q,hq⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hbits n,hn⟩)
    refine ⟨q,?_,hq⟩
    change Hit G (label (positive A) q)
    rw [hq]
    exact ⟨p,hp,hpb⟩

end TuringRigidity.InternalSameNameGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanTop
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanTop
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalRegularOrder
open InternalBooleanSyntax InternalBooleanProjection InternalProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem top_mem_part (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A) : c ∈ A := by
  have h0 : (∅ : ZFSet.{0}) ∈ M := hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero
  have h := closed_inf M c B Q A ∅ hM hT hc hBM hB hQ hA h0
    (fun x hx => False.elim (ZFSet.notMem_empty x hx))
  have he : infCode c ∅ = c := by
    apply ZFSet.ext; intro p
    simp only [infCode,ZFSet.mem_sep,ZFSet.notMem_empty,false_implies,implies_true,and_true]
  rwa [he] at h

theorem label_booleanTop (c A : ZFSet.{0}) (hcA : c ∈ A) (hc0 : c ≠ ∅) :
    @label (positive A) (booleanTop c A hcA hc0).top = c :=
  Classical.choose_spec (label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hcA,hc0⟩))

theorem top_in_filter (c A : ZFSet.{0}) [Top (Conditions (positive A))]
    (hAc : ∀ U ∈ A, U ⊆ c) (ht : label (positive A) ⊤ = c)
    (H : GenericFilter (Conditions (positive A))) : ⊤ ∈ H.carrier := by
  obtain ⟨p,hp⟩ := H.nonempty
  apply H.upper (q := ⊤) _ hp
  change label (positive A) p ⊆ label (positive A) ⊤
  rw [ht]
  exact hAc _ (label_info A p).1

end TuringRigidity.InternalBooleanTop

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSubsetSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSubsetSequence
open TransitiveNameModel BoundedSetTheory

theorem subset_sequence (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (φ : Formula) (e : ℕ → ZFSet.{0}) (he : ∀ i, e i ∈ M)
    (U : ℕ → ZFSet.{0}) (hU : ∀ n, U n ⊆ c)
    (hφ : ∀ n p, p ∈ c → (φ.Eval (cons p (cons (natSet n) e)) ↔ p ∈ U n)) :
    orbitGraph U ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  have hUM (n : ℕ) : U n ∈ M := by
    have hnM := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
    have he' : ∀ i, cons (natSet n) e i ∈ M := by
      intro i; cases i; exact hnM; exact he _
    have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ _ he' hc
    have heq : c.sep (fun p => φ.Eval (cons p (cons (natSet n) e))) = U n := by
      apply ZFSet.ext; intro p
      rw [ZFSet.mem_sep]
      exact ⟨fun ⟨hp,h⟩ => (hφ n p hp).mp h,fun hp => ⟨hU n hp,(hφ n p (hU n hp)).mpr hp⟩⟩
    exact heq ▸ hs
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  have hUQ : ∀ n, U n ∈ Q := fun n => (hQ _).mpr ⟨hUM n,hU n⟩
  let v := cons ZFSet.omega (cons Q (cons c e))
  let ren : ℕ → ℕ := fun | 0 => 0 | 1 => 2 | n+2 => n+7
  let ψ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.conj (.subset 0 5) (.allMem 5 (.iff (.member 0 1) (φ.rename ren))))))
  have hv : ∀ i, v i ∈ M := by
    intro i; rcases i with _|_|_|i; exact hω; exact hQM; exact hc; exact he i
  have renamed (p H n z : ZFSet.{0}) :
      (φ.rename ren).Eval (cons p (cons H (cons n (cons z v)))) ↔
        φ.Eval (cons p (cons n e)) := by
    rw [Formula.eval_rename_comp]
    have hh : (cons p (cons H (cons n (cons z v)))) ∘ ren = cons p (cons n e) := by
      funext i; rcases i with _|_|i <;> rfl
    rw [hh]
  have hψ (z : ZFSet.{0}) : ψ.Eval (cons z v) ↔ z ∈ orbitGraph U := by
    simp only [ψ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,
      Formula.eval_allMem,Formula.eval_iff,cons_zero,cons_succ,v]
    constructor
    · rintro ⟨n,hn,H,_,hz,hH,hdef⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hHU : H = U n := by
        apply ZFSet.ext; intro p
        constructor
        · intro hp
          exact (hφ n p (hH hp)).mp ((renamed p H _ z).mp ((hdef p (hH hp)).mp hp))
        · intro hp
          exact (hdef p (hU n hp)).mpr ((renamed p H _ z).mpr ((hφ n p (hU n hp)).mpr hp))
      exact (mem_orbitGraph U z).mpr ⟨n,by rw [hz,hHU]⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph U z).mp hz
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,U n,hUQ n,rfl,hU n,?_⟩
      intro p hp
      exact (hφ n p hp).symm.trans (renamed p (U n) _ _).symm
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded ψ v hv
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hQM)
  have heq : (ZFSet.prod ZFSet.omega Q).sep (fun z => ψ.Eval (cons z v)) = orbitGraph U := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hψ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function Q U hUQ).1 z hz),hz⟩⟩
  exact heq ▸ hs

end TuringRigidity.InternalSubsetSequence

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanName
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalBooleanBits InternalProjectedGeneric InternalBooleanTop
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem tags_info (M c A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hA : A ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M) :
    ∀ n, tags c A E n ∈ M ∧ tags c A E n ⊆ positive A := by
  intro n
  refine ⟨?_,fun _ h => (ZFSet.mem_sep.mp h).1⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (bitFormula 1 2 0) (cons c (fun _ => E n))
    (by intro i; cases i; exact hc; exact hE n) (positive_mem M A hM hT hA)
  simpa only [bitFormula_spec,cons_zero,cons_succ,tags] using hs

theorem tags_graph_mem (M c A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hA : A ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M) :
    orbitGraph (tags c A E) ∈ M := by
  obtain ⟨R,hRM,hR⟩ := internal_power M hM hT.powerSet hc
  let e := cons c (cons R (fun _ => orbitGraph E))
  let φ : BoundedSetTheory.Formula := .existsMem 3 (.conj (.pairMem 2 0 5) (bitFormula 3 0 1))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i; exact hc; exact hRM; exact hgraph
  apply InternalSubsetSequence.subset_sequence M (positive A) hM hT
    (positive_mem M A hM hT hA) φ e he (tags c A E)
    (fun n _ h => (ZFSet.mem_sep.mp h).1)
  intro n U hU
  simp only [φ,Formula.Eval,Formula.eval_pairMem,bitFormula_spec,cons_zero,cons_succ,e,
    tags,ZFSet.mem_sep,and_iff_right hU]
  constructor
  · rintro ⟨W,_,hnW,hUW⟩
    have hw := (orbitGraph_pair E n W).mp hnW
    exact hw ▸ hUW
  · intro h
    exact ⟨E n,(hR _).mpr (hE n),(orbitGraph_pair E n _).mpr rfl,h⟩

theorem booleanName_internal (M c A : ZFSet.{0}) [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hA : A ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (hgraph : orbitGraph E ∈ M) : (booleanName c A E).encode (label (positive A)) ∈ M :=
  InternalNiceName.nice_internal M hM hT (positive_mem M A hM hT hA)
    (tags c A E) (tags_info M c A hM hT hc hA E (fun n => (hE n).1))
    (tags_graph_mem M c A hM hT hc hA E hE hgraph)

theorem mem_val_booleanName (c A : ZFSet.{0}) [Top (Conditions (positive A))]
    (E : ℕ → ZFSet.{0}) (H : Set (Conditions (positive A))) (hH : ⊤ ∈ H)
    (x : ZFSet.{0}) : x ∈ (booleanName c A E).val H ↔
      ∃ n, (∃ q ∈ H, label (positive A) q = bitCode c (E n)) ∧ natSet n = x := by
  rw [booleanName,InternalNiceName.mem_val_nice _ H hH]
  constructor
  · rintro ⟨n,q,hq,ht,hx⟩
    exact ⟨n,⟨q,hq,(ZFSet.mem_sep.mp ht).2⟩,hx⟩
  · rintro ⟨n,⟨q,hq,he⟩,hx⟩
    exact ⟨n,q,hq,ZFSet.mem_sep.mpr ⟨label_mem _ q,he⟩,hx⟩

theorem val_booleanName (M c B Q A : ZFSet.{0})
    [Top (Conditions c)] [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (ht : label (positive A) ⊤ = c)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (hbits : ∀ n, bitCode c (E n) ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hTop : ⊤ ∈ G.carrier) :
    (booleanName c A E).val (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      (InternalNiceName.nice E : Name (Conditions c)).val G.carrier := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  have hHt := top_in_filter c A (fun U hU => ((hB U).mp (hA.1 hU)).2.1) ht H
  apply ZFSet.ext
  intro x
  rw [mem_val_booleanName c A E H.carrier hHt]
  dsimp only [H]
  simp only [InternalSameNameGeneric.projected_bit_iff M c B Q A hM hT hc hBM hAM
    hB hQ hA E hE hbits G hG hTop]
  constructor
  · rintro ⟨n,hn,rfl⟩; exact hn
  · intro hx
    obtain ⟨n,p,hp,hpE,hnx⟩ := (InternalNiceName.mem_val_nice E G.carrier hTop x).mp hx
    exact ⟨n,hnx.symm ▸ hx,hnx⟩

theorem same_value_mem_projected_extension (M c B Q A : ZFSet.{0})
    [Top (Conditions c)] [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (ht : label (positive A) ⊤ = c)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hbits : ∀ n, bitCode c (E n) ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hTop : ⊤ ∈ G.carrier) :
    (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ∈
      genericExtensionSet M (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier :=
  (mem_extensionSet _ _ _ _).mpr ⟨booleanName c A E,
    booleanName_internal M c A hM hT hc hAM E hE hgraph,
    val_booleanName M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hbits G hG hTop⟩

end TuringRigidity.InternalBooleanName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNameEvaluation
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalNameEvaluation
open TransitiveNameModel RecursiveNames RelationCollapse
universe u

theorem activeRelation_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d g : ZFSet.{u}} (hd : d ∈ M) (hg : g ∈ M) : activeRelation d g ∈ M := by
  simpa only [activeRelation,activeFormula,Formula.Eval,Formula.eval_orderedPair,
    Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded activeFormula (cons d (fun _ => g))
      (by intro i; cases i <;> assumption)
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hd hd)

theorem value_eq (d : ZFSet.{u}) (hd : Transitive d) {c : ZFSet.{u}}
    (G : Set (Conditions c)) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ d) :
    value d (activeRelation d (genericFilterSet c G)) (active_wellFounded _ _) (a.encode (label c)) = a.val G := by
  induction a with
  | mk ι child tag ih =>
    have hc (i : ι) : (child i).encode (label c) ∈ d := by
      have hp := hd _ ha _ (ZFSet.mem_range_self i)
      have hs := hd _ hp _ (ZFSet.mem_pair.mpr (Or.inl rfl))
      exact hd _ hs _ (ZFSet.mem_singleton.mpr rfl)
    apply ZFSet.ext; intro z
    rw [mem_value,Name.mem_val]
    constructor
    · rintro ⟨x,_,hxy,hzx⟩
      obtain ⟨_,_,p,hp,hpa⟩ := (active_pair _ _ _ _).mp hxy
      obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hpa
      obtain ⟨hiX,hiP⟩ := ZFSet.pair_inj.mp hi
      obtain ⟨q,hq,hqp⟩ := (mem_genericFilterSet c G p).mp hp
      have htag : tag i = q := label_injective c (hiP.trans hqp.symm)
      refine ⟨i,htag.symm ▸ hq,?_⟩
      rw [←ih i (hc i),hiX]
      exact hzx.symm
    · rintro ⟨i,hig,hiz⟩
      refine ⟨(child i).encode (label c),hc i,?_,?_⟩
      · exact (active_pair _ _ _ _).mpr ⟨hc i,ha,label c (tag i),
          (mem_genericFilterSet c G _).mpr ⟨tag i,hig,rfl⟩,ZFSet.mem_range_self i⟩
      · exact hiz.symm.trans (ih i (hc i)).symm

theorem name_value_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c : ZFSet.{u}} (G : Set (Conditions c)) (hg : genericFilterSet c G ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) : a.val G ∈ M := by
  obtain ⟨d,hdM,hd,had⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity ha
  obtain ⟨f,hf,hfg⟩ := internal_graph M d (activeRelation d (genericFilterSet c G)) hM
    hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
    hdM (activeRelation_mem M hM hT hdM hg) (active_wellFounded _ _)
  have hp : ZFSet.pair (a.encode (label c))
      (value d (activeRelation d (genericFilterSet c G)) (active_wellFounded _ _) (a.encode (label c))) ∈ f :=
    (hfg.mem_iff (active_wellFounded _ _) _).mpr ⟨_,had,rfl⟩
  have hv := second_mem_doubleUnion hp
  have hi := hM _ (iterUnion_mem M hM hT.union hf 2) _ hv
  rwa [value_eq d hd G a had] at hi

theorem extension_subset (M N : ZFSet.{u}) (hN : Transitive N) (hT : SourceT N) (hMN : M ⊆ N)
    {c : ZFSet.{u}} (G : Set (Conditions c)) (hG : genericFilterSet c G ∈ N) :
    genericExtensionSet M c G ⊆ N := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G x).mp hx
  exact name_value_mem N hN hT G hG a (hMN ha)

end TuringRigidity.BoundedSetTheory.InternalNameEvaluation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanExtension
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalProjectedGeneric InternalBooleanTop InternalBooleanName InternalBooleanGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem hitSet_mem (N A g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hA : A ∈ N) (hg : g ∈ N) : hitSet A g ∈ N := by
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded
    (.existsMem 1 (.member 0 1)) (fun _ => g) (fun _ => hg)
    (positive_mem N A hN hT hA)
  simpa only [hitSet,Formula.Eval,cons_zero,cons_succ] using hs

theorem projected_filterSet (M c B Q A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) :
    genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      hitSet A (genericFilterSet c G.carrier) := by
  apply ZFSet.ext; intro U
  rw [mem_genericFilterSet,hitSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨p,hp,hpq⟩ := hq
    exact ⟨label_mem _ q,label c p,(mem_genericFilterSet c G.carrier _).mpr ⟨p,hp,rfl⟩,hpq⟩
  · rintro ⟨hU,p,hp,hpU⟩
    obtain ⟨q,rfl⟩ := label_surjective (positive A) hU
    obtain ⟨r,hr,rfl⟩ := (mem_genericFilterSet c G.carrier p).mp hp
    exact ⟨q,⟨r,hr,hpU⟩,rfl⟩

theorem projected_extension_subset_model (M N c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hgN : genericFilterSet c G.carrier ∈ N) :
    genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ⊆ N := by
  apply InternalNameEvaluation.extension_subset M N hN hTN hMN
  rw [projected_filterSet M c B Q A hM hT hc hBM hAM hB hQ hA G]
  exact hitSet_mem N A _ hN hTN (hMN hAM) hgN

theorem projected_extension_subset_original (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hTop : ⊤ ∈ G.carrier) :
    genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ⊆
        genericExtensionSet M c G.carrier := by
  have hN := genericExtensionSet_transitive M c hM G.carrier
  have hTN := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair c) G hG hTop
  have hMN := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier hTop
  apply projected_extension_subset_model M _ c B Q A hM hT hN hTN hMN hc hBM hAM hB hQ hA G
  exact genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier hTop

theorem projected_extension_sandwich (M c B Q A : ZFSet.{0})
    [Top (Conditions c)] [Top (Conditions (positive A))]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (ht : label (positive A) ⊤ = c)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hbits : ∀ n, bitCode c (E n) ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hTop : ⊤ ∈ G.carrier) :
    let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
    let N := genericExtensionSet M (positive A) H.carrier
    Transitive N ∧ SourceT N ∧ M ⊆ N ∧
      (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ∈ N ∧
      genericFilterSet (positive A) H.carrier ∈ N ∧ N ⊆ genericExtensionSet M c G.carrier := by
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  have hHt := top_in_filter c A (fun U hU => ((hB U).mp (hA.1 hU)).2.1) ht H
  have hpM := positive_mem M A hM hT hAM
  have hHG := projected_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG
  obtain ⟨hoM,ho⟩ := projected_order_code M A hM hT hAM
  refine ⟨genericExtensionSet_transitive M _ hM H.carrier,
    extension_sourceT M hM hT hpM hoM ho H hHG hHt,?_,?_,?_,
    projected_extension_subset_original M c B Q A hM hT hc hBM hAM hB hQ hA G hG hTop⟩
  · exact ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpM H.carrier hHt
  · exact same_value_mem_projected_extension M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hgraph hbits G hG hTop
  · exact genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hpM H.carrier hHt

end TuringRigidity.InternalBooleanExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanIntermediate
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalBooleanIntermediate
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalProjectedGeneric InternalBooleanTop InternalBooleanName InternalBooleanExtension
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] codeOrder codePreorder

theorem internal_boolean_intermediate_oai (M c : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M) :
    ∃ B ∈ M, ∃ Q ∈ M, ∃ A ∈ M,
      (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
      (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) ∧
      A = InternalGeneratedAlgebra.generated c B Q (seeds c B E) ∧ Closed c B Q A ∧
      ∃ σ : Name (Conditions (positive A)), σ.encode (label (positive A)) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G → ⊤ ∈ G.carrier →
        ∃ H : GenericFilter (Conditions (positive A)), AtomicForcing.GroundGeneric M H ∧
          (∀ q, q ∈ H.carrier ↔ InternalBooleanGeneric.Hit G (label (positive A) q)) ∧
          σ.val H.carrier = (InternalNiceName.nice E : Name (Conditions c)).val G.carrier ∧
          Transitive (genericExtensionSet M (positive A) H.carrier) ∧
          SourceT (genericExtensionSet M (positive A) H.carrier) ∧
          M ⊆ genericExtensionSet M (positive A) H.carrier ∧
          σ.val H.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
          genericFilterSet (positive A) H.carrier ∈ genericExtensionSet M (positive A) H.carrier ∧
          genericExtensionSet M (positive A) H.carrier ⊆ genericExtensionSet M c G.carrier := by
  obtain ⟨B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,hbits,_⟩ :=
    internal_bit_generated_part M c hM hT hc E hE hgraph
  have hcA := top_mem_part M c B Q A hM hT hc hBM hB hQ hA
  have hc0 : c ≠ ∅ := by
    intro h
    exact ZFSet.notMem_empty (label c ⊤)
      (Eq.mp (congrArg (fun d => label c ⊤ ∈ d) h) (label_mem c ⊤))
  let _ := booleanTop c A hcA hc0
  have ht : label (positive A) ⊤ = c := label_booleanTop c A hcA hc0
  let σ := booleanName c A E
  have hσ := booleanName_internal M c A hM hT hc hAM E hE hgraph
  refine ⟨B,hBM,Q,hQM,A,hAM,hB,hQ,heq,hA,σ,hσ,?_⟩
  intro G hG hTop
  let H := projected M c B Q A hM hT hc hBM hAM hB hQ hA G
  have hv := val_booleanName M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hbits G hG hTop
  obtain ⟨hN,hTN,hMN,_,hHN,hNG⟩ :=
    projected_extension_sandwich M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hgraph hbits G hG hTop
  exact ⟨H,projected_ground_generic M c B Q A hM hT hc hBM hAM hB hQ hA G hG,
    fun _ => Iff.rfl,hv,hN,hTN,hMN,(mem_extensionSet _ _ _ _).mpr ⟨σ,hσ,rfl⟩,hHN,hNG⟩

end TuringRigidity.InternalBooleanIntermediate

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.InternalBooleanIntermediate.internal_boolean_intermediate_oai := @OAI.TuringRigidity.InternalBooleanIntermediate.internal_boolean_intermediate_oai
