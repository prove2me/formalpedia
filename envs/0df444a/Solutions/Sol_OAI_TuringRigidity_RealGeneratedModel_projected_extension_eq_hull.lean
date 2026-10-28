-- Prove2me | solution 1 for OAI.TuringRigidity.RealGeneratedModel.projected_extension_eq_hull
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:31:00.545345+00:00
-- url     : https://prove2.me/submissions/4f02e45e-b335-4d72-9a3e-9e27d6ec8a32

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

theorem seeds_subset (c B Q S : ZFSet.{0}) (hS : S ⊆ B) : S ⊆ generated c B Q S := by
  intro U hU
  refine ZFSet.mem_sep.mpr ⟨hS hU,fun A hA => ?_⟩
  exact (ZFSet.mem_sep.mp hA).2.1 hU

theorem generated_le (c B Q S A : ZFSet.{0}) (hA : A ∈ Q)
    (hS : S ⊆ A) (hc : Closed c B Q A) : generated c B Q S ⊆ A := by
  intro U hU
  exact (ZFSet.mem_sep.mp hU).2 A (ZFSet.mem_sep.mpr ⟨hA,hS,hc⟩)

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

theorem decision_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : decision c U ∈ M :=
  binary_union_mem M hM hT.pairing hT.union hU (neg_mem M c U hM hT hc hU)

theorem decision_dense (c U : ZFSet.{0}) (hUc : U ⊆ c) :
    Dense {p : Conditions c | label c p ∈ decision c U} := by
  classical
  intro p
  by_cases h : ∃ q ∈ U, label c p ⊆ q
  · obtain ⟨q,hq,hpq⟩ := h
    obtain ⟨q,rfl⟩ := label_surjective c (hUc hq)
    exact ⟨q,hpq,ZFSet.mem_union.mpr (Or.inl hq)⟩
  · refine ⟨p,le_rfl,ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_sep.mpr ⟨label_mem c p,?_⟩))⟩
    intro q hq hpq
    exact h ⟨q,hq,hpq⟩

theorem generic_decision (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (hUc : U ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G U ∨ Hit G (neg c U) := by
  obtain ⟨p,hp,hpd⟩ := hG (decision c U) (decision_mem M c U hM hT hc hU) (decision_dense c U hUc)
  rcases ZFSet.mem_union.mp hpd with h | h
  · exact Or.inl ⟨p,hp,h⟩
  · exact Or.inr ⟨p,hp,h⟩

theorem hit_neg_excludes (c U : ZFSet.{0}) (hU : Lower c U)
    (G : GenericFilter (Conditions c)) (hn : Hit G (neg c U)) : ¬ Hit G U := by
  rintro ⟨q,hq,hqU⟩
  obtain ⟨p,hp,hpN⟩ := hn
  obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
  have hrU := hU _ hqU _ (label_mem c r) hrq
  exact (ZFSet.mem_sep.mp hpN).2 (label c r) hrU hrp

theorem hit_complement_iff (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hUM : U ∈ M) (hU : IsCode c U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G (neg c U) ↔ ¬ Hit G U := by
  constructor
  · exact hit_neg_excludes c U (code_lower c U hU) G
  · intro hn
    exact (generic_decision M c U hM hT hc hUM hU.1 G hG).resolve_left hn

theorem hit_regular_iff (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hUM : U ∈ M) (hUc : U ⊆ c) (hU : Lower c U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G (regular c U) ↔ Hit G U := by
  constructor
  · intro hr
    rcases generic_decision M c U hM hT hc hUM hUc G hG with hp | hn
    · exact hp
    · exact False.elim (hit_neg_excludes c (neg c U) (neg_lower c U) G hr hn)
  · rintro ⟨p,hp,hpU⟩
    exact ⟨p,hp,subset_regular c U hUc hU hpU⟩

theorem hit_supCode_iff (M c F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hFM : F ∈ M) (hF : ∀ U ∈ F, IsCode c U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G (supCode c F) ↔ ∃ U ∈ F, Hit G U := by
  rw [supCode,hit_regular_iff M c _ hM hT hc (union_mem M hM hT.union hFM)
    (union_subset c F hF) (union_lower c F (fun U hU => code_lower c U (hF U hU))) G hG]
  constructor
  · rintro ⟨p,hp,hpF⟩
    obtain ⟨U,hU,hpU⟩ := ZFSet.mem_sUnion.mp hpF
    exact ⟨U,hU,p,hp,hpU⟩
  · rintro ⟨U,hU,p,hp,hpU⟩
    exact ⟨p,hp,ZFSet.mem_sUnion.mpr ⟨U,hU,hpU⟩⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanExpressionCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanGeneric CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem Step.mono {c B Q S K L g h t U : ZFSet.{0}}
    (hKL : K ⊆ L) (hgh : g ⊆ h) (hs : Step c B Q S K g t U) :
    Step c B Q S L h t U := by
  rcases hs with hs | hs | hs
  · exact Or.inl hs
  · obtain ⟨s,hs,V,hV,ht,hp,hU⟩ := hs
    exact Or.inr (Or.inl ⟨s,hKL hs,V,hV,ht,hgh hp,hU⟩)
  · obtain ⟨T,hT,F,hF,ht,hU,hTF,hFT⟩ := hs
    exact Or.inr (Or.inr ⟨T,hKL hT,F,hF,ht,hU,
      fun s hs => (hTF s hs).imp (fun V h => ⟨h.1,hgh h.2⟩),
      fun V hV => (hFT V hV).imp (fun s h => ⟨h.1,hgh h.2⟩)⟩)

theorem Certificate.step {c B Q S K g t U : ZFSet.{0}}
    (hg : Certificate c B Q S K g) (hp : ZFSet.pair t U ∈ g) :
    t ∈ K ∧ U ∈ B ∧ Step c B Q S K g t U := by
  obtain ⟨s,hs,V,hV,he,hstep⟩ := hg _ hp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact ⟨hs,hV,hstep⟩

theorem Certificate.enlarge {c B Q S K L g : ZFSet.{0}}
    (hg : Certificate c B Q S K g) (hKL : K ⊆ L) : Certificate c B Q S L g := by
  intro z hz
  obtain ⟨t,ht,U,hU,he,hs⟩ := hg z hz
  exact ⟨t,hKL ht,U,hU,he,hs.mono hKL (fun _ h => h)⟩

theorem Certificate.insert {c B Q S K g t U : ZFSet.{0}}
    (hg : Certificate c B Q S K g) (ht : t ∈ K) (hU : U ∈ B)
    (hs : Step c B Q S K g t U) :
    Certificate c B Q S K (g ∪ ({ZFSet.pair t U} : ZFSet.{0})) := by
  have hgg : g ⊆ g ∪ ({ZFSet.pair t U} : ZFSet.{0}) :=
    fun _ h => ZFSet.mem_union.mpr (Or.inl h)
  intro z hz
  rcases ZFSet.mem_union.mp hz with hz | hz
  · obtain ⟨s,hs,V,hV,he,hstep⟩ := hg z hz
    exact ⟨s,hs,V,hV,he,hstep.mono (fun _ h => h) hgg⟩
  · have he := ZFSet.mem_singleton.mp hz
    exact ⟨t,ht,U,hU,he,hs.mono (fun _ h => h) hgg⟩

end TuringRigidity.BooleanExpressionCertificate

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanExpressionSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalBooleanSyntax

theorem stepFormula_spec (c B Q S K g t U z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (stepFormula c B Q S K g t U z0 z1 z2).Eval e ↔
      Step (e c) (e B) (e Q) (e S) (e K) (e g) (e t) (e U) := by
  simp only [stepFormula,Formula.eval_disj,Formula.Eval,Formula.eval_orderedPair,
    Formula.eval_pairMem,Formula.eval_allMem,negFormula_spec,supFormula_spec,
    cons_zero,cons_succ,h0,h1,h2,Step,FiniteTerm.tag]

theorem certificateFormula_spec (c B Q S K g z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (certificateFormula c B Q S K g z0 z1 z2).Eval e ↔
      Certificate (e c) (e B) (e Q) (e S) (e K) (e g) := by
  simp only [certificateFormula,Formula.eval_allMem,Formula.Eval,
    Formula.eval_orderedPair,cons_zero,cons_succ,Certificate]
  apply forall_congr'; intro z
  apply imp_congr_right; intro _
  apply exists_congr; intro t
  apply and_congr_right; intro _
  apply exists_congr; intro U
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact stepFormula_spec _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2

theorem witnessFormula_spec (c B Q S K U z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (witnessFormula c B Q S K U z0 z1 z2).Eval e ↔
      Witness (e c) (e B) (e Q) (e S) (e K) (e U) := by
  simp only [witnessFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_subset,
    Formula.eval_pairMem,cons_zero,cons_succ,Witness,TransitiveNameModel.Transitive]
  apply and_congr Iff.rfl
  apply exists_congr; intro g
  apply and_congr_right; intro _
  exact and_congr (certificateFormula_spec _ _ _ _ _ _ _ _ _ _ h0 h1 h2) Iff.rfl

theorem parameters_mem (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) :
    ∀ i, parameters c B Q S i ∈ M := by
  intro i
  rcases i with _|_|_|_|_|_|i
  exact hc; exact hB; exact hQ; exact hS
  all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)

theorem witnessBody_realize (M c B Q S K U : ZFSet.{0}) (hM : Transitive M)
    (he : ∀ i, parameters c B Q S i ∈ M) (hK : K ∈ M) (hU : U ∈ M) :
    witnessBody.Realize M (cons K (cons U (parameters c B Q S))) ↔ Witness c B Q S K U := by
  rw [Formula.absolute _ M hM _ (by
    intro i; rcases i with _|_|i; exact hK; exact hU; exact he i)]
  exact witnessFormula_spec _ _ _ _ _ _ _ _ _ _ rfl rfl rfl

theorem certified_mem (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) : certified M c B Q S ∈ M := by
  have he := parameters_mem M c B Q S hM hT hc hB hQ hS
  obtain ⟨a,ha,hspec⟩ := hT.separation.finitePrefix
    (.existsSet (.bounded witnessBody)) (parameters c B Q S) he B hB
  have eq : a = certified M c B Q S := by
    apply ZFSet.ext; intro U
    rw [certified,ZFSet.mem_sep]
    constructor
    · intro hU
      obtain ⟨hUB,K,hKM,hK⟩ := (hspec U (hM _ ha _ hU)).mp hU
      exact ⟨hUB,K,hKM,(witnessBody_realize M c B Q S K U hM he hKM (hM _ hB _ hUB)).mp hK⟩
    · rintro ⟨hUB,K,hKM,hK⟩
      have hUM := hM _ hB _ hUB
      exact (hspec U hUM).mpr ⟨hUB,K,hKM,(witnessBody_realize M c B Q S K U hM he hKM hUM).mpr hK⟩
  exact eq ▸ ha

end TuringRigidity.BooleanExpressionCertificate

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanExpressionAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalBooleanSyntax
open InternalRegularOperations InternalRegularAlgebra

theorem tag_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) {x : ZFSet.{0}} (hx : x ∈ M) : FiniteTerm.tag n x ∈ M :=
  orderedPair_mem M hM hT.pairing
    (hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)) hx

theorem witness_of_certificate (M c B Q S K g t U : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hKM : K ∈ M) (hgM : g ∈ M)
    (hg : Certificate c B Q S K g) (hp : ZFSet.pair t U ∈ g) :
    ∃ L ∈ M, Witness c B Q S L U := by
  obtain ⟨L,hLM,hL,hpair⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity
    (pair_mem M hM hT.pairing hKM hgM)
  have hKL := hL _ hpair K (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hgL := hL _ hpair g (ZFSet.mem_pair.mpr (Or.inr rfl))
  have hsub : K ⊆ L := fun x hx => hL K hKL x hx
  exact ⟨L,hLM,hL,g,hgL,hg.enlarge hsub,t,hsub (hg.step hp).1,hp⟩

theorem seed_certified (M c B Q S U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hUM : U ∈ M) (hUB : U ∈ B) (hUS : U ∈ S) : U ∈ certified M c B Q S := by
  let t := FiniteTerm.tag 0 U
  let K := ({t} : ZFSet.{0})
  let g := ({ZFSet.pair t U} : ZFSet.{0})
  have htM : t ∈ M := tag_mem M hM hT 0 hUM
  have htK : t ∈ K := ZFSet.mem_singleton.mpr rfl
  have hg : Certificate c B Q S K g := by
    intro z hz
    exact ⟨t,htK,U,hUB,ZFSet.mem_singleton.mp hz,Or.inl ⟨hUS,rfl⟩⟩
  exact ZFSet.mem_sep.mpr ⟨hUB,witness_of_certificate M c B Q S K g t U hM hT
    (singleton_mem M hM hT.pairing htM)
    (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing htM hUM)) hg
    (ZFSet.mem_singleton.mpr rfl)⟩

theorem neg_certified (M c B Q S U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hU : U ∈ certified M c B Q S) : neg c U ∈ certified M c B Q S := by
  obtain ⟨hUB,K,hKM,hK,g,hgK,hg,t,htK,hp⟩ := ZFSet.mem_sep.mp hU
  have hUM := ((hB U).mp hUB).1
  have hVM := neg_mem M c U hM hT hc hUM
  have hVB := internal_complement M c B hM hT hc hB hUB
  let s := FiniteTerm.tag 1 t
  have hsM : s ∈ M := tag_mem M hM hT 1 (hM K hKM t htK)
  let L := K ∪ ({s} : ZFSet.{0})
  have hKL : K ⊆ L := fun _ h => ZFSet.mem_union.mpr (Or.inl h)
  have hsL : s ∈ L := ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl))
  have hs : Step c B Q S L g s (neg c U) :=
    Or.inr (Or.inl ⟨t,hKL htK,U,hUB,rfl,hp,rfl⟩)
  let f := g ∪ ({ZFSet.pair s (neg c U)} : ZFSet.{0})
  have hf := (hg.enlarge hKL).insert hsL hVB hs
  have hLM : L ∈ M := binary_union_mem M hM hT.pairing hT.union hKM
    (singleton_mem M hM hT.pairing hsM)
  have hfM : f ∈ M := binary_union_mem M hM hT.pairing hT.union (hM K hKM g hgK)
    (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing hsM hVM))
  exact ZFSet.mem_sep.mpr ⟨hVB,witness_of_certificate M c B Q S L f s _ hM hT hLM hfM hf
    (ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl)))⟩

theorem Certificate.sUnion {c B Q S K a : ZFSet.{0}}
    (ha : ∀ g ∈ a, Certificate c B Q S K g) : Certificate c B Q S K (ZFSet.sUnion a) := by
  intro z hz
  obtain ⟨g,hga,hzg⟩ := ZFSet.mem_sUnion.mp hz
  obtain ⟨t,ht,U,hU,he,hs⟩ := ha g hga z hzg
  exact ⟨t,ht,U,hU,he,hs.mono (fun _ h => h) (fun z hz => ZFSet.mem_sUnion.mpr ⟨g,hga,hz⟩)⟩

theorem goodGraphs_mem (M a c B Q S K : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) (hK : K ∈ M) :
    goodGraphs a c B Q S K ∈ M := by
  let e := cons K (parameters c B Q S)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i with
    | zero => exact hK
    | succ i => exact parameters_mem M c B Q S hM hT hc hB hQ hS i
  have spec (g : ZFSet.{0}) :
      (certificateFormula 2 3 4 5 1 0 6 7 8).Eval (cons g e) ↔ Certificate c B Q S K g :=
    certificateFormula_spec _ _ _ _ _ _ _ _ _ _ rfl rfl rfl
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (certificateFormula 2 3 4 5 1 0 6 7 8) e he ha
  simpa only [spec,goodGraphs] using hs

theorem children_mem (M K F g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hF : F ∈ M) (hg : g ∈ M) : children K F g ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 1 0 3)) (cons F (fun _ => g))
    (by intro i; cases i <;> assumption) hK
  simpa only [children,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using hs

end TuringRigidity.BooleanExpressionCertificate

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanExpressionCoverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalBooleanSyntax InternalGeneratedAlgebra
open InternalRegularOperations InternalRegularAlgebra

theorem sup_certified (M c B Q S F : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hFQ : F ∈ Q)
    (hFC : F ⊆ certified M c B Q S) : supCode c F ∈ certified M c B Q S := by
  obtain ⟨hFM,hFB⟩ := (hQ F).mp hFQ
  have he := parameters_mem M c B Q S hM hT hc hBM hQM hSM
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  obtain ⟨W,hWM,hW⟩ := hColl (.bounded witnessBody) (parameters c B Q S) he F hFM (by
    intro U hUF
    obtain ⟨_,K,hKM,hK⟩ := ZFSet.mem_sep.mp (hFC hUF)
    exact ⟨K,hKM,(witnessBody_realize M c B Q S K U hM he hKM (hM F hFM U hUF)).mpr hK⟩)
  obtain ⟨L,hLM,hL,hWL⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hWM
  have hKL (K : ZFSet.{0}) (hK : K ∈ W) : K ⊆ L :=
    fun t ht => hL K (hL W hWL K hK) t ht
  let a := goodGraphs (ZFSet.sUnion W) c B Q S L
  have haM : a ∈ M := goodGraphs_mem M _ c B Q S L hM hT
    (union_mem M hM hT.union hWM) hc hBM hQM hSM hLM
  let g := ZFSet.sUnion a
  have hgM : g ∈ M := union_mem M hM hT.union haM
  have hg : Certificate c B Q S L g := Certificate.sUnion (fun f hf => (ZFSet.mem_sep.mp hf).2)
  have htotal (U : ZFSet.{0}) (hUF : U ∈ F) : ∃ t ∈ L, ZFSet.pair t U ∈ g := by
    obtain ⟨K,hKW,hK⟩ := hW U hUF
    obtain ⟨_,f,hfK,hf,t,htK,hp⟩ :=
      (witnessBody_realize M c B Q S K U hM he (hM W hWM K hKW) (hM F hFM U hUF)).mp hK
    have hfa : f ∈ a := ZFSet.mem_sep.mpr ⟨ZFSet.mem_sUnion.mpr ⟨K,hKW,hfK⟩,hf.enlarge (hKL K hKW)⟩
    exact ⟨t,hKL K hKW htK,ZFSet.mem_sUnion.mpr ⟨f,hfa,hp⟩⟩
  let T := children L F g
  have hTM : T ∈ M := children_mem M L F g hM hT hLM hFM hgM
  let s := FiniteTerm.tag 2 T
  have hsM : s ∈ M := tag_mem M hM hT 2 hTM
  let D := L ∪ ({T,s} : ZFSet.{0})
  have hLD : L ⊆ D := fun _ h => ZFSet.mem_union.mpr (Or.inl h)
  have hTD : T ∈ D := ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_pair.mpr (Or.inl rfl)))
  have hsD : s ∈ D := ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_pair.mpr (Or.inr rfl)))
  have hDM : D ∈ M := binary_union_mem M hM hT.pairing hT.union hLM (pair_mem M hM hT.pairing hTM hsM)
  have hVB := internal_join M c B F hM hT hc hB hFM
  have hVM := ((hB _).mp hVB).1
  have hs : Step c B Q S D g s (supCode c F) := by
    refine Or.inr (Or.inr ⟨T,hTD,F,hFQ,rfl,rfl,?_,?_⟩)
    · exact fun t ht => (ZFSet.mem_sep.mp ht).2
    · intro U hUF
      obtain ⟨t,htL,hp⟩ := htotal U hUF
      exact ⟨t,ZFSet.mem_sep.mpr ⟨htL,U,hUF,hp⟩,hp⟩
  let f := g ∪ ({ZFSet.pair s (supCode c F)} : ZFSet.{0})
  have hfM : f ∈ M := binary_union_mem M hM hT.pairing hT.union hgM
    (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing hsM hVM))
  have hf := (hg.enlarge hLD).insert hsD hVB hs
  exact ZFSet.mem_sep.mpr ⟨hVB,witness_of_certificate M c B Q S D f s _ hM hT hDM hfM hf
    (ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl)))⟩

theorem certified_closed (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) : Closed c B Q (certified M c B Q S) :=
  ⟨fun _ h => (ZFSet.mem_sep.mp h).1,
    fun U hU => neg_certified M c B Q S U hM hT hc hB hU,
    fun F hF hFC => sup_certified M c B Q S F hM hT hc hBM hQM hSM hB hQ hF hFC⟩

theorem generated_certificate (M c B Q S U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hSB : S ⊆ B)
    (hU : U ∈ generated c B Q S) : ∃ K ∈ M, Witness c B Q S K U := by
  have hC := certified_closed M c B Q S hM hT hc hBM hQM hSM hB hQ
  have hCM := certified_mem M c B Q S hM hT hc hBM hQM hSM
  have hCQ := (hQ _).mpr ⟨hCM,hC.1⟩
  have hSC : S ⊆ certified M c B Q S := by
    intro V hV
    exact seed_certified M c B Q S V hM hT (hM S hSM V hV) (hSB hV) hV
  exact (ZFSet.mem_sep.mp (generated_le c B Q S _ hCQ hSC hC hU)).2

end TuringRigidity.BooleanExpressionCertificate

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedTruthRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedTruthRecursion
open TransitiveNameModel BoundedSetTheory

theorem partial_sound (φ : Formula) (e : ℕ → ZFSet.{0}) (K D Y Z : ZFSet.{0})
    (hl : Local φ e) (hp : Partial φ e K D Y)
    (hz : ∀ t ∈ K, t ∈ Z ↔ φ.Eval (cons t (cons Z e))) :
    ∀ t ∈ D, t ∈ Y ↔ t ∈ Z := by
  have wf : WellFounded (fun a b : ZFSet.{0} => ZFSet.rank a < ZFSet.rank b) :=
    InvImage.wf ZFSet.rank Ordinal.lt_wf
  intro t
  induction t using wf.induction with
  | h t ih =>
    intro ht
    exact (hp.2.2.2 t ht).trans ((hl D hp.1 t ht Y Z
      (fun s hs hst => ih s hst hs)).trans (hz t (hp.2.1 ht)).symm)

theorem partialFormula_spec (φ : Formula) (e : ℕ → ZFSet.{0}) (K D Y : ZFSet.{0}) :
    (partialFormula φ).Eval (cons Y (cons D (cons K e))) ↔ Partial φ e K D Y := by
  simp only [partialFormula,Formula.Eval,Formula.eval_transitive,Formula.eval_subset,
    Formula.eval_allMem,Formula.eval_iff,Formula.eval_rename_comp,cons_zero,cons_succ,Partial]
  have eq (t : ZFSet.{0}) : cons t (cons Y (cons D (cons K e))) ∘ dropSlots = cons t (cons Y e) := by
    funext i; rcases i with _|_|i <;> rfl
  simp only [eq]

theorem unionFormula_spec (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q t : ZFSet.{0}) (which : ℕ) :
    (unionFormula φ which).Eval (cons t (cons Q (cons K e))) ↔
      ∃ D ∈ Q, ∃ Y ∈ Q, Partial φ e K D Y ∧
        t ∈ cons Y (cons D (cons t (cons Q (cons K e)))) which := by
  simp only [unionFormula,Formula.Eval,Formula.eval_rename_comp,cons_zero,cons_succ]
  have eq (D Y : ZFSet.{0}) :
      cons Y (cons D (cons t (cons Q (cons K e)))) ∘ candidateSlots = cons Y (cons D (cons K e)) := by
    funext i; rcases i with _|_|i <;> rfl
  simp only [eq,partialFormula_spec]

theorem domain_truth_mem (M K Q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hQ : Q ∈ M) (φ : Formula) (e : ℕ → ZFSet.{0}) (he : ∀ i, e i ∈ M) :
    domain φ e K Q ∈ M ∧ truth φ e K Q ∈ M := by
  have henv : ∀ i, cons Q (cons K e) i ∈ M := by
    intro i; rcases i with _|_|i; exact hQ; exact hK; exact he i
  constructor
  · have hs := sep_mem M hM hT.separation.finitePrefix.bounded (unionFormula φ 1) _ henv hK
    simpa only [unionFormula_spec,cons_succ,cons_zero,domain] using hs
  · have hs := sep_mem M hM hT.separation.finitePrefix.bounded (unionFormula φ 0) _ henv hK
    simpa only [unionFormula_spec,cons_succ,cons_zero,truth] using hs

theorem domain_transitive (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q : ZFSet.{0}) :
    Transitive (domain φ e K Q) := by
  intro t ht s hst
  obtain ⟨_,D,hD,Y,hY,hp,htD⟩ := ZFSet.mem_sep.mp ht
  have hsD := hp.1 t htD s hst
  exact ZFSet.mem_sep.mpr ⟨hp.2.1 hsD,D,hD,Y,hY,hp,hsD⟩

theorem truth_subset_domain (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q : ZFSet.{0}) :
    truth φ e K Q ⊆ domain φ e K Q := by
  intro t ht
  obtain ⟨htK,D,hD,Y,hY,hp,htY⟩ := ZFSet.mem_sep.mp ht
  exact ZFSet.mem_sep.mpr ⟨htK,D,hD,Y,hY,hp,hp.2.2.1 htY⟩

theorem truth_agrees (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q Z : ZFSet.{0})
    (hl : Local φ e) (hz : ∀ t ∈ K, t ∈ Z ↔ φ.Eval (cons t (cons Z e))) :
    ∀ t ∈ domain φ e K Q, t ∈ truth φ e K Q ↔ t ∈ Z := by
  intro t ht
  constructor
  · intro h
    obtain ⟨_,D,_,Y,_,hp,htY⟩ := ZFSet.mem_sep.mp h
    exact (partial_sound φ e K D Y Z hl hp hz t (hp.2.2.1 htY)).mp htY
  · intro h
    obtain ⟨htK,D,hD,Y,hY,hp,htD⟩ := ZFSet.mem_sep.mp ht
    exact ZFSet.mem_sep.mpr ⟨htK,D,hD,Y,hY,hp,(partial_sound φ e K D Y Z hl hp hz t htD).mpr h⟩

theorem partial_of_agrees (φ : Formula) (e : ℕ → ZFSet.{0}) (K D Y Z : ZFSet.{0})
    (hl : Local φ e) (hz : ∀ t ∈ K, t ∈ Z ↔ φ.Eval (cons t (cons Z e)))
    (hD : Transitive D) (hDK : D ⊆ K) (hYD : Y ⊆ D)
    (ha : ∀ t ∈ D, t ∈ Y ↔ t ∈ Z) : Partial φ e K D Y := by
  refine ⟨hD,hDK,hYD,?_⟩
  intro t ht
  exact (ha t ht).trans ((hz t (hDK ht)).trans
    (hl D hD t ht Y Z (fun s hs _ => ha s hs)).symm)

theorem truth_internal (M K Z : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hKM : K ∈ M) (hK : Transitive K) (φ : Formula) (e : ℕ → ZFSet.{0})
    (he : ∀ i, e i ∈ M) (hl : Local φ e)
    (hz : ∀ t ∈ K, t ∈ Z ↔ φ.Eval (cons t (cons Z e))) :
    K.sep (fun t => t ∈ Z) ∈ M := by
  classical
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hKM
  let D := domain φ e K Q
  let Y := truth φ e K Q
  obtain ⟨hDM,hYM⟩ := domain_truth_mem M K Q hM hT hKM hQM φ e he
  have hD : Transitive D := domain_transitive φ e K Q
  have hDK : D ⊆ K := fun _ h => (ZFSet.mem_sep.mp h).1
  have hYD : Y ⊆ D := truth_subset_domain φ e K Q
  have ha : ∀ t ∈ D, t ∈ Y ↔ t ∈ Z := truth_agrees φ e K Q Z hl hz
  have hcover (t : ZFSet.{0}) : t ∈ K → t ∈ D := by
    induction t using ZFSet.inductionOn with
    | h t ih =>
      intro htK
      by_cases htD : t ∈ D
      · exact htD
      have hchildren : t ⊆ D := fun s hs => ih s hs (hK t htK s hs)
      let D' := D ∪ ({t} : ZFSet.{0})
      let Y' := if t ∈ Z then Y ∪ ({t} : ZFSet.{0}) else Y
      have hDD' : D ⊆ D' := fun _ h => ZFSet.mem_union.mpr (Or.inl h)
      have htD' : t ∈ D' := ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl))
      have hD' : Transitive D' := by
        intro a ha b hb
        rcases ZFSet.mem_union.mp ha with ha | ha
        · exact hDD' (hD a ha b hb)
        · have ha := ZFSet.mem_singleton.mp ha
          subst a
          exact hDD' (hchildren hb)
      have hD'K : D' ⊆ K := by
        intro a ha
        rcases ZFSet.mem_union.mp ha with ha | ha
        · exact hDK ha
        · exact (ZFSet.mem_singleton.mp ha) ▸ htK
      have hY'D' : Y' ⊆ D' := by
        intro a ha
        dsimp [Y'] at ha
        split_ifs at ha
        · rcases ZFSet.mem_union.mp ha with ha | ha
          · exact hDD' (hYD ha)
          · exact (ZFSet.mem_singleton.mp ha) ▸ htD'
        · exact hDD' (hYD ha)
      have ha' : ∀ a ∈ D', a ∈ Y' ↔ a ∈ Z := by
        intro a haD'
        by_cases hat : a = t
        · subst a
          have htY : t ∉ Y := fun h => htD (hYD h)
          simp only [Y']
          split_ifs with htZ <;> simp [htZ,htY]
        · have haD : a ∈ D := (ZFSet.mem_union.mp haD').resolve_right (fun h => hat (ZFSet.mem_singleton.mp h))
          have hae := ha a haD
          dsimp [Y']
          split_ifs <;> simpa only [ZFSet.mem_union,ZFSet.mem_singleton,hat,or_false] using hae
      have htM := hM K hKM t htK
      have hsM := singleton_mem M hM hT.pairing htM
      have hD'M : D' ∈ M := binary_union_mem M hM hT.pairing hT.union hDM hsM
      have hY'M : Y' ∈ M := by
        dsimp [Y']; split_ifs
        · exact binary_union_mem M hM hT.pairing hT.union hYM hsM
        · exact hYM
      exact ZFSet.mem_sep.mpr ⟨htK,D',(hQ _).mpr ⟨hD'M,hD'K⟩,
        Y',(hQ _).mpr ⟨hY'M,fun _ h => hD'K (hY'D' h)⟩,
        partial_of_agrees φ e K D' Y' Z hl hz hD' hD'K hY'D' ha',htD'⟩
  have eq : Y = K.sep (fun t => t ∈ Z) := by
    apply ZFSet.ext; intro t
    constructor
    · intro ht
      exact ZFSet.mem_sep.mpr ⟨hDK (hYD ht),(ha t (hYD ht)).mp ht⟩
    · intro ht
      obtain ⟨htK,htZ⟩ := ZFSet.mem_sep.mp ht
      exact (ha t (hcover t htK)).mpr htZ
  exact eq ▸ hYM

end TuringRigidity.BoundedTruthRecursion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanExpressionTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionTruth
open TransitiveNameModel BoundedSetTheory

theorem value_unfold (B R t : ZFSet.{0}) : value B R t ↔
    (∃ U ∈ B, t = FiniteTerm.tag 0 U ∧ U ∈ R) ∨
    (∃ s, t = FiniteTerm.tag 1 s ∧ ¬ value B R s) ∨
    (∃ T, t = FiniteTerm.tag 2 T ∧ ∃ s ∈ T, value B R s) := by
  change rankWF.fix (body B R) t ↔ _
  rw [WellFounded.fix_eq]
  simp only [body,value,exists_prop]

theorem payload_mem (D : ZFSet.{0}) (hD : Transitive D) (n : ℕ) (s : ZFSet.{0})
    (ht : FiniteTerm.tag n s ∈ D) : s ∈ D := by
  have hp := hD _ ht _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  exact hD _ hp _ (ZFSet.mem_pair.mpr (Or.inr rfl))

theorem formula_spec (K B R Y t : ZFSet.{0}) :
    formula.Eval (cons t (cons Y (parameters K B R))) ↔ step K B R Y t := by
  simp only [formula,Formula.eval_disj,Formula.Eval,Formula.eval_orderedPair,
    parameters,cons_zero,cons_succ,step,FiniteTerm.tag]

theorem formula_local (K B R : ZFSet.{0}) : BoundedTruthRecursion.Local formula (parameters K B R) := by
  intro D hD t ht Y Z ha
  rw [formula_spec,formula_spec]
  apply or_congr Iff.rfl
  apply or_congr
  · apply exists_congr; intro s
    apply and_congr_right; intro _
    apply and_congr_right; intro he
    have hsD := payload_mem D hD 1 s (he ▸ ht)
    have hlt : ZFSet.rank s < ZFSet.rank t := by rw [he]; exact FiniteTerm.pair_rank_right _ _
    exact not_congr (ha s hsD hlt)
  · apply exists_congr; intro T
    apply and_congr_right; intro _
    apply and_congr_right; intro he
    have hTD := payload_mem D hD 2 T (he ▸ ht)
    apply exists_congr; intro s
    apply and_congr_right; intro hs
    have hlt : ZFSet.rank s < ZFSet.rank t := by
      rw [he]; exact (ZFSet.rank_lt_of_mem hs).trans (FiniteTerm.pair_rank_right _ _)
    exact ha s (hD T hTD s hs) hlt

theorem valueSet_fixed (K B R : ZFSet.{0}) (hK : Transitive K) :
    ∀ t ∈ K, t ∈ valueSet K B R ↔ formula.Eval (cons t (cons (valueSet K B R) (parameters K B R))) := by
  intro t ht
  rw [valueSet,ZFSet.mem_sep,and_iff_right ht,value_unfold,formula_spec]
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨s,he,hs⟩
      have hsK := payload_mem K hK 1 s (he ▸ ht)
      exact ⟨s,hsK,he,fun h => hs (ZFSet.mem_sep.mp h).2⟩
    · rintro ⟨s,hsK,he,hs⟩
      exact ⟨s,he,fun hv => hs (ZFSet.mem_sep.mpr ⟨hsK,hv⟩)⟩
  · constructor
    · rintro ⟨T,he,s,hs,hv⟩
      have hTK := payload_mem K hK 2 T (he ▸ ht)
      exact ⟨T,hTK,he,s,hs,ZFSet.mem_sep.mpr ⟨hK T hTK s hs,hv⟩⟩
    · rintro ⟨T,_,he,s,hs,hv⟩
      exact ⟨T,he,s,hs,(ZFSet.mem_sep.mp hv).2⟩

theorem valueSet_mem (N K B R : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hKN : K ∈ N) (hK : Transitive K) (hB : B ∈ N) (hR : R ∈ N) : valueSet K B R ∈ N := by
  have he : ∀ i, parameters K B R i ∈ N := by
    intro i; rcases i with _|_|_|_|_|i
    exact hKN; exact hB; exact hR
    all_goals exact hN _ (sourceT_omega_mem N hN hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hi := BoundedTruthRecursion.truth_internal N K (valueSet K B R) hN hT hKN hK
    formula (parameters K B R) he (formula_local K B R) (valueSet_fixed K B R hK)
  have eq : K.sep (fun t => t ∈ valueSet K B R) = valueSet K B R := by
    apply ZFSet.ext; intro t
    simp only [valueSet,ZFSet.mem_sep,and_self_left]
  exact eq ▸ hi

end TuringRigidity.BooleanExpressionTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanTruthReading
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionTruth
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanBits InternalBooleanGeneric
open BooleanExpressionCertificate
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem value_seed (B R U : ZFSet.{0}) (hU : U ∈ B) :
    value B R (FiniteTerm.tag 0 U) ↔ U ∈ R := by
  rw [value_unfold]
  simp [FiniteTerm.tag_inj,hU]

theorem value_neg (B R t : ZFSet.{0}) :
    value B R (FiniteTerm.tag 1 t) ↔ ¬ value B R t := by
  rw [value_unfold]
  simp [FiniteTerm.tag_inj]

theorem value_sup (B R T : ZFSet.{0}) :
    value B R (FiniteTerm.tag 2 T) ↔ ∃ t ∈ T, value B R t := by
  rw [value_unfold]
  simp [FiniteTerm.tag_inj]

theorem certificate_value (M c B Q S K g R : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B)
    (hg : Certificate c B Q S K g)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hseed : ∀ U ∈ S, U ∈ R ↔ Hit G U)
    (t U : ZFSet.{0}) (hp : ZFSet.pair t U ∈ g) : value B R t ↔ Hit G U := by
  induction t using rankWF.induction generalizing U with
  | h t ih =>
    have hUB := (hg.step hp).2.1
    rcases (hg.step hp).2.2 with hs | hs | hs
    · obtain ⟨hUS,rfl⟩ := hs
      exact (value_seed B R U hUB).trans (hseed U hUS)
    · obtain ⟨s,_,V,hVB,rfl,hchild,rfl⟩ := hs
      obtain ⟨hVM,hVc⟩ := (hB V).mp hVB
      rw [value_neg,hit_complement_iff M c V hM hT hc hVM hVc G hG,
        ih s (FiniteTerm.pair_rank_right _ _) V hchild]
    · obtain ⟨T,_,F,hFQ,rfl,rfl,hTF,hFT⟩ := hs
      obtain ⟨hFM,hFB⟩ := (hQ F).mp hFQ
      rw [value_sup,hit_supCode_iff M c F hM hT hc hFM (fun V hV => ((hB V).mp (hFB hV)).2) G hG]
      constructor
      · rintro ⟨s,hs,hv⟩
        obtain ⟨V,hVF,hchild⟩ := hTF s hs
        exact ⟨V,hVF,(ih s ((ZFSet.rank_lt_of_mem hs).trans (FiniteTerm.pair_rank_right _ _)) V hchild).mp hv⟩
      · rintro ⟨V,hVF,hv⟩
        obtain ⟨s,hs,hchild⟩ := hFT V hVF
        exact ⟨s,hs,(ih s ((ZFSet.rank_lt_of_mem hs).trans (FiniteTerm.pair_rank_right _ _)) V hchild).mpr hv⟩

theorem seedTruth_mem (N c B : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hB : B ∈ N) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ N ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ N)
    (X : ZFSet.{0}) (hX : X ∈ N) : seedTruth c B E X ∈ N := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power N hN hT.powerSet hc
  let e := cons c (cons ZFSet.omega (cons Q (cons (orbitGraph E) (fun _ => X))))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|_|i
    exact hc; exact sourceT_omega_mem N hN hT; exact hQ; exact hgraph; exact hX
  let φ : Formula := .existsMem 2 (.conj (.member 0 6)
    (.existsMem 4 (.conj (.pairMem 1 0 6) (bitFormula 3 0 2))))
  have spec (U : ZFSet.{0}) : φ.Eval (cons U e) ↔ ∃ n, natSet n ∈ X ∧ U = bitCode c (E n) := by
    simp only [φ,Formula.Eval,Formula.eval_pairMem,bitFormula_spec,e,cons_zero,cons_succ]
    constructor
    · rintro ⟨n,hn,hnX,V,_,hp,hU⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hV := (orbitGraph_pair E n V).mp hp
      exact ⟨n,hnX,hV ▸ hU⟩
    · rintro ⟨n,hnX,hU⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,hnX,E n,(hQdef _).mpr (hE n),
        (orbitGraph_pair E n _).mpr rfl,hU⟩
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded φ e he hB
  simpa only [spec,seedTruth] using hs

theorem seedTruth_hit (M c B : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hGt : ⊤ ∈ G.carrier) (U : ZFSet.{0}) (hUS : U ∈ seeds c B E) :
    U ∈ seedTruth c B E ((InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier) ↔ Hit G U := by
  constructor
  · intro h
    obtain ⟨_,n,hn,rfl⟩ := ZFSet.mem_sep.mp h
    exact (hit_bit_iff M c hM hT hc E hE G hG hGt n).mpr hn
  · intro h
    obtain ⟨hUB,n,rfl⟩ := ZFSet.mem_sep.mp hUS
    exact ZFSet.mem_sep.mpr ⟨hUB,n,(hit_bit_iff M c hM hT hc E hE G hG hGt n).mp h,rfl⟩

end TuringRigidity.BooleanExpressionTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanEvaluationWitness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanExpressionTruth
open TransitiveNameModel BoundedSetTheory BooleanExpressionCertificate

theorem GoodTruth.agrees {K B R Y : ZFSet.{0}} (hK : Transitive K) (hy : GoodTruth K B R Y) :
    ∀ t ∈ K, t ∈ Y ↔ value B R t := by
  have hp : BoundedTruthRecursion.Partial formula (parameters K B R) K K Y :=
    ⟨hK,fun _ h => h,hy.1,fun t ht => (hy.2 t ht).trans (formula_spec K B R Y t).symm⟩
  intro t ht
  exact (BoundedTruthRecursion.partial_sound formula (parameters K B R) K K Y (valueSet K B R)
    (formula_local K B R) hp (valueSet_fixed K B R hK) t ht).trans
      (ZFSet.mem_sep.trans (and_iff_right ht))

theorem valueSet_good (K B R : ZFSet.{0}) (hK : Transitive K) : GoodTruth K B R (valueSet K B R) :=
  ⟨fun _ h => (ZFSet.mem_sep.mp h).1,
    fun t ht => (valueSet_fixed K B R hK t ht).trans (formula_spec K B R _ t)⟩

theorem truthAt_spec (t Y K B R z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (truthAt t Y K B R z0 z1 z2).Eval e ↔ step (e K) (e B) (e R) (e Y) (e t) := by
  have eq : e ∘ truthSlots t Y K B R z0 z1 z2 = cons (e t) (cons (e Y) (parameters (e K) (e B) (e R))) := by
    funext i
    rcases i with _|_|_|_|_|_|_|i
    rfl; rfl; rfl; rfl; rfl; exact h0; exact h1; exact h2
  rw [truthAt,Formula.eval_rename_comp,eq,formula_spec]

theorem goodTruthFormula_spec (K B R Y z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (goodTruthFormula K B R Y z0 z1 z2).Eval e ↔ GoodTruth (e K) (e B) (e R) (e Y) := by
  simp only [goodTruthFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,Formula.eval_iff,
    cons_zero,cons_succ,GoodTruth]
  apply and_congr Iff.rfl
  apply forall_congr'; intro t
  apply imp_congr_right; intro _
  exact iff_congr Iff.rfl (truthAt_spec _ _ _ _ _ _ _ _ _ h0 h1 h2)

theorem evaluatedFormula_spec (c B Q S R K Y U z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (evaluatedFormula c B Q S R K Y U z0 z1 z2).Eval e ↔
      Evaluated (e c) (e B) (e Q) (e S) (e R) (e K) (e Y) (e U) := by
  simp only [evaluatedFormula,Formula.Eval,Formula.eval_transitive,Formula.eval_pairMem,
    cons_zero,cons_succ,Evaluated]
  apply and_congr Iff.rfl
  apply and_congr (goodTruthFormula_spec _ _ _ _ _ _ _ _ h0 h1 h2)
  apply exists_congr; intro g
  apply and_congr_right; intro _
  exact and_congr (certificateFormula_spec _ _ _ _ _ _ _ _ _ _ h0 h1 h2) Iff.rfl

theorem evaluationBody_realize (N W c B Q S R Y U : ZFSet.{0}) (hN : Transitive N)
    (he : ∀ i, evaluationParameters W c B Q S R i ∈ N) (hY : Y ∈ N) (hU : U ∈ N) :
    evaluationBody.Realize N (cons Y (cons U (evaluationParameters W c B Q S R))) ↔
      ∃ K ∈ W, Evaluated c B Q S R K Y U := by
  rw [Formula.absolute _ N hN _ (by
    intro i; rcases i with _|_|i; exact hY; exact hU; exact he i)]
  change (∃ K ∈ W, (evaluatedFormula 4 5 6 7 8 0 1 2 9 10 11).Eval
    (cons K (cons Y (cons U (evaluationParameters W c B Q S R))))) ↔ _
  apply exists_congr; intro K
  apply and_congr_right; intro _
  exact evaluatedFormula_spec _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl

end TuringRigidity.BooleanExpressionTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BooleanFilterReconstruction
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BooleanFilterReconstruction
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax
open InternalBooleanBits InternalBooleanGeneric InternalGeneratedAlgebra InternalProjectedGeneric
open BooleanExpressionCertificate BooleanExpressionTruth
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

theorem witness_bound (M c B Q S A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hSM : S ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hSB : S ⊆ B)
    (hA : A ⊆ generated c B Q S) :
    ∃ W ∈ M, ∀ U ∈ A, ∃ K ∈ W, Witness c B Q S K U := by
  have he := parameters_mem M c B Q S hM hT hc hBM hQM hSM
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  obtain ⟨W,hWM,hW⟩ := hColl (.bounded witnessBody) (BooleanExpressionCertificate.parameters c B Q S) he A hAM (by
    intro U hU
    obtain ⟨K,hKM,hK⟩ := generated_certificate M c B Q S U hM hT hc hBM hQM hSM hB hQ hSB (hA hU)
    exact ⟨K,hKM,(witnessBody_realize M c B Q S K U hM he hKM (hM A hAM U hU)).mpr hK⟩)
  refine ⟨W,hWM,?_⟩
  intro U hU
  obtain ⟨K,hKW,hK⟩ := hW U hU
  exact ⟨K,hKW,(witnessBody_realize M c B Q S K U hM he (hM W hWM K hKW) (hM A hAM U hU)).mp hK⟩

theorem hit_values_mem (M N c B Q S A W R : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hN : Transitive N) (hTN : SourceT N)
    (hc : c ∈ M) (hcN : c ∈ N) (hBN : B ∈ N) (hQN : Q ∈ N) (hSN : S ∈ N)
    (hAN : A ∈ N) (hWN : W ∈ N) (hRN : R ∈ N)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B)
    (hbound : ∀ U ∈ A, ∃ K ∈ W, Witness c B Q S K U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hseed : ∀ U ∈ S, U ∈ R ↔ Hit G U) : A.sep (Hit G) ∈ N := by
  let e := evaluationParameters W c B Q S R
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|_|_|_|_|_|i
    exact hWN; exact hcN; exact hBN; exact hQN; exact hSN; exact hRN
    all_goals exact hN _ (sourceT_omega_mem N hN hTN) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have spec (U : ZFSet.{0}) (hUA : U ∈ A) :
      (∃ Y ∈ N, evaluationBody.Realize N (cons Y (cons U e))) ↔ Hit G U := by
    constructor
    · rintro ⟨Y,hYN,hbody⟩
      obtain ⟨K,_,hK,hy,g,_,hg,t,htK,hp,htY⟩ :=
        (evaluationBody_realize N W c B Q S R Y U hN he hYN (hN A hAN U hUA)).mp hbody
      have hv := (hy.agrees hK t htK).mp htY
      exact (certificate_value M c B Q S K g R hM hT hc hB hQ hg G hG hseed t U hp).mp hv
    · intro hhit
      obtain ⟨K,hKW,hK,g,hgK,hg,t,htK,hp⟩ := hbound U hUA
      have hKN := hN W hWN K hKW
      have hYN := valueSet_mem N K B R hN hTN hKN hK hBN hRN
      have hv := (certificate_value M c B Q S K g R hM hT hc hB hQ hg G hG hseed t U hp).mpr hhit
      refine ⟨valueSet K B R,hYN,
        (evaluationBody_realize N W c B Q S R _ U hN he hYN (hN A hAN U hUA)).mpr ?_⟩
      exact ⟨K,hKW,hK,valueSet_good K B R hK,g,hgK,hg,t,htK,hp,ZFSet.mem_sep.mpr ⟨htK,hv⟩⟩
  obtain ⟨a,ha,hspec⟩ := hTN.separation.finitePrefix (.existsSet (.bounded evaluationBody)) e he A hAN
  have eq : a = A.sep (Hit G) := by
    apply ZFSet.ext; intro U
    constructor
    · intro hU
      obtain ⟨hUA,hbody⟩ := (hspec U (hN a ha U hU)).mp hU
      exact ZFSet.mem_sep.mpr ⟨hUA,(spec U hUA).mp hbody⟩
    · intro hU
      obtain ⟨hUA,hhit⟩ := ZFSet.mem_sep.mp hU
      exact (hspec U (hN A hAN U hUA)).mpr ⟨hUA,(spec U hUA).mpr hhit⟩
  exact eq ▸ ha

theorem projected_filter_eq_hits (M c B Q A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B) (hA : Closed c B Q A)
    (G : GenericFilter (Conditions c)) :
    genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      A.sep (Hit G) := by
  apply ZFSet.ext; intro U
  rw [mem_genericFilterSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨(ZFSet.mem_sep.mp (label_mem (positive A) q)).1,hq⟩
  · rintro ⟨hUA,p,hp,hpU⟩
    have hU0 : U ≠ ∅ := fun he => ZFSet.notMem_empty _ (he ▸ hpU)
    obtain ⟨q,hq⟩ := label_surjective (positive A) (ZFSet.mem_sep.mpr ⟨hUA,hU0⟩)
    refine ⟨q,?_,hq⟩
    change Hit G (label (positive A) q)
    rw [hq]
    exact ⟨p,hp,hpU⟩

theorem projected_filter_mem_from_real (M N c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈ G.carrier)
    (hX : (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier ∈ N) :
    genericFilterSet (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ∈ N := by
  have hSM := seeds_mem M c B hM hT hc hBM E hE hgraph
  obtain ⟨W,hWM,hbound⟩ := witness_bound M c B Q (seeds c B E) A hM hT hc hBM hQM hSM hAM hB hQ
    (fun _ h => (ZFSet.mem_sep.mp h).1) (fun _ h => hAe ▸ h)
  have hRN := seedTruth_mem N c B hN hTN (hMN hc) (hMN hBM) E
    (fun n => ⟨hMN (hE n).1,(hE n).2⟩) (hMN hgraph) _ hX
  rw [projected_filter_eq_hits M c B Q A hM hT hc hBM hAM hB hQ hA G]
  exact hit_values_mem M N c B Q (seeds c B E) A W _ hM hT hN hTN hc (hMN hc) (hMN hBM)
    (hMN hQM) (hMN hSM) (hMN hAM) (hMN hWM) hRN hB hQ hbound G hG
    (fun U hU => seedTruth_hit M c B hM hT hc E hE G hG hGt U hU)

theorem projected_extension_least_for_real (M N c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hN : Transitive N) (hTN : SourceT N) (hMN : M ⊆ N)
    (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈ G.carrier)
    (hX : (InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier ∈ N) :
    genericExtensionSet M (positive A)
      (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier ⊆ N := by
  apply InternalNameEvaluation.extension_subset M N hN hTN hMN
  exact projected_filter_mem_from_real M N c B Q A hM hT hN hTN hMN hc hBM hQM hAM hB hQ hA
    E hE hgraph hAe G hG hGt hX

end TuringRigidity.BooleanFilterReconstruction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealGeneratedModel
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RealGeneratedModel
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalGeneratedAlgebra InternalProjectedGeneric InternalBooleanTop

theorem mem_hull (M X z : ZFSet.{0}) (h : ∃ N, Contains M X N) :
    z ∈ hull M X ↔ ∀ N, Contains M X N → z ∈ N := by
  rw [hull,dite_eq_left h,ZFSet.mem_sep]
  exact ⟨fun hz => hz.2,fun hz => ⟨hz h.choose h.choose_spec,hz⟩⟩

theorem hull_eq_of_least (M X H : ZFSet.{0}) (hH : Contains M X H)
    (hleast : ∀ N, Contains M X N → H ⊆ N) : hull M X = H := by
  apply ZFSet.ext; intro z
  rw [mem_hull M X z ⟨H,hH⟩]
  exact ⟨fun hz => hz H hH,fun hz N hN => hleast N hN hz⟩

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

theorem projected_extension_eq_hull_oai (M c B Q A : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hQM : Q ∈ M) (hAM : A ∈ M)
    (hB : ∀ V, V ∈ B ↔ V ∈ M ∧ IsCode c V)
    (hQ : ∀ a, a ∈ Q ↔ a ∈ M ∧ a ⊆ B) (hA : Closed c B Q A)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ M)
    (hAe : A = generated c B Q (seeds c B E))
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (hGt : ⊤ ∈ G.carrier) :
    genericExtensionSet M (positive A) (projected M c B Q A hM hT hc hBM hAM hB hQ hA G).carrier =
      hull M ((InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val G.carrier) := by
  have hcA := top_mem_part M c B Q A hM hT hc hBM hB hQ hA
  have hc0 : c ≠ ∅ := fun he => ZFSet.notMem_empty _
    (Eq.mp (congrArg (fun d => label c ⊤ ∈ d) he) (label_mem c ⊤))
  let _ := booleanTop c A hcA hc0
  have ht : label (positive A) ⊤ = c := label_booleanTop c A hcA hc0
  have hbits (n : ℕ) : bitCode c (E n) ∈ A := by
    rw [hAe]
    exact seeds_subset c B Q _ (fun _ h => (ZFSet.mem_sep.mp h).1)
      (bit_mem_seeds M c B hM hT hc hB E (fun n => (hE n).1) n)
  obtain ⟨hN,hTN,hMN,hXN,_,_⟩ := InternalBooleanExtension.projected_extension_sandwich
    M c B Q A hM hT hc hBM hAM hB hQ hA ht E hE hgraph hbits G hG hGt
  symm
  apply hull_eq_of_least M _ _ ⟨hN,hTN,hMN,hXN⟩
  intro N hN
  exact BooleanFilterReconstruction.projected_extension_least_for_real M N c B Q A hM hT
    hN.1 hN.2.1 hN.2.2.1 hc hBM hQM hAM hB hQ hA E hE hgraph hAe G hG hGt hN.2.2.2

end TuringRigidity.RealGeneratedModel

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RealGeneratedModel.projected_extension_eq_hull_oai := @OAI.TuringRigidity.RealGeneratedModel.projected_extension_eq_hull_oai
