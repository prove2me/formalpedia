-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.real_hull_generic_column_realizes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:34:45.729898+00:00
-- url     : https://prove2.me/submissions/3021087d-36e3-4d4f-ad05-9d6108d99df7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_CohenRemainderTransport_transport_to_remainder
import Theorems.Thm_OAI_TuringRigidity_InternalCohen_prefix_extension_eq_hull
import Theorems.Thm_OAI_TuringRigidity_TwoRealHull_joined_factorization

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenConditions
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing

theorem conditions_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) : conditions ∈ M := by
  obtain ⟨c,hc,hdef⟩ := conditions_exist_absolute_without_choice M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT)
    (alphabet_mem M hM hT)
  have he : c = conditions := ZFSet.ext (fun p => (hdef p).trans (mem_conditions p).symm)
  exact he ▸ hc

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCollapseCounting
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

theorem mem_unionGraph {c : ZFSet.{u}} (G : GenericFilter (Conditions c)) (z : ZFSet.{u}) :
    z ∈ unionGraph G ↔ ∃ p ∈ G.carrier, z ∈ label c p := by
  rw [unionGraph,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨p,hp,hz⟩
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet c G.carrier p).mp hp
    exact ⟨q,hq,hz⟩
  · rintro ⟨p,hp,hz⟩
    exact ⟨label c p,(mem_genericFilterSet c G.carrier _).mpr ⟨p,hp,rfl⟩,hz⟩

theorem unionGraph_mem_extension (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c : ZFSet.{u}} (hcM : c ∈ M) (h0 : (∅ : ZFSet.{u}) ∈ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M c G.carrier := by
  let _ := top c h0
  have htop : ⊤ ∈ G.carrier := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact G.upper le_top hp
  have hE := extension_sourceT M hM hT hcM (orderSet_mem M hM hT hcM) (orderSet_pair c) G hG htop
  apply union_mem _ (genericExtensionSet_transitive M c hM G.carrier) hE.union
  exact genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcM G.carrier htop

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGenericUnion
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenGenericUnion
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenSymmetry CohenConditionCode CohenGroundPoset CohenGroundGeneric
open InternalCohen (alphabet mem_alphabet bitSet)
open InternalCollapse (unionGraph mem_unionGraph)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem definedAt_mem (M A x : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hx : x ∈ A) : definedAt A x ∈ M := by
  let e := cons alphabet (fun _ => x)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i
    exact InternalCohen.alphabet_mem M hM hT
    exact hM A hA x hx
  simpa only [definedAt,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.pairMem 3 0 1)) e he (conditions_mem M A hM hT hA)

theorem assign_dense {ι : Type*} (i : ι) :
    Dense {p : Condition ι | ∃ b, p.val i = some b} := by
  classical
  intro p
  cases hi : p.val i with
  | some b => exact ⟨p,le_rfl,b,hi⟩
  | none =>
    let q : Condition ι := {
      val j := if j = i then some false else p.val j
      finite := (p.finite.insert i).subset (by
        intro j hj
        by_cases he : j = i
        · exact Or.inl he
        · exact Or.inr (by simpa [he] using hj)) }
    refine ⟨q,?_,false,by simp [q]⟩
    intro j b hj
    by_cases he : j = i
    · subst j; rw [hi] at hj; cases hj
    · simpa [q,he] using hj

theorem definedAt_dense (A x : ZFSet.{0}) (hx : x ∈ A) :
    Dense {q : Conditions (conditions A) | label _ q ∈ definedAt A x} := by
  let i : Conditions A := equivShrink A ⟨x,hx⟩
  have hi : label A i = x := by simp [i,label]
  intro p
  obtain ⟨q,hq,b,hqb⟩ := assign_dense i ((conditionEquiv A).symm p)
  refine ⟨conditionEquiv A q,by simpa using (conditionEquiv A).monotone hq,?_⟩
  change label _ (encode A q) ∈ definedAt A x
  rw [label_encode,definedAt,ZFSet.mem_sep]
  refine ⟨(mem_conditions A _).mpr (graph_isCondition A q),bitSet b,
    (mem_alphabet _).mpr ⟨b,rfl⟩,?_⟩
  rw [←hi,pair_mem_graph]; exact hqb

theorem union_function (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (G : GenericFilter (Conditions (conditions A)))
    (hG : AtomicForcing.GroundGeneric M G) : FunctionGraph A alphabet (unionGraph G) := by
  constructor
  · intro z hz
    obtain ⟨p,_,hzp⟩ := (mem_unionGraph G z).mp hz
    have hp := ((mem_conditions A _).mp (label_mem _ p)).1
    exact ZFSet.mem_prod.mp (((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp hp).1 hzp)
  · intro x hx
    obtain ⟨p,hp,hpx⟩ := hG (definedAt A x) (definedAt_mem M A x hM hT hA hx)
      (definedAt_dense A x hx)
    obtain ⟨_,b,hb,hpb⟩ := ZFSet.mem_sep.mp hpx
    refine ⟨b,hb,(mem_unionGraph G _).mpr ⟨p,hp,hpb⟩,?_⟩
    intro c hc hxc
    obtain ⟨q,hq,hqc⟩ := (mem_unionGraph G _).mp hxc
    obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
    exact ((mem_conditions A _).mp (label_mem _ r)).2 x hx c hc b hb (hrq hqc) (hrp hpb)

theorem union_internal (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (G : GenericFilter (Conditions (conditions A)))
    (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M (conditions A) G.carrier ∧
      FunctionGraph A alphabet (unionGraph G) :=
  ⟨InternalCollapse.unionGraph_mem_extension M hM hT (conditions_mem M A hM hT hA)
      (empty_mem_conditions A) G hG,
    union_function M A hM hT hA G hG⟩

theorem manyColumn_union (M K : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hK : K ∈ M)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
      FunctionGraph (ZFSet.prod K ZFSet.omega) alphabet (unionGraph G) :=
  union_internal M _ hM hT (product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)) G hG

end TuringRigidity.CohenGenericUnion

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFiniteEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalFiniteEnumeration
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets RelativeConstructible

theorem rangeFormula_ranges (ω U E g : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega) :
    (rangeFormula ω U E g).Eval e ↔ Ranges (e U) (e E) (e g) := by
  simp only [rangeFormula,Ranges,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,hω]

theorem candidateFormula_spec (ω U C E a : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega) :
    (candidateFormula ω U C E a).Eval e ↔ e a = candidates (e U) (e C) (e E) := by
  simp only [candidateFormula,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.Eval,cons_zero,cons_succ]
  have hr (g : ZFSet.{0}) := rangeFormula_ranges (ω+1) (U+1) (E+1) 0 (cons g e) hω
  simp only [cons_zero,cons_succ] at hr
  simp only [hr]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro g
    exact ⟨fun hg => ZFSet.mem_sep.mpr ⟨hsub hg,(h g (hsub hg)).mp hg⟩,
      fun hg => (h g (ZFSet.mem_sep.mp hg).1).mpr (ZFSet.mem_sep.mp hg).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hg => (ZFSet.mem_sep.mp hg).1,
      fun g hg => ZFSet.mem_sep.trans (and_iff_right hg)⟩

theorem candidates_mem (M U C E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (hC : C ∈ M) (hE : E ∈ M) : candidates U C E ∈ M := by
  let e := cons ZFSet.omega (cons U (fun _ => E))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact sourceT_omega_mem M hM hT
    exact hU; exact hE
  have hr (g : ZFSet.{0}) := rangeFormula_ranges 1 2 3 0 (cons g e) rfl
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded (rangeFormula 1 2 3 0) e he hC
  simpa only [hr,candidates,cons_zero,cons_succ,e] using hs

theorem internal_enumeration_selector (M U : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hU : U ∈ M) :
    ∃ C ∈ M, (∀ g, g ∈ C ↔ InternalCollapse.Prefix U g) ∧
      ∃ T ∈ M, FunctionGraph (finiteSubsets U) C T ∧
        ∀ E ∈ finiteSubsets U, ∀ g, ZFSet.pair E g ∈ T → Ranges U E g := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨C,hC,hCdef⟩ := InternalCollapse.conditions_exist_absolute_without_choice M hM
    hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hU
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hT.powerSet
    hT.separation.finitePrefix.bounded hT.choice hC
  have hcan (E : ZFSet.{0}) (hE : E ∈ finiteSubsets U) : candidates U C E ∈ q := by
    apply (hqdef _).mpr
    refine ⟨candidates_mem M U C E hM hT hU hC (finite_subset_mem M U E hM hT hU hE),
      fun _ hg => (ZFSet.mem_sep.mp hg).1,?_⟩
    obtain ⟨n,v,hv,rfl⟩ := (mem_finiteSubsets U E).mp hE
    refine ⟨tupleGraph v,ZFSet.mem_sep.mpr ⟨(hCdef _).mpr ⟨n,tupleGraph_function U v hv⟩,?_⟩⟩
    exact (rangeFormula_ranges 0 1 2 3
      (cons ZFSet.omega (cons U (cons (ZFSet.range v) (fun _ => tupleGraph v)))) rfl).mp
      ((rangeFormula_spec 0 1 2 3 _ rfl hv rfl).mpr rfl)
  let S := finiteSubsets U
  let e := cons ZFSet.omega (cons U (cons C (cons S (cons q (fun _ => s)))))
  let φ : Formula := .existsMem 4 (.existsMem 4 (.conj (.orderedPair 2 1 0)
    (.existsMem 7 (.conj (candidateFormula 4 5 6 2 0) (.pairMem 0 1 9)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact hω; exact hU; exact hC; exact finiteSubsets_mem M U hM hT hU
    exact hq; exact hsM
  let T := (ZFSet.prod S C).sep (fun z => φ.Eval (cons z e))
  have hTM : T ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (finiteSubsets_mem M U hM hT hU) hC)
  have hmem (z : ZFSet.{0}) : z ∈ T ↔ ∃ E ∈ S, ∃ g ∈ C,
      z = ZFSet.pair E g ∧ ZFSet.pair (candidates U C E) g ∈ s := by
    simp only [T,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,E,hE,g,hg,hz,a,_,ha,hag⟩
      have ha' := (candidateFormula_spec 4 5 6 2 0 _ rfl).mp ha
      change a = candidates U C E at ha'
      exact ⟨E,hE,g,hg,hz,ha' ▸ hag⟩
    · rintro ⟨E,hE,g,hg,rfl,hag⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨E,hE,g,hg,rfl⟩,E,hE,g,hg,rfl,
        candidates U C E,hcan E hE,(candidateFormula_spec 4 5 6 2 0 _ rfl).mpr rfl,hag⟩
  refine ⟨C,hC,hCdef,T,hTM,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨E,hE,g,hg,hz,_⟩ := (hmem z).mp hz
    exact ⟨E,hE,g,hg,hz⟩
  · intro E hE
    obtain ⟨g,hg,hag,_⟩ := hs.2 _ (hcan E hE)
    have hgC := (ZFSet.mem_sep.mp hg).1
    refine ⟨g,hgC,(hmem _).mpr ⟨E,hE,g,hgC,rfl,hag⟩,?_⟩
    intro g' _ hEg'
    obtain ⟨E',_,g'',_,hp,hag'⟩ := (hmem _).mp hEg'
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact hs.functional hag' hag
  · intro E _ g hEg
    obtain ⟨E',_,g',_,hp,hag⟩ := (hmem _).mp hEg
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact (ZFSet.mem_sep.mp (InternalWellOrder.choice_value_mem hs hag)).2

end TuringRigidity.InternalFiniteEnumeration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableFiniteUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableFiniteUnion
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteEnumeration

theorem entryFormula_spec (U g d k x : ℕ) (e : ℕ → ZFSet.{0}) :
    (entryFormula U g d k x).Eval e ↔ Entry (e U) (e g) (e d) (e k) (e x) := by
  simp only [entryFormula,Entry,Formula.eval_disj,Formula.eval_allMem,
    Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]

theorem entry_exists_unique (U g d k : ZFSet.{0}) (hg : InternalCollapse.Prefix U g)
    (hd : d ∈ U) : ∃ x ∈ U, Entry U g d k x ∧ ∀ y ∈ U, Entry U g d k y → y = x := by
  classical
  by_cases h : ∃ x ∈ U, ZFSet.pair k x ∈ g
  · obtain ⟨x,hx,hkx⟩ := h
    obtain ⟨n,hg⟩ := hg
    have hk : k ∈ natSet n := by
      obtain ⟨k',hk,x',_,he⟩ := hg.1 _ hkx
      exact (ZFSet.pair_inj.mp he).1 ▸ hk
    refine ⟨x,hx,Or.inl hkx,?_⟩
    intro y _ hy
    rcases hy with hy|⟨_,hy⟩
    · exact hg.functional hk hy hkx
    · exact False.elim (hy x hx hkx)
  · exact ⟨d,hd,Or.inr ⟨rfl,fun y hy hky => h ⟨y,hy,hky⟩⟩,
      fun y hy he => he.elim (fun hky => False.elim (h ⟨y,hy,hky⟩)) And.left⟩

theorem flattenFormula_spec (ω Q S C B T U d k x : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ l, finiteNaturalGraph f l ∈ e Q) (N K : ℕ)
    (hk : e k = natSet (Nat.pair N K)) :
    (flattenFormula ω Q S C B T U d k x).Eval e ↔
      ∃ E ∈ e S, ZFSet.pair (natSet N) E ∈ e B ∧
        ∃ g ∈ e C, ZFSet.pair E g ∈ e T ∧ Entry (e U) g (e d) (natSet K) (e x) := by
  simp only [flattenFormula,Formula.Eval,Formula.eval_pairMem,entryFormula_spec,cons_zero,cons_succ]
  rw [hω]
  constructor
  · rintro ⟨n,hn,j,hj,hpair,hrest⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨j,rfl⟩ := (mem_omega j).mp hj
    have he := (Formula.naturalPair_spec (ω+2) (Q+2) 1 0 (k+2)
      (cons (natSet j) (cons (natSet n) e)) hω hQ n j rfl rfl).mp hpair
    have hh := congrArg Nat.unpair (natSet_injective (hk.symm.trans he))
    simp only [Nat.unpair_pair,Prod.mk.injEq] at hh
    obtain ⟨rfl,rfl⟩ := hh
    exact hrest
  · intro h
    exact ⟨natSet N,(mem_omega _).mpr ⟨N,rfl⟩,natSet K,(mem_omega _).mpr ⟨K,rfl⟩,
      (Formula.naturalPair_spec (ω+2) (Q+2) 1 0 (k+2)
        (cons (natSet K) (cons (natSet N) e)) hω hQ N K rfl rfl).mpr hk,h⟩

theorem internally_countable_union (M U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ finiteSubsets U)
    (hB : orbitGraph E ∈ M) (hcover : ∀ p ∈ U, ∃ n, p ∈ E n)
    (hne : ∃ p, p ∈ U) : InternallyCountable M U := by
  classical
  obtain ⟨d,hd⟩ := hne
  obtain ⟨C,hCM,hC,T,hTM,hTfun,hTrange⟩ := internal_enumeration_selector M U hM hT hU
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  let S := finiteSubsets U
  let B := orbitGraph E
  have hchoice (n k : ℕ) : ∃ x ∈ U, ∃ g ∈ C,
      ZFSet.pair (E n) g ∈ T ∧ Entry U g d (natSet k) x ∧
        ∀ y ∈ U, Entry U g d (natSet k) y → y = x := by
    obtain ⟨g,hg,hEg,_⟩ := hTfun.2 _ (hE n)
    obtain ⟨x,hx,he,hu⟩ := entry_exists_unique U g d (natSet k) ((hC g).mp hg) hd
    exact ⟨x,hx,g,hg,hEg,he,hu⟩
  choose v hv g hg hEg hentry huniq using hchoice
  let f : ℕ → ZFSet.{0} := fun i => v (Nat.unpair i).1 (Nat.unpair i).2
  let e := cons ZFSet.omega (cons Q (cons S (cons C (cons B (cons T (cons U (fun _ => d)))))))
  let φ : Formula := .existsMem 1 (.existsMem 8 (.conj (.orderedPair 2 1 0)
    (flattenFormula 3 4 5 6 7 8 9 10 1 0)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|_|i
    exact hω; exact hQM; exact finiteSubsets_mem M U hM hT hU
    exact hCM; exact hB; exact hTM; exact hU; exact hM U hU d hd
  have flat (N K : ℕ) (x : ZFSet.{0}) (hx : x ∈ U) (z : ZFSet.{0}) :
      (flattenFormula 3 4 5 6 7 8 9 10 1 0).Eval
        (cons x (cons (natSet (Nat.pair N K)) (cons z e))) ↔ x = v N K := by
    rw [flattenFormula_spec 3 4 5 6 7 8 9 10 1 0 _ rfl hQ N K rfl]
    change (∃ H ∈ S, ZFSet.pair (natSet N) H ∈ B ∧
      ∃ t ∈ C, ZFSet.pair H t ∈ T ∧ Entry U t d (natSet K) x) ↔ _
    constructor
    · rintro ⟨H,_,hNH,t,_,hHt,ht⟩
      have hH := (orbitGraph_pair E N H).mp hNH
      rw [hH] at hHt
      have ht' := hTfun.functional (hE N) hHt (hEg N K)
      exact huniq N K x hx (ht' ▸ ht)
    · rintro rfl
      exact ⟨E N,hE N,(orbitGraph_pair E N _).mpr rfl,g N K,hg N K,hEg N K,hentry N K⟩
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph f := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨i,hi,x,hx,hz,hflat⟩
      obtain ⟨i,rfl⟩ := (mem_omega i).mp hi
      have hn : natSet i = natSet (Nat.pair (Nat.unpair i).1 (Nat.unpair i).2) := by rw [Nat.pair_unpair]
      have hflat' := hflat
      rw [hn] at hflat'
      have hx' := (flat (Nat.unpair i).1 (Nat.unpair i).2 x hx z).mp hflat'
      exact (mem_orbitGraph f z).mpr ⟨i,by rw [hz,hx']⟩
    · intro hz
      obtain ⟨i,rfl⟩ := (mem_orbitGraph f z).mp hz
      refine ⟨natSet i,(mem_omega _).mpr ⟨i,rfl⟩,f i,hv _ _,rfl,?_⟩
      have hh := (flat (Nat.unpair i).1 (Nat.unpair i).2 (f i) (hv _ _)
        (ZFSet.pair (natSet i) (f i))).mpr rfl
      simpa only [Nat.pair_unpair] using hh
  have hG : orbitGraph f ∈ M := by
    have hh := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hU)
    have heq : (ZFSet.prod ZFSet.omega U).sep (fun z => φ.Eval (cons z e)) = orbitGraph f := by
      apply ZFSet.ext; intro z
      rw [ZFSet.mem_sep,hφ]
      exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function U f (fun _ => hv _ _)).1 z hz),hz⟩⟩
    exact heq ▸ hh
  refine ⟨orbitGraph f,hG,orbitGraph_function U f (fun _ => hv _ _),?_⟩
  intro p hp
  obtain ⟨n,hpE⟩ := hcover p hp
  have hr := hTrange (E n) (hE n) (g n 0) (hEg n 0)
  obtain ⟨k,hk,hkp⟩ := (hr.2 p hp).mp hpE
  obtain ⟨k,rfl⟩ := (mem_omega k).mp hk
  have heq := hTfun.functional (hE n) (hEg n 0) (hEg n k)
  have hpv := huniq n k p hp (Or.inl (heq ▸ hkp))
  refine ⟨natSet (Nat.pair n k),(mem_omega _).mpr ⟨Nat.pair n k,rfl⟩,?_⟩
  apply (orbitGraph_pair f _ p).mpr
  simpa only [f,Nat.unpair_pair] using hpv

end TuringRigidity.InternalCountableFiniteUnion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenFilters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem filter_ext {P : Type*} [Preorder P] (F H : GenericFilter P)
    (h : F.carrier = H.carrier) : F = H := by
  cases F; cases H; cases h; rfl

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenName
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing RecursiveNames
attribute [local instance] InternalCollapse.order

theorem eval_realNameFormula (z c f r one : ZFSet.{0}) (e : ℕ → ZFSet.{0}) :
    realNameFormula.Eval (cons z (cons c (cons ZFSet.omega (cons f (cons r (cons one e)))))) ↔
      ∃ q ∈ c, ∃ n ∈ ZFSet.omega, ∃ v ∈ r,
        ZFSet.pair n v ∈ f ∧ ZFSet.pair n one ∈ q ∧ z = ZFSet.pair v q := by
  simp only [realNameFormula,BoundedSetTheory.Formula.Eval,BoundedSetTheory.Formula.eval_pairMem,BoundedSetTheory.Formula.eval_orderedPair,cons_zero,cons_succ]

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_SparseCohenRealName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SparseCohenRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop
open InternalCohen (bitSet realNameFormula eval_realNameFormula)

theorem mem_realNameCode (f z : ZFSet.{0}) : z ∈ realNameCode f ↔
    ∃ q ∈ poset, ∃ n ∈ ZFSet.omega, ∃ v,
      ZFSet.pair n v ∈ f ∧ ZFSet.pair n (bitSet true) ∈ q ∧ z = ZFSet.pair v q := by
  rw [realNameCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,hq,n,hn,v,_,hv,hbit,hz⟩; exact ⟨q,hq,n,hn,v,hv,hbit,hz⟩
  · rintro ⟨q,hq,n,hn,v,hv,hbit,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,q,hq,rfl⟩,q,hq,n,hn,v,hr,hv,hbit,rfl⟩

theorem realNameCode_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    {f : ZFSet.{0}} (hf : f ∈ M) : realNameCode f ∈ M := by
  have hc := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  have hω := sourceT_omega_mem M hM hT
  have hr := iterUnion_mem M hM hT.union hf 2
  have h1 : bitSet true ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
  let e := cons poset (cons ZFSet.omega (cons f (cons (iterUnion 2 f) (cons (bitSet true) (fun _ => poset)))))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|_|_|_|i <;> assumption
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded realNameFormula e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hr hc)
  have heq : ZFSet.sep (fun z => realNameFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) poset) = realNameCode f := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_sep,realNameCode]
    exact and_congr_right (fun _ => eval_realNameFormula _ _ _ _ _ _)
  exact heq ▸ hs

theorem encode_realName (d r f : ZFSet.{0}) (hω : ZFSet.omega ⊆ d)
    (hf : CheckGraph d r f (label poset ⊤)) :
    realName.encode (label poset) = realNameCode f := by
  have hfr : TransitiveNameModel.FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,mem_realNameCode]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hz⟩
    have hn := (mem_omega (natSet n)).mpr ⟨n,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 _ (hω hn)
    have he := hf.correct _ (hω hn) v hv hfv
    refine ⟨label poset q,label_mem _ _,natSet n,hn,v,hfv,hbit,?_⟩
    simpa only [realName,encode_check,he] using hz.symm
  · rintro ⟨q,hq,n,hn,v,hfv,hbit,hz⟩
    obtain ⟨k,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨q,rfl⟩ := label_surjective poset hq
    have he := hf.correct _ (hω hn) v (hfr.value_mem hfv) hfv
    exact ⟨⟨(q,k),hbit⟩,by simpa only [realName,encode_check,he] using hz.symm⟩

theorem realName_internal (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    realName.encode (label poset) ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨d,hdM,hd,hωd⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hω
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hT.powerSet hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label poset ⊤) hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
    hdM hqM (hM _ (CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)) _ (label_mem poset ⊤)) hd hq ZFSet.omega hωd
  have hsub : ZFSet.omega ⊆ hull d q ZFSet.omega := fun x hx =>
    hull_transitive d q ZFSet.omega hd _ (self_mem_hull d q hωd) x hx
  rw [encode_realName _ _ f hsub hfg]
  exact realNameCode_mem M hM hT hf

end TuringRigidity.SparseCohenRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnRealName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
attribute [local instance] InternalCollapse.order CohenNiceNameConstruction.cohenTop
open InternalCohen (bitSet)

theorem eval_realNameFormula (z c f r one C a : ZFSet.{0}) (e : ℕ → ZFSet.{0}) :
    realNameFormula.Eval
      (cons z (cons c (cons ZFSet.omega (cons f (cons r (cons one (cons C (cons a e)))))))) ↔
      ∃ q ∈ c, ∃ n ∈ ZFSet.omega, ∃ v ∈ r, ∃ x ∈ C,
        ZFSet.pair n v ∈ f ∧ x = ZFSet.pair a n ∧
        ZFSet.pair x one ∈ q ∧ z = ZFSet.pair v q := by
  simp only [realNameFormula,BoundedSetTheory.Formula.Eval,BoundedSetTheory.Formula.eval_pairMem,
    BoundedSetTheory.Formula.eval_orderedPair,cons_zero,cons_succ]

theorem mem_realNameCode (K a f z : ZFSet.{0}) (ha : a ∈ K) : z ∈ realNameCode K a f ↔
    ∃ q ∈ poset K, ∃ n ∈ ZFSet.omega, ∃ v,
      ZFSet.pair n v ∈ f ∧ ZFSet.pair (ZFSet.pair a n) (bitSet true) ∈ q ∧ z = ZFSet.pair v q := by
  rw [realNameCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,hq,n,hn,v,_,x,_,hv,rfl,hbit,hz⟩; exact ⟨q,hq,n,hn,v,hv,hbit,hz⟩
  · rintro ⟨q,hq,n,hn,v,hv,hbit,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,q,hq,rfl⟩,q,hq,n,hn,v,hr,ZFSet.pair a n,ZFSet.pair_mem_prod.mpr ⟨ha,hn⟩,hv,rfl,hbit,rfl⟩

theorem realNameCode_mem (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    {f : ZFSet.{0}} (hf : f ∈ M) : realNameCode K a f ∈ M := by
  have hc := (CohenGroundPoset.manyColumn_internal M K hM hT hK).1
  have hω := sourceT_omega_mem M hM hT
  have hr := iterUnion_mem M hM hT.union hf 2
  have h1 : bitSet true ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hK hω
  have haM := hM K hK a ha
  let e := cons (poset K) (cons ZFSet.omega (cons f (cons (iterUnion 2 f) (cons (bitSet true) (cons (ZFSet.prod K ZFSet.omega) (cons a (fun _ => a)))))))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|_|_|_|_|_|i <;> assumption
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded realNameFormula e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hr hc)
  have heq : ZFSet.sep (fun z => realNameFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) (poset K)) = realNameCode K a f := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_sep,realNameCode]
    exact and_congr_right (fun _ => eval_realNameFormula z (poset K) f (iterUnion 2 f) (bitSet true)
      (ZFSet.prod K ZFSet.omega) a (fun _ => a))
  exact heq ▸ hs

theorem encode_realName (K a d r f : ZFSet.{0}) (ha : a ∈ K) (hω : ZFSet.omega ⊆ d)
    (hf : CheckGraph d r f (label (poset K) ⊤)) :
    (realName K a).encode (label (poset K)) = realNameCode K a f := by
  have hfr : TransitiveNameModel.FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,mem_realNameCode K a f z ha]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hz⟩
    have hn := (mem_omega (natSet n)).mpr ⟨n,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 _ (hω hn)
    have he := hf.correct _ (hω hn) v hv hfv
    refine ⟨label (poset K) q,label_mem _ _,natSet n,hn,v,hfv,hbit,?_⟩
    simpa only [realName,encode_check,he] using hz.symm
  · rintro ⟨q,hq,n,hn,v,hfv,hbit,hz⟩
    obtain ⟨k,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨q,rfl⟩ := label_surjective (poset K) hq
    have he := hf.correct _ (hω hn) v (hfr.value_mem hfv) hfv
    exact ⟨⟨(q,k),hbit⟩,by simpa only [realName,encode_check,he] using hz.symm⟩

theorem realName_internal (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K) :
    (realName K a).encode (label (poset K)) ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨d,hdM,hd,hωd⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hω
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hT.powerSet hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label (poset K) ⊤) hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
    hdM hqM (hM _ ((CohenGroundPoset.manyColumn_internal M K hM hT hK).1) _ (label_mem (poset K) ⊤)) hd hq ZFSet.omega hωd
  have hsub : ZFSet.omega ⊆ hull d q ZFSet.omega := fun x hx =>
    hull_transitive d q ZFSet.omega hd _ (self_mem_hull d q hωd) x hx
  rw [encode_realName K a _ _ f ha hsub hfg]
  exact realNameCode_mem M K a hM hT hK ha hf

end TuringRigidity.CohenColumnRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenRestriction
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode CohenGroundPoset
open InternalCohen (alphabet)

theorem restrictionFormula_spec (B V p q : ℕ) (e : ℕ → ZFSet.{0}) (hV : e V = alphabet) :
    (restrictionFormula B V p q).Eval e ↔ e q = restrict (e B) (e p) := by
  simp only [restrictionFormula,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,hV]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro z
    exact ⟨fun hz => ZFSet.mem_sep.mpr ⟨hsub hz,(h z (hsub hz)).mp hz⟩,
      fun hz => (h z (ZFSet.mem_sep.mp hz).1).mpr (ZFSet.mem_sep.mp hz).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hz => (ZFSet.mem_sep.mp hz).1,
      fun z hz => ZFSet.mem_sep.trans (and_iff_right hz)⟩

theorem pair_restrictionGraph (A B p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ restrictionGraph A B ↔
      p ∈ conditions A ∧ q ∈ conditions B ∧ q = restrict B p := by
  simp only [restrictionGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,hr⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,hr⟩
  · rintro ⟨hp,hq,hr⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,hr⟩

theorem restrictionGraph_mem (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) : restrictionGraph A B ∈ M := by
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  let e := cons (conditions A) (cons (conditions B) (cons B (fun _ => alphabet)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact hcA; exact hcB; exact hB; exact InternalCohen.alphabet_mem M hM hT
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (restrictionFormula 5 6 1 0)))) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hcB)
  have hs (z p q : ZFSet.{0}) :=
    restrictionFormula_spec 5 6 1 0 (cons q (cons p (cons z e))) rfl
  simpa only [restrictionGraph,Formula.Eval,Formula.eval_orderedPair,
    hs,cons_zero,cons_succ,e] using hh

end TuringRigidity.InternalCohenRestriction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenPartition
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode CohenGroundPoset
open InternalCohenRestriction
open InternalCohen (alphabet)

theorem complement_mem (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) : A \ B ∈ M := by
  simpa only [ZFSet.sep_notMem,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.neg (.member 0 1))
      (fun _ => B) (fun _ => hB) hA

end TuringRigidity.InternalCohenPartition

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenFactor
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenFactor
open TransitiveNameModel BoundedSetTheory CohenGroundPoset InternalCohenRestriction InternalCohenPartition
open InternalCohen (alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem factorGraph_pair (A B p q r : ZFSet.{0}) :
    ZFSet.pair p (ZFSet.pair q r) ∈ factorGraph A B ↔
      p ∈ conditions A ∧ q ∈ conditions B ∧ r ∈ conditions (A \ B) ∧
        q = restrict B p ∧ r = restrict (A \ B) p := by
  simp only [factorGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,r',hr,he,hs⟩
    obtain ⟨hpEq,hqrEq⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hqEq,hrEq⟩ := ZFSet.pair_inj.mp hqrEq
    subst p'; subst q'; subst r'
    exact ⟨hp,hq,hr,hs⟩
  · rintro ⟨hp,hq,hr,hs⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,ZFSet.pair_mem_prod.mpr ⟨hq,hr⟩⟩,
      p,hp,q,hq,r,hr,rfl,hs⟩

theorem factorGraph_is_iso_graph (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A))
    (q : Conditions (conditions B)) (r : Conditions (conditions (A \ B))) :
    ZFSet.pair (label _ p) (ZFSet.pair (label _ q) (label _ r)) ∈ factorGraph A B ↔
      factorIso A B hBA p = (q,r) := by
  rw [factorGraph_pair]
  simp only [label_mem,true_and]
  constructor
  · intro h
    apply Prod.ext <;> apply label_injective
    · exact (label_project A B hBA p).trans h.1.symm
    · exact (label_project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p).trans h.2.symm
  · intro h
    have hq := congrArg (fun t => label (conditions B) t.1) h
    have hr := congrArg (fun t => label (conditions (A \ B)) t.2) h
    exact ⟨hq.symm.trans (label_project A B hBA p),hr.symm.trans (label_project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p)⟩

theorem factor_internal (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) :
    conditions B ∈ M ∧ conditions (A \ B) ∈ M ∧
      InternalCollapse.orderSet (conditions B) ∈ M ∧
      InternalCollapse.orderSet (conditions (A \ B)) ∈ M ∧ factorGraph A B ∈ M := by
  have hD := complement_mem M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  have hcD := conditions_mem M (A \ B) hM hT hD
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcB hcD
  refine ⟨hcB,hcD,InternalCollapse.orderSet_mem M hM hT hcB,
    InternalCollapse.orderSet_mem M hM hT hcD,?_⟩
  let e := cons (conditions A) (cons (conditions B) (cons (conditions (A \ B))
    (cons (productCode A B) (cons B (cons (A \ B) (fun _ => alphabet))))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|i
    exact hcA; exact hcB; exact hcD; exact hprod; exact hB; exact hD
    exact InternalCohen.alphabet_mem M hM hT
  let φ : Formula := .existsMem 1 (.existsMem 3 (.existsMem 5
    (.existsMem 7 (.conj (.orderedPair 0 2 1) (.conj (.orderedPair 4 3 0)
      (.conj (restrictionFormula 9 11 3 2) (restrictionFormula 10 11 3 1)))))))
  have hs₁ (z p q r t : ZFSet.{0}) := restrictionFormula_spec 9 11 3 2
    (cons t (cons r (cons q (cons p (cons z e))))) rfl
  have hs₂ (z p q r t : ZFSet.{0}) := restrictionFormula_spec 10 11 3 1
    (cons t (cons r (cons q (cons p (cons z e))))) rfl
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      ∃ p ∈ conditions A, ∃ q ∈ conditions B, ∃ r ∈ conditions (A \ B),
        z = ZFSet.pair p (ZFSet.pair q r) ∧ q = restrict B p ∧ r = restrict (A \ B) p := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,hs₁,hs₂,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨p,hp,q,hq,r,hr,t,_,ht,hz,hs⟩
      exact ⟨p,hp,q,hq,r,hr,ht ▸ hz,hs⟩
    · rintro ⟨p,hp,q,hq,r,hr,hz,hs⟩
      exact ⟨p,hp,q,hq,r,hr,ZFSet.pair q r,ZFSet.pair_mem_prod.mpr ⟨hq,hr⟩,rfl,hz,hs⟩
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hprod)
  simpa only [factorGraph,hφ,productCode] using hh

end TuringRigidity.InternalCohenFactor

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenProjectedGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenProjectedGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing AutomorphismName
open CohenGroundPoset InternalCohenRestriction InternalCohenPartition InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem mem_projected (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (q : Conditions (conditions B)) :
    q ∈ (projected A B hBA G).carrier ↔ ∃ p ∈ G.carrier, project A B hBA p = q := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨(factorIso A B hBA).symm (q,r),hr,?_⟩
    exact congrArg Prod.fst ((factorIso A B hBA).apply_symm_apply (q,r))
  · rintro ⟨p,hp,rfl⟩
    refine ⟨(factorIso A B hBA p).2,?_⟩
    change (factorIso A B hBA).symm (factorIso A B hBA p) ∈ G.carrier
    simpa using hp

theorem densePreimage_mem (M A B D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hD : D ∈ M) : densePreimage A B D ∈ M := by
  have hc := conditions_mem M B hM hT hB
  have hR := restrictionGraph_mem M A B hM hT hA hB
  let e := cons (conditions B) (cons (restrictionGraph A B) (fun _ => D))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hc; exact hR; exact hD
  simpa only [densePreimage,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.pairMem 1 0 3) (.member 0 4))) e he
      (conditions_mem M A hM hT hA)

theorem label_densePreimage (A B D : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A)) :
    label _ p ∈ densePreimage A B D ↔ label _ (project A B hBA p) ∈ D := by
  rw [densePreimage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,_,hq,hqD⟩
    have he := ((pair_restrictionGraph A B _ q).mp hq).2.2
    rw [label_project,←he]; exact hqD
  · intro h
    exact ⟨label_mem _ p,label _ (project A B hBA p),label_mem _ _,
      (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩,h⟩

theorem densePreimage_dense (A B D : ZFSet.{0}) (hBA : B ⊆ A)
    (hD : Dense {q : Conditions (conditions B) | label _ q ∈ D}) :
    Dense {p : Conditions (conditions A) | label _ p ∈ densePreimage A B D} := by
  intro p
  let e := factorIso A B hBA
  obtain ⟨q,hq,hqD⟩ := hD (e p).1
  let r := e.symm (q,(e p).2)
  have hr : e r = (q,(e p).2) := e.apply_symm_apply _
  refine ⟨r,?_,?_⟩
  · apply e.le_iff_le.mp
    rw [hr]
    exact ⟨hq,le_rfl⟩
  · apply (label_densePreimage A B D hBA r).mpr
    have he := congrArg Prod.fst hr
    change project A B hBA r = q at he
    rw [he]; exact hqD

theorem projected_groundGeneric (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (projected A B hBA G) := by
  intro D hD hd
  obtain ⟨p,hp,hpD⟩ := hG (densePreimage A B D) (densePreimage_mem M A B D hM hT hA hB hD)
    (densePreimage_dense A B D hBA hd)
  exact ⟨project A B hBA p,(mem_projected A B hBA G _).mpr ⟨p,hp,rfl⟩,
    (label_densePreimage A B D hBA p).mp hpD⟩

theorem projected_contains (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) {p : Conditions (conditions A)}
    (hp : p ∈ G.carrier) : project A B hBA p ∈ (projected A B hBA G).carrier :=
  (mem_projected A B hBA G _).mpr ⟨p,hp,rfl⟩

end TuringRigidity.InternalCohenProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_SparseCohenFilter
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SparseCohenFilter
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCollapse
open InternalCohen (alphabet bitSet mem_alphabet bitSet_injective)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem finite_covered {c : ZFSet.{0}} (G : GenericFilter (Conditions c))
    (S : Set ZFSet.{0}) (hS : S.Finite)
    (hsub : ∀ z ∈ S, z ∈ unionGraph G) :
    ∃ p ∈ G.carrier, ∀ z ∈ S, z ∈ label c p := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    obtain ⟨p,hp⟩ := G.nonempty
    exact ⟨p,hp,fun _ h => False.elim h⟩
  | @insert z S hz hS ih =>
    obtain ⟨p,hp,hpS⟩ := ih (fun x hx => hsub x (Or.inr hx))
    obtain ⟨q,hq,hqz⟩ := (mem_unionGraph G z).mp (hsub z (Or.inl rfl))
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    refine ⟨r,hr,fun x hx => ?_⟩
    rcases hx with rfl|hx
    · exact hrq hqz
    · exact hrp (hpS x hx)

theorem mem_filter_iff_subset_union (A : ZFSet.{0})
    (G : GenericFilter (Conditions (conditions A)))
    (p : Conditions (conditions A)) :
    p ∈ G.carrier ↔ label _ p ⊆ unionGraph G := by
  constructor
  · intro hp z hz
    exact (mem_unionGraph G z).mpr ⟨p,hp,hz⟩
  · intro hsub
    have hfin := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions A _).mp (label_mem _ p)).1).2
    obtain ⟨q,hq,hqp⟩ := finite_covered G (label _ p) hfin (fun z hz => hsub hz)
    exact G.upper hqp hq

theorem union_real (G : GenericFilter (Conditions (conditions ZFSet.omega)))
    (hfun : FunctionGraph ZFSet.omega alphabet (unionGraph G)) :
    ∃ A : Oracle, ∀ n b,
      ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b := by
  classical
  have hex (n : ℕ) : ∃ b : Bool, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G := by
    obtain ⟨b,hb,hnb,_⟩ := hfun.2 _ ((mem_omega _).mpr ⟨n,rfl⟩)
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    exact ⟨b,hnb⟩
  let A : Oracle := fun n => (hex n).choose
  refine ⟨A,fun n b => ⟨fun hb => ?_,fun he => he ▸ (hex n).choose_spec⟩⟩
  obtain ⟨v,hv,hnv,huniq⟩ := hfun.2 _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact bitSet_injective ((huniq _ ((mem_alphabet _).mpr ⟨A n,rfl⟩)
    (hex n).choose_spec).trans (huniq _ ((mem_alphabet _).mpr ⟨b,rfl⟩) hb).symm)

theorem mem_filter_iff_agrees (G : GenericFilter (Conditions (conditions ZFSet.omega)))
    (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b)
    (p : Conditions (conditions ZFSet.omega)) :
    p ∈ G.carrier ↔ ∀ n b,
      ZFSet.pair (natSet n) (bitSet b) ∈ label _ p → A n = b := by
  rw [mem_filter_iff_subset_union]
  constructor
  · intro hp n b hb
    exact (hA n b).mp (hp hb)
  · intro hp z hz
    have hsub := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions ZFSet.omega _).mp (label_mem _ p)).1).1
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
    obtain ⟨n,rfl⟩ := (mem_omega _).mp hx
    obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
    exact (hA n b).mpr (hp n b hz)

end TuringRigidity.SparseCohenFilter

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnRealValue
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
open InternalCohen (bitSet alphabet mem_alphabet bitSet_injective)
open CohenGroundPoset InternalCohenProjectedGeneric InternalCohenRestriction InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem union_real (K a : ZFSet.{0}) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K)))
    (hfun : FunctionGraph (ZFSet.prod K ZFSet.omega) alphabet (unionGraph G)) :
    ∃ A : Oracle, ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b := by
  classical
  have hn (n : ℕ) : ZFSet.pair a (natSet n) ∈ ZFSet.prod K ZFSet.omega :=
    ZFSet.pair_mem_prod.mpr ⟨ha,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hex (n : ℕ) : ∃ b : Bool,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G := by
    obtain ⟨b,hb,hnb,_⟩ := hfun.2 _ (hn n)
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    exact ⟨b,hnb⟩
  let A : Oracle := fun n => (hex n).choose
  refine ⟨A,fun n b => ⟨fun hb => ?_,fun he => he ▸ (hex n).choose_spec⟩⟩
  obtain ⟨v,hv,hnv,huniq⟩ := hfun.2 _ (hn n)
  exact bitSet_injective ((huniq _ ((mem_alphabet _).mpr ⟨A n,rfl⟩)
    (hex n).choose_spec).trans (huniq _ ((mem_alphabet _).mpr ⟨b,rfl⟩) hb).symm)

theorem val_realName (K a : ZFSet.{0}) (G : GenericFilter (Conditions (poset K)))
    (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) :
    (realName K a).val G.carrier = realCode A := by
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions (poset K)) ∈ G.carrier := G.upper le_top hp
  apply ZFSet.ext; intro z
  rw [realName,Name.mem_val]
  simp only [Name.val_check _ ht]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hq,rfl⟩
    exact (natSet_mem_realCode A n).mpr ((hA n true).mp
      ((mem_unionGraph G _).mpr ⟨q,hq,hbit⟩))
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_omega _).mp (realCode_subset A hz)
    obtain ⟨q,hq,hbit⟩ := (mem_unionGraph G _).mp
      ((hA n true).mpr ((natSet_mem_realCode A n).mp hz))
    exact ⟨⟨(q,n),hbit⟩,hq,rfl⟩

theorem generic_real_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, (realName K a).val G.carrier = realCode A ∧
      (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      realCode A ∈ genericExtensionSet M (poset K) G.carrier := by
  obtain ⟨A,hA⟩ := union_real K a ha G (CohenGenericUnion.manyColumn_union M K hM hT hK G hG).2
  have hv := val_realName K a G A hA
  exact ⟨A,hv,hA,(mem_extensionSet M (poset K) _ _).mpr
    ⟨realName K a,realName_internal M K a hM hT hK ha,hv⟩⟩

theorem singleton_filter_iff (a : ZFSet.{0})
    (G : GenericFilter (Conditions (poset {a}))) (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b)
    (p : Conditions (poset {a})) :
    p ∈ G.carrier ↔ ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → A n = b := by
  rw [SparseCohenFilter.mem_filter_iff_subset_union]
  constructor
  · intro hp n b hb
    exact (hA n b).mp (hp hb)
  · intro hp z hz
    have hsub := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions (ZFSet.prod {a} ZFSet.omega) _).mp (label_mem _ p)).1).1
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
    obtain ⟨a',ha',n,hn,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain rfl := ZFSet.mem_singleton.mp ha'
    obtain ⟨n,rfl⟩ := (mem_omega _).mp hn
    obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
    exact (hA n b).mpr (hp n b hz)

theorem pair_mem_projected_union (C B : ZFSet.{0}) (hBC : B ⊆ C)
    (G : GenericFilter (Conditions (conditions C))) (x : ZFSet.{0}) (hx : x ∈ B) (b : Bool) :
    ZFSet.pair x (bitSet b) ∈ unionGraph (projected C B hBC G) ↔
      ZFSet.pair x (bitSet b) ∈ unionGraph G := by
  rw [InternalCollapse.mem_unionGraph,InternalCollapse.mem_unionGraph]
  constructor
  · rintro ⟨q,hq,hbit⟩
    obtain ⟨p,hp,rfl⟩ := (mem_projected C B hBC G q).mp hq
    rw [label_project,pair_restrict] at hbit
    exact ⟨p,hp,hbit.1⟩
  · rintro ⟨p,hp,hbit⟩
    refine ⟨project C B hBC p,projected_contains C B hBC G hp,?_⟩
    rw [label_project,pair_restrict]
    exact ⟨hbit,hx,(mem_alphabet _).mpr ⟨b,rfl⟩⟩

theorem projected_real_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G) :
    let C := ZFSet.prod K ZFSet.omega
    let B := ZFSet.prod {a} ZFSet.omega
    let hBC := singleton_coordinates_subset K a ha
    ∃ A : Oracle,
      (realName {a} a).val (projected C B hBC G).carrier = realCode A ∧
      (realName K a).val G.carrier = realCode A ∧
      (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      (∀ p : Conditions (poset {a}), p ∈ (projected C B hBC G).carrier ↔ ∀ n b,
        ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → A n = b) := by
  intro C B hBC
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  obtain ⟨A,hv,hA,_⟩ := generic_real_value M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) (projected C B hBC G)
    (projected_groundGeneric M C B hM hT hC hB hBC G hG)
  have hfull (n : ℕ) (b : Bool) :
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b := by
    rw [←pair_mem_projected_union C B hBC G _
      (ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,(mem_omega _).mpr ⟨n,rfl⟩⟩) b]
    exact hA n b
  exact ⟨A,hv,val_realName K a G A hfull,hfull,
    singleton_filter_iff a (projected C B hBC G) A hA⟩

end TuringRigidity.CohenColumnRealName

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableClosure
open TransitiveNameModel BoundedSetTheory

theorem constant_graph (A : ZFSet.{0}) :
    orbitGraph (fun _ => A) = ZFSet.prod ZFSet.omega {A} := by
  apply ZFSet.ext; intro z
  rw [mem_orbitGraph,ZFSet.mem_prod]
  constructor
  · rintro ⟨n,rfl⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,A,ZFSet.mem_singleton.mpr rfl,rfl⟩
  · rintro ⟨n,hn,x,hx,rfl⟩
    obtain rfl := ZFSet.mem_singleton.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,rfl⟩

theorem finite_countable (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hfin : (A : Set ZFSet.{0}).Finite) (hne : ∃ x, x ∈ A) :
    InternallyCountable M A := by
  apply InternalCountableFiniteUnion.internally_countable_union M A hM hT hA (fun _ => A)
    (fun _ => (InternalFiniteSubsets.mem_finiteSubsets_iff A A).mpr ⟨fun _ h => h,hfin⟩)
    _ (fun x hx => ⟨0,hx⟩) hne
  rw [constant_graph]
  exact product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (sourceT_omega_mem M hM hT) (singleton_mem M hM hT.pairing hA)

theorem singleton_countable (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) : InternallyCountable M ({a} : ZFSet.{0}) := by
  apply finite_countable M {a} hM hT (singleton_mem M hM hT.pairing ha)
  · simpa only [ZFSet.coe_singleton] using Set.finite_singleton a
  · exact ⟨a,ZFSet.mem_singleton.mpr rfl⟩

end TuringRigidity.InternalCountableClosure

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductConditions
open TransitiveNameModel BoundedSetTheory
attribute [local instance] InternalCollapse.order

theorem code_mem (M p s : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hp : p ∈ M) (hs : s ∈ M) : code p s ∈ M := by
  have hn (n : ℕ) : natSet n ∈ M :=
    hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact binary_union_mem M hM hT.pairing hT.union
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (singleton_mem M hM hT.pairing (hn 0)) hp)
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (singleton_mem M hM hT.pairing (hn 1)) hs)

theorem codeFormula_spec (p s z z0 z1 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) :
    (codeFormula p s z z0 z1).Eval e ↔ e z = code (e p) (e s) := by
  simp only [codeFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_disj,
    Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,h0,h1]
  constructor
  · rintro ⟨ha,hb,hc⟩
    apply ZFSet.ext; intro x
    exact ⟨fun hx => (mem_code _ _ _).mpr (ha x hx),fun hx =>
      ((mem_code _ _ _).mp hx).elim (fun ⟨y,hy,he⟩ => he ▸ hb y hy)
        (fun ⟨y,hy,he⟩ => he ▸ hc y hy)⟩
  · intro h; rw [h]
    exact ⟨fun x hx => (mem_code _ _ _).mp hx,
      fun x hx => (left_mem _ _ _).mpr hx,fun x hx => (right_mem _ _ _).mpr hx⟩

theorem code_bounded (a b p s : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) :
    code p s ⊆ bound a b :=
  (code_subset _ _ _ _).mpr ⟨fun _ hx => ZFSet.mem_sUnion.mpr ⟨p,hp,hx⟩,
    fun _ hx => ZFSet.mem_sUnion.mpr ⟨s,hs,hx⟩⟩

theorem internal_product (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) :
    ∃ c ∈ M, (∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s) ∧
      ∃ g ∈ M, FunctionGraph (ZFSet.prod a b) c g ∧
        (∀ p ∈ a, ∀ s ∈ b, ∀ z, ZFSet.pair (ZFSet.pair p s) z ∈ g ↔ z = code p s) ∧
        (∀ z ∈ c, ∃ x ∈ ZFSet.prod a b, ZFSet.pair x z ∈ g) := by
  have hbound := code_mem M _ _ hM hT (union_mem M hM hT.union ha) (union_mem M hM hT.union hb)
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hbound
  have hcode (p s : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) : code p s ∈ Q :=
    (hQdef _).mpr ⟨code_mem M p s hM hT (hM a ha p hp) (hM b hb s hs),code_bounded a b p s hp hs⟩
  let e := cons a (cons b (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact ha; exact hb
    all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  let c := Q.sep (fun z => ∃ p ∈ a, ∃ s ∈ b, z = code p s)
  have hsepCode (left right value : ZFSet.{0}) :
      (codeFormula 1 0 2 5 6).Eval (cons right (cons left (cons value e))) ↔
        value = code left right :=
    codeFormula_spec 1 0 2 5 6 _ rfl rfl
  have hc : c ∈ M := by
    simpa only [c,Formula.Eval,hsepCode,
      cons_zero,cons_succ,e] using
      sep_mem M hM hT.separation.finitePrefix.bounded
        (.existsMem 1 (.existsMem 3 (codeFormula 1 0 2 5 6))) e he hQ
  have hcs (z : ZFSet.{0}) : z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s := by
    change (z ∈ Q.sep _) ↔ _
    rw [ZFSet.mem_sep]
    exact ⟨And.right,fun h@⟨p,hp,s,hs,hz⟩ => ⟨hz ▸ hcode p s hp hs,h⟩⟩
  let v := cons (ZFSet.prod a b) (cons c e)
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb
  have hv : ∀ i, v i ∈ M := by
    intro i; rcases i with _|_|i; exact hprod; exact hc; exact he i
  have hgraphCode (left right value point entry : ZFSet.{0}) :
      (codeFormula 1 0 2 9 10).Eval
        (cons right (cons left (cons value (cons point (cons entry v))))) ↔
          value = code left right :=
    codeFormula_spec 1 0 2 9 10 _ rfl rfl
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.existsMem 7 (.conj (.orderedPair 3 1 0) (codeFormula 1 0 2 9 10))))))
  let g := (ZFSet.prod (ZFSet.prod a b) c).sep (fun z => φ.Eval (cons z v))
  have hg : g ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ v hv
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hprod hc)
  have hgs (p s z : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) :
      ZFSet.pair (ZFSet.pair p s) z ∈ g ↔ z = code p s := by
    simp only [g,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      hgraphCode,cons_zero,cons_succ,v,e]
    constructor
    · rintro ⟨_,x,_,y,_,hxy,p',_,s',_,hx,hy⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hx
      exact hy
    · intro hz
      have hzc := (hcs z).mpr ⟨p,hp,s,hs,hz⟩
      have hps := ZFSet.pair_mem_prod.mpr ⟨hp,hs⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hps,hzc⟩,_,hps,z,hzc,rfl,p,hp,s,hs,rfl,hz⟩
  refine ⟨c,hc,hcs,g,hg,⟨?_,?_⟩,(fun p hp s hs z => hgs p s z hp hs),?_⟩
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    obtain ⟨p,hp,s,hs,rfl⟩ := ZFSet.mem_prod.mp hx
    exact ⟨code p s,(hcs _).mpr ⟨p,hp,s,hs,rfl⟩,(hgs p s _ hp hs).mpr rfl,
      fun y _ hy => (hgs p s y hp hs).mp hy⟩
  · intro z hz
    obtain ⟨p,hp,s,hs,hz⟩ := (hcs z).mp hz
    exact ⟨ZFSet.pair p s,ZFSet.pair_mem_prod.mpr ⟨hp,hs⟩,(hgs p s z hp hs).mpr hz⟩

end TuringRigidity.TaggedProductConditions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open RegularTreeRecovery InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem extension_properties (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let N := genericExtensionSet M c G.carrier
    Transitive N ∧ SourceT N ∧ M ⊆ N ∧ genericFilterSet c G.carrier ∈ N := by
  let _ : Top (Conditions c) := ⟨Classical.choose G.nonempty⟩
  have ht : ⊤ ∈ G.carrier := Classical.choose_spec G.nonempty
  exact ⟨genericExtensionSet_transitive M c hM G.carrier,
    extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
      (InternalCollapse.orderSet_pair c) G hG ht,
    ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht,
    genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht⟩

end TuringRigidity.RegularTreeExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalDenseInclusion
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalDenseInclusion
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem embed_mem_push (a b : ZFSet.{0}) (hab : a ⊆ b)
    (G : GenericFilter (Conditions a)) (p : Conditions a) :
    embed a b hab p ∈ (push a b hab G).carrier ↔ p ∈ G.carrier := by
  constructor
  · rintro ⟨q,hq,hqp⟩; exact G.upper ((embed_le_iff a b hab q p).mp hqp) hq
  · intro hp; exact ⟨p,hp,le_rfl⟩

theorem densePull_mem (M a b D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M) : densePull a b D ∈ M := by
  let e := cons b (fun _ => D)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hb; exact hD
  simpa only [densePull,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.member 0 3) (.subset 0 1))) e he ha

theorem push_ground_generic (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hab : a ⊆ b)
    (hd : ∀ q ∈ b, ∃ p ∈ a, q ⊆ p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (push a b hab G) := by
  intro D hD hden
  have hpull : Dense {p : Conditions a | label a p ∈ densePull a b D} := by
    intro p
    obtain ⟨q,hqp,hqD⟩ := hden (embed a b hab p)
    obtain ⟨r,hr,hqr⟩ := hd (label b q) (label_mem b q)
    obtain ⟨r,rfl⟩ := label_surjective a hr
    have hpr : label a p ⊆ label a r :=
      fun z hz => hqr (hqp ((label_embed a b hab p).symm ▸ hz))
    exact ⟨r,hpr,ZFSet.mem_sep.mpr ⟨label_mem a r,label b q,label_mem b q,hqD,hqr⟩⟩
  obtain ⟨p,hp,hpD⟩ := hG (densePull a b D) (densePull_mem M a b D hM hT ha hb hD) hpull
  obtain ⟨_,q,hqb,hqD,hqp⟩ := ZFSet.mem_sep.mp hpD
  obtain ⟨q,rfl⟩ := label_surjective b hqb
  exact ⟨q,⟨p,hp,by change label b q ⊆ label b (embed a b hab p); rwa [label_embed]⟩,hqD⟩

end TuringRigidity.InternalDenseInclusion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPrefixDensity
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenPrefixDensity
open TransitiveNameModel BoundedSetTheory InternalCohen CohenConditionCode InternalFiniteSubsets
attribute [local instance] InternalCollapse.order

theorem condition_extends_prefix (q : ZFSet.{0})
    (hq : q ∈ CohenGroundPoset.conditions ZFSet.omega) :
    ∃ s : List Bool, q ⊆ wordCode s := by
  classical
  obtain ⟨p,rfl⟩ := (isCondition_iff_graph _ q).mp ((CohenGroundPoset.mem_conditions _ _).mp hq)
  let f (n : ℕ) : Conditions ZFSet.omega :=
    equivShrink _ ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hfl (n : ℕ) : label ZFSet.omega (f n) = natSet n := by simp [f,label]
  have hfi : Function.Injective f := by
    intro n m h
    exact natSet_injective (by simpa only [hfl] using congrArg (label ZFSet.omega) h)
  have hfin := p.finite.preimage hfi.injOn
  obtain ⟨n,hn⟩ := hfin.bddAbove
  let s := List.ofFn (fun i : Fin (n+1) => (p.val (f i.val)).getD false)
  refine ⟨s,?_⟩
  intro z hz
  obtain ⟨i,b,hib,rfl⟩ := (mem_graph _ p z).mp hz
  obtain ⟨k,hk⟩ := (mem_omega _).mp (label_mem ZFSet.omega i)
  have he : i = f k := label_injective _ (hk.trans (hfl k).symm)
  have hkb : p.val (f k) = some b := he ▸ hib
  have hkn : k < n+1 := Nat.lt_succ_of_le (hn (by
    change p.val (f k) ≠ none
    simp [hkb]))
  rw [he,hfl]
  apply (pair_mem_wordCode s k b).mpr
  refine ⟨by simpa only [s,List.length_ofFn] using hkn,?_⟩
  simp only [s,List.getElem_ofFn,hkb,Option.getD_some]

theorem dense_inclusion : ∀ q ∈ CohenGroundPoset.conditions ZFSet.omega,
    ∃ p ∈ InternalCohen.conditions, q ⊆ p := by
  intro q hq
  obtain ⟨s,hs⟩ := condition_extends_prefix q hq
  exact ⟨wordCode s,(mem_conditions _).mpr ⟨s.length,wordCode_function s⟩,hs⟩

end TuringRigidity.CohenPrefixDensity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_SparseCohenRealValue
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SparseCohenRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem val_realName (G : GenericFilter (Conditions poset)) (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b) :
    realName.val G.carrier = realCode A := by
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions poset) ∈ G.carrier := G.upper le_top hp
  apply ZFSet.ext; intro z
  rw [realName,Name.mem_val]
  simp only [Name.val_check _ ht]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hq,rfl⟩
    exact (natSet_mem_realCode A n).mpr ((hA n true).mp
      ((mem_unionGraph G _).mpr ⟨q,hq,hbit⟩))
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_omega _).mp (realCode_subset A hz)
    obtain ⟨q,hq,hbit⟩ := (mem_unionGraph G _).mp
      ((hA n true).mpr ((natSet_mem_realCode A n).mp hz))
    exact ⟨⟨(q,n),hbit⟩,hq,rfl⟩

theorem generic_real_value (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions poset)) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, realName.val G.carrier = realCode A ∧
      (∀ p : Conditions poset, p ∈ G.carrier ↔ ∀ n b,
        ZFSet.pair (natSet n) (bitSet b) ∈ label poset p → A n = b) ∧
      (∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      realCode A ∈ genericExtensionSet M poset G.carrier := by
  obtain ⟨A,hA⟩ := SparseCohenFilter.union_real G
    (CohenGenericUnion.union_function M ZFSet.omega hM hT
      (sourceT_omega_mem M hM hT) G hG)
  have hv := val_realName G A hA
  exact ⟨A,hv,SparseCohenFilter.mem_filter_iff_agrees G A hA,hA,
    (mem_extensionSet M poset _ _).mpr ⟨realName,realName_internal M hM hT,hv⟩⟩

end TuringRigidity.SparseCohenRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DenseInclusionExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.DenseInclusionExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalDenseInclusion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem upperSet_mem (N b g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hb : b ∈ N) (hg : g ∈ N) : upperSet b g ∈ N := by
  let e := fun _ : ℕ => g
  simpa only [upperSet,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.subset 1 0)) e (fun _ => hg) hb

theorem restrictSet_mem (N a k : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (ha : a ∈ N) (hk : k ∈ N) : restrictSet a k ∈ N := by
  let e := fun _ : ℕ => k
  simpa only [restrictSet,Formula.Eval,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded (.member 0 1) e (fun _ => hk) ha

theorem pushFilterSet_eq (a b : ZFSet.{0}) (hab : a ⊆ b) (G : GenericFilter (Conditions a)) :
    genericFilterSet b (push a b hab G).carrier = upperSet b (genericFilterSet a G.carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨q,⟨p,hp,hpq⟩,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    refine ZFSet.mem_sep.mpr ⟨label_mem b q,label a p,
      (mem_genericFilterSet _ _ _).mpr ⟨p,hp,rfl⟩,?_⟩
    change label b q ⊆ label b (embed a b hab p) at hpq
    rwa [label_embed] at hpq
  · intro hx
    obtain ⟨hxb,p,hpg,hxp⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨q,rfl⟩ := label_surjective b hxb
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ p).mp hpg
    exact (mem_genericFilterSet _ _ _).mpr ⟨q,⟨p,hp,by
      change label b q ⊆ label b (embed a b hab p); rwa [label_embed]⟩,rfl⟩

theorem originalFilterSet_eq (a b : ZFSet.{0}) (hab : a ⊆ b) (G : GenericFilter (Conditions a)) :
    genericFilterSet a G.carrier = restrictSet a (genericFilterSet b (push a b hab G).carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,(mem_genericFilterSet _ _ _).mpr
      ⟨embed a b hab p,(embed_mem_push a b hab G p).mpr hp,label_embed a b hab p⟩⟩
  · intro hx
    obtain ⟨hxa,hxk⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨p,rfl⟩ := label_surjective a hxa
    obtain ⟨q,hq,hqe⟩ := (mem_genericFilterSet _ _ _).mp hxk
    have he : q = embed a b hab p := label_injective b (hqe.trans (label_embed a b hab p).symm)
    exact (mem_genericFilterSet _ _ _).mpr ⟨p,(embed_mem_push a b hab G p).mp (he ▸ hq),rfl⟩

theorem extension_eq (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hab : a ⊆ b)
    (hd : ∀ q ∈ b, ∃ p ∈ a, q ⊆ p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M b (push a b hab G).carrier = genericExtensionSet M a G.carrier := by
  let K := push a b hab G
  have hK := push_ground_generic M a b hM hT ha hb hab hd G hG
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hMV,hkV⟩ := RegularTreeExtension.extension_properties M b hM hT hb K hK
  have hkN : genericFilterSet b K.carrier ∈ genericExtensionSet M a G.carrier := by
    rw [pushFilterSet_eq]
    exact upperSet_mem _ b _ hN hTN (hMN hb) hgN
  have hgV : genericFilterSet a G.carrier ∈ genericExtensionSet M b K.carrier := by
    rw [originalFilterSet_eq a b hab G]
    exact restrictSet_mem _ a _ hV hTV (hMV ha) hkV
  apply ZFSet.ext; intro x
  exact ⟨fun hx => InternalNameEvaluation.extension_subset M _ hN hTN hMN K.carrier hkN hx,
    fun hx => InternalNameEvaluation.extension_subset M _ hV hTV hMV G.carrier hgV hx⟩

end TuringRigidity.DenseInclusionExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalOrderIsoTransport
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalOrderIsoTransport
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem imageSet_mem (M b f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hb : b ∈ M) (hf : f ∈ M) (hg : g ∈ M) : imageSet b f g ∈ M := by
  let e := cons g (fun _ => f)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hg; exact hf
  simpa only [imageSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 1 3)) e he hb

theorem preimageSet_mem (M a f k : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hf : f ∈ M) (hk : k ∈ M) : preimageSet a f k ∈ M := by
  let e := cons k (fun _ => f)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hk; exact hf
  simpa only [preimageSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 1 0 3)) e he ha

theorem map_ground_generic (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (AutomorphismName.mapFilter e G) := by
  intro D hD hd
  let E := DenseInclusionExtension.restrictSet b D
  have hE := DenseInclusionExtension.restrictSet_mem M b D hM hT hb hD
  have hden : Dense {p : Conditions a | label a p ∈ preimageSet a f E} := by
    intro p
    obtain ⟨q,hqp,hqD⟩ := hd (e p)
    refine ⟨e.symm q,by simpa using e.symm.monotone hqp,?_⟩
    exact ZFSet.mem_sep.mpr ⟨label_mem a _,label b q,ZFSet.mem_sep.mpr ⟨label_mem b q,hqD⟩,(he _ _).mpr (e.apply_symm_apply q).symm⟩
  obtain ⟨p,hp,hpD⟩ := hG (preimageSet a f E) (preimageSet_mem M a f E hM hT ha hf hE) hden
  obtain ⟨_,y,hyD,hpy⟩ := ZFSet.mem_sep.mp hpD
  obtain ⟨hyb,hyD⟩ := ZFSet.mem_sep.mp hyD
  obtain ⟨q,rfl⟩ := label_surjective b hyb
  obtain rfl := (he p q).mp hpy
  exact ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,hyD⟩

theorem mapFilterSet_eq (a b f : ZFSet.{0}) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) :
    genericFilterSet b (AutomorphismName.mapFilter e G).carrier =
      imageSet b f (genericFilterSet a G.carrier) := by
  apply ZFSet.ext; intro y
  constructor
  · intro hy
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet _ _ y).mp hy
    exact ZFSet.mem_sep.mpr ⟨label_mem b q,label a (e.symm q),
      (mem_genericFilterSet _ _ _).mpr ⟨e.symm q,hq,rfl⟩,(he _ _).mpr (e.apply_symm_apply q).symm⟩
  · intro hy
    obtain ⟨hyb,x,hx,hxy⟩ := ZFSet.mem_sep.mp hy
    obtain ⟨q,rfl⟩ := label_surjective b hyb
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    obtain rfl := (he p q).mp hxy
    exact (mem_genericFilterSet _ _ _).mpr ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,rfl⟩

theorem originalFilterSet_eq (a b f : ZFSet.{0}) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) :
    genericFilterSet a G.carrier =
      preimageSet a f (genericFilterSet b (AutomorphismName.mapFilter e G).carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,label b (e p),
      (mem_genericFilterSet _ _ _).mpr ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,rfl⟩,
      (he p (e p)).mpr rfl⟩
  · intro hx
    obtain ⟨hxa,y,hy,hxy⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨p,rfl⟩ := label_surjective a hxa
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet _ _ y).mp hy
    obtain rfl := (he p q).mp hxy
    exact (mem_genericFilterSet _ _ _).mpr ⟨p,by simpa [AutomorphismName.mapFilter] using hq,rfl⟩

theorem extension_eq (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M b (AutomorphismName.mapFilter e G).carrier = genericExtensionSet M a G.carrier := by
  let K := AutomorphismName.mapFilter e G
  have hK := map_ground_generic M a b f hM hT ha hb hf e he G hG
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hMV,hkV⟩ := RegularTreeExtension.extension_properties M b hM hT hb K hK
  have hkN : genericFilterSet b K.carrier ∈ genericExtensionSet M a G.carrier := by
    rw [mapFilterSet_eq a b f e he G]
    exact imageSet_mem _ b f _ hN hTN (hMN hb) (hMN hf) hgN
  have hgV : genericFilterSet a G.carrier ∈ genericExtensionSet M b K.carrier := by
    rw [originalFilterSet_eq a b f e he G]
    exact preimageSet_mem _ a f _ hV hTV (hMV ha) (hMV hf) hkV
  apply ZFSet.ext; intro x
  exact ⟨fun hx => InternalNameEvaluation.extension_subset M _ hN hTN hMN K.carrier hkN hx,
    fun hx => InternalNameEvaluation.extension_subset M _ hV hTV hMV G.carrier hgV hx⟩

end TuringRigidity.InternalOrderIsoTransport

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInverseGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalInverseGraph
open TransitiveNameModel BoundedSetTheory

theorem pair_inverse (A B f y x : ZFSet.{0}) :
    ZFSet.pair y x ∈ inverse A B f ↔ y ∈ B ∧ x ∈ A ∧ ZFSet.pair x y ∈ f := by
  simp only [inverse,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y',hy,x',hx,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hy,hx,h⟩
  · rintro ⟨hy,hx,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hy,hx⟩,y,hy,x,hx,rfl,h⟩

theorem inverse_mem (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hf : f ∈ M) : inverse A B f ∈ M := by
  let e := cons B (cons A (fun _ => f))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hB; exact hA; exact hf
  simpa only [inverse,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (.pairMem 0 1 5)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hB hA)

end TuringRigidity.InternalInverseGraph

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalGraphEquiv
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalGraphEquiv
open TransitiveNameModel BoundedSetTheory

theorem graphEquiv_spec (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) (x : Conditions A) (y : Conditions B) :
    ZFSet.pair (label A x) (label B y) ∈ f ↔ y = graphEquiv A B f hf hi hs x := by
  exact ⟨fun h => label_injective B (hf.functional (label_mem A x) h (graphMap_spec A B f hf x)),
    fun h => h.symm ▸ graphMap_spec A B f hf x⟩

end TuringRigidity.InternalGraphEquiv

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenReindex
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenReindex
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem matchesFormula_spec (A B f p q bit : ℕ) (e : ℕ → ZFSet.{0}) (hb : e bit = alphabet) :
    (matchesFormula A B f p q bit).Eval e ↔ Matches (e A) (e B) (e f) (e p) (e q) := by
  simp only [Matches,matchesFormula,Formula.eval_allMem,Formula.eval_imp,Formula.eval_iff,
    Formula.eval_pairMem,cons_zero,cons_succ,hb]

theorem matches_graph_iff (A B f : ZFSet.{0}) (e : Conditions A ≃ Conditions B)
    (he : ∀ x : Conditions A, ∀ y : Conditions B,
      ZFSet.pair (label A x) (label B y) ∈ f ↔ y = e x)
    (p : Condition (Conditions A)) (q : Condition (Conditions B)) :
    Matches A B f (graph A p) (graph B q) ↔ q = CohenCoordinates.reindex e p := by
  constructor
  · intro h
    apply Condition.ext; funext j
    apply Option.ext; intro b
    have hh := h (label A (e.symm j)) (label_mem _ _) (label B j) (label_mem _ _)
      ((he _ _).mpr (e.apply_symm_apply j).symm) (bitSet b) ((mem_alphabet _).mpr ⟨b,rfl⟩)
    rw [pair_mem_graph,pair_mem_graph] at hh
    exact hh.symm
  · rintro rfl x hx y hy hxy b hb
    obtain ⟨i,rfl⟩ := label_surjective A hx
    obtain ⟨j,rfl⟩ := label_surjective B hy
    obtain rfl := (he i j).mp hxy
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    rw [pair_mem_graph,pair_mem_graph]
    change p.val i = some b ↔ p.val (e.symm (e i)) = some b
    rw [e.symm_apply_apply]

theorem pair_reindexGraph (A B f p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ reindexGraph A B f ↔ p ∈ conditions A ∧ q ∈ conditions B ∧ Matches A B f p q := by
  simp only [reindexGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,h⟩
  · rintro ⟨hp,hq,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,h⟩

theorem reindexGraph_mem (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hf : f ∈ M) : reindexGraph A B f ∈ M := by
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  let e := cons (conditions A) (cons (conditions B) (cons A (cons B (cons f (fun _ => alphabet)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact hcA; exact hcB; exact hA; exact hB; exact hf; exact InternalCohen.alphabet_mem M hM hT
  have hmatches (pairValue leftCondition rightCondition : ZFSet.{0}) :
      (matchesFormula 5 6 7 1 0 8).Eval
        (cons rightCondition (cons leftCondition (cons pairValue e))) ↔
        Matches A B f leftCondition rightCondition :=
    matchesFormula_spec 5 6 7 1 0 8 _ rfl
  simpa only [reindexGraph,Formula.Eval,Formula.eval_orderedPair,hmatches,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (matchesFormula 5 6 7 1 0 8)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hcB)

theorem reindexGraph_spec (A B f : ZFSet.{0}) (e : Conditions A ≃ Conditions B)
    (he : ∀ x : Conditions A, ∀ y : Conditions B,
      ZFSet.pair (label A x) (label B y) ∈ f ↔ y = e x)
    (p : Conditions (conditions A)) (q : Conditions (conditions B)) :
    ZFSet.pair (label _ p) (label _ q) ∈ reindexGraph A B f ↔ q = reindexIso A B e p := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv B).surjective q
  rw [pair_reindexGraph]
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv B q) = graph B q := label_encode B q
  rw [and_iff_right (label_mem _ _),and_iff_right (label_mem _ _),hp,hq,matches_graph_iff A B f e he]
  change q = CohenCoordinates.reindex e p ↔
    conditionEquiv B q = conditionEquiv B (CohenCoordinates.reindex e ((conditionEquiv A).symm (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply]
  exact (conditionEquiv B).injective.eq_iff.symm

theorem internal_reindex (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hfM : f ∈ M) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) :
    ∃ e : Conditions (conditions A) ≃o Conditions (conditions B),
      reindexGraph A B f ∈ M ∧
      (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ reindexGraph A B f ↔ q = e p) ∧
      conditions A ∈ M ∧ InternalCollapse.orderSet (conditions A) ∈ M ∧
      conditions B ∈ M ∧ InternalCollapse.orderSet (conditions B) ∈ M := by
  let e := InternalGraphEquiv.graphEquiv A B f hf hi hs
  exact ⟨reindexIso A B e,reindexGraph_mem M A B f hM hT hA hB hfM,
    reindexGraph_spec A B f e (InternalGraphEquiv.graphEquiv_spec A B f hf hi hs),
    (poset_internal M A hM hT hA).1,(poset_internal M A hM hT hA).2,
    poset_internal M B hM hT hB⟩

end TuringRigidity.InternalCohenReindex

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSingletonColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSingletonColumn
open TransitiveNameModel BoundedSetTheory CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem pair_graph (a W u n : ZFSet.{0}) :
    ZFSet.pair u n ∈ graph a W ↔ n ∈ W ∧ u = ZFSet.pair a n := by
  constructor
  · intro h
    obtain ⟨_,v,_,m,hm,he,hv⟩ := ZFSet.mem_sep.mp h
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hm,hv⟩
  · rintro ⟨hn,hu⟩
    have huA : u ∈ ZFSet.prod {a} W := hu ▸ ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hn⟩
    exact ZFSet.mem_sep.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨huA,hn⟩,u,huA,n,hn,rfl,hu⟩

theorem graph_mem (M a W : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hW : W ∈ M) : graph a W ∈ M := by
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hW
  let e := cons (ZFSet.prod {a} W) (cons W (fun _ => a))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hA; exact hW; exact ha
  simpa only [graph,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (.orderedPair 1 5 0)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hW)

theorem graph_function (a W : ZFSet.{0}) : FunctionGraph (ZFSet.prod {a} W) W (graph a W) := by
  refine ⟨fun z hz => ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1,?_⟩
  intro u hu
  obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hu
  have hx_eq : x = a := ZFSet.mem_singleton.mp hx
  subst x
  exact ⟨n,hn,(pair_graph a W _ n).mpr ⟨hn,rfl⟩,fun m _ hm =>
    (ZFSet.pair_inj.mp ((pair_graph a W _ m).mp hm).2).2.symm⟩

theorem graph_injective (a W : ZFSet.{0}) :
    ∀ x ∈ ZFSet.prod {a} W, ∀ x' ∈ ZFSet.prod {a} W, ∀ y ∈ W,
      ZFSet.pair x y ∈ graph a W → ZFSet.pair x' y ∈ graph a W → x = x' := by
  intro x _ x' _ y _ hx hx'
  exact ((pair_graph a W x y).mp hx).2.trans ((pair_graph a W x' y).mp hx').2.symm

theorem graph_onto (a W : ZFSet.{0}) :
    ∀ y ∈ W, ∃ x ∈ ZFSet.prod {a} W, ZFSet.pair x y ∈ graph a W := by
  intro y hy
  exact ⟨ZFSet.pair a y,ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hy⟩,
    (pair_graph a W _ y).mpr ⟨hy,rfl⟩⟩

end TuringRigidity.InternalSingletonColumn

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnPrefixGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenProjectedGeneric AutomorphismName
open InternalCohen (bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem singleton_iso_bits (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) :
    ∃ e : Conditions (poset {a}) ≃o Conditions SparseCohenRealName.poset,
      ∃ f ∈ M,
        (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ f ↔ q = e p) ∧
        ∀ p n b, ZFSet.pair (natSet n) (bitSet b) ∈ label _ (e p) ↔
          ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p := by
  let B := ZFSet.prod {a} ZFSet.omega
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (singleton_mem M hM hT.pairing ha) hω
  obtain ⟨e,hf,he,_⟩ := InternalCohenReindex.internal_reindex M B ZFSet.omega
    (InternalSingletonColumn.graph a ZFSet.omega) hM hT hB hω
    (InternalSingletonColumn.graph_mem M a ZFSet.omega hM hT ha hω)
    (InternalSingletonColumn.graph_function a ZFSet.omega)
    (InternalSingletonColumn.graph_injective a ZFSet.omega)
    (InternalSingletonColumn.graph_onto a ZFSet.omega)
  refine ⟨e,_,hf,he,fun p n b => ?_⟩
  have hn : natSet n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  have hm := ((InternalCohenReindex.pair_reindexGraph B ZFSet.omega
    (InternalSingletonColumn.graph a ZFSet.omega) _ _).mp ((he p (e p)).mpr rfl)).2.2
  exact (hm _ (ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hn⟩) _ hn
    ((InternalSingletonColumn.pair_graph a ZFSet.omega _ _).mpr ⟨hn,rfl⟩)
    (bitSet b) ((mem_alphabet _).mpr ⟨b,rfl⟩)).symm

end TuringRigidity.CohenColumnRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem joint_mem (a b c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (H : GenericFilter (Conditions b))
    (p : Conditions a) (s : Conditions b) :
    productMap a b c hcs (p,s) ∈ (joint a b c hcs G H).carrier ↔
      p ∈ G.carrier ∧ s ∈ H.carrier := by
  change (productIso a b c hcs).symm ((productIso a b c hcs) (p,s)) ∈ (SourceEquationTail.productFilter G H).carrier ↔ _
  rw [OrderIso.symm_apply_apply]
  rfl

theorem sectionSet_mem (M a b D r : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M) (hr : r ∈ M) : sectionSet a b D r ∈ M := by
  let e := cons b (cons D (cons r (cons (natSet 0) (fun _ => natSet 1))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact hb; exact hD; exact hr
    all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hsectionCode (left right value : ZFSet.{0}) :
      (codeFormula 2 1 0 6 7).Eval (cons value (cons right (cons left e))) ↔
        value = code left right :=
    codeFormula_spec 2 1 0 6 7 _ rfl rfl
  simpa only [sectionSet,Formula.Eval,hsectionCode,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (codeFormula 2 1 0 6 7) (.subset 5 1)))) e he ha

theorem fiberSet_mem (N b D g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hb : b ∈ N) (hD : D ∈ N) (hg : g ∈ N) : fiberSet b D g ∈ N := by
  let e := cons g (cons D (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|i
    exact hg; exact hD
    all_goals exact hN _ (sourceT_omega_mem N hN hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hfiberCode (left right value : ZFSet.{0}) :
      (codeFormula 1 2 0 5 6).Eval (cons value (cons left (cons right e))) ↔
        value = code left right :=
    codeFormula_spec 1 2 0 5 6 _ rfl rfl
  simpa only [fiberSet,Formula.Eval,hfiberCode,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (codeFormula 1 2 0 5 6))) e he hb

theorem sectionSet_dense (a b c D : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (hD : Dense {x : Conditions c | label c x ∈ D}) (r : Conditions b) :
    Dense {p : Conditions a | label a p ∈ sectionSet a b D (label b r)} := by
  intro p
  obtain ⟨x,hx,hxD⟩ := hD (productMap a b c hcs (p,r))
  let y := (productIso a b c hcs).symm x
  have hy : y ≤ (p,r) := by
    have hh := (productIso a b c hcs).symm.monotone hx
    change (productIso a b c hcs).symm x ≤ (productIso a b c hcs).symm ((productIso a b c hcs) (p,r)) at hh
    simpa only [OrderIso.symm_apply_apply] using hh
  have hl : label c x = code (label a y.1) (label b y.2) := by
    rw [←label_productMap a b c hcs y]
    exact congrArg (label c) ((productIso a b c hcs).apply_symm_apply x).symm
  exact ⟨y.1,hy.1,ZFSet.mem_sep.mpr ⟨label_mem a y.1,label b y.2,label_mem b y.2,
    label c x,hxD,hl,hy.2⟩⟩

theorem fiberSet_dense (M a b c D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (hd : Dense {x : Conditions c | label c x ∈ D})
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    Dense {r : Conditions b | label b r ∈ fiberSet b D (genericFilterSet a G.carrier)} := by
  intro r
  obtain ⟨p,hp,hpr⟩ := hG (sectionSet a b D (label b r))
    (sectionSet_mem M a b D _ hM hT ha hb hD (hM b hb _ (label_mem b r)))
    (sectionSet_dense a b c D hcs hd r)
  obtain ⟨_,s,hs,z,hz,hzs,hrs⟩ := ZFSet.mem_sep.mp hpr
  obtain ⟨s,rfl⟩ := label_surjective b hs
  exact ⟨s,hrs,ZFSet.mem_sep.mpr ⟨label_mem b s,label a p,
    (mem_genericFilterSet a G.carrier _).mpr ⟨p,hp,rfl⟩,z,hz,hzs⟩⟩

theorem joint_ground_generic (M a b c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions b))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M a G.carrier) H) :
    AtomicForcing.GroundGeneric M (joint a b c hcs G H) := by
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  intro D hD hd
  obtain ⟨s,hs,hsE⟩ := hH (fiberSet b D (genericFilterSet a G.carrier))
    (fiberSet_mem _ b D _ hN hTN (hMN hb) (hMN hD) hgN)
    (fiberSet_dense M a b c D hM hT ha hb hD hcs hd G hG)
  obtain ⟨_,p,hp,z,hz,he⟩ := ZFSet.mem_sep.mp hsE
  obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a G.carrier p).mp hp
  refine ⟨productMap a b c hcs (p,s),(joint_mem a b c hcs G H p s).mpr ⟨hpG,hs⟩,?_⟩
  rw [label_productMap,←he]
  exact hz

end TuringRigidity.TaggedProductGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPartitionBridge
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenPartitionBridge
open TransitiveNameModel BoundedSetTheory CohenGroundPoset InternalCohenFactor
open TaggedProductConditions CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem pair_bridge (a b T f g x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ bridge a b T f g ↔
      x ∈ a ∧ y ∈ b ∧ ∃ t ∈ T, ZFSet.pair t x ∈ f ∧ ZFSet.pair y t ∈ g := by
  constructor
  · intro h
    obtain ⟨_,x',hx,y',hy,he,ht⟩ := ZFSet.mem_sep.mp h
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,ht⟩
  · rintro ⟨hx,hy,ht⟩
    exact ZFSet.mem_sep.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,ht⟩

theorem bridge_mem (M a b T f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hTm : T ∈ M) (hf : f ∈ M) (hg : g ∈ M) :
    bridge a b T f g ∈ M := by
  let e := cons a (cons b (cons T (cons f (fun _ => g))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i; exact ha; exact hb; exact hTm; exact hf; exact hg
  simpa only [bridge,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.conj (.pairMem 0 2 7) (.pairMem 1 0 8)))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb)

theorem internal_union_iso (M A B c f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A) (hc : c ∈ M) (hf : f ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ conditions B, ∃ s ∈ conditions (A \ B), z = code p s)
    (hfs : ∀ p ∈ conditions B, ∀ s ∈ conditions (A \ B), ∀ z,
      ZFSet.pair (ZFSet.pair p s) z ∈ f ↔ z = code p s) :
    let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B hBA).symm
    ∃ g ∈ M, ∀ p q, ZFSet.pair (label c p) (label (conditions A) q) ∈ g ↔ q = e p := by
  have hfac := factor_internal M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hfac.1 hfac.2.1
  let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B hBA).symm
  refine ⟨bridge c (conditions A) (productCode A B) f (factorGraph A B),
    bridge_mem M _ _ _ _ _ hM hT hc hcA hprod hf hfac.2.2.2.2,?_⟩
  intro p q
  obtain ⟨⟨r,s⟩,rfl⟩ := (productIso (conditions B) (conditions (A \ B)) c hcs).surjective p
  have heval : e (productIso (conditions B) (conditions (A \ B)) c hcs (r,s)) =
      (factorIso A B hBA).symm (r,s) := by
    change (factorIso A B hBA).symm
      ((productIso (conditions B) (conditions (A \ B)) c hcs).symm
        ((productIso (conditions B) (conditions (A \ B)) c hcs) (r,s))) = _
    rw [OrderIso.symm_apply_apply]
  rw [pair_bridge]
  simp only [label_mem,true_and]
  change (∃ t ∈ productCode A B,
    ZFSet.pair t (label c (productMap _ _ c hcs (r,s))) ∈ f ∧
      ZFSet.pair (label _ q) t ∈ factorGraph A B) ↔ q = e ((productIso _ _ c hcs) (r,s))
  rw [label_productMap,heval]
  constructor
  · rintro ⟨t,ht,htf,htg⟩
    obtain ⟨u,hu,v,hv,rfl⟩ := ZFSet.mem_prod.mp ht
    obtain ⟨u,rfl⟩ := label_surjective (conditions B) hu
    obtain ⟨v,rfl⟩ := label_surjective (conditions (A \ B)) hv
    obtain ⟨hu,hv⟩ := (code_injective _ _ _ _).mp ((hfs _ (label_mem _ u) _ (label_mem _ v) _).mp htf)
    have hur : u = r := label_injective _ hu.symm
    have hvs : v = s := label_injective _ hv.symm
    subst u; subst v
    have hq := (factorGraph_is_iso_graph A B hBA q r s).mp htg
    simpa only [OrderIso.symm_apply_apply] using congrArg (factorIso A B hBA).symm hq
  · intro hq
    refine ⟨ZFSet.pair (label _ r) (label _ s),ZFSet.pair_mem_prod.mpr ⟨label_mem _ r,label_mem _ s⟩,
      (hfs _ (label_mem _ r) _ (label_mem _ s) _).mpr rfl,?_⟩
    apply (factorGraph_is_iso_graph A B hBA q r s).mpr
    rw [hq,OrderIso.apply_symm_apply]

end TuringRigidity.CohenPartitionBridge

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductRecovery
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductRecovery
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting TaggedProductGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem jointSet_mem (N c g h : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hg : g ∈ N) (hh : h ∈ N) : jointSet c g h ∈ N := by
  let e := cons g (cons h (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|i; exact hg; exact hh
    all_goals exact hN _ (sourceT_omega_mem N hN hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hsepCode (left right value : ZFSet.{0}) :
      (codeFormula 1 0 2 5 6).Eval (cons right (cons left (cons value e))) ↔
        value = code left right :=
    codeFormula_spec 1 0 2 5 6 _ rfl rfl
  simpa only [jointSet,Formula.Eval,hsepCode,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (codeFormula 1 0 2 5 6))) e he hc

variable (a b c : ZFSet.{0})
variable (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
variable (G : GenericFilter (Conditions a)) (H : GenericFilter (Conditions b))

theorem code_mem_joint (p : Conditions a) (s : Conditions b) :
    code (label a p) (label b s) ∈ genericFilterSet c (joint a b c hcs G H).carrier ↔
      p ∈ G.carrier ∧ s ∈ H.carrier := by
  rw [mem_genericFilterSet]
  constructor
  · rintro ⟨r,hr,he⟩
    have hrps : r = productMap a b c hcs (p,s) := label_injective c
      (he.trans (label_productMap a b c hcs (p,s)).symm)
    exact (joint_mem a b c hcs G H p s).mp (hrps ▸ hr)
  · intro h
    exact ⟨productMap a b c hcs (p,s),(joint_mem a b c hcs G H p s).mpr h,
      label_productMap a b c hcs (p,s)⟩

theorem jointFilterSet_eq :
    genericFilterSet c (joint a b c hcs G H).carrier =
      jointSet c (genericFilterSet a G.carrier) (genericFilterSet b H.carrier) := by
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨r,_,hrz⟩ := (mem_genericFilterSet c _ z).mp hz
    have hzc := hrz ▸ label_mem c r
    obtain ⟨p,hp,s,hs,he⟩ := (hcs z).mp hzc
    obtain ⟨p,rfl⟩ := label_surjective a hp
    obtain ⟨s,rfl⟩ := label_surjective b hs
    obtain ⟨hpG,hsH⟩ := (code_mem_joint a b c hcs G H p s).mp (he ▸ hz)
    exact ZFSet.mem_sep.mpr ⟨hzc,label a p,(mem_genericFilterSet a _ _).mpr ⟨p,hpG,rfl⟩,
      label b s,(mem_genericFilterSet b _ _).mpr ⟨s,hsH,rfl⟩,he⟩
  · intro hz
    obtain ⟨_,p,hp,s,hs,he⟩ := ZFSet.mem_sep.mp hz
    obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a G.carrier p).mp hp
    obtain ⟨s,hsH,rfl⟩ := (mem_genericFilterSet b H.carrier s).mp hs
    exact he.symm ▸ (code_mem_joint a b c hcs G H p s).mpr ⟨hpG,hsH⟩

theorem leftFilterSet_eq : genericFilterSet a G.carrier =
    sectionSet a b (genericFilterSet c (joint a b c hcs G H).carrier) ∅ := by
  apply ZFSet.ext; intro p
  constructor
  · intro hp
    obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a _ p).mp hp
    obtain ⟨s,hs⟩ := H.nonempty
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,label b s,label_mem b s,
      code (label a p) (label b s),(code_mem_joint a b c hcs G H p s).mpr ⟨hpG,hs⟩,rfl,
      fun x hx => False.elim (ZFSet.notMem_empty x hx)⟩
  · intro hp
    obtain ⟨hpa,s,hs,z,hz,he,_⟩ := ZFSet.mem_sep.mp hp
    obtain ⟨p,rfl⟩ := label_surjective a hpa
    obtain ⟨s,rfl⟩ := label_surjective b hs
    have hpG := ((code_mem_joint a b c hcs G H p s).mp (he ▸ hz)).1
    exact (mem_genericFilterSet a _ _).mpr ⟨p,hpG,rfl⟩

theorem rightFilterSet_eq : genericFilterSet b H.carrier =
    fiberSet b (genericFilterSet c (joint a b c hcs G H).carrier) a := by
  apply ZFSet.ext; intro s
  constructor
  · intro hs
    obtain ⟨s,hsH,rfl⟩ := (mem_genericFilterSet b _ s).mp hs
    obtain ⟨p,hp⟩ := G.nonempty
    exact ZFSet.mem_sep.mpr ⟨label_mem b s,label a p,label_mem a p,
      code (label a p) (label b s),(code_mem_joint a b c hcs G H p s).mpr ⟨hp,hsH⟩,rfl⟩
  · intro hs
    obtain ⟨hsb,p,hp,z,hz,he⟩ := ZFSet.mem_sep.mp hs
    obtain ⟨p,rfl⟩ := label_surjective a hp
    obtain ⟨s,rfl⟩ := label_surjective b hsb
    have hsH := ((code_mem_joint a b c hcs G H p s).mp (he ▸ hz)).2
    exact (mem_genericFilterSet b _ _).mpr ⟨s,hsH,rfl⟩

end TuringRigidity.TaggedProductRecovery

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductExtension
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open TaggedProductGeneric TaggedProductRecovery RegularTreeExtension
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem extension_eq (M a b c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions b))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M a G.carrier) H) :
    genericExtensionSet M c (joint a b c hcs G H).carrier =
      genericExtensionSet (genericExtensionSet M a G.carrier) b H.carrier := by
  let N := genericExtensionSet M a G.carrier
  let V := genericExtensionSet N b H.carrier
  let J := joint a b c hcs G H
  let O := genericExtensionSet M c J.carrier
  obtain ⟨hN,hTN,hMN,hgN⟩ := extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hNV,hhV⟩ := extension_properties N b hN hTN (hMN hb) H hH
  have hJ := joint_ground_generic M a b c hM hT ha hb hcs G hG H hH
  obtain ⟨hO,hTO,hMO,hjO⟩ := extension_properties M c hM hT hc J hJ
  have hgO : genericFilterSet a G.carrier ∈ O := by
    rw [leftFilterSet_eq a b c hcs G H]
    exact sectionSet_mem O a b _ ∅ hO hTO (hMO ha) (hMO hb) hjO
      (hO _ (sourceT_omega_mem O hO hTO) _ ZFSet.omega_zero)
  have hhO : genericFilterSet b H.carrier ∈ O := by
    rw [rightFilterSet_eq a b c hcs G H]
    exact fiberSet_mem O b _ a hO hTO (hMO hb) hjO (hMO ha)
  have hNO : N ⊆ O := InternalNameEvaluation.extension_subset M O hO hTO hMO G.carrier hgO
  have hVO : V ⊆ O := InternalNameEvaluation.extension_subset N O hO hTO hNO H.carrier hhO
  have hjV : genericFilterSet c J.carrier ∈ V := by
    rw [jointFilterSet_eq a b c hcs G H]
    exact jointSet_mem V c _ _ hV hTV (hNV (hMN hc)) (hNV hgN) hhV
  have hOV : O ⊆ V := InternalNameEvaluation.extension_subset M V hV hTV
    (fun _ hx => hNV (hMN hx)) J.carrier hjV
  exact ZFSet.ext (fun x => ⟨fun hx => hOV hx,fun hx => hVO hx⟩)

end TuringRigidity.TaggedProductExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPartitionRealization
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.CohenPartitionRealization
open TransitiveNameModel BoundedSetTheory CountableForcing CohenGroundPoset
open InternalCohenFactor InternalCohenProjectedGeneric TaggedProductConditions CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem reassemble_projected (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (J : GenericFilter (Conditions (conditions B))) (hJ : AtomicForcing.GroundGeneric M J)
    (R : GenericFilter (Conditions (conditions (A \ B))))
    (hR : AtomicForcing.GroundGeneric (genericExtensionSet M (conditions B) J.carrier) R) :
    ∃ U : GenericFilter (Conditions (conditions A)), AtomicForcing.GroundGeneric M U ∧
      genericExtensionSet M (conditions A) U.carrier =
        genericExtensionSet (genericExtensionSet M (conditions B) J.carrier)
          (conditions (A \ B)) R.carrier ∧ projected A B hBA U = J := by
  have hfac := factor_internal M A B hM hT hA hB
  have hcA := conditions_mem M A hM hT hA
  obtain ⟨c,hc,hcs,f,hf,_,hfs,_⟩ := internal_product M _ _ hM hT hfac.1 hfac.2.1
  let T := TaggedProductGeneric.joint _ _ c hcs J R
  have hTg := TaggedProductGeneric.joint_ground_generic M _ _ c hM hT hfac.1 hfac.2.1 hcs J hJ R hR
  have hTe := TaggedProductExtension.extension_eq M _ _ c hM hT hfac.1 hfac.2.1 hc hcs J hJ R hR
  let e := (productIso (conditions B) (conditions (A \ B)) c hcs).symm.trans (factorIso A B hBA).symm
  obtain ⟨g,hg,hge⟩ := CohenPartitionBridge.internal_union_iso M A B c f hM hT hA hB hBA hc hf hcs hfs
  let U := AutomorphismName.mapFilter e T
  have hU := InternalOrderIsoTransport.map_ground_generic M _ _ g hM hT hc hcA hg e hge T hTg
  have hUe := (InternalOrderIsoTransport.extension_eq M _ _ g hM hT hc hcA hg e hge T hTg).trans hTe
  have hmem (p : Conditions (conditions A)) : p ∈ U.carrier ↔
      project A B hBA p ∈ J.carrier ∧
      project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p ∈ R.carrier := by
    change (productIso _ _ c hcs).symm ((productIso _ _ c hcs) ((factorIso A B hBA) p)) ∈
      (SourceEquationTail.productFilter J R).carrier ↔ _
    rw [OrderIso.symm_apply_apply]
    rfl
  refine ⟨U,hU,hUe,InternalCohen.filter_ext _ _ ?_⟩
  apply Set.ext
  intro p
  rw [mem_projected]
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ((hmem q).mp hq).1
  · intro hp
    obtain ⟨r,hr⟩ := R.nonempty
    let q := (factorIso A B hBA).symm (p,r)
    have hq : factorIso A B hBA q = (p,r) := (factorIso A B hBA).apply_symm_apply _
    have hq1 : project A B hBA q = p := congrArg Prod.fst hq
    have hq2 : project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) q = r := congrArg Prod.snd hq
    exact ⟨q,(hmem q).mpr ⟨hq1.symm ▸ hp,hq2.symm ▸ hr⟩,hq1⟩

theorem reassemble_column (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (X : Oracle)
    (J : GenericFilter (Conditions (CohenColumnRealName.poset {a})))
    (hJ : AtomicForcing.GroundGeneric M J)
    (hJX : (CohenColumnRealName.realName {a} a).val J.carrier = realCode X)
    (R : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod {a} ZFSet.omega))))
    (hR : AtomicForcing.GroundGeneric (genericExtensionSet M (CohenColumnRealName.poset {a}) J.carrier) R) :
    ∃ U : GenericFilter (Conditions (CohenColumnRealName.poset K)),
      AtomicForcing.GroundGeneric M U ∧
      genericExtensionSet M (CohenColumnRealName.poset K) U.carrier =
        genericExtensionSet (genericExtensionSet M (CohenColumnRealName.poset {a}) J.carrier)
          (conditions (ZFSet.prod K ZFSet.omega \ ZFSet.prod {a} ZFSet.omega)) R.carrier ∧
      (CohenColumnRealName.realName K a).val U.carrier = realCode X := by
  have hω := sourceT_omega_mem M hM hT
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hK hω
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hsingle hω
  obtain ⟨U,hU,hUe,hUJ⟩ := reassemble_projected M _ _ hM hT hA hB
    (CohenColumnRealName.singleton_coordinates_subset K a ha) J hJ R hR
  obtain ⟨Y,hYJ,hYU,_,_⟩ := CohenColumnRealName.projected_real_value M K a hM hT hK ha U hU
  rw [hUJ,hJX] at hYJ
  exact ⟨U,hU,hUe,hYU.trans hYJ.symm⟩

end TuringRigidity.CohenPartitionRealization

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_PrefixSingletonRealization
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.PrefixSingletonRealization
open TransitiveNameModel BoundedSetTheory CountableForcing CohenBorelForcing
open InternalCohen (bitSet wordCode)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem sparse_realization (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (realFilter A))) :
    ∃ L : GenericFilter (Conditions SparseCohenRealName.poset),
      AtomicForcing.GroundGeneric M L ∧
      genericExtensionSet M SparseCohenRealName.poset L.carrier = RealGeneratedModel.hull M (realCode A) ∧
      ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ InternalCollapse.unionGraph L ↔ A n = b := by
  let H := InternalCohen.pushFilter (realFilter A)
  let L := InternalDenseInclusion.push InternalCohen.conditions SparseCohenRealName.poset
    CohenPrefixDensity.conditions_subset H
  have hc := InternalCohen.conditions_mem M hM hT
  have hs := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  have hL := InternalDenseInclusion.push_ground_generic M _ _ hM hT hc hs
    CohenPrefixDensity.conditions_subset CohenPrefixDensity.dense_inclusion H hA
  have he := DenseInclusionExtension.extension_eq M _ _ hM hT hc hs
    CohenPrefixDensity.conditions_subset CohenPrefixDensity.dense_inclusion H hA
  obtain ⟨B,_,hfilter,hbits,_⟩ := SparseCohenRealName.generic_real_value M hM hT L hL
  have hBA : B = A := by
    funext n
    let p := InternalCohen.conditionEquiv (⟨FiniteShuffle.initial A (n+1)⟩ : Condition)
    have hp : p ∈ H.carrier := by
      change InternalCohen.conditionEquiv.symm p ∈ (realFilter A).carrier
      rw [show p = InternalCohen.conditionEquiv ⟨FiniteShuffle.initial A (n+1)⟩ from rfl,
        OrderIso.symm_apply_apply]
      exact (ShuffleRequirements.realizes_initial A A (n+1)).mpr (fun _ _ => rfl)
    let q := InternalDenseInclusion.embed InternalCohen.conditions SparseCohenRealName.poset
      CohenPrefixDensity.conditions_subset p
    have hq : q ∈ L.carrier := (InternalDenseInclusion.embed_mem_push _ _ _ H p).mpr hp
    apply (hfilter q).mp hq n (A n)
    rw [InternalDenseInclusion.label_embed,
      show label InternalCohen.conditions p = wordCode (FiniteShuffle.initial A (n+1)) from
        InternalCohen.label_encodeCondition ⟨FiniteShuffle.initial A (n+1)⟩]
    apply (InternalCohen.pair_mem_wordCode _ _ _).mpr
    exact ⟨by simp,by simp [FiniteShuffle.initial]⟩
  subst B
  exact ⟨L,hL,he.trans (InternalCohen.prefix_extension_eq_hull M hM hT A hA),hbits⟩

theorem singleton_realization (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (A : Oracle)
    (hA : AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (realFilter A))) :
    ∃ J : GenericFilter (Conditions (CohenColumnRealName.poset {a})),
      AtomicForcing.GroundGeneric M J ∧
      genericExtensionSet M (CohenColumnRealName.poset {a}) J.carrier =
        RealGeneratedModel.hull M (realCode A) ∧
      (CohenColumnRealName.realName {a} a).val J.carrier = realCode A := by
  obtain ⟨L,hL,hLe,hbits⟩ := sparse_realization M hM hT A hA
  obtain ⟨e,f,hf,he,hbit⟩ := CohenColumnRealName.singleton_iso_bits M a hM hT ha
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hω
  have hcB := CohenGroundPoset.conditions_mem M _ hM hT hB
  have hcω := CohenGroundPoset.conditions_mem M _ hM hT hω
  have hfi := InternalInverseGraph.inverse_mem M _ _ f hM hT hcB hcω hf
  have hfie : ∀ condition image,
      ZFSet.pair (label SparseCohenRealName.poset condition)
        (label (CohenColumnRealName.poset {a}) image) ∈
        InternalInverseGraph.inverse (CohenColumnRealName.poset {a}) SparseCohenRealName.poset f ↔
        image = e.symm condition := by
    intro condition image
    rw [InternalInverseGraph.pair_inverse]
    simp only [label_mem,true_and,he]
    constructor
    · intro equality
      apply e.injective
      rw [OrderIso.apply_symm_apply]
      exact equality.symm
    · intro equality
      rw [equality,OrderIso.apply_symm_apply]
  let J := AutomorphismName.mapFilter e.symm L
  have hJ := InternalOrderIsoTransport.map_ground_generic M _ _ _ hM hT hcω hcB hfi e.symm hfie L hL
  have hJe := InternalOrderIsoTransport.extension_eq M _ _ _ hM hT hcω hcB hfi e.symm hfie L hL
  refine ⟨J,hJ,hJe.trans hLe,CohenColumnRealName.val_realName {a} a J A ?_⟩
  intro n b
  rw [←hbits n b,InternalCollapse.mem_unionGraph,InternalCollapse.mem_unionGraph]
  constructor
  · rintro ⟨p,hp,hpb⟩
    exact ⟨e p,hp,(hbit p n b).mpr hpb⟩
  · rintro ⟨p,hp,hpb⟩
    exact ⟨e.symm p,by simpa only [J,AutomorphismName.mapFilter,Set.mem_ofPred_eq,
      OrderIso.symm_symm,OrderIso.apply_symm_apply] using hp,
      (hbit (e.symm p) n b).mp (by simpa only [OrderIso.apply_symm_apply] using hpb)⟩

end TuringRigidity.PrefixSingletonRealization

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealHullColumnRealization
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCountableOrdinals
open CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem real_hull_generic_column_realizes_oai (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (X A : Oracle)
    (hXE : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hAE : realCode A ∈ genericExtensionSet M (poset K) G.carrier)
    (hA : AtomicForcing.GroundGeneric (RealGeneratedModel.hull M (realCode X))
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter A))) :
    ColumnRealizesExtension (RealGeneratedModel.hull M (realCode X)) K a
      (genericExtensionSet M (poset K) G.carrier) A := by
  obtain ⟨hN,hH,L,hL,hLE⟩ := TwoRealHull.joined_factorization M K hM hT hK G hG X A hXE hAE
  let N := RealGeneratedModel.hull M (realCode X)
  have haM := hM K hK.2.1 a ha
  have hsingle := singleton_mem M hM hT.pairing haM
  have hsK : ({a} : ZFSet.{0}) ⊆ K := fun _ hx => ZFSet.mem_singleton.mp hx ▸ ha
  obtain ⟨R,hR,hRE⟩ := CohenRemainderTransport.transport_to_remainder M _ K {a}
    hM hT hH.1 hH.2.1 (fun _ hz => hH.2.2.1 (hN.2.2.1 hz)) hK hsingle hsK
    (Or.inr (InternalCountableClosure.singleton_countable M a hM hT haM)) L hL
  obtain ⟨J,hJ,hJE,hJA⟩ := PrefixSingletonRealization.singleton_realization N a
    hN.1 hN.2.1 (hN.2.2.1 haM) A hA
  have hRJ : AtomicForcing.GroundGeneric (genericExtensionSet N (poset {a}) J.carrier) R := by
    rw [hJE]
    exact hR
  obtain ⟨U,hU,hUE,hUA⟩ := CohenPartitionRealization.reassemble_column N K a
    hN.1 hN.2.1 (hN.2.2.1 hK.2.1) ha A J hJ hJA R hRJ
  refine ⟨U,hU,hUE.trans ?_,hUA⟩
  rw [hJE]
  exact hRE.trans hLE

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RelativeConstructible.real_hull_generic_column_realizes_oai := @OAI.TuringRigidity.RelativeConstructible.real_hull_generic_column_realizes_oai
