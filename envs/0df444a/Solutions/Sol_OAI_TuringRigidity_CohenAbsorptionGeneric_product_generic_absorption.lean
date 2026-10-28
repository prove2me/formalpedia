-- Prove2me | solution 1 for OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:56:47.312251+00:00
-- url     : https://prove2.me/submissions/dfdce5fb-a35d-4279-8d29-98efea045c66

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_FiniteModelGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem finiteModelGraph_pair (f : ℕ → ZFSet.{u}) (n i : ℕ) (y : ZFSet.{u}) :
    ZFSet.pair (natSet i) y ∈ finiteModelGraph f n ↔ i ≤ n ∧ y = f i := by
  rw [mem_finiteModelGraph]
  constructor
  · rintro ⟨j,hj,he⟩
    obtain ⟨hij,hy⟩ := ZFSet.pair_inj.mp he
    have heq := natSet_injective hij
    subst j
    exact ⟨hj,hy⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨i,hi,rfl⟩

theorem finiteModelGraph_function (R : ZFSet.{u}) (f : ℕ → ZFSet.{u}) (hf : ∀ i, f i ∈ R) (n : ℕ) :
    TransitiveNameModel.FunctionGraph (natSet (n+1)) R (finiteModelGraph.{u} f n) := by
  constructor
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := (mem_finiteModelGraph f n z).mp hz
    exact ⟨natSet i,(natSet_mem_natSet i (n+1)).mpr (by omega),f i,
      hf i,rfl⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) x).mp hx
    have hin : i ≤ n := by omega
    refine ⟨f i,hf i,
      (finiteModelGraph_pair f n i _).mpr ⟨hin,rfl⟩,?_⟩
    intro y _ hy
    exact ((finiteModelGraph_pair f n i y).mp hy).2

theorem internal_finite_model_graph_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M) (R : ZFSet.{u}) (hR : R ∈ M) :
    ∃ Q ∈ M, (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ ZFSet.prod ZFSet.omega R) ∧
      ∀ f : ℕ → ZFSet.{u}, (∀ i, f i ∈ R) → ∀ n, finiteModelGraph f n ∈ Q := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hPow (product_mem M hM hP hU hPow hS hω hR)
  refine ⟨Q,hQ,hQdef,?_⟩
  intro f hf n
  apply (hQdef _).mpr
  refine ⟨finiteModelGraph_mem M hM hP hU hω f (fun i => hM _ hR _ (hf i)) n,?_⟩
  intro z hz
  obtain ⟨i,_,rfl⟩ := (mem_finiteModelGraph f n z).mp hz
  exact ZFSet.mem_prod.mpr ⟨_,(mem_omega _).mpr ⟨i,rfl⟩,_,hf i,rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelIterationTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem modelIterationTrace_exists (R : ZFSet.{u}) (a : ℕ → ZFSet.{u})
    (ha : ∀ i, a i ∈ R) (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i, S (natSet i) (a i) (a (i+1))) (n : ℕ) :
    ModelIterationTrace ZFSet.omega R (natSet 0) (natSet (n+1)) (natSet n) (a 0)
      (finiteModelGraph a n) S := by
  refine ⟨finiteModelGraph_function R a ha n,rfl,rfl,?_,?_⟩
  · exact (finiteModelGraph_pair a n 0 _).mpr ⟨Nat.zero_le _,rfl⟩
  · intro i hi j _ hj v _ w _ hiv hjw
    obtain ⟨i,_,rfl⟩ := (mem_natSet n i).mp hi
    have hj' : j = natSet (i+1) := hj
    subst j
    rw [((finiteModelGraph_pair a n i v).mp hiv).2,
      ((finiteModelGraph_pair a n (i+1) w).mp hjw).2]
    exact hS i

theorem ModelIterationTrace.correct {R z k f : ZFSet.{u}} (a : ℕ → ZFSet.{u})
    (ha : ∀ i, a i ∈ R) (n : ℕ)
    (S : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : ∀ i w, w ∈ R → S (natSet i) (a i) w → w = a (i+1))
    (hf : ModelIterationTrace ZFSet.omega R z k (natSet n) (a 0) f S)
    {y : ZFSet.{u}} (hy : ZFSet.pair (natSet n) y ∈ f) : y = a n := by
  obtain ⟨hfun,hk,rfl,hzero,hstep⟩ := hf
  have hk' : k = natSet (n+1) := hk
  subst k
  have computes (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (a i) ∈ f := by
    induction i with
    | zero => exact hzero
    | succ i ih =>
      have hin : i ≤ n := by omega
      have hj : natSet.{u} (i+1) ∈ natSet (n+1) := (natSet_mem_natSet _ _).mpr (by omega)
      obtain ⟨w,hw,hjw,_⟩ := hfun.2 _ hj
      have hs := hstep (natSet i) ((natSet_mem_natSet _ _).mpr (by omega)) (natSet (i+1))
        ((mem_omega _).mpr ⟨i+1,rfl⟩) rfl (a i) (ha i) w hw (ih hin) hjw
      have he : w = a (i+1) := hS i w hw hs
      exact he ▸ hjw
  exact hfun.functional ((natSet_mem_natSet n (n+1)).mpr (Nat.lt_succ_self n)) hy (computes n le_rfl)

namespace Formula

theorem eval_modelIterationTrace (o R z k n b f : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (modelIterationTrace o R z k n b f θ).Eval e ↔ ModelIterationTrace (e o) (e R) (e z) (e k) (e n) (e b) (e f)
      (fun i v w => θ.Eval (cons w (cons v (cons i e)))) := by
  simp only [modelIterationTrace,ModelIterationTrace,TransitiveNameModel.FunctionGraph,Formula.Eval,
    eval_functionGraph,eval_successor,eval_empty,eval_pairMem,eval_allMem,eval_imp,eval_rename,cons_zero,cons_succ]
  have eq (i j v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons j (cons i e))) (modelIterationVars n)) = cons w (cons v (cons i e)) := by
    funext n
    rcases n with _|n; rfl
    rcases n with _|n; rfl
    rcases n with _|n <;> rfl
  simp only [eq]
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelIterationFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

theorem eval_modelIteration (o R Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u}) :
    (modelIteration o R Q n b y θ).Eval e ↔ ∃ k ∈ e o, ∃ z ∈ e o, ∃ f ∈ e Q,
      ModelIterationTrace (e o) (e R) z k (e n) (e b) f
        (fun i v w => θ.Eval (cons w (cons v (cons i e)))) ∧ ZFSet.pair (e n) (e y) ∈ f := by
  simp only [modelIteration,Formula.Eval,eval_modelIterationTrace,eval_pairMem,eval_rename,cons_zero,cons_succ]
  have eq (k z f i v w : ZFSet.{u}) :
      (fun n => cons w (cons v (cons i (cons f (cons z (cons k e))))) (modelIterationOuterVars n)) =
        cons w (cons v (cons i e)) := by
    funext n
    rcases n with _|n; rfl
    rcases n with _|n; rfl
    rcases n with _|n <;> rfl
  simp only [eq]

theorem modelIteration_spec (o R Q n b y : ℕ) (θ : Formula) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega)
    (hQ : ∀ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ e R) → ∀ k, finiteModelGraph a k ∈ e Q)
    (N : ℕ) (hn : e n = natSet N) (a : ℕ → ZFSet.{u}) (ha : ∀ i, a i ∈ e R)
    (hb : e b = a 0)
    (hθ : ∀ i w, w ∈ e R →
      (θ.Eval (cons w (cons (a i) (cons (natSet i) e))) ↔ w = a (i+1))) :
    (modelIteration o R Q n b y θ).Eval e ↔ e y = a N := by
  rw [eval_modelIteration,ho,hn,hb]
  constructor
  · rintro ⟨k,_,z,_,f,_,hf,hy⟩
    exact hf.correct a ha N _ (fun i w hw h => (hθ i w hw).mp h) hy
  · intro hy
    refine ⟨natSet (N+1),(mem_omega _).mpr ⟨N+1,rfl⟩,natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,
      finiteModelGraph a N,hQ a ha N,?_,?_⟩
    · exact modelIterationTrace_exists (e R) a ha _ (fun i => (hθ i _ (ha (i+1))).mpr rfl) N
    · exact (finiteModelGraph_pair a N N _).mpr ⟨le_rfl,hy⟩

end Formula
end TuringRigidity.BoundedSetTheory

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRelationSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRelationSelection
open TransitiveNameModel BoundedSetTheory

theorem fiberFormula_spec (Y R x a : ℕ) (e : ℕ → ZFSet.{0}) :
    (fiberFormula Y R x a).Eval e ↔ e a = fiber (e Y) (e R) (e x) := by
  simp only [fiberFormula,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_pairMem,Formula.Eval,cons_zero,cons_succ]
  constructor
  · rintro ⟨hs,h⟩
    apply ZFSet.ext; intro y
    exact ⟨fun hy => ZFSet.mem_sep.mpr ⟨hs hy,(h y (hs hy)).mp hy⟩,
      fun hy => (h y (ZFSet.mem_sep.mp hy).1).mpr (ZFSet.mem_sep.mp hy).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hy => (ZFSet.mem_sep.mp hy).1,
      fun y hy => ZFSet.mem_sep.trans (and_iff_right hy)⟩

theorem fiber_mem (M Y R x : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hY : Y ∈ M) (hR : R ∈ M) (hx : x ∈ M) : fiber Y R x ∈ M := by
  let e := cons x (fun _ => R)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hx; exact hR
  simpa only [fiber,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.pairMem 1 0 2) e he hY

theorem select_relation (M X Y R : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hX : X ∈ M) (hY : Y ∈ M) (hR : R ∈ M)
    (htotal : ∀ x ∈ X, ∃ y ∈ Y, ZFSet.pair x y ∈ R) :
    ∃ T ∈ M, FunctionGraph X Y T ∧ T ⊆ R := by
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hT.powerSet
    hT.separation.finitePrefix.bounded hT.choice hY
  have hf (x : ZFSet.{0}) (hx : x ∈ X) : fiber Y R x ∈ q := by
    apply (hqdef _).mpr
    obtain ⟨y,hy,hxy⟩ := htotal x hx
    exact ⟨fiber_mem M Y R x hM hT hY hR (hM X hX x hx),
      fun _ h => (ZFSet.mem_sep.mp h).1,y,ZFSet.mem_sep.mpr ⟨hy,hxy⟩⟩
  let e := cons X (cons Y (cons R (cons q (fun _ => s))))
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 6 (.conj (fiberFormula 5 6 2 0) (.pairMem 0 1 8)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact hX; exact hY; exact hR; exact hq; exact hsM
  let T := (ZFSet.prod X Y).sep (fun z => φ.Eval (cons z e))
  have hTM : T ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hX hY)
  have hmem (z : ZFSet.{0}) : z ∈ T ↔ ∃ x ∈ X, ∃ y ∈ Y,
      z = ZFSet.pair x y ∧ ZFSet.pair (fiber Y R x) y ∈ s := by
    simp only [T,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_pairMem,fiberFormula_spec,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,x,hx,y,hy,hz,a,_,ha,hay⟩
      exact ⟨x,hx,y,hy,hz,ha ▸ hay⟩
    · rintro ⟨x,hx,y,hy,rfl,hay⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,fiber Y R x,hf x hx,rfl,hay⟩
  refine ⟨T,hTM,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,y,hy,hz,_⟩ := (hmem z).mp hz
    exact ⟨x,hx,y,hy,hz⟩
  · intro x hx
    obtain ⟨y,hy,hxy,_⟩ := hs.2 _ (hf x hx)
    have hyY := (ZFSet.mem_sep.mp hy).1
    refine ⟨y,hyY,(hmem _).mpr ⟨x,hx,y,hyY,rfl,hxy⟩,?_⟩
    intro y' _ hxy'
    obtain ⟨x',_,y'',_,hp,hfy⟩ := (hmem _).mp hxy'
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact hs.functional hfy hxy
  · intro z hz
    obtain ⟨x,_,y,_,rfl,hfy⟩ := (hmem z).mp hz
    exact (ZFSet.mem_sep.mp (InternalWellOrder.choice_value_mem hs hfy)).2

end TuringRigidity.InternalRelationSelection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableFamily
open TransitiveNameModel BoundedSetTheory

theorem sequence_of_graph (S B : ZFSet.{0}) (hB : FunctionGraph ZFSet.omega S B) :
    ∃ E : ℕ → ZFSet.{0}, (∀ n, E n ∈ S) ∧ orbitGraph E = B := by
  classical
  have h (n : ℕ) := hB.2 (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
  choose E hE hpair huniq using h
  refine ⟨E,hE,?_⟩
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_orbitGraph E z).mp hz
    exact hpair n
  · intro hz
    obtain ⟨n,hn,x,hx,rfl⟩ := hB.1 z hz
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact (orbitGraph_pair E n x).mpr (huniq n x hx hz)

end TuringRigidity.InternalCountableFamily

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableMap
open TransitiveNameModel BoundedSetTheory

theorem pair_composite (A B C f g x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ composite A B C f g ↔
      x ∈ A ∧ y ∈ C ∧ ∃ t ∈ B, ZFSet.pair x t ∈ f ∧ ZFSet.pair t y ∈ g := by
  simp only [composite,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',hx,y',hy,he,ht⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,ht⟩
  · rintro ⟨hx,hy,ht⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,ht⟩

theorem composite_mem (M A B C f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hC : C ∈ M) (hf : f ∈ M) (hg : g ∈ M) :
    composite A B C f g ∈ M := by
  let e := cons A (cons C (cons B (cons f (fun _ => g))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact hA; exact hC; exact hB; exact hf; exact hg
  simpa only [composite,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.conj (.pairMem 2 0 7) (.pairMem 0 1 8)))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hC)

theorem composite_function (A B C f g : ZFSet.{0})
    (hf : FunctionGraph A B f) (hg : FunctionGraph B C g) :
    FunctionGraph A C (composite A B C f g) := by
  constructor
  · intro z hz
    exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    obtain ⟨t,ht,hxt,_⟩ := hf.2 x hx
    obtain ⟨y,hy,hty,_⟩ := hg.2 t ht
    refine ⟨y,hy,(pair_composite A B C f g x y).mpr ⟨hx,hy,t,ht,hxt,hty⟩,?_⟩
    intro y' _ hxy'
    obtain ⟨_,_,t',_,hxt',hty'⟩ := (pair_composite A B C f g x y').mp hxy'
    have he := hf.functional hx hxt' hxt
    exact hg.functional ht (he ▸ hty') hty

theorem countable_of_surjection (M A B g : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hgM : g ∈ M)
    (hg : FunctionGraph A B g) (honto : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ g)
    (hct : InternallyCountable M A) : InternallyCountable M B := by
  obtain ⟨f,hfM,hf,hfOnto⟩ := hct
  refine ⟨composite ZFSet.omega A B f g,
    composite_mem M _ A B f g hM hT (sourceT_omega_mem M hM hT) hA hB hfM hgM,
    composite_function _ A B f g hf hg,?_⟩
  intro y hy
  obtain ⟨x,hx,hxy⟩ := honto y hy
  obtain ⟨n,hn,hnx⟩ := hfOnto x hx
  exact ⟨n,hn,(pair_composite _ A B f g n y).mpr ⟨hn,hy,x,hx,hnx,hxy⟩⟩

end TuringRigidity.InternalCountableMap

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

theorem pair_retractGraph (A B d x y : ZFSet.{0}) :
    ZFSet.pair x y ∈ retractGraph A B d ↔
      x ∈ A ∧ y ∈ B ∧ ((x ∈ B ∧ y = x) ∨ (x ∉ B ∧ y = d)) := by
  simp only [retractGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',hx,y',hy,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hx,hy,h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,x,hx,y,hy,rfl,h⟩

theorem retractGraph_mem (M A B d : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hd : d ∈ M) : retractGraph A B d ∈ M := by
  let e := cons A (cons B (fun _ => d))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hA; exact hB; exact hd
  simpa only [retractGraph,Formula.Eval,Formula.eval_orderedPair,Formula.eval_disj,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.disj (.conj (.member 1 4) (.equal 0 1))
          (.conj (.neg (.member 1 4)) (.equal 0 5)))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hB)

theorem retractGraph_function (A B d : ZFSet.{0}) (hd : d ∈ B) :
    FunctionGraph A B (retractGraph A B d) := by
  classical
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    by_cases hxB : x ∈ B
    · refine ⟨x,hxB,(pair_retractGraph A B d x x).mpr ⟨hx,hxB,Or.inl ⟨hxB,rfl⟩⟩,?_⟩
      intro y _ hy
      exact ((pair_retractGraph A B d x y).mp hy).2.2.elim And.right
        (fun h => False.elim (h.1 hxB))
    · refine ⟨d,hd,(pair_retractGraph A B d x d).mpr ⟨hx,hd,Or.inr ⟨hxB,rfl⟩⟩,?_⟩
      intro y _ hy
      exact ((pair_retractGraph A B d x y).mp hy).2.2.elim
        (fun h => False.elim (hxB h.1)) And.right

theorem countable_subset (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hsub : B ⊆ A)
    (hct : InternallyCountable M A) (hne : ∃ d, d ∈ B) : InternallyCountable M B := by
  obtain ⟨d,hd⟩ := hne
  apply InternalCountableMap.countable_of_surjection M A B (retractGraph A B d) hM hT hA hB
    (retractGraph_mem M A B d hM hT hA hB (hM B hB d hd)) (retractGraph_function A B d hd) _ hct
  intro y hy
  exact ⟨y,hsub hy,(pair_retractGraph A B d y y).mpr ⟨hsub hy,hy,Or.inl ⟨hy,rfl⟩⟩⟩

end TuringRigidity.InternalCountableClosure

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalFiniteExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalFiniteExhaustion
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets

theorem mem_initial (f : ℕ → ZFSet.{0}) (n : ℕ) (x : ZFSet.{0}) :
    x ∈ initial f n ↔ ∃ k < n, x = f k := by
  rw [initial,ZFSet.mem_range]
  exact ⟨fun ⟨i,hi⟩ => ⟨i.val,i.isLt,hi.symm⟩,fun ⟨k,hk,hx⟩ => ⟨⟨k,hk⟩,hx.symm⟩⟩

theorem initial_finite (f : ℕ → ZFSet.{0}) (n : ℕ) :
    (initial f n : Set ZFSet.{0}).Finite := by
  rw [initial,ZFSet.coe_range]
  exact Set.finite_range _

theorem initial_subset (A : ZFSet.{0}) (f : ℕ → ZFSet.{0})
    (hf : ∀ n, f n ∈ A) (n : ℕ) : initial f n ⊆ A := by
  intro x hx
  obtain ⟨k,_,rfl⟩ := (mem_initial f n x).mp hx
  exact hf k

theorem initialFormula_spec (g n x : ℕ) (e : ℕ → ZFSet.{0})
    (f : ℕ → ZFSet.{0}) (N : ℕ) (hg : e g = orbitGraph f) (hn : e n = natSet N) :
    (initialFormula g n x).Eval e ↔ e x ∈ initial f N := by
  simp only [initialFormula,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,hg,hn]
  rw [mem_initial]
  constructor
  · rintro ⟨k,hk,hkx⟩
    obtain ⟨k,hklt,rfl⟩ := (mem_natSet N k).mp hk
    exact ⟨k,hklt,(orbitGraph_pair f k _).mp hkx⟩
  · rintro ⟨k,hk,hkx⟩
    exact ⟨natSet k,(natSet_mem_natSet k N).mpr hk,(orbitGraph_pair f k _).mpr hkx⟩

theorem finite_subsets_finite (A : ZFSet.{0}) (hA : (A : Set ZFSet.{0}).Finite) :
    (finiteSubsets A : Set ZFSet.{0}).Finite := by
  apply Set.Finite.of_injOn (f := fun x : ZFSet.{0} => (x : Set ZFSet.{0}))
    (t := Set.powerset (A : Set ZFSet.{0}))
  · intro x hx
    exact (mem_finiteSubsets_iff A x).mp hx |>.1
  · intro x _ y _ hxy
    exact ZFSet.ext (fun z => Set.ext_iff.mp hxy z)
  · exact hA.powerset

theorem finite_subset_initial (A : ZFSet.{0}) (f : ℕ → ZFSet.{0})
    (honto : ∀ x ∈ A, ∃ n, x = f n) (a : ZFSet.{0}) (ha : a ∈ finiteSubsets A) :
    ∃ n, a ⊆ initial f n := by
  classical
  obtain ⟨k,v,hv,rfl⟩ := (mem_finiteSubsets A a).mp ha
  choose idx hidx using fun i => honto (v i) (hv i)
  refine ⟨Finset.univ.sup idx + 1,?_⟩
  intro x hx
  obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hx
  apply (mem_initial f _ _).mpr
  exact ⟨idx i,Nat.lt_succ_of_le (Finset.le_sup (f := idx) (Finset.mem_univ i)),hidx i⟩

theorem finite_subsets_countable (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hct : InternallyCountable M A) :
    InternallyCountable M (finiteSubsets A) := by
  obtain ⟨g,hg,hfun,honto⟩ := hct
  obtain ⟨f,hf,hfg⟩ := InternalCountableFamily.sequence_of_graph A g hfun
  have hgf : orbitGraph f ∈ M := hfg.symm ▸ hg
  have onto : ∀ x ∈ A, ∃ n, x = f n := by
    intro x hx
    obtain ⟨n,hn,hnx⟩ := honto x hx
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,(orbitGraph_pair f n x).mp (hfg.symm ▸ hnx)⟩
  let U := finiteSubsets A
  let E := fun n => finiteSubsets (initial f n)
  have hsub (n : ℕ) : E n ⊆ U := by
    intro a ha
    obtain ⟨hs,hfin⟩ := (mem_finiteSubsets_iff _ a).mp ha
    exact (mem_finiteSubsets_iff A a).mpr ⟨fun x hx => initial_subset A f hf n (hs hx),hfin⟩
  have hEM : orbitGraph E ∈ M := by
    apply InternalSubsetSequence.subset_sequence M U hM hT (finiteSubsets_mem M A hM hT hA)
      (.allMem 0 (initialFormula 3 2 0)) (fun _ => orbitGraph f) (fun _ => hgf) E hsub
    intro n a ha
    rw [Formula.eval_allMem]
    change (∀ x ∈ a, (initialFormula 3 2 0).Eval
      (cons x (cons a (cons (natSet n) (fun _ => orbitGraph f)))) ) ↔ _
    have heval (x : ZFSet.{0}) := initialFormula_spec 3 2 0
      (cons x (cons a (cons (natSet n) (fun _ => orbitGraph f)))) f n rfl rfl
    constructor
    · intro hs
      exact (mem_finiteSubsets_iff _ a).mpr
        ⟨fun x hx => (heval x).mp (hs x hx),((mem_finiteSubsets_iff A a).mp ha).2⟩
    · intro h x hx
      exact (heval x).mpr (((mem_finiteSubsets_iff _ a).mp h).1 hx)
  apply InternalCountableFiniteUnion.internally_countable_union M U hM hT
    (finiteSubsets_mem M A hM hT hA) E
    (fun n => (mem_finiteSubsets_iff U (E n)).mpr
      ⟨hsub n,finite_subsets_finite _ (initial_finite f n)⟩) hEM
  · intro a ha
    obtain ⟨n,hn⟩ := finite_subset_initial A f onto a ha
    exact ⟨n,(mem_finiteSubsets_iff _ a).mpr ⟨hn,((mem_finiteSubsets_iff A a).mp ha).2⟩⟩
  · exact ⟨∅,(mem_finiteSubsets_iff A ∅).mpr
      ⟨ZFSet.empty_subset A,by simpa only [ZFSet.coe_empty] using Set.finite_empty⟩⟩

end TuringRigidity.InternalFiniteExhaustion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableProduct
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteExhaustion

theorem finite_product (A B : ZFSet.{0})
    (hA : (A : Set ZFSet.{0}).Finite) (hB : (B : Set ZFSet.{0}).Finite) :
    (ZFSet.prod A B : Set ZFSet.{0}).Finite := by
  apply ((hA.prod hB).image (fun t => ZFSet.pair t.1 t.2)).subset
  intro z hz
  obtain ⟨x,hx,y,hy,hz⟩ := ZFSet.mem_prod.mp hz
  exact ⟨(x,y),⟨hx,hy⟩,hz.symm⟩

theorem rectangleFormula_spec (A B f g n p : ℕ) (e : ℕ → ZFSet.{0})
    (F G : ℕ → ZFSet.{0}) (N : ℕ)
    (hF : ∀ k, F k ∈ e A) (hG : ∀ k, G k ∈ e B)
    (hf : e f = orbitGraph F) (hg : e g = orbitGraph G) (hn : e n = natSet N) :
    (rectangleFormula A B f g n p).Eval e ↔ e p ∈ ZFSet.prod (initial F N) (initial G N) := by
  simp only [rectangleFormula,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ]
  constructor
  · rintro ⟨x,_,y,_,hp,hx,hy⟩
    exact ZFSet.mem_prod.mpr ⟨x,
      (initialFormula_spec (f+2) (n+2) 1 _ F N hf hn).mp hx,y,
      (initialFormula_spec (g+2) (n+2) 0 _ G N hg hn).mp hy,hp⟩
  · intro hp
    obtain ⟨x,hx,y,hy,hp⟩ := ZFSet.mem_prod.mp hp
    exact ⟨x,initial_subset (e A) F hF N hx,y,initial_subset (e B) G hG N hy,hp,
      (initialFormula_spec (f+2) (n+2) 1 _ F N hf hn).mpr hx,
      (initialFormula_spec (g+2) (n+2) 0 _ G N hg hn).mpr hy⟩

theorem product_countable (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M)
    (hcA : InternallyCountable M A) (hcB : InternallyCountable M B) :
    InternallyCountable M (ZFSet.prod A B) := by
  obtain ⟨f,hf,hff,hfo⟩ := hcA
  obtain ⟨g,hg,hgf,hgo⟩ := hcB
  obtain ⟨F,hF,hFf⟩ := InternalCountableFamily.sequence_of_graph A f hff
  obtain ⟨G,hG,hGg⟩ := InternalCountableFamily.sequence_of_graph B g hgf
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA hB
  let E := fun n => ZFSet.prod (initial F n) (initial G n)
  have hsub (n : ℕ) : E n ⊆ ZFSet.prod A B := by
    intro z hz
    obtain ⟨x,hx,y,hy,hz⟩ := ZFSet.mem_prod.mp hz
    exact ZFSet.mem_prod.mpr ⟨x,initial_subset A F hF n hx,y,initial_subset B G hG n hy,hz⟩
  have hgraph : orbitGraph E ∈ M := by
    let e := cons A (cons B (cons f (fun _ => g)))
    have he : ∀ i, e i ∈ M := by
      intro i; rcases i with _|_|_|i
      exact hA; exact hB; exact hf; exact hg
    exact InternalSubsetSequence.subset_sequence M _ hM hT hprod
      (rectangleFormula 2 3 4 5 1 0) e he E hsub
      (fun n _ _ => rectangleFormula_spec 2 3 4 5 1 0 _ F G n hF hG hFf.symm hGg.symm rfl)
  apply InternalCountableFiniteUnion.internally_countable_union M _ hM hT hprod E
    (fun n => (mem_finiteSubsets_iff _ (E n)).mpr
      ⟨hsub n,finite_product _ _ (initial_finite F n) (initial_finite G n)⟩) hgraph
  · intro z hz
    obtain ⟨x,hx,y,hy,hz⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨i,hi,hix⟩ := hfo x hx
    obtain ⟨j,hj,hjy⟩ := hgo y hy
    obtain ⟨i,rfl⟩ := (mem_omega i).mp hi
    obtain ⟨j,rfl⟩ := (mem_omega j).mp hj
    refine ⟨max i j + 1,ZFSet.mem_prod.mpr ⟨x,?_,y,?_,hz⟩⟩
    · exact (mem_initial F _ x).mpr
        ⟨i,Nat.lt_succ_of_le (Nat.le_max_left i j),(orbitGraph_pair F i x).mp (hFf.symm ▸ hix)⟩
    · exact (mem_initial G _ y).mpr
        ⟨j,Nat.lt_succ_of_le (Nat.le_max_right i j),(orbitGraph_pair G j y).mp (hGg.symm ▸ hjy)⟩
  · exact ⟨ZFSet.pair (F 0) (G 0),ZFSet.pair_mem_prod.mpr ⟨hF 0,hG 0⟩⟩

theorem product_empty_left (B : ZFSet.{0}) : ZFSet.prod ∅ B = ∅ := by
  apply ZFSet.ext; intro z; simp [ZFSet.mem_prod]

theorem product_empty_right (A : ZFSet.{0}) : ZFSet.prod A ∅ = ∅ := by
  apply ZFSet.ext; intro z; simp [ZFSet.mem_prod]

theorem product_countable_or_empty (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M)
    (hcA : A = ∅ ∨ InternallyCountable M A) (hcB : B = ∅ ∨ InternallyCountable M B) :
    ZFSet.prod A B = ∅ ∨ InternallyCountable M (ZFSet.prod A B) := by
  rcases hcA with rfl|hcA
  · exact Or.inl (product_empty_left B)
  rcases hcB with rfl|hcB
  · exact Or.inl (product_empty_right A)
  exact Or.inr (product_countable M A B hM hT hA hB hcA hcB)

theorem omega_countable (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    InternallyCountable M ZFSet.omega := by
  have hω := sourceT_omega_mem M hM hT
  have hn (n : ℕ) : natSet.{0} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  let e : ℕ → ZFSet.{0} := fun _ => ZFSet.omega
  let φ : Formula := .existsMem 1 (.orderedPair 1 0 0)
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph natSet := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e,mem_orbitGraph]
    exact ⟨fun ⟨x,hx,hz⟩ => by obtain ⟨n,rfl⟩ := (mem_omega x).mp hx; exact ⟨n,hz⟩,
      fun ⟨n,hz⟩ => ⟨natSet n,hn n,hz⟩⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e (fun _ => hω)
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hω)
  have heq : (ZFSet.prod ZFSet.omega ZFSet.omega).sep (fun z => φ.Eval (cons z e)) =
      orbitGraph natSet := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function _ natSet hn).1 z hz),hz⟩⟩
  refine ⟨orbitGraph natSet,heq ▸ hs,orbitGraph_function _ natSet hn,?_⟩
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact ⟨natSet n,hn n,(orbitGraph_pair natSet n _).mpr rfl⟩

end TuringRigidity.InternalCountableProduct

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CountedCohenConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountedCohenConditions
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets InternalFiniteExhaustion
open InternalCountableProduct InternalCountableClosure CohenGroundPoset

theorem finite_subsets_countable_or_empty (M A : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M)
    (hct : A = ∅ ∨ InternallyCountable M A) :
    InternallyCountable M (finiteSubsets A) := by
  rcases hct with rfl|hct
  · apply finite_countable M _ hM hT (finiteSubsets_mem M ∅ hM hT hA)
      (finite_subsets_finite ∅ (by simpa only [ZFSet.coe_empty] using Set.finite_empty))
    exact ⟨∅,(mem_finiteSubsets_iff ∅ ∅).mpr
      ⟨ZFSet.empty_subset ∅,by simpa only [ZFSet.coe_empty] using Set.finite_empty⟩⟩
  · exact finite_subsets_countable M A hM hT hA hct

theorem empty_condition (A : ZFSet.{0}) : ∅ ∈ conditions A := by
  apply (mem_conditions A ∅).mpr
  refine ⟨(mem_finiteSubsets_iff _ ∅).mpr
    ⟨ZFSet.empty_subset _,by simpa only [ZFSet.coe_empty] using Set.finite_empty⟩,?_⟩
  intro x _ b _ c _ hb
  exact False.elim (ZFSet.notMem_empty _ hb)

theorem alphabet_countable (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    InternallyCountable M InternalCohen.alphabet := by
  apply finite_countable M _ hM hT (InternalCohen.alphabet_mem M hM hT)
  · have he : (InternalCohen.alphabet : Set ZFSet.{0}) = Set.range InternalCohen.bitSet := by
      ext x
      exact (InternalCohen.mem_alphabet x).trans ⟨fun ⟨b,hb⟩ => ⟨b,hb.symm⟩,
        fun ⟨b,hb⟩ => ⟨b,hb.symm⟩⟩
    rw [he]
    exact Set.finite_range _
  · exact ⟨InternalCohen.bitSet false,(InternalCohen.mem_alphabet _).mpr ⟨false,rfl⟩⟩

theorem conditions_countable (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hct : A = ∅ ∨ InternallyCountable M A) :
    InternallyCountable M (conditions A) := by
  have hB := InternalCohen.alphabet_mem M hM hT
  have hP := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA hB
  have hpc := product_countable_or_empty M A InternalCohen.alphabet hM hT hA hB
    hct (Or.inr (alphabet_countable M hM hT))
  have hfc := finite_subsets_countable_or_empty M _ hM hT hP hpc
  exact countable_subset M _ _ hM hT (finiteSubsets_mem M _ hM hT hP)
    (conditions_mem M A hM hT hA) (fun _ hp => ((mem_conditions A _).mp hp).1)
    hfc ⟨∅,empty_condition A⟩

end TuringRigidity.CountedCohenConditions

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

theorem product_countable (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hca : InternallyCountable M a) (hcb : InternallyCountable M b) :
    ∃ c ∈ M, (∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s) ∧
      InternalCollapse.orderSet c ∈ M ∧ InternallyCountable M c := by
  obtain ⟨c,hc,hcs,g,hg,hgf,_,hgo⟩ := internal_product M a b hM hT ha hb
  refine ⟨c,hc,hcs,InternalCollapse.orderSet_mem M hM hT hc,?_⟩
  exact InternalCountableMap.countable_of_surjection M _ c g hM hT
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb)
    hc hg hgf hgo (InternalCountableProduct.product_countable M a b hM hT ha hb hca hcb)

end TuringRigidity.TaggedProductConditions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenProductSplitting
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenProductSplitting
open TransitiveNameModel BoundedSetTheory TaggedProductConditions CohenGroundPoset
open CohenSymmetry
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem putBit_le {ι : Type} (p : Condition ι) (i : ι) (b : Bool) (hi : p.val i = none) :
    putBit p i b ≤ p := by
  classical
  intro j d hd
  by_cases h : j = i
  · subst j; rw [hi] at hd; cases hd
  · simpa only [putBit,ite_eq_right h] using hd

theorem putBit_incompatible {ι : Type} (p : Condition ι) (i : ι) :
    ¬ ∃ r : Condition ι, r ≤ putBit p i false ∧ r ≤ putBit p i true := by
  classical
  rintro ⟨r,h0,h1⟩
  have h0' := h0 i false (by simp [putBit])
  have h1' := h1 i true (by simp [putBit])
  have he := Option.some.inj (h0'.symm.trans h1')
  cases he

theorem cohen_splits (s : ZFSet.{0}) (hs : s ∈ conditions ZFSet.omega) :
    ∃ s0 ∈ conditions ZFSet.omega, ∃ s1 ∈ conditions ZFSet.omega,
      s ⊆ s0 ∧ s ⊆ s1 ∧
        ¬ ∃ r ∈ conditions ZFSet.omega, s0 ⊆ r ∧ s1 ⊆ r := by
  classical
  obtain ⟨p,rfl⟩ := (CohenConditionCode.isCondition_iff_graph _ s).mp ((mem_conditions _ s).mp hs)
  let f (n : ℕ) : Conditions ZFSet.omega :=
    equivShrink _ ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hf : Function.Injective f := by
    intro n m h
    have he := congrArg (label ZFSet.omega) h
    simp only [f,label,Equiv.symm_apply_apply] at he
    exact natSet_injective he
  have hfin := p.finite.preimage hf.injOn
  obtain ⟨n,hn⟩ := hfin.exists_notMem
  have hn' : p.val (f n) = none := by simpa only [Set.mem_preimage,Set.mem_ofPred_eq,not_not] using hn
  let p0 := putBit p (f n) false
  let p1 := putBit p (f n) true
  refine ⟨CohenConditionCode.graph _ p0,(mem_conditions _ _).mpr (CohenConditionCode.graph_isCondition _ _),
    CohenConditionCode.graph _ p1,(mem_conditions _ _).mpr (CohenConditionCode.graph_isCondition _ _),
    (CohenConditionCode.graph_subset_iff _ _ _).mpr (putBit_le p _ false hn'),
    (CohenConditionCode.graph_subset_iff _ _ _).mpr (putBit_le p _ true hn'),?_⟩
  rintro ⟨r,hr,h0,h1⟩
  obtain ⟨r,rfl⟩ := (CohenConditionCode.isCondition_iff_graph _ r).mp ((mem_conditions _ r).mp hr)
  exact putBit_incompatible p (f n) ⟨r,(CohenConditionCode.graph_subset_iff _ _ _).mp h0,
    (CohenConditionCode.graph_subset_iff _ _ _).mp h1⟩

theorem product_splits (a c : ZFSet.{0})
    (hc : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ conditions ZFSet.omega, z = code p s) :
    ∀ z ∈ c, ∃ z0 ∈ c, ∃ z1 ∈ c, z ⊆ z0 ∧ z ⊆ z1 ∧
      ¬ ∃ r ∈ c, z0 ⊆ r ∧ z1 ⊆ r := by
  intro z hz
  obtain ⟨p,hp,s,hs,rfl⟩ := (hc z).mp hz
  obtain ⟨s0,hs0,s1,hs1,h0,h1,hinc⟩ := cohen_splits s hs
  refine ⟨code p s0,(hc _).mpr ⟨p,hp,s0,hs0,rfl⟩,
    code p s1,(hc _).mpr ⟨p,hp,s1,hs1,rfl⟩,
    (code_subset _ _ _ _).mpr ⟨fun _ h => h,h0⟩,
    (code_subset _ _ _ _).mpr ⟨fun _ h => h,h1⟩,?_⟩
  rintro ⟨r,hr,h0r,h1r⟩
  obtain ⟨p',_,s',hs',rfl⟩ := (hc r).mp hr
  exact hinc ⟨s',hs',(code_subset _ _ _ _).mp h0r |>.2,(code_subset _ _ _ _).mp h1r |>.2⟩

end TuringRigidity.CohenProductSplitting

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

end TuringRigidity.InternalRegularAlgebra

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

end TuringRigidity.InternalBooleanGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalBooleanDense
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

end TuringRigidity.InternalBooleanDense

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalProjectedGeneric
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

end TuringRigidity.InternalProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CountedRegularBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountedRegularBasis
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanDense

theorem basicFormula_spec (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (b p U : ℕ) (e : ℕ → ZFSet.{0}) (hb : e b = B) (hp : e p ∈ c) :
    (basicFormula b p U).Eval e ↔ e U = basicCode c (e p) := by
  have hbasic : basicCode c (e p) ∈ B :=
    (hB _).mpr ⟨basicCode_mem M c _ hM hT hc hp,regular_isCode c _⟩
  simp only [basicFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_imp,
    Formula.eval_subset,cons_zero,cons_succ,hb]
  constructor
  · rintro ⟨hU,hpU,hmin⟩
    have h₁ := hmin _ hbasic (mem_basicCode c _ hp)
    have h₂ := (basicCode_le_iff c _ _ hp ((hB _).mp hU).2).mpr hpU
    exact ZFSet.ext (fun z => ⟨fun hz => h₁ hz,fun hz => h₂ hz⟩)
  · rintro h; rw [h]
    exact ⟨hbasic,mem_basicCode c _ hp,fun V hV hpV =>
      (basicCode_le_iff c _ V hp ((hB V).mp hV).2).mpr hpV⟩

theorem internal_basis (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) :
    ∃ B ∈ M, (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
      ∃ S ∈ M, (∀ U, U ∈ S ↔ ∃ p ∈ c, U = basicCode c p) ∧
        ∃ g ∈ M, FunctionGraph c S g ∧
          (∀ p ∈ c, ∀ U, ZFSet.pair p U ∈ g ↔ U = basicCode c p) ∧
          (∀ U ∈ S, ∃ p ∈ c, ZFSet.pair p U ∈ g) := by
  obtain ⟨B,hBM,hB⟩ := internal_algebra M c hM hT hc
  let e := cons c (fun _ => B)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hc; exact hBM
  let S := B.sep (fun U => ∃ p ∈ c, U = basicCode c p)
  have hs (U : ZFSet.{0}) : U ∈ S ↔ ∃ p ∈ c, U = basicCode c p := by
    change (U ∈ B.sep _) ↔ _
    rw [ZFSet.mem_sep]
    exact ⟨And.right,fun h@⟨p,hp,hU⟩ => ⟨hU ▸ (hB _).mpr
      ⟨basicCode_mem M c p hM hT hc hp,regular_isCode c _⟩,h⟩⟩
  have hφ (U : ZFSet.{0}) : (Formula.existsMem 1 (basicFormula 3 0 1)).Eval (cons U e) ↔
      ∃ p ∈ c, U = basicCode c p := by
    change (∃ p ∈ c, (basicFormula 3 0 1).Eval (cons p (cons U e))) ↔ _
    exact exists_congr (fun p => and_congr_right (fun hp =>
      basicFormula_spec M c B hM hT hc hB 3 0 1 _ rfl hp))
  have hSM : S ∈ M := by
    simpa only [hφ,S] using sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (basicFormula 3 0 1)) e he hBM
  let v := cons c (cons S (fun _ => B))
  have hv : ∀ i, v i ∈ M := by
    intro i; rcases i with _|_|i; exact hc; exact hSM; exact hBM
  let ψ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (basicFormula 5 1 0)))
  let g := (ZFSet.prod c S).sep (fun z => ψ.Eval (cons z v))
  have hgM : g ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded ψ v hv
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hc hSM)
  have hψ (z : ZFSet.{0}) : ψ.Eval (cons z v) ↔
      ∃ p ∈ c, ∃ U ∈ S, z = ZFSet.pair p U ∧ U = basicCode c p := by
    simp only [ψ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,v]
    apply exists_congr; intro p
    apply and_congr_right; intro hp
    apply exists_congr; intro U
    apply and_congr_right; intro _
    exact and_congr_right (fun _ => basicFormula_spec M c B hM hT hc hB 5 1 0 _ rfl hp)
  have hgs (p U : ZFSet.{0}) (hp : p ∈ c) :
      ZFSet.pair p U ∈ g ↔ U = basicCode c p := by
    simp only [g,ZFSet.mem_sep,hψ]
    constructor
    · rintro ⟨_,p',_,U',_,he,hU⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      exact hU
    · intro hU
      have hUS := (hs U).mpr ⟨p,hp,hU⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hUS⟩,p,hp,U,hUS,rfl,hU⟩
  refine ⟨B,hBM,hB,S,hSM,hs,g,hgM,⟨?_,?_⟩,(fun p hp U => hgs p U hp),?_⟩
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro p hp
    exact ⟨basicCode c p,(hs _).mpr ⟨p,hp,rfl⟩,(hgs p _ hp).mpr rfl,
      fun U _ hU => (hgs p U hp).mp hU⟩
  · intro U hU
    obtain ⟨p,hp,he⟩ := (hs U).mp hU
    exact ⟨p,hp,(hgs p U hp).mpr he⟩

theorem counted_basis (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hct : InternallyCountable M c) :
    ∃ S ∈ M, InternallyCountable M S ∧
      (∀ U, U ∈ S ↔ ∃ p ∈ c, U = basicCode c p) ∧
      (∀ U ∈ S, IsCode c U ∧ U ≠ ∅) ∧
      (∀ U, IsCode c U → U ≠ ∅ → ∃ V ∈ S, V ⊆ U) := by
  classical
  obtain ⟨B,_,_,S,hS,hSs,g,hg,hgf,_,hgo⟩ := internal_basis M c hM hT hc
  refine ⟨S,hS,InternalCountableMap.countable_of_surjection M c S g hM hT hc hS hg hgf hgo hct,
    hSs,?_,?_⟩
  · intro U hU
    obtain ⟨p,hp,rfl⟩ := (hSs U).mp hU
    exact ⟨regular_isCode c _,fun h => ZFSet.notMem_empty p (h ▸ mem_basicCode c p hp)⟩
  · intro U hU hne
    have hex : ∃ p, p ∈ U := by
      by_contra h
      exact hne (ZFSet.ext (fun p => ⟨fun hp => False.elim (h ⟨p,hp⟩),
        fun hp => False.elim (ZFSet.notMem_empty p hp)⟩))
    obtain ⟨p,hp⟩ := hex
    exact ⟨basicCode c p,(hSs _).mpr ⟨p,hU.1 hp,rfl⟩,
      (basicCode_le_iff c p U (hU.1 hp) hU).mpr hp⟩

end TuringRigidity.CountedRegularBasis

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularCodeSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularCodeSplitting
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanDense

theorem mem_basic_iff (c p t : ZFSet.{0}) : t ∈ basicCode c p ↔
    t ∈ c ∧ ∀ q ∈ c, t ⊆ q → ∃ r ∈ c, q ⊆ r ∧ p ⊆ r := by
  rw [basicCode,bitCode,mem_regular]
  apply and_congr_right; intro _
  apply forall_congr'; intro q
  apply forall_congr'; intro _
  apply forall_congr'; intro _
  simp only [CohenInternalDecision.below,ZFSet.mem_sep,ZFSet.mem_singleton]
  constructor
  · rintro ⟨r,⟨hr,x,hx,hxr⟩,hqr⟩
    subst x; exact ⟨r,hr,hqr,hxr⟩
  · rintro ⟨r,hr,hqr,hpr⟩; exact ⟨r,⟨hr,p,rfl,hpr⟩,hqr⟩

theorem remainder_isCode (c U V : ZFSet.{0}) (hU : IsCode c U) (hV : IsCode c V) :
    IsCode c (remainder U c V) := by
  have he : remainder U c V = infCode c {U,neg c V} := by
    apply ZFSet.ext; intro p
    simp only [remainder,infCode,ZFSet.mem_sep,ZFSet.mem_pair]
    constructor
    · rintro ⟨hpu,hpn⟩
      exact ⟨hU.1 hpu,fun W hW => hW.elim (fun h => h ▸ hpu) (fun h => h ▸ hpn)⟩
    · rintro ⟨_,h⟩; exact ⟨h U (Or.inl rfl),h _ (Or.inr rfl)⟩
  rw [he]
  exact inf_isCode c _ (fun W hW => (ZFSet.mem_pair.mp hW).elim
    (fun h => h ▸ hU) (fun h => h ▸ neg_isCode c V hV))

theorem remainder_mem (M c U V : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (hV : V ∈ M) : remainder U c V ∈ M := by
  simpa only [remainder,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.member 0 1)
      (fun _ => neg c V) (fun _ => neg_mem M c V hM hT hc hV) hU

theorem partitionFormula_spec (U V W : ℕ) (e : ℕ → ZFSet.{0}) :
    (partitionFormula U V W).Eval e ↔ Partition (e U) (e V) (e W) := by
  simp only [partitionFormula,Partition,Formula.Eval,Formula.eval_subset,Formula.eval_empty,
    Formula.eval_allMem,Formula.eval_disj,cons_zero,cons_succ]

theorem internal_partition (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hsplit : ∀ p ∈ c, ∃ p0 ∈ c, ∃ p1 ∈ c, p ⊆ p0 ∧ p ⊆ p1 ∧
      ¬ ∃ r ∈ c, p0 ⊆ r ∧ p1 ⊆ r) :
    ∀ U ∈ B, U ≠ ∅ → ∃ V ∈ B, ∃ W ∈ B, Partition U V W := by
  classical
  intro U hUB hU0
  have hUM := ((hB U).mp hUB).1
  have hU := ((hB U).mp hUB).2
  have hex : ∃ p, p ∈ U := by
    by_contra h
    exact hU0 (ZFSet.ext (fun p => ⟨fun hp => False.elim (h ⟨p,hp⟩),
      fun hp => False.elim (ZFSet.notMem_empty p hp)⟩))
  obtain ⟨p,hp⟩ := hex
  obtain ⟨p0,hp0,p1,hp1,h0,h1,hinc⟩ := hsplit p (hU.1 hp)
  let V := basicCode c p0
  let W := remainder U c V
  have hV : IsCode c V := regular_isCode c _
  have hVM := basicCode_mem M c p0 hM hT hc hp0
  have hVU : V ⊆ U := (basicCode_le_iff c p0 U hp0 hU).mpr
    (code_lower c U hU p hp p0 hp0 h0)
  have hp1U := code_lower c U hU p hp p1 hp1 h1
  have hp1N : p1 ∈ neg c V := by
    refine ZFSet.mem_sep.mpr ⟨hp1,fun q hq hp1q => ?_⟩
    obtain ⟨r,hr,hqr,hp0r⟩ := ((mem_basic_iff c p0 q).mp hq).2 q
      ((mem_basic_iff c p0 q).mp hq).1 (fun _ h => h)
    exact hinc ⟨r,hr,hp0r,fun _ h => hqr (hp1q h)⟩
  have hp1W : p1 ∈ W := ZFSet.mem_sep.mpr ⟨hp1U,hp1N⟩
  refine ⟨V,(hB V).mpr ⟨hVM,hV⟩,W,
    (hB W).mpr ⟨remainder_mem M c U V hM hT hc hUM hVM,remainder_isCode c U V hU hV⟩,
    hVU,(fun _ h => (ZFSet.mem_sep.mp h).1),
    (fun h => ZFSet.notMem_empty p0 (h ▸ mem_basicCode c p0 hp0)),
    (fun h => ZFSet.notMem_empty p1 (h ▸ hp1W)),?_,?_⟩
  · intro q hq hqW
    exact (ZFSet.mem_sep.mp (ZFSet.mem_sep.mp hqW).2).2 q hq (fun _ h => h)
  · intro q hq
    by_cases hex : ∃ r ∈ V, q ⊆ r
    · obtain ⟨r,hr,hqr⟩ := hex
      exact ⟨r,hVU hr,hqr,Or.inl hr⟩
    · exact ⟨q,hq,(fun _ h => h),Or.inr (ZFSet.mem_sep.mpr ⟨hq,
        ZFSet.mem_sep.mpr ⟨hU.1 hq,fun r hr hqr => hex ⟨r,hr,hqr⟩⟩⟩)⟩

end TuringRigidity.RegularCodeSplitting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularDecisionPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularDecisionPartition
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder RegularCodeSplitting

theorem meet_mem (M U V : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (hV : V ∈ M) : meet U V ∈ M := by
  simpa only [meet,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.member 0 1)
      (fun _ => V) (fun _ => hV) hU

theorem meet_isCode (c U V : ZFSet.{0}) (hU : IsCode c U) (hV : IsCode c V) :
    IsCode c (meet U V) := by
  have he : meet U V = remainder U c (neg c V) := by
    change U.sep (fun p => p ∈ V) = U.sep (fun p => p ∈ regular c V)
    rw [hV.2]
  rw [he]
  exact remainder_isCode c U (neg c V) hU (neg_isCode c V hV)

theorem disjoint_le_neg (c U D : ZFSet.{0}) (hU : IsCode c U) (hD : IsCode c D)
    (he : meet U D = ∅) : U ⊆ neg c D := by
  intro p hp
  refine ZFSet.mem_sep.mpr ⟨hU.1 hp,fun q hq hpq => ?_⟩
  have hqM : q ∈ meet U D := ZFSet.mem_sep.mpr
    ⟨code_lower c U hU p hp q (hD.1 hq) hpq,hq⟩
  exact ZFSet.notMem_empty q (he ▸ hqM)

theorem remainder_empty_le (c U D : ZFSet.{0}) (hU : IsCode c U) (hD : IsCode c D)
    (he : remainder U c D = ∅) : U ⊆ D := by
  classical
  intro p hp
  rw [←hD.2]
  apply (mem_regular c D p).mpr
  refine ⟨hU.1 hp,fun q hq hpq => ?_⟩
  by_contra hn
  have hqR : q ∈ remainder U c D := ZFSet.mem_sep.mpr
    ⟨code_lower c U hU p hp q hq hpq,
      ZFSet.mem_sep.mpr ⟨hq,fun r hr hqr => hn ⟨r,hr,hqr⟩⟩⟩
  exact ZFSet.notMem_empty q (he ▸ hqR)

theorem decidesFormula_spec (c D V : ℕ) (e : ℕ → ZFSet.{0}) :
    (decidesFormula c D V).Eval e ↔ e V ⊆ e D ∨ e V ⊆ neg (e c) (e D) := by
  simp only [decidesFormula,Formula.eval_disj,Formula.eval_subset,Formula.eval_allMem,
    Formula.Eval,cons_zero,cons_succ]
  apply or_congr Iff.rfl
  exact ⟨fun h p hp => ZFSet.mem_sep.mpr (h p hp),
    fun h p hp => ZFSet.mem_sep.mp (h hp)⟩

theorem refiningFormula_spec (c U D V W : ℕ) (e : ℕ → ZFSet.{0}) :
    (refiningFormula c U D V W).Eval e ↔ Refines (e c) (e U) (e D) (e V) (e W) := by
  simp only [refiningFormula,Refines,Formula.Eval,partitionFormula_spec,decidesFormula_spec]

theorem refining_partition (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hsplit : ∀ p ∈ c, ∃ p0 ∈ c, ∃ p1 ∈ c, p ⊆ p0 ∧ p ⊆ p1 ∧
      ¬ ∃ r ∈ c, p0 ⊆ r ∧ p1 ⊆ r)
    (U D : ZFSet.{0}) (hUB : U ∈ B) (hDB : D ∈ B) (hne : U ≠ ∅) :
    ∃ V ∈ B, ∃ W ∈ B, Refines c U D V W := by
  classical
  have hU := ((hB U).mp hUB).2
  have hD := ((hB D).mp hDB).2
  obtain ⟨V,hVB,W,hWB,hpart⟩ := internal_partition M c B hM hT hc hB hsplit U hUB hne
  by_cases hUD : U ⊆ D
  · exact ⟨V,hVB,W,hWB,hpart,Or.inl (fun _ h => hUD (hpart.1 h)),
      Or.inl (fun _ h => hUD (hpart.2.1 h))⟩
  by_cases hUN : U ⊆ neg c D
  · exact ⟨V,hVB,W,hWB,hpart,Or.inr (fun _ h => hUN (hpart.1 h)),
      Or.inr (fun _ h => hUN (hpart.2.1 h))⟩
  have hL : meet U D ≠ ∅ := fun h => hUN (disjoint_le_neg c U D hU hD h)
  have hR : remainder U c D ≠ ∅ := fun h => hUD (remainder_empty_le c U D hU hD h)
  have hUM := ((hB U).mp hUB).1
  have hDM := ((hB D).mp hDB).1
  refine ⟨meet U D,(hB _).mpr ⟨meet_mem M U D hM hT hUM hDM,meet_isCode c U D hU hD⟩,
    remainder U c D,(hB _).mpr
      ⟨remainder_mem M c U D hM hT hc hUM hDM,remainder_isCode c U D hU hD⟩,
    ⟨(fun _ h => (ZFSet.mem_sep.mp h).1),(fun _ h => (ZFSet.mem_sep.mp h).1),hL,hR,?_,?_⟩,
    Or.inl (fun _ h => (ZFSet.mem_sep.mp h).2),Or.inr (fun _ h => (ZFSet.mem_sep.mp h).2)⟩
  · intro p hp hpR
    exact (ZFSet.mem_sep.mp (ZFSet.mem_sep.mp hpR).2).2 p
      (ZFSet.mem_sep.mp hp).2 (fun _ h => h)
  · intro p hp
    by_cases hex : ∃ q ∈ D, p ⊆ q
    · obtain ⟨q,hq,hpq⟩ := hex
      have hqU := code_lower c U hU p hp q (hD.1 hq) hpq
      exact ⟨q,hqU,hpq,Or.inl (ZFSet.mem_sep.mpr ⟨hqU,hq⟩)⟩
    · exact ⟨p,hp,(fun _ h => h),Or.inr (ZFSet.mem_sep.mpr
        ⟨hp,ZFSet.mem_sep.mpr ⟨hU.1 hp,fun q hq hpq => hex ⟨q,hq,hpq⟩⟩⟩)⟩

end TuringRigidity.RegularDecisionPartition

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularSplitter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularSplitter
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalProjectedGeneric RegularDecisionPartition RegularCodeSplitting

theorem splitter_graph (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hBM : B ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hsplit : ∀ p ∈ c, ∃ p0 ∈ c, ∃ p1 ∈ c, p ⊆ p0 ∧ p ⊆ p1 ∧
      ¬ ∃ r ∈ c, p0 ⊆ r ∧ p1 ⊆ r) :
    ∃ T ∈ M, FunctionGraph (ZFSet.prod (positive B) B)
      (ZFSet.prod (positive B) (positive B)) T ∧
      ∀ U ∈ positive B, ∀ D ∈ B, ∀ V W,
        ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ T →
          V ∈ positive B ∧ W ∈ positive B ∧ Refines c U D V W := by
  let P := positive B
  let X := ZFSet.prod P B
  let Y := ZFSet.prod P P
  have hP := positive_mem M B hM hT hBM
  have hX := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hP hBM
  have hY := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hP hP
  let e := cons X (cons Y (cons P (cons B (fun _ => c))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact hX; exact hY; exact hP; exact hBM; exact hc
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.existsMem 7 (.conj (.orderedPair 3 1 0)
      (.existsMem 7 (.existsMem 8 (.conj (.orderedPair 4 1 0)
        (refiningFormula 11 3 2 1 0)))))))))
  let R := (ZFSet.prod X Y).sep (fun z => φ.Eval (cons z e))
  have hRM : R ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hX hY)
  have hR (U D V W : ZFSet.{0}) :
      ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ R ↔
        U ∈ P ∧ D ∈ B ∧ V ∈ P ∧ W ∈ P ∧ Refines c U D V W := by
    simp only [R,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      refiningFormula_spec,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,x,_,y,_,hxy,U',hU,D',hD,hUD,V',hV,W',hW,hVW,h⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hUD
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hVW
      exact ⟨hU,hD,hV,hW,h⟩
    · rintro ⟨hU,hD,hV,hW,h⟩
      have hx : ZFSet.pair U D ∈ X := ZFSet.pair_mem_prod.mpr ⟨hU,hD⟩
      have hy : ZFSet.pair V W ∈ Y := ZFSet.pair_mem_prod.mpr ⟨hV,hW⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hy⟩,_,hx,_,hy,rfl,U,hU,D,hD,rfl,V,hV,W,hW,rfl,h⟩
  have htotal : ∀ x ∈ X, ∃ y ∈ Y, ZFSet.pair x y ∈ R := by
    intro x hx
    obtain ⟨U,hU,D,hD,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨hUB,hU0⟩ := ZFSet.mem_sep.mp hU
    obtain ⟨V,hV,W,hW,h⟩ := refining_partition M c B hM hT hc hB hsplit U D hUB hD hU0
    have hVP : V ∈ P := ZFSet.mem_sep.mpr ⟨hV,h.1.2.2.1⟩
    have hWP : W ∈ P := ZFSet.mem_sep.mpr ⟨hW,h.1.2.2.2.1⟩
    exact ⟨ZFSet.pair V W,ZFSet.pair_mem_prod.mpr ⟨hVP,hWP⟩,
      (hR U D V W).mpr ⟨hU,hD,hVP,hWP,h⟩⟩
  obtain ⟨T,hTmem,hfun,hTR⟩ := InternalRelationSelection.select_relation M X Y R
    hM hT hX hY hRM htotal
  exact ⟨T,hTmem,hfun,fun U _ D _ V W hp => ((hR U D V W).mp (hTR hp)).2.2⟩

theorem counted_cohen_presentation (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) :
    ∃ c ∈ M,
      (∀ z, z ∈ c ↔ ∃ p ∈ q, ∃ s ∈ CohenGroundPoset.conditions ZFSet.omega,
        z = TaggedProductConditions.code p s) ∧
      InternalCollapse.orderSet c ∈ M ∧ InternallyCountable M c ∧
      ∃ B ∈ M, (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
        ∃ S ∈ M, InternallyCountable M S ∧ S ⊆ positive B ∧
          (∀ U, U ∈ S ↔ ∃ p ∈ c, U = InternalBooleanDense.basicCode c p) ∧
          (∀ U, IsCode c U → U ≠ ∅ → ∃ V ∈ S, V ⊆ U) ∧
          ∃ T ∈ M, FunctionGraph (ZFSet.prod (positive B) B)
            (ZFSet.prod (positive B) (positive B)) T ∧
            ∀ U ∈ positive B, ∀ D ∈ B, ∀ V W,
              ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ T →
                V ∈ positive B ∧ W ∈ positive B ∧ Refines c U D V W := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨c,hc,hcs,hco,hcc⟩ := TaggedProductConditions.product_countable M q
    (CohenGroundPoset.conditions ZFSet.omega) hM hT hq
    (CohenGroundPoset.conditions_mem M _ hM hT hω) hct
    (CountedCohenConditions.conditions_countable M _ hM hT hω
      (Or.inr (InternalCountableProduct.omega_countable M hM hT)))
  obtain ⟨B,hBM,hB⟩ := internal_algebra M c hM hT hc
  obtain ⟨S,hSM,hSc,hSs,hSp,hSd⟩ := CountedRegularBasis.counted_basis M c hM hT hc hcc
  refine ⟨c,hc,hcs,hco,hcc,B,hBM,hB,S,hSM,hSc,?_,hSs,hSd,?_⟩
  · intro U hU
    exact ZFSet.mem_sep.mpr ⟨(hB U).mpr ⟨hM S hSM U hU,(hSp U hU).1⟩,(hSp U hU).2⟩
  · exact splitter_graph M c B hM hT hc hBM hB (CohenProductSplitting.product_splits q c hcs)

end TuringRigidity.InternalRegularSplitter

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularBinaryTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularBinaryTree
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalProjectedGeneric RegularDecisionPartition RegularCodeSplitting

theorem children_spec (B T U D : ZFSet.{0})
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hU : U ∈ positive B) (hD : D ∈ B) :
    (∀ b, children B T U D b ∈ positive B) ∧
      ZFSet.pair (ZFSet.pair U D)
        (ZFSet.pair (children B T U D false) (children B T U D true)) ∈ T := by
  classical
  obtain ⟨y,hy,hxy,_⟩ := hf.2 (ZFSet.pair U D) (ZFSet.pair_mem_prod.mpr ⟨hU,hD⟩)
  obtain ⟨V,hV,W,hW,rfl⟩ := ZFSet.mem_prod.mp hy
  have hex : ∃ f : Bool → ZFSet.{0}, (∀ b, f b ∈ positive B) ∧
      ZFSet.pair (ZFSet.pair U D) (ZFSet.pair (f false) (f true)) ∈ T := by
    refine ⟨(fun b => if b then W else V),?_,hxy⟩
    intro b; cases b; exact hV; exact hW
  simp only [children,dite_eq_left hex]
  exact hex.choose_spec

theorem children_unique (B T U D V W : ZFSet.{0})
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hU : U ∈ positive B) (hD : D ∈ B)
    (hp : ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ T) :
    V = children B T U D false ∧ W = children B T U D true :=
  ZFSet.pair_inj.mp (hf.functional (ZFSet.pair_mem_prod.mpr ⟨hU,hD⟩) hp
    (children_spec B T U D hf hU hD).2)

theorem tree_nil (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) : tree c B T E [] = c := by
  simp only [tree,List.reverseRecOn_nil]

theorem tree_append (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (s : List Bool) (b : Bool) :
    tree c B T E (s ++ [b]) = children B T (tree c B T E s) (E s.length) b := by
  simp only [tree,List.reverseRecOn_concat]

variable (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0})
variable (hc : c ∈ positive B)
variable (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
variable (hE : ∀ n, E n ∈ B)
variable (hB : ∀ U ∈ B, IsCode c U)
variable (hs : ∀ U ∈ positive B, ∀ D ∈ B, ∀ V W,
  ZFSet.pair (ZFSet.pair U D) (ZFSet.pair V W) ∈ T →
    V ∈ positive B ∧ W ∈ positive B ∧ Refines c U D V W)

include hc hf hE

theorem tree_positive (s : List Bool) : tree c B T E s ∈ positive B := by
  induction s using List.reverseRecOn with
  | nil => simpa only [tree_nil] using hc
  | append_singleton s b ih =>
    rw [tree_append]
    exact (children_spec B T _ _ hf ih (hE s.length)).1 b

include hs

theorem tree_refines (s : List Bool) :
    Refines c (tree c B T E s) (E s.length)
      (tree c B T E (s ++ [false])) (tree c B T E (s ++ [true])) := by
  rw [tree_append,tree_append]
  have hp := tree_positive c B T E hc hf hE s
  exact (hs _ hp _ (hE s.length) _ _ (children_spec B T _ _ hf hp (hE s.length)).2).2.2

theorem tree_child_subset (s : List Bool) (b : Bool) :
    tree c B T E (s ++ [b]) ⊆ tree c B T E s := by
  have h := (tree_refines c B T E hc hf hE hs s).1
  cases b; exact h.1; exact h.2.1

theorem tree_append_subset (s t : List Bool) : tree c B T E (s ++ t) ⊆ tree c B T E s := by
  induction t using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using (show tree c B T E s ⊆ tree c B T E s from fun _ h => h)
  | append_singleton t b ih =>
    rw [←List.append_assoc]
    exact fun _ hp => ih (tree_child_subset c B T E hc hf hE hs (s ++ t) b hp)

theorem tree_prefix (s t : List Bool) (hst : s <+: t) : tree c B T E t ⊆ tree c B T E s := by
  obtain ⟨u,rfl⟩ := hst
  exact tree_append_subset c B T E hc hf hE hs s u

theorem tree_incompatible (s u v : List Bool) :
    ∀ p ∈ tree c B T E (s ++ [false] ++ u), p ∉ tree c B T E (s ++ [true] ++ v) := by
  intro p hp hq
  exact (tree_refines c B T E hc hf hE hs s).1.2.2.2.2.1 p
    (tree_append_subset c B T E hc hf hE hs (s ++ [false]) u hp)
    (tree_append_subset c B T E hc hf hE hs (s ++ [true]) v hq)

include hB

theorem level_overlaps (D : ZFSet.{0}) (hD : IsCode c D) (hD0 : D ≠ ∅) (n : ℕ) :
    ∃ s : List Bool, s.length = n ∧ ∃ p ∈ tree c B T E s, p ∈ D := by
  classical
  induction n with
  | zero =>
    obtain he|⟨p,hp⟩ := ZFSet.eq_empty_or_nonempty D
    · exact False.elim (hD0 he)
    · exact ⟨[],rfl,p,by rw [tree_nil]; exact hD.1 hp,hp⟩
  | succ n ih =>
    obtain ⟨s,hlen,p,hp,hpD⟩ := ih
    have hpart := (tree_refines c B T E hc hf hE hs s).1
    obtain ⟨r,hr,hpr,hrL|hrR⟩ := hpart.2.2.2.2.2 p hp
    · have hrC := (hB _ (ZFSet.mem_sep.mp (tree_positive c B T E hc hf hE s)).1).1 hr
      exact ⟨s ++ [false],by simp [hlen],r,hrL,code_lower c D hD p hpD r hrC hpr⟩
    · have hrC := (hB _ (ZFSet.mem_sep.mp (tree_positive c B T E hc hf hE s)).1).1 hr
      exact ⟨s ++ [true],by simp [hlen],r,hrR,code_lower c D hD p hpD r hrC hpr⟩

theorem refines_enumerated (n : ℕ) (hn : E n ≠ ∅) :
    ∃ s : List Bool, s.length = n+1 ∧ tree c B T E s ⊆ E n := by
  obtain ⟨s,hlen,p,hp,hpE⟩ := level_overlaps c B T E hc hf hE hB hs (E n) (hB _ (hE n)) hn (n+1)
  cases s using List.reverseRecOn with
  | nil => simp at hlen
  | append_singleton s b =>
    have hslen : s.length = n := by simpa only [List.length_append,List.length_singleton,Nat.add_right_cancel_iff] using hlen
    have hd := tree_refines c B T E hc hf hE hs s
    have hdec : tree c B T E (s ++ [b]) ⊆ E n ∨ tree c B T E (s ++ [b]) ⊆ neg c (E n) := by
      rw [←hslen]
      cases b; exact hd.2.1; exact hd.2.2
    rcases hdec with h|h
    · exact ⟨s ++ [b],hlen,h⟩
    · exact False.elim ((ZFSet.mem_sep.mp (h hp)).2 p hpE (fun _ h => h))

theorem tree_dense
    (hDense : ∀ D, IsCode c D → D ≠ ∅ → ∃ n, E n ≠ ∅ ∧ E n ⊆ D) :
    ∀ D, IsCode c D → D ≠ ∅ → ∃ s : List Bool, tree c B T E s ⊆ D := by
  intro D hD hD0
  obtain ⟨n,hn,hnD⟩ := hDense D hD hD0
  obtain ⟨s,_,hsD⟩ := refines_enumerated c B T E hc hf hE hB hs n hn
  exact ⟨s,fun _ hp => hnD (hsD hp)⟩

end TuringRigidity.RegularBinaryTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeRun
open TransitiveNameModel BoundedSetTheory InternalProjectedGeneric RegularBinaryTree

theorem bit_word (s : List Bool) (n : ℕ) (hn : n < s.length) :
    bit (InternalCohen.wordCode s) (natSet n) = s[n] := by
  classical
  simp only [bit,InternalCohen.pair_mem_wordCode]
  cases h : s[n] <;> simp [h,hn]

theorem run_positive (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (w : ZFSet.{0})
    (hc : c ∈ positive B)
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hE : ∀ n, E n ∈ B) : ∀ n, run c B T E w n ∈ positive B := by
  intro n; induction n with
  | zero => exact hc
  | succ n ih => exact (children_spec B T _ _ hf ih (hE n)).1 _

theorem run_take (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (s : List Bool)
    (n : ℕ) (hn : n ≤ s.length) :
    run c B T E (InternalCohen.wordCode s) n = tree c B T E (s.take n) := by
  induction n with
  | zero => simp only [run,List.take_zero,tree_nil]
  | succ n ih =>
    have hlt : n < s.length := hn
    rw [run,List.take_succ_eq_append_getElem hlt,tree_append,ih (Nat.le_of_lt hlt),
      List.length_take,Nat.min_eq_left (Nat.le_of_lt hlt),bit_word s n hlt]

theorem run_word (c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (s : List Bool) :
    run c B T E (InternalCohen.wordCode s) s.length = tree c B T E s := by
  simpa only [List.take_length] using run_take c B T E s s.length le_rfl

theorem stepFormula_spec (B T : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (w U V : ZFSet.{0}) (n : ℕ)
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hU : U ∈ positive B) (hE : ∀ n, E n ∈ B)
    (b p x y t e word b1 i u v : ℕ) (env : ℕ → ZFSet.{0})
    (hb : env b = B) (hp : env p = positive B)
    (hx : env x = ZFSet.prod (positive B) B) (hy : env y = ZFSet.prod (positive B) (positive B))
    (ht : env t = T) (he : env e = orbitGraph E) (hw : env word = w)
    (h1 : env b1 = InternalCohen.bitSet true) (hi : env i = natSet n)
    (hu : env u = U) (hv : env v = V) :
    (stepFormula b p x y t e word b1 i u v).Eval env ↔
      V = children B T U (E n) (bit w (natSet n)) := by
  classical
  simp only [stepFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    Formula.eval_disj,cons_zero,cons_succ,hb,hp,hx,hy,ht,he,hw,h1,hi,hu,hv]
  constructor
  · rintro ⟨D,_,L,_,R,_,a,_,z,_,ha,hz,hED,haz,hout⟩
    obtain rfl := (orbitGraph_pair E n D).mp hED
    subst a; subst z
    obtain ⟨hL,hR⟩ := children_unique B T U (E n) L R hf hU (hE n) haz
    rcases hout with ⟨hbit,hV⟩|⟨hbit,hV⟩
    · simpa [bit,hbit] using hV.trans hR
    · simpa [bit,hbit] using hV.trans hL
  · intro hV
    have hc := children_spec B T U (E n) hf hU (hE n)
    refine ⟨E n,hE n,children B T U (E n) false,hc.1 false,
      children B T U (E n) true,hc.1 true,ZFSet.pair U (E n),
      ZFSet.pair_mem_prod.mpr ⟨hU,hE n⟩,_,ZFSet.pair_mem_prod.mpr ⟨hc.1 false,hc.1 true⟩,
      rfl,rfl,(orbitGraph_pair E n _).mpr rfl,hc.2,?_⟩
    by_cases hbit : ZFSet.pair (natSet n) (InternalCohen.bitSet true) ∈ w
    · exact Or.inl ⟨hbit,by simpa [bit,hbit] using hV⟩
    · exact Or.inr ⟨hbit,by simpa [bit,hbit] using hV⟩

end TuringRigidity.RegularTreeRun

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalRegularTree
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalRegularTree
open TransitiveNameModel BoundedSetTheory InternalProjectedGeneric RegularBinaryTree RegularTreeRun

theorem graph_domain_unique (a b C f : ZFSet.{0})
    (ha : FunctionGraph a C f) (hb : FunctionGraph b C f) : a = b := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨y,_,hxy,_⟩ := ha.2 x hx
    obtain ⟨x',hx',y',_,he⟩ := hb.1 _ hxy
    exact (ZFSet.pair_inj.mp he).1 ▸ hx'
  · intro hx
    obtain ⟨y,_,hxy,_⟩ := hb.2 x hx
    obtain ⟨x',hx',y',_,he⟩ := ha.1 _ hxy
    exact (ZFSet.pair_inj.mp he).1 ▸ hx'

theorem tree_graph_internal (M c B T : ZFSet.{0}) (E : ℕ → ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hBM : B ∈ M) (hTM : T ∈ M)
    (hc : c ∈ positive B)
    (hf : FunctionGraph (ZFSet.prod (positive B) B) (ZFSet.prod (positive B) (positive B)) T)
    (hE : ∀ n, E n ∈ B) (hEM : orbitGraph E ∈ M) :
    ∃ A ∈ M, FunctionGraph InternalCohen.conditions (positive B) A ∧
      ∀ (s : List Bool) U,
        ZFSet.pair (InternalCohen.wordCode s) U ∈ A ↔ U = tree c B T E s := by
  let P := positive B
  let X := ZFSet.prod P B
  let Y := ZFSet.prod P P
  have hP := positive_mem M B hM hT hBM
  have hω := sourceT_omega_mem M hM hT
  have hcM := hM _ hP _ hc
  have hX := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hP hBM
  have hY := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hP hP
  have hW := InternalCohen.conditions_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_model_graph_bound M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hω P hP
  let e := cons ZFSet.omega (cons P (cons Q (cons c (cons B (cons X (cons Y
    (cons T (cons (orbitGraph E) (cons (InternalCohen.bitSet true)
      (cons InternalCohen.alphabet (fun _ => InternalCohen.conditions)))))))))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|_|_|_|_|_|i
    exact hω; exact hP; exact hQM; exact hcM; exact hBM; exact hX; exact hY
    exact hTM; exact hEM
    exact hM _ (InternalCohen.alphabet_mem M hM hT) _ ((InternalCohen.mem_alphabet _).mpr ⟨true,rfl⟩)
    exact InternalCohen.alphabet_mem M hM hT
    exact hW
  let θ := stepFormula 11 8 12 13 14 15 5 16 2 1 0
  let ψ := Formula.modelIteration 4 5 6 0 7 1 θ
  have hψ (s : List Bool) (n : ℕ) (U z : ZFSet.{0}) :
      ψ.Eval (cons (natSet n) (cons U (cons (InternalCohen.wordCode s) (cons z e)))) ↔
        U = run c B T E (InternalCohen.wordCode s) n := by
    apply Formula.modelIteration_spec 4 5 6 0 7 1 θ _ rfl hQ n rfl
      (run c B T E (InternalCohen.wordCode s)) (run_positive c B T E _ hc hf hE) rfl
    intro i V _
    exact stepFormula_spec B T E (InternalCohen.wordCode s) _ V i hf
      (run_positive c B T E _ hc hf hE i) hE
      11 8 12 13 14 15 5 16 2 1 0 _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  let φ : Formula := .existsMem 12 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 3 (.conj (.functionGraph 2 0 14) ψ))))
  let A := (ZFSet.prod InternalCohen.conditions P).sep (fun z => φ.Eval (cons z e))
  have hAM : A ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hW hP)
  have hgs (s : List Bool) (U : ZFSet.{0}) :
      ZFSet.pair (InternalCohen.wordCode s) U ∈ A ↔ U = tree c B T E s := by
    simp only [A,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,w,_,V,_,he,n,hn,hfun,hiter⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      have hfg : FunctionGraph n InternalCohen.alphabet (InternalCohen.wordCode s) :=
        (Formula.eval_functionGraph 2 0 14 _).mp hfun
      have hlen := graph_domain_unique n (natSet s.length) _ _ hfg (InternalCohen.wordCode_function s)
      subst n
      exact ((hψ s s.length U _).mp hiter).trans (run_word c B T E s)
    · intro heq
      have hUP : U ∈ P := heq ▸ tree_positive c B T E hc hf hE s
      have hsW : InternalCohen.wordCode s ∈ InternalCohen.conditions :=
        (InternalCohen.mem_conditions _).mpr ((InternalCohen.prefix_iff_wordCode _).mpr ⟨s,rfl⟩)
      refine ⟨ZFSet.pair_mem_prod.mpr ⟨hsW,hUP⟩,_,hsW,U,hUP,rfl,natSet s.length,
        (mem_omega _).mpr ⟨s.length,rfl⟩,?_,?_⟩
      · exact (Formula.eval_functionGraph 2 0 14 _).mpr (InternalCohen.wordCode_function s)
      · exact (hψ s s.length U _).mpr (heq.trans (run_word c B T E s).symm)
  refine ⟨A,hAM,⟨?_,?_⟩,hgs⟩
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro w hw
    obtain ⟨s,rfl⟩ := (InternalCohen.prefix_iff_wordCode w).mp ((InternalCohen.mem_conditions w).mp hw)
    exact ⟨tree c B T E s,tree_positive c B T E hc hf hE s,(hgs s _).mpr rfl,
      fun U _ hU => (hgs s U).mp hU⟩

end TuringRigidity.InternalRegularTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenAbsorptionTree
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAbsorptionTree
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalProjectedGeneric RegularBinaryTree RegularDecisionPartition

theorem top_code (c : ZFSet.{0}) : IsCode c c := by
  refine ⟨(fun _ h => h),ZFSet.ext (fun p => ?_)⟩
  rw [mem_regular]
  exact ⟨And.left,fun hp => ⟨hp,fun q hq _ => ⟨q,hq,fun _ h => h⟩⟩⟩

theorem internal_dense_tree (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) :
    ∃ c ∈ M,
      (∀ z, z ∈ c ↔ ∃ p ∈ q, ∃ s ∈ CohenGroundPoset.conditions ZFSet.omega,
        z = TaggedProductConditions.code p s) ∧
      InternalCollapse.orderSet c ∈ M ∧ InternallyCountable M c ∧
      ∃ B ∈ M, (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
        ∃ T ∈ M, ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
          ∃ A ∈ M, FunctionGraph InternalCohen.conditions (positive B) A ∧
            (∀ (s : List Bool) U,
              ZFSet.pair (InternalCohen.wordCode s) U ∈ A ↔ U = tree c B T E s) ∧
            (∀ s : List Bool, tree c B T E s ∈ positive B) ∧
            (∀ s : List Bool, Refines c (tree c B T E s) (E s.length)
              (tree c B T E (s ++ [false])) (tree c B T E (s ++ [true]))) ∧
            (∀ s t : List Bool, s <+: t → tree c B T E t ⊆ tree c B T E s) ∧
            (∀ s u v : List Bool, ∀ p ∈ tree c B T E (s ++ [false] ++ u),
              p ∉ tree c B T E (s ++ [true] ++ v)) ∧
            (∀ D, IsCode c D → D ≠ ∅ → ∃ s : List Bool, tree c B T E s ⊆ D) := by
  obtain ⟨c,hc,hcs,hco,hcc,B,hBM,hB,S,hSM,hSc,hSP,hSs,hSd,T,hTM,hTf,hTs⟩ :=
    InternalRegularSplitter.counted_cohen_presentation M q hM hT hq hct
  have hc0 : c ≠ ∅ := by
    obtain ⟨g,_,hg,_⟩ := hcc
    obtain ⟨p,hp,_,_⟩ := hg.2 (natSet 0) ((mem_omega _).mpr ⟨0,rfl⟩)
    exact fun he => ZFSet.notMem_empty p (he ▸ hp)
  have hcP : c ∈ positive B := ZFSet.mem_sep.mpr ⟨(hB c).mpr ⟨hc,top_code c⟩,hc0⟩
  obtain ⟨g,hgM,hgf,hgo⟩ := hSc
  obtain ⟨E,hES,hEg⟩ := InternalCountableFamily.sequence_of_graph S g hgf
  have hE : ∀ n, E n ∈ B := fun n => (ZFSet.mem_sep.mp (hSP (hES n))).1
  have hEM : orbitGraph E ∈ M := hEg.symm ▸ hgM
  have hDense : ∀ D, IsCode c D → D ≠ ∅ → ∃ n, E n ≠ ∅ ∧ E n ⊆ D := by
    intro D hD hD0
    obtain ⟨V,hV,hVD⟩ := hSd D hD hD0
    obtain ⟨n,hn,hnV⟩ := hgo V hV
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    have hVE : V = E n := (orbitGraph_pair E n V).mp (hEg.symm ▸ hnV)
    exact ⟨n,(ZFSet.mem_sep.mp (hSP (hES n))).2,hVE ▸ hVD⟩
  obtain ⟨A,hAM,hAf,hAs⟩ := InternalRegularTree.tree_graph_internal M c B T E
    hM hT hBM hTM hcP hTf hE hEM
  refine ⟨c,hc,hcs,hco,hcc,B,hBM,hB,T,hTM,E,hEM,A,hAM,hAf,hAs,
    tree_positive c B T E hcP hTf hE,
    tree_refines c B T E hcP hTf hE hTs,
    tree_prefix c B T E hcP hTf hE hTs,
    tree_incompatible c B T E hcP hTf hE hTs,?_⟩
  exact tree_dense c B T E hcP hTf hE (fun U hU => ((hB U).mp hU).2) hTs hDense

end TuringRigidity.CohenAbsorptionTree

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenFilters
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
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

theorem pull_push (G : GenericFilter Condition) : pullFilter (pushFilter G) = G := by
  have he : (pullFilter (pushFilter G)).carrier = G.carrier := by
    ext p; simp [pullFilter,pushFilter]
  exact filter_ext _ _ he

theorem dense_pull_iff (D : Set (Conditions conditions)) :
    Dense {p : Condition | conditionEquiv p ∈ D} ↔ Dense D := by
  constructor
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv.symm q)
    exact ⟨conditionEquiv p,by simpa using conditionEquiv.monotone hp,hpD⟩
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv q)
    exact ⟨conditionEquiv.symm p,by simpa using conditionEquiv.symm.monotone hp,
      by simpa using hpD⟩

theorem groundGeneric_iff (M : ZFSet.{0}) (G : GenericFilter (Conditions conditions)) :
    AtomicForcing.GroundGeneric M G ↔
      ∀ D ∈ M, Dense {p : Condition | wordCode p.word ∈ D} →
        ∃ p ∈ (pullFilter G).carrier, wordCode p.word ∈ D := by
  have hl (p : Condition) : label conditions (conditionEquiv p) = wordCode p.word :=
    label_encodeCondition p
  constructor
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mp (by simpa only [Set.mem_ofPred_eq,hl] using hd)
    obtain ⟨q,hq,hqD⟩ := h D hD hd'
    refine ⟨conditionEquiv.symm q,by simpa [pullFilter] using hq,?_⟩
    simpa only [←hl,OrderIso.apply_symm_apply] using hqD
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mpr hd
    obtain ⟨q,hq,hqD⟩ := h D hD (by simpa only [Set.mem_ofPred_eq,hl] using hd')
    exact ⟨conditionEquiv q,hq,by simpa only [hl] using hqD⟩

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeFilter
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeFilter
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense InternalBooleanSyntax
open InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem refines_condition (c U p : ZFSet.{0}) (hU : IsCode c U) (hU0 : U ≠ ∅)
    (hUp : U ⊆ basicCode c p) : ∃ r ∈ U, p ⊆ r := by
  obtain he|⟨q,hq⟩ := ZFSet.eq_empty_or_nonempty U
  · exact False.elim (hU0 he)
  have hb : q ∈ regular c (CohenInternalDecision.below c {p}) := hUp hq
  obtain ⟨r,hr,hqr⟩ := (mem_regular _ _ _).mp hb |>.2 q (hU.1 hq) (fun _ h => h)
  obtain ⟨hrc,s,hs,hsr⟩ := ZFSet.mem_sep.mp hr
  have hsp := ZFSet.mem_singleton.mp hs
  exact ⟨r,code_lower c U hU q hq r hrc hqr,hsp ▸ hsr⟩

theorem nodeFamily_mem (M B A D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hB : B ∈ M) (hA : A ∈ M) (hD : D ∈ M) : nodeFamily B A D ∈ M := by
  simpa only [nodeFamily,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 1 3))
      (cons D (fun _ => A)) (by intro i; cases i <;> assumption) hB

theorem nodeFamily_dense (c B A D : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hA : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s)
    (hm : ∀ s t, s <+: t → f t ⊆ f s)
    (hden : ∀ U, IsCode c U → U ≠ ∅ → ∃ s, f s ⊆ U)
    (hD : Dense {p : CohenBorelForcing.Condition | wordCode p.word ∈ D}) :
    Dense {p : Conditions c | label c p ∈ ZFSet.sUnion (nodeFamily B A D)} := by
  intro p
  have hpB := mem_basicCode c _ (label_mem c p)
  have hp0 : basicCode c (label c p) ≠ ∅ := fun he => ZFSet.notMem_empty _ (he ▸ hpB)
  obtain ⟨s,hs⟩ := hden _ (regular_isCode c _) hp0
  obtain ⟨t,ht,htD⟩ := hD ⟨s⟩
  have htp : f t.word ⊆ basicCode c (label c p) := fun _ h => hs (hm s t.word ht h)
  obtain ⟨r,hr,hpr⟩ := refines_condition c _ _ (hf _).2.1 (hf _).2.2 htp
  obtain ⟨r,rfl⟩ := label_surjective c ((hf _).2.1.1 hr)
  exact ⟨r,hpr,ZFSet.mem_sUnion.mpr ⟨f t.word,
    ZFSet.mem_sep.mpr ⟨(hf _).1,wordCode t.word,htD,(hA _ _).mpr rfl⟩,hr⟩⟩

theorem branch_ground_generic (M c B A : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hAf : FunctionGraph conditions B A)
    (hAs : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s)
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hroot : f [] = c)
    (hm : ∀ s t, s <+: t → f t ⊆ f s)
    (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
      p ∉ f (a ++ [true] ++ v))
    (hden : ∀ U, IsCode c U → U ≠ ∅ → ∃ s, f s ⊆ U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M
      (pushFilter (branch c f hroot (fun s => (hf s).2.1) hm hd G)) := by
  apply (groundGeneric_iff M _).mpr
  intro D hDM hD
  obtain ⟨p,hp,hpD⟩ := hG (ZFSet.sUnion (nodeFamily B A D))
    (union_mem M hM hT.union (nodeFamily_mem M B A D hM hT hBM hAM hDM))
    (nodeFamily_dense c B A D f hf hAs hm hden hD)
  obtain ⟨U,hUF,hpU⟩ := ZFSet.mem_sUnion.mp hpD
  obtain ⟨_,w,hw,hwU⟩ := ZFSet.mem_sep.mp hUF
  obtain ⟨w',hw',U',_,he⟩ := hAf.1 _ hwU
  have hwc : w ∈ conditions := (ZFSet.pair_inj.mp he).1 ▸ hw'
  obtain ⟨s,hs⟩ := (prefix_iff_wordCode w).mp ((mem_conditions w).mp hwc)
  have hUs : U = f s := (hAs s U).mp (hs.symm ▸ hwU)
  refine ⟨⟨s⟩,?_,hs.symm ▸ hw⟩
  rw [pull_push]
  exact ⟨p,hp,hUs ▸ hpU⟩

end TuringRigidity.RegularTreeFilter

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeCofinality
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeCofinality
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem nodesBelow_mem (M B A U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hB : B ∈ M) (hA : A ∈ M) (hU : U ∈ M) : nodesBelow B A U ∈ M := by
  let e := cons conditions (cons A (fun _ => U))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact conditions_mem M hM hT; exact hA; exact hU
  simpa only [nodesBelow,Formula.Eval,Formula.eval_pairMem,Formula.eval_subset,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.pairMem 0 1 3) (.subset 1 4))) e he hB

theorem nodesBelow_decision_dense (c B A U : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hAs : ∀ s V, ZFSet.pair (wordCode s) V ∈ A ↔ V = f s)
    (hden : ∀ V, IsCode c V → V ≠ ∅ → ∃ s, f s ⊆ V)
    (hU : IsCode c U) :
    Dense {p : Conditions c | label c p ∈ ZFSet.sUnion (nodesBelow B A U) ∪ neg c U} := by
  intro p
  obtain ⟨q,hqp,hq⟩ := decision_dense c U hU.1 p
  rcases ZFSet.mem_union.mp hq with hqU|hqN
  · have hb := mem_basicCode c _ (label_mem c q)
    have hb0 : basicCode c (label c q) ≠ ∅ := fun he => ZFSet.notMem_empty _ (he ▸ hb)
    obtain ⟨s,hs⟩ := hden _ (regular_isCode c _) hb0
    obtain ⟨r,hr,hqr⟩ := refines_condition c _ _ (hf s).2.1 (hf s).2.2 hs
    obtain ⟨r,rfl⟩ := label_surjective c ((hf s).2.1.1 hr)
    have hsU : f s ⊆ U := fun _ h =>
      (basicCode_le_iff c _ U (label_mem c q) hU).mpr hqU (hs h)
    exact ⟨r,le_trans hqr hqp,ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_sUnion.mpr
      ⟨f s,ZFSet.mem_sep.mpr ⟨(hf s).1,wordCode s,
        (mem_conditions _).mpr ⟨_,wordCode_function s⟩,(hAs _ _).mpr rfl,hsU⟩,hr⟩))⟩
  · exact ⟨q,hqp,ZFSet.mem_union.mpr (Or.inr hqN)⟩

theorem hit_iff_node (M c B A U : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hB : B ∈ M) (hA : A ∈ M)
    (hU : U ∈ M) (hUc : IsCode c U)
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hAs : ∀ s V, ZFSet.pair (wordCode s) V ∈ A ↔ V = f s)
    (hden : ∀ V, IsCode c V → V ≠ ∅ → ∃ s, f s ⊆ V)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G U ↔ ∃ s, Hit G (f s) ∧ f s ⊆ U := by
  constructor
  · intro hGU
    have hFM := nodesBelow_mem M B A U hM hT hB hA hU
    obtain ⟨p,hp,hpD⟩ := hG (ZFSet.sUnion (nodesBelow B A U) ∪ neg c U)
      (binary_union_mem M hM hT.pairing hT.union (union_mem M hM hT.union hFM)
        (neg_mem M c U hM hT hc hU))
      (nodesBelow_decision_dense c B A U f hf hAs hden hUc)
    rcases ZFSet.mem_union.mp hpD with hpF|hpN
    · obtain ⟨V,hVF,hpV⟩ := ZFSet.mem_sUnion.mp hpF
      obtain ⟨_,w,hw,hwV,hVU⟩ := ZFSet.mem_sep.mp hVF
      obtain ⟨s,hs⟩ := (prefix_iff_wordCode w).mp ((mem_conditions w).mp hw)
      have hV : V = f s := (hAs s V).mp (hs.symm ▸ hwV)
      exact ⟨s,⟨p,hp,hV ▸ hpV⟩,hV ▸ hVU⟩
    · exact False.elim (hit_neg_excludes c U (code_lower c U hUc) G ⟨p,hp,hpN⟩ hGU)
  · rintro ⟨s,⟨p,hp,hps⟩,hsU⟩
    exact ⟨p,hp,hsU hps⟩

theorem hit_basic_iff (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (G : GenericFilter (Conditions c))
    (hG : AtomicForcing.GroundGeneric M G) (p : Conditions c) :
    Hit G (basicCode c (label c p)) ↔ p ∈ G.carrier := by
  have hpM := hM c hc _ (label_mem c p)
  have hsM := singleton_mem M hM hT.pairing hpM
  have he := hit_regular_iff M c (CohenInternalDecision.below c {label c p}) hM hT hc
    (CohenInternalDecision.below_mem M c _ hM hT hc hsM)
    (fun _ h => (ZFSet.mem_sep.mp h).1) (below_lower c _) G hG
  change Hit G (basicCode c (label c p)) ↔ _ at he
  rw [he]
  constructor
  · rintro ⟨q,hq,hqp⟩
    obtain ⟨_,r,hr,hrq⟩ := ZFSet.mem_sep.mp hqp
    have hrp := ZFSet.mem_singleton.mp hr
    have hqp : label c p ⊆ label c q := hrp ▸ hrq
    exact G.upper hqp hq
  · intro hp
    exact ⟨p,hp,ZFSet.mem_sep.mpr ⟨label_mem c p,label c p,ZFSet.mem_singleton.mpr rfl,
      fun _ h => h⟩⟩

end TuringRigidity.RegularTreeCofinality

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeRecovery
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeRecovery
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open RegularTreeCofinality InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem branchSet_mem (N B A g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hB : B ∈ N) (hA : A ∈ N) (hg : g ∈ N) : branchSet B A g ∈ N := by
  let e := cons B (cons A (fun _ => g))
  have he : ∀ i, e i ∈ N := by intro i; rcases i with _|_|i; exact hB; exact hA; exact hg
  simpa only [branchSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.pairMem 1 0 3) (.existsMem 4 (.member 0 1)))) e he
      (conditions_mem N hN hT)

theorem recoverySet_mem (N c B A S k w : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hB : B ∈ N) (hA : A ∈ N) (hS : S ∈ N) (hk : k ∈ N) (hw : w ∈ N) :
    recoverySet c B A S k w ∈ N := by
  let e := cons B (cons S (cons w (cons A (fun _ => k))))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|_|i; exact hB; exact hS; exact hw; exact hA; exact hk
  simpa only [recoverySet,Formula.Eval,Formula.eval_pairMem,Formula.eval_subset,
    cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.existsMem 5
        (.conj (.pairMem 0 2 7) (.conj (.pairMem 3 1 8) (.subset 2 1)))))) e he hc

variable (c : ZFSet.{0}) (f : List Bool → ZFSet.{0})
variable (hroot : f [] = c) (hcode : ∀ s, IsCode c (f s))
variable (hm : ∀ s t, s <+: t → f t ⊆ f s)
variable (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
  p ∉ f (a ++ [true] ++ v))
variable (G : GenericFilter (Conditions c))

theorem word_mem (s : List Bool) :
    wordCode s ∈ genericFilterSet conditions (pushFilter (RegularTreeFilter.branch c f hroot hcode hm hd G)).carrier ↔
      Hit G (f s) := by
  rw [mem_genericFilterSet]
  constructor
  · rintro ⟨p,hp,hps⟩
    have he : p = conditionEquiv ⟨s⟩ := label_injective conditions (hps.trans (label_encodeCondition ⟨s⟩).symm)
    subst p
    simpa only [pushFilter,OrderIso.symm_apply_apply,Set.mem_ofPred_eq,RegularTreeFilter.branch] using hp
  · intro h
    exact ⟨conditionEquiv ⟨s⟩,by simpa only [pushFilter,OrderIso.symm_apply_apply,Set.mem_ofPred_eq,RegularTreeFilter.branch] using h,
      label_encodeCondition ⟨s⟩⟩

theorem branchFilterSet_eq (B A : ZFSet.{0})
    (hfB : ∀ s, f s ∈ B)
    (hAs : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s) :
    genericFilterSet conditions (pushFilter (RegularTreeFilter.branch c f hroot hcode hm hd G)).carrier =
      branchSet B A (genericFilterSet c G.carrier) := by
  apply ZFSet.ext; intro w
  constructor
  · intro hw
    obtain ⟨p,_,he⟩ := (mem_genericFilterSet _ _ w).mp hw
    have hwc : w ∈ conditions := he ▸ label_mem conditions p
    obtain ⟨s,hs⟩ := (prefix_iff_wordCode w).mp ((mem_conditions w).mp hwc)
    have hhit := (word_mem c f hroot hcode hm hd G s).mp (hs.symm ▸ hw)
    obtain ⟨p,hp,hps⟩ := hhit
    exact ZFSet.mem_sep.mpr ⟨hwc,f s,hfB s,hs ▸ (hAs s _).mpr rfl,
      label c p,(mem_genericFilterSet c _ _).mpr ⟨p,hp,rfl⟩,hps⟩
  · intro hw
    obtain ⟨hwc,U,hUB,hwU,p,hpg,hpU⟩ := ZFSet.mem_sep.mp hw
    obtain ⟨s,hs⟩ := (prefix_iff_wordCode w).mp ((mem_conditions w).mp hwc)
    have hU := (hAs s U).mp (hs.symm ▸ hwU)
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet c _ p).mp hpg
    exact hs ▸ (word_mem c f hroot hcode hm hd G s).mpr ⟨p,hp,hU ▸ hpU⟩

theorem originalFilterSet_eq (M B A S k : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hB : B ∈ M) (hA : A ∈ M)
    (hfB : ∀ s, f s ∈ B) (hf0 : ∀ s, f s ≠ ∅)
    (hAs : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s)
    (hden : ∀ U, IsCode c U → U ≠ ∅ → ∃ s, f s ⊆ U)
    (hSs : ∀ p ∈ c, basicCode c p ∈ S)
    (hks : ∀ p ∈ c, ∀ U, ZFSet.pair p U ∈ k ↔ U = basicCode c p)
    (hG : AtomicForcing.GroundGeneric M G) :
    genericFilterSet c G.carrier = recoverySet c B A S k
      (genericFilterSet conditions (pushFilter (RegularTreeFilter.branch c f hroot hcode hm hd G)).carrier) := by
  apply ZFSet.ext; intro p
  constructor
  · intro hp
    obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet c _ p).mp hp
    have hhit := (hit_basic_iff M c hM hT hc G hG p).mpr hpG
    obtain ⟨s,hs,hsB⟩ := (hit_iff_node M c B A _ f hM hT hc hB hA
      (basicCode_mem M c _ hM hT hc (label_mem c p)) (regular_isCode c _)
      (fun s => ⟨hfB s,hcode s,hf0 s⟩) hAs hden G hG).mp hhit
    exact ZFSet.mem_sep.mpr ⟨label_mem c p,f s,hfB s,basicCode c (label c p),hSs _ (label_mem c p),
      wordCode s,(word_mem c f hroot hcode hm hd G s).mpr hs,(hAs s _).mpr rfl,
      (hks _ (label_mem c p) _).mpr rfl,hsB⟩
  · intro hp
    obtain ⟨hpc,U,_,V,_,s,hsw,hsU,hpV,hUV⟩ := ZFSet.mem_sep.mp hp
    obtain ⟨p,rfl⟩ := label_surjective c hpc
    have hV := (hks _ (label_mem c p) V).mp hpV
    obtain ⟨q,_,hqs⟩ := (mem_genericFilterSet _ _ s).mp hsw
    have hsc : s ∈ conditions := hqs ▸ label_mem conditions q
    obtain ⟨t,ht⟩ := (prefix_iff_wordCode s).mp ((mem_conditions s).mp hsc)
    have hU := (hAs t U).mp (ht.symm ▸ hsU)
    obtain ⟨r,hr,hrt⟩ := (word_mem c f hroot hcode hm hd G t).mp (ht.symm ▸ hsw)
    have hhit : Hit G (basicCode c (label c p)) := ⟨r,hr,hV ▸ hUV (hU.symm ▸ hrt)⟩
    exact (mem_genericFilterSet c _ _).mpr ⟨p,(hit_basic_iff M c hM hT hc G hG p).mp hhit,rfl⟩

end TuringRigidity.RegularTreeRecovery

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

theorem branch_extension_eq (M c B A : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hAf : FunctionGraph conditions B A)
    (hAs : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s)
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hroot : f [] = c)
    (hm : ∀ s t, s <+: t → f t ⊆ f s)
    (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
      p ∉ f (a ++ [true] ++ v))
    (hden : ∀ U, IsCode c U → U ≠ ∅ → ∃ s, f s ⊆ U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let W := pushFilter (RegularTreeFilter.branch c f hroot (fun s => (hf s).2.1) hm hd G)
    AtomicForcing.GroundGeneric M W ∧
      genericExtensionSet M conditions W.carrier = genericExtensionSet M c G.carrier := by
  let W := pushFilter (RegularTreeFilter.branch c f hroot (fun s => (hf s).2.1) hm hd G)
  have hW := branch_ground_generic M c B A f hM hT hBM hAM hAf hAs hf hroot hm hd hden G hG
  refine ⟨hW,?_⟩
  have hWM := conditions_mem M hM hT
  obtain ⟨hN,hTN,hMN,hgN⟩ := extension_properties M c hM hT hc G hG
  obtain ⟨hV,hTV,hMV,hwV⟩ := extension_properties M conditions hM hT hWM W hW
  obtain ⟨B',_,_,S,hSM,hSs,k,hkM,_,hks,_⟩ := CountedRegularBasis.internal_basis M c hM hT hc
  have hwN : genericFilterSet conditions W.carrier ∈ genericExtensionSet M c G.carrier := by
    rw [branchFilterSet_eq c f hroot (fun s => (hf s).2.1) hm hd G B A (fun s => (hf s).1) hAs]
    exact branchSet_mem _ B A _ hN hTN (hMN hBM) (hMN hAM) hgN
  have hgV : genericFilterSet c G.carrier ∈ genericExtensionSet M conditions W.carrier := by
    rw [originalFilterSet_eq c f hroot (fun s => (hf s).2.1) hm hd G M B A S k
      hM hT hc hBM hAM (fun s => (hf s).1) (fun s => (hf s).2.2) hAs hden
      (fun p hp => (hSs _).mpr ⟨p,hp,rfl⟩) hks hG]
    exact recoverySet_mem _ c B A S k _ hV hTV (hMV hc) (hMV hBM) (hMV hAM) (hMV hSM) (hMV hkM) hwV
  apply ZFSet.ext; intro x
  exact ⟨fun hx => InternalNameEvaluation.extension_subset M _ hN hTN hMN W.carrier hwN hx,
    fun hx => InternalNameEvaluation.extension_subset M _ hV hTV hMV G.carrier hgV hx⟩

end TuringRigidity.RegularTreeExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenAbsorptionGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAbsorptionGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalProjectedGeneric RegularBinaryTree
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem product_generic_absorption_oai (M q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hq : q ∈ M) (hct : InternallyCountable M q) :
    ∃ c ∈ M,
      (∀ z, z ∈ c ↔ ∃ p ∈ q, ∃ s ∈ CohenGroundPoset.conditions ZFSet.omega,
        z = TaggedProductConditions.code p s) ∧
      ∀ G : GenericFilter (Conditions c), AtomicForcing.GroundGeneric M G →
        ∃ W : GenericFilter (Conditions InternalCohen.conditions),
          AtomicForcing.GroundGeneric M W ∧
            genericExtensionSet M InternalCohen.conditions W.carrier =
              genericExtensionSet M c G.carrier := by
  obtain ⟨c,hc,hcs,_,_,B,hBM,hB,T,_,E,_,A,hAM,hAf,hAs,hpos,_,hm,hd,hden⟩ :=
    CohenAbsorptionTree.internal_dense_tree M q hM hT hq hct
  refine ⟨c,hc,hcs,?_⟩
  intro G hG
  have hBP := positive_mem M B hM hT hBM
  have hf : ∀ s, tree c B T E s ∈ positive B ∧
      IsCode c (tree c B T E s) ∧ tree c B T E s ≠ ∅ := by
    intro s
    have hp := ZFSet.mem_sep.mp (hpos s)
    exact ⟨hpos s,((hB _).mp hp.1).2,hp.2⟩
  have hr := tree_nil c B T E
  exact ⟨InternalCohen.pushFilter
      (RegularTreeFilter.branch c (tree c B T E) hr (fun s => (hf s).2.1) hm hd G),
    RegularTreeExtension.branch_extension_eq M c (positive B) A (tree c B T E)
      hM hT hc hBP hAM hAf hAs hf hr hm hd hden G hG⟩

end TuringRigidity.CohenAbsorptionGeneric

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption_oai := @OAI.TuringRigidity.CohenAbsorptionGeneric.product_generic_absorption_oai
