-- Prove2me | solution 1 for OAI.TuringRigidity.RealHullIteration.exists_iterated_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:10:18.353812+00:00
-- url     : https://prove2.me/submissions/917c5e4f-39af-4be2-ae00-4c760efaf66f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_CohenDisjointPrefixPair_exists_iterated_pair
import Theorems.Thm_OAI_TuringRigidity_TwoRealHull_joined_factorization

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableEnumeration
open TransitiveNameModel BoundedSetTheory InternalRelationSelection
open InternalCountableFiniteUnion InternalFiniteEnumeration

theorem enumeratesFormula_spec (ω E g : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega) :
    (enumeratesFormula ω E g).Eval e ↔ Enumerates (e E) (e g) := by
  simp only [enumeratesFormula,Enumerates,FunctionGraph,Formula.eval_disj,Formula.Eval,
    Formula.eval_empty,Formula.eval_functionGraph,Formula.eval_allMem,
    Formula.eval_pairMem,cons_zero,cons_succ,hω]

theorem enumerates_ranges (U E g : ZFSet.{0}) (hE : E ⊆ U) (hg : Enumerates E g) :
    Ranges U E g := by
  refine ⟨hE,fun x _ => ?_⟩
  rcases hg with ⟨rfl,rfl⟩|⟨hg,honto⟩
  · simp
  · refine ⟨fun hx => honto x hx,?_⟩
    rintro ⟨n,_,hn⟩
    obtain ⟨n',_,x',hx,hp⟩ := hg.1 _ hn
    exact (ZFSet.pair_inj.mp hp).2 ▸ hx

theorem enumerates_entry (U E g d k : ZFSet.{0}) (hE : E ⊆ U) (hg : Enumerates E g)
    (hd : d ∈ U) (hk : k ∈ ZFSet.omega) :
    ∃ x ∈ U, Entry U g d k x ∧ ∀ y ∈ U, Entry U g d k y → y = x := by
  rcases hg with ⟨_,rfl⟩|⟨hg,_⟩
  · exact ⟨d,hd,Or.inr ⟨rfl,fun y _ => ZFSet.notMem_empty _⟩,
      fun y _ hy => hy.elim (fun h => False.elim (ZFSet.notMem_empty _ h)) And.left⟩
  · obtain ⟨x,hx,hkx,_⟩ := hg.2 k hk
    refine ⟨x,hE hx,Or.inl hkx,?_⟩
    intro y _ hy
    rcases hy with hy|⟨_,hy⟩
    · exact hg.functional hk hy hkx
    · exact False.elim (hy x (hE hx) hkx)

theorem internal_countable_selector (M U S : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hU : U ∈ M) (hS : S ∈ M)
    (hsub : ∀ E ∈ S, E ⊆ U)
    (hct : ∀ E ∈ S, E = ∅ ∨ InternallyCountable M E) :
    ∃ C ∈ M, ∃ T ∈ M, FunctionGraph S C T ∧
      ∀ E ∈ S, ∀ g, ZFSet.pair E g ∈ T → Enumerates E g := by
  have hω := sourceT_omega_mem M hM hT
  have hp := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hω hU
  obtain ⟨C,hCM,hC⟩ := internal_power M hM hT.powerSet hp
  let e := cons S (cons C (fun _ => ZFSet.omega))
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (enumeratesFormula 5 1 0)))
  let R := (ZFSet.prod S C).sep (fun z => φ.Eval (cons z e))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hS; exact hCM; exact hω
  have hRM : R ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hS hCM)
  have hr (E g : ZFSet.{0}) : ZFSet.pair E g ∈ R ↔ E ∈ S ∧ g ∈ C ∧ Enumerates E g := by
    have henum (domain graph pair : ZFSet.{0}) :
        (enumeratesFormula 5 1 0).Eval (cons graph (cons domain (cons pair e))) ↔
          Enumerates domain graph := enumeratesFormula_spec 5 1 0 _ rfl
    simp only [R,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      henum,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,E',hE,g',hg,hp,hEnum⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
      exact ⟨hE,hg,hEnum⟩
    · rintro ⟨hE,hg,hEnum⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨E,hE,g,hg,rfl⟩,E,hE,g,hg,rfl,hEnum⟩
  have htotal : ∀ E ∈ S, ∃ g ∈ C, ZFSet.pair E g ∈ R := by
    intro E hE
    rcases hct E hE with hempty|⟨g,hgM,hg,honto⟩
    · have hzero : (∅ : ZFSet.{0}) ∈ M := hempty ▸ hM S hS E hE
      have hgC := (hC ∅).mpr ⟨hzero,fun _ h => False.elim (ZFSet.notMem_empty _ h)⟩
      exact ⟨∅,hgC,(hr E ∅).mpr ⟨hE,hgC,Or.inl ⟨hempty,rfl⟩⟩⟩
    · have hgC := (hC g).mpr ⟨hgM,by
        intro z hz
        obtain ⟨n,hn,x,hx,hz⟩ := hg.1 z hz
        exact ZFSet.mem_prod.mpr ⟨n,hn,x,hsub E hE hx,hz⟩⟩
      exact ⟨g,hgC,(hr E g).mpr ⟨hE,hgC,Or.inr ⟨hg,honto⟩⟩⟩
  obtain ⟨T,hTM,hfun,hTR⟩ := select_relation M S C R hM hT hS hCM hRM htotal
  exact ⟨C,hCM,T,hTM,hfun,fun E _ g hEg => ((hr E g).mp (hTR hEg)).2.2⟩

end TuringRigidity.InternalCountableEnumeration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableUnion
open TransitiveNameModel BoundedSetTheory InternalCountableFiniteUnion InternalCountableEnumeration

theorem internally_countable_union (M U S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (hS : S ∈ M)
    (hsub : ∀ H ∈ S, H ⊆ U) (hct : ∀ H ∈ S, H = ∅ ∨ InternallyCountable M H)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ S)
    (hB : orbitGraph E ∈ M) (hcover : ∀ p ∈ U, ∃ n, p ∈ E n)
    (hne : ∃ p, p ∈ U) : InternallyCountable M U := by
  classical
  obtain ⟨d,hd⟩ := hne
  obtain ⟨C,hCM,T,hTM,hTfun,hEnum⟩ := internal_countable_selector M U S hM hT hU hS hsub hct
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  let B := orbitGraph E
  have hchoice (n k : ℕ) : ∃ x ∈ U, ∃ g ∈ C,
      ZFSet.pair (E n) g ∈ T ∧ Entry U g d (natSet k) x ∧
        ∀ y ∈ U, Entry U g d (natSet k) y → y = x := by
    obtain ⟨g,hg,hEg,_⟩ := hTfun.2 _ (hE n)
    obtain ⟨x,hx,he,hu⟩ := enumerates_entry U (E n) g d (natSet k) (hsub _ (hE n))
      (hEnum _ (hE n) g hEg) hd ((mem_omega _).mpr ⟨k,rfl⟩)
    exact ⟨x,hx,g,hg,hEg,he,hu⟩
  choose v hv g hg hEg hentry huniq using hchoice
  let f : ℕ → ZFSet.{0} := fun i => v (Nat.unpair i).1 (Nat.unpair i).2
  let e := cons ZFSet.omega (cons Q (cons S (cons C (cons B (cons T (cons U (fun _ => d)))))))
  let φ : Formula := .existsMem 1 (.existsMem 8 (.conj (.orderedPair 2 1 0)
    (flattenFormula 3 4 5 6 7 8 9 10 1 0)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|_|i
    exact hω; exact hQM; exact hS
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
  have hr := enumerates_ranges U (E n) (g n 0) (hsub _ (hE n))
    (hEnum (E n) (hE n) (g n 0) (hEg n 0))
  obtain ⟨k,hk,hkp⟩ := (hr.2 p hp).mp hpE
  obtain ⟨k,rfl⟩ := (mem_omega k).mp hk
  have heq := hTfun.functional (hE n) (hEg n 0) (hEg n k)
  have hpv := huniq n k p hp (Or.inl (heq ▸ hkp))
  refine ⟨natSet (Nat.pair n k),(mem_omega _).mpr ⟨Nat.pair n k,rfl⟩,?_⟩
  apply (orbitGraph_pair f _ p).mpr
  simpa only [f,Nat.unpair_pair] using hpv

end TuringRigidity.InternalCountableUnion

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

theorem inverse_function (A B f : ZFSet.{0})
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) :
    FunctionGraph B A (inverse A B f) := by
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := hs y hy
    refine ⟨x,hx,(pair_inverse A B f y x).mpr ⟨hy,hx,hxy⟩,?_⟩
    intro x' hx' hyx'
    exact hi x' hx' x hx y hy ((pair_inverse A B f y x').mp hyx').2.2 hxy

theorem inverse_onto (A B f : ZFSet.{0}) (hf : FunctionGraph A B f) :
    ∀ x ∈ A, ∃ y ∈ B, ZFSet.pair y x ∈ inverse A B f := by
  intro x hx
  obtain ⟨y,hy,hxy,_⟩ := hf.2 x hx
  exact ⟨y,hy,(pair_inverse A B f y x).mpr ⟨hy,hx,hxy⟩⟩

theorem countable_of_bijection (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hfM : f ∈ M) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f)
    (hct : InternallyCountable M B) : InternallyCountable M A :=
  InternalCountableMap.countable_of_surjection M B A (inverse A B f) hM hT hB hA
    (inverse_mem M A B f hM hT hA hB hfM) (inverse_function A B f hi hs)
    (inverse_onto A B f hf) hct

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalProductBijection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalProductBijection
open TransitiveNameModel BoundedSetTheory

theorem pair_productGraph (A B W f u v : ZFSet.{0}) :
    ZFSet.pair u v ∈ productGraph A B W f ↔
      ∃ x ∈ A, ∃ y ∈ B, ∃ n ∈ W, u = ZFSet.pair x n ∧ v = ZFSet.pair y n ∧ ZFSet.pair x y ∈ f := by
  simp only [productGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,u',_,v',_,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact h
  · intro h
    obtain ⟨x,hx,y,hy,n,hn,rfl,rfl,hxy⟩ := h
    have hu := ZFSet.pair_mem_prod.mpr ⟨hx,hn⟩
    have hv := ZFSet.pair_mem_prod.mpr ⟨hy,hn⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hu,hv⟩,_,hu,_,hv,rfl,x,hx,y,hy,n,hn,rfl,rfl,hxy⟩

theorem productGraph_mem (M A B W f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hW : W ∈ M) (hf : f ∈ M) : productGraph A B W f ∈ M := by
  have hAW := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hW
  have hBW := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hB hW
  let e := cons (ZFSet.prod A W) (cons (ZFSet.prod B W) (cons A (cons B (cons W (fun _ => f)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact hAW; exact hBW; exact hA; exact hB; exact hW; exact hf
  simpa only [productGraph,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
        (.existsMem 5 (.existsMem 7 (.existsMem 9 (.conj (.orderedPair 4 2 0)
          (.conj (.orderedPair 3 1 0) (.pairMem 2 1 11))))))))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hAW hBW)

theorem productGraph_function (A B W f : ZFSet.{0}) (hf : FunctionGraph A B f) :
    FunctionGraph (ZFSet.prod A W) (ZFSet.prod B W) (productGraph A B W f) := by
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro u hu
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hu
    obtain ⟨y,hy,hxy,_⟩ := hf.2 x hx
    refine ⟨ZFSet.pair y n,ZFSet.pair_mem_prod.mpr ⟨hy,hn⟩,
      (pair_productGraph A B W f _ _).mpr ⟨x,hx,y,hy,n,hn,rfl,rfl,hxy⟩,?_⟩
    intro v _ hv
    obtain ⟨x',_,y',_,n',_,he,rfl,hxy'⟩ := (pair_productGraph A B W f _ v).mp hv
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    rw [hf.functional hx hxy' hxy]

theorem productGraph_injective (A B W f : ZFSet.{0})
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') :
    ∀ u ∈ ZFSet.prod A W, ∀ u' ∈ ZFSet.prod A W, ∀ v ∈ ZFSet.prod B W,
      ZFSet.pair u v ∈ productGraph A B W f → ZFSet.pair u' v ∈ productGraph A B W f → u = u' := by
  intro u _ u' _ v _ huv hu'v
  obtain ⟨x,hx,y,hy,n,_,rfl,rfl,hxy⟩ := (pair_productGraph A B W f u v).mp huv
  obtain ⟨x',hx',y',_,n',_,rfl,he,hx'y⟩ := (pair_productGraph A B W f u' _).mp hu'v
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  rw [hi x hx x' hx' y hy hxy hx'y]

theorem productGraph_onto (A B W f : ZFSet.{0})
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) :
    ∀ v ∈ ZFSet.prod B W, ∃ u ∈ ZFSet.prod A W, ZFSet.pair u v ∈ productGraph A B W f := by
  intro v hv
  obtain ⟨y,hy,n,hn,rfl⟩ := ZFSet.mem_prod.mp hv
  obtain ⟨x,hx,hxy⟩ := hs y hy
  exact ⟨ZFSet.pair x n,ZFSet.pair_mem_prod.mpr ⟨hx,hn⟩,
    (pair_productGraph A B W f _ _).mpr ⟨x,hx,y,hy,n,hn,rfl,rfl,hxy⟩⟩

end TuringRigidity.InternalProductBijection

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

theorem countable_sUnion (M S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hS : S ∈ M) (hcount : S = ∅ ∨ InternallyCountable M S)
    (hsets : ∀ A ∈ S, A = ∅ ∨ InternallyCountable M A) :
    ZFSet.sUnion S = ∅ ∨ InternallyCountable M (ZFSet.sUnion S) := by
  classical
  by_cases hne : ∃ x, x ∈ ZFSet.sUnion S
  · right
    rcases hcount with rfl|⟨B,hBM,hB,honto⟩
    · simp at hne
    obtain ⟨E,hE,hEB⟩ := sequence_of_graph S B hB
    apply InternalCountableUnion.internally_countable_union M (ZFSet.sUnion S) S hM hT
      (union_mem M hM hT.union hS) hS
      (fun A hA x hx => ZFSet.mem_sUnion.mpr ⟨A,hA,hx⟩) hsets E hE (hEB.symm ▸ hBM) _ hne
    intro x hx
    obtain ⟨A,hA,hxA⟩ := ZFSet.mem_sUnion.mp hx
    obtain ⟨n,hn,hnA⟩ := honto A hA
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    have he : A = E n := (orbitGraph_pair E n A).mp (hEB.symm ▸ hnA)
    exact ⟨n,he ▸ hxA⟩
  · left
    apply ZFSet.ext; intro x
    exact ⟨fun hx => False.elim (hne ⟨x,hx⟩),fun hx => False.elim (ZFSet.notMem_empty x hx)⟩

end TuringRigidity.InternalCountableFamily

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

theorem pair_countable (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) : InternallyCountable M ({a,b} : ZFSet.{0}) := by
  apply finite_countable M {a,b} hM hT (pair_mem M hM hT.pairing ha hb)
  · simpa only [ZFSet.coe_insert,ZFSet.coe_singleton] using (Set.finite_singleton b).insert a
  · exact ⟨a,ZFSet.mem_pair.mpr (Or.inl rfl)⟩

theorem countable_union (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M)
    (hcA : A = ∅ ∨ InternallyCountable M A) (hcB : B = ∅ ∨ InternallyCountable M B) :
    A ∪ B = ∅ ∨ InternallyCountable M (A ∪ B) := by
  have h := InternalCountableFamily.countable_sUnion M {A,B} hM hT
    (pair_mem M hM hT.pairing hA hB) (Or.inr (pair_countable M A B hM hT hA hB))
    (fun E hE => (ZFSet.mem_pair.mp hE).elim (fun h => h ▸ hcA) (fun h => h ▸ hcB))
  simpa only [ZFSet.sUnion_pair] using h

theorem countable_insert (M A a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (ha : a ∈ M) (hcA : A = ∅ ∨ InternallyCountable M A) :
    InternallyCountable M (insert a A) := by
  have he : ({a} : ZFSet.{0}) ∪ A = insert a A := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_insert_iff]
  have h := countable_union M {a} A hM hT (singleton_mem M hM hT.pairing ha) hA
    (Or.inr (singleton_countable M a hM hT ha)) hcA
  rw [he] at h
  rcases h with h|h
  · exact False.elim (ZFSet.notMem_empty a (h ▸ ZFSet.mem_insert a A))
  · exact h

end TuringRigidity.InternalCountableClosure

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableOrdinals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableOrdinals
open TransitiveNameModel BoundedSetTheory InternalCountableClosure

theorem nonempty (M K : ZFSet.{0}) (hK : FirstUncountable M K) : ∃ x, x ∈ K := by
  classical
  by_contra h
  apply hK.2.2.1; left
  apply ZFSet.ext; intro x
  exact ⟨fun hx => False.elim (h ⟨x,hx⟩),fun hx => False.elim (ZFSet.notMem_empty x hx)⟩

end TuringRigidity.InternalCountableOrdinals

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderType
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem value_isOrdinal {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) (x : ZFSet.{u}) (hx : x ∈ d) :
    (value d r wf x).IsOrdinal := by
  induction x using wf.induction with
  | h x ih =>
    apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
    constructor
    · intro y hy z hz
      obtain ⟨b,hb,hbx,rfl⟩ := (mem_value d r wf x y).mp hy
      obtain ⟨a,ha,hab,rfl⟩ := (mem_value d r wf b z).mp hz
      exact (mem_value d r wf x _).mpr ⟨a,ha,ht a ha b hb x hx hab hbx,rfl⟩
    · intro y hy
      obtain ⟨a,ha,hax,rfl⟩ := (mem_value d r wf x y).mp hy
      exact ih a ⟨ha,hax⟩ ha

theorem total_extensional {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TotalOn d r) : Extensional d r := by
  intro x hx y hy he
  rcases ht x hx y hy with h|h|h
  · exact h
  · exact False.elim (wf.irrefl.irrefl x ⟨hx,(he x hx).mpr h⟩)
  · exact False.elim (wf.irrefl.irrefl y ⟨hy,(he y hy).mp h⟩)

theorem mem_ordinalRange (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) (z : ZFSet.{u}) :
    z ∈ ordinalRange d r wf ↔ ∃ x ∈ d, z = value d r wf x := by
  rw [ordinalRange,ZFSet.mem_range]
  constructor
  · rintro ⟨s,hs⟩; exact ⟨label d s,label_mem d s,hs.symm⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨s,rfl⟩ := label_surjective d hx
    exact ⟨s,rfl⟩

theorem ordinalRange_isOrdinal {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) : (ordinalRange d r wf).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro x hx y hy
    obtain ⟨a,_,rfl⟩ := (mem_ordinalRange d r wf x).mp hx
    obtain ⟨b,hb,_,rfl⟩ := (mem_value d r wf a y).mp hy
    exact (mem_ordinalRange d r wf _).mpr ⟨b,hb,rfl⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := (mem_ordinalRange d r wf x).mp hx
    exact value_isOrdinal wf ht a ha

theorem orderType_toZFSet {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) : (orderType d r wf).toZFSet = ordinalRange d r wf :=
  (ordinalRange_isOrdinal wf ht).toZFSet_rank_eq

theorem orderType_internal (M d r : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) :
    (orderType d r wf).toZFSet ∈ M ∧
      ∃ f ∈ M, Graph d r d (orderType d r wf).toZFSet f ∧
        ∀ z ∈ (orderType d r wf).toZFSet, ∃ x ∈ d, ZFSet.pair x z ∈ f := by
  obtain ⟨f,hf,hg⟩ := internal_graph M d r hM hP hU hPow hS hR hd hr wf
  have heq : graphRange d f = ordinalRange d r wf := by
    apply ZFSet.ext; intro z
    exact (hg.range_iff wf z).trans (mem_ordinalRange d r wf z).symm
  have hm : ordinalRange d r wf ∈ M := heq ▸ graphRange_mem M hM hU hS hd hf
  rw [orderType_toZFSet wf ht]
  refine ⟨hm,f,hf,?_,?_⟩
  · refine ⟨(fun _ hx => hx),(fun _ _ _ hy _ => hy),?_,?_,?_⟩
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := (hg.mem_iff wf z).mp hz
      exact ⟨x,hx,_,(mem_ordinalRange d r wf _).mpr ⟨x,hx,rfl⟩,rfl⟩
    · intro x hx
      refine ⟨value d r wf x,(mem_ordinalRange d r wf _).mpr ⟨x,hx,rfl⟩,
        (hg.mem_iff wf _).mpr ⟨x,hx,rfl⟩,?_⟩
      intro z _ hxz
      obtain ⟨y,_,he⟩ := (hg.mem_iff wf _).mp hxz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      rfl
    · intro x hx z _ hxz
      obtain ⟨y,hy,he⟩ := (hg.mem_iff wf _).mp hxz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      constructor
      · intro z hz
        obtain ⟨y,hy,hyx,rfl⟩ := (mem_value d r wf x z).mp hz
        exact ⟨y,hy,hyx,(hg.mem_iff wf _).mpr ⟨y,hy,rfl⟩⟩
      · intro y hy hyx z _ hyz
        obtain ⟨w,_,he⟩ := (hg.mem_iff wf _).mp hyz
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
        exact (mem_value d r wf x _).mpr ⟨y,hy,hyx,rfl⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (mem_ordinalRange d r wf z).mp hz
    exact ⟨x,hx,(hg.mem_iff wf _).mpr ⟨x,hx,rfl⟩⟩

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalOrdinalSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalOrdinalSubset
open TransitiveNameModel BoundedSetTheory RelationCollapse

theorem memberOrder_mem (M D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hD : D ∈ M) : memberOrder D ∈ M := by
  simpa only [memberOrder,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.member 1 0))))
      (fun _ => D) (fun _ => hD)
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hD hD)

theorem memberOrder_transitive (K D : ZFSet.{0}) (hK : K.IsOrdinal) (hD : D ⊆ K) :
    TransitiveOn D (memberOrder D) := by
  intro x hx y _ z hz hxy hyz
  exact (pair_memberOrder D x z).mpr ⟨hx,hz,(hK.mem (hD hz)).mem_trans
    ((pair_memberOrder D x y).mp hxy).2.2 ((pair_memberOrder D y z).mp hyz).2.2⟩

theorem memberOrder_total (K D : ZFSet.{0}) (hK : K.IsOrdinal) (hD : D ⊆ K) :
    TotalOn D (memberOrder D) := by
  intro x hx y hy
  rcases (hK.mem (hD hx)).mem_trichotomous (hK.mem (hD hy)) with h|h|h
  · exact Or.inr (Or.inl ((pair_memberOrder D x y).mpr ⟨hx,hy,h⟩))
  · exact Or.inl h
  · exact Or.inr (Or.inr ((pair_memberOrder D y x).mpr ⟨hy,hx,h⟩))

theorem value_subset (K D x : ZFSet.{0}) (hK : K.IsOrdinal) (hD : D ⊆ K) (hx : x ∈ D) :
    value D (memberOrder D) (memberOrder_wf D) x ⊆ x := by
  induction x using (memberOrder_wf D).induction with
  | h x ih =>
    intro z hz
    obtain ⟨y,hy,hyx,rfl⟩ := (mem_value D _ _ x z).mp hz
    have hv := value_isOrdinal (memberOrder_wf D) (memberOrder_transitive K D hK hD) y hy
    have hs := (hv.subset_iff_eq_or_mem (hK.mem (hD hy))).mp (ih y ⟨hy,hyx⟩ hy)
    have hyx' := ((pair_memberOrder D y x).mp hyx).2.2
    exact hs.elim (fun h => h.symm ▸ hyx')
      (fun h => (hK.mem (hD hx)).mem_trans h hyx')

theorem range_subset (K D : ZFSet.{0}) (hK : K.IsOrdinal) (hD : D ⊆ K) :
    ordinalRange D (memberOrder D) (memberOrder_wf D) ⊆ K := by
  intro z hz
  obtain ⟨x,hx,rfl⟩ := (mem_ordinalRange D _ _ z).mp hz
  exact (value_isOrdinal (memberOrder_wf D) (memberOrder_transitive K D hK hD) x hx).mem_of_subset_of_mem
    hK (value_subset K D x hK hD hx) (hD hx)

theorem internal_subset_orderType (M K D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K.IsOrdinal) (hD : D ∈ M) (hDK : D ⊆ K) :
    ∃ J ∈ M, J.IsOrdinal ∧ J ⊆ K ∧ ∃ f ∈ M, FunctionGraph D J f ∧
      (∀ x ∈ D, ∀ x' ∈ D, ∀ y ∈ J, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') ∧
      (∀ y ∈ J, ∃ x ∈ D, ZFSet.pair x y ∈ f) := by
  let wf := memberOrder_wf D
  have ht := memberOrder_transitive K D hK hDK
  obtain ⟨hJ,f,hf,hg,honto⟩ := orderType_internal M D (memberOrder D) hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hD
    (memberOrder_mem M D hM hT hD) wf ht
  refine ⟨(orderType D (memberOrder D) wf).toZFSet,hJ,ZFSet.isOrdinal_toZFSet _,?_,f,hf,?_,?_,honto⟩
  · rw [orderType_toZFSet wf ht]
    exact range_subset K D hK hDK
  · exact ⟨hg.2.2.1,hg.2.2.2.1⟩
  · intro x hx x' hx' y hy hxy hx'y
    apply value_injective wf (total_extensional wf (memberOrder_total K D hK hDK)) x hx x' hx'
    exact (hg.correct wf x hx y hy hxy).symm.trans (hg.correct wf x' hx' y hy hx'y)

end TuringRigidity.InternalOrdinalSubset

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalUncountableComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalUncountableComplement
open TransitiveNameModel BoundedSetTheory InternalCountableOrdinals InternalCountableClosure

theorem difference_mem (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hC : C ∈ M) : K \ C ∈ M := by
  simpa only [ZFSet.sep_notMem,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.neg (.member 0 1))
      (fun _ => C) (fun _ => hC) hK

theorem difference_uncountable (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hunc : ¬ (K = ∅ ∨ InternallyCountable M K)) (hC : C ∈ M)
    (hCK : C ⊆ K) (hct : C = ∅ ∨ InternallyCountable M C) :
    ¬ (K \ C = ∅ ∨ InternallyCountable M (K \ C)) := by
  classical
  intro h
  have hc := countable_union M C (K \ C) hM hT hC (difference_mem M K C hM hT hK hC) hct h
  have he : C ∪ (K \ C) = K := by
    apply ZFSet.ext; intro x
    rw [ZFSet.mem_union,ZFSet.mem_sdiff]
    exact ⟨fun h => h.elim (fun h => hCK h) And.left,
      fun h => (Classical.em (x ∈ C)).elim Or.inl (fun hn => Or.inr ⟨h,hn⟩)⟩
  exact hunc (he ▸ hc)

theorem uncountable_subset_bijection (M K D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hD : D ∈ M) (hDK : D ⊆ K)
    (hunc : ¬ (D = ∅ ∨ InternallyCountable M D)) :
    ∃ f ∈ M, FunctionGraph D K f ∧
      (∀ x ∈ D, ∀ x' ∈ D, ∀ y ∈ K, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') ∧
      (∀ y ∈ K, ∃ x ∈ D, ZFSet.pair x y ∈ f) := by
  obtain ⟨J,hJM,hJ,hJK,f,hfM,hf,hi,hs⟩ :=
    InternalOrdinalSubset.internal_subset_orderType M K D hM hT hK.1 hD hDK
  have huncJ : ¬ (J = ∅ ∨ InternallyCountable M J) := by
    rintro (rfl|hct)
    · apply hunc; left
      apply ZFSet.ext; intro x
      constructor
      · intro hx
        obtain ⟨y,hy,_,_⟩ := hf.2 x hx
        exact False.elim (ZFSet.notMem_empty y hy)
      · intro hx; exact False.elim (ZFSet.notMem_empty x hx)
    · exact hunc (Or.inr (InternalInverseGraph.countable_of_bijection M D J f hM hT hD hJM hfM hf hi hs hct))
  have he : J = K := by
    rcases (hJ.subset_iff_eq_or_mem hK.1).mp hJK with h|h
    · exact h
    · exact False.elim (huncJ (hK.2.2.2 J h))
  exact he ▸ ⟨f,hfM,hf,hi,hs⟩

theorem complement_bijection (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
    (hct : C = ∅ ∨ InternallyCountable M C) :
    ∃ f ∈ M, FunctionGraph (K \ C) K f ∧
      (∀ x ∈ K \ C, ∀ x' ∈ K \ C, ∀ y ∈ K,
        ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') ∧
      (∀ y ∈ K, ∃ x ∈ K \ C, ZFSet.pair x y ∈ f) :=
  uncountable_subset_bijection M K (K \ C) hM hT hK
    (difference_mem M K C hM hT hK.2.1 hC)
    (fun _ h => (ZFSet.mem_sdiff.mp h).1)
    (difference_uncountable M K C hM hT hK.2.1 hK.2.2.1 hC hCK hct)

end TuringRigidity.InternalUncountableComplement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenUnusedColumns
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenUnusedColumns
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open InternalCountableOrdinals InternalUncountableComplement InternalProductBijection
open CohenGroundPoset InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem unused_columns_forcing (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
    (hct : C = ∅ ∨ InternallyCountable M C) :
    ∃ f ∈ M, FunctionGraph (K \ C) K f ∧
      (∀ x ∈ K \ C, ∀ x' ∈ K \ C, ∀ y ∈ K,
        ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') ∧
      (∀ y ∈ K, ∃ x ∈ K \ C, ZFSet.pair x y ∈ f) ∧
      productGraph (K \ C) K ZFSet.omega f ∈ M ∧
      ∃ e : Conditions (conditions (ZFSet.prod (K \ C) ZFSet.omega)) ≃o
          Conditions (conditions (ZFSet.prod K ZFSet.omega)),
        ∃ g ∈ M, (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ g ↔ q = e p) ∧
          conditions (ZFSet.prod (K \ C) ZFSet.omega) ∈ M ∧
          InternalCollapse.orderSet (conditions (ZFSet.prod (K \ C) ZFSet.omega)) ∈ M ∧
          conditions (ZFSet.prod K ZFSet.omega) ∈ M ∧
          InternalCollapse.orderSet (conditions (ZFSet.prod K ZFSet.omega)) ∈ M := by
  obtain ⟨f,hfM,hf,hi,hs⟩ := complement_bijection M K C hM hT hK hC hCK hct
  have hD := difference_mem M K C hM hT hK.2.1 hC
  have hω := sourceT_omega_mem M hM hT
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hD hω
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hK.2.1 hω
  have hF := productGraph_mem M (K \ C) K ZFSet.omega f hM hT hD hK.2.1 hω hfM
  obtain ⟨e,hg,hge,horders⟩ := InternalCohenReindex.internal_reindex M _ _ _ hM hT hA hB hF
    (productGraph_function _ _ _ _ hf) (productGraph_injective _ _ _ _ hi) (productGraph_onto _ _ _ _ hs)
  exact ⟨f,hfM,hf,hi,hs,hF,e,_,hg,hge,horders⟩

end TuringRigidity.InternalCohenUnusedColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSingletonColumn
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
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

theorem internal_column_iso (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (ha : a ∈ M) :
    ∃ e : Conditions (conditions (ZFSet.prod {a} ZFSet.omega)) ≃o
        Conditions (conditions ZFSet.omega),
      ∃ f ∈ M, ∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ f ↔ q = e p := by
  have hW := sourceT_omega_mem M hM hT
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hW
  obtain ⟨e,hf,hfe,_⟩ := InternalCohenReindex.internal_reindex M _ _ (graph a ZFSet.omega)
    hM hT hA hW (graph_mem M a _ hM hT ha hW) (graph_function a _)
    (graph_injective a _) (graph_onto a _)
  exact ⟨e,_,hf,hfe⟩

end TuringRigidity.InternalSingletonColumn

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFreshColumn
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenFreshColumn
open TransitiveNameModel BoundedSetTheory InternalCountableOrdinals InternalCountableClosure
open InternalUncountableComplement CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem product_difference (K C W : ZFSet.{0}) :
    ZFSet.prod K W \ ZFSet.prod C W = ZFSet.prod (K \ C) W := by
  apply ZFSet.ext; intro z
  constructor
  · intro hz
    obtain ⟨hzK,hzC⟩ := ZFSet.mem_sdiff.mp hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hzK
    exact ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_sdiff.mpr ⟨hx,fun h =>
      hzC (ZFSet.pair_mem_prod.mpr ⟨h,hn⟩)⟩,hn⟩
  · intro hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨hxK,hxC⟩ := ZFSet.mem_sdiff.mp hx
    exact ZFSet.mem_sdiff.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hxK,hn⟩,
      fun h => hxC (ZFSet.pair_mem_prod.mp h).1⟩

theorem difference_singleton (K C a : ZFSet.{0}) :
    (K \ C) \ {a} = K \ insert a C := by
  apply ZFSet.ext; intro z
  simp only [ZFSet.mem_sdiff,ZFSet.mem_singleton,ZFSet.mem_insert_iff]
  tauto

theorem fresh_column (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
    (hct : C = ∅ ∨ InternallyCountable M C) :
    ∃ a ∈ K \ C,
      ZFSet.prod {a} ZFSet.omega ⊆ ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega ∧
      (ZFSet.prod K ZFSet.omega \ ZFSet.prod C ZFSet.omega) \ ZFSet.prod {a} ZFSet.omega =
        ZFSet.prod (K \ insert a C) ZFSet.omega ∧
      ∃ e : Conditions (conditions (ZFSet.prod {a} ZFSet.omega)) ≃o Conditions (conditions ZFSet.omega),
      ∃ f ∈ M, (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ f ↔ q = e p) ∧
      ∃ eR : Conditions (conditions (ZFSet.prod (K \ insert a C) ZFSet.omega)) ≃o
          Conditions (conditions (ZFSet.prod K ZFSet.omega)),
      ∃ g ∈ M, ∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ g ↔ q = eR p := by
  classical
  have hunc := difference_uncountable M K C hM hT hK.2.1 hK.2.2.1 hC hCK hct
  have hne : ∃ a, a ∈ K \ C := by
    by_contra hn
    apply hunc; left
    apply ZFSet.ext; intro a
    exact ⟨fun ha => False.elim (hn ⟨a,ha⟩),fun ha => False.elim (ZFSet.notMem_empty a ha)⟩
  obtain ⟨a,ha⟩ := hne
  have haK := (ZFSet.mem_sdiff.mp ha).1
  have haM := hM K hK.2.1 a haK
  have hCi : insert a C ∈ M := by
    have hi : insert a C = ({a} : ZFSet.{0}) ∪ C := by
      apply ZFSet.ext; intro z
      simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
    rw [hi]
    exact binary_union_mem M hM hT.pairing hT.union (singleton_mem M hM hT.pairing haM) hC
  have hiK : insert a C ⊆ K := by
    intro x hx
    exact (ZFSet.mem_insert_iff.mp hx).elim (fun he => he ▸ haK) (fun hx => hCK hx)
  obtain ⟨e,f,hf,hfe⟩ := InternalSingletonColumn.internal_column_iso M a hM hT haM
  obtain ⟨_,_,_,_,_,_,eR,g,hg,hge,_⟩ := InternalCohenUnusedColumns.unused_columns_forcing
    M K (insert a C) hM hT hK hCi hiK (Or.inr (countable_insert M C a hM hT hC haM hct))
  refine ⟨a,ha,?_,?_,e,f,hf,hfe,eR,g,hg,hge⟩
  · intro z hz
    obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hz
    have hx_eq : x = a := ZFSet.mem_singleton.mp hx
    subst x
    rw [product_difference]
    exact ZFSet.pair_mem_prod.mpr ⟨ha,hn⟩
  · rw [product_difference,product_difference,difference_singleton]

end TuringRigidity.CohenFreshColumn

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealHullIteration
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RealHullIteration
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals RealGeneratedModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_iterated_pair_oai (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X Y : Oracle)
    (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) :
    let N := RealGeneratedModel.hull M (realCode X)
    let H := RealGeneratedModel.hull N (realCode Y)
    Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧ ∃ L R : Oracle,
      realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
      realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric H (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
      GroundGeneric (genericExtensionSet H InternalCohen.conditions
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) := by
  dsimp only
  obtain ⟨hN,hH,U,hU,hUE⟩ := TwoRealHull.joined_factorization M K hM hT hK G hG X Y hX hY
  obtain ⟨a,ha⟩ := InternalCountableOrdinals.nonempty M K hK
  have haM := hM K hK.2.1 a ha
  have hsingle := singleton_mem M hM hT.pairing haM
  have hsub : ({a} : ZFSet.{0}) ⊆ K := fun _ h => (ZFSet.mem_singleton.mp h) ▸ ha
  obtain ⟨b,hb,_,_,_⟩ := CohenFreshColumn.fresh_column M K {a} hM hT hK hsingle hsub
    (Or.inr (InternalCountableClosure.singleton_countable M a hM hT haM))
  have hbK := (ZFSet.mem_sdiff.mp hb).1
  have hba : b ≠ a := fun he => (ZFSet.mem_sdiff.mp hb).2 (ZFSet.mem_singleton.mpr he)
  obtain ⟨L,R,hLE,hRE,hL,hR⟩ := CohenDisjointPrefixPair.exists_iterated_pair
    _ K a b hH.1 hH.2.1 (hH.2.2.1 (hN.2.2.1 hK.2.1)) ha hbK hba U hU
  exact ⟨hN,hH,L,R,hUE ▸ hLE,hUE ▸ hRE,hL,hR⟩

end TuringRigidity.RealHullIteration

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RealHullIteration.exists_iterated_pair_oai := @OAI.TuringRigidity.RealHullIteration.exists_iterated_pair_oai
