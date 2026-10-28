-- Prove2me | solution 1 for OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:58:50.301254+00:00
-- url     : https://prove2.me/submissions/8ef35935-656e-41fd-9aa6-5586065704ae

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenSymmetry
open Set CountableForcing

variable {ι : Type*}

theorem merge_le_left (p q : Condition ι) : merge p q ≤ p := by
  intro i b hb
  simp [merge,hb]

theorem merge_le_right {p q : Condition ι} (h : Compatible p q) : merge p q ≤ q := by
  intro i b hb
  cases hp : p.val i with
  | none => simp [merge,hp,hb]
  | some a => simpa [merge,hp] using congrArg some (h i a b hp hb)

end TuringRigidity.CohenSymmetry

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenCoordinates
open Set CohenSymmetry
universe u v
variable {ι : Type u} {κ : Type v}

theorem support_erase [DecidableEq ι] (p : Condition ι) (i : ι) :
    support (erase i p) = (support p).erase i := by
  classical
  ext j
  by_cases h : j = i <;> simp [mem_support,erase,h]

theorem erase_injective_on (i : ι) (b : Bool) :
    Set.InjOn (erase i) {p : Condition ι | p.val i = some b} := by
  intro p hp q hq he
  apply Condition.ext
  funext j
  by_cases h : j = i
  · subst j
    exact hp.trans hq.symm
  · have := congrArg (fun r : Condition ι => r.val j) he
    simpa [erase,h] using this

theorem compatible_of_erase (i : ι) (b : Bool) {p q : Condition ι}
    (hp : p.val i = some b) (hq : q.val i = some b)
    (h : Compatible (erase i p) (erase i q)) : Compatible p q := by
  intro j a c ha hc
  by_cases hj : j = i
  · have hab : a = b := Option.some.inj (ha.symm.trans (hj ▸ hp))
    have hcb : c = b := Option.some.inj (hc.symm.trans (hj ▸ hq))
    exact hab.trans hcb.symm
  · exact h j a c (by simpa [erase,hj] using ha) (by simpa [erase,hj] using hc)

end TuringRigidity.CohenCoordinates

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenChainCondition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenChainCondition
open Set CohenSymmetry CohenCoordinates
universe u
variable {ι : Type u}

theorem bounded_antichain_finite (n : ℕ) (A : Set (Condition ι))
    (hA : Antichain A) (hn : ∀ p ∈ A, (support p).card ≤ n) : A.Finite := by
  classical
  induction n generalizing A with
  | zero =>
    apply Set.finite_singleton (⊤ : Condition ι) |>.subset
    intro p hp
    have hzero : support p = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hn p hp))
    have he : p = ⊤ := by
      apply Condition.ext
      funext i
      have hi : p.val i = none := by
        by_contra hi
        have := (mem_support p i).mpr hi
        simp [hzero] at this
      exact hi
    exact he
  | succ n ih =>
    by_cases hempty : A = ∅
    · simp [hempty]
    obtain ⟨p,hp⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    let slice (i : ι) (b : Bool) : Set (Condition ι) := {q ∈ A | q.val i = some b}
    have hs (i : ι) (b : Bool) : (slice i b).Finite := by
      have he : (erase i '' slice i b).Finite := by
        apply ih
        · intro r hr s hs hrs
          obtain ⟨q,hq,rfl⟩ := hr
          obtain ⟨t,ht,rfl⟩ := hs
          intro hcomp
          exact hA hq.1 ht.1 (fun h => hrs (congrArg (erase i) h))
            (compatible_of_erase i b hq.2 ht.2 hcomp)
        · rintro r ⟨q,hq,rfl⟩
          rw [support_erase,Finset.card_erase_of_mem]
          · have := hn q hq.1
            have hpos : 0 < (support q).card := Finset.card_pos.mpr
              ⟨i,(mem_support q i).mpr (by simp [hq.2])⟩
            omega
          · exact (mem_support q i).mpr (by simp [hq.2])
      exact he.of_finite_image ((erase_injective_on i b).mono (fun _ h => h.2))
    apply (Set.finite_singleton p |>.union
      (p.finite.biUnion (fun i _ => Set.finite_univ.biUnion (fun b _ => hs i b)))).subset
    intro q hq
    by_cases he : q = p
    · exact Or.inl he
    · right
      have hc := hA hp hq (Ne.symm he)
      have hw : ∃ i a b, p.val i = some a ∧ q.val i = some b := by
        by_contra hw
        apply hc
        intro i a b ha hb
        exact False.elim (hw ⟨i,a,b,ha,hb⟩)
      obtain ⟨i,a,b,ha,hb⟩ := hw
      exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
        ⟨(by simp [ha]),Set.mem_iUnion.mpr
          ⟨b,Set.mem_iUnion.mpr ⟨Set.mem_univ b,⟨hq,hb⟩⟩⟩⟩⟩

theorem antichain_countable (A : Set (Condition ι)) (hA : Antichain A) :
    A.Countable := by
  have h (n : ℕ) : {p ∈ A | (support p).card ≤ n}.Countable :=
    (bounded_antichain_finite n _ (hA.mono (fun _ h => h.1)) (fun _ h => h.2)).countable
  apply (Set.countable_iUnion h).mono
  intro p hp
  exact Set.mem_iUnion.mpr ⟨(support p).card,hp,le_rfl⟩

end TuringRigidity.CohenChainCondition

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenNiceNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenNiceNames
open Set CountableForcing CohenSymmetry CohenCoordinates CohenChainCondition
universe u
variable {ι : Type u}

theorem compatible_symm {p q : Condition ι} (h : Compatible p q) : Compatible q p :=
  fun i a b ha hb => (h i b a hb ha).symm

theorem compatible_refl (p : Condition ι) : Compatible p p :=
  fun _ _ _ ha hb => Option.some.inj (ha.symm.trans hb)

theorem countable_predense_antichain (U : Set (Condition ι)) :
    ∃ A ⊆ U, Antichain A ∧ A.Countable ∧
      ∀ p ∈ U, ∃ a ∈ A, Compatible p a := by
  classical
  obtain ⟨A,hA⟩ := zorn_subset {A : Set (Condition ι) | A ⊆ U ∧ Antichain A} (by
    intro c hc hchain
    refine ⟨⋃₀ c,⟨?_,?_⟩,fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro p ⟨s,hs,hp⟩
      exact (hc hs).1 hp
    · intro p hp q hq hpq
      obtain ⟨s,hs,hps⟩ := hp
      obtain ⟨t,ht,hqt⟩ := hq
      rcases hchain.total hs ht with hst | hts
      · exact (hc ht).2 (hst hps) hqt hpq
      · exact (hc hs).2 hps (hts hqt) hpq)
  refine ⟨A,hA.1.1,hA.1.2,antichain_countable A hA.1.2,?_⟩
  intro p hp
  by_contra h
  have hnone : ∀ a ∈ A, ¬ Compatible p a := by
    intro a ha hpa
    exact h ⟨a,ha,hpa⟩
  have hins : insert p A ⊆ U ∧ Antichain (insert p A) := by
    constructor
    · exact Set.insert_subset hp hA.1.1
    · exact hA.1.2.insert (fun a ha _ =>
        ⟨hnone a ha,fun hap => hnone a ha (compatible_symm hap)⟩)
  have hpA : p ∈ A := hA.2 hins (Set.subset_insert _ _) (Set.mem_insert _ _)
  exact hnone p hpA (compatible_refl p)

end TuringRigidity.CohenNiceNames

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFiniteAntichains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenFiniteAntichains
open Set CohenSymmetry CohenCoordinates CohenChainCondition CohenNiceNames
universe u
variable {ι : Type u}

theorem finite_extension (U V E : Set (Condition ι)) (hVU : V ⊆ U)
    (hEU : E ⊆ U) (hE : Antichain E) (hfin : E.Finite)
    (n : ℕ) (hn : ∀ p ∈ V, (support p).card ≤ n) :
    ∃ F, F.Finite ∧ E ⊆ F ∧ F ⊆ U ∧ Antichain F ∧
      ∀ p ∈ V, ∃ q ∈ F, Compatible p q := by
  classical
  let W := {p ∈ V | ∀ q ∈ E, ¬ Compatible p q}
  obtain ⟨B,hBW,hB,_,hpred⟩ := countable_predense_antichain W
  have hBfin : B.Finite := bounded_antichain_finite n B hB
    (fun p hp => hn p (hBW hp).1)
  refine ⟨E ∪ B,hfin.union hBfin,Set.subset_union_left,
    Set.union_subset hEU (fun p hp => hVU (hBW hp).1),?_,?_⟩
  · intro p hp q hq hpq
    rcases hp with hp|hp <;> rcases hq with hq|hq
    · exact hE hp hq hpq
    · exact fun hc => (hBW hq).2 p hp (compatible_symm hc)
    · exact (hBW hp).2 q hq
    · exact hB hp hq hpq
  · intro p hp
    by_cases he : ∃ q ∈ E, Compatible p q
    · obtain ⟨q,hq,hpq⟩ := he; exact ⟨q,Or.inl hq,hpq⟩
    · obtain ⟨q,hq,hpq⟩ := hpred p ⟨hp,fun q hq hc => he ⟨q,hq,hc⟩⟩
      exact ⟨q,Or.inr hq,hpq⟩

end TuringRigidity.CohenFiniteAntichains

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem omega_transitive : Transitive ZFSet.omega.{u} := by
  intro x hx y hy
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  obtain ⟨i,_,rfl⟩ := (mem_natSet n y).mp hy
  exact (mem_omega _).mpr ⟨i,rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalAtomicTruth
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem internal_atomic_truth (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ M) (hb : b.encode (label c) ∈ M) :
    (Name.val G.carrier a = Name.val G.carrier b ↔ ∃ p ∈ G.carrier, EqForces a b p) ∧
    (Name.val G.carrier a ∈ Name.val G.carrier b ↔ ∃ p ∈ G.carrier, MemForces a b p) := by
  have hg := groundGeneric_atomic M hM hP hU hPow hS hR hI hc hoM ho G hG
  exact ⟨eq_truth (names_childClosed M c hM) G hg a b ha hb,
    mem_truth (names_childClosed M c hM) G hg a b ha hb⟩

end TuringRigidity.AtomicForcing

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGroundGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenGroundGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AutomorphismName
open CohenSymmetry CohenConditionCode CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem graph_mem_codeSet (A : ZFSet.{0}) (E : Set (Condition (Conditions A)))
    (p : Condition (Conditions A)) : graph A p ∈ codeSet A E ↔ p ∈ E := by
  rw [codeSet,ZFSet.mem_range]
  exact ⟨fun ⟨q,hq⟩ => graph_injective A hq ▸ q.property,fun hp => ⟨⟨p,hp⟩,rfl⟩⟩

end TuringRigidity.CohenGroundGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenSizeLevels
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenSizeLevels
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open RelativeConstructible CohenSymmetry CohenCoordinates CohenConditionCode

theorem small_graph_bound (A : ZFSet.{0}) (p : Condition (Conditions A))
    (n : ℕ) (h : Small n (graph A p)) : (support p).card < n := by
  classical
  obtain ⟨k,hk,v,hv⟩ := h
  have hex (i : ↥(support p)) : ∃ j : Fin k,
      v j = ZFSet.pair (label A i.val) (InternalCohen.bitSet ((p.val i.val).getD false)) := by
    apply ZFSet.mem_range.mp
    rw [←hv]
    exact ZFSet.mem_range_self i
  let f : ↥(support p) → Fin k := fun i => (hex i).choose
  have hf : Function.Injective f := by
    intro i j hij
    have he := (hex i).choose_spec.symm.trans ((congrArg v hij).trans (hex j).choose_spec)
    exact Subtype.ext (label_injective A (ZFSet.pair_inj.mp he).1)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe,Fintype.card_fin] at hc
  exact lt_of_le_of_lt hc hk

theorem graph_small (A : ZFSet.{0}) (p : Condition (Conditions A)) :
    Small ((support p).card + 1) (graph A p) := by
  classical
  let e : Fin (support p).card ≃ ↥(support p) :=
    (finCongr (Fintype.card_coe _).symm).trans (Fintype.equivFin ↥(support p)).symm
  refine ⟨(support p).card,Nat.lt_succ_self _,fun i =>
    ZFSet.pair (label A (e i).val) (InternalCohen.bitSet ((p.val (e i).val).getD false)),?_⟩
  apply ZFSet.ext; intro z
  simp only [graph,ZFSet.mem_range]
  exact ⟨fun ⟨i,hi⟩ => ⟨e.symm i,by simpa using hi⟩,
    fun ⟨i,hi⟩ => ⟨e i,hi⟩⟩

theorem smallFormula_spec (ω B C n p : ℕ) (e : ℕ → ZFSet.{0}) (N : ℕ)
    (hω : e ω = ZFSet.omega) (hn : e n = natSet N) (hp : e p ⊆ e B)
    (hC : ∀ g, g ∈ e C ↔ InternalCollapse.Prefix (e B) g) :
    (smallFormula ω B C n p).Eval e ↔ Small N (e p) := by
  simp only [smallFormula,Formula.Eval,Formula.eval_functionGraph,cons_zero,cons_succ]
  change (∃ k ∈ e n, ∃ g ∈ e C, FunctionGraph k (e B) g ∧
    (rangeFormula (ω+2) (B+2) (p+2) 0).Eval (cons g (cons k e))) ↔ _
  rw [hn]
  constructor
  · rintro ⟨k,hk,g,_,hf,hr⟩
    obtain ⟨k,hlt,rfl⟩ := (mem_natSet N k).mp hk
    obtain ⟨v,hv,rfl⟩ := functionGraph_tuple (e B) g k hf
    exact ⟨k,hlt,v,(rangeFormula_spec (ω+2) (B+2) (p+2) 0
      (cons (tupleGraph v) (cons (natSet k) e)) hω hv rfl).mp hr⟩
  · rintro ⟨k,hk,v,hv⟩
    have hvB : ∀ i, v i ∈ e B := fun i => hp (hv ▸ ZFSet.mem_range_self i)
    refine ⟨natSet k,(natSet_mem_natSet _ _).mpr hk,tupleGraph v,
      (hC _).mpr ⟨k,tupleGraph_function _ v hvB⟩,tupleGraph_function _ v hvB,?_⟩
    exact (rangeFormula_spec (ω+2) (B+2) (p+2) 0
      (cons (tupleGraph v) (cons (natSet k) e)) hω hvB rfl).mpr hv

theorem pair_levels (A : ZFSet.{0}) (n : ℕ) (p : ZFSet.{0}) :
    ZFSet.pair (natSet n) p ∈ levels A ↔ p ∈ CohenGroundPoset.conditions A ∧ Small n p := by
  simp only [levels,ZFSet.mem_sep,ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨_,hp⟩,m,q,he,hs⟩
    obtain ⟨h1,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,natSet_injective h1 ▸ hs⟩
  · rintro ⟨hp,hs⟩
    exact ⟨⟨(mem_omega _).mpr ⟨n,rfl⟩,hp⟩,n,p,rfl,hs⟩

theorem levels_mem (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) : levels A ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  have hc := CohenGroundPoset.conditions_mem M A hM hT hA
  let B := ZFSet.prod A InternalCohen.alphabet
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA (InternalCohen.alphabet_mem M hM hT)
  obtain ⟨C,hCM,hC⟩ := InternalCollapse.conditions_exist_absolute_without_choice M hM
    hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hB
  let e := cons ZFSet.omega (cons (CohenGroundPoset.conditions A) (cons B (fun _ => C)))
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (smallFormula 3 5 6 1 0)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i; exact hω; exact hc; exact hB; exact hCM
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hc)
  have heq : (ZFSet.prod ZFSet.omega (CohenGroundPoset.conditions A)).sep
      (fun z => φ.Eval (cons z e)) = levels A := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,levels,ZFSet.mem_sep]
    apply and_congr_right; intro _
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    change (∃ n ∈ ZFSet.omega, ∃ p ∈ CohenGroundPoset.conditions A,
      z = ZFSet.pair n p ∧ (smallFormula 3 5 6 1 0).Eval (cons p (cons n (cons z e)))) ↔ _
    constructor
    · rintro ⟨n,hn,p,hp,hz,hsmall⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hpb := ((mem_finiteSubsets_iff _ _).mp ((CohenGroundPoset.mem_conditions A p).mp hp).1).1
      exact ⟨n,p,hz,(smallFormula_spec 3 5 6 1 0 (cons p (cons (natSet n) (cons z e))) n rfl rfl hpb hC).mp hsmall⟩
    · rintro ⟨n,p,rfl,hsmall⟩
      rename_i hz
      have hp := (ZFSet.pair_mem_prod.mp hz).2
      have hpb := ((mem_finiteSubsets_iff _ _).mp ((CohenGroundPoset.mem_conditions A p).mp hp).1).1
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,p,hp,rfl,
        (smallFormula_spec 3 5 6 1 0 (cons p (cons (natSet n) (cons (ZFSet.pair (natSet n) p) e))) n rfl rfl hpb hC).mpr hsmall⟩
  exact heq ▸ hs

end TuringRigidity.CohenSizeLevels

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenAntichainStages
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAntichainStages
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenSymmetry CohenCoordinates CohenConditionCode CohenGroundPoset
open CohenGroundGeneric CohenChainCondition CohenNiceNames

theorem compFormula_spec (c p q : ℕ) (e : ℕ → ZFSet.{0}) :
    (compFormula c p q).Eval e ↔ Comp (e c) (e p) (e q) := by
  simp only [compFormula,Comp,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ]

theorem comp_graph (A : ZFSet.{0}) (p q : Condition (Conditions A)) :
    Comp (conditions A) (graph A p) (graph A q) ↔ Compatible p q := by
  constructor
  · rintro ⟨r,hr,hpr,hqr⟩
    obtain ⟨r,rfl⟩ := (isCondition_iff_graph A r).mp ((mem_conditions A r).mp hr)
    have hrp := (graph_subset_iff A r p).mp hpr
    have hrq := (graph_subset_iff A r q).mp hqr
    intro i a b ha hb
    exact Option.some.inj ((hrp i a ha).symm.trans (hrq i b hb))
  · intro h
    exact ⟨graph A (merge p q),(mem_conditions A _).mpr (graph_isCondition A _),
      (graph_subset_iff A _ p).mpr (merge_le_left p q),
      (graph_subset_iff A _ q).mpr (merge_le_right h)⟩

theorem antiFormula_spec (c E : ℕ) (e : ℕ → ZFSet.{0}) :
    (antiFormula c E).Eval e ↔ Anti (e c) (e E) := by
  simp only [antiFormula,Anti,Formula.eval_allMem,Formula.eval_imp,
    Formula.Eval,compFormula_spec,cons_zero,cons_succ]

theorem mem_stages (c U E : ZFSet.{0}) :
    E ∈ stages c U ↔ (E ⊆ U ∧ (E : Set ZFSet.{0}).Finite) ∧ Anti c E := by
  rw [stages,ZFSet.mem_sep,mem_finiteSubsets_iff]

theorem stages_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : stages c U ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded (antiFormula 1 0)
    (fun _ => c) (fun _ => hc) (finiteSubsets_mem M U hM hT hU)
  simpa only [antiFormula_spec,cons_zero,cons_succ,stages] using hs

theorem empty_stage (c U : ZFSet.{0}) : (∅ : ZFSet.{0}) ∈ stages c U := by
  apply (mem_stages c U ∅).mpr
  exact ⟨⟨fun _ h => False.elim (ZFSet.notMem_empty _ h),by simp⟩,
    fun _ h => False.elim (ZFSet.notMem_empty _ h)⟩

theorem extend_stage (A U E : ZFSet.{0}) (hU : U ⊆ conditions A)
    (hE : E ∈ stages (conditions A) U) (n : ℕ) :
    ∃ F ∈ stages (conditions A) U, E ⊆ F ∧
      ∀ p ∈ U, CohenSizeLevels.Small n p → ∃ q ∈ F, Comp (conditions A) p q := by
  classical
  obtain ⟨⟨hEU,hEfin⟩,hEa⟩ := (mem_stages _ _ _).mp hE
  let U' : Set (Condition (Conditions A)) := {p | graph A p ∈ U}
  let E' : Set (Condition (Conditions A)) := {p | graph A p ∈ E}
  let V' : Set (Condition (Conditions A)) := {p ∈ U' | CohenSizeLevels.Small n (graph A p)}
  have hE' : Antichain E' := by
    intro p hp q hq hne hc
    exact hEa _ hp _ hq (fun he => hne (graph_injective A he)) ((comp_graph A p q).mpr hc)
  have hE'f : E'.Finite := hEfin.preimage (graph_injective A).injOn
  obtain ⟨F,hFfin,hEF,hFU,hFa,hpred⟩ := CohenFiniteAntichains.finite_extension
    U' V' E' (fun _ h => h.1) (fun p h => show graph A p ∈ U from hEU h) hE' hE'f n
      (fun p hp => Nat.le_of_lt (CohenSizeLevels.small_graph_bound A p n hp.2))
  have hcode : codeSet A F ∈ stages (conditions A) U := by
    apply (mem_stages _ _ _).mpr
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro z hz
      obtain ⟨p,rfl⟩ := ZFSet.mem_range.mp hz
      exact hFU p.property
    · let : Fintype F := hFfin.fintype
      rw [codeSet,ZFSet.coe_range]
      exact Set.finite_range _
    · intro p hp q hq hpq hc
      obtain ⟨p,rfl⟩ := ZFSet.mem_range.mp hp
      obtain ⟨q,rfl⟩ := ZFSet.mem_range.mp hq
      exact hFa p.property q.property (fun he => hpq (congrArg (graph A) he))
        ((comp_graph A p.val q.val).mp hc)
  refine ⟨codeSet A F,hcode,?_,?_⟩
  · intro p hp
    obtain ⟨p,rfl⟩ := (isCondition_iff_graph A p).mp ((mem_conditions A p).mp (hU (hEU hp)))
    exact (graph_mem_codeSet A F p).mpr (hEF hp)
  · intro p hp hsmall
    obtain ⟨p,rfl⟩ := (isCondition_iff_graph A p).mp ((mem_conditions A p).mp (hU hp))
    obtain ⟨q,hq,hpq⟩ := hpred p ⟨hp,hsmall⟩
    exact ⟨graph A q,(graph_mem_codeSet A F q).mpr hq,(comp_graph A p q).mpr hpq⟩

end TuringRigidity.CohenAntichainStages

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

namespace Formula

theorem orbitMember_spec (o d Q b F z : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ e d) → ∀ k, finiteModelGraph a k ∈ e Q)
    (hF : TransitiveNameModel.FunctionGraph (e d) (e d) (e F))
    (a : ℕ → ZFSet.{u}) (ha : ∀ i, a i ∈ e d) (hb : e b = a 0)
    (hstep : ∀ i, ZFSet.pair (a i) (a (i+1)) ∈ e F) :
    (orbitMember o d Q b F z).Eval e ↔ e z ∈ orbitGraph a := by
  simp only [orbitMember,Formula.Eval,eval_orderedPair,cons_zero,cons_succ]
  rw [ho,mem_orbitGraph]
  have hs (n : ℕ) (w : ZFSet.{u}) :
      (modelIteration (o+2) (d+2) (Q+2) 1 (b+2) 0 (.pairMem 1 0 (F+5))).Eval
        (cons w (cons (natSet n) e)) ↔ w = a n := by
    apply modelIteration_spec (o+2) (d+2) (Q+2) 1 (b+2) 0 (.pairMem 1 0 (F+5))
      (cons w (cons (natSet n) e)) ho hQ n rfl a ha hb
    intro i v _
    simp only [eval_pairMem,cons_zero,cons_succ]
    exact ⟨fun hv => hF.functional (ha i) hv (hstep i),fun hv => hv.symm ▸ hstep i⟩
  constructor
  · rintro ⟨n,hn,w,_,hz,hw⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    rw [(hs n w).mp hw] at hz
    exact ⟨n,hz⟩
  · rintro ⟨n,hz⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,a n,ha n,hz,(hs n _).mpr rfl⟩
end Formula

theorem internal_orbitGraph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d F : ZFSet.{u}} (hd : d ∈ M) (hFM : F ∈ M)
    (hF : TransitiveNameModel.FunctionGraph d d F) (a : ℕ → ZFSet.{u})
    (ha : ∀ i, a i ∈ d) (hstep : ∀ i, ZFSet.pair (a i) (a (i+1)) ∈ F) : orbitGraph a ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_model_graph_bound M hM hT.pairing hT.union hT.powerSet hS hω d hd
  let e := cons ZFSet.omega (cons d (cons Q (cons (a 0) (fun _ => F))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hω
    rcases i with _|i; exact hd
    rcases i with _|i; exact hQM
    rcases i with _|i; exact hM _ hd _ (ha 0)
    exact hFM
  have hs := sep_mem M hM hS (Formula.orbitMember 1 2 3 4 5 0) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hd)
  have hEq : ZFSet.sep (fun z => (Formula.orbitMember 1 2 3 4 5 0).Eval (cons z e))
      (ZFSet.prod ZFSet.omega d) = orbitGraph a := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,Formula.orbitMember_spec 1 2 3 4 5 0 (cons z e) rfl hQ hF a ha rfl hstep]
    exact ⟨And.right,fun h => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function d a ha).1 z h),h⟩⟩
  exact hEq ▸ hs

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSerialSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationHull
universe u
namespace Formula

theorem eval_predecessorSet (d r x a : ℕ) (e : ℕ → ZFSet.{u}) :
    (predecessorSet d r x a).Eval e ↔ e a = predecessors (e d) (e r) (e x) := by
  simp only [predecessorSet,Formula.Eval,eval_subset,eval_allMem,eval_iff,eval_pairMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro y
    rw [mem_predecessors]
    exact ⟨fun hy => ⟨hsub hy,(h y (hsub hy)).mp hy⟩,fun hy => (h y hy.1).mpr hy.2⟩
  · intro he
    rw [he]
    exact ⟨fun _ h => (mem_predecessors _ _ _ _).mp h |>.1,
      fun y hy => (mem_predecessors _ _ _ _).trans (and_iff_right hy)⟩

end Formula

theorem internal_serial_function (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M)
    (hser : ∀ x ∈ d, ∃ y ∈ d, ZFSet.pair y x ∈ r) :
    ∃ F ∈ M, TransitiveNameModel.FunctionGraph d d F ∧
      ∀ x y, ZFSet.pair x y ∈ F → ZFSet.pair y x ∈ r := by
  have hS := hT.separation.finitePrefix.bounded
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hT.powerSet hS hT.choice hd
  have hp (x : ZFSet.{u}) (hx : x ∈ d) : predecessors d r x ∈ q := by
    apply (hqdef _).mpr
    refine ⟨predecessors_mem M hM hS hd hr (hM _ hd _ hx),
      fun _ h => (mem_predecessors _ _ _ _).mp h |>.1,?_⟩
    obtain ⟨y,hy,hyx⟩ := hser x hx
    exact ⟨y,(mem_predecessors _ _ _ _).mpr ⟨hy,hyx⟩⟩
  let e := cons d (cons r (cons q (fun _ => s)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact hr
    rcases i with _|i; exact hq
    exact hsM
  let F := ZFSet.sep (fun z => (Formula.serialSelector 1 2 3 4 0).Eval (cons z e)) (ZFSet.prod d d)
  have hFM : F ∈ M := sep_mem M hM hS _ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hd hd)
  have hmem (z : ZFSet.{u}) : z ∈ F ↔
      ∃ x ∈ d, ∃ y ∈ d, z = ZFSet.pair x y ∧ ZFSet.pair (predecessors d r x) y ∈ s := by
    simp only [F,ZFSet.mem_sep,Formula.serialSelector,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_predecessorSet,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨_,x,hx,y,hy,hz,a,_,rfl,hay⟩; exact ⟨x,hx,y,hy,hz,hay⟩
    · rintro ⟨x,hx,y,hy,rfl,hxy⟩
      exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,y,hy,rfl⟩,x,hx,y,hy,rfl,predecessors d r x,hp x hx,rfl,hxy⟩
  refine ⟨F,hFM,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,y,hy,hz,_⟩ := (hmem z).mp hz
    exact ⟨x,hx,y,hy,hz⟩
  · intro x hx
    obtain ⟨y,hy,hxy,_⟩ := hs.2 _ (hp x hx)
    have hyd := ((mem_predecessors _ _ _ _).mp hy).1
    refine ⟨y,hyd,(hmem _).mpr ⟨x,hx,y,hyd,rfl,hxy⟩,?_⟩
    intro z _ hxz
    obtain ⟨x',_,z',_,heq,hxz'⟩ := (hmem _).mp hxz
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact hs.functional hxz' hxy
  · intro x y hxy
    obtain ⟨x',_,y',_,heq,hsy⟩ := (hmem _).mp hxy
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    exact ((mem_predecessors _ _ _ _).mp (InternalWellOrder.choice_value_mem hs hsy)).2

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTDependentChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse InternalWellOrder
universe u

theorem sourceT_dependent_choice (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d r x : ZFSet.{u}} (hd : d ∈ M) (hr : r ∈ M) (hx : x ∈ d)
    (hser : ∀ x ∈ d, ∃ y ∈ d, ZFSet.pair y x ∈ r) :
    ∃ a : ℕ → ZFSet.{u}, a 0 = x ∧ (∀ n, a n ∈ d) ∧ orbitGraph a ∈ M ∧
      ∀ n, ZFSet.pair (a (n+1)) (a n) ∈ r := by
  classical
  obtain ⟨F,hFM,hF,hrel⟩ := internal_serial_function M hM hT hd hr hser
  let next (y : ZFSet.{u}) : ZFSet.{u} := if hy : y ∈ d then (hF.2 y hy).choose else y
  have hn (y : ZFSet.{u}) (hy : y ∈ d) : next y ∈ d ∧ ZFSet.pair y (next y) ∈ F := by
    simp only [next,dite_eq_left hy]
    exact ⟨(hF.2 y hy).choose_spec.1,(hF.2 y hy).choose_spec.2.1⟩
  let a : ℕ → ZFSet.{u} := Nat.rec x (fun _ y => next y)
  have ha : ∀ n, a n ∈ d := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => exact (hn (a n) ih).1
  have hstep : ∀ n, ZFSet.pair (a n) (a (n+1)) ∈ F := fun n => (hn (a n) (ha n)).2
  exact ⟨a,rfl,ha,internal_orbitGraph M hM hT hd hFM hF a ha hstep,
    fun n => hrel _ _ (hstep n)⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenAntichainSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAntichainSequence
open Set TransitiveNameModel BoundedSetTheory CohenAntichainStages
open CohenGroundPoset CohenConditionCode CohenSizeLevels

theorem stepFormula_spec (ω s c U L x y : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega) :
    (stepFormula ω s c U L x y).Eval e ↔ Step (e s) (e c) (e U) (e L) (e x) (e y) := by
  simp only [stepFormula,Step,Formula.Eval,Formula.eval_orderedPair,
    Formula.eval_successor,Formula.eval_subset,Formula.eval_allMem,Formula.eval_imp,
    Formula.eval_pairMem,compFormula_spec,cons_zero,cons_succ,hω]

theorem pair_relation (s c U L x y : ZFSet.{0}) :
    ZFSet.pair y x ∈ relation s c U L ↔ Step s c U L x y := by
  rw [relation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',_,y',_,he,hs⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact hs
  · intro hs
    have hs' := hs
    obtain ⟨n,hn,E,hE,m,hm,F,hF,hx,hy,_⟩ := hs
    have hxd : x ∈ ZFSet.prod ZFSet.omega s := hx ▸ ZFSet.mem_prod.mpr ⟨n,hn,E,hE,rfl⟩
    have hyd : y ∈ ZFSet.prod ZFSet.omega s := hy ▸ ZFSet.mem_prod.mpr ⟨m,hm,F,hF,rfl⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨y,hyd,x,hxd,rfl⟩,x,hxd,y,hyd,rfl,hs'⟩

theorem relation_mem (M s c U L : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hs : s ∈ M) (hc : c ∈ M) (hU : U ∈ M) (hL : L ∈ M) : relation s c U L ∈ M := by
  let d := ZFSet.prod ZFSet.omega s
  have hd := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) hs
  let e := cons ZFSet.omega (cons s (cons c (cons U (cons L (fun _ => d)))))
  let φ : Formula := .existsMem 6 (.existsMem 7 (.conj (.orderedPair 2 0 1)
    (stepFormula 3 4 5 6 7 1 0)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact sourceT_omega_mem M hM hT
    exact hs; exact hc; exact hU; exact hL; exact hd
  have hsep := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hd hd)
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      ∃ x ∈ d, ∃ y ∈ d, z = ZFSet.pair y x ∧ Step s c U L x y := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply exists_congr; intro y
    apply and_congr_right; intro _
    apply and_congr_right; intro _
    exact stepFormula_spec 3 4 5 6 7 1 0 _ rfl
  simpa only [hφ,relation] using hsep

theorem internal_sequence (M A U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hU : U ∈ M) (hUc : U ⊆ conditions A) :
    ∃ E : ℕ → ZFSet.{0}, E 0 = ∅ ∧ (∀ n, E n ∈ stages (conditions A) U) ∧
      orbitGraph (fun n => ZFSet.pair (natSet n) (E n)) ∈ M ∧
      (∀ n, E n ⊆ E (n+1)) ∧
      ∀ n p, p ∈ U → Small n p → ∃ q ∈ E (n+1), Comp (conditions A) p q := by
  classical
  let s := stages (conditions A) U
  let d := ZFSet.prod ZFSet.omega s
  have hc := conditions_mem M A hM hT hA
  have hs := stages_mem M _ U hM hT hc hU
  have hd := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) hs
  have hserial : ∀ x ∈ d, ∃ y ∈ d, ZFSet.pair y x ∈ relation s (conditions A) U (levels A) := by
    intro x hx
    obtain ⟨n,hn,E,hE,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨F,hF,hEF,hpred⟩ := extend_stage A U E hUc hE n
    refine ⟨ZFSet.pair (natSet (n+1)) F,ZFSet.mem_prod.mpr
      ⟨_,(mem_omega _).mpr ⟨n+1,rfl⟩,F,hF,rfl⟩,(pair_relation _ _ _ _ _ _).mpr ?_⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E,hE,natSet (n+1),
      (mem_omega _).mpr ⟨n+1,rfl⟩,F,hF,rfl,rfl,rfl,hEF,
      fun p hp hpn => hpred p hp ((pair_levels A n p).mp hpn).2⟩
  obtain ⟨b,hb0,hb,hbM,hstep⟩ := sourceT_dependent_choice M hM hT hd
    (relation_mem M s (conditions A) U (levels A) hM hT hs hc hU (levels_mem M A hM hT hA))
    (ZFSet.mem_prod.mpr ⟨natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,∅,empty_stage _ _,rfl⟩) hserial
  have shape : ∀ n, ∃ E ∈ s, b n = ZFSet.pair (natSet n) E := by
    intro n
    induction n with
    | zero => exact ⟨∅,empty_stage _ _,hb0⟩
    | succ n ih =>
      obtain ⟨E,_,hE⟩ := ih
      obtain ⟨k,_,F,_,m,_,H,hH,hbk,hbn,hm,_⟩ := (pair_relation _ _ _ _ _ _).mp (hstep n)
      have hk := (ZFSet.pair_inj.mp (hbk.symm.trans hE)).1
      rw [hk] at hm
      exact ⟨H,hH,by rw [hbn,hm]; rfl⟩
  choose E hE hEb using shape
  have h0 : E 0 = ∅ := (ZFSet.pair_inj.mp ((hEb 0).symm.trans hb0)).2
  have b_eq : b = fun n => ZFSet.pair (natSet n) (E n) := funext hEb
  refine ⟨E,h0,hE,b_eq ▸ hbM,?_,?_⟩
  · intro n
    obtain ⟨k,_,F,_,m,_,H,_,hx,hy,_,hFH,_⟩ := (pair_relation _ _ _ _ _ _).mp (hstep n)
    have hf := (ZFSet.pair_inj.mp (hx.symm.trans (hEb n))).2
    have hh := (ZFSet.pair_inj.mp (hy.symm.trans (hEb (n+1)))).2
    rwa [hf,hh] at hFH
  · intro n p hp hsmall
    obtain ⟨k,_,F,_,m,_,H,_,hx,hy,_,_,hpred⟩ := (pair_relation _ _ _ _ _ _).mp (hstep n)
    have hk := (ZFSet.pair_inj.mp (hx.symm.trans (hEb n))).1
    have hh := (ZFSet.pair_inj.mp (hy.symm.trans (hEb (n+1)))).2
    rw [hk,hh] at hpred
    exact hpred p hp ((pair_levels A n p).mpr ⟨hUc hp,hsmall⟩)

end TuringRigidity.CohenAntichainSequence

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenInternalAntichain
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenInternalAntichain
open Set TransitiveNameModel BoundedSetTheory CohenAntichainStages
open CohenAntichainSequence CohenGroundPoset CohenConditionCode CohenSizeLevels

theorem stage_union_internal (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ stages c U)
    (hgraph : orbitGraph (fun n => ZFSet.pair (natSet n) (E n)) ∈ M) :
    ∃ F ∈ M, ∀ p, p ∈ F ↔ ∃ n, p ∈ E n := by
  let s := stages c U
  let d := ZFSet.prod ZFSet.omega s
  let g := orbitGraph (fun n => ZFSet.pair (natSet n) (E n))
  have hs := stages_mem M c U hM hT hc hU
  have hd := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) hs
  let e := cons ZFSet.omega (cons s (cons d (fun _ => g)))
  let φ : Formula := .existsMem 1 (.existsMem 3 (.existsMem 5
    (.conj (.orderedPair 0 2 1) (.conj (.pairMem 2 0 7) (.member 3 1)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact sourceT_omega_mem M hM hT
    exact hs; exact hd; exact hgraph
  have hφ (p : ZFSet.{0}) : φ.Eval (cons p e) ↔ ∃ n, p ∈ E n := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,F,_,t,_,ht,hnt,hp⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have ht' := (orbitGraph_pair (fun n => ZFSet.pair (natSet n) (E n)) n t).mp hnt
      have hF := (ZFSet.pair_inj.mp (ht.symm.trans ht')).2
      exact ⟨n,hF ▸ hp⟩
    · rintro ⟨n,hp⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,hE n,
        ZFSet.pair (natSet n) (E n),ZFSet.mem_prod.mpr
          ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,hE n,rfl⟩,
        rfl,(orbitGraph_pair _ n _).mpr rfl,hp⟩
  refine ⟨U.sep (fun p => φ.Eval (cons p e)),
    sep_mem M hM hT.separation.finitePrefix.bounded φ e he hU,?_⟩
  intro p
  rw [ZFSet.mem_sep,hφ]
  exact ⟨And.right,fun ⟨n,hp⟩ => ⟨((mem_stages _ _ _).mp (hE n)).1.1 hp,n,hp⟩⟩

theorem internal_predense_antichain (M A U : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hU : U ∈ M)
    (hUc : U ⊆ conditions A) :
    ∃ F ∈ M, F ⊆ U ∧ Anti (conditions A) F ∧
      ∀ p ∈ U, ∃ q ∈ F, Comp (conditions A) p q := by
  obtain ⟨E,_,hE,hg,hstep,hpred⟩ := internal_sequence M A U hM hT hA hU hUc
  obtain ⟨F,hFM,hF⟩ := stage_union_internal M (conditions A) U hM hT
    (conditions_mem M A hM hT hA) hU E hE hg
  have hmono : ∀ n m, n ≤ m → E n ⊆ E m := by
    intro n m hnm
    induction hnm with
    | refl => exact fun _ h => h
    | @step m _ ih => exact fun _ h => hstep m (ih h)
  refine ⟨F,hFM,?_,?_,?_⟩
  · intro p hp
    obtain ⟨n,hn⟩ := (hF p).mp hp
    exact ((mem_stages _ _ _).mp (hE n)).1.1 hn
  · intro p hp q hq hpq hc
    obtain ⟨n,hn⟩ := (hF p).mp hp
    obtain ⟨m,hm⟩ := (hF q).mp hq
    exact ((mem_stages _ _ _).mp (hE (max n m))).2 p
      (hmono n _ (Nat.le_max_left _ _) hn) q (hmono m _ (Nat.le_max_right _ _) hm) hpq hc
  · intro p hp
    obtain ⟨p,rfl⟩ := (isCondition_iff_graph A p).mp ((mem_conditions A p).mp (hUc hp))
    obtain ⟨q,hq,hpq⟩ := hpred _ (graph A p) hp (graph_small A p)
    exact ⟨q,(hF q).mpr ⟨_,hq⟩,hpq⟩

end TuringRigidity.CohenInternalAntichain

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenCountedAntichain
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenCountedAntichain
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenAntichainStages CohenAntichainSequence CohenInternalAntichain CohenGroundPoset

theorem project_sequence (M S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hS : S ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ S)
    (hB : orbitGraph (fun n => ZFSet.pair (natSet n) (E n)) ∈ M) : orbitGraph E ∈ M := by
  let B := orbitGraph (fun n => ZFSet.pair (natSet n) (E n))
  let e := cons ZFSet.omega (cons S (fun _ => B))
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (.pairMem 1 2 5)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact sourceT_omega_mem M hM hT
    exact hS; exact hB
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph E := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,F,_,hz,hnz⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hh := (orbitGraph_pair (fun n => ZFSet.pair (natSet n) (E n)) n z).mp hnz
      exact (mem_orbitGraph E z).mpr ⟨n,hh⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph E z).mp hz
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,hE n,rfl,(orbitGraph_pair _ n _).mpr rfl⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (sourceT_omega_mem M hM hT) hS)
  have heq : (ZFSet.prod ZFSet.omega S).sep (fun z => φ.Eval (cons z e)) = orbitGraph E := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function S E hE).1 z hz),hz⟩⟩
  exact heq ▸ hs

theorem internal_counted_antichain (M A U : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hU : U ∈ M) (hUc : U ⊆ conditions A) :
    ∃ F ∈ M, F ⊆ U ∧ Anti (conditions A) F ∧
      (∀ p ∈ U, ∃ q ∈ F, Comp (conditions A) p q) ∧
      (F = ∅ ∨ InternallyCountable M F) := by
  classical
  obtain ⟨E,_,hE,hg,hstep,hpred⟩ := internal_sequence M A U hM hT hA hU hUc
  have hc := conditions_mem M A hM hT hA
  obtain ⟨F,hFM,hF⟩ := stage_union_internal M (conditions A) U hM hT hc hU E hE hg
  have hmono : ∀ n m, n ≤ m → E n ⊆ E m := by
    intro n m hnm
    induction hnm with
    | refl => exact fun _ h => h
    | @step m _ ih => exact fun _ h => hstep m (ih h)
  refine ⟨F,hFM,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨n,hn⟩ := (hF p).mp hp
    exact ((mem_stages _ _ _).mp (hE n)).1.1 hn
  · intro p hp q hq hpq hcomp
    obtain ⟨n,hn⟩ := (hF p).mp hp
    obtain ⟨m,hm⟩ := (hF q).mp hq
    exact ((mem_stages _ _ _).mp (hE (max n m))).2 p
      (hmono n _ (Nat.le_max_left _ _) hn) q (hmono m _ (Nat.le_max_right _ _) hm) hpq hcomp
  · intro p hp
    obtain ⟨p,rfl⟩ := (CohenConditionCode.isCondition_iff_graph A p).mp
      ((mem_conditions A p).mp (hUc hp))
    obtain ⟨q,hq,hpq⟩ := hpred _ (CohenConditionCode.graph A p) hp (CohenSizeLevels.graph_small A p)
    exact ⟨q,(hF q).mpr ⟨_,hq⟩,hpq⟩
  · by_cases hempty : F = ∅
    · exact Or.inl hempty
    · right
      apply InternalCountableFiniteUnion.internally_countable_union M F hM hT hFM E
      · intro n
        exact (mem_finiteSubsets_iff F (E n)).mpr
          ⟨fun p hp => (hF p).mpr ⟨n,hp⟩,((mem_stages _ _ _).mp (hE n)).1.2⟩
      · exact project_sequence M (stages (conditions A) U) hM hT
          (stages_mem M _ U hM hT hc hU) E hE hg
      · exact fun p hp => (hF p).mp hp
      · by_contra h
        apply hempty
        apply ZFSet.ext; intro p
        exact ⟨fun hp => False.elim (h ⟨p,hp⟩),fun hp => False.elim (ZFSet.notMem_empty p hp)⟩

theorem every_internal_antichain_counted (M A E : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hE : E ∈ M) (hEc : E ⊆ conditions A)
    (ha : Anti (conditions A) E) : E = ∅ ∨ InternallyCountable M E := by
  obtain ⟨F,_,hFE,_,hpred,hcount⟩ := internal_counted_antichain M A E hM hT hA hE hEc
  have he : F = E := by
    apply ZFSet.ext; intro p
    refine ⟨fun hp => hFE hp,fun hp => ?_⟩
    obtain ⟨q,hq,hpq⟩ := hpred p hp
    have hpq' : p = q := Classical.byContradiction (fun hn => ha p hp q (hFE hq) hn hpq)
    exact hpq' ▸ hq
  exact he ▸ hcount

end TuringRigidity.CohenCountedAntichain

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
open CohenCountedAntichain CohenConditionCode CohenSymmetry CohenCoordinates

theorem decision_mem (M c U E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (hE : E ∈ M) : decision c U E ∈ M := by
  let e := cons U (fun _ => E)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hU; exact hE
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.disj (.existsMem 2 (.subset 0 1)) (.allMem 1 (.neg (.subset 1 0)))) e he hc
  simpa only [decision,Formula.eval_disj,Formula.eval_allMem,Formula.Eval,
    Formula.eval_subset,cons_zero,cons_succ,e] using hs

theorem decision_dense (A U E : ZFSet.{0})
    (hpred : ∀ p ∈ below (conditions A) U, ∃ q ∈ E, Comp (conditions A) p q) :
    ∀ p ∈ conditions A, ∃ q ∈ decision (conditions A) (below (conditions A) U) E, p ⊆ q := by
  classical
  intro p hp
  by_cases h : ∃ r ∈ below (conditions A) U, p ⊆ r
  · obtain ⟨r,hr,hpr⟩ := h
    obtain ⟨a,ha,t,ht,hrt,hat⟩ := hpred r hr
    exact ⟨t,ZFSet.mem_sep.mpr ⟨ht,Or.inl ⟨a,ha,hat⟩⟩,fun z hz => hrt (hpr hz)⟩
  · exact ⟨p,ZFSet.mem_sep.mpr ⟨hp,Or.inr (fun r hr hpr => h ⟨r,hr,hpr⟩)⟩,fun _ h => h⟩

end TuringRigidity.CohenInternalDecision

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

theorem map_sequence (M X Y T : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hX : X ∈ M) (hY : Y ∈ M) (hTM : T ∈ M) (hf : FunctionGraph X Y T)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ X) (hB : orbitGraph E ∈ M) :
    ∃ F : ℕ → ZFSet.{0}, orbitGraph F ∈ M ∧
      ∀ n, F n ∈ Y ∧ ZFSet.pair (E n) (F n) ∈ T := by
  choose F hF hp hu using fun n => hf.2 (E n) (hE n)
  let B := orbitGraph E
  let e := cons ZFSet.omega (cons X (cons Y (cons B (fun _ => T))))
  let φ : Formula := .existsMem 1 (.existsMem 4 (.conj (.orderedPair 2 1 0)
    (.existsMem 4 (.conj (.pairMem 2 0 7) (.pairMem 0 1 8)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact sourceT_omega_mem M hM hT; exact hX; exact hY; exact hB; exact hTM
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph F := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,y,hy,hz,x,_,hnx,hxy⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hx := (orbitGraph_pair E n x).mp hnx
      have hy' := hf.functional (hE n) (hx ▸ hxy) (hp n)
      exact (mem_orbitGraph F z).mpr ⟨n,by rw [hz,hy']⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph F z).mp hz
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,F n,hF n,rfl,E n,hE n,
        (orbitGraph_pair E n _).mpr rfl,hp n⟩
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (sourceT_omega_mem M hM hT) hY)
  have heq : (ZFSet.prod ZFSet.omega Y).sep (fun z => φ.Eval (cons z e)) = orbitGraph F := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function Y F hF).1 z hz),hz⟩⟩
  exact ⟨F,heq ▸ hh,fun n => ⟨hF n,hp n⟩⟩

end TuringRigidity.InternalRelationSelection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenAntichainSelector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAntichainSelector
open TransitiveNameModel BoundedSetTheory CohenAntichainStages CohenGroundPoset
open InternalRelationSelection

theorem selectedFormula_spec (c U E : ℕ) (e : ℕ → ZFSet.{0}) :
    (selectedFormula c U E).Eval e ↔ Selected (e c) (e U) (e E) := by
  simp only [selectedFormula,Selected,Formula.Eval,Formula.eval_subset,
    antiFormula_spec,Formula.eval_allMem,compFormula_spec,cons_zero,cons_succ]

theorem pair_selectionRelation (c Q U E : ZFSet.{0}) :
    ZFSet.pair U E ∈ selectionRelation c Q ↔ U ∈ Q ∧ E ∈ Q ∧ Selected c U E := by
  simp only [selectionRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,U',hU,E',hE,hp,hsel⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact ⟨hU,hE,hsel⟩
  · rintro ⟨hU,hE,hsel⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨U,hU,E,hE,rfl⟩,U,hU,E,hE,rfl,hsel⟩

theorem selectionRelation_mem (M c Q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hQ : Q ∈ M) : selectionRelation c Q ∈ M := by
  let e := cons Q (fun _ => c)
  let φ : Formula := .existsMem 1 (.existsMem 2
    (.conj (.orderedPair 2 1 0) (selectedFormula 4 1 0)))
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hQ; exact hc
  simpa only [selectionRelation,φ,Formula.Eval,Formula.eval_orderedPair,
    selectedFormula_spec,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded φ e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hQ hQ)

theorem internal_antichain_selector (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) :
    ∃ Q ∈ M, (∀ U, U ∈ Q ↔ U ∈ M ∧ U ⊆ conditions A) ∧
      ∃ T ∈ M, FunctionGraph Q Q T ∧
        ∀ U ∈ Q, ∀ E, ZFSet.pair U E ∈ T → Selected (conditions A) U E := by
  have hc := conditions_mem M A hM hT hA
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  have hr := selectionRelation_mem M (conditions A) Q hM hT hc hQM
  have htotal : ∀ U ∈ Q, ∃ E ∈ Q, ZFSet.pair U E ∈ selectionRelation (conditions A) Q := by
    intro U hU
    obtain ⟨hUM,hUc⟩ := (hQ U).mp hU
    obtain ⟨E,hEM,hEU,hanti,hpred⟩ :=
      CohenInternalAntichain.internal_predense_antichain M A U hM hT hA hUM hUc
    have hEQ := (hQ E).mpr ⟨hEM,fun _ h => hUc (hEU h)⟩
    exact ⟨E,hEQ,(pair_selectionRelation _ _ _ _).mpr ⟨hU,hEQ,hEU,hanti,hpred⟩⟩
  obtain ⟨T,hTM,hfun,hsub⟩ := select_relation M Q Q _ hM hT hQM hQM hr htotal
  exact ⟨Q,hQM,hQ,T,hTM,hfun,fun U _ E hUE => (pair_selectionRelation _ _ _ _).mp (hsub hUE) |>.2.2⟩

theorem internal_antichain_family (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (U : ℕ → ZFSet.{0})
    (hU : ∀ n, U n ∈ M ∧ U n ⊆ conditions A) (hB : orbitGraph U ∈ M) :
    ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
      ∀ n, E n ∈ M ∧ Selected (conditions A) (U n) (E n) ∧
        (E n = ∅ ∨ InternallyCountable M (E n)) := by
  obtain ⟨Q,hQM,hQ,T,hTM,hfun,hsel⟩ := internal_antichain_selector M A hM hT hA
  have hUQ : ∀ n, U n ∈ Q := fun n => (hQ _).mpr (hU n)
  obtain ⟨E,hE,hval⟩ := map_sequence M Q Q T hM hT hQM hQM hTM hfun U hUQ hB
  refine ⟨E,hE,fun n => ?_⟩
  have hEM := ((hQ _).mp (hval n).1).1
  have hs := hsel (U n) (hUQ n) (E n) (hval n).2
  exact ⟨hEM,hs,CohenCountedAntichain.every_internal_antichain_counted M A (E n) hM hT hA hEM
    (fun _ h => (hU n).2 (hs.1 h)) hs.2.1⟩

end TuringRigidity.CohenAntichainSelector

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenInternalSupport
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenInternalSupport
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenGroundPoset CohenConditionCode CohenSymmetry CohenCoordinates InternalCohen

theorem support_graph (A : ZFSet.{0}) (p : Condition (Conditions A)) :
    supportSet A (graph A p) = ZFSet.range (fun i : ↥(support p) => label A i.val) := by
  apply ZFSet.ext; intro x
  rw [supportSet,ZFSet.mem_sep,ZFSet.mem_range]
  constructor
  · rintro ⟨hx,b,hb,hpb⟩
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    let i : Conditions A := equivShrink A ⟨x,hx⟩
    have hi : label A i = x := by simp [i,label]
    rw [←hi,pair_mem_graph] at hpb
    exact ⟨⟨i,(mem_support p i).mpr (by simp [hpb])⟩,hi⟩
  · rintro ⟨i,rfl⟩
    have hi := (mem_support p i.val).mp i.property
    cases hv : p.val i.val with
    | none => exact False.elim (hi hv)
    | some b => exact ⟨label_mem A i.val,bitSet b,(mem_alphabet _).mpr ⟨b,rfl⟩,
        (pair_mem_graph A p i.val b).mpr hv⟩

theorem support_finite (A p : ZFSet.{0}) (hp : p ∈ conditions A) :
    supportSet A p ∈ finiteSubsets A := by
  obtain ⟨p,rfl⟩ := (isCondition_iff_graph A p).mp ((mem_conditions A p).mp hp)
  apply (mem_finiteSubsets_iff _ _).mpr
  exact ⟨fun _ h => (ZFSet.mem_sep.mp h).1,by rw [support_graph,ZFSet.coe_range]; exact Set.finite_range _⟩

theorem supportFormula_spec (A B p S : ℕ) (e : ℕ → ZFSet.{0}) (hB : e B = alphabet) :
    (supportFormula A B p S).Eval e ↔ e S = supportSet (e A) (e p) := by
  simp only [supportFormula,Formula.eval_subset,Formula.eval_allMem,Formula.eval_iff,
    Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,hB]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro x
    exact ⟨fun hx => ZFSet.mem_sep.mpr ⟨hsub hx,(h x (hsub hx)).mp hx⟩,
      fun hx => (h x (ZFSet.mem_sep.mp hx).1).mpr (ZFSet.mem_sep.mp hx).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hx => (ZFSet.mem_sep.mp hx).1,
      fun x hx => ZFSet.mem_sep.trans (and_iff_right hx)⟩

theorem used_mem (M A E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hE : E ∈ M) : used A E ∈ M := by
  let e := cons E (fun _ => alphabet)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hE; exact alphabet_mem M hM hT
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.existsMem 3 (.pairMem 2 0 1))) e he hA
  have heq : A.sep (fun x => (Formula.existsMem 1 (.existsMem 3 (.pairMem 2 0 1))).Eval (cons x e)) = used A E := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e,used,supportSet]
    constructor
    · rintro ⟨hx,p,hp,b,hb,hpb⟩; exact ⟨hx,p,hp,hx,b,hb,hpb⟩
    · rintro ⟨hx,p,hp,_,hb⟩; exact ⟨hx,p,hp,hb⟩
  exact heq ▸ hs

theorem used_counted (M A E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hE : E ∈ M) (hEc : E ⊆ conditions A)
    (hct : InternallyCountable M E) :
    used A E = ∅ ∨ InternallyCountable M (used A E) := by
  classical
  obtain ⟨B,hBM,hB,honto⟩ := hct
  have hvals (n : ℕ) := hB.2 (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
  choose p hp hnp hpu using hvals
  let S := finiteSubsets A
  let v : ℕ → ZFSet.{0} := fun n => supportSet A (p n)
  have hv : ∀ n, v n ∈ S := fun n => support_finite A (p n) (hEc (hp n))
  have hS := finiteSubsets_mem M A hM hT hA
  have hω := sourceT_omega_mem M hM hT
  let e := cons ZFSet.omega (cons S (cons E (cons B (cons A (fun _ => alphabet)))))
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.conj (.pairMem 2 0 7) (supportFormula 8 9 0 1)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact hω; exact hS; exact hE; exact hBM; exact hA; exact alphabet_mem M hM hT
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph v := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,T,_,hz,q,hq,hnq,hT⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hq' := hpu n q hq hnq
      have ht := (supportFormula_spec 8 9 0 1 _ rfl).mp hT
      change T = supportSet A q at ht
      exact (mem_orbitGraph v z).mpr ⟨n,by rw [hz,ht,hq']⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph v z).mp hz
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,v n,hv n,rfl,p n,hp n,hnp n,
        (supportFormula_spec 8 9 0 1 _ rfl).mpr rfl⟩
  have hV : orbitGraph v ∈ M := by
    have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hS)
    have heq : (ZFSet.prod ZFSet.omega S).sep (fun z => φ.Eval (cons z e)) = orbitGraph v := by
      apply ZFSet.ext; intro z
      rw [ZFSet.mem_sep,hφ]
      exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function S v hv).1 z hz),hz⟩⟩
    exact heq ▸ hs
  by_cases hempty : used A E = ∅
  · exact Or.inl hempty
  · right
    apply InternalCountableFiniteUnion.internally_countable_union M (used A E) hM hT
      (used_mem M A E hM hT hA hE) v
    · intro n
      exact (mem_finiteSubsets_iff _ _).mpr ⟨fun x hx => ZFSet.mem_sep.mpr
        ⟨(ZFSet.mem_sep.mp hx).1,p n,hp n,hx⟩,((mem_finiteSubsets_iff A (v n)).mp (hv n)).2⟩
    · exact hV
    · intro x hx
      obtain ⟨_,q,hq,hxq⟩ := ZFSet.mem_sep.mp hx
      obtain ⟨n,hn,hnq⟩ := honto q hq
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      refine ⟨n,?_⟩
      change x ∈ supportSet A (p n)
      rwa [hpu n q hq hnq] at hxq
    · by_contra h
      apply hempty
      apply ZFSet.ext; intro x
      exact ⟨fun hx => False.elim (h ⟨x,hx⟩),fun hx => False.elim (ZFSet.notMem_empty x hx)⟩

end TuringRigidity.CohenInternalSupport

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSequenceRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSequenceRange
open TransitiveNameModel BoundedSetTheory

theorem rangeSet_mem (M X B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hX : X ∈ M) (hB : B ∈ M) : rangeSet X B ∈ M := by
  let e := cons ZFSet.omega (fun _ => B)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i; exact sourceT_omega_mem M hM hT; exact hB
  simpa only [rangeSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 1 3)) e he hX

theorem mem_rangeSet (X : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ X)
    (x : ZFSet.{0}) : x ∈ rangeSet X (orbitGraph E) ↔ ∃ n, x = E n := by
  rw [rangeSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,n,hn,hpair⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,(orbitGraph_pair E n x).mp hpair⟩
  · rintro ⟨n,rfl⟩
    exact ⟨hE n,natSet n,(mem_omega _).mpr ⟨n,rfl⟩,(orbitGraph_pair E n _).mpr rfl⟩

theorem unionSet_mem (M U S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hU : U ∈ M) (hS : S ∈ M) : unionSet U S ∈ M := by
  simpa only [unionSet,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.member 1 0))
      (fun _ => S) (fun _ => hS) hU

theorem mem_unionSet (U S x : ZFSet.{0}) (hS : ∀ E ∈ S, E ⊆ U) :
    x ∈ unionSet U S ↔ ∃ E ∈ S, x ∈ E := by
  rw [unionSet,ZFSet.mem_sep]
  exact ⟨And.right,fun ⟨E,hE,hx⟩ => ⟨hS E hE hx,E,hE,hx⟩⟩

end TuringRigidity.InternalSequenceRange

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenAntichainFamilySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenAntichainFamilySupport
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenAntichainStages
open InternalSequenceRange CohenInternalSupport

theorem antichain_union_counted (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ conditions A ∧ Anti (conditions A) (E n))
    (hB : orbitGraph E ∈ M) :
    ∃ F ∈ M, (∀ p, p ∈ F ↔ ∃ n, p ∈ E n) ∧ F ⊆ conditions A ∧
      (F = ∅ ∨ InternallyCountable M F) := by
  classical
  have hc := conditions_mem M A hM hT hA
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  have hEQ : ∀ n, E n ∈ Q := fun n => (hQ _).mpr ⟨(hE n).1,(hE n).2.1⟩
  let S := rangeSet Q (orbitGraph E)
  have hSM : S ∈ M := rangeSet_mem M Q _ hM hT hQM hB
  have hS (H : ZFSet.{0}) : H ∈ S ↔ ∃ n, H = E n := mem_rangeSet Q E hEQ H
  have hsub : ∀ H ∈ S, H ⊆ conditions A := by
    intro H hH
    obtain ⟨n,rfl⟩ := (hS H).mp hH
    exact (hE n).2.1
  let F := unionSet (conditions A) S
  have hFM : F ∈ M := unionSet_mem M _ S hM hT hc hSM
  have hF (p : ZFSet.{0}) : p ∈ F ↔ ∃ n, p ∈ E n := by
    rw [mem_unionSet _ _ _ hsub]
    exact ⟨fun ⟨H,hH,hp⟩ => by obtain ⟨n,rfl⟩ := (hS H).mp hH; exact ⟨n,hp⟩,
      fun ⟨n,hp⟩ => ⟨E n,(hS _).mpr ⟨n,rfl⟩,hp⟩⟩
  refine ⟨F,hFM,hF,fun _ h => (ZFSet.mem_sep.mp h).1,?_⟩
  by_cases hempty : F = ∅
  · exact Or.inl hempty
  · right
    apply InternalCountableUnion.internally_countable_union M F S hM hT hFM hSM
    · intro H hH p hp
      obtain ⟨n,rfl⟩ := (hS H).mp hH
      exact (hF p).mpr ⟨n,hp⟩
    · intro H hH
      obtain ⟨n,rfl⟩ := (hS H).mp hH
      exact CohenCountedAntichain.every_internal_antichain_counted M A (E n) hM hT hA
        (hE n).1 (hE n).2.1 (hE n).2.2
    · exact fun n => (hS _).mpr ⟨n,rfl⟩
    · exact hB
    · exact fun p hp => (hF p).mp hp
    · by_contra h
      apply hempty
      apply ZFSet.ext; intro p
      exact ⟨fun hp => False.elim (h ⟨p,hp⟩),fun hp => False.elim (ZFSet.notMem_empty p hp)⟩

theorem family_support_counted (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ E n ⊆ conditions A ∧ Anti (conditions A) (E n))
    (hB : orbitGraph E ∈ M) :
    ∃ S ∈ M, S ⊆ A ∧ (∀ x, x ∈ S ↔ ∃ n, ∃ p ∈ E n, x ∈ supportSet A p) ∧
      (S = ∅ ∨ InternallyCountable M S) := by
  obtain ⟨F,hFM,hF,hFc,hct⟩ := antichain_union_counted M A hM hT hA E hE hB
  refine ⟨used A F,used_mem M A F hM hT hA hFM,
    fun _ h => (ZFSet.mem_sep.mp h).1,?_,?_⟩
  · intro x
    simp only [used,ZFSet.mem_sep]
    constructor
    · rintro ⟨_,p,hp,hxp⟩
      obtain ⟨n,hp⟩ := (hF p).mp hp
      exact ⟨n,p,hp,hxp⟩
    · rintro ⟨n,p,hp,hxp⟩
      exact ⟨(ZFSet.mem_sep.mp hxp).1,p,(hF p).mpr ⟨n,hp⟩,hxp⟩
  · rcases hct with rfl|hct
    · left
      apply ZFSet.ext; intro x
      simp only [used,ZFSet.mem_sep,ZFSet.notMem_empty,false_and,exists_false,and_false]
    · exact used_counted M A F hM hT hA hFM hFc hct

theorem selected_family_support (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (U : ℕ → ZFSet.{0})
    (hU : ∀ n, U n ∈ M ∧ U n ⊆ conditions A) (hB : orbitGraph U ∈ M) :
    ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
      (∀ n, E n ∈ M ∧ CohenAntichainSelector.Selected (conditions A) (U n) (E n)) ∧
      ∃ S ∈ M, S ⊆ A ∧ (∀ x, x ∈ S ↔ ∃ n, ∃ p ∈ E n, x ∈ supportSet A p) ∧
        (S = ∅ ∨ InternallyCountable M S) := by
  obtain ⟨E,hE,hsel⟩ := CohenAntichainSelector.internal_antichain_family M A hM hT hA U hU hB
  refine ⟨E,hE,fun n => ⟨(hsel n).1,(hsel n).2.1⟩,?_⟩
  exact family_support_counted M A hM hT hA E
    (fun n => ⟨(hsel n).1,fun _ h => (hU n).2 ((hsel n).2.1.1 h),(hsel n).2.1.2.1⟩) hE

end TuringRigidity.CohenAntichainFamilySupport

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalPositiveNameFamily
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalPositiveNameFamily
open TransitiveNameModel BoundedSetTheory RecursiveNames AtomicForcing
variable {c : ZFSet.{0}} [Preorder (Conditions c)] [Top (Conditions c)]

theorem label_positive (τ : Name (Conditions c)) (n : ℕ) (p : Conditions c) :
    label c p ∈ positive τ n ↔ MemForces (Name.check (natSet n)) τ p := by
  rw [positive,ZFSet.mem_sep]
  exact ⟨fun ⟨_,q,hq,h⟩ => label_injective c hq ▸ h,
    fun h => ⟨label_mem c p,p,rfl,h⟩⟩

theorem internal_positive_family (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) {o : ZFSet.{0}} (hoM : o ∈ M)
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q)
    (τ : Name (Conditions c)) (hτ : τ.encode (label c) ∈ M) :
    orbitGraph (positive τ) ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  let B := orbitGraph (fun n => checkedCode (label c ⊤) (natSet n))
  have hBM : B ∈ M := InternalNaturalCheckSequence.natural_check_sequence M _ hM hT
    (hM c hc _ (label_mem c ⊤))
  have hrM := iterUnion_mem M hM hT.union hBM 2
  obtain ⟨d,hdM,hd,hboth⟩ := internal_transitive_container M hM hT.pairing hT.union hS
    hT.replacement.finitePrefix hT.infinity (pair_mem M hM hT.pairing hrM hτ)
  have hrd : iterUnion 2 B ∈ d := hd _ hboth _ (ZFSet.mem_pair.mpr (Or.inl rfl))
  have hτd : τ.encode (label c) ∈ d := hd _ hboth _ (ZFSet.mem_pair.mpr (Or.inr rfl))
  have hn (n : ℕ) : (Name.check (natSet n) : Name (Conditions c)).encode (label c) ∈ d := by
    rw [encode_check]
    exact hd _ hrd _ (second_mem_doubleUnion ((orbitGraph_pair _ n _).mpr rfl))
  obtain ⟨f,hfM,hf⟩ := internal_atomic_graph M hM hT.pairing hT.union hT.powerSet hS hdM hc hoM
  let k := ZFSet.prod d d
  have hkM := product_mem M hM hT.pairing hT.union hT.powerSet hS hdM hdM
  let e := cons d (cons c (cons k (cons o (cons f (cons B (fun _ => τ.encode (label c)))))))
  let φ : BoundedSetTheory.Formula := .existsMem 2 (.conj (.pairMem 2 0 8)
    (AtomicFormula.membership 3 4 5 6 7 0 9 1))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|_|i
    exact hdM; exact hc; exact hkM; exact hoM; exact hfM; exact hBM; exact hτ
  have hφ (n : ℕ) (p : Conditions c) :
      φ.Eval (cons (label c p) (cons (natSet n) e)) ↔ MemForces (Name.check (natSet n)) τ p := by
    simp only [φ,BoundedSetTheory.Formula.Eval,BoundedSetTheory.Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨v,_,hnv,hquery⟩
      have hv := (orbitGraph_pair _ n v).mp hnv
      have hv' : v = (Name.check (natSet n) : Name (Conditions c)).encode (label c) := by
        rw [encode_check]; exact hv
      clear hv
      subst v
      exact (eval_membership hd ho hf (Name.check (natSet n)) τ (hn n) hτd p
        _ 3 4 5 6 7 0 9 1 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩).mp hquery
    · intro h
      refine ⟨(Name.check (natSet n) : Name (Conditions c)).encode (label c),hn n,?_,?_⟩
      · apply (orbitGraph_pair _ n _).mpr
        exact encode_check _ _
      · exact (eval_membership hd ho hf (Name.check (natSet n)) τ (hn n) hτd p
          _ 3 4 5 6 7 0 9 1 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩).mpr h
  apply InternalSubsetSequence.subset_sequence M c hM hT hc φ e he (positive τ)
    (fun n p hp => (ZFSet.mem_sep.mp hp).1)
  intro n p hp
  obtain ⟨p,rfl⟩ := label_surjective c hp
  exact (hφ n p).trans (label_positive τ n p).symm

end TuringRigidity.InternalPositiveNameFamily

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenNiceNameConstruction
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenNiceNameConstruction
open TransitiveNameModel BoundedSetTheory RecursiveNames AtomicForcing CountableForcing
open CohenGroundPoset CohenAntichainSelector CohenInternalDecision InternalPositiveNameFamily
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

attribute [local instance] cohenTop

theorem positive_downward (A : ZFSet.{0}) (τ : Name (Conditions (conditions A))) (n : ℕ)
    (p q : ZFSet.{0}) (hp : p ∈ positive τ n) (hq : q ∈ conditions A) (hpq : p ⊆ q) :
    q ∈ positive τ n := by
  obtain ⟨p,rfl⟩ := label_surjective (conditions A) (ZFSet.mem_sep.mp hp).1
  obtain ⟨q,rfl⟩ := label_surjective (conditions A) hq
  exact (label_positive τ n q).mpr
    (mem_mono (Name.check (natSet n)) τ hpq ((label_positive τ n p).mp hp))

theorem selected_hit_iff (M A U E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hU : U ∈ M) (hE : E ∈ M) (hUc : U ⊆ conditions A)
    (hopen : ∀ p ∈ U, ∀ q ∈ conditions A, p ⊆ q → q ∈ U)
    (hsel : Selected (conditions A) U E)
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G) :
    (∃ p ∈ G.carrier, label (conditions A) p ∈ E) ↔
      ∃ p ∈ G.carrier, label (conditions A) p ∈ U := by
  have hb : below (conditions A) U = U := by
    apply ZFSet.ext; intro q
    rw [below,ZFSet.mem_sep]
    exact ⟨fun ⟨hq,p,hp,hpq⟩ => hopen p hp q hq hpq,
      fun hq => ⟨hUc hq,q,hq,fun _ h => h⟩⟩
  have hpred : ∀ p ∈ below (conditions A) U, ∃ q ∈ E, CohenAntichainStages.Comp (conditions A) p q := by
    rw [hb]; exact hsel.2.2
  have hd := decision_dense A U E hpred
  rw [hb] at hd
  have hDM := decision_mem M (conditions A) U E hM hT (conditions_mem M A hM hT hA) hU hE
  have hdense : Dense {p : Conditions (conditions A) | label (conditions A) p ∈ decision (conditions A) U E} := by
    intro p
    obtain ⟨q,hq,hpq⟩ := hd _ (label_mem _ p)
    obtain ⟨q,rfl⟩ := label_surjective (conditions A) (ZFSet.mem_sep.mp hq).1
    exact ⟨q,hpq,hq⟩
  constructor
  · rintro ⟨p,hp,hpE⟩
    exact ⟨p,hp,hsel.1 hpE⟩
  · rintro ⟨q,hq,hqU⟩
    obtain ⟨p,hp,hpD⟩ := hG _ hDM hdense
    rcases (ZFSet.mem_sep.mp hpD).2 with ⟨a,ha,hap⟩|hneg
    · obtain ⟨a,rfl⟩ := label_surjective (conditions A) (hUc (hsel.1 ha))
      exact ⟨a,G.upper hap hp,ha⟩
    · obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
      exact False.elim (hneg _ (hopen _ hqU _ (label_mem _ r) hrq) hrp)

theorem selected_nice_value (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (τ : Name (Conditions (conditions A))) (hτ : τ.encode (label (conditions A)) ∈ M)
    (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ M ∧ Selected (conditions A) (positive τ n) (E n))
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G)
    (hreal : τ.val G.carrier ⊆ ZFSet.omega) :
    (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier = τ.val G.carrier := by
  have hc := conditions_mem M A hM hT hA
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  have hB := internal_positive_family M hM hT hc ho (InternalCollapse.orderSet_pair _) τ hτ
  have hUM (n : ℕ) : positive τ n ∈ M :=
    hM _ (iterUnion_mem M hM hT.union hB 2) _
      (second_mem_doubleUnion ((orbitGraph_pair (positive τ) n _).mpr rfl))
  obtain ⟨p,hp⟩ := G.nonempty
  have htop : (⊤ : Conditions (conditions A)) ∈ G.carrier := G.upper le_top hp
  have hbits (n : ℕ) : (∃ p ∈ G.carrier, label (conditions A) p ∈ E n) ↔
      natSet n ∈ τ.val G.carrier := by
    rw [selected_hit_iff M A _ _ hM hT hA (hUM n) (hE n).1
      (fun _ h => (ZFSet.mem_sep.mp h).1) (fun p hp q hq hpq => positive_downward A τ n p q hp hq hpq) (hE n).2 G hG]
    have hnM := encoded_check_mem_of_container M (conditions A) ZFSet.omega hM hT.pairing
      hT.union hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
      hc (sourceT_omega_mem M hM hT) omega_transitive ((mem_omega _).mpr ⟨n,rfl⟩)
    have hh := (internal_atomic_truth M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc ho
      (InternalCollapse.orderSet_pair _) G hG (Name.check (natSet n)) τ hnM hτ).2
    rw [Name.val_check _ htop] at hh
    simpa only [label_positive] using hh.symm
  apply ZFSet.ext; intro x
  rw [InternalNiceName.mem_val_nice E G.carrier htop x]
  constructor
  · rintro ⟨n,p,hp,hpE,rfl⟩
    exact (hbits n).mp ⟨p,hp,hpE⟩
  · intro hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp (hreal hx)
    obtain ⟨p,hp,hpE⟩ := (hbits n).mpr hx
    exact ⟨n,p,hp,hpE,rfl⟩

theorem internal_nice_name_oai (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (τ : Name (Conditions (conditions A))) (hτ : τ.encode (label (conditions A)) ∈ M) :
    ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
      (∀ n, E n ∈ M ∧ Selected (conditions A) (positive τ n) (E n)) ∧
      (InternalNiceName.nice E : Name (Conditions (conditions A))).encode (label (conditions A)) ∈ M ∧
      (∃ S ∈ M, S ⊆ A ∧ (∀ x, x ∈ S ↔ ∃ n, ∃ p ∈ E n, x ∈ CohenInternalSupport.supportSet A p) ∧
        (S = ∅ ∨ InternallyCountable M S)) ∧
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        τ.val G.carrier ⊆ ZFSet.omega →
        (InternalNiceName.nice E : Name (Conditions (conditions A))).val G.carrier = τ.val G.carrier := by
  have hc := conditions_mem M A hM hT hA
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  have hB := internal_positive_family M hM hT hc ho (InternalCollapse.orderSet_pair _) τ hτ
  have hU (n : ℕ) : positive τ n ∈ M ∧ positive τ n ⊆ conditions A :=
    ⟨hM _ (iterUnion_mem M hM hT.union hB 2) _
      (second_mem_doubleUnion ((orbitGraph_pair (positive τ) n _).mpr rfl)),
      fun _ h => (ZFSet.mem_sep.mp h).1⟩
  obtain ⟨E,hgraph,hE,hS⟩ := CohenAntichainFamilySupport.selected_family_support M A hM hT hA
    (positive τ) hU hB
  exact ⟨E,hgraph,hE,InternalNiceName.nice_internal M hM hT hc E
      (fun n => ⟨(hE n).1,fun _ h => (hU n).2 ((hE n).2.1 h)⟩) hgraph,hS,
    fun G hG hreal => selected_nice_value M A hM hT hA τ hτ E hE G hG hreal⟩

end TuringRigidity.CohenNiceNameConstruction

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name_oai := @OAI.TuringRigidity.CohenNiceNameConstruction.internal_nice_name_oai
