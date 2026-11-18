-- Prove2me | solution 1 for GreedyColoringLCA969.LowerBound.finite_amplification
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:25:36.801216+00:00
-- url     : https://prove2.me/submissions/71b1b039-58e6-4c52-84b4-178aa062d461

import Definitions.Def_GreedyColoringLCA969_LowerBound_Performance
import Theorems.Thm_GreedyColoringLCA969_LowerBound_observation_3_5
import Mathlib
import Definitions.Def_GreedyColoringLCA969_LowerBound_Distribution
import Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics
import Theorems.Thm_GreedyColoringLCA969_LowerBound_lemma_3_6
import Theorems.Thm_GreedyColoringLCA969_LowerBound_lemma_3_4

open scoped ENNReal Classical BigOperators
open MeasureTheory
namespace GreedyColoringLCA969.LowerBound

def queryVertex {n : ℕ} (q : GraphQuery .standard n) : Fin n :=
  match q with
  | .inl v => v
  | .inr (v, _) => v

noncomputable def traceVertices {n : ℕ} (A : Algorithm .standard)
    (R : Representation n) (r : Tape) (v : Fin n) : ℕ → Finset (Fin n)
  | 0 => ∅
  | t + 1 =>
    let s := run A R r v t
    match s.2.2 with
    | some _ => traceVertices A R r v t
    | none => match A n v s.1 with
      | .query q => insert (queryVertex q) (traceVertices A R r v t)
      | _ => traceVertices A R r v t

theorem trace_card_le_counter {n : ℕ} (A : Algorithm .standard)
    (R : Representation n) (r : Tape) (v : Fin n) (t : ℕ) :
    (traceVertices A R r v t).card ≤ (run A R r v t).2.1 := by
  classical
  induction t with
  | zero => simp [traceVertices, run]
  | succ t ih =>
    cases hs : (run A R r v t).2.2 with
    | some a => simpa [traceVertices, run, step, hs] using ih
    | none =>
      cases ha : A n v (run A R r v t).1 with
      | query q =>
        simp only [traceVertices, hs, ha, run, step]
        exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)
      | halt c => simpa [traceVertices, hs, ha, run, step] using ih
      | tick => simpa [traceVertices, hs, ha, run, step] using ih
      | readBit j => simpa [traceVertices, hs, ha, run, step] using ih

theorem run_preserved {n : ℕ} (A : Algorithm .standard)
    (R R' : Representation n) (r : Tape) (v : Fin n) (t : ℕ)
    (h : ∀ u ∈ traceVertices A R r v t, R'.val u = R.val u) :
    run A R' r v t = run A R r v t := by
  classical
  induction t with
  | zero => rfl
  | succ t ih =>
    have hsub : traceVertices A R r v t ⊆ traceVertices A R r v (t + 1) := by
      simp only [traceVertices]
      split
      · exact le_rfl
      · split <;> first | exact Finset.subset_insert _ _ | exact le_rfl
    have hprev := ih (fun u hu => h u (hsub hu))
    simp only [run, hprev]
    cases hs : (run A R r v t).2.2 with
    | some a => simp [step, hs]
    | none =>
      cases ha : A n v (run A R r v t).1 with
      | halt c => simp [step, hs, ha]
      | tick => simp [step, hs, ha]
      | readBit j => simp [step, hs, ha]
      | query q =>
        have hq := h (queryVertex q) (by simp [traceVertices, hs, ha])
        have hreply : oracleReply .standard R' q = oracleReply .standard R q := by
          cases q with
          | inl u => simpa [oracleReply, queryVertex] using congrArg List.length hq
          | inr p => rcases p with ⟨u,i⟩; simp only [queryVertex] at hq; simp [oracleReply, hq]
        simp [step, hs, ha, hreply]

theorem run_stable {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (r : Tape) (v : Fin n) {t : ℕ} {c : ℕ+}
    (h : (run A R r v t).2.2 = some c) {s : ℕ} (hts : t ≤ s) :
    run A R r v s = run A R r v t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hts
  clear hts
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, run, ih]
    simp only [step, h]

theorem returns_unique {m : OracleMode} {n : ℕ} (A : Algorithm m)
    (R : Representation n) (r : Tape) (v : Fin n) {a b : ℕ+}
    (ha : Returns A R r v a) (hb : Returns A R r v b) : a = b := by
  obtain ⟨t, ht⟩ := ha
  obtain ⟨s, hs⟩ := hb
  rcases le_total t s with hts | hst
  · have heq := congrArg (fun z : Config => z.2.2) (run_stable A R r v ht hts)
    rw [ht, hs] at heq
    exact Option.some.inj heq.symm
  · have heq := congrArg (fun z : Config => z.2.2) (run_stable A R r v hs hst)
    rw [ht, hs] at heq
    exact Option.some.inj heq

theorem finite_cost_trace {n : ℕ} (A : Algorithm .standard)
    (R : Representation n) (r : Tape) (v : Fin n) (hfinite : queryCost A R r v ≠ ⊤) :
    ∃ c : ℕ+, ∃ Q : Finset (Fin n), Returns A R r v c ∧
      (Q.card : ℝ≥0∞) ≤ queryCost A R r v ∧
      ∀ R' : Representation n, (∀ u ∈ Q, R'.val u = R.val u) → Returns A R' r v c := by
  classical
  have hterm : ∃ t, (run A R r v t).2.2 ≠ none := by
    by_contra hn
    exact hfinite (by simp [queryCost, hn])
  obtain ⟨t, ht⟩ := hterm
  obtain ⟨c, hc⟩ : ∃ c, (run A R r v t).2.2 = some c := Option.ne_none_iff_exists'.mp ht
  refine ⟨c, traceVertices A R r v t, ⟨t, hc⟩, ?_, ?_⟩
  · calc
      _ ≤ ((run A R r v t).2.1 : ℝ≥0∞) := by exact_mod_cast trace_card_le_counter A R r v t
      _ ≤ queryCost A R r v := by rw [queryCost, if_pos ⟨t, ht⟩]; exact le_iSup (fun s : ℕ => ((run A R r v s).2.1 : ℝ≥0∞)) t
  · intro R' hR'
    exact ⟨t, by rw [run_preserved A R R' r v t hR']; exact hc⟩

end GreedyColoringLCA969.LowerBound

open scoped ENNReal Classical BigOperators
open MeasureTheory
namespace GreedyColoringLCA969.LowerBound

noncomputable section

def copyIndex {N n : ℕ} (v : Fin (N * n)) : Fin N := (finProdFinEquiv.symm v).1

def copyVertex {N n : ℕ} (v : Fin (N * n)) : Fin n := (finProdFinEquiv.symm v).2

def inCopy {N n : ℕ} (i : Fin N) (v : Fin n) : Fin (N * n) := finProdFinEquiv (i,v)

@[simp] theorem copyIndex_inCopy {N n : ℕ} (i : Fin N) (v : Fin n) : copyIndex (inCopy i v) = i := by simp [copyIndex, inCopy]
@[simp] theorem copyVertex_inCopy {N n : ℕ} (i : Fin N) (v : Fin n) : copyVertex (inCopy i v) = v := by simp [copyVertex, inCopy]
@[simp] theorem inCopy_decode {N n : ℕ} (v : Fin (N*n)) : inCopy (copyIndex v) (copyVertex v) = v := by
  change finProdFinEquiv (finProdFinEquiv.symm v) = v
  exact finProdFinEquiv.apply_symm_apply v

def copiesGraph {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) : SimpleGraph (Fin (N*n)) where
  Adj u v := copyIndex u = copyIndex v ∧ G.Adj (copyVertex u) (copyVertex v)
  symm.symm u v h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl u h := G.irrefl h.2

@[simp] theorem copies_adj {N n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin N) (u v : Fin n) :
    (copiesGraph G N).Adj (inCopy i u) (inCopy j v) ↔ i = j ∧ G.Adj u v := by
  simp [copiesGraph]

def canonicalRepresentation {n : ℕ} (G : SimpleGraph (Fin n)) : Representation n :=
  ⟨G, ⟨fun v => (G.neighborFinset v).toList, fun _ => List.Perm.refl _⟩⟩

/-- Keep the original order of every surviving adjacency entry. -/
def restrictedRepresentation {n : ℕ} (R : Representation n) (G : SimpleGraph (Fin n))
    (hG : G ≤ R.graph) : Representation n :=
  ⟨G, ⟨fun v => (R.val v).filter (fun u => decide (G.Adj v u)), by
    intro v
    apply List.perm_iff_count.mpr
    intro u
    have hperm := R.2.perm v
    have hnR : (R.val v).Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
    have hnG : ((R.val v).filter (fun u => decide (G.Adj v u))).Nodup := hnR.filter _
    have hmem : u ∈ (R.val v).filter (fun u => decide (G.Adj v u)) ↔ G.Adj v u := by
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · exact And.right
      · intro hu
        refine ⟨?_,hu⟩
        exact (hperm.mem_iff).mpr (by simpa [Representation.graph] using hG hu)
    rw [hnG.count, (Finset.nodup_toList _).count]
    simp [hmem]⟩⟩

theorem restricted_val_eq {n : ℕ} (R : Representation n) (G : SimpleGraph (Fin n))
    (hG : G ≤ R.graph) (v : Fin n) (h : ∀ u, R.graph.Adj v u → G.Adj v u) :
    (restrictedRepresentation R G hG).val v = R.val v := by
  apply List.filter_eq_self.mpr
  intro u hu
  have huR : R.graph.Adj v u := by
    have hh := (R.2.perm v).mem_iff.mp hu
    simpa [Representation.graph] using hh
  simpa using h u huR

def copyNeighborEquiv {N n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin (N*n)) :
    (copiesGraph G N).neighborSet v ≃ G.neighborSet (copyVertex v) where
  toFun w := ⟨copyVertex w.val, w.prop.2⟩
  invFun w := ⟨inCopy (copyIndex v) w.val, by
    change copyIndex v = copyIndex (inCopy (copyIndex v) w.val) ∧ G.Adj (copyVertex v) (copyVertex (inCopy (copyIndex v) w.val))
    constructor
    · simp
    · simpa only [copyVertex_inCopy, SimpleGraph.mem_neighborSet] using w.prop⟩
  left_inv w := by
    apply Subtype.ext
    have hi := w.prop.1
    change inCopy (copyIndex v) (copyVertex w.val) = w.val
    rw [hi]
    exact inCopy_decode w.val
  right_inv w := by apply Subtype.ext; simp

theorem copies_maxDegree {n N : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℝ)
    (hG : MaxDegreeAtMost G Δ) : MaxDegreeAtMost (copiesGraph G N) Δ := by
  intro v
  have hcard := Nat.card_congr (copyNeighborEquiv G v)
  change (Nat.card ((copiesGraph G N).neighborSet v) : ℝ) ≤ Δ
  rw [hcard]
  exact hG (copyVertex v)

theorem extend_partial_coloring {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (c : Fin n → ℕ+)
    (hc : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) :
    ∃ c' : Fin n → ℕ+, IsProper G c' ∧ ∀ v ∈ S, c' v = c v := by
  classical
  let M := ∑ v : Fin n, (c v).val
  have hM (v : Fin n) : (c v).val ≤ M :=
    Finset.single_le_sum (f := fun w : Fin n => (c w).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  let fresh (v : Fin n) : ℕ+ := ⟨M + v.val + 1, by omega⟩
  let c' := fun v => if v ∈ S then c v else fresh v
  refine ⟨c', ?_, ?_⟩
  · intro u v huv heq
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · exact hc u hu v hv huv (by simpa [c',hu,hv] using heq)
    · have hh := congrArg PNat.val heq
      simp [c',hu,hv,fresh] at hh
      have := hM u
      omega
    · have hh := congrArg PNat.val heq
      simp [c',hu,hv,fresh] at hh
      have := hM v
      omega
    · have hh := congrArg PNat.val heq
      simp [c',hu,hv,fresh] at hh
      have huv' : u = v := Fin.ext (by omega)
      exact huv.ne huv'
  · intro v hv
    simp [c',hv]

theorem copies_many_high {N n : ℕ} (G : SimpleGraph (Fin n)) (ε K : ℝ)
    (hG : ∀ c : Fin n → ℕ+, IsProper G c →
      (1 - ε) * (n : ℝ) ≤ (Nat.card {v : Fin n // K ≤ ((c v).val : ℝ)} : ℝ))
    (c : Fin (N*n) → ℕ+) (hc : IsProper (copiesGraph G N) c) :
    (1 - ε) * (N*n : ℕ) ≤ (Nat.card {v : Fin (N*n) // K ≤ ((c v).val : ℝ)} : ℝ) := by
  classical
  have hlocal (i : Fin N) : (1 - ε) * (n : ℝ) ≤
      (Nat.card {v : Fin n // K ≤ ((c (inCopy i v)).val : ℝ)} : ℝ) := by
    apply hG
    intro u v huv
    exact hc _ _ ((copies_adj G i i u v).mpr ⟨rfl,huv⟩)
  have hcard : Nat.card {v : Fin (N*n) // K ≤ ((c v).val : ℝ)} =
      ∑ i : Fin N, Nat.card {v : Fin n // K ≤ ((c (inCopy i v)).val : ℝ)} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    rfl
  rw [hcard, Nat.cast_sum]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlocal i)
  simpa [mul_comm,mul_left_comm,mul_assoc] using hsum

theorem useful_count {n : ℕ} (G : SimpleGraph (Fin n)) (ε K : ℝ)
    (hG : ∀ c : Fin n → ℕ+, IsProper G c →
      (1 - ε / 4) * (n : ℝ) ≤ (Nat.card {v : Fin n // K ≤ ((c v).val : ℝ)} : ℝ))
    (S : Finset (Fin n)) (c : Fin n → ℕ+)
    (hS : ε / 2 * (n : ℝ) ≤ S.card)
    (hc : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) :
    ε / 4 * (n : ℝ) ≤ ((S.filter (fun v => K ≤ ((c v).val : ℝ))).card : ℝ) := by
  classical
  obtain ⟨c', hc', hcc⟩ := extend_partial_coloring G S c hc
  have hhigh := hG c' hc'
  let High := Finset.univ.filter (fun v => K ≤ ((c' v).val : ℝ))
  have hcard : Nat.card {v : Fin n // K ≤ ((c' v).val : ℝ)} = High.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard] at hhigh
  have hinter : S ∩ High = S.filter (fun v => K ≤ ((c v).val : ℝ)) := by
    ext v
    by_cases hv : v ∈ S
    · simp [High,hv,hcc v hv]
    · simp [hv]
  have hcount := Finset.card_union_add_card_inter S High
  have hunion := Finset.card_le_univ (s := S ∪ High)
  have hcount' : ((S ∪ High).card : ℝ) + ((S ∩ High).card : ℝ) = S.card + High.card := by exact_mod_cast hcount
  have hunion' : ((S ∪ High).card : ℝ) ≤ n := by simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hunion : ((S ∪ High).card : ℝ) ≤ Fintype.card (Fin n))
  rw [hinter] at hcount'
  linarith

end
end GreedyColoringLCA969.LowerBound

open scoped Classical
open SimpleGraph
namespace GreedyColoringLCA969.LowerBound

theorem forest_bound {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
    (c : Fin n → ℕ+) (hc : IsGreedy G c) (v : Fin n) : 2 ^ ((c v).val - 1) ≤ n := by
  classical
  let C := G.connectedComponentMk v
  let V := C.supp
  let k := Fintype.card V
  let e : V ≃ Fin k := Fintype.equivFin V
  let T : SimpleGraph (Fin k) := C.toSimpleGraph.comap e.symm
  let iso : T ≃g C.toSimpleGraph := ⟨e.symm, by intros; rfl⟩
  have hT : T.IsTree := iso.isTree_iff.mpr (hG.isTree_connectedComponent C)
  let c' : Fin k → ℕ+ := fun w => c (e.symm w).val
  have hc' : IsGreedy T c' := by
    constructor
    · intro u w huw
      exact hc.1 _ _ huw
    · intro w j hj
      obtain ⟨u, hu, hcu⟩ := hc.2 (e.symm w).val j hj
      have huC : u ∈ C.supp := by
        exact C.mem_supp_of_adj_mem_supp (e.symm w).prop hu
      refine ⟨e ⟨u, huC⟩, ?_, ?_⟩
      · change G.Adj (e.symm w).val (e.symm (e ⟨u,huC⟩)).val
        simpa using hu
      · change c (e.symm (e ⟨u,huC⟩)).val = j
        simpa using hcu
  have hv : v ∈ C.supp := by simp [C]
  have hbound := observation_3_5 k T hT c' hc' (e ⟨v,hv⟩)
  have hk : k ≤ n := by
    exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
  apply le_trans _ hk
  simpa [c'] using hbound

theorem small_support_greedy_bound {n : ℕ} (G H : SimpleGraph (Fin n)) (hHG : H ≤ G)
    (g : ℝ) (hg : GirthAtLeast G g) (W : Finset (Fin n)) (hW : (W.card : ℝ) < g)
    (hsupport : ∀ u v, H.Adj u v → u ∈ W ∧ v ∈ W)
    (c : Fin n → ℕ+) (hc : IsGreedy H c) (v : Fin n) (hv : v ∈ W) :
    2 ^ ((c v).val - 1) ≤ W.card := by
  classical
  let e : Fin W.card ≃ W := (Fintype.equivFinOfCardEq (by simp : Fintype.card W = W.card)).symm
  let T : SimpleGraph (Fin W.card) := H.comap (fun i => (e i).val)
  let f : T →g G := ⟨fun i => (e i).val, fun h => hHG h⟩
  have hfinj : Function.Injective f := Subtype.val_injective.comp e.injective
  have hT : T.IsAcyclic := by
    intro u p hp
    have hcycle := hp.map hfinj
    have hlow := hg (f u) (p.map f) hcycle
    have hlen : p.length ≤ W.card := by
      have hh := hp.support_nodup.length_le_card
      simpa only [List.length_tail, Walk.length_support, Nat.add_sub_cancel, Fintype.card_fin] using hh
    have hlenr : (p.length : ℝ) ≤ W.card := by exact_mod_cast hlen
    simp only [Walk.length_map] at hlow
    linarith
  let c' : Fin W.card → ℕ+ := fun i => c (e i).val
  have hc' : IsGreedy T c' := by
    constructor
    · intro i j hij
      exact hc.1 _ _ hij
    · intro i k hki
      obtain ⟨w, hw, hcw⟩ := hc.2 (e i).val k hki
      have hwW := (hsupport _ _ hw).2
      refine ⟨e.symm ⟨w,hwW⟩, ?_, ?_⟩
      · change H.Adj (e i).val (e (e.symm ⟨w,hwW⟩)).val
        simpa using hw
      · change c (e (e.symm ⟨w,hwW⟩)).val = k
        simpa using hcw
  have hb := forest_bound T hT c' hc' (e.symm ⟨v,hv⟩)
  simpa [c'] using hb

end GreedyColoringLCA969.LowerBound

open scoped ENNReal BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace GreedyColoringLCA969.LowerBound
noncomputable section

def dependsOn {ι : Type} (E : Set (ι → Bool)) (K : Finset ι) : Prop :=
  ∀ x y, (∀ i ∈ K, x i = y i) → (x ∈ E ↔ y ∈ E)

def extendBlock {ι : Type} (K : Finset ι) (x : K → Bool) (i : ι) : Bool :=
  if hi : i ∈ K then x ⟨i,hi⟩ else false

theorem block_preimage {ι : Type} (K : Finset ι) (E : Set (ι → Bool))
    (hE : dependsOn E K) :
    E = (fun x : ι → Bool => K.restrict x) ⁻¹' {y | extendBlock K y ∈ E} := by
  classical
  ext x
  apply hE
  intro i hi
  simp [extendBlock, hi]

theorem independent_blocks {ι : Type} [Fintype ι] (μ : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (S T : Finset ι) (hST : Disjoint S T)
    (E F : Set (ι → Bool)) (hE : dependsOn E S) (hF : dependsOn F T) :
    (Measure.pi μ) (E ∩ F) = (Measure.pi μ) E * (Measure.pi μ) F := by
  classical
  have hind : iIndepFun (fun i (x : ι → Bool) => x i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hpair := hind.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  rw [block_preimage S E hE, block_preimage T F hF]
  exact hpair.measure_inter_preimage_eq_mul _ _ (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet

theorem intersection_depends {ι κ : Type} (K : κ → Finset ι) (E : κ → Set (ι → Bool))
    (s : Finset κ) (hE : ∀ i ∈ s, dependsOn (E i) (K i)) :
    dependsOn {x | ∀ i ∈ s, x ∈ E i} (s.biUnion K) := by
  intro x y hxy
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  exact hE i hi x y (fun j hj => hxy j (Finset.mem_biUnion.mpr ⟨i,hi,hj⟩))

theorem disjoint_blocks_product {ι κ : Type} [Fintype ι] (μ : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (K : κ → Finset ι) (E : κ → Set (ι → Bool))
    (s : Finset κ) (hK : Set.Pairwise (↑s : Set κ) (fun i j => Disjoint (K i) (K j)))
    (hE : ∀ i ∈ s, dependsOn (E i) (K i)) :
    (Measure.pi μ) {x | ∀ i ∈ s, x ∈ E i} = ∏ i ∈ s, (Measure.pi μ) (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hdisj : Disjoint (K i) (s.biUnion K) := by
      apply Finset.disjoint_left.mpr
      intro j hji hjs
      obtain ⟨k,hks,hjk⟩ := Finset.mem_biUnion.mp hjs
      exact Finset.disjoint_left.mp (hK (by simp) (by simp [hks]) (by intro he; subst k; exact hi hks)) hji hjk
    have hset : {x | ∀ j ∈ insert i s, x ∈ E j} = E i ∩ {x | ∀ j ∈ s, x ∈ E j} := by ext x; simp
    rw [hset, independent_blocks μ (K i) (s.biUnion K) hdisj _ _ (hE i (by simp))
      (intersection_depends K E s (fun j hj => hE j (by simp [hj]))),
      ih (fun a ha b hb hab => hK (by simp [ha]) (by simp [hb]) hab) (fun j hj => hE j (by simp [hj])),
      Finset.prod_insert hi]

theorem pattern_probability {ι : Type} [Fintype ι] (p : unitInterval)
    (K : Finset ι) (a : ι → Bool) :
    (Measure.pi (fun _ : ι => bernoulliMeasure true false p)) {x | ∀ i ∈ K, x i = a i} =
      ∏ i ∈ K, if a i then ENNReal.ofReal (p : ℝ) else ENNReal.ofReal (1 - (p : ℝ)) := by
  classical
  have heq : {x : ι → Bool | ∀ i ∈ K, x i = a i} = (↑K : Set ι).pi (fun i => {a i}) := by ext x; simp
  rw [heq, Measure.pi_pi_finset]
  apply Finset.prod_congr rfl
  intro i _
  cases ha : a i <;> simp [bernoulliMeasure_apply, ha]
  all_goals rw [← ENNReal.ofReal_coe_nnreal]; rfl

theorem pattern_probability_lower {ι : Type} [Fintype ι] (p : unitInterval)
    (r : ℝ) (hr : 0 ≤ r) (hrp : r ≤ p) (hrp' : r ≤ 1 - (p : ℝ))
    (K : Finset ι) (a : ι → Bool) (b : ℕ) (hKb : K.card ≤ b) :
    ENNReal.ofReal (r ^ b) ≤
      (Measure.pi (fun _ : ι => bernoulliMeasure true false p)) {x | ∀ i ∈ K, x i = a i} := by
  classical
  rw [pattern_probability]
  have hr1 : r ≤ 1 := hrp.trans p.2.2
  calc
    _ ≤ ENNReal.ofReal (r ^ K.card) := ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one hr hr1 hKb)
    _ = ∏ _i ∈ K, ENNReal.ofReal r := by simp [ENNReal.ofReal_pow hr]
    _ ≤ ∏ i ∈ K, if a i then ENNReal.ofReal (p : ℝ) else ENNReal.ofReal (1 - (p : ℝ)) := by
      apply Finset.prod_le_prod'
      intro i _
      split <;> apply ENNReal.ofReal_le_ofReal <;> assumption

theorem disjoint_blocks_failure_bound {ι κ : Type} [Fintype ι] (μ : ι → Measure Bool)
    [∀ i, IsProbabilityMeasure (μ i)] (K : κ → Finset ι) (E : κ → Set (ι → Bool))
    (s : Finset κ) (hK : Set.Pairwise (↑s : Set κ) (fun i j => Disjoint (K i) (K j)))
    (hE : ∀ i ∈ s, dependsOn (E i) (K i)) (β b : ℝ) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hprob : ∀ i ∈ s, β ≤ (Measure.pi μ).real (E i))
    (Good Success : Set (ι → Bool)) (hgood : (Measure.pi μ).real Goodᶜ ≤ b)
    (hfail : ∀ x ∈ Good, ∀ i ∈ s, x ∈ E i → x ∉ Success) :
    (Measure.pi μ).real Success ≤ b + (1 - β) ^ s.card := by
  classical
  let P := Measure.pi μ
  have hno : P.real {x | ∀ i ∈ s, x ∉ E i} ≤ (1 - β) ^ s.card := by
    have hcompl : ∀ i ∈ s, dependsOn (E i)ᶜ (K i) := by
      intro i hi x y hxy
      exact not_congr (hE i hi x y hxy)
    have hprod := disjoint_blocks_product μ K (fun i => (E i)ᶜ) s hK hcompl
    have hprodReal := congrArg ENNReal.toReal hprod
    change P.real {x | ∀ i ∈ s, x ∉ E i} = _ at hprodReal
    rw [ENNReal.toReal_prod] at hprodReal
    rw [hprodReal]
    calc
      _ ≤ (∏ _i ∈ s, (1 - β : ℝ)) := by
        apply Finset.prod_le_prod (f := fun i => ((Measure.pi μ) (E i)ᶜ).toReal) (g := fun _ => (1 - β : ℝ))
        · intro i _; exact ENNReal.toReal_nonneg
        · intro i hi
          change P.real (E i)ᶜ ≤ 1 - β
          rw [measureReal_compl (Set.to_countable _).measurableSet]
          simpa [P] using sub_le_sub_left (hprob i hi) 1
      _ = (1 - β) ^ s.card := by simp
  have hsub : Success ⊆ Goodᶜ ∪ {x | ∀ i ∈ s, x ∉ E i} := by
    intro x hx
    by_cases hg : x ∈ Good
    · apply Or.inr
      intro i hi hxi
      exact hfail x hg i hi hxi hx
    · exact Or.inl hg
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hgood hno))

theorem all_true_failure_bound {ι : Type} [Fintype ι] (p : unitInterval) (K : Finset ι) :
    (Measure.pi (fun _ : ι => bernoulliMeasure true false p)).real
      {x | ∀ i ∈ K, x i = true}ᶜ ≤ (K.card : ℝ) * (1 - (p : ℝ)) := by
  classical
  rw [measureReal_compl (Set.to_countable _).measurableSet]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
  have hprob := pattern_probability p K (fun _ => true)
  simp only [if_true,Finset.prod_const] at hprob
  have hreal := congrArg ENNReal.toReal hprob
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal p.2.1] at hreal
  change 1 - ((Measure.pi (fun _ : ι => bernoulliMeasure true false p)) {x | ∀ i ∈ K, x i = true}).toReal ≤ _
  rw [hreal]
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ (p : ℝ) - 1 by linarith [p.2.1]) K.card
  have heq : 1 + ((p : ℝ) - 1) = p := by ring
  rw [heq] at hbern
  linarith

end
end GreedyColoringLCA969.LowerBound

open scoped ENNReal BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace GreedyColoringLCA969.LowerBound
noncomputable section

def deletedCopies {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ)
    (x : Fin N × Sym2 (Fin n) → Bool) : SimpleGraph (Fin (N*n)) where
  Adj u v := copyIndex u = copyIndex v ∧ G.Adj (copyVertex u) (copyVertex v) ∧
    x (copyIndex u, s(copyVertex u,copyVertex v)) = true
  symm.symm u v h := by
    refine ⟨h.1.symm, h.2.1.symm, ?_⟩
    simpa [h.1,Sym2.eq_swap] using h.2.2
  loopless.irrefl u h := G.irrefl h.2.1

theorem deletedCopies_le {N n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin N × Sym2 (Fin n) → Bool) : deletedCopies G N x ≤ copiesGraph G N := fun _ _ h => ⟨h.1,h.2.1⟩

def deletionInput {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ)
    (x : Fin N × Sym2 (Fin n) → Bool) : Input :=
  ⟨N*n, restrictedRepresentation (canonicalRepresentation (copiesGraph G N))
    (deletedCopies G N x) (deletedCopies_le G x)⟩

def deletionLaw {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) (p : unitInterval) : Measure Input :=
  (Measure.pi (fun _ : Fin N × Sym2 (Fin n) => bernoulliMeasure true false p)).map (deletionInput G N)

instance deletionLaw_probability {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) (p : unitInterval) :
    IsProbabilityMeasure (deletionLaw G N p) := Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem representation_ext {n : ℕ} (R R' : Representation n)
    (hG : R.graph = R'.graph) (hL : ∀ v, R.val v = R'.val v) : R = R' := by
  rcases R with ⟨G,L⟩
  rcases R' with ⟨G',L'⟩
  change G = G' at hG
  cases hG
  cases L with
  | mk lists perm =>
    cases L' with
    | mk lists' perm' =>
      have hh : lists = lists' := funext hL
      cases hh
      rfl

theorem deletionInput_full {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) :
    deletionInput G N (fun _ => true) = ⟨N*n,canonicalRepresentation (copiesGraph G N)⟩ := by
  have hgraph : deletedCopies G N (fun _ => true) = copiesGraph G N := by
    ext u v
    simp [deletedCopies,copiesGraph]
  apply congrArg (Sigma.mk (N*n))
  apply representation_ext
  · exact hgraph
  intro v
  apply restricted_val_eq
  intro u hu
  change (deletedCopies G N (fun _ => true)).Adj v u
  rw [hgraph]
  exact hu

theorem maxDegree_mono {n : ℕ} {G H : SimpleGraph (Fin n)} (hHG : H ≤ G)
    {Δ : ℝ} (hG : MaxDegreeAtMost G Δ) : MaxDegreeAtMost H Δ := by
  intro v
  have hh : Nat.card (H.neighborSet v) ≤ Nat.card (G.neighborSet v) := by
    apply Nat.card_le_card_of_injective (fun u : H.neighborSet v => (⟨u.val,hHG u.prop⟩ : G.neighborSet v))
    intro u w heq
    exact Subtype.ext (congrArg (fun z : G.neighborSet v => z.val) heq)
  exact (Nat.cast_le.mpr hh).trans (hG v)

theorem deletion_support_range {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) (p : unitInterval)
    (R : Input) (hR : InSupport (deletionLaw G N p) R) :
    ∃ x : Fin N × Sym2 (Fin n) → Bool, deletionInput G N x = R := by
  by_contra hn
  have hempty : (deletionInput G N) ⁻¹' {R} = ∅ := by
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
    exact fun h => hn ⟨x,h⟩
  unfold InSupport deletionLaw at hR
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton R), hempty, measure_empty] at hR
  exact (lt_irrefl 0) hR

theorem deletion_support_degree {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) (p : unitInterval)
    (Δ : ℝ) (hG : MaxDegreeAtMost G Δ) (R : Input) (hR : InSupport (deletionLaw G N p) R) :
    MaxDegreeAtMost R.2.graph Δ := by
  obtain ⟨x,rfl⟩ := deletion_support_range G N p R hR
  exact maxDegree_mono (deletedCopies_le G x) (copies_maxDegree G Δ hG)

theorem deletion_full_inSupport {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) (p : unitInterval)
    (hp : 0 < (p : ℝ)) :
    InSupport (deletionLaw G N p) ⟨N*n,canonicalRepresentation (copiesGraph G N)⟩ := by
  let x : Fin N × Sym2 (Fin n) → Bool := fun _ => true
  let P := Measure.pi (fun _ : Fin N × Sym2 (Fin n) => bernoulliMeasure true false p)
  have hevent : {x} = {y : Fin N × Sym2 (Fin n) → Bool | ∀ i ∈ (Finset.univ : Finset (Fin N × Sym2 (Fin n))), y i = true} := by
    ext y
    simp only [Set.mem_singleton_iff,Set.mem_ofPred_eq,Finset.mem_univ,forall_const]
    exact ⟨fun h => by rw [h]; intro _; rfl, fun h => funext h⟩
  have hmass : 0 < P {x} := by
    rw [hevent,pattern_probability p Finset.univ (fun _ => true)]
    simp only [if_true,Finset.prod_const,Finset.card_univ]
    positivity
  unfold InSupport deletionLaw
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  apply hmass.trans_le
  apply measure_mono
  intro y hy
  have hy' : y = x := hy
  subst y
  exact deletionInput_full G N

theorem distributional_deletion_success {n : ℕ} (G : SimpleGraph (Fin n)) (N : ℕ) (p : unitInterval)
    (A : Algorithm .standard) (r : Tape) :
    distributionalSuccess (A,r) (deletionLaw G N p) =
      (Measure.pi (fun _ : Fin N × Sym2 (Fin n) => bernoulliMeasure true false p))
        {x | r ∈ successEvent A (deletionInput G N x).2} := by
  unfold distributionalSuccess deletionLaw
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  rfl

theorem deletion_preserves_list {n N : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin N × Sym2 (Fin n) → Bool) (v : Fin (N*n))
    (h : ∀ e : Sym2 (Fin n), x (copyIndex v,e) = true) :
    (deletionInput G N x).2.val v = (canonicalRepresentation (copiesGraph G N)).val v := by
  apply restricted_val_eq (canonicalRepresentation (copiesGraph G N)) (deletedCopies G N x) (deletedCopies_le G x) v
  intro w hw
  exact ⟨hw.1,hw.2,h _⟩

end
end GreedyColoringLCA969.LowerBound


open scoped Classical BigOperators
namespace GreedyColoringLCA969.LowerBound
noncomputable section

def incidentGraph {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ (u ∈ Q ∨ v ∈ Q)
  symm.symm u v h := ⟨h.1.symm,h.2.symm⟩
  loopless.irrefl u h := G.irrefl h.1

theorem incident_high_color_impossible {n : ℕ} (G : SimpleGraph (Fin n))
    (Δ D K : ℕ) (hΔ : 1 ≤ Δ) (hD : 1 ≤ D)
    (hdegree : MaxDegreeAtMost G (Δ : ℝ))
    (hgirth : GirthAtLeast G (2 * Δ * D + 1 : ℕ))
    (hlarge : 2 * Δ * D < 2 ^ (K - 1))
    (Q : Finset (Fin n)) (hQ : Q.card < D)
    (c : Fin n → ℕ+) (hc : IsGreedy (incidentGraph G Q) c) (v : Fin n) :
    (c v).val < K := by
  classical
  let W := insert v (Q ∪ Q.biUnion (fun u => G.neighborFinset u))
  have hdegree' (u : Fin n) : (G.neighborFinset u).card ≤ Δ := by
    have hh := hdegree u
    change (Nat.card (G.neighborSet u) : ℝ) ≤ Δ at hh
    rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree] at hh
    exact_mod_cast hh
  have hWcard : W.card ≤ 2 * Δ * D := by
    calc
      _ ≤ (Q ∪ Q.biUnion (fun u => G.neighborFinset u)).card + 1 := Finset.card_insert_le _ _
      _ ≤ Q.card + (Q.biUnion (fun u => G.neighborFinset u)).card + 1 := Nat.add_le_add_right (Finset.card_union_le _ _) 1
      _ ≤ Q.card + (∑ u ∈ Q, (G.neighborFinset u).card) + 1 := Nat.add_le_add_right (Nat.add_le_add_left Finset.card_biUnion_le _) 1
      _ ≤ Q.card + (∑ _u ∈ Q, Δ) + 1 := by gcongr; exact hdegree' _
      _ = (Δ + 1) * Q.card + 1 := by simp; ring
      _ ≤ (Δ + 1) * (Q.card + 1) := by simp only [Nat.mul_add, Nat.mul_one]; omega
      _ ≤ (Δ + 1) * D := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (2 * Δ) * D := Nat.mul_le_mul_right _ (by omega)
  have hsupport : ∀ u w, (incidentGraph G Q).Adj u w → u ∈ W ∧ w ∈ W := by
    intro u w huw
    rcases huw.2 with hu | hw
    · constructor
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hu)
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨u,hu,(G.mem_neighborFinset u w).mpr huw.1⟩))
    · constructor
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨w,hw,(G.mem_neighborFinset w u).mpr huw.1.symm⟩))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hw)
  have hWg : (W.card : ℝ) < (2 * Δ * D + 1 : ℕ) := by exact_mod_cast (Nat.lt_succ_of_le hWcard)
  have hbound := small_support_greedy_bound G (incidentGraph G Q) (fun _ _ h => h.1)
    _ hgirth W hWg hsupport c hc v (Finset.mem_insert_self _ _)
  by_contra hnot
  have hcolor : K - 1 ≤ (c v).val - 1 := Nat.sub_le_sub_right (le_of_not_gt hnot) 1
  have hpow : 2 ^ (K - 1) ≤ 2 ^ ((c v).val - 1) := Nat.pow_le_pow_right (by omega) hcolor
  exact (not_lt_of_ge (hpow.trans (hbound.trans hWcard))) hlarge

end
end GreedyColoringLCA969.LowerBound

open scoped Classical
open Filter Asymptotics
namespace GreedyColoringLCA969.LowerBound

theorem exists_amplification_size (ε δ β : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (D : ℕ) (hD : 1 ≤ D) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ M : ℕ, ε / 4 * N ≤ M →
      2 ≤ M ∧ 2 * (D : ℝ) * log2 (M : ℝ) ^ D ≤ M ∧
      ∀ k : ℕ, log2 (M : ℝ) / (2 * D) ≤ k → (1 - β) ^ k ≤ δ / 10 := by
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD
  have htend := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - β) (by linarith : 1 - β < 1)
  obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 10))).exists
  have hsmall : ∀ᶠ x : ℝ in atTop, 2 * D * log2 x ^ D ≤ x := by
    have hh := (Real.isLittleO_pow_logb_id_atTop (b := 2) (n := D)).def (by positivity : (0 : ℝ) < 1 / (2 * D))
    filter_upwards [hh, eventually_ge_atTop (2 : ℝ)] with x hx hx2
    have hlog : 0 ≤ Real.logb 2 x := by
      exact (Real.logb_nonneg (by norm_num) (by linarith))
    simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog _), id_eq, abs_of_nonneg (by linarith : 0 ≤ x)] at hx
    change 2 * D * Real.logb 2 x ^ D ≤ x
    have hmul := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 2 * D)
    field_simp at hmul
    nlinarith
  have hlogbig : ∀ᶠ x : ℝ in atTop, (2 * D : ℝ) * k ≤ log2 x := by
    exact (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).eventually (eventually_ge_atTop _)
  obtain ⟨a, ha⟩ := eventually_atTop.mp ((eventually_ge_atTop (2 : ℝ)).and (hsmall.and hlogbig))
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (4 * a / ε))
  have hN1 : 1 ≤ N := by have := (le_max_left 1 (4*a/ε)).trans_lt hN; exact_mod_cast this.le
  have hNa : a ≤ ε / 4 * N := by
    have hh := (le_max_right 1 (4*a/ε)).trans_lt hN
    have hmul := (div_lt_iff₀ hε).mp hh
    linarith
  refine ⟨N, hN1, ?_⟩
  intro M hM
  have hMa : a ≤ (M : ℝ) := hNa.trans hM
  obtain ⟨hM2, hpack, hlog⟩ := ha M hMa
  refine ⟨by exact_mod_cast hM2, hpack, ?_⟩
  intro j hj
  have hkj : k ≤ j := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * D)).mp hj
    exact_mod_cast (show (k : ℝ) ≤ j by nlinarith)
  exact (pow_le_pow_of_le_one (by linarith) (by linarith) hkj).trans hk.le

end GreedyColoringLCA969.LowerBound

open scoped ENNReal BigOperators Classical
open MeasureTheory ProbabilityTheory
namespace GreedyColoringLCA969.LowerBound
noncomputable section

theorem cheap_certificates {n : ℕ} (A : Algorithm .standard) (R : Representation n)
    (r : Tape) (D : ℕ) (hD : 1 ≤ D) (S : Finset (Fin n))
    (hS : ∀ v ∈ S, queryCost A R r v ≤ ENNReal.ofReal ((D - 1 : ℕ) : ℝ)) :
    ∃ c : Fin n → ℕ+, ∃ Q : Fin n → Finset (Fin n),
      ∀ v ∈ S, Returns A R r v (c v) ∧ (Q v).card < D ∧
        ∀ R' : Representation n, (∀ u ∈ Q v, R'.val u = R.val u) → Returns A R' r v (c v) := by
  classical
  have hex (v : Fin n) : ∃ c : ℕ+, ∃ Q : Finset (Fin n), v ∈ S →
      Returns A R r v c ∧ Q.card < D ∧
        ∀ R' : Representation n, (∀ u ∈ Q, R'.val u = R.val u) → Returns A R' r v c := by
    by_cases hv : v ∈ S
    · have hfinite : queryCost A R r v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hS v hv)
      obtain ⟨c,Q,hret,hcard,hpres⟩ := finite_cost_trace A R r v hfinite
      refine ⟨c,Q,fun _ => ⟨hret,?_,hpres⟩⟩
      have hsize : Q.card ≤ D - 1 := by
        have hh := hcard.trans (hS v hv)
        rw [ENNReal.ofReal_natCast] at hh
        exact_mod_cast hh
      omega
    · exact ⟨1,∅,by simp [hv]⟩
  choose c Q h using hex
  exact ⟨c,Q,h⟩

def queryCopies {N n : ℕ} (v : Fin (N*n)) (Q : Finset (Fin (N*n))) : Finset (Fin N) :=
  insert (copyIndex v) (Q.image copyIndex)

theorem queryCopies_card {N n : ℕ} (v : Fin (N*n)) (Q : Finset (Fin (N*n))) :
    (queryCopies v Q).card ≤ Q.card + 1 := (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)

theorem monochromatic_returns_failure {n : ℕ} (A : Algorithm .standard) (R : Representation n)
    (r : Tape) (u v : Fin n) (c : ℕ+) (huv : R.graph.Adj u v)
    (hu : Returns A R r u c) (hv : Returns A R r v c) : r ∉ successEvent A R := by
  rintro ⟨colors,hgreedy,hret⟩
  have hcu := returns_unique A R r u hu (hret u)
  have hcv := returns_unique A R r v hv (hret v)
  exact hgreedy.1 u v huv (hcu.symm.trans hcv)

theorem cheap_pair_failure_bound {n N : ℕ} (G : SimpleGraph (Fin n)) (A : Algorithm .standard)
    (r : Tape) (p : unitInterval) (D : ℕ) (u v : Fin (N*n)) (c : ℕ+)
    (huv : (copiesGraph G N).Adj u v) (Qu Qv : Finset (Fin (N*n)))
    (hQu : Qu.card < D) (hQv : Qv.card < D)
    (hpresu : ∀ R' : Representation (N*n),
      (∀ z ∈ Qu, R'.val z = (canonicalRepresentation (copiesGraph G N)).val z) → Returns A R' r u c)
    (hpresv : ∀ R' : Representation (N*n),
      (∀ z ∈ Qv, R'.val z = (canonicalRepresentation (copiesGraph G N)).val z) → Returns A R' r v c) :
    (distributionalSuccess (A,r) (deletionLaw G N p)).toReal ≤
      (2 * D : ℝ) * Fintype.card (Sym2 (Fin n)) * (1 - (p : ℝ)) := by
  classical
  let T := queryCopies u Qu ∪ queryCopies v Qv
  let K := T ×ˢ (Finset.univ : Finset (Sym2 (Fin n)))
  let P := Measure.pi (fun _ : Fin N × Sym2 (Fin n) => bernoulliMeasure true false p)
  let Good : Set (Fin N × Sym2 (Fin n) → Bool) := {x | ∀ i ∈ K, x i = true}
  have hTcard : T.card ≤ 2 * D := by
    have hu := queryCopies_card u Qu
    have hv := queryCopies_card v Qv
    have hh := Finset.card_union_le (queryCopies u Qu) (queryCopies v Qv)
    dsimp [T]
    omega
  have hfail : ∀ x ∈ Good, r ∉ successEvent A (deletionInput G N x).2 := by
    intro x hx
    have hbits (i : Fin N) (hi : i ∈ T) (e : Sym2 (Fin n)) : x (i,e) = true :=
      hx (i,e) (Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩)
    have hretu := hpresu (deletionInput G N x).2 (fun z hz => deletion_preserves_list G x z (hbits _
      (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z,hz,rfl⟩)))))
    have hretv := hpresv (deletionInput G N x).2 (fun z hz => deletion_preserves_list G x z (hbits _
      (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z,hz,rfl⟩)))))
    have hadj : (deletionInput G N x).2.graph.Adj u v :=
      ⟨huv.1,huv.2,hbits _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _)) _⟩
    exact monochromatic_returns_failure A _ r u v c hadj hretu hretv
  rw [distributional_deletion_success]
  change P.real {x | r ∈ successEvent A (deletionInput G N x).2} ≤ _
  calc
    _ ≤ P.real Goodᶜ := measureReal_mono (fun x hx hg => hfail x hg hx)
    _ ≤ (K.card : ℝ) * (1 - (p : ℝ)) := all_true_failure_bound p K
    _ ≤ (2 * D : ℝ) * Fintype.card (Sym2 (Fin n)) * (1 - (p : ℝ)) := by
      have hK : (K.card : ℝ) ≤ (2 * D : ℝ) * Fintype.card (Sym2 (Fin n)) := by
        dsimp [K]
        rw [Finset.card_product,Finset.card_univ]
        exact_mod_cast Nat.mul_le_mul_right (Fintype.card (Sym2 (Fin n))) hTcard
      exact mul_le_mul_of_nonneg_right hK (by linarith [p.2.2])

def localQueries {N n : ℕ} (i : Fin N) (Q : Finset (Fin (N*n))) : Finset (Fin n) :=
  (Q.filter (fun v => copyIndex v = i)).image copyVertex

def badAssignment {N n : ℕ} (i : Fin N) (Q : Finset (Fin n)) (j : Fin N × Sym2 (Fin n)) : Bool :=
  if j.1 = i then decide (∃ v ∈ Q, v ∈ j.2) else true

@[simp] theorem badAssignment_own {N n : ℕ} (i : Fin N) (Q : Finset (Fin n)) (u v : Fin n) :
    badAssignment i Q (i,s(u,v)) = decide (u ∈ Q ∨ v ∈ Q) := by
  simp [badAssignment,Sym2.mem_iff,and_or_left,exists_or]

theorem bad_pattern_failure {n N : ℕ} (G : SimpleGraph (Fin n)) (A : Algorithm .standard)
    (r : Tape) (Δ D K : ℕ) (hΔ : 1 ≤ Δ) (hD : 1 ≤ D)
    (hdegree : MaxDegreeAtMost G (Δ : ℝ)) (hgirth : GirthAtLeast G (2 * Δ * D + 1 : ℕ))
    (hlarge : 2 * Δ * D < 2 ^ (K-1))
    (v : Fin (N*n)) (a : ℕ+) (ha : K ≤ a.val) (Q : Finset (Fin (N*n))) (hQ : Q.card < D)
    (hpres : ∀ R' : Representation (N*n),
      (∀ z ∈ Q, R'.val z = (canonicalRepresentation (copiesGraph G N)).val z) → Returns A R' r v a)
    (S : Finset (Fin N)) (hvS : copyIndex v ∉ S)
    (x : Fin N × Sym2 (Fin n) → Bool)
    (hgood : ∀ i ∈ S, ∀ e, x (i,e) = true)
    (hpattern : ∀ i ∈ queryCopies v Q \ S, ∀ e,
      x (i,e) = badAssignment (copyIndex v) (localQueries (copyIndex v) Q) (i,e)) :
    r ∉ successEvent A (deletionInput G N x).2 := by
  classical
  let i := copyIndex v
  let L := localQueries i Q
  have hiT : i ∈ queryCopies v Q \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _,hvS⟩
  have hown (u w : Fin n) : (deletedCopies G N x).Adj (inCopy i u) (inCopy i w) ↔ (incidentGraph G L).Adj u w := by
    simp only [deletedCopies,copyIndex_inCopy,copyVertex_inCopy,true_and]
    rw [hpattern i hiT s(u,w)]
    simp [badAssignment,incidentGraph,L,i,Sym2.mem_iff,and_or_left,exists_or]
  have hret : Returns A (deletionInput G N x).2 r v a := by
    apply hpres
    intro z hz
    apply restricted_val_eq (canonicalRepresentation (copiesGraph G N)) (deletedCopies G N x) (deletedCopies_le G x) z
    intro w hzw
    refine ⟨hzw.1,hzw.2,?_⟩
    by_cases hzS : copyIndex z ∈ S
    · exact hgood _ hzS _
    · have hzT : copyIndex z ∈ queryCopies v Q \ S := Finset.mem_sdiff.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z,hz,rfl⟩),hzS⟩
      rw [hpattern _ hzT]
      by_cases hzi : copyIndex z = i
      · have hzL : copyVertex z ∈ L := Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,hzi⟩,rfl⟩
        simp [badAssignment,hzi,show i = copyIndex v from rfl]
        exact ⟨copyVertex z,hzL,Or.inl rfl⟩
      · simp [badAssignment,show copyIndex z ≠ copyIndex v from hzi]
  rintro ⟨colors,hgreedy,hreturns⟩
  let c : Fin n → ℕ+ := fun w => colors (inCopy i w)
  have hc : IsGreedy (incidentGraph G L) c := by
    constructor
    · intro u w huw
      exact hgreedy.1 _ _ ((hown u w).mpr huw)
    · intro u k hku
      obtain ⟨z,huz,hcz⟩ := hgreedy.2 (inCopy i u) k hku
      have hzi : copyIndex z = i := by simpa using huz.1.symm
      have heqz : inCopy i (copyVertex z) = z := by rw [← hzi]; exact inCopy_decode z
      refine ⟨copyVertex z, (hown u (copyVertex z)).mp ?_, ?_⟩
      · rw [heqz]; exact huz
      · change colors (inCopy i (copyVertex z)) = k
        rw [heqz]; exact hcz
  have hLcard : L.card < D := (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans_lt hQ
  have hsmall := incident_high_color_impossible G Δ D K hΔ hD hdegree hgirth hlarge L hLcard c hc (copyVertex v)
  have heq : a = colors v := returns_unique A _ r v hret (hreturns v)
  have hcolor : (c (copyVertex v)).val = a.val := by simp [c,i,heq]
  rw [hcolor] at hsmall
  exact (not_lt_of_ge ha) hsmall

theorem proper_cheap_failure_bound {n N : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (hN : 1 ≤ N)
    (A : Algorithm .standard) (r : Tape) (p : unitInterval) (hp : (1 / 2 : ℝ) ≤ p) (hp1 : (p : ℝ) < 1)
    (Δ D K : ℕ) (hΔ : 1 ≤ Δ) (hD : 1 ≤ D)
    (hdegree : MaxDegreeAtMost G (Δ : ℝ)) (hgirth : GirthAtLeast G (2 * Δ * D + 1 : ℕ))
    (hlarge : 2 * Δ * D < 2 ^ (K-1)) (ε δ : ℝ)
    (hhigh : ∀ c : Fin n → ℕ+, IsProper G c →
      (1 - ε / 4) * (n : ℝ) ≤ (Nat.card {v : Fin n // (K : ℝ) ≤ ((c v).val : ℝ)} : ℝ))
    (hNsize : ∀ M : ℕ, ε / 4 * N ≤ M →
      2 ≤ M ∧ 2 * (D : ℝ) * log2 (M : ℝ) ^ D ≤ M ∧
      ∀ k : ℕ, log2 (M : ℝ) / (2 * D) ≤ k → (1 - (1 - (p : ℝ)) ^ (D * Fintype.card (Sym2 (Fin n)))) ^ k ≤ δ / 10)
    (S : Finset (Fin (N*n))) (hS : ε / 2 * (N*n : ℕ) ≤ S.card)
    (c : Fin (N*n) → ℕ+) (Q : Fin (N*n) → Finset (Fin (N*n)))
    (hcert : ∀ v ∈ S, Returns A (canonicalRepresentation (copiesGraph G N)) r v (c v) ∧ (Q v).card < D ∧
      ∀ R' : Representation (N*n), (∀ z ∈ Q v, R'.val z = (canonicalRepresentation (copiesGraph G N)).val z) → Returns A R' r v (c v))
    (hc : ∀ u ∈ S, ∀ v ∈ S, (copiesGraph G N).Adj u v → c u ≠ c v) :
    (distributionalSuccess (A,r) (deletionLaw G N p)).toReal ≤
      D * (Fintype.card (Sym2 (Fin n)) : ℝ) * (1 - (p : ℝ)) + δ / 10 := by
  classical
  let Useful := S.filter (fun v => (K : ℝ) ≤ ((c v).val : ℝ))
  have hUseful : ε / 4 * (N*n : ℕ) ≤ (Useful.card : ℝ) :=
    useful_count (copiesGraph G N) ε K (fun colors hcolors => copies_many_high G (ε / 4) K hhigh colors hcolors) S c hS hc
  let R := Useful.image copyIndex
  have hCopies : ε / 4 * (N : ℝ) ≤ R.card := by
    have hsub : Useful ⊆ (R ×ˢ (Finset.univ : Finset (Fin n))).image (fun z => inCopy z.1 z.2) := by
      intro v hv
      exact Finset.mem_image.mpr ⟨(copyIndex v,copyVertex v),Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨v,hv,rfl⟩,Finset.mem_univ _⟩,inCopy_decode v⟩
    have hcard : Useful.card ≤ R.card * n := (Finset.card_le_card hsub).trans
      (Finset.card_image_le.trans_eq (by rw [Finset.card_product,Finset.card_univ,Fintype.card_fin]))
    have hcard' : (Useful.card : ℝ) ≤ (R.card : ℝ) * n := by exact_mod_cast hcard
    apply (mul_le_mul_iff_right₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mp
    push_cast at hUseful
    nlinarith
  have hex (i : Fin N) : ∃ v : Fin (N*n), i ∈ R → v ∈ Useful ∧ copyIndex v = i := by
    by_cases hi : i ∈ R
    · obtain ⟨v,hv,hvi⟩ := Finset.mem_image.mp hi
      exact ⟨v,fun _ => ⟨hv,hvi⟩⟩
    · exact ⟨⟨0,Nat.mul_pos (by omega) hn⟩,by simp [hi]⟩
  choose root hroot using hex
  let T := fun i => queryCopies (root i) (Q (root i))
  have hrootS (i : Fin N) (hi : i ∈ R) : root i ∈ S := (Finset.mem_filter.mp (hroot i hi).1).1
  have hrootHigh (i : Fin N) (hi : i ∈ R) : K ≤ (c (root i)).val := by
    exact_mod_cast (Finset.mem_filter.mp (hroot i hi).1).2
  have hT (i : Fin N) (hi : i ∈ R) : (T i).card ≤ D :=
    (queryCopies_card _ _).trans (by have hh := (hcert _ (hrootS i hi)).2.1; omega)
  let H : Digraph N := fun i j => i ∈ R ∧ j ∈ T i
  have hOutEq (i : Fin N) (hi : i ∈ R) : outNeighbors H i = T i := by ext j; simp [outNeighbors,H,hi]
  have hOut : ∀ i, (outNeighbors H i).card ≤ D := by
    intro i
    by_cases hi : i ∈ R
    · rw [hOutEq i hi]; exact hT i hi
    · simp [outNeighbors,H,hi]
  have hLoops : ∀ i ∈ R, H i i := by
    intro i hi
    refine ⟨hi,?_⟩
    have hh := (hroot i hi).2
    change i ∈ queryCopies (root i) (Q (root i))
    exact Finset.mem_insert.mpr (Or.inl hh.symm)
  obtain ⟨hRsize,hRlarge,hRpow⟩ := hNsize R.card hCopies
  obtain ⟨U,Core,hUR,hUsize,hCore,hDisj,hInter⟩ := lemma_3_6 N D hD H hOut R hRsize hLoops hRlarge
  let Blocks := fun i => (T i \ Core) ×ˢ (Finset.univ : Finset (Sym2 (Fin n)))
  let Events := fun i => {x : Fin N × Sym2 (Fin n) → Bool | ∀ j ∈ Blocks i,
    x j = badAssignment (copyIndex (root i)) (localQueries (copyIndex (root i)) (Q (root i))) j}
  have hBlocks : Set.Pairwise (↑U : Set (Fin N)) (fun i j => Disjoint (Blocks i) (Blocks j)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    have hzi' := Finset.mem_sdiff.mp (Finset.mem_product.mp hzi).1
    have hzj' := Finset.mem_sdiff.mp (Finset.mem_product.mp hzj).1
    have hcommon : z.1 ∈ outNeighbors H i ∩ outNeighbors H j := by
      rw [hOutEq i (hUR hi),hOutEq j (hUR hj)]
      exact Finset.mem_inter.mpr ⟨hzi'.1,hzj'.1⟩
    exact hzi'.2 (hInter i hi j hj hij hcommon)
  have hDepends : ∀ i ∈ U, dependsOn (Events i) (Blocks i) := by
    intro i _ x y hxy
    constructor
    · intro hx z hz
      rw [← hxy z hz]
      exact hx z hz
    · intro hy z hz
      rw [hxy z hz]
      exact hy z hz
  let P := Measure.pi (fun _ : Fin N × Sym2 (Fin n) => bernoulliMeasure true false p)
  let β := (1 - (p : ℝ)) ^ (D * Fintype.card (Sym2 (Fin n)))
  have hβ : 0 ≤ β := pow_nonneg (by linarith [p.2.2]) _
  have hβ1 : β ≤ 1 := pow_le_one₀ (by linarith [p.2.2]) (by linarith [p.2.1])
  have hProb : ∀ i ∈ U, β ≤ P.real (Events i) := by
    intro i hi
    have hcard : (Blocks i).card ≤ D * Fintype.card (Sym2 (Fin n)) := by
      dsimp [Blocks]
      rw [Finset.card_product,Finset.card_univ]
      exact Nat.mul_le_mul_right _ ((Finset.card_le_card Finset.sdiff_subset).trans (hT i (hUR hi)))
    have hbound := pattern_probability_lower p (1 - (p : ℝ)) (by linarith [p.2.2]) (by linarith) le_rfl
      (Blocks i) (badAssignment (copyIndex (root i)) (localQueries (copyIndex (root i)) (Q (root i)))) _ hcard
    have hh := ENNReal.toReal_mono (measure_ne_top P (Events i)) hbound
    rw [ENNReal.toReal_ofReal (show 0 ≤ (1 - (p : ℝ)) ^ (D * Fintype.card (Sym2 (Fin n))) from hβ)] at hh
    change β ≤ (P (Events i)).toReal
    exact hh
  let CoreBlock := Core ×ˢ (Finset.univ : Finset (Sym2 (Fin n)))
  let Good : Set (Fin N × Sym2 (Fin n) → Bool) := {x | ∀ j ∈ CoreBlock, x j = true}
  have hGood : P.real Goodᶜ ≤ D * (Fintype.card (Sym2 (Fin n)) : ℝ) * (1 - (p : ℝ)) := by
    apply (all_true_failure_bound p CoreBlock).trans
    apply mul_le_mul_of_nonneg_right _ (by linarith [p.2.2])
    dsimp [CoreBlock]
    rw [Finset.card_product,Finset.card_univ,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCore) (by positivity)
  let Success := {x : Fin N × Sym2 (Fin n) → Bool | r ∈ successEvent A (deletionInput G N x).2}
  have hfail : ∀ x ∈ Good, ∀ i ∈ U, x ∈ Events i → x ∉ Success := by
    intro x hx i hi hxi
    have hiR := hUR hi
    have hiCore : copyIndex (root i) ∉ Core := by
      rw [(hroot i hiR).2]
      exact fun hh => Finset.disjoint_left.mp hDisj hi hh
    apply bad_pattern_failure G A r Δ D K hΔ hD hdegree hgirth hlarge (root i) (c (root i))
      (hrootHigh i hiR) (Q (root i)) (hcert _ (hrootS i hiR)).2.1 (hcert _ (hrootS i hiR)).2.2 Core hiCore x
    · intro j hj e
      exact hx (j,e) (Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩)
    · intro j hj e
      exact hxi (j,e) (Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩)
  have hbound := disjoint_blocks_failure_bound (fun _ : Fin N × Sym2 (Fin n) => bernoulliMeasure true false p)
    Blocks Events U hBlocks hDepends β _ hβ hβ1 hProb Good Success hGood hfail
  rw [distributional_deletion_success]
  change P.real Success ≤ _
  exact hbound.trans (add_le_add le_rfl (hRpow U.card hUsize))

theorem finite_deterministic_amplification {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (Δ D K : ℕ) (hΔ : 1 ≤ Δ) (hD : 1 ≤ D)
    (hdegree : MaxDegreeAtMost G (Δ : ℝ)) (hgirth : GirthAtLeast G (2 * Δ * D + 1 : ℕ))
    (hlarge : 2 * Δ * D < 2 ^ (K-1)) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hhigh : ∀ c : Fin n → ℕ+, IsProper G c →
      (1 - ε / 4) * (n : ℝ) ≤ (Nat.card {v : Fin n // (K : ℝ) ≤ ((c v).val : ℝ)} : ℝ)) :
    ∃ (N : ℕ) (p : unitInterval), 1 ≤ N ∧ 0 < (p : ℝ) ∧
      ∀ B : DeterministicLCA .standard,
        DeterministicEfficient B (canonicalRepresentation (copiesGraph G N)) ((D-1 : ℕ) : ℝ) (ε/2) →
          distributionalSuccess B (deletionLaw G N p) < ENNReal.ofReal (δ / 2) := by
  classical
  let m := Fintype.card (Sym2 (Fin n))
  have hm : 1 ≤ m := by
    letI : Nonempty (Sym2 (Fin n)) := ⟨s(⟨0,hn⟩,⟨0,hn⟩)⟩
    exact Fintype.card_pos
  have hDm : (0 : ℝ) < D * m := by exact_mod_cast Nat.mul_pos (by omega : 0 < D) (by omega : 0 < m)
  let d := δ / (100 * D * m)
  have hdp : 0 < d := by dsimp [d]; positivity
  have hdsmall : d ≤ 1 / 100 := by
    dsimp [d]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 100 * D * m)).mpr
    have hh : (1 : ℝ) ≤ D * m := by exact_mod_cast Nat.mul_pos (by omega : 0 < D) (by omega : 0 < m)
    nlinarith
  let p : unitInterval := ⟨1-d,by constructor <;> linarith⟩
  have hp : (1 / 2 : ℝ) ≤ p := by change 1/2 ≤ 1-d; linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (p : ℝ) < 1 := by change 1-d < 1; linarith
  have hdel : 1 - (p : ℝ) = d := by dsimp [p]; ring
  let β := d ^ (D*m)
  have hβ : 0 < β := pow_pos hdp _
  have hβ1 : β ≤ 1 := pow_le_one₀ hdp.le (by linarith)
  obtain ⟨N,hN,hNsize⟩ := exists_amplification_size ε δ β hε hδ hβ hβ1 D hD
  refine ⟨N,p,hN,hp0,?_⟩
  intro B hB
  rcases B with ⟨A,r⟩
  let Rhat := canonicalRepresentation (copiesGraph G N)
  let S := Finset.univ.filter (fun v => 0 ≤ ((D-1 : ℕ) : ℝ) ∧ queryCost A Rhat r v ≤ ENNReal.ofReal ((D-1 : ℕ) : ℝ))
  have hS : ε/2 * (N*n : ℕ) ≤ (S.card : ℝ) := hB
  obtain ⟨c,Q,hcert⟩ := cheap_certificates A Rhat r D hD S (fun v hv => (Finset.mem_filter.mp hv).2.2)
  have hbound : (distributionalSuccess (A,r) (deletionLaw G N p)).toReal < δ/2 := by
    by_cases hc : ∀ u ∈ S, ∀ v ∈ S, (copiesGraph G N).Adj u v → c u ≠ c v
    · have hns : ∀ M : ℕ, ε/4 * N ≤ M →
          2 ≤ M ∧ 2*(D:ℝ)*log2 (M:ℝ)^D ≤ M ∧
          ∀ k : ℕ, log2 (M:ℝ)/(2*D) ≤ k → (1-(1-(p:ℝ))^(D*Fintype.card (Sym2 (Fin n))))^k ≤ δ/10 := by
        simpa only [hdel] using hNsize
      have hh := proper_cheap_failure_bound G hn hN A r p hp hp1 Δ D K hΔ hD hdegree hgirth hlarge ε δ hhigh hns S hS c Q hcert hc
      rw [hdel] at hh
      have heq : (D : ℝ) * m * d = δ/100 := by dsimp [d]; field_simp <;> ring
      change (distributionalSuccess (A,r) (deletionLaw G N p)).toReal ≤ D * (m : ℝ) * d + δ/10 at hh
      rw [heq] at hh
      linarith
    · push_neg at hc
      obtain ⟨u,hu,v,hv,huv,hcolors⟩ := hc
      have hh := cheap_pair_failure_bound G A r p D u v (c u) huv (Q u) (Q v)
        (hcert u hu).2.1 (hcert v hv).2.1 (hcert u hu).2.2
        (by simpa only [hcolors] using (hcert v hv).2.2)
      rw [hdel] at hh
      have heq : (2*D : ℝ) * m * d = δ/50 := by dsimp [d]; field_simp <;> ring
      change (distributionalSuccess (A,r) (deletionLaw G N p)).toReal ≤ (2*D : ℝ) * m * d at hh
      rw [heq] at hh
      linarith
  have hfinite : distributionalSuccess (A,r) (deletionLaw G N p) ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfinite]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hbound

end
end GreedyColoringLCA969.LowerBound

open scoped ENNReal BigOperators Classical
open MeasureTheory
namespace GreedyColoringLCA969.LowerBound

theorem deterministicEfficient_mono {n : ℕ} (B : DeterministicLCA .standard) (R : Representation n)
    (q q' ε : ℝ) (hqq' : q ≤ q') (h : DeterministicEfficient B R q ε) :
    DeterministicEfficient B R q' ε := by
  classical
  apply h.trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro v hv
  have hh := (Finset.mem_filter.mp hv).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1.trans hqq',hh.2.trans (ENNReal.ofReal_le_ofReal hqq')⟩


end GreedyColoringLCA969.LowerBound

open GreedyColoringLCA969.LowerBound
theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (Δ D K : ℕ) (hΔ : 1 ≤ Δ) (hD : 1 ≤ D)
    (hdegree : MaxDegreeAtMost G (Δ : ℝ)) (hgirth : GirthAtLeast G (2 * Δ * D + 1 : ℕ))
    (hlarge : 2 * Δ * D < 2 ^ (K-1)) (ε δ q : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hq : 0 < q) (hbudget : 6 * q / δ ≤ ((D-1 : ℕ) : ℝ))
    (hhigh : ∀ c : Fin n → ℕ+, IsProper G c →
      (1 - ε / 4) * (n : ℝ) ≤ (Nat.card {v : Fin n // (K : ℝ) ≤ ((c v).val : ℝ)} : ℝ))
    (A : Algorithm .standard) (hA : UniformlyEfficient A Δ q ε) :
    ∃ (n' : ℕ) (R : Representation n'), MaxDegreeAtMost R.graph (Δ : ℝ) ∧
      successProbability A R ≤ ENNReal.ofReal δ := by
  classical
  obtain ⟨N,p,hN,hp,hdet⟩ := finite_deterministic_amplification G hn Δ D K hΔ hD hdegree hgirth hlarge ε δ hε hδ hδ1 hhigh
  let μ := deletionLaw G N p
  let Rhat : Input := ⟨N*n,canonicalRepresentation (copiesGraph G N)⟩
  have hhat : InSupport μ Rhat := deletion_full_inSupport G N p hp
  have hreduce := (lemma_3_4 .standard μ Rhat hhat q ε hq hε).1 (δ/2) δ (by linarith) (by linarith) hδ1
  have hdet' : ∀ B : DeterministicLCA .standard,
      DeterministicEfficient B Rhat.2 (3*q/(δ/2)) (ε/2) →
      distributionalSuccess B μ < ENNReal.ofReal (δ-δ/2) := by
    intro B hB
    have hqq' : 3*q/(δ/2) ≤ ((D-1 : ℕ) : ℝ) := by
      convert hbudget using 1 <;> ring
    have hh := hdet B (deterministicEfficient_mono B Rhat.2 _ _ _ hqq' hB)
    convert hh using 1 <;> congr 1 <;> ring
  have heff : Efficient A Rhat.2 q ε := hA (N*n) Rhat.2 (copies_maxDegree G _ hdegree)
  obtain ⟨R,hR,hfail⟩ := hreduce hdet' A heff
  exact ⟨R.1,R.2,deletion_support_degree G N p _ hdegree R hR,hfail.le⟩