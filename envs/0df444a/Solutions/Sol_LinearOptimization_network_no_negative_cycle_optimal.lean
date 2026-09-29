-- Prove2me | solution 1 for LinearOptimization.network_no_negative_cycle_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T21:13:10.466565+00:00
-- url     : https://prove2.me/submissions/9a6e698a-25cf-4eff-8f83-524b146f15ae

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ENNReal.BigOperators
import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Theorems.Thm_LinearOptimization_traversalVector_isCirculation_of_isCycle
import Theorems.Thm_LinearOptimization_network_flow_decomposition

/-!
# Negative cycle optimality (Bertsimas & Tsitsiklis, Theorem 7.6, p. 298)

A feasible flow is optimal iff no unsaturated cycle has negative cost.

`→` : pushing a positive amount around an unsaturated negative-cost cycle keeps
feasibility (the traversal vector of a cycle is a circulation) and strictly
lowers the cost.

`←` : for another feasible `f'`, the difference `g = f' − f` is a circulation.
Splitting `g` into its positive and negative parts over a *doubled* arc family
(each arc together with its reverse) turns `g` into a *nonnegative* circulation,
so Lemma 7.1 decomposes it into directed cycles; read back in the original graph
these are unsaturated cycles, hence of nonnegative cost, and `c'g ≥ 0`.
-/

open Matrix
open scoped ENNReal

namespace NegCycle

open LinearOptimization

variable {n m : ℕ} {arcs : Fin m → Fin n × Fin n}

/-! ### The traversal vector of a list with distinct arcs -/

lemma tv_of_true {P : List (Fin m × Bool)} (hnd : (P.map Prod.fst).Nodup) {k : Fin m}
    (h : (k, true) ∈ P) : traversalVector P k = 1 := by
  have h2 : (k, false) ∉ P := by
    intro hc
    have := List.inj_on_of_nodup_map hnd h hc rfl
    simp at this
  simp [traversalVector, h, h2]

lemma tv_of_false {P : List (Fin m × Bool)} (hnd : (P.map Prod.fst).Nodup) {k : Fin m}
    (h : (k, false) ∈ P) : traversalVector P k = -1 := by
  have h2 : (k, true) ∉ P := by
    intro hc
    have := List.inj_on_of_nodup_map hnd h hc rfl
    simp at this
  simp [traversalVector, h, h2]

lemma tv_of_none {P : List (Fin m × Bool)} {k : Fin m}
    (h1 : (k, true) ∉ P) (h2 : (k, false) ∉ P) : traversalVector P k = 0 := by
  simp [traversalVector, h1, h2]

/-! ### The largest amount that can be pushed around a cycle -/

/-- The residual bound `δ(C)` of Eq. (7.12). -/
noncomputable def cycDelta (u : Fin m → ℝ≥0∞) (f : Fin m → ℝ)
    (steps : List (Fin m × Bool)) : ℝ≥0∞ :=
  (steps.map fun st =>
    if st.2 then u st.1 - ENNReal.ofReal (f st.1) else ENNReal.ofReal (f st.1)).foldr min ⊤

lemma foldr_min_le (l : List ℝ≥0∞) {x : ℝ≥0∞} (hx : x ∈ l) : l.foldr min ⊤ ≤ x := by
  induction l with
  | nil => simp at hx
  | cons a rest ih =>
      rcases List.mem_cons.1 hx with h | h
      · subst h; exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih h)

lemma foldr_min_pos (l : List ℝ≥0∞) (h : ∀ x ∈ l, 0 < x) : 0 < l.foldr min ⊤ := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      exact lt_min (h a (List.mem_cons_self ..))
        (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

lemma cycDelta_le {u : Fin m → ℝ≥0∞} {f : Fin m → ℝ} {steps : List (Fin m × Bool)}
    {st : Fin m × Bool} (hst : st ∈ steps) :
    cycDelta u f steps ≤
      (if st.2 then u st.1 - ENNReal.ofReal (f st.1) else ENNReal.ofReal (f st.1)) :=
  foldr_min_le _ (List.mem_map.2 ⟨st, hst, rfl⟩)

lemma cycDelta_pos {u : Fin m → ℝ≥0∞} {f : Fin m → ℝ} {steps : List (Fin m × Bool)}
    (hfwd : ∀ st ∈ steps, st.2 = true → ENNReal.ofReal (f st.1) < u st.1)
    (hbwd : ∀ st ∈ steps, st.2 = false → 0 < f st.1) :
    0 < cycDelta u f steps := by
  refine foldr_min_pos _ (fun x hx => ?_)
  obtain ⟨st, hst, rfl⟩ := List.mem_map.1 hx
  by_cases hd : st.2
  · simp only [hd, if_true]
    exact tsub_pos_of_lt (hfwd st hst hd)
  · simp only [Bool.not_eq_true] at hd
    simp only [hd, Bool.false_eq_true, if_false]
    exact ENNReal.ofReal_pos.2 (hbwd st hst hd)

/-- Pushing `ε` units of flow around an unsaturated cycle keeps feasibility. -/
lemma push_cycle {bsupply : Fin n → ℝ} {u : Fin m → ℝ≥0∞} {cost : Fin m → ℝ} {f : Fin m → ℝ}
    (hf : IsFeasibleFlow arcs bsupply u f) {v : Fin n} {C : List (Fin m × Bool)}
    (hcyc : IsCycle arcs v C)
    (hfwd : ∀ st ∈ C, st.2 = true → ENNReal.ofReal (f st.1) < u st.1)
    (hbwd : ∀ st ∈ C, st.2 = false → 0 < f st.1)
    {ε : ℝ} (hε : 0 < ε) (hεδ : ENNReal.ofReal ε ≤ cycDelta u f C) :
    IsFeasibleFlow arcs bsupply u (fun k => f k + ε * traversalVector C k) := by
  have hnd : (C.map Prod.fst).Nodup := hcyc.2.2.2
  have hcirc : IsCirculation arcs (traversalVector C) :=
    LinearOptimization.traversalVector_isCirculation_of_isCycle arcs hcyc
  constructor
  · funext i
    have h1 : (incidenceMatrix arcs).mulVec (fun k => f k + ε * traversalVector C k) i
        = (incidenceMatrix arcs).mulVec f i
          + ε * (incidenceMatrix arcs).mulVec (traversalVector C) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [h1, congrFun hcirc i, congrFun hf.1 i]
    simp
  · intro k
    by_cases h1 : (k, true) ∈ C
    · have htv : traversalVector C k = 1 := tv_of_true hnd h1
      have hεk : ENNReal.ofReal ε ≤ u k - ENNReal.ofReal (f k) := by
        refine le_trans hεδ ?_
        simpa using cycDelta_le (u := u) (f := f) h1
      refine ⟨by simp only [htv, mul_one]; linarith [(hf.2 k).1, hε.le], ?_⟩
      simp only [htv, mul_one]
      rw [ENNReal.ofReal_add (hf.2 k).1 hε.le]
      calc ENNReal.ofReal (f k) + ENNReal.ofReal ε
          ≤ ENNReal.ofReal (f k) + (u k - ENNReal.ofReal (f k)) := by gcongr
        _ = u k := add_tsub_cancel_of_le (hf.2 k).2
    · by_cases h2 : (k, false) ∈ C
      · have htv : traversalVector C k = -1 := tv_of_false hnd h2
        have hεk : ENNReal.ofReal ε ≤ ENNReal.ofReal (f k) := by
          refine le_trans hεδ ?_
          simpa using cycDelta_le (u := u) (f := f) h2
        have hle : ε ≤ f k := (ENNReal.ofReal_le_ofReal_iff (hf.2 k).1).1 hεk
        refine ⟨by simp only [htv]; linarith, ?_⟩
        simp only [htv]
        exact le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (hf.2 k).2
      · have htv : traversalVector C k = 0 := tv_of_none h1 h2
        simpa [htv] using hf.2 k

/-! ### The doubled arc family -/

/-- Each arc together with its reverse. -/
def dbl (arcs : Fin m → Fin n × Fin n) : Fin (m + m) → Fin n × Fin n :=
  Fin.addCases (fun k : Fin m => arcs k) (fun k : Fin m => ((arcs k).2, (arcs k).1))

/-- Positive part on the forward copy, negative part on the reverse copy. -/
noncomputable def split (g : Fin m → ℝ) : Fin (m + m) → ℝ :=
  Fin.addCases (fun k : Fin m => max (g k) 0) (fun k : Fin m => max (-(g k)) 0)

/-- Read a doubled arc back as a signed step of the original graph. -/
def back (m : ℕ) : Fin (m + m) → Fin m × Bool :=
  Fin.addCases (fun k : Fin m => (k, true)) (fun k : Fin m => (k, false))

lemma dbl_left (k : Fin m) : dbl arcs (Fin.castAdd m k) = arcs k := Fin.addCases_left k
lemma dbl_right (k : Fin m) : dbl arcs (Fin.natAdd m k) = ((arcs k).2, (arcs k).1) :=
  Fin.addCases_right k
lemma split_left (g : Fin m → ℝ) (k : Fin m) : split g (Fin.castAdd m k) = max (g k) 0 :=
  Fin.addCases_left k
lemma split_right (g : Fin m → ℝ) (k : Fin m) : split g (Fin.natAdd m k) = max (-(g k)) 0 :=
  Fin.addCases_right k
lemma back_left (k : Fin m) : back m (Fin.castAdd m k) = (k, true) := Fin.addCases_left k
lemma back_right (k : Fin m) : back m (Fin.natAdd m k) = (k, false) := Fin.addCases_right k

lemma dbl_noSelfLoops (hloop : HasNoSelfLoops arcs) : HasNoSelfLoops (dbl arcs) := by
  intro e
  refine Fin.addCases (motive := fun e => (dbl arcs e).1 ≠ (dbl arcs e).2) ?_ ?_ e
  · intro k; rw [dbl_left]; exact hloop k
  · intro k; rw [dbl_right]; exact (hloop k).symm

lemma incid_dbl_left (i : Fin n) (k : Fin m) :
    incidenceMatrix (dbl arcs) i (Fin.castAdd m k) = incidenceMatrix arcs i k := by
  simp [incidenceMatrix, dbl_left]

lemma incid_dbl_right (i : Fin n) (k : Fin m) :
    incidenceMatrix (dbl arcs) i (Fin.natAdd m k) = -incidenceMatrix arcs i k := by
  simp only [incidenceMatrix, Matrix.of_apply, dbl_right]
  ring

lemma split_sub (g : Fin m → ℝ) (k : Fin m) :
    split g (Fin.castAdd m k) - split g (Fin.natAdd m k) = g k := by
  rw [split_left, split_right]
  rcases le_total 0 (g k) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma split_nonneg (g : Fin m → ℝ) : 0 ≤ split g := by
  intro e
  simp only [Pi.zero_apply]
  refine Fin.addCases (motive := fun e => 0 ≤ split g e) ?_ ?_ e
  · intro k; rw [split_left]; exact le_max_right _ _
  · intro k; rw [split_right]; exact le_max_right _ _

lemma split_circulation {g : Fin m → ℝ} (hg : IsCirculation arcs g) :
    IsCirculation (dbl arcs) (split g) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  rw [Fin.sum_univ_add]
  have : ∀ k : Fin m,
      incidenceMatrix (dbl arcs) i (Fin.castAdd m k) * split g (Fin.castAdd m k)
        + incidenceMatrix (dbl arcs) i (Fin.natAdd m k) * split g (Fin.natAdd m k)
      = incidenceMatrix arcs i k * g k := by
    intro k
    rw [incid_dbl_left, incid_dbl_right, ← split_sub g k]
    ring
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun k _ => this k)]
  exact congrFun hg i

/-! ### Reading doubled arcs back -/

lemma back_injective : Function.Injective (back m) := by
  intro e e' h
  refine Fin.addCases (motive := fun e => back m e = back m e' → e = e') ?_ ?_ e h
  · intro j hj
    refine Fin.addCases (motive := fun e' => back m (Fin.castAdd m j) = back m e' →
      Fin.castAdd m j = e') ?_ ?_ e' hj
    · intro j' hj'
      rw [back_left, back_left] at hj'
      have : j = j' := by simpa using hj'
      rw [this]
    · intro j' hj'
      rw [back_left, back_right] at hj'
      simp at hj'
  · intro j hj
    refine Fin.addCases (motive := fun e' => back m (Fin.natAdd m j) = back m e' →
      Fin.natAdd m j = e') ?_ ?_ e' hj
    · intro j' hj'
      rw [back_right, back_left] at hj'
      simp at hj'
    · intro j' hj'
      rw [back_right, back_right] at hj'
      have : j = j' := by simpa using hj'
      rw [this]

lemma back_true_eq (e : Fin (m + m)) (h : (back m e).2 = true) :
    e = Fin.castAdd m (back m e).1 := by
  refine Fin.addCases (motive := fun e => (back m e).2 = true → e = Fin.castAdd m (back m e).1)
    ?_ ?_ e h
  · intro j _; rw [back_left]
  · intro j hj; rw [back_right] at hj; simp at hj

lemma back_false_eq (e : Fin (m + m)) (h : (back m e).2 = false) :
    e = Fin.natAdd m (back m e).1 := by
  refine Fin.addCases (motive := fun e => (back m e).2 = false → e = Fin.natAdd m (back m e).1)
    ?_ ?_ e h
  · intro j hj; rw [back_left] at hj; simp at hj
  · intro j _; rw [back_right]

lemma stepStart_back (arcs : Fin m → Fin n × Fin n) (e : Fin (m + m)) :
    stepStart arcs (back m e) = stepStart (dbl arcs) (e, true) := by
  refine Fin.addCases (motive := fun e =>
    stepStart arcs (back m e) = stepStart (dbl arcs) (e, true)) ?_ ?_ e
  · intro j; simp only [back_left, stepStart, dbl_left, if_true]
  · intro j
    simp only [back_right, stepStart, dbl_right, Bool.false_eq_true, if_false, if_true]

lemma stepEnd_back (arcs : Fin m → Fin n × Fin n) (e : Fin (m + m)) :
    stepEnd arcs (back m e) = stepEnd (dbl arcs) (e, true) := by
  refine Fin.addCases (motive := fun e =>
    stepEnd arcs (back m e) = stepEnd (dbl arcs) (e, true)) ?_ ?_ e
  · intro j; simp only [back_left, stepEnd, dbl_left, if_true]
  · intro j
    simp only [back_right, stepEnd, dbl_right, Bool.false_eq_true, if_false, if_true]

lemma walk_map {L : List (Fin (m + m) × Bool)} (hall : ∀ st ∈ L, st.2 = true) {a b : Fin n}
    (h : IsWalkFrom (dbl arcs) a b L) :
    IsWalkFrom arcs a b (L.map (fun st => back m st.1)) := by
  induction L generalizing a with
  | nil => exact h
  | cons st rest ih =>
      obtain ⟨h1, h2⟩ := h
      have hst : (st.1, true) = st :=
        Prod.ext_iff.2 ⟨rfl, (hall st (List.mem_cons_self ..)).symm⟩
      refine ⟨?_, ?_⟩
      · rw [stepStart_back, hst]; exact h1
      · have : stepEnd arcs (back m st.1) = stepEnd (dbl arcs) st := by
          rw [stepEnd_back, hst]
        rw [this]
        exact ih (fun x hx => hall x (List.mem_cons_of_mem _ hx)) h2

lemma walkNodes_map {L : List (Fin (m + m) × Bool)} (hall : ∀ st ∈ L, st.2 = true) (a : Fin n) :
    walkNodes arcs a (L.map (fun st => back m st.1)) = walkNodes (dbl arcs) a L := by
  simp only [walkNodes, List.map_map, List.cons.injEq, true_and]
  refine List.map_congr_left (fun st hst => ?_)
  have hst2 : (st.1, true) = st := Prod.ext_iff.2 ⟨rfl, (hall st hst).symm⟩
  simp only [Function.comp_apply]
  rw [stepEnd_back, hst2]

lemma mem_map_back_true {L : List (Fin (m + m) × Bool)} (hall : ∀ st ∈ L, st.2 = true)
    (j : Fin m) :
    ((j, true) ∈ L.map (fun st => back m st.1)) ↔ (Fin.castAdd m j, true) ∈ L := by
  constructor
  · intro h
    obtain ⟨st, hst, hb⟩ := List.mem_map.1 h
    have h1 : (back m st.1).1 = j := by rw [hb]
    have h2 : (back m st.1).2 = true := by rw [hb]
    have := back_true_eq st.1 h2
    rw [h1] at this
    have hst2 : (st.1, true) = st := Prod.ext_iff.2 ⟨rfl, (hall st hst).symm⟩
    rw [← this, hst2]; exact hst
  · intro h
    exact List.mem_map.2 ⟨(Fin.castAdd m j, true), h, by rw [back_left]⟩

lemma mem_map_back_false {L : List (Fin (m + m) × Bool)} (hall : ∀ st ∈ L, st.2 = true)
    (j : Fin m) :
    ((j, false) ∈ L.map (fun st => back m st.1)) ↔ (Fin.natAdd m j, true) ∈ L := by
  constructor
  · intro h
    obtain ⟨st, hst, hb⟩ := List.mem_map.1 h
    have h1 : (back m st.1).1 = j := by rw [hb]
    have h2 : (back m st.1).2 = false := by rw [hb]
    have := back_false_eq st.1 h2
    rw [h1] at this
    have hst2 : (st.1, true) = st := Prod.ext_iff.2 ⟨rfl, (hall st hst).symm⟩
    rw [← this, hst2]; exact hst
  · intro h
    exact List.mem_map.2 ⟨(Fin.natAdd m j, true), h, by rw [back_right]⟩

lemma tv_map {L : List (Fin (m + m) × Bool)} (hall : ∀ st ∈ L, st.2 = true) (j : Fin m) :
    traversalVector (L.map (fun st => back m st.1)) j
      = traversalVector L (Fin.castAdd m j) - traversalVector L (Fin.natAdd m j) := by
  have hfalse : ∀ e : Fin (m + m), (e, false) ∉ L := by
    intro e he
    simpa using hall _ he
  simp only [traversalVector, mem_map_back_true hall, mem_map_back_false hall, hfalse,
    if_false, sub_zero]

end NegCycle

open LinearOptimization NegCycle
open Matrix
open scoped ENNReal

theorem solution {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (hloop : HasNoSelfLoops arcs)
    (bsupply : Fin n → ℝ) (u : Fin m → ℝ≥0∞) (cost : Fin m → ℝ)
    (f : Fin m → ℝ) (hf : IsFeasibleFlow arcs bsupply u f) :
    (∀ f', IsFeasibleFlow arcs bsupply u f' → cost ⬝ᵥ f ≤ cost ⬝ᵥ f') ↔
      ¬∃ (v : Fin n) (steps : List (Fin m × Bool)),
        IsCycle arcs v steps ∧
        (∀ st ∈ steps, st.2 = true → ENNReal.ofReal (f st.1) < u st.1) ∧
        (∀ st ∈ steps, st.2 = false → 0 < f st.1) ∧
        cost ⬝ᵥ traversalVector steps < 0 := by
  classical
  constructor
  · -- optimal ⟹ no unsaturated negative cycle
    rintro hopt ⟨v, C, hcyc, hfwd, hbwd, hneg⟩
    obtain ⟨ε, hεpos, hεle⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ cycDelta u f C := by
      have hδ : 0 < cycDelta u f C := cycDelta_pos hfwd hbwd
      by_cases htop : cycDelta u f C = ⊤
      · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
      · exact ⟨(cycDelta u f C).toReal, ENNReal.toReal_pos hδ.ne' htop,
          by rw [ENNReal.ofReal_toReal htop]⟩
    have hfeas := push_cycle (cost := cost) hf hcyc hfwd hbwd hεpos hεle
    have hcost : cost ⬝ᵥ (fun k => f k + ε * traversalVector C k)
        = cost ⬝ᵥ f + ε * (cost ⬝ᵥ traversalVector C) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have := hopt _ hfeas
    rw [hcost] at this
    nlinarith
  · -- no unsaturated negative cycle ⟹ optimal
    intro hno f' hf'
    by_contra hlt
    push_neg at hlt
    set g : Fin m → ℝ := fun k => f' k - f k with hgdef
    have hgcirc : IsCirculation arcs g := by
      funext i
      have : (incidenceMatrix arcs).mulVec g i
          = (incidenceMatrix arcs).mulVec f' i - (incidenceMatrix arcs).mulVec f i := by
        simp only [Matrix.mulVec, dotProduct, hgdef, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [this, congrFun hf'.1 i, congrFun hf.1 i]
      simp
    -- the cost of `g` is negative
    have hcostg : cost ⬝ᵥ g < 0 := by
      have : cost ⬝ᵥ g = cost ⬝ᵥ f' - cost ⬝ᵥ f := by
        simp only [dotProduct, hgdef, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [this]; linarith
    have hg2nn : 0 ≤ split g := split_nonneg g
    have hg2circ : IsCirculation (dbl arcs) (split g) := split_circulation hgcirc
    have hg2ne : split g ≠ 0 := by
      intro h
      apply absurd hcostg
      have : g = 0 := by
        funext k
        rw [← split_sub g k, h]
        simp
      rw [this]
      simp
    obtain ⟨⟨k, cyc, a, hcycles, hfwds, has, hsum⟩, -⟩ :=
      LinearOptimization.network_flow_decomposition (dbl arcs) (dbl_noSelfLoops hloop)
        (split g) hg2nn hg2circ hg2ne
    -- every arc used by a cycle carries positive `split g`
    have harcpos : ∀ (i : Fin k) (e : Fin (m + m)), (e, true) ∈ cyc i → 0 < split g e := by
      intro i e he
      have hnd : ∀ j, ((cyc j).map Prod.fst).Nodup := fun j => (hcycles j).choose_spec.2.2.2
      have h1 : traversalVector (cyc i) e = 1 := tv_of_true (hnd i) he
      have hterm : ∀ j, 0 ≤ a j * traversalVector (cyc j) e := by
        intro j
        have hfalse : (e, false) ∉ cyc j := by
          intro hc
          simpa using hfwds j _ hc
        by_cases hc : (e, true) ∈ cyc j
        · rw [tv_of_true (hnd j) hc]; linarith [has j]
        · rw [tv_of_none hc hfalse]; simp
      have := congrFun hsum e
      rw [this]
      calc (0 : ℝ) < a i * traversalVector (cyc i) e := by rw [h1]; simpa using has i
        _ ≤ ∑ j, a j * traversalVector (cyc j) e :=
            Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
    have hgval : ∀ j, g j = f' j - f j := fun j => congrFun hgdef j
    have hsplitpos_left : ∀ j : Fin m, 0 < split g (Fin.castAdd m j) → 0 < g j := by
      intro j h
      rw [split_left] at h
      exact (lt_max_iff.1 h).resolve_right (lt_irrefl 0)
    have hsplitpos_right : ∀ j : Fin m, 0 < split g (Fin.natAdd m j) → g j < 0 := by
      intro j h
      rw [split_right] at h
      have := (lt_max_iff.1 h).resolve_right (lt_irrefl 0)
      linarith
    have hnd2 : ∀ i, ((cyc i).map Prod.fst).Nodup := by
      intro i; obtain ⟨v, hv⟩ := hcycles i; exact hv.2.2.2
    have hposmem : ∀ (i : Fin k) (st : Fin (m + m) × Bool), st ∈ cyc i → 0 < split g st.1 := by
      intro i st hst
      have hmem : (st.1, true) ∈ cyc i := by
        have hd := hfwds i st hst
        rwa [show (st.1, true) = st from Prod.ext_iff.2 ⟨rfl, hd.symm⟩]
      exact harcpos i st.1 hmem
    -- the mapped step lists have pairwise distinct arcs
    have hmpnd : ∀ i, (((cyc i).map (fun st => back m st.1)).map Prod.fst).Nodup := by
      intro i
      rw [List.map_map]
      refine List.Nodup.map_on ?_ ((hnd2 i).of_map)
      intro st hst st' hst' heq
      simp only [Function.comp_apply] at heq
      by_cases hd : (back m st.1).2 = (back m st'.1).2
      · have hb : back m st.1 = back m st'.1 := Prod.ext_iff.2 ⟨heq, hd⟩
        exact List.inj_on_of_nodup_map (hnd2 i) hst hst' (back_injective hb)
      · exfalso
        have hpos := hposmem i st hst
        have hpos' := hposmem i st' hst'
        rcases Bool.eq_false_or_eq_true (back m st.1).2 with h1 | h1
        · have h2 : (back m st'.1).2 = false := by
            rcases Bool.eq_false_or_eq_true (back m st'.1).2 with h | h
            · exact absurd (h1.trans h.symm) hd
            · exact h
          have e1 : st.1 = Fin.castAdd m (back m st.1).1 := back_true_eq _ h1
          have e2 : st'.1 = Fin.natAdd m (back m st'.1).1 := back_false_eq _ h2
          rw [e1] at hpos
          rw [e2, ← heq] at hpos'
          have := hsplitpos_left _ hpos
          have := hsplitpos_right _ hpos'
          linarith
        · have h2 : (back m st'.1).2 = true := by
            rcases Bool.eq_false_or_eq_true (back m st'.1).2 with h | h
            · exact h
            · exact absurd (h1.trans h.symm) hd
          have e1 : st.1 = Fin.natAdd m (back m st.1).1 := back_false_eq _ h1
          have e2 : st'.1 = Fin.castAdd m (back m st'.1).1 := back_true_eq _ h2
          rw [e1] at hpos
          rw [e2, ← heq] at hpos'
          have := hsplitpos_right _ hpos
          have := hsplitpos_left _ hpos'
          linarith
    -- each mapped step list is a cycle of the original graph
    have hcycmp : ∀ i, ∃ v, IsCycle arcs v ((cyc i).map (fun st => back m st.1)) := by
      intro i
      obtain ⟨v, hv⟩ := hcycles i
      exact ⟨v, by simpa using hv.1, walk_map (hfwds i) hv.2.1,
        by rw [walkNodes_map (hfwds i)]; exact hv.2.2.1, hmpnd i⟩
    -- and it is unsaturated
    have hunsat : ∀ i,
        (∀ st ∈ (cyc i).map (fun st => back m st.1), st.2 = true →
          ENNReal.ofReal (f st.1) < u st.1) ∧
        (∀ st ∈ (cyc i).map (fun st => back m st.1), st.2 = false → 0 < f st.1) := by
      intro i
      constructor
      · intro st hst hd
        obtain ⟨w, hw, hb⟩ := List.mem_map.1 hst
        have hpos : 0 < split g w.1 := hposmem i w hw
        have h2 : (back m w.1).2 = true := by rw [hb]; exact hd
        have hcast : w.1 = Fin.castAdd m (back m w.1).1 := back_true_eq _ h2
        rw [hcast] at hpos
        have hg : 0 < g (back m w.1).1 := hsplitpos_left _ hpos
        have hst1 : st.1 = (back m w.1).1 := by rw [← hb]
        rw [hst1]
        have h3 : f (back m w.1).1 < f' (back m w.1).1 := by
          rw [hgval] at hg; linarith
        calc ENNReal.ofReal (f (back m w.1).1) < ENNReal.ofReal (f' (back m w.1).1) := by
              refine (ENNReal.ofReal_lt_ofReal_iff ?_).2 h3
              linarith [(hf.2 (back m w.1).1).1]
          _ ≤ u (back m w.1).1 := (hf'.2 (back m w.1).1).2
      · intro st hst hd
        obtain ⟨w, hw, hb⟩ := List.mem_map.1 hst
        have hpos : 0 < split g w.1 := hposmem i w hw
        have h2 : (back m w.1).2 = false := by rw [hb]; exact hd
        have hnat : w.1 = Fin.natAdd m (back m w.1).1 := back_false_eq _ h2
        rw [hnat] at hpos
        have hg : g (back m w.1).1 < 0 := hsplitpos_right _ hpos
        have hst1 : st.1 = (back m w.1).1 := by rw [← hb]
        rw [hst1]
        rw [hgval] at hg
        linarith [(hf'.2 (back m w.1).1).1]
    -- hence every mapped cycle has nonnegative cost
    have hcostnn : ∀ i, 0 ≤ cost ⬝ᵥ traversalVector ((cyc i).map (fun st => back m st.1)) := by
      intro i
      by_contra hneg
      push_neg at hneg
      obtain ⟨v, hv⟩ := hcycmp i
      exact hno ⟨v, _, hv, (hunsat i).1, (hunsat i).2, hneg⟩
    -- and `g` is the corresponding combination
    have hgj : ∀ j, g j
        = ∑ i, a i * traversalVector ((cyc i).map (fun st => back m st.1)) j := by
      intro j
      rw [← split_sub g j, congrFun hsum (Fin.castAdd m j), congrFun hsum (Fin.natAdd m j),
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [tv_map (hfwds i) j]
      ring
    have hfinal : (0 : ℝ) ≤ cost ⬝ᵥ g := by
      have hexp : cost ⬝ᵥ g
          = ∑ i, a i * (cost ⬝ᵥ traversalVector ((cyc i).map (fun st => back m st.1))) := by
        simp only [dotProduct]
        calc ∑ j, cost j * g j
            = ∑ j, ∑ i, a i * (cost j *
                traversalVector ((cyc i).map (fun st => back m st.1)) j) := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [hgj j, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun i _ => by ring)
          _ = ∑ i, ∑ j, a i * (cost j *
                traversalVector ((cyc i).map (fun st => back m st.1)) j) := Finset.sum_comm
          _ = ∑ i, a i * ∑ j, cost j *
                traversalVector ((cyc i).map (fun st => back m st.1)) j :=
              Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm)
      rw [hexp]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (has i).le (hcostnn i))
    linarith
