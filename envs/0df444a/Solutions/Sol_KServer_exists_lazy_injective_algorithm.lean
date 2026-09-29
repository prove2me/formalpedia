-- Prove2me | solution 1 for KServer.exists_lazy_injective_algorithm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T08:39:58.681817+00:00
-- url     : https://prove2.me/submissions/0e13aa21-2f79-45ee-8aaa-96ebc5a99e7b

import Mathlib
import Definitions.Def_KServer_model

open KServer

/-- Splitting the cost of an online algorithm at the last request. -/
private theorem cost_concat {k : ℕ} {M : Type*} [MetricSpace M]
    (X : OnlineAlgorithm k M) (l : List M) (r : M) :
    X.cost (l ++ [r]) = X.cost l + moveCost (X.conf l) (X.conf (l ++ [r])) := by
  unfold OnlineAlgorithm.cost
  have hlen : (l ++ [r]).length = l.length + 1 := by simp
  rw [hlen, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [List.take_append_of_le_length (le_refl _), List.take_length,
      List.take_of_length_le (by simp)]

/-- The minimum-cost matching between two configurations. -/
private noncomputable def matchCost {k : ℕ} {M : Type*} [MetricSpace M]
    (b a : Config k M) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin k))).inf' ⟨1, Finset.mem_univ 1⟩
    fun π => ∑ i, dist (b i) (a (π i))

private theorem matchCost_le {k : ℕ} {M : Type*} [MetricSpace M]
    (b a : Config k M) (π : Equiv.Perm (Fin k)) :
    matchCost b a ≤ ∑ i, dist (b i) (a (π i)) :=
  Finset.inf'_le _ (Finset.mem_univ π)

private theorem matchCost_nonneg {k : ℕ} {M : Type*} [MetricSpace M]
    (b a : Config k M) : 0 ≤ matchCost b a :=
  Finset.le_inf' _ _ fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg

private theorem exists_matchCost_eq {k : ℕ} {M : Type*} [MetricSpace M]
    (b a : Config k M) :
    ∃ π : Equiv.Perm (Fin k), matchCost b a = ∑ i, dist (b i) (a (π i)) := by
  obtain ⟨π, -, hπ⟩ := Finset.exists_mem_eq_inf'
    (⟨1, Finset.mem_univ 1⟩ : (Finset.univ : Finset (Equiv.Perm (Fin k))).Nonempty)
    (fun π => ∑ i, dist (b i) (a (π i)))
  exact ⟨π, hπ⟩

/-- The matching cost is 1-Lipschitz in its second argument. -/
private theorem matchCost_lipschitz {k : ℕ} {M : Type*} [MetricSpace M]
    (b a a' : Config k M) : matchCost b a' ≤ matchCost b a + moveCost a a' := by
  obtain ⟨π, hπ⟩ := exists_matchCost_eq b a
  have h1 : matchCost b a' ≤ ∑ i, dist (b i) (a' (π i)) := matchCost_le b a' π
  have h2 : ∀ i, dist (b i) (a' (π i)) ≤ dist (b i) (a (π i)) + dist (a (π i)) (a' (π i)) :=
    fun i => dist_triangle _ _ _
  have h3 : (∑ i, dist (a (π i)) (a' (π i))) = moveCost a a' := by
    unfold moveCost
    exact Fintype.sum_equiv π _ _ fun i => rfl
  calc matchCost b a' ≤ ∑ i, dist (b i) (a' (π i)) := h1
    _ ≤ (∑ i, dist (b i) (a (π i))) + ∑ i, dist (a (π i)) (a' (π i)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => h2 i
    _ = matchCost b a + moveCost a a' := by rw [← hπ, h3]

theorem solution (k : ℕ) (M : Type*) [MetricSpace M]
    (A : OnlineAlgorithm k M) (hinj : Function.Injective (A.conf [])) :
    ∃ B : OnlineAlgorithm k M,
      B.conf [] = A.conf [] ∧
      (∀ σ : List M, B.cost σ ≤ A.cost σ) ∧
      (∀ l : List M, Function.Injective (B.conf l)) ∧
      (∀ (l : List M) (r : M), (∃ i, B.conf l i = r) → B.conf (l ++ [r]) = B.conf l) ∧
      (∀ (l : List M) (r : M), ∃ i : Fin k, B.conf (l ++ [r]) = Function.update (B.conf l) i r) := by
  classical
  -- `idx l r` is a server that `A` places on the request `r` after the list `l`.
  set idx : List M → M → Fin k := fun l r => (A.serves l r).choose with hidxdef
  have hidx : ∀ (l : List M) (r : M), A.conf (l ++ [r]) (idx l r) = r :=
    fun l r => (A.serves l r).choose_spec
  -- the step: stay if covered, otherwise move the server matched (by a minimum-cost
  -- matching against A's next configuration) to A's server at the request
  set mover : List M → Config k M → M → Fin k := fun l b r =>
    (exists_matchCost_eq b (A.conf (l ++ [r]))).choose.symm (idx l r) with hmoverdef
  set bstep : List M → Config k M → M → Config k M := fun l b r =>
    if h : ∃ i, b i = r then b else Function.update b (mover l b r) r with hstepdef
  set bconf : List M → Config k M := fun l =>
    List.reverseRecOn l (A.conf []) (fun l r prev => bstep l prev r) with hbdef
  have hb_nil : bconf [] = A.conf [] := by simp [hbdef]
  have hb_concat : ∀ (l : List M) (r : M),
      bconf (l ++ [r]) = bstep l (bconf l) r := by
    intro l r; simp [hbdef]
  -- covered/uncovered case shapes
  have hb_covered : ∀ (l : List M) (r : M), (∃ i, bconf l i = r) →
      bconf (l ++ [r]) = bconf l := by
    intro l r h
    rw [hb_concat l r, hstepdef]
    simp only []
    rw [dif_pos h]
  have hb_uncovered : ∀ (l : List M) (r : M), ¬(∃ i, bconf l i = r) →
      bconf (l ++ [r]) = Function.update (bconf l) (mover l (bconf l) r) r := by
    intro l r h
    rw [hb_concat l r, hstepdef]
    simp only []
    rw [dif_neg h]
  -- injectivity is maintained
  have hinjall : ∀ l : List M, Function.Injective (bconf l) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => rw [hb_nil]; exact hinj
    | append_singleton l r ih =>
      by_cases h : ∃ i, bconf l i = r
      · rw [hb_covered l r h]; exact ih
      · rw [hb_uncovered l r h]
        intro x y hxy
        by_cases hx : x = mover l (bconf l) r <;> by_cases hy : y = mover l (bconf l) r
        · rw [hx, hy]
        · exfalso
          rw [hx, Function.update_self, Function.update_of_ne hy] at hxy
          exact h ⟨y, hxy.symm⟩
        · exfalso
          rw [hy, Function.update_self, Function.update_of_ne hx] at hxy
          exact h ⟨x, hxy⟩
        · rw [Function.update_of_ne hx, Function.update_of_ne hy] at hxy
          exact ih hxy
  -- serving
  have hserves : ∀ (l : List M) (r : M), ∃ i, bconf (l ++ [r]) i = r := by
    intro l r
    by_cases h : ∃ i, bconf l i = r
    · obtain ⟨i, hi⟩ := h
      rw [hb_covered l r ⟨i, hi⟩]
      exact ⟨i, hi⟩
    · rw [hb_uncovered l r h]
      exact ⟨mover l (bconf l) r, Function.update_self _ _ _⟩
  -- the potential argument
  have main : ∀ l : List M,
      (∑ j ∈ Finset.range l.length,
          moveCost (bconf (l.take j)) (bconf (l.take (j + 1))))
        + matchCost (bconf l) (A.conf l) ≤ A.cost l := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      have h0 : matchCost (bconf []) (A.conf []) ≤ 0 := by
        have h1 := matchCost_le (bconf []) (A.conf []) 1
        have h2 : (∑ i, dist (bconf [] i) (A.conf [] ((1 : Equiv.Perm (Fin k)) i))) = 0 := by
          rw [hb_nil]
          simp
        rw [h2] at h1
        exact h1
      simpa [OnlineAlgorithm.cost] using h0
    | append_singleton l r ih =>
      set a : Config k M := A.conf l with hadef
      set a' : Config k M := A.conf (l ++ [r]) with ha'def
      set b : Config k M := bconf l with hbdefl
      -- B's cost splits off the last step
      have hsplit : (∑ i ∈ Finset.range (l ++ [r]).length,
            moveCost (bconf ((l ++ [r]).take i)) (bconf ((l ++ [r]).take (i + 1))))
          = (∑ i ∈ Finset.range l.length,
            moveCost (bconf (l.take i)) (bconf (l.take (i + 1))))
            + moveCost b (bconf (l ++ [r])) := by
        have hlen : (l ++ [r]).length = l.length + 1 := by simp
        rw [hlen, Finset.sum_range_succ]
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro i hi
          simp only [Finset.mem_range] at hi
          rw [List.take_append_of_le_length (by omega),
            List.take_append_of_le_length (by omega)]
        · rw [List.take_append_of_le_length (le_refl _), List.take_length,
            List.take_of_length_le (by simp)]
      have hkey : moveCost b (bconf (l ++ [r])) + matchCost (bconf (l ++ [r])) a'
          ≤ matchCost b a + moveCost a a' := by
        by_cases h : ∃ i, b i = r
        · rw [hb_covered l r h, ← hbdefl, moveCost, ]
          have hmc0 : (∑ i, dist (b i) (b i)) = 0 := by simp
          rw [show (∑ i, dist (b i) (b i)) = 0 from hmc0]
          have := matchCost_lipschitz b a a'
          linarith
        · rw [hb_uncovered l r h, ← hbdefl]
          set π : Equiv.Perm (Fin k) := (exists_matchCost_eq b a').choose with hπdef
          have hπ : matchCost b a' = ∑ i, dist (b i) (a' (π i)) :=
            (exists_matchCost_eq b a').choose_spec
          set i₀ : Fin k := π.symm (idx l r) with hi₀def
          have hmoverval : mover l b r = i₀ := by rw [hmoverdef]
          have hπi₀ : a' (π i₀) = r := by
            rw [hi₀def, Equiv.apply_symm_apply]
            exact hidx l r
          -- the move costs exactly the matched edge at `i₀`
          have hmove : moveCost b (Function.update b (mover l b r) r)
              = dist (b i₀) r := by
            rw [hmoverval]
            unfold moveCost
            rw [Finset.sum_eq_single i₀
              (fun i _ hij => by rw [Function.update_of_ne hij, dist_self])
              (by intro hn; exact absurd (Finset.mem_univ i₀) hn)]
            rw [Function.update_self]
          -- after the move, the same matching drops the `i₀` edge
          have hafter : matchCost (Function.update b (mover l b r) r) a'
              ≤ matchCost b a' - dist (b i₀) r := by
            have h1 : matchCost (Function.update b (mover l b r) r) a'
                ≤ ∑ i, dist (Function.update b (mover l b r) r i) (a' (π i)) :=
              matchCost_le _ _ π
            have h2 : (∑ i, dist (Function.update b (mover l b r) r i) (a' (π i)))
                = ∑ i ∈ Finset.univ.erase i₀, dist (b i) (a' (π i)) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hmoverval,
                Function.update_self, hπi₀, dist_self, zero_add]
              exact Finset.sum_congr rfl fun i hi => by
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
            have h3 : (∑ i ∈ Finset.univ.erase i₀, dist (b i) (a' (π i)))
                = (∑ i, dist (b i) (a' (π i))) - dist (b i₀) (a' (π i₀)) := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
              ring
            rw [h2, h3, hπi₀] at h1
            rw [← hπ] at h1
            exact h1
          have hlip := matchCost_lipschitz b a a'
          rw [hmove]
          linarith
      rw [hsplit, cost_concat A l r, ← hadef, ← ha'def]
      linarith
  -- assemble the algorithm
  refine ⟨⟨bconf, hserves⟩, hb_nil, ?_, hinjall, hb_covered, ?_⟩
  · intro σ
    have h := main σ
    have hΦ : 0 ≤ matchCost (bconf σ) (A.conf σ) := matchCost_nonneg _ _
    have hcost : (⟨bconf, hserves⟩ : OnlineAlgorithm k M).cost σ
        = ∑ j ∈ Finset.range σ.length,
            moveCost (bconf (σ.take j)) (bconf (σ.take (j + 1))) := rfl
    linarith
  · intro l r
    by_cases h : ∃ i, bconf l i = r
    · obtain ⟨i, hi⟩ := h
      refine ⟨i, ?_⟩
      show bconf (l ++ [r]) = Function.update (bconf l) i r
      rw [hb_covered l r ⟨i, hi⟩]
      funext x
      by_cases hx : x = i
      · rw [hx, Function.update_self, hi]
      · rw [Function.update_of_ne hx]
    · refine ⟨mover l (bconf l) r, ?_⟩
      show bconf (l ++ [r]) = Function.update (bconf l) (mover l (bconf l) r) r
      exact hb_uncovered l r h
