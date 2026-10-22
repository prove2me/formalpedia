-- Prove2me | solution 1 for LeightonRao.Product.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:08:48.846923+00:00
-- url     : https://prove2.me/submissions/b9bafb93-98f6-4ec0-83a8-ff3f383ac87e

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

open scoped BigOperators

namespace LeightonRao.Product

variable {V : Type} [Fintype V] [DecidableEq V]

lemma lr_walkLen_nonneg (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    {u v : V} (p : N.graph.Walk u v) : 0 ≤ walkLen N d p := by
  unfold walkLen
  apply List.sum_nonneg
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact hd.1 _ _

lemma lr_walkLen_concat (N : Network V) (d : V → V → ℝ) {u v w : V}
    (p : N.graph.Walk u v) (h : N.graph.Adj v w) :
    walkLen N d (p.concat h) = walkLen N d p + d v w := by
  unfold walkLen
  simp [SimpleGraph.Walk.darts_concat, List.concat_eq_append]

lemma lr_walkLen_nil (N : Network V) (d : V → V → ℝ) (u : V) :
    walkLen N d (SimpleGraph.Walk.nil : N.graph.Walk u u) = 0 := by
  simp [walkLen]

lemma lr_dist_nonneg (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (u v : V) :
    0 ≤ dist N d u v :=
  Real.iInf_nonneg (fun p => lr_walkLen_nonneg N d hd p)

lemma lr_dist_le (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) {u v : V}
    (p : N.graph.Walk u v) : dist N d u v ≤ walkLen N d p :=
  ciInf_le ⟨0, by rintro _ ⟨q, rfl⟩; exact lr_walkLen_nonneg N d hd q⟩ p

lemma lr_dist_self (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (u : V) :
    dist N d u u = 0 :=
  le_antisymm (by simpa [lr_walkLen_nil] using lr_dist_le N d hd (SimpleGraph.Walk.nil : N.graph.Walk u u))
    (lr_dist_nonneg N d hd u u)

lemma lr_dist_adj (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (t : V) {u w : V}
    (h : N.graph.Adj u w) : dist N d t w ≤ dist N d t u + d u w := by
  by_cases hE : IsEmpty (N.graph.Walk t u)
  · have hE2 : IsEmpty (N.graph.Walk t w) := ⟨fun q => hE.false (q.concat h.symm)⟩
    have h1 : dist N d t w = 0 := Real.iInf_of_isEmpty _
    have h2 : dist N d t u = 0 := Real.iInf_of_isEmpty _
    rw [h1, h2]; linarith [hd.1 u w]
  · rw [not_isEmpty_iff] at hE
    have : dist N d t w - d u w ≤ dist N d t u := by
      apply le_ciInf
      intro p
      have := lr_dist_le N d hd (p.concat h)
      rw [lr_walkLen_concat] at this
      linarith
    linarith

lemma lr_distFrom_nonneg (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (u : V) : 0 ≤ distFrom N d T u :=
  Real.iInf_nonneg (fun t => lr_dist_nonneg N d hd _ _)

lemma lr_distFrom_le (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (u : V) (t : V) (ht : t ∈ T) : distFrom N d T u ≤ dist N d t u :=
  ciInf_le (f := fun s : T => dist N d s u)
    ⟨0, by rintro _ ⟨q, rfl⟩; exact lr_dist_nonneg N d hd _ _⟩ ⟨t, ht⟩

lemma lr_distFrom_mem (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (t : V) (ht : t ∈ T) : distFrom N d T t = 0 :=
  le_antisymm (by simpa [lr_dist_self N d hd] using lr_distFrom_le N d hd T t t ht)
    (lr_distFrom_nonneg N d hd T t)

lemma lr_distFrom_adj (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (hT : T.Nonempty) {u w : V} (h : N.graph.Adj u w) :
    distFrom N d T w ≤ distFrom N d T u + d u w := by
  have : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  have : distFrom N d T w - d u w ≤ distFrom N d T u := by
    apply le_ciInf
    intro t
    have h1 := lr_distFrom_le N d hd T w t.1 t.2
    have h2 := lr_dist_adj N d hd t.1 h
    linarith
  linarith

lemma lr_adj_of_pos (N : Network V) {u w : V} (h : 0 < N.C u w) : N.graph.Adj u w := by
  unfold Network.graph
  rw [SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl h⟩
  rintro rfl
  rw [N.C_self] at h
  exact lt_irrefl _ h

lemma lr_lip (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (hT : T.Nonempty) (u w : V) :
    N.C u w * |distFrom N d T w - distFrom N d T u| ≤ N.C u w * d u w := by
  rcases (N.C_nonneg u w).lt_or_eq with hC | hC
  · apply mul_le_mul_of_nonneg_left _ hC.le
    have h1 := lr_distFrom_adj N d hd T hT (lr_adj_of_pos N hC)
    have hC' : 0 < N.C w u := by rw [N.C_symm]; exact hC
    have h2 := lr_distFrom_adj N d hd T hT (lr_adj_of_pos N hC')
    rw [hd.2 w u] at h2
    rw [abs_le]; constructor <;> linarith
  · rw [← hC]; simp

lemma lr_integral_step (a b c : ℝ) :
    ∫ r, (Set.Ico a b).indicator (fun _ => c) r = max (b - a) 0 * c := by
  rw [MeasureTheory.integral_indicator_const _ measurableSet_Ico]
  simp [Real.volume_Ico, ENNReal.toReal_ofReal', MeasureTheory.Measure.real]

lemma lr_integrable_step (a b c : ℝ) :
    MeasureTheory.Integrable (fun r => (Set.Ico a b).indicator (fun _ => c) r) := by
  apply MeasureTheory.IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ico])

lemma lr_walkLen_append (N : Network V) (d : V → V → ℝ) {u v w : V}
    (p : N.graph.Walk u v) (q : N.graph.Walk v w) :
    walkLen N d (p.append q) = walkLen N d p + walkLen N d q := by
  unfold walkLen; simp [SimpleGraph.Walk.darts_append]

abbrev LrReach (N : Network V) (R : Finset V) (c y : V) :=
  {p : N.graph.Walk c y // ∀ x ∈ p.support, x ∈ R}

noncomputable def lrRho (N : Network V) (d : V → V → ℝ) (R : Finset V) (c : V) (M : ℝ)
    (y : V) : ℝ :=
  by classical exact if Nonempty (LrReach N R c y) then ⨅ p : LrReach N R c y, walkLen N d p.1 else M

lemma lr_rho_of_reach (N : Network V) (d : V → V → ℝ) (R : Finset V) (c : V) (M : ℝ) (y : V)
    (h : Nonempty (LrReach N R c y)) :
    lrRho N d R c M y = ⨅ p : LrReach N R c y, walkLen N d p.1 := by
  unfold lrRho; rw [if_pos h]

lemma lr_rho_of_not_reach (N : Network V) (d : V → V → ℝ) (R : Finset V) (c : V) (M : ℝ) (y : V)
    (h : ¬ Nonempty (LrReach N R c y)) : lrRho N d R c M y = M := by
  unfold lrRho; rw [if_neg h]

lemma lr_rho_le (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (R : Finset V)
    (c : V) (M : ℝ) {y : V} (p : LrReach N R c y) : lrRho N d R c M y ≤ walkLen N d p.1 := by
  rw [lr_rho_of_reach N d R c M y ⟨p⟩]
  exact ciInf_le ⟨0, by rintro _ ⟨q, rfl⟩; exact lr_walkLen_nonneg N d hd q.1⟩ p

lemma lr_rho_nonneg (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (R : Finset V)
    (c : V) (M : ℝ) (hM : 0 ≤ M) (y : V) : 0 ≤ lrRho N d R c M y := by
  by_cases h : Nonempty (LrReach N R c y)
  · rw [lr_rho_of_reach N d R c M y h]
    exact Real.iInf_nonneg fun p => lr_walkLen_nonneg N d hd p.1
  · rw [lr_rho_of_not_reach N d R c M y h]; exact hM

noncomputable def lrReachConcat (N : Network V) (R : Finset V) {c x y : V} (p : LrReach N R c x)
    (h : N.graph.Adj x y) (hy : y ∈ R) : LrReach N R c y :=
  ⟨p.1.concat h, by
    intro z hz
    rw [SimpleGraph.Walk.support_concat] at hz
    simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | hz
    · exact p.2 z hz
    · rw [hz]; exact hy⟩

lemma lr_rho_lip (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (R : Finset V)
    (c : V) (M : ℝ) {x y : V} (hx : x ∈ R) (hy : y ∈ R) (h : N.graph.Adj x y) :
    lrRho N d R c M y ≤ lrRho N d R c M x + d x y := by
  by_cases hr : Nonempty (LrReach N R c x)
  · have key : ∀ p : LrReach N R c x, lrRho N d R c M y - d x y ≤ walkLen N d p.1 := by
      intro p
      have := lr_rho_le N d hd R c M (lrReachConcat N R p h hy)
      simp only [lrReachConcat, lr_walkLen_concat] at this
      linarith
    have : lrRho N d R c M y - d x y ≤ lrRho N d R c M x := by
      rw [lr_rho_of_reach N d R c M x hr]
      exact le_ciInf key
    linarith
  · have hry : ¬ Nonempty (LrReach N R c y) := by
      rintro ⟨q⟩
      exact hr ⟨lrReachConcat N R q h.symm hx⟩
    rw [lr_rho_of_not_reach N d R c M x hr, lr_rho_of_not_reach N d R c M y hry]
    linarith [hd.1 x y]

open Classical in
noncomputable def lrBall (N : Network V) (d : V → V → ℝ) (R : Finset V) (c : V) (t : ℝ) :
    Finset V :=
  R.filter (fun y => ∃ p : LrReach N R c y, walkLen N d p.1 ≤ t)

lemma lr_mem_ball (N : Network V) (d : V → V → ℝ) (R : Finset V) (c : V) (t : ℝ) (y : V) :
    y ∈ lrBall N d R c t ↔ y ∈ R ∧ ∃ p : LrReach N R c y, walkLen N d p.1 ≤ t := by
  classical
  unfold lrBall; exact Finset.mem_filter

lemma lr_ball_iff (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (R : Finset V)
    (c : V) (M t : ℝ) (htM : t < M)
    (hF : ∀ y ∈ R, lrRho N d R c M y ≠ t) (y : V) :
    y ∈ lrBall N d R c t ↔ y ∈ R ∧ lrRho N d R c M y < t := by
  rw [lr_mem_ball]
  constructor
  · rintro ⟨hy, p, hp⟩
    exact ⟨hy, lt_of_le_of_ne (le_trans (lr_rho_le N d hd R c M p) hp) (hF y hy)⟩
  · rintro ⟨hy, hlt⟩
    refine ⟨hy, ?_⟩
    by_cases hr : Nonempty (LrReach N R c y)
    · rw [lr_rho_of_reach N d R c M y hr] at hlt
      obtain ⟨p, hp⟩ := exists_lt_of_ciInf_lt hlt
      exact ⟨p, hp.le⟩
    · rw [lr_rho_of_not_reach N d R c M y hr] at hlt
      linarith

lemma lr_ball_radius (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (R : Finset V)
    (c : V) (hc : c ∈ R) (t Δ : ℝ) (ht0 : 0 ≤ t) (htΔ : t ≤ Δ) :
    c ∈ lrBall N d R c t ∧ HasRadiusLE N d (lrBall N d R c t) Δ := by
  have hcB : c ∈ lrBall N d R c t := by
    rw [lr_mem_ball]
    refine ⟨hc, ⟨SimpleGraph.Walk.nil, by simp [hc]⟩, ?_⟩
    simp [lr_walkLen_nil, ht0]
  refine ⟨hcB, c, hcB, ?_⟩
  intro y hy
  rw [lr_mem_ball] at hy
  obtain ⟨hyR, p, hp⟩ := hy
  refine ⟨p.1, ?_, by linarith⟩
  intro x hx
  rw [lr_mem_ball]
  refine ⟨p.2 x hx, ⟨p.1.takeUntil x hx, fun z hz =>
    p.2 z (SimpleGraph.Walk.support_takeUntil_subset_support p.1 hx hz)⟩, ?_⟩
  have hsplit := congrArg (walkLen N d) (p.1.take_spec hx)
  rw [lr_walkLen_append] at hsplit
  have := lr_walkLen_nonneg N d hd (p.1.dropUntil x hx)
  simp only
  linarith


noncomputable def lrCutF (N : Network V) (R : Finset V) (ρ : V → ℝ) (t : ℝ) : ℝ :=
  ∑ x ∈ R, ∑ y ∈ R, (Set.Ioc (ρ x) (ρ y)).indicator (fun _ => N.C x y) t

lemma lr_cutF_nonneg (N : Network V) (R : Finset V) (ρ : V → ℝ) (t : ℝ) :
    0 ≤ lrCutF N R ρ t :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    Set.indicator_nonneg (fun _ _ => N.C_nonneg x y) t

lemma lr_integrable_Ioc (a b c : ℝ) :
    MeasureTheory.Integrable (fun r => (Set.Ioc a b).indicator (fun _ => c) r) := by
  apply MeasureTheory.IntegrableOn.integrable_indicator _ measurableSet_Ioc
  exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc])

lemma lr_cutF_integrable (N : Network V) (R : Finset V) (ρ : V → ℝ) :
    MeasureTheory.Integrable (lrCutF N R ρ) := by
  unfold lrCutF
  exact MeasureTheory.integrable_finsetSum _ fun x _ =>
    MeasureTheory.integrable_finsetSum _ fun y _ => lr_integrable_Ioc _ _ _

lemma lr_term_bound (a b c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    ∫ t in (0:ℝ)..r, (Set.Ioc a b).indicator (fun _ => c) t ≤ c * max (b - a) 0 := by
  rw [intervalIntegral.integral_of_le hr]
  calc ∫ t in Set.Ioc 0 r, (Set.Ioc a b).indicator (fun _ => c) t
      ≤ ∫ t, (Set.Ioc a b).indicator (fun _ => c) t :=
        MeasureTheory.setIntegral_le_integral (lr_integrable_Ioc a b c)
          (Filter.Eventually.of_forall (fun t => Set.indicator_nonneg (fun _ _ => hc) t))
    _ = c * max (b - a) 0 := by
        rw [MeasureTheory.integral_indicator_const _ measurableSet_Ioc]
        simp [Real.volume_Ioc, MeasureTheory.Measure.real, mul_comm, ENNReal.toReal_ofReal']

lemma lr_term_zero (a b c r : ℝ) (hr : 0 ≤ r) (har : r ≤ a) :
    ∫ t in (0:ℝ)..r, (Set.Ioc a b).indicator (fun _ => c) t = 0 := by
  rw [intervalIntegral.integral_of_le hr]
  apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  simp only [Set.indicator_apply, Set.mem_Ioc]
  rw [if_neg]
  intro h
  linarith [ht.2, h.1]

lemma lr_int_bound (N : Network V) (d : V → V → ℝ) (R : Finset V) (ρ : V → ℝ)
    (hlip : ∀ x ∈ R, ∀ y ∈ R, N.graph.Adj x y → ρ y ≤ ρ x + d x y)
    (hdsymm : ∀ u v, d u v = d v u) (r : ℝ) (hr : 0 ≤ r) :
    ∫ t in (0:ℝ)..r, lrCutF N R ρ t ≤
      (1/2) * ∑ x ∈ R, ∑ y ∈ R, if (ρ x < r ∨ ρ y < r) then N.C x y * d x y else 0 := by
  have hII : ∀ a b c : ℝ, IntervalIntegrable (fun t => (Set.Ioc a b).indicator (fun _ => c) t)
      MeasureTheory.volume 0 r := fun a b c => (lr_integrable_Ioc a b c).intervalIntegrable
  set T : V → V → ℝ := fun x y => ∫ t in (0:ℝ)..r, (Set.Ioc (ρ x) (ρ y)).indicator (fun _ => N.C x y) t
    with hTdef
  have hsplit : ∫ t in (0:ℝ)..r, lrCutF N R ρ t = ∑ x ∈ R, ∑ y ∈ R, T x y := by
    unfold lrCutF
    rw [intervalIntegral.integral_finsetSum
      (f := fun x t => ∑ y ∈ R, (Set.Ioc (ρ x) (ρ y)).indicator (fun _ => N.C x y) t)
      (fun x _ => (MeasureTheory.integrable_finsetSum _
        (fun y _ => lr_integrable_Ioc _ _ _)).intervalIntegrable)]
    refine Finset.sum_congr rfl fun x _ => ?_
    exact intervalIntegral.integral_finsetSum
      (f := fun y t => (Set.Ioc (ρ x) (ρ y)).indicator (fun _ => N.C x y) t) (fun y _ => hII _ _ _)
  rw [hsplit]
  have hsym : ∑ x ∈ R, ∑ y ∈ R, T x y = (1/2) * ∑ x ∈ R, ∑ y ∈ R, (T x y + T y x) := by
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun x y => T y x)]
    ring
  rw [hsym]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum; intro x hx
  apply Finset.sum_le_sum; intro y hy
  by_cases hcond : ρ x < r ∨ ρ y < r
  · rw [if_pos hcond]
    have h1 : T x y ≤ N.C x y * max (ρ y - ρ x) 0 := lr_term_bound _ _ _ _ (N.C_nonneg x y) hr
    have h2 : T y x ≤ N.C x y * max (ρ x - ρ y) 0 := by
      rw [N.C_symm]; exact lr_term_bound _ _ _ _ (N.C_nonneg y x) hr
    rcases (N.C_nonneg x y).lt_or_eq with hC | hC
    · have hadj := lr_adj_of_pos N hC
      have l1 := hlip x hx y hy hadj
      have l2 := hlip y hy x hx hadj.symm
      rw [hdsymm y x] at l2
      have : max (ρ y - ρ x) 0 + max (ρ x - ρ y) 0 ≤ d x y := by
        rcases le_total (ρ x) (ρ y) with h | h
        · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
        · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; linarith
      nlinarith
    · rw [← hC] at h1 h2 ⊢; simp at h1 h2; linarith
  · rw [if_neg hcond]
    push_neg at hcond
    have h1 : T x y = 0 := lr_term_zero _ _ _ _ hr hcond.1
    have h2 : T y x = 0 := lr_term_zero _ _ _ _ hr hcond.2
    rw [h1, h2]; norm_num

lemma lr_doubling (f : ℝ → ℝ) (hf : MeasureTheory.Integrable f) (hf0 : ∀ t, 0 ≤ f t)
    (s Δ : ℝ) (hΔ : 0 < Δ) (m : ℕ) (hm : 1 ≤ m) (F : Finset ℝ)
    (H : ∀ t, 0 ≤ t → t < Δ → t ∉ F → (m / Δ) * (s + ∫ u in (0:ℝ)..t, f u) ≤ f t) :
    2 ^ m * s ≤ s + ∫ u in (0:ℝ)..Δ, f u := by
  set g : ℝ → ℝ := fun t => s + ∫ u in (0:ℝ)..t, f u with hg
  have hII : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hf.intervalIntegrable
  have hgdiff : ∀ a b, g b = g a + ∫ u in a..b, f u := by
    intro a b
    simp only [hg]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII 0 a) (hII a b)]
    ring
  have hgmono : Monotone g := by
    intro a b hab
    rw [hgdiff a b]
    have := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hab (fun u _ => hf0 u)
    linarith
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  set h := Δ / m with hh
  have hhpos : 0 < h := div_pos hΔ hmpos
  have key : ∀ j : ℕ, j ≤ m → 2 ^ j * s ≤ g (j * h) := by
    intro j
    induction j with
    | zero => intro _; simp [hg]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      set a := (j : ℝ) * h
      have hb : ((j + 1 : ℕ) : ℝ) * h = a + h := by push_cast; ring
      rw [hb, hgdiff a (a + h)]
      have ha0 : 0 ≤ a := by positivity
      have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
      have hah : a + h ≤ Δ := by
        have : a + h = ((j:ℝ) + 1) * h := by ring
        rw [this, hh]
        calc ((j:ℝ) + 1) * (Δ / m) ≤ m * (Δ / m) := by
              apply mul_le_mul_of_nonneg_right hjm (by positivity)
          _ = Δ := by field_simp
      have hint : ∫ u in a..(a + h), (m / Δ) * g a ≤ ∫ u in a..(a + h), f u := by
        apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) (hII _ _)
        have hfin : MeasureTheory.volume ((F : Set ℝ) ∪ {a + h}) = 0 :=
          (F.finite_toSet.union (Set.finite_singleton _)).measure_zero _
        have hae : ∀ᵐ t ∂MeasureTheory.volume, t ∉ ((F : Set ℝ) ∪ {a + h}) :=
          MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hfin
        filter_upwards [MeasureTheory.ae_restrict_of_ae hae,
          MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht1 ht2
        simp only [Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff, not_or] at ht1
        have htb : t < a + h := lt_of_le_of_ne ht2.2 ht1.2
        have := H t (by linarith [ht2.1]) (by linarith) ht1.1
        have hmono := hgmono ht2.1
        have hk : 0 ≤ (m:ℝ) / Δ := by positivity
        calc (m / Δ) * g a ≤ (m / Δ) * g t := mul_le_mul_of_nonneg_left hmono hk
          _ ≤ f t := this
      rw [intervalIntegral.integral_const, smul_eq_mul] at hint
      have hcalc : (a + h - a) * ((m:ℝ) / Δ * g a) = g a := by
        rw [hh]; field_simp <;> ring
      rw [hcalc] at hint
      rw [pow_succ]
      linarith
  have := key m le_rfl
  have hmh : (m : ℝ) * h = Δ := by rw [hh]; field_simp
  rw [hmh] at this
  exact this


noncomputable def lrWR (N : Network V) (d : V → V → ℝ) (R : Finset V) : ℝ :=
  (1/2) * ∑ x ∈ R, ∑ y ∈ R, N.C x y * d x y

noncomputable def lrCutR (N : Network V) (R B : Finset V) : ℝ :=
  ∑ x ∈ B, ∑ y ∈ R \ B, N.C x y

lemma lr_ball_step (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (R : Finset V)
    (c : V) (hc : c ∈ R) (Δ : ℝ) (hΔ : 0 < Δ) (s : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hgrow : s + lrWR N d R < 2 ^ m * s) :
    ∃ B ⊆ R, c ∈ B ∧ HasRadiusLE N d B Δ ∧
      lrCutR N R B ≤ (m / Δ) * (s + (lrWR N d R - lrWR N d (R \ B))) := by
  set ρ := lrRho N d R c Δ with hρ
  have hlip : ∀ x ∈ R, ∀ y ∈ R, N.graph.Adj x y → ρ y ≤ ρ x + d x y :=
    fun x hx y hy h => lr_rho_lip N d hd R c Δ hx hy h
  set F : Finset ℝ := R.image ρ with hFdef
  set f := lrCutF N R ρ with hfdef
  have hCd : ∀ x y, 0 ≤ N.C x y * d x y := fun x y => mul_nonneg (N.C_nonneg x y) (hd.1 x y)
  obtain ⟨t, ht0, htΔ, htF, hlt⟩ : ∃ t, 0 ≤ t ∧ t < Δ ∧ t ∉ F ∧
      f t < (m / Δ) * (s + ∫ u in (0:ℝ)..t, f u) := by
    by_contra hcon
    push_neg at hcon
    have h1 := lr_doubling f (lr_cutF_integrable N R ρ) (lr_cutF_nonneg N R ρ) s Δ hΔ m hm F
      (fun t h0 h1 h2 => hcon t h0 h1 h2)
    have h2 := lr_int_bound N d R ρ hlip hd.2 Δ hΔ.le
    have h3 : (1/2) * ∑ x ∈ R, ∑ y ∈ R,
        (if (ρ x < Δ ∨ ρ y < Δ) then N.C x y * d x y else 0) ≤ lrWR N d R := by
      unfold lrWR
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum; intro x _; apply Finset.sum_le_sum; intro y _
      split_ifs
      · exact le_rfl
      · exact hCd x y
    linarith
  have hF : ∀ y ∈ R, ρ y ≠ t := by
    intro y hy heq; exact htF (Finset.mem_image.mpr ⟨y, hy, heq⟩)
  set B := lrBall N d R c t with hB
  have hBiff : ∀ y, y ∈ B ↔ y ∈ R ∧ ρ y < t := lr_ball_iff N d hd R c Δ t htΔ hF
  obtain ⟨hcB, hrad⟩ := lr_ball_radius N d hd R c hc t Δ ht0 htΔ.le
  have hBsub : B ⊆ R := fun y hy => ((hBiff y).mp hy).1
  have hBf : B = R.filter (fun y => ρ y < t) := by ext y; rw [hBiff, Finset.mem_filter]
  have hRBf : R \ B = R.filter (fun y => ¬ ρ y < t) := by
    ext y; rw [Finset.mem_sdiff, hBiff, Finset.mem_filter]; tauto
  refine ⟨B, hBsub, hcB, hrad, ?_⟩
  have hcut : lrCutR N R B = f t := by
    unfold lrCutR
    rw [hRBf, hBf]
    simp only [hfdef, lrCutF, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : ρ y < t
      · simp [Set.indicator_apply, hy, not_le.mpr hy]
      · simp [Set.indicator_apply, hx, hy, not_lt.mp hy]
    · symm; apply Finset.sum_eq_zero; intro y _
      simp only [Set.indicator_apply, Set.mem_Ioc]
      rw [if_neg]; intro h; exact hx h.1
  have hW : lrWR N d R - lrWR N d (R \ B) = (1/2) * ∑ x ∈ R, ∑ y ∈ R,
      (if (ρ x < t ∨ ρ y < t) then N.C x y * d x y else 0) := by
    unfold lrWR
    rw [hRBf]
    simp only [Finset.sum_filter]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ρ x < t
    · simp [hx]
    · simp only [hx, not_false_eq_true, if_true, false_or]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : ρ y < t <;> simp [hy]
  have hb := lr_int_bound N d R ρ hlip hd.2 t ht0
  have hk : 0 ≤ (m:ℝ) / Δ := by positivity
  rw [hcut, hW]
  calc f t ≤ (m / Δ) * (s + ∫ u in (0:ℝ)..t, f u) := hlt.le
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hk
      linarith

noncomputable def lrCross (N : Network V) (R : Finset V) (lab : V → V) : ℝ :=
  (1/2) * ∑ x ∈ R, ∑ y ∈ R, if lab x = lab y then 0 else N.C x y

lemma lr_WR_mono (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) {R S : Finset V}
    (h : R ⊆ S) : lrWR N d R ≤ lrWR N d S := by
  unfold lrWR
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hCd : ∀ x y, 0 ≤ N.C x y * d x y := fun x y => mul_nonneg (N.C_nonneg x y) (hd.1 x y)
  calc ∑ x ∈ R, ∑ y ∈ R, N.C x y * d x y ≤ ∑ x ∈ R, ∑ y ∈ S, N.C x y * d x y :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum_of_subset_of_nonneg h
          (fun y _ _ => hCd x y)
    _ ≤ ∑ x ∈ S, ∑ y ∈ S, N.C x y * d x y :=
        Finset.sum_le_sum_of_subset_of_nonneg h
          (fun x _ _ => Finset.sum_nonneg fun y _ => hCd x y)


lemma lr_main (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (π : V → ℝ)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (s : ℝ) (hs : 0 < s) (m : ℕ) (hm : 1 ≤ m)
    (hgrow : s + lrWR N d Finset.univ < 2 ^ m * s) :
    ∀ R : Finset V, ∃ lab : V → V, (∀ v ∈ R, lab v ∈ R) ∧
      (∀ u ∈ R, π u ≠ 0 → HasRadiusLE N d (R.filter (fun v => lab v = lab u)) Δ) ∧
      lrCross N R lab ≤ (m / Δ) * ((R.filter (fun v => π v ≠ 0)).card * s + lrWR N d R) := by
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
  have hk : 0 ≤ (m:ℝ) / Δ := by positivity
  have hWRnn : ∀ R : Finset V, 0 ≤ lrWR N d R := fun R => by
    unfold lrWR
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (N.C_nonneg x y) (hd.1 x y))
  by_cases hsupp : ∃ c ∈ R, π c ≠ 0
  swap
  · push_neg at hsupp
    rcases R.eq_empty_or_nonempty with hR | ⟨c0, hc0⟩
    · subst hR; refine ⟨id, by simp, by simp, ?_⟩; simp [lrCross, lrWR]
    · refine ⟨fun _ => c0, fun _ _ => hc0, fun u hu hπu => absurd (hsupp u hu) hπu, ?_⟩
      have h0 : lrCross N R (fun _ => c0) = 0 := by simp [lrCross]
      rw [h0]
      apply mul_nonneg hk
      have := hWRnn R
      positivity
  obtain ⟨c, hc, hcπ⟩ := hsupp
  · have hgR : s + lrWR N d R < 2 ^ m * s :=
      lt_of_le_of_lt (by linarith [lr_WR_mono N d hd (Finset.subset_univ R)]) hgrow
    obtain ⟨B, hBR, hcB, hrad, hcut⟩ := lr_ball_step N d hd R c hc Δ hΔ s m hm hgR
    set R' := R \ B with hR'
    have hR'lt : R' ⊂ R := Finset.sdiff_ssubset hBR ⟨c, hcB⟩
    obtain ⟨lab', hl1, hl2, hl3⟩ := ih R' hR'lt
    set lab : V → V := fun v => if v ∈ B then c else lab' v with hlab
    have hcR' : c ∉ R' := fun h => (Finset.mem_sdiff.mp h).2 hcB
    refine ⟨lab, ?_, ?_, ?_⟩
    · intro v hv
      by_cases hvB : v ∈ B
      · simp [lab, hvB, hc]
      · simp only [lab, hvB, if_false]
        exact (Finset.mem_sdiff.mp (hl1 v (Finset.mem_sdiff.mpr ⟨hv, hvB⟩))).1
    · intro u hu hπu
      by_cases huB : u ∈ B
      · have : R.filter (fun v => lab v = lab u) = B := by
          ext v
          simp only [Finset.mem_filter, lab, huB, if_true]
          constructor
          · rintro ⟨hv, hl⟩
            by_contra hvB
            rw [if_neg hvB] at hl
            exact hcR' (hl ▸ hl1 v (Finset.mem_sdiff.mpr ⟨hv, hvB⟩))
          · intro hvB; exact ⟨hBR hvB, by rw [if_pos hvB]⟩
        rw [this]; exact hrad
      · have huR' : u ∈ R' := Finset.mem_sdiff.mpr ⟨hu, huB⟩
        have : R.filter (fun v => lab v = lab u) = R'.filter (fun v => lab' v = lab' u) := by
          ext v
          simp only [Finset.mem_filter, lab, huB, if_false, hR', Finset.mem_sdiff]
          constructor
          · rintro ⟨hv, hl⟩
            by_cases hvB : v ∈ B
            · rw [if_pos hvB] at hl
              exact absurd (hl ▸ hl1 u huR') hcR'
            · rw [if_neg hvB] at hl; exact ⟨⟨hv, hvB⟩, hl⟩
          · rintro ⟨⟨hv, hvB⟩, hl⟩; exact ⟨hv, by rw [if_neg hvB]; exact hl⟩
        rw [this]; exact hl2 u huR' hπu
    · have e2 : ∀ x ∈ B, ∀ y ∈ R', (if lab x = lab y then (0:ℝ) else N.C x y) = N.C x y := by
        intro x hx y hy
        have hyB : y ∉ B := (Finset.mem_sdiff.mp hy).2
        have : lab x ≠ lab y := by
          simp only [lab, hx, hyB, if_true, if_false]
          intro h; exact hcR' (h ▸ hl1 y hy)
        rw [if_neg this]
      have e3 : ∀ x ∈ R', ∀ y ∈ B, (if lab x = lab y then (0:ℝ) else N.C x y) = N.C x y := by
        intro x hx y hy
        have hxB : x ∉ B := (Finset.mem_sdiff.mp hx).2
        have : lab x ≠ lab y := by
          simp only [lab, hy, hxB, if_true, if_false]
          intro h; exact hcR' (h.symm ▸ hl1 x hx)
        rw [if_neg this]
      have e1 : ∀ x ∈ B, ∀ y ∈ B, (if lab x = lab y then (0:ℝ) else N.C x y) = 0 := by
        intro x hx y hy; simp [lab, hx, hy]
      have e4 : ∀ x ∈ R', ∀ y ∈ R', (if lab x = lab y then (0:ℝ) else N.C x y) =
          (if lab' x = lab' y then (0:ℝ) else N.C x y) := by
        intro x hx y hy
        simp [lab, (Finset.mem_sdiff.mp hx).2, (Finset.mem_sdiff.mp hy).2]
      have hsum : ∑ x ∈ R, ∑ y ∈ R, (if lab x = lab y then (0:ℝ) else N.C x y) =
          ∑ x ∈ R', ∑ y ∈ R', (if lab' x = lab' y then (0:ℝ) else N.C x y) +
            2 * ∑ x ∈ B, ∑ y ∈ R', N.C x y := by
        calc ∑ x ∈ R, ∑ y ∈ R, (if lab x = lab y then (0:ℝ) else N.C x y)
            = ∑ x ∈ R, (∑ y ∈ R', (if lab x = lab y then (0:ℝ) else N.C x y) +
                ∑ y ∈ B, (if lab x = lab y then (0:ℝ) else N.C x y)) :=
              Finset.sum_congr rfl (fun x _ => (Finset.sum_sdiff hBR).symm)
          _ = ∑ x ∈ R', (∑ y ∈ R', (if lab x = lab y then (0:ℝ) else N.C x y) +
                ∑ y ∈ B, (if lab x = lab y then (0:ℝ) else N.C x y)) +
              ∑ x ∈ B, (∑ y ∈ R', (if lab x = lab y then (0:ℝ) else N.C x y) +
                ∑ y ∈ B, (if lab x = lab y then (0:ℝ) else N.C x y)) :=
              (Finset.sum_sdiff hBR).symm
          _ = ∑ x ∈ R', (∑ y ∈ R', (if lab' x = lab' y then (0:ℝ) else N.C x y) +
                ∑ y ∈ B, N.C x y) + ∑ x ∈ B, (∑ y ∈ R', N.C x y + 0) := by
              congr 1
              · refine Finset.sum_congr rfl fun x hx => ?_
                rw [Finset.sum_congr rfl (e4 x hx), Finset.sum_congr rfl (e3 x hx)]
              · refine Finset.sum_congr rfl fun x hx => ?_
                rw [Finset.sum_congr rfl (e2 x hx), Finset.sum_eq_zero (e1 x hx)]
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_comm (s := R') (t := B)]
              have : ∑ y ∈ B, ∑ x ∈ R', N.C x y = ∑ x ∈ B, ∑ y ∈ R', N.C x y := by
                refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
                rw [N.C_symm]
              rw [this]; simp only [add_zero]; ring
      have hsplit : lrCross N R lab = lrCross N R' lab' + lrCutR N R B := by
        unfold lrCross lrCutR
        rw [hsum]; ring
      have hcard : ((R'.filter (fun v => π v ≠ 0)).card : ℝ) + 1 ≤
          (R.filter (fun v => π v ≠ 0)).card := by
        have hsub : R'.filter (fun v => π v ≠ 0) ⊆ R.filter (fun v => π v ≠ 0) :=
          Finset.filter_subset_filter _ Finset.sdiff_subset
        have hss : R'.filter (fun v => π v ≠ 0) ⊂ R.filter (fun v => π v ≠ 0) :=
          (Finset.ssubset_iff_of_subset hsub).mpr
            ⟨c, Finset.mem_filter.mpr ⟨hc, hcπ⟩, fun h => hcR' (Finset.mem_filter.mp h).1⟩
        have := Finset.card_lt_card hss
        have : (R'.filter (fun v => π v ≠ 0)).card + 1 ≤ (R.filter (fun v => π v ≠ 0)).card := by
          omega
        exact_mod_cast this
      rw [hsplit]
      calc _ ≤ (m / Δ) * ((R'.filter (fun v => π v ≠ 0)).card * s + lrWR N d R') +
            (m / Δ) * (s + (lrWR N d R - lrWR N d R')) := add_le_add hl3 hcut
        _ = (m / Δ) * (((R'.filter (fun v => π v ≠ 0)).card + 1) * s + lrWR N d R) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) hk


lemma lr_partition (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (π : V → ℝ)
    (Δ : ℝ) (hΔ : 0 < Δ) (s : ℝ) (hs : 0 < s) (m : ℕ) (hm : 1 ≤ m)
    (hgrow : s + lrWR N d Finset.univ < 2 ^ m * s) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, (∃ x ∈ S, π x ≠ 0) → HasRadiusLE N d S Δ) ∧
      crossCap N P ≤ (m / Δ) * ((support π).card * s + totalWeight N d) := by
  classical
  obtain ⟨lab, -, hrad, hcross⟩ := lr_main N d hd π Δ hΔ s hs m hm hgrow Finset.univ
  let P := Finpartition.ofSetoid (Setoid.ker lab)
  have hpart : ∀ u, P.part u = Finset.univ.filter (fun v => lab v = lab u) := by
    intro u; ext v
    rw [Finpartition.mem_part_ofSetoid_iff_rel]
    simp [Setoid.ker, Function.onFun, eq_comm]
  have hpp : ∀ u v, P.part u = P.part v ↔ lab u = lab v := by
    intro u v; rw [hpart, hpart]; constructor
    · intro h
      have : u ∈ Finset.univ.filter (fun w => lab w = lab v) := by rw [← h]; simp
      simpa using this
    · intro h; rw [h]
  refine ⟨P, ?_, ?_⟩
  · rintro S hS ⟨x, hxS, hx⟩
    have hu : P.part x = S := P.part_eq_of_mem hS hxS
    rw [← hu, hpart]; exact hrad _ (Finset.mem_univ _) hx
  · have : crossCap N P = lrCross N Finset.univ lab := by
      unfold crossCap lrCross
      congr 1
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      by_cases h : lab x = lab y
      · rw [if_pos ((hpp x y).mpr h), if_pos h]
      · rw [if_neg (fun h' => h ((hpp x y).mp h')), if_neg h]
    rw [this]
    have hWR : lrWR N d Finset.univ = totalWeight N d := rfl
    have hsupp : support π = Finset.univ.filter (fun v => π v ≠ 0) := rfl
    rw [← hWR, hsupp]
    convert hcross using 4

theorem lemma_8_core (N : Network V) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (π : V → ℝ) (hp : 2 ≤ (support π).card) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, (∃ x ∈ S, π x ≠ 0) → HasRadiusLE N d S Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d * Real.logb 2 ((support π).card : ℝ) / Δ := by
  classical
  set W := totalWeight N d with hWdef
  have hW : 0 ≤ W := by
    rw [hWdef, totalWeight]
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (N.C_nonneg u v) (hd.1 u v)
  have hWR : lrWR N d Finset.univ = W := rfl
  set n := (support π).card with hn_def
  have hn : 1 < n := by omega
  set m := Nat.log 2 n + 1 with hm_def
  have hm : 1 ≤ m := by omega
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have h2m : (n:ℝ) + 1 ≤ 2 ^ m := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    have : n + 1 ≤ 2 ^ m := this
    exact_mod_cast this
  have hnpos : (0:ℝ) < n := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hp
    linarith
  have hmlog : (m:ℝ) ≤ 2 * Real.logb 2 n := by
    have hk : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.logb 2 n := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos, Real.rpow_natCast]
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h1 : (1:ℝ) ≤ Real.logb 2 n := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos, Real.rpow_one]
      exact_mod_cast hp
    have : (m:ℝ) = (Nat.log 2 n : ℕ) + 1 := by rw [hm_def]; push_cast; ring
    rw [this]; linarith
  have hε : ∀ ε > 0, ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, (∃ x ∈ S, π x ≠ 0) → HasRadiusLE N d S Δ) ∧
      crossCap N P ≤ 4 * W * Real.logb 2 n / Δ + ε := by
    intro ε hε
    set η := ε * Δ / m with hη_def
    have hη : 0 < η := by positivity
    set s := (W + η) / n with hs_def
    have hs : 0 < s := by positivity
    have hns : (n:ℝ) * s = W + η := by rw [hs_def]; field_simp
    have hgrow : s + lrWR N d Finset.univ < 2 ^ m * s := by
      rw [hWR]
      have := mul_le_mul_of_nonneg_right h2m hs.le
      nlinarith
    obtain ⟨P, hP, hc⟩ := lr_partition N d hd π Δ hΔ s hs m hm hgrow
    refine ⟨P, hP, ?_⟩
    calc crossCap N P ≤ (m / Δ) * (n * s + W) := hc
      _ = 2 * m * W / Δ + ε := by rw [hns, hη_def]; field_simp; ring
      _ ≤ 4 * W * Real.logb 2 n / Δ + ε := by
        have : 2 * m * W ≤ 4 * W * Real.logb 2 n := by nlinarith
        have := div_le_div_of_nonneg_right this hΔ.le
        linarith
  let good := (Finset.univ : Finset (Finpartition (Finset.univ : Finset V))).filter
    (fun P => ∀ S ∈ P.parts, (∃ x ∈ S, π x ≠ 0) → HasRadiusLE N d S Δ)
  obtain ⟨P0, hP0, -⟩ := hε 1 one_pos
  have hne : good.Nonempty := ⟨P0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP0⟩⟩
  obtain ⟨P, hPg, hPmin⟩ := good.exists_min_image (fun P => crossCap N P) hne
  refine ⟨P, (Finset.mem_filter.mp hPg).2, ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε'
  obtain ⟨Q, hQ, hQc⟩ := hε ε hε'
  exact le_trans (hPmin Q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ⟩)) hQc

end LeightonRao.Product

open LeightonRao.Product


theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (π : V → ℝ) (hp : 2 ≤ (support π).card) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      (∀ S ∈ P.parts, (∃ x ∈ S, π x ≠ 0) → HasRadiusLE N d S Δ) ∧
      crossCap N P ≤ 4 * totalWeight N d * Real.logb 2 ((support π).card : ℝ) / Δ := by
  exact lemma_8_core N d hd π hp Δ hΔ
