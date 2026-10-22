-- Prove2me | solution 1 for LeightonRao.Product.lp_duality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:33:19.800997+00:00
-- url     : https://prove2.me/submissions/1681dc17-91e4-426a-a848-d820ef50e436

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

lemma lr_sum_mem (U : Finset V) (g : V → ℝ) :
    ∑ u ∈ U, g u = ∑ u, if u ∈ U then g u else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma lr_cut_le_cross (N : Network V) (P : Finpartition (Finset.univ : Finset V)) (U : Finset V)
    (hU : ∀ u ∈ U, ∀ v, v ∉ U → P.part u ≠ P.part v) : cutCap N U ≤ crossCap N P := by
  have h1 : cutCap N U = ∑ u, ∑ v, if (u ∈ U ∧ v ∉ U) then N.C u v else 0 := by
    unfold cutCap
    rw [lr_sum_mem]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ U
    · rw [if_pos hu, lr_sum_mem]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v ∈ U <;> simp [hu, hv]
    · rw [if_neg hu]; symm; apply Finset.sum_eq_zero; intro v _; simp [hu]
  have h2 : cutCap N U = ∑ u, ∑ v, if (u ∉ U ∧ v ∈ U) then N.C u v else 0 := by
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;> simp [hu, hv, N.C_symm u v]
  have h3 : cutCap N U + cutCap N U ≤ ∑ u, ∑ v, if P.part u = P.part v then 0 else N.C u v := by
    conv_lhs => arg 1; rw [h1]
    rw [h2, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro u _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro v _
    by_cases hu : u ∈ U <;> by_cases hv : v ∈ U
    · simp only [hu, hv, not_true_eq_false, and_false, false_and, if_false, add_zero]
      split_ifs <;> linarith [N.C_nonneg u v]
    · simp only [hu, hv, not_false_eq_true, and_self, if_true, not_true_eq_false, false_and,
        if_false, add_zero]
      rw [if_neg (hU u hu v hv)]
    · simp only [hu, hv, not_false_eq_true, and_self, if_true, not_true_eq_false, false_and,
        and_false, if_false, zero_add]
      rw [if_neg (fun h => hU v hv u hu h.symm)]
    · simp only [hu, hv, not_false_eq_true, and_false, false_and, if_false, add_zero]
      split_ifs <;> linarith [N.C_nonneg u v]
  unfold crossCap; linarith


lemma lr_group (P : Finpartition (Finset.univ : Finset V)) (π : V → ℝ) (n : ℝ) (hn : 0 < n)
    (hsmall : ∀ S ∈ P.parts, 3 * piSum π S < 2 * n) :
    ∀ Q : Finset (Finset V), Q ⊆ P.parts →
      (∃ Q' ⊆ Q, n ≤ 3 * piSum π (Q'.sup id) ∧ 3 * piSum π (Q'.sup id) ≤ 2 * n) ∨
        3 * piSum π (Q.sup id) < n := by
  intro Q
  induction Q using Finset.induction_on with
  | empty => intro _; right; simp [piSum]; exact hn
  | insert S Q hSQ ih =>
    intro hsub
    have hS : S ∈ P.parts := hsub (Finset.mem_insert_self _ _)
    rcases ih (fun x hx => hsub (Finset.mem_insert_of_mem hx)) with ⟨Q', hQ', h1, h2⟩ | hlt
    · left; exact ⟨Q', hQ'.trans (Finset.subset_insert _ _), h1, h2⟩
    · have hdisj : Disjoint S (Q.sup id) := by
        rw [Finset.disjoint_sup_right]
        intro T hT
        have hTp : T ∈ P.parts := hsub (Finset.mem_insert_of_mem hT)
        have hne : S ≠ T := fun h => hSQ (h ▸ hT)
        exact P.disjoint hS hTp hne
      have hcard : piSum π ((insert S Q).sup id) = piSum π S + piSum π (Q.sup id) := by
        rw [Finset.sup_insert, id, Finset.sup_eq_union, piSum, Finset.sum_union hdisj]; rfl
      by_cases hA : 3 * piSum π ((insert S Q).sup id) < n
      · right; exact hA
      · by_cases hB : 3 * piSum π ((insert S Q).sup id) ≤ 2 * n
        · left; exact ⟨insert S Q, le_rfl, by linarith, hB⟩
        · left
          refine ⟨{S}, by simp, ?_, ?_⟩
          · simp only [Finset.sup_singleton, id]; linarith
          · simp only [Finset.sup_singleton, id]; have := hsmall S hS; linarith

theorem corollary_9_core (N : Network V) (π : V → ℝ)
    (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) :
    (∃ T : Finset V, 2 * ((support π).card : ℝ) ≤ 3 * piSum π T ∧
        HasRadiusLE N d T (1 / (2 * ((support π).card : ℝ) ^ 2))) ∨
    (∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
        weightedRatio N π U ≤
          36 * totalWeight N d * Real.logb 2 ((support π).card : ℝ)) := by
  set n : ℝ := ((support π).card : ℝ) with hn_def
  have hnR : (2:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hp
  have hΔ : (0:ℝ) < 1 / (2 * n ^ 2) := by positivity
  obtain ⟨P, hrad, hcc⟩ := lemma_8_core N d hd π hp _ hΔ
  have htot : piSum π Finset.univ = n := hπ.2
  by_cases hbig : ∃ S ∈ P.parts, 2 * n ≤ 3 * piSum π S
  · obtain ⟨S, hS, hSc⟩ := hbig
    left
    refine ⟨S, hSc, hrad S hS ?_⟩
    by_contra hno
    push_neg at hno
    have : piSum π S = 0 := Finset.sum_eq_zero hno
    linarith
  · push_neg at hbig
    right
    rcases lr_group P π n (by linarith) hbig P.parts le_rfl with ⟨Q', hQ', h1, h2⟩ | hlt
    · set U := Q'.sup id with hU
      have hUc : piSum π Uᶜ = n - piSum π U := by
        have := Finset.sum_add_sum_compl U π
        rw [← htot]; unfold piSum; linarith
      have hUpos : (0:ℝ) < piSum π U := by linarith
      have hUcpos : (0:ℝ) < piSum π Uᶜ := by rw [hUc]; linarith
      refine ⟨U, hUpos, hUcpos, ?_⟩
      have hsep : ∀ u ∈ U, ∀ v, v ∉ U → P.part u ≠ P.part v := by
        intro u hu v hv heq
        rw [hU, Finset.mem_sup] at hu
        obtain ⟨S, hSQ, huS⟩ := hu
        have hSp : S ∈ P.parts := hQ' hSQ
        have h1 : P.part u = S := P.part_eq_of_mem hSp huS
        have hvS : v ∈ S := by rw [← h1, heq]; exact P.mem_part (Finset.mem_univ v)
        exact hv (by rw [hU, Finset.mem_sup]; exact ⟨S, hSQ, hvS⟩)
      have hcut := lr_cut_le_cross N P U hsep
      have hcut0 : 0 ≤ cutCap N U := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
        N.C_nonneg u v
      have hprod : 2 * n ^ 2 / 9 ≤ piSum π U * piSum π Uᶜ := by
        rw [hUc]; nlinarith
      have hppos : 0 < piSum π U * piSum π Uᶜ := by positivity
      have hcc' : crossCap N P ≤ 8 * n ^ 2 * (totalWeight N d * Real.logb 2 n) := by
        rw [show 4 * totalWeight N d * Real.logb 2 n / (1 / (2 * n ^ 2)) =
          8 * n ^ 2 * (totalWeight N d * Real.logb 2 n) by field_simp; ring] at hcc
        exact hcc
      rw [weightedRatio, div_le_iff₀ hppos]
      have hX : 0 ≤ totalWeight N d * Real.logb 2 n := by
        have := le_trans hcut0 (le_trans hcut hcc')
        have hn2 : (0:ℝ) < 8 * n ^ 2 := by positivity
        nlinarith
      nlinarith
    · exfalso
      have : P.parts.sup id = Finset.univ := P.sup_parts
      rw [this, htot] at hlt
      linarith


lemma lr_piSum_nonneg (π : V → ℝ) (hπ : ∀ u, 0 ≤ π u) (U : Finset V) : 0 ≤ piSum π U :=
  Finset.sum_nonneg fun u _ => hπ u

lemma lemma_10_core (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (T : Finset V)
    (hT : 2 * ((support π).card : ℝ) ≤ 3 * piSum π T)
    (hsum : 1 / (2 * ((support π).card : ℝ)) ≤ ∑ u ∈ Tᶜ, π u * distFrom N d T u) :
    ∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
      weightedRatio N π U ≤ 6 * totalWeight N d := by
  have hπ0 : ∀ u, 0 ≤ π u := hπ.1
  set n : ℝ := ((support π).card : ℝ) with hn_def
  have hn2 : (2:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hp
  have hTpos : 0 < piSum π T := by linarith
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h | h
    · rw [h] at hTpos; simp [piSum] at hTpos
    · exact h
  set δ : V → ℝ := fun u => distFrom N d T u with hδ
  have hδnn : ∀ u, 0 ≤ δ u := fun u => lr_distFrom_nonneg N d hd T u
  have hδT : ∀ t ∈ T, δ t = 0 := fun t ht => lr_distFrom_mem N d hd T t ht
  set W := totalWeight N d with hW
  have hWnn : 0 ≤ W := by
    rw [hW, totalWeight]
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (N.C_nonneg u v) (hd.1 u v)
  -- Claim A
  set A := ∑ u, ∑ v, N.C u v * max (δ v - δ u) 0 with hA
  have hA_le : A ≤ W := by
    have hswap : ∑ u, ∑ v, N.C u v * max (δ u - δ v) 0 = A := by
      rw [hA, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [N.C_symm]
    have h2 : A + A ≤ ∑ u, ∑ v, N.C u v * d u v := by
      calc A + A = ∑ u, ∑ v, N.C u v * |δ v - δ u| := by
            conv_lhs => arg 1; rw [← hswap]
            rw [hA, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [← mul_add]
            congr 1
            rcases le_total (δ u) (δ v) with h | h
            · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith),
                max_eq_left (by linarith)]; ring
            · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith),
                max_eq_right (by linarith)]; ring
        _ ≤ ∑ u, ∑ v, N.C u v * d u v := by
            apply Finset.sum_le_sum; intro u _
            apply Finset.sum_le_sum; intro v _
            exact lr_lip N d hd T hTne u v
    rw [hW, totalWeight]; linarith
  have hAnn : ∀ u v, 0 ≤ N.C u v * max (δ v - δ u) 0 :=
    fun u v => mul_nonneg (N.C_nonneg u v) (le_max_right _ _)
  -- Claim B
  set B := ∑ u, ∑ v, π u * π v * max (δ v - δ u) 0 with hB
  have hB_ge : 1 / 3 ≤ B := by
    have hS : 1 / (2 * n) ≤ ∑ v, π v * δ v := by
      calc 1 / (2 * n) ≤ ∑ u ∈ Tᶜ, π u * δ u := hsum
        _ ≤ ∑ v, π v * δ v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun v _ _ => mul_nonneg (hπ0 v) (hδnn v))
    have h1 : piSum π T * ∑ v, π v * δ v ≤ B := by
      calc piSum π T * ∑ v, π v * δ v = ∑ u ∈ T, ∑ v, π u * π v * max (δ v - δ u) 0 := by
            rw [piSum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [hδT u hu, sub_zero, max_eq_left (hδnn v)]; ring
        _ ≤ B := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun u _ _ => Finset.sum_nonneg fun v _ =>
              mul_nonneg (mul_nonneg (hπ0 u) (hπ0 v)) (le_max_right _ _))
    have h3 : (1:ℝ) / 3 ≤ piSum π T * ∑ v, π v * δ v := by
      have hnpos : 0 < n := by linarith
      have : (1:ℝ) / 3 = (2 * n / 3) * (1 / (2 * n)) := by field_simp
      rw [this]
      apply mul_le_mul (by linarith) hS (by positivity) hTpos.le
    linarith
  -- the step function
  let f : ℝ → ℝ := fun r => ∑ u, ∑ v,
    (Set.Ico (δ u) (δ v)).indicator (fun _ => N.C u v - 6 * W * (π u * π v)) r
  have hint : ∫ r, f r = A - 6 * W * B := by
    simp only [f]
    rw [MeasureTheory.integral_finsetSum _ (fun u _ => MeasureTheory.integrable_finsetSum _
      (fun v _ => lr_integrable_step _ _ _))]
    simp_rw [MeasureTheory.integral_finsetSum _ (fun v _ => lr_integrable_step _ _ _),
      lr_integral_step]
    rw [hA, hB, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  -- f r in terms of a cut
  have hf_eq : ∀ r, f r = cutCap N (Finset.univ.filter (fun u => δ u ≤ r)) -
      6 * W * (piSum π (Finset.univ.filter (fun u => δ u ≤ r)) *
        piSum π (Finset.univ.filter (fun u => δ u ≤ r))ᶜ) := by
    intro r
    set U := Finset.univ.filter (fun u => δ u ≤ r) with hUdef
    have key : cutCap N U - 6 * W * (piSum π U * piSum π Uᶜ) =
        ∑ u ∈ U, ∑ v ∈ Uᶜ, (N.C u v - 6 * W * (π u * π v)) := by
      rw [cutCap, piSum, piSum, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hc : Uᶜ = Finset.univ.filter (fun u => ¬ δ u ≤ r) := Finset.compl_filter _
    rw [key, hc, hUdef]
    simp only [f, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with hu
    · refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : δ v ≤ r
      · simp [Set.indicator_apply, Set.mem_Ico, hu, hv, not_lt.mpr hv]
      · simp [Set.indicator_apply, Set.mem_Ico, hu, hv, lt_of_not_ge hv]
    · refine Finset.sum_eq_zero fun v _ => ?_
      simp only [Set.indicator_apply, Set.mem_Ico]
      rw [if_neg]
      tauto
  rcases hWnn.lt_or_eq with hWpos | hW0
  · have hneg : ∫ r, f r < 0 := by
      rw [hint]; nlinarith
    obtain ⟨r, hr⟩ : ∃ r, f r < 0 := by
      by_contra hcon
      push_neg at hcon
      exact absurd (MeasureTheory.integral_nonneg hcon) (not_le.mpr hneg)
    set U := Finset.univ.filter (fun u => δ u ≤ r)
    rw [hf_eq] at hr
    have hcut : 0 ≤ cutCap N U := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      N.C_nonneg u v
    have hprod : 0 < piSum π U * piSum π Uᶜ := by
      by_contra hc; push_neg at hc; nlinarith
    have hU0 := lr_piSum_nonneg π hπ0 U
    have hUc0 := lr_piSum_nonneg π hπ0 Uᶜ
    have hU : 0 < piSum π U := by
      rcases hU0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hprod; simp at hprod
    have hUc : 0 < piSum π Uᶜ := by
      rcases hUc0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hprod; simp at hprod
    refine ⟨U, hU, hUc, ?_⟩
    rw [weightedRatio, div_le_iff₀ hprod]; linarith
  · exfalso
    have hA0 : A = 0 := le_antisymm (by linarith)
      (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => hAnn u v)
    have hterm : ∀ u v, N.C u v * max (δ v - δ u) 0 = 0 := by
      intro u v
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ =>
        Finset.sum_nonneg fun v _ => hAnn u v)).mp hA0 u (Finset.mem_univ _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hAnn u v)).mp h1 v (Finset.mem_univ _)
    set U := Finset.univ.filter (fun u => δ u ≤ 0) with hUdef
    have hUne : U.Nonempty := by
      obtain ⟨t, ht⟩ := hTne
      exact ⟨t, by simp [hUdef, hδT t ht]⟩
    have hUcne : Uᶜ.Nonempty := by
      by_contra hc
      rw [Finset.not_nonempty_iff_eq_empty] at hc
      have hall : ∀ u, δ u = 0 := by
        intro u
        have : u ∉ Uᶜ := by rw [hc]; simp
        rw [Finset.mem_compl, not_not, hUdef, Finset.mem_filter] at this
        exact le_antisymm this.2 (hδnn u)
      have : ∑ u ∈ Tᶜ, π u * distFrom N d T u = 0 :=
        Finset.sum_eq_zero fun u _ => by
          have := hall u
          simp only [hδ] at this
          rw [this, mul_zero]
      rw [this] at hsum
      have : 0 < 1 / (2 * n) := by positivity
      linarith
    have hcut := hconn U hUne hUcne
    have : cutCap N U = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      apply Finset.sum_eq_zero
      intro v hv
      rw [hUdef, Finset.mem_filter] at hu
      rw [Finset.mem_compl, hUdef, Finset.mem_filter] at hv
      push_neg at hv
      have hpos : 0 < max (δ v - δ u) 0 := lt_max_of_lt_left (by linarith [hv (Finset.mem_univ _)])
      have := hterm u v
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · linarith
    linarith

lemma lr_conn (N : Network V) (hconn : IsConnectedNet N) (u v : V) :
    Nonempty (N.graph.Walk u v) := by
  classical
  by_contra h
  set U := Finset.univ.filter (fun w => N.graph.Reachable u w) with hU
  have huU : u ∈ U := by simp [hU]
  have hvU : v ∈ Uᶜ := by simp [hU]; exact h
  have hpos := hconn U ⟨u, huU⟩ ⟨v, hvU⟩
  have : cutCap N U ≤ 0 := by
    apply Finset.sum_nonpos; intro x hx
    apply Finset.sum_nonpos; intro y hy
    by_contra hC; push_neg at hC
    have hadj := lr_adj_of_pos N hC
    simp only [hU, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [hU, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact hy (hx.trans hadj.reachable)
  linarith

lemma lr_walkLen_reverse (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) {u v : V}
    (p : N.graph.Walk u v) : walkLen N d p.reverse = walkLen N d p := by
  unfold walkLen
  rw [SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  simp [hd.2]

lemma lr_dist_symm (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (hconn : IsConnectedNet N) (u v : V) : dist N d u v ≤ dist N d v u := by
  haveI := lr_conn N hconn v u
  apply le_ciInf
  intro q
  have := lr_dist_le N d hd q.reverse
  rwa [lr_walkLen_reverse N d hd] at this

lemma lr_dist_triangle (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (hconn : IsConnectedNet N) (u v w : V) : dist N d u w ≤ dist N d u v + dist N d v w := by
  haveI := lr_conn N hconn u v
  haveI := lr_conn N hconn v w
  have h1 : ∀ q : N.graph.Walk v w, dist N d u w - walkLen N d q ≤ dist N d u v := by
    intro q
    apply le_ciInf
    intro p
    have := lr_dist_le N d hd (p.append q)
    rw [lr_walkLen_append] at this
    linarith
  have h2 : dist N d u w - dist N d u v ≤ dist N d v w := by
    apply le_ciInf
    intro q
    have := h1 q
    linarith
  linarith


theorem lemma_11_core (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (hdc : SatisfiesPMFPConstraint N π d) :
    ∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
      weightedRatio N π U ≤ 36 * totalWeight N d * Real.logb 2 ((support π).card : ℝ) := by
  have hπ0 : ∀ u, 0 ≤ π u := hπ.1
  set n : ℝ := ((support π).card : ℝ) with hn_def
  have hnR : (2:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hp
  have hnpos : (0:ℝ) < n := by linarith
  have htot : ∑ u, π u = n := hπ.2
  have hW : 0 ≤ totalWeight N d := by
    rw [totalWeight]
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (N.C_nonneg u v) (hd.1 u v)
  have hlog : (1:ℝ) ≤ Real.logb 2 n := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hnpos, Real.rpow_one]; exact hnR
  rcases corollary_9_core N π hπ hp d hd with ⟨T, hT, hrad⟩ | h
  · set Δ : ℝ := 1 / (2 * n ^ 2) with hΔ
    obtain ⟨c, hcT, hc⟩ := hrad
    have hTne : T.Nonempty := ⟨c, hcT⟩
    haveI : Nonempty T := ⟨⟨c, hcT⟩⟩
    have hcy : ∀ y ∈ T, dist N d c y ≤ Δ := by
      intro y hy
      obtain ⟨p, -, hp⟩ := hc y hy
      exact le_trans (lr_dist_le N d hd p) hp
    set δ : V → ℝ := fun u => distFrom N d T u with hδ
    have hatt : ∀ u, ∃ t ∈ T, dist N d t u = δ u := by
      intro u
      obtain ⟨t, ht⟩ := exists_eq_ciInf_of_finite (f := fun t : T => dist N d t.1 u)
      exact ⟨t.1, t.2, ht⟩
    have hpair : ∀ u v, dist N d u v ≤ δ u + δ v + 2 * Δ := by
      intro u v
      obtain ⟨tu, htu, hu⟩ := hatt u
      obtain ⟨tv, htv, hv⟩ := hatt v
      have a1 := lr_dist_triangle N d hd hconn u tu v
      have a2 := lr_dist_triangle N d hd hconn tu c v
      have a3 := lr_dist_triangle N d hd hconn c tv v
      have b1 := lr_dist_symm N d hd hconn u tu
      have b2 := lr_dist_symm N d hd hconn tu c
      have c1 := hcy tu htu
      have c2 := hcy tv htv
      linarith
    have hsumall : 2 ≤ ∑ u, ∑ v, π u * π v * dist N d u v := by
      have := hdc; unfold SatisfiesPMFPConstraint at this; linarith
    set S := ∑ u, π u * δ u with hSdef
    have hexp : ∀ u, ∑ v, π u * π v * (δ u + δ v + 2 * Δ) =
        π u * δ u * n + π u * S + 2 * Δ * π u * n := by
      intro u
      rw [← htot, hSdef, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      ring
    have hbound : ∑ u, ∑ v, π u * π v * dist N d u v ≤ 2 * n * S + 1 := by
      calc ∑ u, ∑ v, π u * π v * dist N d u v
          ≤ ∑ u, ∑ v, π u * π v * (δ u + δ v + 2 * Δ) :=
            Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
              mul_le_mul_of_nonneg_left (hpair u v) (mul_nonneg (hπ0 u) (hπ0 v))
        _ = ∑ u, (π u * δ u * n + π u * S + 2 * Δ * π u * n) := Finset.sum_congr rfl fun u _ => hexp u
        _ = S * n + n * S + 2 * Δ * n * n := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
              ← hSdef, htot, ← Finset.sum_mul, ← Finset.mul_sum, htot]
        _ = 2 * n * S + 1 := by rw [hΔ]; field_simp; ring
    have hS : 1 / (2 * n) ≤ S := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hST : ∑ u ∈ Tᶜ, π u * distFrom N d T u = S := by
      rw [hSdef, ← Finset.sum_compl_add_sum T]
      have : ∑ u ∈ T, π u * δ u = 0 :=
        Finset.sum_eq_zero fun u hu => by simp [hδ, lr_distFrom_mem N d hd T u hu]
      rw [this, add_zero]
    obtain ⟨U, hU1, hU2, hU3⟩ := lemma_10_core N hconn π hπ hp d hd T hT (by rw [hST]; exact hS)
    refine ⟨U, hU1, hU2, le_trans hU3 ?_⟩
    nlinarith
  · exact h


lemma lr_flow_le_cap (N : Network V) (D : V → V → ℝ) (f : V → V → V → V → ℝ) (lam : ℝ)
    (hf : IsConcurrentFlow N D f lam) (s t i j : V) : f s t i j ≤ N.C i j := by
  have h1 : f s t i j ≤ f s t i j + f s t j i := by linarith [hf.1 s t j i]
  have h2 : f s t i j + f s t j i ≤ ∑ t', (f s t' i j + f s t' j i) :=
    Finset.single_le_sum (f := fun t' => f s t' i j + f s t' j i)
      (fun t' _ => add_nonneg (hf.1 _ _ _ _) (hf.1 _ _ _ _)) (Finset.mem_univ t)
  have h3 : ∑ t', (f s t' i j + f s t' j i) ≤ ∑ s', ∑ t', (f s' t' i j + f s' t' j i) :=
    Finset.single_le_sum (f := fun s' => ∑ t', (f s' t' i j + f s' t' j i))
      (fun s' _ => Finset.sum_nonneg fun t' _ => add_nonneg (hf.1 _ _ _ _) (hf.1 _ _ _ _))
      (Finset.mem_univ s)
  linarith [hf.2.2.2 i j]

lemma lr_potential (g : V → V → ℝ) (φ : V → ℝ) :
    ∑ i, ∑ j, g i j * (φ j - φ i) = - ∑ v, φ v * (∑ j, g v j - ∑ j, g j v) := by
  have e1 : ∑ i, ∑ j, g i j * φ j = ∑ v, φ v * ∑ j, g j v := by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have e2 : ∑ i, ∑ j, g i j * φ i = ∑ v, φ v * ∑ j, g v j := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have e3 : ∑ i, ∑ j, g i j * (φ j - φ i) =
      ∑ i, ∑ j, g i j * φ j - ∑ i, ∑ j, g i j * φ i := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j _ => ?_; ring
  have e4 : ∑ v, φ v * (∑ j, g v j - ∑ j, g j v) =
      ∑ v, φ v * ∑ j, g v j - ∑ v, φ v * ∑ j, g j v := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun v _ => ?_; ring
  rw [e3, e1, e2, e4]; ring

lemma lr_commodity_bound (N : Network V) (D : V → V → ℝ) (f : V → V → V → V → ℝ) (lam : ℝ)
    (hf : IsConcurrentFlow N D f lam) (d : V → V → ℝ) (hd : IsDistanceFunction d) (s t : V) :
    lam * D s t * dist N d s t ≤ ∑ i, ∑ j, f s t i j * d i j := by
  by_cases hst : s = t
  · subst hst
    rw [lr_dist_self N d hd s]
    simp [hf.2.2.1 s]
  · set φ : V → ℝ := fun v => dist N d s v with hφ
    have hcons := hf.2.1 s t hst
    have hpot := lr_potential (f s t) φ
    have hrhs : ∑ v, φ v * (∑ j, f s t v j - ∑ j, f s t j v) = lam * D s t * (φ s - φ t) := by
      rw [Finset.sum_congr rfl fun v _ => by rw [hcons v]]
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have hφs : φ s = 0 := lr_dist_self N d hd s
    have hle : ∀ i j, f s t i j * (φ j - φ i) ≤ f s t i j * d i j := by
      intro i j
      rcases (N.C_nonneg i j).lt_or_eq with hC | hC
      · apply mul_le_mul_of_nonneg_left _ (hf.1 s t i j)
        have := lr_dist_adj N d hd s (lr_adj_of_pos N hC)
        simp only [hφ]; linarith
      · have h0 : f s t i j = 0 :=
          le_antisymm (by rw [hC]; exact lr_flow_le_cap N D f lam hf s t i j) (hf.1 s t i j)
        rw [h0]; simp
    have hsum : ∑ i, ∑ j, f s t i j * (φ j - φ i) ≤ ∑ i, ∑ j, f s t i j * d i j :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hle i j
    rw [hpot, hrhs, hφs] at hsum
    have : dist N d s t = φ t := rfl
    rw [this]; linarith

lemma lr_sum4_comm (F : V → V → V → V → ℝ) :
    ∑ s, ∑ t, ∑ i, ∑ j, F s t i j = ∑ i, ∑ j, ∑ s, ∑ t, F s t i j := by
  calc ∑ s, ∑ t, ∑ i, ∑ j, F s t i j = ∑ s, ∑ i, ∑ t, ∑ j, F s t i j :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ i, ∑ s, ∑ t, ∑ j, F s t i j := Finset.sum_comm
    _ = ∑ i, ∑ s, ∑ j, ∑ t, F s t i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ s, ∑ t, F s t i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm

lemma lr_weak_dual (N : Network V) (D : V → V → ℝ) (f : V → V → V → V → ℝ) (lam : ℝ)
    (hf : IsConcurrentFlow N D f lam) (d : V → V → ℝ) (hd : IsDistanceFunction d) :
    lam * ∑ s, ∑ t, D s t * dist N d s t ≤ totalWeight N d := by
  have h1 : lam * ∑ s, ∑ t, D s t * dist N d s t ≤ ∑ s, ∑ t, ∑ i, ∑ j, f s t i j * d i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro t _
    have := lr_commodity_bound N D f lam hf d hd s t
    linarith
  have h2 : ∑ s, ∑ t, ∑ i, ∑ j, f s t i j * d i j =
      ∑ i, ∑ j, d i j * ∑ s, ∑ t, f s t i j := by
    rw [lr_sum4_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => ?_
    ring
  set G : V → V → ℝ := fun i j => ∑ s, ∑ t, f s t i j with hG
  have h3 : ∑ i, ∑ j, d i j * G i j = (1/2) * ∑ i, ∑ j, d i j * (G i j + G j i) := by
    have : ∑ i, ∑ j, d i j * G j i = ∑ i, ∑ j, d i j * G i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hd.2]
    simp only [mul_add, Finset.sum_add_distrib, this]; ring
  have h4 : ∀ i j, G i j + G j i ≤ N.C i j := by
    intro i j
    have := hf.2.2.2 i j
    simp only [hG, ← Finset.sum_add_distrib]
    exact this
  have h5 : ∑ i, ∑ j, d i j * (G i j + G j i) ≤ ∑ i, ∑ j, N.C i j * d i j :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      rw [mul_comm (N.C i j)]; exact mul_le_mul_of_nonneg_left (h4 i j) (hd.1 i j)
  rw [totalWeight]
  have : ∑ s, ∑ t, ∑ i, ∑ j, f s t i j * d i j = ∑ i, ∑ j, d i j * G i j := h2
  linarith

lemma lr_zero_flow (N : Network V) (D : V → V → ℝ) :
    IsConcurrentFlow N D (fun _ _ _ _ => 0) 0 := by
  refine ⟨fun _ _ _ _ => le_rfl, ?_, fun _ _ _ => rfl, ?_⟩
  · intro s t _ v; simp
  · intro i j; simp [N.C_nonneg]

lemma lr_DX (N : Network V) (π : V → ℝ) (d : V → V → ℝ) (hd : IsDistanceFunction d) :
    ∑ s, ∑ t, productDemand π s t * dist N d s t =
      (1/2) * ∑ u, ∑ v, π u * π v * dist N d u v := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold productDemand
  split_ifs with h
  · subst h; rw [lr_dist_self N d hd]; ring
  · ring

lemma lr_flowset_le (N : Network V) (π : V → ℝ) (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (hc : SatisfiesPMFPConstraint N π d) (lam : ℝ)
    (hlam : lam ∈ {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N (productDemand π) f lam}) :
    lam ≤ totalWeight N d := by
  obtain ⟨h0, f, hf⟩ := hlam
  have := lr_weak_dual N _ f lam hf d hd
  rw [lr_DX N π d hd] at this
  unfold SatisfiesPMFPConstraint at hc
  nlinarith

theorem lp_duality_part1 (N : Network V) (π : V → ℝ) :
    ∀ d : V → V → ℝ, IsDistanceFunction d → SatisfiesPMFPConstraint N π d →
        maxFlow N (productDemand π) ≤ totalWeight N d := by
  intro d hd hc
  unfold maxFlow
  apply csSup_le (⟨0, le_rfl, _, lr_zero_flow N _⟩ :
    Set.Nonempty {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N (productDemand π) f lam})
  intro lam hlam
  exact lr_flowset_le N π d hd hc lam hlam

def lrCutMetric (U : Finset V) : V → V → ℝ := fun i j => if (i ∈ U ↔ j ∈ U) then 0 else 1

lemma lr_cutMetric_isDist (U : Finset V) : IsDistanceFunction (lrCutMetric U) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · unfold lrCutMetric; split_ifs <;> norm_num
  · unfold lrCutMetric; simp only [iff_comm]

lemma lr_walkLen_cons (N : Network V) (d : V → V → ℝ) {u v w : V} (h : N.graph.Adj u v)
    (p : N.graph.Walk v w) :
    walkLen N d (SimpleGraph.Walk.cons h p) = d u v + walkLen N d p := by
  simp [walkLen, SimpleGraph.Walk.darts_cons]

lemma lr_cutmetric_walk (N : Network V) (U : Finset V) : ∀ {a b : V} (p : N.graph.Walk a b),
    (if (a ∈ U ↔ b ∈ U) then (0:ℝ) else 1) ≤ walkLen N (lrCutMetric U) p := by
  intro a b p
  induction p with
  | nil => simp [lr_walkLen_nil]
  | @cons u v w h p ih =>
    rw [lr_walkLen_cons]
    have hnn := lr_walkLen_nonneg N _ (lr_cutMetric_isDist U) p
    unfold lrCutMetric at ih ⊢
    by_cases hu : u ∈ U <;> by_cases hv : v ∈ U <;> by_cases hw : w ∈ U <;>
      simp [hu, hv, hw] at ih ⊢ <;> linarith

lemma lr_cutmetric_dist (N : Network V) (hconn : IsConnectedNet N) (U : Finset V) (s t : V) :
    (if (s ∈ U ↔ t ∈ U) then (0:ℝ) else 1) ≤ dist N (lrCutMetric U) s t := by
  haveI := lr_conn N hconn s t
  exact le_ciInf fun p => lr_cutmetric_walk N U p

lemma lr_sum_ind (U : Finset V) (g : V → V → ℝ) :
    ∑ s, ∑ t, (if s ∈ U ∧ t ∉ U then g s t else 0) = ∑ s ∈ U, ∑ t ∈ Uᶜ, g s t := by
  rw [lr_sum_mem U]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s ∈ U
  · simp only [hs, true_and, if_true]; rw [lr_sum_mem Uᶜ]; simp [Finset.mem_compl]
  · simp [hs]

lemma lr_sum_ind2 (U : Finset V) (g : V → V → ℝ) :
    ∑ s, ∑ t, (if s ∉ U ∧ t ∈ U then g s t else 0) = ∑ s ∈ Uᶜ, ∑ t ∈ U, g s t := by
  rw [lr_sum_mem Uᶜ]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s ∈ U
  · simp [hs]
  · simp only [hs, not_false_eq_true, true_and, if_true, Finset.mem_compl]; rw [lr_sum_mem U]

lemma lr_cutMetric_weight (N : Network V) (U : Finset V) :
    totalWeight N (lrCutMetric U) = cutCap N U := by
  have e : ∀ i j, N.C i j * lrCutMetric U i j =
      (if i ∈ U ∧ j ∉ U then N.C i j else 0) + (if i ∉ U ∧ j ∈ U then N.C i j else 0) := by
    intro i j
    unfold lrCutMetric
    by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;> simp [hi, hj]
  rw [totalWeight]
  simp only [e, Finset.sum_add_distrib]
  rw [lr_sum_ind, lr_sum_ind2]
  have : ∑ s ∈ Uᶜ, ∑ t ∈ U, N.C s t = cutCap N U := by
    rw [cutCap, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [N.C_symm]
  rw [this, ← cutCap]; ring

lemma lr_cut_bound (N : Network V) (hconn : IsConnectedNet N) (π : V → ℝ) (hπ0 : ∀ u, 0 ≤ π u)
    (f : V → V → V → V → ℝ) (lam : ℝ) (hf : IsConcurrentFlow N (productDemand π) f lam)
    (hlam : 0 ≤ lam) (U : Finset V) :
    lam * (piSum π U * piSum π Uᶜ) ≤ cutCap N U := by
  have hw := lr_weak_dual N _ f lam hf (lrCutMetric U) (lr_cutMetric_isDist U)
  rw [lr_cutMetric_weight] at hw
  have hD : ∀ s t, 0 ≤ productDemand π s t := by
    intro s t; unfold productDemand; split_ifs
    · exact le_rfl
    · have := mul_nonneg (hπ0 s) (hπ0 t); linarith
  have e : ∀ s t, productDemand π s t * (if (s ∈ U ↔ t ∈ U) then (0:ℝ) else 1) =
      (if s ∈ U ∧ t ∉ U then π s * π t / 2 else 0) +
        (if s ∉ U ∧ t ∈ U then π s * π t / 2 else 0) := by
    intro s t
    by_cases hst : s = t
    · subst hst; simp [productDemand]
    · unfold productDemand
      by_cases hs : s ∈ U <;> by_cases ht : t ∈ U <;> simp [hs, ht, hst]
  have hlow : piSum π U * piSum π Uᶜ ≤ ∑ s, ∑ t, productDemand π s t * dist N (lrCutMetric U) s t := by
    calc piSum π U * piSum π Uᶜ
        = ∑ s, ∑ t, productDemand π s t * (if (s ∈ U ↔ t ∈ U) then (0:ℝ) else 1) := by
          simp only [e, Finset.sum_add_distrib]
          rw [lr_sum_ind, lr_sum_ind2]
          have h1 := Finset.sum_mul_sum U Uᶜ π π
          have h2 := Finset.sum_mul_sum Uᶜ U π π
          simp_rw [← Finset.sum_div]
          rw [← h1, ← h2]; unfold piSum; ring
      _ ≤ _ := Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left (lr_cutmetric_dist N hconn U s t) (hD s t)
  nlinarith

lemma lr_shortest_walk (N : Network V) (hconn : IsConnectedNet N) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (s t : V) :
    ∃ w : N.graph.Walk s t, walkLen N d w = dist N d s t ∧ w.length ≤ Fintype.card V := by
  classical
  set S : Finset (N.graph.Walk s t) :=
    (Finset.range (Fintype.card V)).biUnion (fun k => N.graph.finsetWalkLength k s t) with hS
  obtain ⟨p⟩ := lr_conn N hconn s t
  have hmem : ∀ q : N.graph.Walk s t, q.IsPath → q ∈ S := by
    intro q hq
    simp only [hS, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨q.length, hq.length_lt, SimpleGraph.mem_finsetWalkLength_iff.mpr rfl⟩
  have hne : S.Nonempty := ⟨_, hmem _ p.bypass_isPath⟩
  obtain ⟨w, hwS, hwmin⟩ := S.exists_min_image (fun q => walkLen N d q) hne
  have hwlen : w.length ≤ Fintype.card V := by
    simp only [hS, Finset.mem_biUnion, Finset.mem_range] at hwS
    obtain ⟨k, hk, hw⟩ := hwS
    rw [SimpleGraph.mem_finsetWalkLength_iff] at hw; omega
  refine ⟨w, le_antisymm ?_ (lr_dist_le N d hd w), hwlen⟩
  haveI : Nonempty (N.graph.Walk s t) := ⟨p⟩
  apply le_ciInf
  intro q
  calc walkLen N d w ≤ walkLen N d q.bypass := hwmin _ (hmem _ q.bypass_isPath)
    _ ≤ walkLen N d q := by
      unfold walkLen
      apply ((SimpleGraph.Walk.darts_bypass_sublist_darts q).map _).sum_le_sum
      intro a ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      exact hd.1 _ _

noncomputable def lrCnt (N : Network V) {s t : V} (w : N.graph.Walk s t) (i j : V) : ℝ :=
  (w.darts.map (fun a => if a.fst = i ∧ a.snd = j then (1:ℝ) else 0)).sum

lemma lr_cnt_cons (N : Network V) {u v w : V} (h : N.graph.Adj u v) (p : N.graph.Walk v w)
    (i j : V) : lrCnt N (SimpleGraph.Walk.cons h p) i j =
      (if u = i ∧ v = j then (1:ℝ) else 0) + lrCnt N p i j := by
  simp [lrCnt, SimpleGraph.Walk.darts_cons]

lemma lr_cnt_nil (N : Network V) {u : V} (i j : V) :
    lrCnt N (SimpleGraph.Walk.nil : N.graph.Walk u u) i j = 0 := by
  simp [lrCnt]

lemma lr_cnt_len (N : Network V) (d : V → V → ℝ) : ∀ {s t : V} (w : N.graph.Walk s t),
    ∑ i, ∑ j, d i j * lrCnt N w i j = walkLen N d w := by
  intro s t w
  induction w with
  | nil => simp [lr_cnt_nil, lr_walkLen_nil]
  | @cons u v w h p ih =>
    rw [lr_walkLen_cons, ← ih]
    simp only [lr_cnt_cons, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_and]
    simp

lemma lr_cnt_cons_eq (N : Network V) : ∀ {s t : V} (w : N.graph.Walk s t) (v : V),
    ∑ j, lrCnt N w v j - ∑ j, lrCnt N w j v =
      (if v = s then (1:ℝ) else 0) - (if v = t then 1 else 0) := by
  intro s t w
  induction w with
  | nil => intro v; simp [lr_cnt_nil]
  | @cons u x w h p ih =>
    intro v
    have := ih v
    simp only [lr_cnt_cons, Finset.sum_add_distrib, ite_and]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have a1 : (if u = v then (1:ℝ) else 0) = if v = u then 1 else 0 := by
      by_cases h : v = u
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (fun h' => h h'.symm), if_neg h]
    have a2 : (if x = v then (1:ℝ) else 0) = if v = x then 1 else 0 := by
      by_cases h : v = x
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (fun h' => h h'.symm), if_neg h]
    have a0 : (∑ j, if u = v then (if x = j then (1:ℝ) else 0) else 0) = if u = v then 1 else 0 := by
      split_ifs <;> simp
    rw [a0, a1, a2]; linarith

lemma lr_cnt_nonneg (N : Network V) {s t : V} (w : N.graph.Walk s t) (i j : V) :
    0 ≤ lrCnt N w i j := by
  unfold lrCnt
  apply List.sum_nonneg
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  split_ifs <;> norm_num

lemma lr_cnt_le (N : Network V) : ∀ {s t : V} (w : N.graph.Walk s t) (i j : V),
    lrCnt N w i j ≤ w.length := by
  intro s t w
  induction w with
  | nil => intro i j; simp [lr_cnt_nil]
  | @cons u v w h p ih =>
    intro i j
    rw [lr_cnt_cons, SimpleGraph.Walk.length_cons]
    have := ih i j
    push_cast
    split_ifs <;> linarith

lemma lr_dist_scale (N : Network V) (d : V → V → ℝ) (c : ℝ) (hc : 0 ≤ c) (u v : V) :
    dist N (fun i j => c * d i j) u v = c * dist N d u v := by
  unfold dist
  rw [Real.mul_iInf_of_nonneg hc]
  congr 1; funext p
  simp [walkLen, List.sum_map_mul_left]

lemma lr_dual_approx (N : Network V) (hconn : IsConnectedNet N) (π : V → ℝ)
    (hπ0 : ∀ u, 0 ≤ π u) (lam : ℝ) (hlam : 0 < lam)
    (hnot : ∀ f, ¬ IsConcurrentFlow N (productDemand π) f lam) :
    ∃ d, IsDistanceFunction d ∧ SatisfiesPMFPConstraint N π d ∧ totalWeight N d < lam := by
  classical
  set D := productDemand π with hDdef
  have hD : ∀ s t, 0 ≤ D s t := by
    intro s t; simp only [hDdef, productDemand]; split_ifs
    · exact le_rfl
    · have := mul_nonneg (hπ0 s) (hπ0 t); linarith
  set M : ℝ := (∑ s, ∑ t, D s t) * Fintype.card V with hM
  have hDM : ∀ s t, D s t * Fintype.card V ≤ M := by
    intro s t
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    calc D s t ≤ ∑ t', D s t' := Finset.single_le_sum (fun t' _ => hD s t') (Finset.mem_univ t)
      _ ≤ ∑ s', ∑ t', D s' t' := Finset.single_le_sum (f := fun s' => ∑ t', D s' t')
          (fun s' _ => Finset.sum_nonneg fun t' _ => hD s' t') (Finset.mem_univ s)
  let K : Set (V → V → V → V → ℝ) := {f | (∀ s t i j, 0 ≤ f s t i j ∧ f s t i j ≤ M) ∧
      (∀ s t, s ≠ t → ∀ v, ∑ j, f s t v j - ∑ j, f s t j v =
        D s t * ((if v = s then 1 else 0) - (if v = t then 1 else 0))) ∧
      (∀ s i j, f s s i j = 0)}
  have hKsub : K ⊆ Set.Icc 0 (fun _ _ _ _ => M) := by
    intro f hf; exact ⟨fun s t i j => (hf.1 s t i j).1, fun s t i j => (hf.1 s t i j).2⟩
  have hKc : IsClosed K := by
    show IsClosed {f : V → V → V → V → ℝ | _}
    simp only [Set.setOf_and, Set.setOf_forall]
    refine ((isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun i =>
      isClosed_iInter fun j => (isClosed_le continuous_const (by fun_prop)).inter
        (isClosed_le (by fun_prop) continuous_const))).inter
      (((isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
        isClosed_iInter fun v => isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_iInter fun s => isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_eq (by fun_prop) continuous_const))
  have hKcomp : IsCompact K := isCompact_Icc.of_isClosed_subset hKc hKsub
  have hKconv : Convex ℝ K := by
    intro f hf g hg a b ha hb hab
    refine ⟨fun s t i j => ⟨?_, ?_⟩, fun s t hst v => ?_, fun s i j => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := (hf.1 s t i j).1; have := (hg.1 s t i j).1; positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left (hf.1 s t i j).2 ha
      have h2 := mul_le_mul_of_nonneg_left (hg.1 s t i j).2 hb
      have h3 : a * M + b * M = M := by rw [← add_mul, hab, one_mul]
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      have h1 := hf.2.1 s t hst v; have h2 := hg.2.1 s t hst v
      linear_combination a * h1 + b * h2 +
        (D s t * ((if v = s then 1 else 0) - (if v = t then 1 else 0))) * hab
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf.2.2 s i j, hg.2.2 s i j]; ring
  let ℓ : (V → V → V → V → ℝ) →ₗ[ℝ] (V → V → ℝ) :=
    { toFun := fun f i j => ∑ s, ∑ t, (f s t i j + f s t j i)
      map_add' := by
        intro f g; funext i j; simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun t _ => ?_; ring
      map_smul' := by
        intro c f; funext i j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_; ring }
  have hℓ : ∀ f i j, ℓ f i j = ∑ s, ∑ t, (f s t i j + f s t j i) := fun _ _ _ => rfl
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  set L := ℓ '' K with hLdef
  have hLcomp : IsCompact L := hKcomp.image hℓc
  have hLconv : Convex ℝ L := hKconv.linear_image ℓ
  let Q : Set (V → V → ℝ) := {q | ∀ i j, q i j ≤ N.C i j / lam}
  have hQc : IsClosed Q := by
    show IsClosed {q : V → V → ℝ | ∀ i j, _}
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
  have hQconv : Convex ℝ Q := by
    intro q hq r hr a b ha hb hab i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hq i j) ha
    have h2 := mul_le_mul_of_nonneg_left (hr i j) hb
    have h3 : a * (N.C i j / lam) + b * (N.C i j / lam) = N.C i j / lam := by
      rw [← add_mul, hab, one_mul]
    linarith
  have hdisj : Disjoint L Q := by
    rw [Set.disjoint_left]
    rintro _ ⟨f, hfK, rfl⟩ hQ
    apply hnot (fun s t i j => lam * f s t i j)
    refine ⟨fun s t i j => mul_nonneg hlam.le (hfK.1 s t i j).1, fun s t hst v => ?_,
      fun s i j => by simp [hfK.2.2 s i j], fun i j => ?_⟩
    · rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, hfK.2.1 s t hst v]; ring
    · have := hQ i j
      rw [hℓ] at this
      calc ∑ s, ∑ t, (lam * f s t i j + lam * f s t j i)
          = lam * ∑ s, ∑ t, (f s t i j + f s t j i) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun t _ => ?_; ring
        _ ≤ lam * (N.C i j / lam) := mul_le_mul_of_nonneg_left this hlam.le
        _ = N.C i j := by field_simp
  obtain ⟨φ, u, v, hφL, huv, hφQ⟩ :=
    geometric_hahn_banach_compact_closed hLconv hLcomp hQconv hQc hdisj
  let e : V → V → (V → V → ℝ) := fun i j a b => if a = i ∧ b = j then 1 else 0
  have hrep : ∀ q, φ q = ∑ i, ∑ j, q i j * φ (e i j) := by
    intro q
    have hq : q = ∑ i, ∑ j, q i j • e i j := by
      funext a b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, mul_ite, mul_one, mul_zero,
        ite_and]
      simp
    conv_lhs => rw [hq]
    simp only [map_sum, map_smul, smul_eq_mul]
  set y : V → V → ℝ := fun i j => - φ (e i j) with hydef
  set q0 : V → V → ℝ := fun i j => N.C i j / lam with hq0def
  have hq0 : q0 ∈ Q := fun i j => le_rfl
  have hy : ∀ i j, 0 ≤ y i j := by
    intro i j
    by_contra hneg; push_neg at hneg
    have hv0 := hφQ q0 hq0
    set τ := (φ q0 - v) / (- y i j) with hτ
    have hτ0 : 0 ≤ τ := div_nonneg (by linarith) (by linarith)
    have hmem : q0 - τ • e i j ∈ Q := by
      intro a b
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e, hq0def]
      split_ifs
      · linarith
      · simp
    have h1 := hφQ _ hmem
    rw [map_sub, map_smul, smul_eq_mul] at h1
    have h2 : τ * (- y i j) = φ q0 - v := by
      rw [hτ]; exact div_mul_cancel₀ _ (neg_ne_zero.mpr hneg.ne)
    have h3 : φ (e i j) = - y i j := by simp [hydef]
    rw [h3] at h1
    linarith
  have e1 : ∀ q : V → V → ℝ, ∑ i, ∑ j, q i j * φ (e i j) = - ∑ i, ∑ j, y i j * q i j := by
    intro q
    simp only [hydef, neg_mul, Finset.sum_neg_distrib, neg_neg]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hmain : ∀ f ∈ K, ∑ i, ∑ j, y i j * q0 i j < ∑ i, ∑ j, y i j * ℓ f i j := by
    intro f hf
    have h1 := hφL (ℓ f) ⟨f, hf, rfl⟩
    have h2 := hφQ q0 hq0
    rw [hrep, e1] at h1 h2
    linarith
  set d : V → V → ℝ := fun i j => y i j + y j i with hddef
  have hd : IsDistanceFunction d := ⟨fun i j => add_nonneg (hy i j) (hy j i), fun i j => add_comm _ _⟩
  have hW : totalWeight N d = lam * ∑ i, ∑ j, y i j * q0 i j := by
    have hs : ∑ i, ∑ j, N.C i j * y j i = ∑ i, ∑ j, N.C i j * y i j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [N.C_symm]
    have hq : ∑ i, ∑ j, y i j * q0 i j = (∑ i, ∑ j, N.C i j * y i j) / lam := by
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]; refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hq0def]; ring
    rw [totalWeight, hq]
    simp only [hddef, mul_add, Finset.sum_add_distrib, hs]
    field_simp; ring
  have hL : ∀ f, ∑ i, ∑ j, y i j * ℓ f i j = ∑ s, ∑ t, ∑ i, ∑ j, f s t i j * d i j := by
    intro f
    rw [lr_sum4_comm]
    set A : V → V → ℝ := fun i j => ∑ s, ∑ t, f s t i j with hA
    have hA' : ∀ i j, ℓ f i j = A i j + A j i := by
      intro i j; rw [hℓ]; simp only [hA, ← Finset.sum_add_distrib]
    have hR : ∀ i j, ∑ s, ∑ t, f s t i j * d i j = d i j * A i j := by
      intro i j; simp only [hA, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => mul_comm _ _
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hR i j]
    simp only [hA', hddef, mul_add, add_mul, Finset.sum_add_distrib]
    have : ∑ i, ∑ j, y i j * A j i = ∑ i, ∑ j, y j i * A i j := Finset.sum_comm
    linarith
  choose W hW1 hW2 using fun s t => lr_shortest_walk N hconn d hd s t
  let f0 : V → V → V → V → ℝ := fun s t i j => D s t * lrCnt N (W s t) i j
  have hf0K : f0 ∈ K := by
    refine ⟨fun s t i j => ⟨mul_nonneg (hD s t) (lr_cnt_nonneg _ _ _ _), ?_⟩, fun s t hst v => ?_,
      fun s i j => by simp [f0, hDdef, productDemand]⟩
    · refine le_trans (mul_le_mul_of_nonneg_left (le_trans (lr_cnt_le N (W s t) i j)
        (by exact_mod_cast hW2 s t)) (hD s t)) (hDM s t)
    · simp only [f0, ← Finset.mul_sum, ← mul_sub]
      rw [lr_cnt_cons_eq]
  have hval : ∑ s, ∑ t, ∑ i, ∑ j, f0 s t i j * d i j = ∑ s, ∑ t, D s t * dist N d s t := by
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [← hW1 s t, ← lr_cnt_len N d (W s t), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [f0]; ring
  have hlt := hmain f0 hf0K
  rw [hL, hval, lr_DX N π d hd] at hlt
  set Z := (1/2) * ∑ u, ∑ v, π u * π v * dist N d u v with hZ
  have hWnn : 0 ≤ totalWeight N d := by
    rw [totalWeight]
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      mul_nonneg (N.C_nonneg u v) (hd.1 u v)
  have hWlt : totalWeight N d < lam * Z := by rw [hW]; exact mul_lt_mul_of_pos_left hlt hlam
  have hZpos : 0 < Z := by nlinarith
  refine ⟨fun i j => (1/Z) * d i j,
    ⟨fun i j => mul_nonneg (by positivity) (hd.1 i j), fun i j => by show 1 / Z * d i j = 1 / Z * d j i; rw [hd.2]⟩, ?_, ?_⟩
  · unfold SatisfiesPMFPConstraint
    simp only [lr_dist_scale N d _ (by positivity : (0:ℝ) ≤ 1/Z)]
    have e : ∀ u v, π u * π v * ((1/Z) * dist N d u v) = (1/Z) * (π u * π v * dist N d u v) :=
      fun u v => by ring
    simp only [e, ← Finset.mul_sum]
    rw [show (1:ℝ)/2 * (1/Z * ∑ u, ∑ v, π u * π v * dist N d u v) =
      (1/Z) * ((1/2) * ∑ u, ∑ v, π u * π v * dist N d u v) by ring, ← hZ,
      one_div_mul_cancel hZpos.ne']
  · have : totalWeight N (fun i j => (1/Z) * d i j) = (1/Z) * totalWeight N d := by
      unfold totalWeight
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
    rw [this, one_div_mul_eq_div, div_lt_iff₀ hZpos]
    linarith

lemma lr_card_le_K (n : ℕ) (hn : 2 ≤ n) : n ≤ max (n.choose 2) 2 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · have : n = 2 := by omega
    subst this; simp
  · apply le_trans _ (le_max_left _ _)
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul_left n (by omega)

lemma lr_theorem7_aux (N : Network V) (π : V → ℝ) (hconn : IsConnectedNet N)
    (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) :
    (1/36) * pmfpMinCut N π / Real.logb 2 ((max (numCommodities π) 2 : ℕ) : ℝ) ≤
        maxFlow N (productDemand π) ∧
      maxFlow N (productDemand π) ≤ pmfpMinCut N π := by
  classical
  have hπ0 := hπ.1
  set Fset := {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N (productDemand π) f lam} with hF
  have h0F : (0:ℝ) ∈ Fset := ⟨le_rfl, _, lr_zero_flow N _⟩
  have hFne : Fset.Nonempty := ⟨0, h0F⟩
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ support π, ∃ y ∈ support π, x ≠ y :=
    Finset.one_lt_card.mp (by omega)
  have hxpos : 0 < π x := lt_of_le_of_ne (hπ0 x) (Ne.symm (Finset.mem_filter.mp hx).2)
  have hypos : 0 < π y := lt_of_le_of_ne (hπ0 y) (Ne.symm (Finset.mem_filter.mp hy).2)
  have hU0 : 0 < piSum π {x} ∧ 0 < piSum π ({x}ᶜ) := by
    refine ⟨by simp [piSum, hxpos], lt_of_lt_of_le hypos ?_⟩
    exact Finset.single_le_sum (f := π) (fun u _ => hπ0 u)
      (by simp [Ne.symm hxy] : y ∈ ({x}ᶜ : Finset V))
  haveI : Nonempty {U : Finset V // 0 < piSum π U ∧ 0 < piSum π Uᶜ} := ⟨⟨{x}, hU0⟩⟩
  have hbddι : BddBelow (Set.range fun U : {U : Finset V // 0 < piSum π U ∧ 0 < piSum π Uᶜ} =>
      weightedRatio N π U.1) := (Set.finite_range _).bddBelow
  have hratio_nn : ∀ U : {U : Finset V // 0 < piSum π U ∧ 0 < piSum π Uᶜ},
      0 ≤ weightedRatio N π U.1 := fun U =>
    div_nonneg (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => N.C_nonneg u v)
      (mul_pos U.2.1 U.2.2).le
  have hS0 : 0 ≤ pmfpMinCut N π := le_ciInf hratio_nn
  have hFle : ∀ lam ∈ Fset, ∀ U : {U : Finset V // 0 < piSum π U ∧ 0 < piSum π Uᶜ},
      lam ≤ weightedRatio N π U.1 := by
    rintro lam ⟨h0, f, hf⟩ U
    rw [weightedRatio, le_div_iff₀ (mul_pos U.2.1 U.2.2)]
    exact lr_cut_bound N hconn π hπ0 f lam hf h0 U.1
  have hFbdd : BddAbove Fset :=
    ⟨weightedRatio N π ({x} : Finset V), fun lam hl => hFle lam hl ⟨{x}, hU0⟩⟩
  have hupper : maxFlow N (productDemand π) ≤ pmfpMinCut N π := by
    apply csSup_le hFne
    intro lam hl
    exact le_ciInf (hFle lam hl)
  have hmf0 : 0 ≤ maxFlow N (productDemand π) := le_csSup hFbdd h0F
  refine ⟨?_, hupper⟩
  set p : ℝ := ((support π).card : ℝ) with hpdef
  have hp2 : (2:ℝ) ≤ p := by rw [hpdef]; exact_mod_cast hp
  have hlogp : 1 ≤ Real.logb 2 p := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]; exact hp2
  have hkey : ∀ lam, maxFlow N (productDemand π) < lam →
      pmfpMinCut N π ≤ 36 * Real.logb 2 p * lam := by
    intro lam hlam
    have hlam0 : 0 < lam := lt_of_le_of_lt hmf0 hlam
    have hnot : ∀ f, ¬ IsConcurrentFlow N (productDemand π) f lam := by
      intro f hf
      have : lam ≤ sSup Fset := le_csSup hFbdd ⟨hlam0.le, f, hf⟩
      have h2 : sSup Fset = maxFlow N (productDemand π) := rfl
      linarith
    obtain ⟨d, hd, hdc, hWd⟩ := lr_dual_approx N hconn π hπ0 lam hlam0 hnot
    obtain ⟨U, hU1, hU2, hU3⟩ := lemma_11_core N hconn π hπ hp d hd hdc
    calc pmfpMinCut N π ≤ weightedRatio N π U :=
          ciInf_le hbddι (⟨U, hU1, hU2⟩ : {U : Finset V // 0 < piSum π U ∧ 0 < piSum π Uᶜ})
      _ ≤ 36 * totalWeight N d * Real.logb 2 p := hU3
      _ ≤ 36 * lam * Real.logb 2 p := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          linarith
      _ = 36 * Real.logb 2 p * lam := by ring
  set A := 36 * Real.logb 2 p with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have hS : pmfpMinCut N π / A ≤ maxFlow N (productDemand π) := by
    by_contra hcon; push_neg at hcon
    set m := maxFlow N (productDemand π)
    set r := pmfpMinCut N π / A with hr
    have hAr : A * r = pmfpMinCut N π := by rw [hr]; field_simp
    have := hkey ((r + m) / 2) (by linarith)
    nlinarith [mul_lt_mul_of_pos_left hcon hApos]
  have hpK : p ≤ ((max (numCommodities π) 2 : ℕ) : ℝ) := by
    rw [hpdef]; exact_mod_cast lr_card_le_K _ hp
  have hlogK : Real.logb 2 p ≤ Real.logb 2 ((max (numCommodities π) 2 : ℕ) : ℝ) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) hpK
  calc (1/36) * pmfpMinCut N π / Real.logb 2 ((max (numCommodities π) 2 : ℕ) : ℝ)
      = pmfpMinCut N π / (36 * Real.logb 2 ((max (numCommodities π) 2 : ℕ) : ℝ)) := by ring
    _ ≤ pmfpMinCut N π / A := by
        apply div_le_div_of_nonneg_left hS0 hApos
        rw [hA]; linarith
    _ ≤ _ := hS

theorem theorem_7_core : ∃ c : ℝ, 0 < c ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (π : V → ℝ),
      IsConnectedNet N → IsPMFPWeight π → 2 ≤ (support π).card →
      c * pmfpMinCut N π / Real.logb 2 ((max (numCommodities π) 2 : ℕ) : ℝ) ≤
          maxFlow N (productDemand π) ∧
        maxFlow N (productDemand π) ≤ pmfpMinCut N π := by
  refine ⟨1/36, by norm_num, ?_⟩
  intro V _ _ N π hconn hπ hp
  exact lr_theorem7_aux N π hconn hπ hp

noncomputable def lrWS (N : Network V) (u v : V) : Finset (N.graph.Walk u v) := by
  classical exact (Finset.range (Fintype.card V)).biUnion (fun k => N.graph.finsetWalkLength k u v)

lemma lr_mem_WS (N : Network V) {u v : V} (q : N.graph.Walk u v) (hq : q.IsPath) :
    q ∈ lrWS N u v := by
  classical
  unfold lrWS
  simp only [Finset.mem_biUnion, Finset.mem_range]
  exact ⟨q.length, hq.length_lt, SimpleGraph.mem_finsetWalkLength_iff.mpr rfl⟩

lemma lr_WS_ne (N : Network V) (hconn : IsConnectedNet N) (u v : V) : (lrWS N u v).Nonempty :=
  ⟨_, lr_mem_WS N _ (Classical.choice (lr_conn N hconn u v)).bypass_isPath⟩

lemma lr_walkLen_bypass (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) {u v : V}
    (q : N.graph.Walk u v) : walkLen N d q.bypass ≤ walkLen N d q := by
  classical
  unfold walkLen
  apply ((SimpleGraph.Walk.darts_bypass_sublist_darts q).map _).sum_le_sum
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact hd.1 _ _

lemma lr_dist_eq_inf' (N : Network V) (hconn : IsConnectedNet N) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (u v : V) :
    dist N d u v = (lrWS N u v).inf' (lr_WS_ne N hconn u v) (fun w => walkLen N d w) := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ fun w _ => lr_dist_le N d hd w
  · haveI := lr_conn N hconn u v
    apply le_ciInf; intro q
    calc _ ≤ walkLen N d q.bypass := Finset.inf'_le _ (lr_mem_WS N _ q.bypass_isPath)
      _ ≤ walkLen N d q := lr_walkLen_bypass N d hd q

lemma lr_walkLen_cont (N : Network V) {u v : V} (w : N.graph.Walk u v) :
    Continuous fun d : V → V → ℝ => walkLen N d w := by
  have : (fun d : V → V → ℝ => walkLen N d w) = fun d => ∑ i, ∑ j, d i j * lrCnt N w i j := by
    funext d; rw [lr_cnt_len]
  rw [this]; fun_prop

noncomputable def lrProj (N : Network V) (d : V → V → ℝ) : V → V → ℝ :=
  fun i j => if 0 < N.C i j then d i j else 0

lemma lr_proj_walkLen (N : Network V) (d : V → V → ℝ) : ∀ {u v : V} (p : N.graph.Walk u v),
    walkLen N (lrProj N d) p = walkLen N d p := by
  intro u v p
  induction p with
  | nil => simp [lr_walkLen_nil]
  | @cons a b c h p ih =>
    rw [lr_walkLen_cons, lr_walkLen_cons, ih]
    have hC : 0 < N.C a b := by
      have h' := h
      unfold Network.graph at h'
      rw [SimpleGraph.fromRel_adj] at h'
      rcases h'.2 with h1 | h1
      · exact h1
      · rw [N.C_symm]; exact h1
    simp [lrProj, hC]

lemma lr_proj_dist (N : Network V) (d : V → V → ℝ) (u v : V) :
    dist N (lrProj N d) u v = dist N d u v := by
  unfold dist
  congr 1; funext p; exact lr_proj_walkLen N d p

lemma lr_proj_W (N : Network V) (d : V → V → ℝ) :
    totalWeight N (lrProj N d) = totalWeight N d := by
  unfold totalWeight lrProj
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · have : N.C i j = 0 := le_antisymm (not_lt.mp h) (N.C_nonneg i j)
    simp [this]

lemma lr_proj_isDist (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) :
    IsDistanceFunction (lrProj N d) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · unfold lrProj; split_ifs
    · exact hd.1 i j
    · exact le_rfl
  · unfold lrProj; rw [N.C_symm i j, hd.2 i j]

lemma lr_proj_bound (N : Network V) (d : V → V → ℝ) (hd : IsDistanceFunction d) (B0 : ℝ)
    (hW : totalWeight N d ≤ B0) (i j : V) :
    lrProj N d i j ≤ (if 0 < N.C i j then 2 * B0 / N.C i j else 0) := by
  unfold lrProj
  split_ifs with h
  · rw [le_div_iff₀ h]
    have hnn : ∀ a b, 0 ≤ N.C a b * d a b := fun a b => mul_nonneg (N.C_nonneg a b) (hd.1 a b)
    have h1 : N.C i j * d i j ≤ ∑ b, N.C i b * d i b :=
      Finset.single_le_sum (f := fun b => N.C i b * d i b) (fun b _ => hnn i b) (Finset.mem_univ j)
    have h2 : ∑ b, N.C i b * d i b ≤ ∑ a, ∑ b, N.C a b * d a b :=
      Finset.single_le_sum (f := fun a => ∑ b, N.C a b * d a b)
        (fun a _ => Finset.sum_nonneg fun b _ => hnn a b) (Finset.mem_univ i)
    unfold totalWeight at hW
    linarith
  · exact le_rfl

theorem lp_duality_core (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) :
    (∀ d : V → V → ℝ, IsDistanceFunction d → SatisfiesPMFPConstraint N π d →
        maxFlow N (productDemand π) ≤ totalWeight N d) ∧
    (∃ d : V → V → ℝ, IsDistanceFunction d ∧ SatisfiesPMFPConstraint N π d ∧
        totalWeight N d = maxFlow N (productDemand π)) := by
  refine ⟨lp_duality_part1 N π, ?_⟩
  classical
  have hπ0 := hπ.1
  set Fset := {lam : ℝ | 0 ≤ lam ∧ ∃ f, IsConcurrentFlow N (productDemand π) f lam} with hF
  have h0F : (0:ℝ) ∈ Fset := ⟨le_rfl, _, lr_zero_flow N _⟩
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ support π, ∃ y ∈ support π, x ≠ y :=
    Finset.one_lt_card.mp (by omega)
  have hxpos : 0 < π x := lt_of_le_of_ne (hπ0 x) (Ne.symm (Finset.mem_filter.mp hx).2)
  have hypos : 0 < π y := lt_of_le_of_ne (hπ0 y) (Ne.symm (Finset.mem_filter.mp hy).2)
  have hU0 : 0 < piSum π {x} ∧ 0 < piSum π ({x}ᶜ) := by
    refine ⟨by simp [piSum, hxpos], lt_of_lt_of_le hypos ?_⟩
    exact Finset.single_le_sum (f := π) (fun u _ => hπ0 u)
      (by simp [Ne.symm hxy] : y ∈ ({x}ᶜ : Finset V))
  have hFbdd : BddAbove Fset := by
    refine ⟨weightedRatio N π ({x} : Finset V), ?_⟩
    rintro lam ⟨h0, f, hf⟩
    rw [weightedRatio, le_div_iff₀ (mul_pos hU0.1 hU0.2)]
    exact lr_cut_bound N hconn π hπ0 f lam hf h0 {x}
  have hmf0 : 0 ≤ maxFlow N (productDemand π) := le_csSup hFbdd h0F
  set m := maxFlow N (productDemand π) with hm
  have hnot : ∀ lam, m < lam → ∀ f, ¬ IsConcurrentFlow N (productDemand π) f lam := by
    intro lam hlam f hf
    have : lam ≤ sSup Fset := le_csSup hFbdd ⟨by linarith, f, hf⟩
    have h2 : sSup Fset = m := rfl
    linarith
  set B0 := m + 1 with hB0
  set bnd : V → V → ℝ := fun i j => if 0 < N.C i j then 2 * B0 / N.C i j else 0 with hbnd
  let F : Set (V → V → ℝ) := {d | (0 ≤ d ∧ d ≤ bnd) ∧ (∀ i j, d i j = d j i) ∧
    1 ≤ (1/2) * ∑ u, ∑ v, π u * π v *
      (lrWS N u v).inf' (lr_WS_ne N hconn u v) (fun w => walkLen N d w)}
  have hFsub : F ⊆ Set.Icc 0 bnd := fun d hd => hd.1
  have hFc : IsClosed F := by
    show IsClosed (Set.Icc 0 bnd ∩ ({d : V → V → ℝ | ∀ i j, d i j = d j i} ∩
      {d | 1 ≤ (1/2) * ∑ u, ∑ v, π u * π v *
        (lrWS N u v).inf' (lr_WS_ne N hconn u v) (fun w => walkLen N d w)}))
    refine isClosed_Icc.inter (IsClosed.inter ?_ ?_)
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
    · apply isClosed_le continuous_const
      apply Continuous.mul continuous_const
      apply continuous_finset_sum _ fun u _ => continuous_finset_sum _ fun v _ => ?_
      apply Continuous.mul continuous_const
      exact Continuous.finset_inf'_apply _ fun w _ => lr_walkLen_cont N w
  have hFcomp : IsCompact F := isCompact_Icc.of_isClosed_subset hFc hFsub
  have hmemF : ∀ d, IsDistanceFunction d → SatisfiesPMFPConstraint N π d →
      totalWeight N d ≤ B0 → lrProj N d ∈ F := by
    intro d hd hc hW
    have hpd := lr_proj_isDist N d hd
    refine ⟨⟨fun i j => hpd.1 i j, fun i j => lr_proj_bound N d hd B0 hW i j⟩, hpd.2, ?_⟩
    have : ∀ u v, (lrWS N u v).inf' (lr_WS_ne N hconn u v)
        (fun w => walkLen N (lrProj N d) w) = dist N d u v := by
      intro u v; rw [← lr_dist_eq_inf' N hconn _ hpd, lr_proj_dist]
    simp only [this]; exact hc
  obtain ⟨d1, hd1, hc1, hW1⟩ := lr_dual_approx N hconn π hπ0 (m + 1) (by linarith)
    (hnot _ (by linarith))
  have hFne : F.Nonempty := ⟨_, hmemF d1 hd1 hc1 hW1.le⟩
  have hWc : Continuous fun d : V → V → ℝ => totalWeight N d := by unfold totalWeight; fun_prop
  obtain ⟨dstar, hdF, hmin⟩ := hFcomp.exists_isMinOn hFne hWc.continuousOn
  have hdstar : IsDistanceFunction dstar := ⟨fun i j => hdF.1.1 i j, hdF.2.1⟩
  have hcstar : SatisfiesPMFPConstraint N π dstar := by
    have h := hdF.2.2
    unfold SatisfiesPMFPConstraint
    have : ∀ u v, (lrWS N u v).inf' (lr_WS_ne N hconn u v)
        (fun w => walkLen N dstar w) = dist N dstar u v := by
      intro u v; rw [← lr_dist_eq_inf' N hconn _ hdstar]
    simp only [this] at h; exact h
  refine ⟨dstar, hdstar, hcstar, le_antisymm ?_ (lp_duality_part1 N π dstar hdstar hcstar)⟩
  by_contra hcon; push_neg at hcon
  set lam := min (totalWeight N dstar) (m + 1) with hlam
  have hlam1 : m < lam := lt_min hcon (by linarith)
  obtain ⟨d, hd, hc, hW⟩ := lr_dual_approx N hconn π hπ0 lam (by linarith) (hnot lam hlam1)
  have hWB : totalWeight N d ≤ B0 := le_trans hW.le (min_le_right _ _)
  have hmem := hmemF d hd hc hWB
  have := isMinOn_iff.mp hmin _ hmem
  rw [lr_proj_W] at this
  have := min_le_left (totalWeight N dstar) (m + 1)
  linarith

end LeightonRao.Product

open LeightonRao.Product


theorem solution {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) :
    (∀ d : V → V → ℝ, IsDistanceFunction d → SatisfiesPMFPConstraint N π d →
        maxFlow N (productDemand π) ≤ totalWeight N d) ∧
    (∃ d : V → V → ℝ, IsDistanceFunction d ∧ SatisfiesPMFPConstraint N π d ∧
        totalWeight N d = maxFlow N (productDemand π)) := by
  exact lp_duality_core N hconn π hπ hp
