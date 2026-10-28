-- Prove2me | solution 1 for LowerFareFirst.Critical.theorem2_critical_values_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T09:54:28.597243+00:00
-- url     : https://prove2.me/submissions/07001f51-d99a-4676-b622-1d9291bb7fa3

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

set_option autoImplicit false

namespace LFF2da

open MeasureTheory LowerFareFirst.Critical

/-- The inner maximum of the recursion for `Z`. -/
noncomputable def G (h : ℕ → ℝ) (a : ℝ) (d n : ℕ) : ℝ :=
  (Finset.range (min d n + 1)).sup' Finset.nonempty_range_add_one
    (fun x => a * (x : ℝ) + h (n - x))

lemma le_G {h : ℕ → ℝ} {a : ℝ} {d n x : ℕ} (hx : x ≤ min d n) :
    a * (x : ℝ) + h (n - x) ≤ G h a d n :=
  Finset.le_sup' (fun x : ℕ => a * (x : ℝ) + h (n - x)) (Finset.mem_range.2 (by omega))

lemma G_le {h : ℕ → ℝ} {a B : ℝ} {d n : ℕ}
    (H : ∀ x, x ≤ min d n → a * (x : ℝ) + h (n - x) ≤ B) : G h a d n ≤ B := by
  unfold G
  exact Finset.sup'_le _ _ (fun x hx => H x (by have := Finset.mem_range.1 hx; omega))

lemma G_eq_some (h : ℕ → ℝ) (a : ℝ) (d n : ℕ) :
    ∃ x, x ≤ min d n ∧ G h a d n = a * (x : ℝ) + h (n - x) := by
  obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_add_one (n := min d n))
    (fun x => a * (x : ℝ) + h (n - x))
  exact ⟨x, by have := Finset.mem_range.1 hx; omega, he⟩

lemma G_zero (h : ℕ → ℝ) (a : ℝ) (d : ℕ) : G h a d 0 = h 0 := by
  apply le_antisymm
  · apply G_le
    intro x hx
    have : x = 0 := by omega
    subst this
    simp
  · have := le_G (h := h) (a := a) (d := d) (n := 0) (x := 0) (by omega)
    simpa using this

/-- Discrete concavity: increments are nonincreasing. -/
def Conc (h : ℕ → ℝ) : Prop := ∀ n, h (n + 2) - h (n + 1) ≤ h (n + 1) - h n

lemma inc_anti {h : ℕ → ℝ} (hc : Conc h) {a b : ℕ} (hab : a ≤ b) :
    h (b + 1) - h b ≤ h (a + 1) - h a :=
  (antitone_nat_of_succ_le (f := fun n => h (n + 1) - h n) (fun n => hc n)) hab

lemma G_conc {h : ℕ → ℝ} (hc : Conc h) (a : ℝ) (d n : ℕ) :
    G h a d (n + 2) + G h a d n ≤ 2 * G h a d (n + 1) := by
  obtain ⟨x1, hx1, e1⟩ := G_eq_some h a d (n + 2)
  obtain ⟨x2, hx2, e2⟩ := G_eq_some h a d n
  rw [e1, e2]
  rcases Nat.lt_or_ge x2 x1 with hlt | hge
  · have l1 := le_G (h := h) (a := a) (d := d) (n := n + 1) (x := x1 - 1) (by omega)
    have l2 := le_G (h := h) (a := a) (d := d) (n := n + 1) (x := x2 + 1) (by omega)
    have q1 : n + 1 - (x1 - 1) = n + 2 - x1 := by omega
    have q2 : n + 1 - (x2 + 1) = n - x2 := by omega
    rw [q1] at l1
    rw [q2] at l2
    have c1 : ((x1 - 1 : ℕ) : ℝ) = (x1 : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [c1] at l1
    push_cast at l2
    linarith
  · have l1 := le_G (h := h) (a := a) (d := d) (n := n + 1) (x := x1) (by omega)
    have l2 := le_G (h := h) (a := a) (d := d) (n := n + 1) (x := x2) (by omega)
    have key := inc_anti hc (a := n - x2) (b := n + 1 - x1) (by omega)
    have q1 : n + 1 - x1 + 1 = n + 2 - x1 := by omega
    have q2 : n - x2 + 1 = n + 1 - x2 := by omega
    rw [q1, q2] at key
    linarith

section measure

variable {Ω : Type*} [MeasurableSpace Ω]

lemma Z_succ (μ : Measure Ω) (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (m n : ℕ) :
    Z μ D r (m + 1) n = ∫ ω, G (Z μ D r m) (r (m + 1)) (D (m + 1) ω) n ∂μ := by
  rw [Z]; rfl

lemma G_bound (h : ℕ → ℝ) (a : ℝ) (d n : ℕ) :
    |G h a d n| ≤ ∑ x ∈ Finset.range (n + 1), |a * (x : ℝ) + h (n - x)| := by
  obtain ⟨x, hx, e⟩ := G_eq_some h a d n
  rw [e]
  exact Finset.single_le_sum (f := fun x : ℕ => |a * (x : ℝ) + h (n - x)|)
    (fun i _ => abs_nonneg _) (Finset.mem_range.2 (by omega))

lemma G_int {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℕ} (hX : Measurable X)
    (h : ℕ → ℝ) (a : ℝ) (n : ℕ) : Integrable (fun ω => G h a (X ω) n) μ := by
  refine Integrable.of_bound
    ((measurable_from_nat (f := fun d => G h a d n)).comp hX).aestronglyMeasurable
    (∑ x ∈ Finset.range (n + 1), |a * (x : ℝ) + h (n - x)|) ?_
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs]; exact G_bound _ _ _ _)

lemma ms_lt {X : Ω → ℕ} (hX : Measurable X) (N : ℕ) : MeasurableSet {ω | N < X ω} :=
  measurableSet_lt measurable_const hX

lemma ms_le {X : Ω → ℕ} (hX : Measurable X) (N : ℕ) : MeasurableSet {ω | X ω ≤ N} :=
  measurableSet_le hX measurable_const

lemma ms_ge {X : Ω → ℕ} (hX : Measurable X) (N : ℕ) : MeasurableSet {ω | N ≤ X ω} :=
  measurableSet_le measurable_const hX

lemma ind_int {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s) (c : ℝ) :
    Integrable (fun ω => c * s.indicator (1 : Ω → ℝ) ω) μ :=
  ((integrable_const (1 : ℝ)).indicator hs).const_mul c

lemma int_ind {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    (K c : ℝ) : ∫ ω, (K + c * s.indicator 1 ω) ∂μ = K + c * μ.real s := by
  rw [integral_add (integrable_const K) (ind_int hs c),
    integral_const_mul]
  have : ∫ ω, s.indicator (1 : Ω → ℝ) ω ∂μ = μ.real s := integral_indicator_one hs
  rw [this]
  simp

lemma tail_small {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℕ} (hX : Measurable X)
    {δ : ℝ} (hδ : 0 < δ) : ∃ N : ℕ, μ.real {ω | N < X ω} ≤ δ := by
  have hanti : Antitone (fun N : ℕ => {ω | N < X ω}) :=
    fun a b hab ω hω => lt_of_le_of_lt hab hω
  have hinter : (⋂ N : ℕ, {ω | N < X ω}) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_lt]
    exact ⟨X ω, le_refl _⟩
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun N => (ms_lt hX N).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
  rw [hinter, measure_empty] at ht
  have hev := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))
  obtain ⟨N, hN⟩ := hev.exists
  exact ⟨N, ENNReal.toReal_le_of_le_ofReal hδ.le hN.le⟩

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {D : ℕ → Ω → ℕ} {r : ℕ → ℝ}

lemma Z_zero (hD : ∀ m, Measurable (D m)) : ∀ m, Z μ D r m 0 = 0 := by
  intro m
  induction m with
  | zero => simp [Z]
  | succ m ih => rw [Z_succ]; simp [G_zero, ih]

lemma Z_mono_m (hD : ∀ m, Measurable (D m)) (m n : ℕ) : Z μ D r m n ≤ Z μ D r (m + 1) n := by
  rw [Z_succ]
  have := integral_mono (μ := μ) (integrable_const (Z μ D r m n)) (G_int (hD (m + 1)) _ _ _)
    (fun ω => by
      simpa using le_G (h := Z μ D r m) (a := r (m + 1)) (d := D (m + 1) ω) (n := n) (x := 0)
        (by omega))
  simpa using this

lemma Z_conc (hD : ∀ m, Measurable (D m)) : ∀ m, Conc (Z μ D r m) := by
  intro m
  induction m with
  | zero => intro n; simp [Z]
  | succ m ih =>
    intro n
    simp only [Z_succ]
    have hi : ∫ ω, (G (Z μ D r m) (r (m + 1)) (D (m + 1) ω) (n + 2)
          + G (Z μ D r m) (r (m + 1)) (D (m + 1) ω) n) ∂μ
        ≤ ∫ ω, 2 * G (Z μ D r m) (r (m + 1)) (D (m + 1) ω) (n + 1) ∂μ :=
      integral_mono ((G_int (hD _) _ _ _).add (G_int (hD _) _ _ _))
        ((G_int (hD _) _ _ _).const_mul 2) (fun ω => G_conc ih _ _ _)
    rw [integral_add (G_int (hD _) _ _ _) (G_int (hD _) _ _ _), integral_const_mul] at hi
    linarith

lemma Z_ub (hD : ∀ m, Measurable (D m)) (R δ : ℝ) (M J : ℕ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ)
    (hr : ∀ i, 1 ≤ i → i ≤ J → r i ≤ R)
    (hδ : ∀ i, 1 ≤ i → i ≤ J → μ.real {ω | M < D i ω} ≤ δ) :
    ∀ j, j ≤ J → ∀ n : ℕ, Z μ D r j n ≤ j * (R * M + R * n * δ) := by
  intro j
  induction j with
  | zero => intro _ n; simp [Z]
  | succ j ih =>
    intro hj n
    rw [Z_succ]
    have hs := ms_lt (hD (j + 1)) M
    have hpt : ∀ ω, G (Z μ D r j) (r (j + 1)) (D (j + 1) ω) n ≤
        (R * M + j * (R * M + R * n * δ)) + (R * n) * {ω | M < D (j + 1) ω}.indicator 1 ω := by
      intro ω
      apply G_le
      intro x hx
      have h1 := ih (by omega) (n - x)
      have h2 : ((n - x : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n x
      have h3 : r (j + 1) * x ≤ R * x :=
        mul_le_mul_of_nonneg_right (hr (j + 1) (by omega) hj) (Nat.cast_nonneg x)
      have h4 : (j : ℝ) * (R * ((n - x : ℕ) : ℝ) * δ) ≤ j * (R * n * δ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hR) hδ0) (Nat.cast_nonneg j)
      have hRM : 0 ≤ R * M := mul_nonneg hR (Nat.cast_nonneg _)
      by_cases hd : M < D (j + 1) ω
      · have hind : {ω | M < D (j + 1) ω}.indicator (1 : Ω → ℝ) ω = 1 :=
          Set.indicator_of_mem (s := {ω | M < D (j + 1) ω}) (by exact hd) _
        rw [hind]
        have hxn : (x : ℝ) ≤ n := by exact_mod_cast (by omega : x ≤ n)
        have : R * x ≤ R * n := mul_le_mul_of_nonneg_left hxn hR
        push_cast
        nlinarith
      · have hind : {ω | M < D (j + 1) ω}.indicator (1 : Ω → ℝ) ω = 0 :=
          Set.indicator_of_notMem (s := {ω | M < D (j + 1) ω}) (by exact hd) _
        rw [hind]
        have hxM : (x : ℝ) ≤ M := by exact_mod_cast (by omega : x ≤ M)
        have : R * x ≤ R * M := mul_le_mul_of_nonneg_left hxM hR
        push_cast
        nlinarith
    have hi := integral_mono (μ := μ) (G_int (hD (j + 1)) _ _ n)
      ((integrable_const _).add (ind_int hs (R * n))) hpt
    have := int_ind (μ := μ) hs (R * M + j * (R * M + R * n * δ)) (R * n)
    have hd := hδ (j + 1) (by omega) hj
    have hRn : 0 ≤ R * n := mul_nonneg hR (Nat.cast_nonneg _)
    have : R * n * μ.real {ω | M < D (j + 1) ω} ≤ R * n * δ := mul_le_mul_of_nonneg_left hd hRn
    push_cast
    simp only [Pi.add_apply] at hi
    nlinarith

end measure

/-! Pure optimality lemmas. -/

lemma phi_up {h : ℕ → ℝ} {a : ℝ} {k : ℕ} (H : ∀ y, y < k → a < h (y + 1) - h y) :
    ∀ b, b ≤ k → ∀ x, x < b → h x - a * x < h b - a * b := by
  intro b
  induction b with
  | zero => intro _ x hx; omega
  | succ b ih =>
    intro hb x hx
    have step := H b (by omega)
    push_cast
    rcases Nat.lt_or_ge x b with hlt | hge
    · have := ih (by omega) x hlt; linarith
    · have : x = b := by omega
      subst this; linarith

lemma phi_down {h : ℕ → ℝ} {a : ℝ} {k : ℕ} (H : ∀ y, k ≤ y → h (y + 1) - h y ≤ a) :
    ∀ b x, k ≤ x → x ≤ b → h b - a * b ≤ h x - a * x := by
  intro b
  induction b with
  | zero =>
    intro x _ hx
    have : x = 0 := by omega
    subst this; exact le_refl _
  | succ b ih =>
    intro x hkx hx
    rcases Nat.lt_or_ge x (b + 1) with hlt | hge
    · have := ih x hkx (by omega)
      have := H b (by omega)
      push_cast; linarith
    · have : x = b + 1 := by omega
      subst this; exact le_refl _

lemma opt {h : ℕ → ℝ} {a : ℝ} {k : ℕ} (H1 : ∀ y, y < k → a < h (y + 1) - h y)
    (H2 : ∀ y, k ≤ y → h (y + 1) - h y ≤ a) (n d x : ℕ) (hx : x ≤ min d n) :
    a * (x : ℝ) + h (n - x) ≤ a * ((min d (n - k) : ℕ) : ℝ) + h (n - min d (n - k)) ∧
    (n - k < x → a * (x : ℝ) + h (n - x) < a * ((min d (n - k) : ℕ) : ℝ) + h (n - min d (n - k))) := by
  have hxsn : min d (n - k) ≤ n := by omega
  have hxn : x ≤ n := by omega
  have e1 : (x : ℝ) = (n : ℝ) - ((n - x : ℕ) : ℝ) := by rw [Nat.cast_sub hxn]; ring
  have e2 : ((min d (n - k) : ℕ) : ℝ) = (n : ℝ) - ((n - min d (n - k) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hxsn]; ring
  rw [e1, e2]
  have key : ∀ u v : ℕ, h u - a * u ≤ h v - a * v →
      a * ((n : ℝ) - u) + h u ≤ a * ((n : ℝ) - v) + h v := by
    intro u v huv; linarith
  have keys : ∀ u v : ℕ, h u - a * u < h v - a * v →
      a * ((n : ℝ) - u) + h u < a * ((n : ℝ) - v) + h v := by
    intro u v huv; linarith
  constructor
  · apply key
    rcases (by omega : n - x = n - min d (n - k) ∨
        (n - x < n - min d (n - k) ∧ n - min d (n - k) ≤ k) ∨
        (k ≤ n - min d (n - k) ∧ n - min d (n - k) ≤ n - x)) with h0 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h0]
    · exact (phi_up H1 _ h2 _ h1).le
    · exact phi_down H2 _ _ h1 h2
  · intro hlt
    apply keys
    exact phi_up H1 _ (by omega) _ (by omega)

lemma G_opt {h : ℕ → ℝ} {a : ℝ} {k : ℕ} (H1 : ∀ y, y < k → a < h (y + 1) - h y)
    (H2 : ∀ y, k ≤ y → h (y + 1) - h y ≤ a) (d n : ℕ) :
    G h a d n = a * ((min d (n - k) : ℕ) : ℝ) + h (n - min d (n - k)) :=
  le_antisymm (G_le (fun x hx => (opt H1 H2 n d x hx).1)) (le_G (by omega))

lemma tele (h : ℕ → ℝ) (a : ℝ) (T d : ℕ) : ∀ j, j ≤ T →
    ∑ i ∈ Finset.range j, ((h (T - i) - h (T - i - 1)) * (if d ≤ i then (1 : ℝ) else 0)
      + a * (if i + 1 ≤ d then (1 : ℝ) else 0))
      = a * ((min d j : ℕ) : ℝ) + h (T - min d j) - h (T - j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    rw [Finset.sum_range_succ, ih (by omega)]
    have e3 : T - (j + 1) = T - j - 1 := by omega
    rcases Nat.lt_or_ge j d with hjd | hjd
    · have e1 : min d j = j := by omega
      have e2 : min d (j + 1) = j + 1 := by omega
      rw [e1, e2, if_neg (show ¬ (d ≤ j) by omega), if_pos (show j + 1 ≤ d by omega), e3]
      push_cast; ring
    · have e1 : min d j = d := by omega
      have e2 : min d (j + 1) = d := by omega
      rw [e1, e2, if_pos (show d ≤ j by omega), if_neg (show ¬ (j + 1 ≤ d) by omega), e3]
      ring

end LFF2da

open LFF2da in
open MeasureTheory LowerFareFirst.Critical in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ)
    (hM : IsSeatModel μ D r c) :
    (∀ m : ℕ, 1 ≤ m → m ≤ c → ∀ n : ℕ, 1 ≤ n → dZ μ D r m (n + 1) ≤ dZ μ D r m n) ∧
      (∀ m : ℕ, 2 ≤ m → m ≤ c → ∃ k : ℕ, IsCriticalValue μ D r m k ∧
        (∀ j : ℕ, 1 ≤ j → Z μ D r m (k + j) =
          Z μ D r m k + ∑ i ∈ Finset.range j,
            (dZ μ D r (m - 1) (k + j - i) * probLe μ D m i + r m * probGe μ D m (i + 1))) ∧
        (∀ n : ℕ, n ≤ k → Z μ D r m n = Z μ D r (m - 1) n) ∧
        CriticalRuleOptimal μ D r m k) := by
  have := hM.isProb
  have hD := hM.meas
  -- antitone increments of every `Z m`
  have hconc := Z_conc (μ := μ) (r := r) hD
  have dZ_anti : ∀ m u v : ℕ, 1 ≤ u → u ≤ v → dZ μ D r m v ≤ dZ μ D r m u := by
    intro m u v hu huv
    have := inc_anti (hconc m) (a := u - 1) (b := v - 1) (by omega)
    have e1 : u - 1 + 1 = u := by omega
    have e2 : v - 1 + 1 = v := by omega
    rw [e1, e2] at this
    exact this
  refine ⟨?_, ?_⟩
  · intro m _ _ n hn
    exact dZ_anti m n (n + 1) hn (by omega)
  · intro m hm2 hmc
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hp : 1 ≤ p := by omega
    -- fares
    have fare_anti : ∀ i j, 1 ≤ i → i ≤ j → j ≤ c → r j ≤ r i := by
      intro i j hi hij hjc
      induction j, hij using Nat.le_induction with
      | base => exact le_refl _
      | succ j hij ih =>
        exact le_trans (hM.fare_strictAnti j (by omega) (by omega)).le (ih (by omega))
    have ha : 0 < r (p + 1) := lt_of_lt_of_le hM.fare_pos (fare_anti (p + 1) c (by omega) hmc le_rfl)
    have hR : 0 < r 1 := lt_of_lt_of_le ha (fare_anti 1 (p + 1) le_rfl (by omega) hmc)
    set a := r (p + 1) with ha_def
    set h := Z μ D r p with hh
    -- the set of (2b)
    set S := {n : ℕ | 1 ≤ n ∧ a < dZ μ D r p n} with hS
    -- nonempty: 1 ∈ S
    have hZ11 : r 1 * probGe μ D 1 1 ≤ Z μ D r 1 1 := by
      have hs := ms_ge (hD 1) 1
      have hpt : ∀ ω, (0 : ℝ) + r 1 * {ω | 1 ≤ D 1 ω}.indicator 1 ω ≤
          G (Z μ D r 0) (r (0 + 1)) (D (0 + 1) ω) 1 := by
        intro ω
        by_cases hd : 1 ≤ D 1 ω
        · rw [Set.indicator_of_mem (s := {ω | 1 ≤ D 1 ω}) (by exact hd)]
          have := le_G (h := Z μ D r 0) (a := r (0 + 1)) (d := D (0 + 1) ω) (n := 1) (x := 1)
            (by simp; omega)
          simpa [Z] using this
        · rw [Set.indicator_of_notMem (s := {ω | 1 ≤ D 1 ω}) (by exact hd)]
          have := le_G (h := Z μ D r 0) (a := r (0 + 1)) (d := D (0 + 1) ω) (n := 1) (x := 0)
            (by omega)
          simpa [Z] using this
      have hi : ∫ ω, ((0 : ℝ) + r 1 * {ω | 1 ≤ D 1 ω}.indicator 1 ω) ∂μ ≤
          ∫ ω, G (Z μ D r 0) (r (0 + 1)) (D (0 + 1) ω) 1 ∂μ := integral_mono (μ := μ)
        ((integrable_const (0 : ℝ)).add (ind_int hs (r 1)))
        (G_int (hD (0 + 1)) _ _ 1) hpt
      rw [int_ind hs] at hi
      have : Z μ D r 1 1 = Z μ D r (0 + 1) 1 := rfl
      rw [this, Z_succ]
      unfold probGe
      linarith
    have hZmono : ∀ q, 1 ≤ q → Z μ D r 1 1 ≤ Z μ D r q 1 := by
      intro q hq
      induction q, hq using Nat.le_induction with
      | base => exact le_refl _
      | succ q hq ih => exact le_trans ih (Z_mono_m hD q 1)
    have h1S : 1 ∈ S := by
      refine ⟨le_rfl, ?_⟩
      have e : dZ μ D r p 1 = Z μ D r p 1 := by
        unfold dZ; simp [Z_zero hD]
      rw [e]
      have := hM.two_class
      have := fare_anti 2 (p + 1) (by omega) (by omega) hmc
      have := hZmono p hp
      linarith
    -- bounded
    have hbdd : BddAbove S := by
      set R := r 1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
      set δ := a / (2 * (p * R)) with hδ_def
      have hδ : 0 < δ := by positivity
      have hpRδ : (p : ℝ) * R * δ = a / 2 := by
        rw [hδ_def]; field_simp
      choose N hN using fun i => tail_small (μ := μ) (hD i) hδ
      set M := ∑ i ∈ Finset.range (p + 1), N i
      have hNM : ∀ i, i ≤ p → N i ≤ M := fun i hi =>
        Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
      have hub := Z_ub (μ := μ) (D := D) (r := r) hD R δ M p hR.le hδ.le
        (fun i hi hip => fare_anti 1 i le_rfl hi (by omega))
        (fun i hi hip => le_trans (measureReal_mono (fun ω hω => lt_of_le_of_lt
          (by exact_mod_cast hNM i hip) hω)) (hN i)) p le_rfl
      set X := 2 * p * R * M / a with hX
      have hXa : X * a = 2 * p * R * M := by rw [hX]; field_simp
      set n0 := ⌈X⌉₊ + 1
      have hn0 : X < n0 := by
        have := Nat.le_ceil X
        push_cast [n0]; linarith
      have hex : ∃ y, 1 ≤ y ∧ y ≤ n0 ∧ dZ μ D r p y ≤ a := by
        by_contra hcon
        push_neg at hcon
        have low : ∀ n, n ≤ n0 → a * n ≤ Z μ D r p n := by
          intro n
          induction n with
          | zero => intro _; simp [Z_zero hD]
          | succ n ih =>
            intro hn
            have h1 := ih (by omega)
            have h2 := hcon (n + 1) (by omega) hn
            unfold dZ at h2
            simp only [Nat.add_sub_cancel] at h2
            push_cast
            linarith
        have l := low n0 le_rfl
        have u := hub n0
        have := mul_lt_mul_of_pos_right hn0 ha
        nlinarith
      obtain ⟨y, hy1, -, hy⟩ := hex
      refine ⟨y, fun s hs => ?_⟩
      by_contra hlt
      push_neg at hlt
      have := dZ_anti p y s hy1 hlt.le
      have := hs.2
      linarith
    obtain ⟨k, hk⟩ : ∃ k, IsGreatest S k := ⟨sSup S, Nat.sSup_mem ⟨1, h1S⟩ hbdd,
      fun x hx => le_csSup hbdd hx⟩
    have hk1 : 1 ≤ k := hk.1.1
    have H1 : ∀ y, y < k → a < h (y + 1) - h y := by
      intro y hy
      have := inc_anti (hconc p) (a := y) (b := k - 1) (by omega)
      have e : k - 1 + 1 = k := by omega
      rw [e] at this
      have h2 := hk.1.2
      unfold dZ at h2
      linarith
    have H2 : ∀ y, k ≤ y → h (y + 1) - h y ≤ a := by
      intro y hy
      by_contra hcon
      push_neg at hcon
      have hmem : y + 1 ∈ S := by
        refine ⟨by omega, ?_⟩
        unfold dZ; simp only [Nat.add_sub_cancel]; exact hcon
      have := hk.2 hmem
      omega
    have hZ : ∀ n, Z μ D r (p + 1) n =
        ∫ ω, (a * ((min (D (p + 1) ω) (n - k) : ℕ) : ℝ) + h (n - min (D (p + 1) ω) (n - k))) ∂μ := by
      intro n
      rw [Z_succ]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => G_opt H1 H2 _ _))
    have hlow : ∀ n, n ≤ k → Z μ D r (p + 1) n = Z μ D r p n := by
      intro n hn
      rw [hZ]
      have e : n - k = 0 := by omega
      simp [e, hh]
    refine ⟨k, ?_, ?_, hlow, ?_⟩
    · exact hk
    · intro j _
      rw [hlow k le_rfl, hZ]
      have hpt : ∀ ω, a * ((min (D (p + 1) ω) (k + j - k) : ℕ) : ℝ)
            + h (k + j - min (D (p + 1) ω) (k + j - k))
          = h k + ∑ i ∈ Finset.range j, (dZ μ D r p (k + j - i)
              * ({ω | D (p + 1) ω ≤ i}.indicator 1 ω)
              + a * ({ω | i + 1 ≤ D (p + 1) ω}.indicator 1 ω)) := by
        intro ω
        have t := tele h a (k + j) (D (p + 1) ω) j (by omega)
        have e : k + j - k = j := by omega
        have e2 : k + j - j = k := by omega
        rw [e2] at t
        rw [e]
        simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
        unfold dZ
        rw [← hh]
        linarith
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      have hint : ∀ i, Integrable (fun ω => dZ μ D r p (k + j - i)
              * ({ω | D (p + 1) ω ≤ i}.indicator 1 ω)
              + a * ({ω | i + 1 ≤ D (p + 1) ω}.indicator 1 ω)) μ := fun i =>
        (ind_int (ms_le (hD (p + 1)) i) _).add (ind_int (ms_ge (hD (p + 1)) (i + 1)) _)
      rw [integral_add (integrable_const _) (integrable_finset_sum _ (fun i _ => hint i)),
        integral_finset_sum _ (fun i _ => hint i)]
      have hc : ∫ _ω, h k ∂μ = h k := by simp
      rw [hc]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_add (ind_int (ms_le (hD (p + 1)) i) _) (ind_int (ms_ge (hD (p + 1)) (i + 1)) _),
        integral_const_mul, integral_const_mul, integral_indicator_one (ms_le (hD (p + 1)) i),
        integral_indicator_one (ms_ge (hD (p + 1)) (i + 1))]
      rfl
    · intro n d x hx
      exact opt H1 H2 n d x hx
