-- Prove2me | solution 1 for LyonsPeres.isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T13:12:41.601987+00:00
-- url     : https://prove2.me/submissions/cdce50b1-4d63-4fd2-a22c-f3634b79cf1f

import Mathlib
import Definitions.Def_IntervalExchange

section

/-!
# Lyons–Peres, Theorem 2.17: rough embeddings transfer transience

Route: transience at `a` gives a bounded truncated Green function, hence a one-sided Hardy
inequality `f a ≤ (2 t G + E(f)/t)/4` for finitely supported `f`. If the target network were
recurrent at `φ a`, its truncated Green densities `u'_M` have energy `≤ 2 u'_M(φ a)` with
`u'_M(φ a)` unbounded; pulling back along `φ` (Cauchy–Schwarz along the paths `Φ`, each target
edge used at most `β` times) and truncating to a finite set gives test functions contradicting
the Hardy inequality.
-/

open IntervalExchange

namespace LyonsPeres.IETLP

open Classical

/-! ## Summation helpers -/

section Sums

variable {V W : Type*}

lemma prod_summable {F : V → W → ℝ} (h0 : ∀ x y, 0 ≤ F x y) (h1 : ∀ x, Summable (F x))
    (h2 : Summable fun x => ∑' y, F x y) : Summable (fun q : V × W => F q.1 q.2) :=
  (summable_prod_of_nonneg (f := fun q : V × W => F q.1 q.2) (fun q => h0 q.1 q.2)).2 ⟨h1, h2⟩

lemma dom_summable {ι : Type*} {F G : ι → ℝ} (hF : Summable F) (h : ∀ q, |G q| ≤ F q) :
    Summable G :=
  Summable.of_norm_bounded hF (fun q => by rw [Real.norm_eq_abs]; exact h q)

lemma swap_summable {G : V × W → ℝ} (h : Summable G) : Summable (fun q : W × V => G q.swap) :=
  (Equiv.prodComm W V).summable_iff.2 h

lemma tsum_swap_eq (G : V × W → ℝ) : ∑' q : W × V, G q.swap = ∑' q, G q :=
  (Equiv.prodComm W V).tsum_eq G

lemma col_summable {G : V → W → ℝ} (h : Summable (fun q : V × W => G q.1 q.2)) :
    Summable fun y => ∑' x, G x y :=
  (swap_summable h).prod

lemma tsum_comm_of {G : V → W → ℝ} (h : Summable (fun q : V × W => G q.1 q.2)) :
    ∑' x, ∑' y, G x y = ∑' y, ∑' x, G x y :=
  (Summable.tsum_comm (f := G) h).symm

lemma FS_summable {f : V → ℝ} (hf : (Function.support f).Finite) : Summable f :=
  summable_of_ne_finset_zero (s := hf.toFinset) (fun x hx => by simpa using hx)

end Sums

/-! ## Networks and their walks -/

section Net

variable {V : Type*} {c : V → V → ℝ}

/-- The total conductance at `x`. -/
noncomputable def pi (c : V → V → ℝ) (x : V) : ℝ := ∑' z, c x z

lemma nw_eq (x y : V) : networkWalk c x y = c x y / pi c x := rfl

lemma c_nn (hc : IsNetwork c) (x y : V) : 0 ≤ c x y := hc.1 x y
lemma c_sym (hc : IsNetwork c) (x y : V) : c x y = c y x := hc.2.1 x y
lemma c_sum (hc : IsNetwork c) (x : V) : Summable (c x) := hc.2.2.2.1 x

lemma c_le_pi (hc : IsNetwork c) (x y : V) : c x y ≤ pi c x :=
  (c_sum hc x).le_tsum y (fun j _ => c_nn hc x j)

lemma pi_pos (hc : IsNetwork c) (x : V) : 0 < pi c x := by
  obtain ⟨y, hy⟩ := hc.2.2.1 x
  exact lt_of_lt_of_le hy (c_le_pi hc x y)

lemma P_nn (hc : IsNetwork c) (x y : V) : 0 ≤ networkWalk c x y :=
  div_nonneg (c_nn hc x y) (pi_pos hc x).le

lemma P_le (hc : IsNetwork c) (x y : V) : networkWalk c x y ≤ 1 := by
  rw [nw_eq, div_le_one (pi_pos hc x)]; exact c_le_pi hc x y

lemma P_sum (hc : IsNetwork c) (x : V) : Summable (networkWalk c x) :=
  (c_sum hc x).div_const _

lemma P_tsum (hc : IsNetwork c) (x : V) : ∑' y, networkWalk c x y = 1 := by
  simp_rw [nw_eq]; rw [tsum_div_const]; exact div_self (pi_pos hc x).ne'

/-- The transition operator acting on measures. -/
noncomputable def T (c : V → V → ℝ) (f : V → ℝ) (y : V) : ℝ := ∑' x, f x * networkWalk c x y

lemma T_row (hc : IsNetwork c) {f : V → ℝ} (hf : Summable f) (y : V) :
    Summable fun x => f x * networkWalk c x y :=
  dom_summable hf.abs fun x => by
    rw [abs_mul, abs_of_nonneg (P_nn hc x y)]
    exact mul_le_of_le_one_right (abs_nonneg _) (P_le hc x y)

lemma T_prod (hc : IsNetwork c) {f : V → ℝ} (hf : Summable f) :
    Summable (fun q : V × V => f q.1 * networkWalk c q.1 q.2) := by
  have hF := prod_summable (F := fun x y => |f x| * networkWalk c x y)
    (fun x y => mul_nonneg (abs_nonneg _) (P_nn hc x y)) (fun x => (P_sum hc x).mul_left _)
    (by simp_rw [tsum_mul_left, P_tsum hc, mul_one]; exact hf.abs)
  exact dom_summable hF fun q => by rw [abs_mul, abs_of_nonneg (P_nn hc _ _)]

lemma T_summable (hc : IsNetwork c) {f : V → ℝ} (hf : Summable f) : Summable (T c f) :=
  col_summable (G := fun x y => f x * networkWalk c x y) (T_prod hc hf)

lemma T_tsum (hc : IsNetwork c) {f : V → ℝ} (hf : Summable f) : ∑' y, T c f y = ∑' x, f x := by
  unfold T
  rw [← tsum_comm_of (G := fun x y => f x * networkWalk c x y) (T_prod hc hf)]
  simp_rw [tsum_mul_left, P_tsum hc, mul_one]

lemma T_add (hc : IsNetwork c) {f g : V → ℝ} (hf : Summable f) (hg : Summable g) (y : V) :
    T c (fun x => f x + g x) y = T c f y + T c g y := by
  unfold T; simp_rw [add_mul]; exact (T_row hc hf y).tsum_add (T_row hc hg y)

lemma T_smul (r : ℝ) (f : V → ℝ) (y : V) : T c (fun x => r * f x) y = r * T c f y := by
  unfold T; simp_rw [mul_assoc]; exact tsum_mul_left

lemma T_sum (hc : IsNetwork c) {ι : Type*} (s : Finset ι) (F : ι → V → ℝ)
    (hF : ∀ i, Summable (F i)) (y : V) :
    T c (fun x => ∑ i ∈ s, F i x) y = ∑ i ∈ s, T c (F i) y := by
  unfold T; simp_rw [Finset.sum_mul]; exact Summable.tsum_finsetSum fun i _ => T_row hc (hF i) y

lemma T_nn (hc : IsNetwork c) {f : V → ℝ} (hf : ∀ x, 0 ≤ f x) (y : V) : 0 ≤ T c f y :=
  tsum_nonneg fun x => mul_nonneg (hf x) (P_nn hc x y)

lemma T_delta (o y : V) : T c (fun z => if z = o then 1 else 0) y = networkWalk c o y := by
  unfold T; simp only [ite_mul, one_mul, zero_mul]; exact tsum_ite_eq o _

/-! ### Laws, killed laws, first returns -/

/-- The law of the walk at time `n`, started at `o`. -/
noncomputable def p (c : V → V → ℝ) (o : V) : ℕ → V → ℝ
  | 0 => fun z => if z = o then 1 else 0
  | n + 1 => T c (p c o n)

/-- The law at time `n` of the walk killed at its first return to `o`. -/
noncomputable def ak (c : V → V → ℝ) (o : V) : ℕ → V → ℝ
  | 0 => fun z => if z = o then 1 else 0
  | n + 1 => fun z => if z = o then 0 else T c (ak c o n) z

noncomputable def fr (c : V → V → ℝ) (o : V) (n : ℕ) : ℝ := T c (ak c o n) o

noncomputable def green (c : V → V → ℝ) (o : V) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, p c o n o

lemma p_summable (hc : IsNetwork c) (o : V) : ∀ n, Summable (p c o n)
  | 0 => (hasSum_ite_eq o (1 : ℝ)).summable
  | n + 1 => T_summable hc (p_summable hc o n)

lemma p_nn (hc : IsNetwork c) (o : V) : ∀ n z, 0 ≤ p c o n z
  | 0, z => by simp only [p]; split_ifs <;> norm_num
  | n + 1, z => T_nn hc (p_nn hc o n) z

lemma ak_nn (hc : IsNetwork c) (o : V) : ∀ n z, 0 ≤ ak c o n z
  | 0, z => by simp only [ak]; split_ifs <;> norm_num
  | n + 1, z => by
    simp only [ak]; split_ifs
    · exact le_rfl
    · exact T_nn hc (ak_nn hc o n) z

lemma ak_summable (hc : IsNetwork c) (o : V) : ∀ n, Summable (ak c o n)
  | 0 => (hasSum_ite_eq o (1 : ℝ)).summable
  | n + 1 => Summable.of_nonneg_of_le (ak_nn hc o (n + 1)) (fun z => by
      simp only [ak]; split_ifs
      · exact T_nn hc (ak_nn hc o n) z
      · exact le_rfl) (T_summable hc (ak_summable hc o n))

lemma fr_nn (hc : IsNetwork c) (o : V) (n : ℕ) : 0 ≤ fr c o n := T_nn hc (ak_nn hc o n) o

lemma avoidProb_eq (o : V) (n : ℕ) :
    avoidProb (networkWalk c) o (n + 1) = ak c o (n + 1) := by
  induction n with
  | zero =>
    funext y
    simp only [avoidProb, ak]
    rw [T_delta]
  | succ n ih =>
    funext y
    simp only [avoidProb]
    rw [ih]
    rfl

lemma firstReturnProb_eq (o : V) (n : ℕ) :
    firstReturnProb (networkWalk c) o n = fr c o n := by
  cases n with
  | zero =>
    simp only [firstReturnProb, fr, ak]
    rw [T_delta]
  | succ n =>
    simp only [firstReturnProb, fr]
    rw [avoidProb_eq]
    rfl

lemma fr_partial (hc : IsNetwork c) (o : V) (n : ℕ) :
    ∑ k ∈ Finset.range n, fr c o k + ∑' z, ak c o n z = 1 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, ak]
    exact tsum_ite_eq o (fun _ => (1 : ℝ))
  | succ n ih =>
    have hs := T_summable hc (ak_summable hc o n)
    have e : ∑' z, ak c o (n + 1) z = ∑' z, ak c o n z - fr c o n := by
      rw [← T_tsum hc (ak_summable hc o n), hs.tsum_eq_add_tsum_ite o]
      simp only [ak, fr]
      ring
    rw [Finset.sum_range_succ, e]
    linarith

lemma fr_sum_le (hc : IsNetwork c) (o : V) (n : ℕ) : ∑ k ∈ Finset.range n, fr c o k ≤ 1 := by
  have := fr_partial hc o n
  have : 0 ≤ ∑' z, ak c o n z := tsum_nonneg (ak_nn hc o n)
  linarith

lemma fr_summable (hc : IsNetwork c) (o : V) : Summable (fr c o) :=
  summable_of_sum_range_le (fr_nn hc o) (fr_sum_le hc o)

lemma renewal (hc : IsNetwork c) (o : V) (n : ℕ) (z : V) :
    p c o (n + 1) z = ak c o (n + 1) z +
      ∑ k ∈ Finset.range (n + 1), fr c o k * p c o (n - k) z := by
  induction n generalizing z with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero]
    show T c (p c o 0) z = (if z = o then 0 else T c (ak c o 0) z) + T c (ak c o 0) o * p c o 0 z
    have h0 : ak c o 0 = p c o 0 := rfl
    rw [h0]
    by_cases hz : z = o
    · subst hz; simp [p]
    · simp [p, hz]
  | succ n ih =>
    have hfun : p c o (n + 1) = fun w => ak c o (n + 1) w +
        ∑ k ∈ Finset.range (n + 1), fr c o k * p c o (n - k) w := funext ih
    have step : p c o (n + 2) z = T c (ak c o (n + 1)) z +
        ∑ k ∈ Finset.range (n + 1), fr c o k * p c o (n + 1 - k) z := by
      show T c (p c o (n + 1)) z = _
      rw [hfun, T_add hc (ak_summable hc o (n + 1))
        (summable_sum fun k _ => (p_summable hc o (n - k)).mul_left _),
        T_sum hc _ _ (fun k => (p_summable hc o (n - k)).mul_left _)]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < n + 1 := Finset.mem_range.1 hk
      rw [T_smul, show n + 1 - k = (n - k) + 1 by omega]
      rfl
    rw [step, Finset.sum_range_succ _ (n + 1), Nat.sub_self]
    by_cases hz : z = o
    · subst hz
      simp only [ak, p, fr, if_true]
      ring
    · simp only [ak, p, hz, if_false]
      ring

lemma green_succ (hc : IsNetwork c) (o : V) (N : ℕ) :
    green c o (N + 1) = 1 + ∑ k ∈ Finset.range N, fr c o k * green c o (N - k) := by
  unfold green
  rw [Finset.sum_range_succ']
  have h0 : p c o 0 o = 1 := by simp [p]
  rw [h0, add_comm]
  congr 1
  have : ∀ n, p c o (n + 1) o = ∑ k ∈ Finset.range (n + 1), fr c o k * p c o (n - k) o := by
    intro n
    rw [renewal hc]
    simp [ak]
  simp_rw [this]
  rw [Finset.sum_range_diag_flip N (fun k m => fr c o k * p c o m o)]
  simp_rw [Finset.mul_sum]

lemma green_nn (hc : IsNetwork c) (o : V) (N : ℕ) : 0 ≤ green c o N :=
  Finset.sum_nonneg fun n _ => p_nn hc o n o

lemma green_mono (hc : IsNetwork c) (o : V) : Monotone (green c o) := by
  refine monotone_nat_of_le_succ fun N => ?_
  unfold green
  rw [Finset.sum_range_succ]
  linarith [p_nn hc o N o]

lemma green_bdd (hc : IsNetwork c) (o : V) (hF : ∑' k, fr c o k < 1) (N : ℕ) :
    green c o N ≤ 1 / (1 - ∑' k, fr c o k) := by
  set F := ∑' k, fr c o k
  set M := 1 / (1 - F)
  have hne : 1 - F ≠ 0 := by linarith
  have hM : 1 + F * M = M := by
    simp only [M]; field_simp; ring
  have hM0 : 0 ≤ M := by simp only [M]; exact div_nonneg zero_le_one (by linarith)
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    cases N with
    | zero => simp [green, hM0]
    | succ N =>
      rw [green_succ hc]
      have h1 : ∑ k ∈ Finset.range N, fr c o k * green c o (N - k) ≤
          ∑ k ∈ Finset.range N, fr c o k * M :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (ih _ (by omega)) (fr_nn hc o k)
      have h2 : ∑ k ∈ Finset.range N, fr c o k ≤ F :=
        (fr_summable hc o).sum_le_tsum _ (fun k _ => fr_nn hc o k)
      rw [← Finset.sum_mul] at h1
      nlinarith

lemma not_bdd (hc : IsNetwork c) (o : V) (hrec : HasSum (fr c o) 1) (M : ℝ)
    (hM : ∀ N, green c o N ≤ M) : False := by
  have hbdd : BddAbove (Set.range fun N => green c o N) := ⟨M, by rintro _ ⟨N, rfl⟩; exact hM N⟩
  set S := ⨆ N, green c o N
  have hle : ∀ N, green c o N ≤ S := fun N => le_ciSup hbdd N
  have hS1 : 1 ≤ S := by
    have := hle 1
    simp [green, p] at this
    exact this
  have hK : ∀ K, 1 + (∑ k ∈ Finset.range K, fr c o k) * S ≤ S := by
    intro K
    set FK := ∑ k ∈ Finset.range K, fr c o k
    have hFK : 0 ≤ FK := Finset.sum_nonneg fun k _ => fr_nn hc o k
    have hJ : ∀ J, FK * green c o J ≤ S - 1 := by
      intro J
      have e := green_succ hc o (J + K)
      have h1 : FK * green c o J ≤ ∑ k ∈ Finset.range K, fr c o k * green c o (J + K - k) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
          (green_mono hc o (by have := Finset.mem_range.1 hk; omega)) (fr_nn hc o k)
      have h2 : ∑ k ∈ Finset.range K, fr c o k * green c o (J + K - k) ≤
          ∑ k ∈ Finset.range (J + K), fr c o k * green c o (J + K - k) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun k _ _ => mul_nonneg (fr_nn hc o k) (green_nn hc o _))
      have h3 := hle (J + K + 1)
      linarith
    have : FK * S ≤ S - 1 := by
      rw [Real.mul_iSup_of_nonneg hFK]
      exact ciSup_le hJ
    linarith
  have ht : Filter.Tendsto (fun K => 1 + (∑ k ∈ Finset.range K, fr c o k) * S) Filter.atTop
      (nhds (1 + 1 * S)) :=
    tendsto_const_nhds.add (hrec.tendsto_sum_nat.mul tendsto_const_nhds)
  have := le_of_tendsto' ht hK
  linarith

lemma bdd_of_not_rec (hc : IsNetwork c) (o : V) (h : ¬ IsRecurrentChain (networkWalk c) o) :
    ∃ G, ∀ N, green c o N ≤ G := by
  unfold IsRecurrentChain at h
  have efr : firstReturnProb (networkWalk c) o = fr c o := funext (firstReturnProb_eq o)
  rw [efr] at h
  have hle1 : ∑' k, fr c o k ≤ 1 :=
    Real.tsum_le_of_sum_range_le (fr_nn hc o) (fr_sum_le hc o)
  have hlt : ∑' k, fr c o k < 1 := by
    rcases hle1.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (h' ▸ (fr_summable hc o).hasSum) h
  exact ⟨_, green_bdd hc o hlt⟩

lemma not_bdd_of_rec (hc : IsNetwork c) (o : V) (h : IsRecurrentChain (networkWalk c) o)
    (M : ℝ) (hM : ∀ N, green c o N ≤ M) : False := by
  unfold IsRecurrentChain at h
  have efr : firstReturnProb (networkWalk c) o = fr c o := funext (firstReturnProb_eq o)
  rw [efr] at h
  exact not_bdd hc o h M hM


/-! ### Green densities and the energy identity -/

/-- The density of the law at time `n` with respect to `π`. -/
noncomputable def d (c : V → V → ℝ) (o : V) (n : ℕ) (x : V) : ℝ := p c o n x / pi c x

/-- The truncated Green density. -/
noncomputable def u (c : V → V → ℝ) (o : V) (N : ℕ) (x : V) : ℝ :=
  ∑ n ∈ Finset.range N, d c o n x

lemma pd (hc : IsNetwork c) (o : V) (n : ℕ) (x : V) : pi c x * d c o n x = p c o n x := by
  unfold d; field_simp [(pi_pos hc x).ne']

lemma cd_eq (hc : IsNetwork c) (o : V) (n : ℕ) (x : V) :
    (Summable fun y => c x y * d c o n y) ∧ ∑' y, c x y * d c o n y = p c o (n + 1) x := by
  have e : (fun y => c x y * d c o n y) = fun y => p c o n y * networkWalk c y x := by
    funext y; unfold d; rw [nw_eq, c_sym hc x y]; ring
  rw [e]; exact ⟨T_row hc (p_summable hc o n) x, rfl⟩

lemma d_nn (hc : IsNetwork c) (o : V) (n : ℕ) (x : V) : 0 ≤ d c o n x :=
  div_nonneg (p_nn hc o n x) (pi_pos hc x).le

lemma d_le (hc : IsNetwork c) (o : V) : ∀ n x, d c o n x ≤ 1 / pi c o
  | 0, x => by
    unfold d; simp only [p]; split_ifs with h
    · subst h; exact le_rfl
    · rw [zero_div]; exact (one_div_pos.2 (pi_pos hc o)).le
  | n + 1, x => by
    have hx := pi_pos hc x
    show p c o (n + 1) x / pi c x ≤ _
    rw [← (cd_eq hc o n x).2, div_le_iff₀ hx]
    calc ∑' y, c x y * d c o n y ≤ ∑' y, c x y * (1 / pi c o) :=
          Summable.tsum_le_tsum (fun y => mul_le_mul_of_nonneg_left (d_le hc o n y) (c_nn hc x y))
            (cd_eq hc o n x).1 ((c_sum hc x).mul_right _)
      _ = 1 / pi c o * pi c x := by rw [tsum_mul_right]; unfold pi; ring

lemma u_nn (hc : IsNetwork c) (o : V) (N : ℕ) (x : V) : 0 ≤ u c o N x :=
  Finset.sum_nonneg fun n _ => d_nn hc o n x

lemma u_le (hc : IsNetwork c) (o : V) (N : ℕ) (x : V) : u c o N x ≤ N * (1 / pi c o) := by
  unfold u
  calc ∑ n ∈ Finset.range N, d c o n x ≤ ∑ n ∈ Finset.range N, 1 / pi c o :=
        Finset.sum_le_sum fun n _ => d_le hc o n x
    _ = N * (1 / pi c o) := by simp

lemma pi_u (hc : IsNetwork c) (o : V) (N : ℕ) (x : V) :
    pi c x * u c o N x = ∑ n ∈ Finset.range N, p c o n x := by
  unfold u; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => pd hc o n x

lemma pu_summable (hc : IsNetwork c) (o : V) (N : ℕ) :
    Summable (fun x => pi c x * u c o N x) := by
  simp_rw [pi_u hc]; exact summable_sum fun n _ => p_summable hc o n

lemma green_eq (hc : IsNetwork c) (o : V) (N : ℕ) : green c o N = pi c o * u c o N o := by
  rw [pi_u hc]; rfl

lemma cu (hc : IsNetwork c) (o : V) (N : ℕ) (x : V) :
    (Summable fun y => c x y * u c o N y) ∧
      ∑' y, c x y * u c o N y = ∑ n ∈ Finset.range N, p c o (n + 1) x := by
  unfold u
  simp_rw [Finset.mul_sum]
  refine ⟨summable_sum fun n _ => (cd_eq hc o n x).1, ?_⟩
  rw [Summable.tsum_finsetSum fun n _ => (cd_eq hc o n x).1]
  exact Finset.sum_congr rfl fun n _ => (cd_eq hc o n x).2

lemma dom1 {ι : Type*} {f g : ι → ℝ} (hg : Summable g) (H : ℝ) (hf : ∀ x, |f x| ≤ H)
    (hg0 : ∀ x, 0 ≤ g x) : Summable fun x => f x * g x :=
  dom_summable (hg.mul_left H) fun x => by
    rw [abs_mul, abs_of_nonneg (hg0 x)]; exact mul_le_mul_of_nonneg_right (hf x) (hg0 x)

/-- Summation by parts against the truncated Green density. -/
lemma ibp (hc : IsNetwork c) (o : V) (N : ℕ) (h : V → ℝ) (H : ℝ) (hH : ∀ x, |h x| ≤ H) :
    Summable (fun q : V × V => c q.1 q.2 * (u c o N q.1 - u c o N q.2) * (h q.1 - h q.2)) ∧
    ∑' q : V × V, c q.1 q.2 * (u c o N q.1 - u c o N q.2) * (h q.1 - h q.2) =
      2 * (h o - ∑' x, h x * p c o N x) := by
  set U := u c o N with hUdef
  have B1 : Summable (fun q : V × V => c q.1 q.2 * U q.1) :=
    prod_summable (F := fun x y => c x y * U x)
      (fun x y => mul_nonneg (c_nn hc x y) (u_nn hc o N x))
      (fun x => (c_sum hc x).mul_right _) (by simp_rw [tsum_mul_right]; exact pu_summable hc o N)
  have B2 : Summable (fun q : V × V => c q.1 q.2 * U q.2) := by
    refine (swap_summable B1).congr fun q => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]; rw [c_sym hc]
  set A : V × V → ℝ := fun q => c q.1 q.2 * (U q.1 - U q.2) * h q.1 with hA
  have SA : Summable A := dom_summable ((B1.add B2).mul_left H) fun q => by
    simp only [A]
    rw [abs_mul, abs_mul, abs_of_nonneg (c_nn hc _ _)]
    have h1 := u_nn hc o N q.1
    have h2 := u_nn hc o N q.2
    have hΔ : |U q.1 - U q.2| ≤ U q.1 + U q.2 := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    have hc0 := c_nn hc q.1 q.2
    calc c q.1 q.2 * |U q.1 - U q.2| * |h q.1| ≤ c q.1 q.2 * (U q.1 + U q.2) * H :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΔ hc0) (hH _) (abs_nonneg _)
            (mul_nonneg hc0 (by linarith))
      _ = H * (c q.1 q.2 * U q.1 + c q.1 q.2 * U q.2) := by ring
  have SAs : Summable (fun q : V × V => A q.swap) := swap_summable SA
  have term : ∀ q : V × V, c q.1 q.2 * (U q.1 - U q.2) * (h q.1 - h q.2) = A q + A q.swap := by
    intro q; simp only [A, Prod.fst_swap, Prod.snd_swap]; rw [c_sym hc q.2 q.1]; ring
  refine ⟨(SA.add SAs).congr fun q => (term q).symm, ?_⟩
  simp_rw [term]
  rw [SA.tsum_add SAs, tsum_swap_eq A, SA.tsum_prod]
  have inner : ∀ x, ∑' y, A (x, y) = h x * (p c o 0 x - p c o N x) := by
    intro x
    have e : (fun y => A (x, y)) = fun y => h x * (c x y * U x - c x y * U y) := by
      funext y; simp only [A]; ring
    rw [e, tsum_mul_left, Summable.tsum_sub ((c_sum hc x).mul_right _) (cu hc o N x).1,
      tsum_mul_right, (cu hc o N x).2]
    have : (∑' y, c x y) * U x = ∑ n ∈ Finset.range N, p c o n x := pi_u hc o N x
    rw [this, ← Finset.sum_sub_distrib, Finset.sum_range_sub' (fun n => p c o n x)]
  simp_rw [inner, mul_sub]
  have hb : ∀ n, Summable fun x => h x * p c o n x :=
    fun n => dom1 (p_summable hc o n) H hH (p_nn hc o n)
  rw [Summable.tsum_sub (hb 0) (hb N)]
  have : ∑' x, h x * p c o 0 x = h o := by
    simp only [p, mul_ite, mul_one, mul_zero]; exact tsum_ite_eq o h
  rw [this]; ring

lemma energy_u (hc : IsNetwork c) (o : V) (N : ℕ) :
    Summable (fun q : V × V => c q.1 q.2 * (u c o N q.1 - u c o N q.2) ^ 2) ∧
    ∑' q : V × V, c q.1 q.2 * (u c o N q.1 - u c o N q.2) ^ 2 ≤ 2 * u c o N o := by
  have hH : ∀ x, |u c o N x| ≤ N * (1 / pi c o) := fun x => by
    rw [abs_of_nonneg (u_nn hc o N x)]; exact u_le hc o N x
  obtain ⟨hs, he⟩ := ibp hc o N (u c o N) _ hH
  have eq : (fun q : V × V => c q.1 q.2 * (u c o N q.1 - u c o N q.2) ^ 2) =
      fun q => c q.1 q.2 * (u c o N q.1 - u c o N q.2) * (u c o N q.1 - u c o N q.2) := by
    funext q; ring
  rw [eq]
  refine ⟨hs, ?_⟩
  rw [he]
  have : 0 ≤ ∑' x, u c o N x * p c o N x :=
    tsum_nonneg fun x => mul_nonneg (u_nn hc o N x) (p_nn hc o N x)
  linarith

/-! ### `p_N → 0` pointwise under transience -/

lemma ip_d (hc : IsNetwork c) (o : V) : ∀ m n,
    ∑' y, pi c y * d c o m y * d c o n y = d c o (m + n) o
  | 0, n => by
    simp_rw [pd hc o 0]
    simp only [p, ite_mul, one_mul, zero_mul, zero_add]
    exact tsum_ite_eq o _
  | m + 1, n => by
    simp_rw [pd hc o (m + 1)]
    have hS : Summable (fun q : V × V => c q.1 q.2 * d c o m q.2 * d c o n q.1) := by
      have hF := prod_summable (F := fun y x => c y x * d c o n y * (1 / pi c o))
        (fun y x => mul_nonneg (mul_nonneg (c_nn hc y x) (d_nn hc o n y))
          (one_div_pos.2 (pi_pos hc o)).le)
        (fun y => ((c_sum hc y).mul_right _).mul_right _)
        (by
          simp_rw [tsum_mul_right]
          have : Summable fun y => pi c y * d c o n y * (1 / pi c o) := by
            simp_rw [pd hc o n]; exact (p_summable hc o n).mul_right _
          exact this)
      refine dom_summable hF fun q => ?_
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (c_nn hc _ _) (d_nn hc o m _)) (d_nn hc o n _))]
      have := d_le hc o m q.2
      have h0 := mul_nonneg (c_nn hc q.1 q.2) (d_nn hc o n q.1)
      calc c q.1 q.2 * d c o m q.2 * d c o n q.1 = c q.1 q.2 * d c o n q.1 * d c o m q.2 := by ring
        _ ≤ c q.1 q.2 * d c o n q.1 * (1 / pi c o) := mul_le_mul_of_nonneg_left this h0
    calc ∑' y, p c o (m + 1) y * d c o n y
        = ∑' y, ∑' x, c y x * d c o m x * d c o n y := by
          refine tsum_congr fun y => ?_
          rw [← (cd_eq hc o m y).2, ← tsum_mul_right]
      _ = ∑' x, ∑' y, c y x * d c o m x * d c o n y :=
          tsum_comm_of (G := fun y x => c y x * d c o m x * d c o n y) hS
      _ = ∑' x, d c o m x * p c o (n + 1) x := by
          refine tsum_congr fun x => ?_
          rw [← (cd_eq hc o n x).2, ← tsum_mul_left]
          refine tsum_congr fun y => ?_
          rw [c_sym hc y x]; ring
      _ = ∑' x, pi c x * d c o m x * d c o (n + 1) x := by
          refine tsum_congr fun x => ?_
          rw [← pd hc o (n + 1) x]; ring
      _ = d c o (m + 1 + n) o := by rw [ip_d hc o m (n + 1)]; congr 1; omega

lemma p_tendsto (hc : IsNetwork c) (o : V) (G : ℝ) (hG : ∀ N, green c o N ≤ G) (x : V) :
    Filter.Tendsto (fun N => p c o N x) Filter.atTop (nhds 0) := by
  have hsum : Summable fun n => p c o n o :=
    summable_of_sum_range_le (fun n => p_nn hc o n o) hG
  have hlim : Filter.Tendsto (fun N => p c o (N + N) o / pi c o) Filter.atTop (nhds 0) := by
    have := (hsum.tendsto_atTop_zero.comp (f := fun N : ℕ => N + N)
      (Filter.tendsto_atTop_mono (fun n => Nat.le_add_right n n) Filter.tendsto_id)).div_const
        (pi c o)
    simpa using this
  have hx := pi_pos hc x
  have hbound : ∀ N, p c o N x ≤ Real.sqrt (pi c x * (p c o (N + N) o / pi c o)) := by
    intro N
    have hS : Summable fun y => pi c y * d c o N y * d c o N y := by
      refine Summable.of_nonneg_of_le (fun y => mul_nonneg (mul_nonneg (pi_pos hc y).le
        (d_nn hc o N y)) (d_nn hc o N y)) (fun y => ?_) ((p_summable hc o N).mul_right (1 / pi c o))
      rw [pd hc o N y]
      exact mul_le_mul_of_nonneg_left (d_le hc o N y) (p_nn hc o N y)
    have h1 : pi c x * d c o N x * d c o N x ≤ d c o (N + N) o := by
      rw [← ip_d hc o N N]
      exact hS.le_tsum x (fun y _ => mul_nonneg (mul_nonneg (pi_pos hc y).le
        (d_nn hc o N y)) (d_nn hc o N y))
    have h2 : p c o N x ^ 2 ≤ pi c x * (p c o (N + N) o / pi c o) := by
      rw [← pd hc o N x]
      have : d c o (N + N) o = p c o (N + N) o / pi c o := rfl
      rw [← this]
      nlinarith
    calc p c o N x = Real.sqrt (p c o N x ^ 2) := (Real.sqrt_sq (p_nn hc o N x)).symm
      _ ≤ _ := Real.sqrt_le_sqrt h2
  have hlim2 : Filter.Tendsto (fun N => Real.sqrt (pi c x * (p c o (N + N) o / pi c o)))
      Filter.atTop (nhds 0) := by
    have := ((hlim.const_mul (pi c x)).sqrt)
    simpa using this
  exact squeeze_zero (fun N => p_nn hc o N x) hbound hlim2

/-! ### The one-sided Hardy inequality -/

lemma hardy (hc : IsNetwork c) (o : V) (G : ℝ) (hG : ∀ N, green c o N ≤ G) (f : V → ℝ)
    (hf : (Function.support f).Finite) (t : ℝ) (ht : 0 < t) :
    f o ≤ (2 * t * (G / pi c o) + (∑' q : V × V, c q.1 q.2 * (f q.1 - f q.2) ^ 2) / t) / 4 := by
  -- bound and energy of `f`
  set H := ∑ x ∈ hf.toFinset, |f x|
  have hH : ∀ x, |f x| ≤ H := by
    intro x
    by_cases hx : x ∈ hf.toFinset
    · exact Finset.single_le_sum (f := fun x => |f x|) (fun _ _ => abs_nonneg _) hx
    · have : f x = 0 := by simpa using hx
      rw [this, abs_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have C1 : Summable (fun q : V × V => c q.1 q.2 * f q.1 ^ 2) := by
    refine prod_summable (F := fun x y => c x y * f x ^ 2)
      (fun x y => mul_nonneg (c_nn hc x y) (sq_nonneg _))
      (fun x => (c_sum hc x).mul_right _) ?_
    simp_rw [tsum_mul_right]
    refine FS_summable (hf.subset fun x hx => ?_)
    intro h0; apply hx; show (∑' y, c x y) * f x ^ 2 = 0; rw [h0]; ring
  have C2 : Summable (fun q : V × V => c q.1 q.2 * f q.2 ^ 2) := by
    refine (swap_summable C1).congr fun q => ?_
    simp only [Prod.fst_swap, Prod.snd_swap]; rw [c_sym hc]
  have Ef : Summable (fun q : V × V => c q.1 q.2 * (f q.1 - f q.2) ^ 2) := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg (c_nn hc _ _) (sq_nonneg _))
      (fun q => ?_) ((C1.add C2).mul_left 2)
    have hc0 := c_nn hc q.1 q.2
    have : (f q.1 - f q.2) ^ 2 ≤ 2 * (f q.1 ^ 2 + f q.2 ^ 2) := by
      nlinarith [sq_nonneg (f q.1 + f q.2)]
    calc c q.1 q.2 * (f q.1 - f q.2) ^ 2 ≤ c q.1 q.2 * (2 * (f q.1 ^ 2 + f q.2 ^ 2)) :=
          mul_le_mul_of_nonneg_left this hc0
      _ = 2 * (c q.1 q.2 * f q.1 ^ 2 + c q.1 q.2 * f q.2 ^ 2) := by ring
  set EF := ∑' q : V × V, c q.1 q.2 * (f q.1 - f q.2) ^ 2
  have hN : ∀ N, f o ≤ ∑' x, f x * p c o N x + (2 * t * (G / pi c o) + EF / t) / 4 := by
    intro N
    obtain ⟨sU, eU⟩ := energy_u hc o N
    obtain ⟨sUf, eUf⟩ := ibp hc o N f H hH
    have hUo : u c o N o ≤ G / pi c o := by
      rw [le_div_iff₀ (pi_pos hc o), mul_comm, ← green_eq hc]; exact hG N
    set U := u c o N
    have key : ∀ q : V × V, c q.1 q.2 * (U q.1 - U q.2) * (f q.1 - f q.2) ≤
        (t * (c q.1 q.2 * (U q.1 - U q.2) ^ 2) + c q.1 q.2 * (f q.1 - f q.2) ^ 2 / t) / 2 := by
      intro q
      set a := U q.1 - U q.2
      set b := f q.1 - f q.2
      have hab : a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
        have e : (t * a ^ 2 + b ^ 2 / t) / 2 - a * b = (t * a - b) ^ 2 / (2 * t) := by
          field_simp; ring
        have : 0 ≤ (t * a - b) ^ 2 / (2 * t) := by positivity
        linarith
      have hc0 := c_nn hc q.1 q.2
      calc c q.1 q.2 * a * b = c q.1 q.2 * (a * b) := by ring
        _ ≤ c q.1 q.2 * ((t * a ^ 2 + b ^ 2 / t) / 2) := mul_le_mul_of_nonneg_left hab hc0
        _ = _ := by ring
    have hle := Summable.tsum_le_tsum key sUf
      (((sU.mul_left t).add (Ef.div_const t)).div_const 2)
    rw [eUf, tsum_div_const, Summable.tsum_add (sU.mul_left t) (Ef.div_const t), tsum_mul_left,
      tsum_div_const] at hle
    have h1 : t * ∑' q : V × V, c q.1 q.2 * (U q.1 - U q.2) ^ 2 ≤ t * (2 * (G / pi c o)) :=
      mul_le_mul_of_nonneg_left (by linarith) ht.le
    linarith
  have hT : Filter.Tendsto (fun N => ∑' x, f x * p c o N x + (2 * t * (G / pi c o) + EF / t) / 4)
      Filter.atTop (nhds (0 + (2 * t * (G / pi c o) + EF / t) / 4)) := by
    refine Filter.Tendsto.add ?_ tendsto_const_nhds
    have e : (fun N => ∑' x, f x * p c o N x) = fun N => ∑ x ∈ hf.toFinset, f x * p c o N x := by
      funext N
      refine tsum_eq_sum fun x hx => ?_
      have : f x = 0 := by simpa using hx
      rw [this, zero_mul]
    rw [e]
    have := tendsto_finsetSum hf.toFinset fun x _ =>
      (p_tendsto hc o G hG x).const_mul (f x)
    simpa using this
  have := ge_of_tendsto' hT hN
  linarith

end Net

/-! ## Paths and rough embeddings -/

section Rough

variable {V V' : Type*}

lemma pathEdges_cons_cons (a w : V) (l : List V) :
    pathEdges (a :: w :: l) = (a, w) :: pathEdges (w :: l) := rfl

lemma fst_mem_of_mem_pathEdges {l : List V} {e : V × V} (he : e ∈ pathEdges l) : e.1 ∈ l := by
  obtain ⟨x, y⟩ := e
  exact (List.of_mem_zip he).1

lemma pathEdges_nodup : ∀ {l : List V}, l.Nodup → (pathEdges l).Nodup
  | [], _ => by simp [pathEdges]
  | [_], _ => by simp [pathEdges]
  | a :: w :: l, h => by
    rw [pathEdges_cons_cons]
    have h' := List.nodup_cons.1 h
    exact List.nodup_cons.2 ⟨fun hm => h'.1 (fst_mem_of_mem_pathEdges hm), pathEdges_nodup h'.2⟩

lemma telescope (g : V → ℝ) : ∀ (l : List V) (a b : V), l.head? = some a → l.getLast? = some b →
    ((pathEdges l).map fun e => g e.1 - g e.2).sum = g a - g b
  | [], a, b, h, _ => by simp at h
  | [x], a, b, h1, h2 => by
    simp at h1 h2; subst h1; subst h2; simp [pathEdges]
  | x :: w :: l, a, b, h1, h2 => by
    rw [List.getLast?_cons_cons] at h2
    rw [pathEdges_cons_cons, List.map_cons, List.sum_cons, telescope g (w :: l) w b rfl h2]
    simp at h1; subst h1; ring

lemma head_edge : ∀ (l : List V) (a : V), 2 ≤ l.length → l.head? = some a →
    ∃ e ∈ pathEdges l, e.1 = a
  | x :: w :: l, a, _, h => ⟨(x, w), by rw [pathEdges_cons_cons]; exact List.mem_cons_self .., by
      simpa using h⟩
  | [], _, h, _ => by simp at h
  | [_], _, h, _ => by simp at h

/-- The `c'`-edges used by the image path of a `c`-edge (empty for non-edges). -/
noncomputable def S (c : V → V → ℝ) (Φ : V → V → List V') (q : V × V) : Finset (V' × V') :=
  if q.1 ≠ q.2 ∧ 0 < c q.1 q.2 then (pathEdges (Φ q.1 q.2)).toFinset else ∅

lemma regroup (c : V → V → ℝ) (c' : V' → V' → ℝ) (Φ : V → V → List V') (β : ℕ)
    (hpos : ∀ x y, x ≠ y → 0 < c x y → ∀ e ∈ pathEdges (Φ x y), 0 < c' e.1 e.2)
    (hcount : ∀ u v, 0 < c' u v →
      {p : V × V | p.1 ≠ p.2 ∧ 0 < c p.1 p.2 ∧ (u, v) ∈ pathEdges (Φ p.1 p.2)}.ncard ≤ β ∧
      {p : V × V | p.1 ≠ p.2 ∧ 0 < c p.1 p.2 ∧ (u, v) ∈ pathEdges (Φ p.1 p.2)}.Finite)
    (w : V' × V' → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw : Summable w) :
    Summable (fun q => ∑ e ∈ S c Φ q, w e) ∧ ∑' q, ∑ e ∈ S c Φ q, w e ≤ β * ∑' e, w e := by
  have hcard : ∀ (s : Finset (V × V)) (e : V' × V'),
      (s.filter fun q => e ∈ S c Φ q).card ≤ β := by
    intro s e
    by_cases hne : (s.filter fun q => e ∈ S c Φ q).Nonempty
    · obtain ⟨q0, hq0⟩ := hne
      have hq0' := (Finset.mem_filter.1 hq0).2
      unfold S at hq0'
      split_ifs at hq0' with hE
      · have he := List.mem_toFinset.1 hq0'
        have hc' := hpos _ _ hE.1 hE.2 e he
        obtain ⟨hn, hfin⟩ := hcount e.1 e.2 hc'
        refine le_trans ?_ hn
        rw [← Set.ncard_coe_finset]
        refine Set.ncard_le_ncard (fun q hq => ?_) hfin
        have hq' := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
        unfold S at hq'
        split_ifs at hq' with hE'
        · exact ⟨hE'.1, hE'.2, List.mem_toFinset.1 hq'⟩
        · simp at hq'
      · simp at hq0'
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  have hsum : ∀ s : Finset (V × V), ∑ q ∈ s, ∑ e ∈ S c Φ q, w e ≤ β * ∑' e, w e := by
    intro s
    rw [Finset.sum_comm' (t' := s.biUnion (S c Φ)) (s' := fun e => s.filter fun q => e ∈ S c Φ q)
      (fun q e => ⟨fun ⟨hq, he⟩ => ⟨Finset.mem_filter.2 ⟨hq, he⟩, Finset.mem_biUnion.2 ⟨q, hq, he⟩⟩,
        fun ⟨h, _⟩ => Finset.mem_filter.1 h⟩)]
    calc ∑ e ∈ s.biUnion (S c Φ), ∑ q ∈ s.filter (fun q => e ∈ S c Φ q), w e
        = ∑ e ∈ s.biUnion (S c Φ), ((s.filter fun q => e ∈ S c Φ q).card : ℝ) * w e := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ e ∈ s.biUnion (S c Φ), (β : ℝ) * w e :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hcard s e)
            (hw0 e)
      _ = β * ∑ e ∈ s.biUnion (S c Φ), w e := by rw [Finset.mul_sum]
      _ ≤ β * ∑' e, w e :=
          mul_le_mul_of_nonneg_left (hw.sum_le_tsum _ fun e _ => hw0 e) (Nat.cast_nonneg β)
  have hnn : 0 ≤ fun q => ∑ e ∈ S c Φ q, w e := fun q => Finset.sum_nonneg fun e _ => hw0 e
  have hS := summable_of_sum_le hnn hsum
  exact ⟨hS, hS.tsum_le_of_sum_le hsum⟩

variable (c : V → V → ℝ) (c' : V' → V' → ℝ) (φ : V → V') (Φ : V → V → List V') (α : ℝ)

/-- The data of a rough embedding at one edge. -/
def EdgeData (x y : V) : Prop :=
  2 ≤ (Φ x y).length ∧ (Φ x y).head? = some (φ x) ∧ (Φ x y).getLast? = some (φ y) ∧
    (Φ x y).Nodup ∧ (∀ e ∈ pathEdges (Φ x y), 0 < c' e.1 e.2) ∧
    ((pathEdges (Φ x y)).map fun e => 1 / c' e.1 e.2).sum ≤ α * (1 / c x y) ∧
    Φ y x = (Φ x y).reverse

variable {c c' φ Φ α}

lemma edge_energy {x y : V} (hcxy : 0 < c x y) (hE : EdgeData c c' φ Φ α x y) (f : V' → ℝ) :
    c x y * (f (φ x) - f (φ y)) ^ 2 ≤
      max α 0 * ∑ e ∈ (pathEdges (Φ x y)).toFinset, c' e.1 e.2 * (f e.1 - f e.2) ^ 2 := by
  obtain ⟨hlen, hhead, hlast, hnd, hpos, hr, -⟩ := hE
  have hLnd : (pathEdges (Φ x y)).Nodup := pathEdges_nodup hnd
  set s := (pathEdges (Φ x y)).toFinset
  have htel : f (φ x) - f (φ y) = ∑ e ∈ s, (f e.1 - f e.2) := by
    rw [List.sum_toFinset _ hLnd, telescope f _ _ _ hhead hlast]
  have hR : ∑ e ∈ s, 1 / c' e.1 e.2 ≤ α * (1 / c x y) := by rwa [List.sum_toFinset _ hLnd]
  have hpos' : ∀ e ∈ s, 0 < 1 / c' e.1 e.2 :=
    fun e he => one_div_pos.2 (hpos e (List.mem_toFinset.1 he))
  obtain ⟨e0, he0, -⟩ := head_edge _ _ hlen hhead
  have hRpos : 0 < ∑ e ∈ s, 1 / c' e.1 e.2 :=
    Finset.sum_pos hpos' ⟨e0, List.mem_toFinset.2 he0⟩
  have hCS := Finset.sq_sum_div_le_sum_sq_div s (fun e => f e.1 - f e.2) hpos'
  have hW : ∑ e ∈ s, (f e.1 - f e.2) ^ 2 / (1 / c' e.1 e.2) =
      ∑ e ∈ s, c' e.1 e.2 * (f e.1 - f e.2) ^ 2 :=
    Finset.sum_congr rfl fun e _ => by rw [div_div_eq_mul_div, div_one]; ring
  rw [hW, div_le_iff₀ hRpos] at hCS
  set W := ∑ e ∈ s, c' e.1 e.2 * (f e.1 - f e.2) ^ 2
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun e he =>
    mul_nonneg (hpos e (List.mem_toFinset.1 he)).le (sq_nonneg _)
  have hcR : c x y * ∑ e ∈ s, 1 / c' e.1 e.2 ≤ α := by
    have := mul_le_mul_of_nonneg_left hR hcxy.le
    rwa [show c x y * (α * (1 / c x y)) = α by field_simp] at this
  rw [htel]
  calc c x y * (∑ e ∈ s, (f e.1 - f e.2)) ^ 2 ≤ c x y * (W * ∑ e ∈ s, 1 / c' e.1 e.2) :=
        mul_le_mul_of_nonneg_left hCS hcxy.le
    _ = (c x y * ∑ e ∈ s, 1 / c' e.1 e.2) * W := by ring
    _ ≤ α * W := mul_le_mul_of_nonneg_right hcR hW0
    _ ≤ max α 0 * W := mul_le_mul_of_nonneg_right (le_max_left _ _) hW0

lemma edge_first {x y : V} (hcxy : 0 < c x y) (hE : EdgeData c c' φ Φ α x y) (F : V' → ℝ)
    (hF : ∀ z, 0 ≤ F z) :
    c x y * F (φ x) ≤ max α 0 * ∑ e ∈ (pathEdges (Φ x y)).toFinset, c' e.1 e.2 * F e.1 := by
  obtain ⟨hlen, hhead, -, hnd, hpos, hr, -⟩ := hE
  have hLnd : (pathEdges (Φ x y)).Nodup := pathEdges_nodup hnd
  set s := (pathEdges (Φ x y)).toFinset
  have hR : ∑ e ∈ s, 1 / c' e.1 e.2 ≤ α * (1 / c x y) := by rwa [List.sum_toFinset _ hLnd]
  have hpos' : ∀ e ∈ s, 0 < 1 / c' e.1 e.2 :=
    fun e he => one_div_pos.2 (hpos e (List.mem_toFinset.1 he))
  obtain ⟨e0, he0, h0⟩ := head_edge _ _ hlen hhead
  have he0' : e0 ∈ s := List.mem_toFinset.2 he0
  have hsingle : 1 / c' e0.1 e0.2 ≤ ∑ e ∈ s, 1 / c' e.1 e.2 :=
    Finset.single_le_sum (f := fun e => 1 / c' e.1 e.2) (fun e he => (hpos' e he).le) he0'
  have hc0 := hpos e0 he0
  have hle : c x y ≤ α * c' e0.1 e0.2 := by
    have h := mul_le_mul_of_nonneg_left (hsingle.trans hR) hcxy.le
    rw [show c x y * (α * (1 / c x y)) = α by field_simp, mul_one_div, div_le_iff₀ hc0] at h
    exact h
  calc c x y * F (φ x) = c x y * F e0.1 := by rw [h0]
    _ ≤ (max α 0 * c' e0.1 e0.2) * F e0.1 := by
        exact mul_le_mul_of_nonneg_right
          (hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hc0.le)) (hF _)
    _ = max α 0 * (c' e0.1 e0.2 * F e0.1) := by ring
    _ ≤ max α 0 * ∑ e ∈ s, c' e.1 e.2 * F e.1 :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun e => c' e.1 e.2 * F e.1)
          (fun e he => mul_nonneg (hpos e (List.mem_toFinset.1 he)).le (hF _)) he0')
          (le_max_right _ _)

end Rough

/-! ## The transfer theorem -/

theorem transfer {V V' : Type*} (c : V → V → ℝ) (c' : V' → V' → ℝ) (hc : IsNetwork c)
    (hc' : IsNetwork c') (φ : V → V') (hφ : IsRoughEmbedding c c' φ) (a : V)
    (ha : ¬ IsRecurrentChain (networkWalk c) a) :
    ¬ IsRecurrentChain (networkWalk c') (φ a) := by
  obtain ⟨α, β, Φ, h1, h2⟩ := hφ
  have hED : ∀ x y, x ≠ y → 0 < c x y → EdgeData c c' φ Φ α x y := h1
  have hpos : ∀ x y, x ≠ y → 0 < c x y → ∀ e ∈ pathEdges (Φ x y), 0 < c' e.1 e.2 :=
    fun x y hxy hcxy => (h1 x y hxy hcxy).2.2.2.2.1
  set A := max α 0
  have hA : 0 ≤ A := le_max_right _ _
  obtain ⟨G, hG⟩ := bdd_of_not_rec hc a ha
  have hG0 : 0 ≤ G := le_trans (green_nn hc a 0) (hG 0)
  intro hrec
  set o' := φ a
  set G1 := G / pi c a
  have hG1 : 0 ≤ G1 := div_nonneg hG0 (pi_pos hc a).le
  set t : ℝ := 4 * A * β + 4
  have ht : 0 < t := by positivity
  apply not_bdd_of_rec hc' o' hrec (pi c' o' * (2 * t * G1 / 3))
  intro M
  set U := u c' o' M
  set X := U o'
  rw [green_eq hc']
  refine mul_le_mul_of_nonneg_left ?_ (pi_pos hc' o').le
  by_cases hX : X ≤ 0
  · have : 0 ≤ 2 * t * G1 / 3 := by positivity
    linarith
  push Not at hX
  obtain ⟨hEs', hE'⟩ := energy_u hc' o' M
  set h : V → ℝ := fun x => U (φ x)
  -- non-edges contribute nothing
  have nonedge : ∀ q : V × V, ¬ (q.1 ≠ q.2 ∧ 0 < c q.1 q.2) → q.1 ≠ q.2 → c q.1 q.2 = 0 := by
    intro q hE hne
    push Not at hE
    exact le_antisymm (hE hne) (c_nn hc _ _)
  -- pulled-back energy
  obtain ⟨hR1, hR1le⟩ := regroup c c' Φ β hpos h2
    (fun e => c' e.1 e.2 * (U e.1 - U e.2) ^ 2) (fun e => mul_nonneg (c_nn hc' _ _) (sq_nonneg _))
    hEs'
  have bound1 : ∀ q : V × V, c q.1 q.2 * (h q.1 - h q.2) ^ 2 ≤
      A * ∑ e ∈ S c Φ q, c' e.1 e.2 * (U e.1 - U e.2) ^ 2 := by
    intro q
    unfold S
    split_ifs with hE
    · exact edge_energy hE.2 (hED _ _ hE.1 hE.2) U
    · simp only [Finset.sum_empty, mul_zero]
      by_cases heq : q.1 = q.2
      · rw [heq]; simp
      · rw [nonedge q hE heq]; simp
  have Eh : Summable (fun q : V × V => c q.1 q.2 * (h q.1 - h q.2) ^ 2) :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (c_nn hc _ _) (sq_nonneg _)) bound1
      (hR1.mul_left A)
  have Ehle : ∑' q : V × V, c q.1 q.2 * (h q.1 - h q.2) ^ 2 ≤ A * β * (2 * X) := by
    calc ∑' q : V × V, c q.1 q.2 * (h q.1 - h q.2) ^ 2
        ≤ ∑' q, A * ∑ e ∈ S c Φ q, c' e.1 e.2 * (U e.1 - U e.2) ^ 2 :=
          Summable.tsum_le_tsum bound1 Eh (hR1.mul_left A)
      _ = A * ∑' q, ∑ e ∈ S c Φ q, c' e.1 e.2 * (U e.1 - U e.2) ^ 2 := tsum_mul_left
      _ ≤ A * (β * (2 * X)) := mul_le_mul_of_nonneg_left
          (hR1le.trans (mul_le_mul_of_nonneg_left hE' (Nat.cast_nonneg β))) hA
      _ = A * β * (2 * X) := by ring
  -- the tail family
  set Gf : V × V → ℝ := fun q => if q.1 ≠ q.2 then c q.1 q.2 * h q.1 ^ 2 else 0
  have hGf0 : ∀ q, 0 ≤ Gf q := fun q => by
    simp only [Gf]; split_ifs
    · exact mul_nonneg (c_nn hc _ _) (sq_nonneg _)
    · exact le_rfl
  have hw2 : Summable (fun e : V' × V' => c' e.1 e.2 * U e.1 ^ 2) := by
    refine prod_summable (F := fun x y => c' x y * U x ^ 2)
      (fun x y => mul_nonneg (c_nn hc' x y) (sq_nonneg _)) (fun x => (c_sum hc' x).mul_right _) ?_
    simp_rw [tsum_mul_right]
    have hb : ∀ x, U x ^ 2 ≤ (M * (1 / pi c' o')) * U x := fun x => by
      have h0 := u_nn hc' o' M x
      have h1 := u_le hc' o' M x
      nlinarith
    have : Summable fun x => pi c' x * U x ^ 2 :=
      Summable.of_nonneg_of_le (fun x => mul_nonneg (pi_pos hc' x).le (sq_nonneg _))
        (fun x => by
          calc pi c' x * U x ^ 2 ≤ pi c' x * ((M * (1 / pi c' o')) * U x) :=
                mul_le_mul_of_nonneg_left (hb x) (pi_pos hc' x).le
            _ = (M * (1 / pi c' o')) * (pi c' x * U x) := by ring)
        ((pu_summable hc' o' M).mul_left _)
    exact this
  obtain ⟨hR2, -⟩ := regroup c c' Φ β hpos h2
    (fun e => c' e.1 e.2 * U e.1 ^ 2) (fun e => mul_nonneg (c_nn hc' _ _) (sq_nonneg _)) hw2
  have bound2 : ∀ q : V × V, Gf q ≤ A * ∑ e ∈ S c Φ q, c' e.1 e.2 * U e.1 ^ 2 := by
    intro q
    unfold S
    split_ifs with hE
    · simp only [Gf, if_pos hE.1]
      exact edge_first hE.2 (hED _ _ hE.1 hE.2) (fun z => U z ^ 2) (fun z => sq_nonneg _)
    · simp only [Finset.sum_empty, mul_zero, Gf]
      split_ifs with heq
      · rw [nonedge q hE heq]; simp
      · exact le_rfl
  have hGfs : Summable Gf := Summable.of_nonneg_of_le hGf0 bound2 (hR2.mul_left A)
  -- choose a finite set carrying all but `X` of the tail mass
  obtain ⟨s, hs⟩ : ∃ s : Finset (V × V), ∑' q : {q // q ∉ s}, Gf q < X :=
    ((tendsto_tsum_compl_atTop_zero Gf).eventually (gt_mem_nhds hX)).exists
  set K : Finset V := insert a (s.image Prod.fst)
  have hsK : ∀ q : V × V, q.1 ∉ K → q ∉ s := fun q hq hqs =>
    hq (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hqs))
  set T1 : V × V → ℝ := fun q => if q.1 ∉ K then Gf q else 0
  have hT1le : ∀ q, T1 q ≤ Gf q := fun q => by
    simp only [T1]; split_ifs
    · exact hGf0 q
    · exact le_rfl
  have hT10 : ∀ q, 0 ≤ T1 q := fun q => by
    simp only [T1]; split_ifs
    · exact le_rfl
    · exact hGf0 q
  have hT1s : Summable T1 := Summable.of_nonneg_of_le hT10 hT1le hGfs
  have hTl : ∑' q, T1 q ≤ X := by
    have e := tsum_subtype ({q | q ∉ s} : Set (V × V)) Gf
    have hle : ∑' q, T1 q ≤ ∑' q, ({q | q ∉ s} : Set (V × V)).indicator Gf q := by
      refine Summable.tsum_le_tsum (fun q => ?_) hT1s (hGfs.indicator _)
      by_cases hq : q.1 ∉ K
      · simp only [T1, if_pos hq]
        rw [Set.indicator_of_mem (show q ∈ ({q | q ∉ s} : Set (V × V)) from hsK q hq)]
      · simp only [T1, if_neg hq]
        exact Set.indicator_nonneg (fun q _ => hGf0 q) q
    have : ∑' q, ({q | q ∉ s} : Set (V × V)).indicator Gf q < X := by
      rw [← e]; exact hs
    linarith
  -- the truncated test function
  set hK : V → ℝ := fun x => if x ∈ K then h x else 0
  have hKfin : (Function.support hK).Finite :=
    (K.finite_toSet).subset fun x hx => by
      by_contra h'
      exact hx (if_neg h')
  have hKa : hK a = X := by
    have haK : a ∈ K := Finset.mem_insert_self _ _
    show (if a ∈ K then h a else 0) = X
    rw [if_pos haK]
  have termK : ∀ q : V × V, c q.1 q.2 * (hK q.1 - hK q.2) ^ 2 ≤
      2 * (c q.1 q.2 * (h q.1 - h q.2) ^ 2) + 2 * T1 q + 2 * T1 q.swap := by
    intro q
    obtain ⟨x, y⟩ := q
    show c x y * ((if x ∈ K then h x else 0) - (if y ∈ K then h y else 0)) ^ 2 ≤
      2 * (c x y * (h x - h y) ^ 2) + 2 * (if x ∉ K then Gf (x, y) else 0) +
        2 * (if y ∉ K then Gf (y, x) else 0)
    have hc0 := c_nn hc x y
    have g1 : 0 ≤ Gf (x, y) := hGf0 _
    have g2 : 0 ≤ Gf (y, x) := hGf0 _
    by_cases hx : x ∈ K <;> by_cases hy : y ∈ K
    · rw [if_pos hx, if_pos hy, if_neg (not_not.2 hx), if_neg (not_not.2 hy)]
      nlinarith [mul_nonneg hc0 (sq_nonneg (h x - h y))]
    · have hxy : x ≠ y := fun e => hy (e ▸ hx)
      have eG : Gf (y, x) = c y x * h y ^ 2 := if_pos hxy.symm
      rw [if_pos hx, if_neg hy, if_neg (not_not.2 hx), if_pos hy, eG, c_sym hc y x]
      have : h x ^ 2 ≤ 2 * (h x - h y) ^ 2 + 2 * h y ^ 2 := by
        nlinarith [sq_nonneg (h x - 2 * h y)]
      nlinarith [mul_le_mul_of_nonneg_left this hc0]
    · have hxy : x ≠ y := fun e => hx (e ▸ hy)
      have eG : Gf (x, y) = c x y * h x ^ 2 := if_pos hxy
      rw [if_neg hx, if_pos hy, if_pos hx, if_neg (not_not.2 hy), eG]
      have : h y ^ 2 ≤ 2 * (h x - h y) ^ 2 + 2 * h x ^ 2 := by
        nlinarith [sq_nonneg (h y - 2 * h x)]
      nlinarith [mul_le_mul_of_nonneg_left this hc0]
    · rw [if_neg hx, if_neg hy, if_pos hx, if_pos hy]
      nlinarith [mul_nonneg hc0 (sq_nonneg (h x - h y))]
  have hT1sw : Summable (fun q : V × V => T1 q.swap) := swap_summable hT1s
  have hRHS : Summable (fun q : V × V => 2 * (c q.1 q.2 * (h q.1 - h q.2) ^ 2) + 2 * T1 q +
      2 * T1 q.swap) :=
    ((Eh.mul_left 2).add (hT1s.mul_left 2)).add (hT1sw.mul_left 2)
  have EK : Summable (fun q : V × V => c q.1 q.2 * (hK q.1 - hK q.2) ^ 2) :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (c_nn hc _ _) (sq_nonneg _)) termK hRHS
  have EKle : ∑' q : V × V, c q.1 q.2 * (hK q.1 - hK q.2) ^ 2 ≤ t * X := by
    have h0 := Summable.tsum_le_tsum termK EK hRHS
    rw [Summable.tsum_add ((Eh.mul_left 2).add (hT1s.mul_left 2)) (hT1sw.mul_left 2),
      Summable.tsum_add (Eh.mul_left 2) (hT1s.mul_left 2), tsum_mul_left, tsum_mul_left,
      tsum_mul_left, tsum_swap_eq T1] at h0
    have : t * X = 4 * A * β * X + 4 * X := by simp only [t]; ring
    rw [this]
    nlinarith
  have hH := hardy hc a G hG hK hKfin t ht
  rw [hKa] at hH
  have : (∑' q : V × V, c q.1 q.2 * (hK q.1 - hK q.2) ^ 2) / t ≤ X := by
    rw [div_le_iff₀ ht]; linarith
  linarith

end LyonsPeres.IETLP

namespace LyonsPeres

theorem chk_isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding {V V' : Type*} (c : V → V → ℝ)
    (c' : V' → V' → ℝ) (hc : IsNetwork c) (hc' : IsNetwork c') :
    (∀ (φ : V → V') (ψ : V' → V), IsRoughEmbedding c c' φ → IsRoughEmbedding c' c ψ →
      (IsTransientNetwork c ↔ IsTransientNetwork c')) ∧
    ∀ φ : V → V', IsRoughEmbedding c c' φ → IsTransientNetwork c → IsTransientNetwork c' := by
  refine ⟨fun φ ψ hφ hψ => ⟨fun ⟨a, ha⟩ => ⟨φ a, IETLP.transfer c c' hc hc' φ hφ a ha⟩,
    fun ⟨a, ha⟩ => ⟨ψ a, IETLP.transfer c' c hc' hc ψ hψ a ha⟩⟩,
    fun φ hφ ⟨a, ha⟩ => ⟨φ a, IETLP.transfer c c' hc hc' φ hφ a ha⟩⟩

end LyonsPeres

end

open IntervalExchange
open LyonsPeres in
theorem solution {V V' : Type*} (c : V → V → ℝ)
    (c' : V' → V' → ℝ) (hc : IsNetwork c) (hc' : IsNetwork c') :
    (∀ (φ : V → V') (ψ : V' → V), IsRoughEmbedding c c' φ → IsRoughEmbedding c' c ψ →
      (IsTransientNetwork c ↔ IsTransientNetwork c')) ∧
    ∀ φ : V → V', IsRoughEmbedding c c' φ → IsTransientNetwork c → IsTransientNetwork c' :=
  LyonsPeres.chk_isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding c c' hc hc'
