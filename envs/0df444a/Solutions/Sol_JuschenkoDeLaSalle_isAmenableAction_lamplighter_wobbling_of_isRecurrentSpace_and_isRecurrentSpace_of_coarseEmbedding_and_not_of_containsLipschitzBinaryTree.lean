-- Prove2me | solution 1 for JuschenkoDeLaSalle.isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarseEmbedding_and_not_of_containsLipschitzBinaryTree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T14:08:23.538984+00:00
-- url     : https://prove2.me/submissions/b038c98f-810a-46bf-acf5-0462e16bc3ed

import Mathlib
import Definitions.Def_IntervalExchange
import Theorems.Thm_JMMS_isExtensivelyAmenable_of_isRecurrentAction
import Theorems.Thm_MarkovMixing_polya_recurrence
import Theorems.Thm_LyonsPeres_isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding

section

section

/-!
# Juschenko–de la Salle, wobbling groups: conjuncts 1 and 3

(1) If `X` (bounded geometry) is recurrent at `x₀`, the lamplighter action of `W(X)` on
`(ℤ/2)^(X)` is amenable. Route: for a symmetric finitely supported probability `μ` on `W(X)`,
its walk on `X` is a network (conductances `walkKernel μ`) that embeds roughly, via the
transposition `(x₀ x₁)`, into the ball network of radius `R` (Lyons–Peres 2.17, pointwise
form copied from `Solutions/IET/LP217.lean`; connectivity is never used there, so it is
dropped). Hence `W(X) ↷ X` is a recurrent action, extensively amenable by JMMS Theorem 4.2
(imported milestone), and an extensively amenable action has an amenable lamplighter action:
integrate the uniform measures on configurations supported in `E` against the extensive mean.

(3) A Lipschitz injective binary tree carries the Cayley graph of `ℤ/2 * ℤ/2 * ℤ/2` (reduced
words, letters coded by two bits), whose three right multiplications are bounded-displacement
involutions. An invariant mean on lamp configurations gives (averaging over the lit lamps
on the tree) a mean on the reduced words invariant under the three involutions; the ping-pong
`r_s(A_s) = A_sᶜ` gives `ν(A_s) = ν/2` for three disjoint sets, so `ν = 0`, while lamp
invariance forces `ν ≥ 1/2`.
-/

open IntervalExchange

namespace JuschenkoDeLaSalle.IETJ13.LP

open Classical

/-- A network without the connectivity condition (never used by the transfer argument). -/
def IsNet {V : Type*} (c : V → V → ℝ) : Prop :=
  (∀ x y, 0 ≤ c x y) ∧ (∀ x y, c x y = c y x) ∧ (∀ x, ∃ y, 0 < c x y) ∧
    (∀ x, Summable (c x))


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

lemma c_nn (hc : IsNet c) (x y : V) : 0 ≤ c x y := hc.1 x y
lemma c_sym (hc : IsNet c) (x y : V) : c x y = c y x := hc.2.1 x y
lemma c_sum (hc : IsNet c) (x : V) : Summable (c x) := hc.2.2.2 x

lemma c_le_pi (hc : IsNet c) (x y : V) : c x y ≤ pi c x :=
  (c_sum hc x).le_tsum y (fun j _ => c_nn hc x j)

lemma pi_pos (hc : IsNet c) (x : V) : 0 < pi c x := by
  obtain ⟨y, hy⟩ := hc.2.2.1 x
  exact lt_of_lt_of_le hy (c_le_pi hc x y)

lemma P_nn (hc : IsNet c) (x y : V) : 0 ≤ networkWalk c x y :=
  div_nonneg (c_nn hc x y) (pi_pos hc x).le

lemma P_le (hc : IsNet c) (x y : V) : networkWalk c x y ≤ 1 := by
  rw [nw_eq, div_le_one (pi_pos hc x)]; exact c_le_pi hc x y

lemma P_sum (hc : IsNet c) (x : V) : Summable (networkWalk c x) :=
  (c_sum hc x).div_const _

lemma P_tsum (hc : IsNet c) (x : V) : ∑' y, networkWalk c x y = 1 := by
  simp_rw [nw_eq]; rw [tsum_div_const]; exact div_self (pi_pos hc x).ne'

/-- The transition operator acting on measures. -/
noncomputable def T (c : V → V → ℝ) (f : V → ℝ) (y : V) : ℝ := ∑' x, f x * networkWalk c x y

lemma T_row (hc : IsNet c) {f : V → ℝ} (hf : Summable f) (y : V) :
    Summable fun x => f x * networkWalk c x y :=
  dom_summable hf.abs fun x => by
    rw [abs_mul, abs_of_nonneg (P_nn hc x y)]
    exact mul_le_of_le_one_right (abs_nonneg _) (P_le hc x y)

lemma T_prod (hc : IsNet c) {f : V → ℝ} (hf : Summable f) :
    Summable (fun q : V × V => f q.1 * networkWalk c q.1 q.2) := by
  have hF := prod_summable (F := fun x y => |f x| * networkWalk c x y)
    (fun x y => mul_nonneg (abs_nonneg _) (P_nn hc x y)) (fun x => (P_sum hc x).mul_left _)
    (by simp_rw [tsum_mul_left, P_tsum hc, mul_one]; exact hf.abs)
  exact dom_summable hF fun q => by rw [abs_mul, abs_of_nonneg (P_nn hc _ _)]

lemma T_summable (hc : IsNet c) {f : V → ℝ} (hf : Summable f) : Summable (T c f) :=
  col_summable (G := fun x y => f x * networkWalk c x y) (T_prod hc hf)

lemma T_tsum (hc : IsNet c) {f : V → ℝ} (hf : Summable f) : ∑' y, T c f y = ∑' x, f x := by
  unfold T
  rw [← tsum_comm_of (G := fun x y => f x * networkWalk c x y) (T_prod hc hf)]
  simp_rw [tsum_mul_left, P_tsum hc, mul_one]

lemma T_add (hc : IsNet c) {f g : V → ℝ} (hf : Summable f) (hg : Summable g) (y : V) :
    T c (fun x => f x + g x) y = T c f y + T c g y := by
  unfold T; simp_rw [add_mul]; exact (T_row hc hf y).tsum_add (T_row hc hg y)

lemma T_smul (r : ℝ) (f : V → ℝ) (y : V) : T c (fun x => r * f x) y = r * T c f y := by
  unfold T; simp_rw [mul_assoc]; exact tsum_mul_left

lemma T_sum (hc : IsNet c) {ι : Type*} (s : Finset ι) (F : ι → V → ℝ)
    (hF : ∀ i, Summable (F i)) (y : V) :
    T c (fun x => ∑ i ∈ s, F i x) y = ∑ i ∈ s, T c (F i) y := by
  unfold T; simp_rw [Finset.sum_mul]; exact Summable.tsum_finsetSum fun i _ => T_row hc (hF i) y

lemma T_nn (hc : IsNet c) {f : V → ℝ} (hf : ∀ x, 0 ≤ f x) (y : V) : 0 ≤ T c f y :=
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

lemma p_summable (hc : IsNet c) (o : V) : ∀ n, Summable (p c o n)
  | 0 => (hasSum_ite_eq o (1 : ℝ)).summable
  | n + 1 => T_summable hc (p_summable hc o n)

lemma p_nn (hc : IsNet c) (o : V) : ∀ n z, 0 ≤ p c o n z
  | 0, z => by simp only [p]; split_ifs <;> norm_num
  | n + 1, z => T_nn hc (p_nn hc o n) z

lemma ak_nn (hc : IsNet c) (o : V) : ∀ n z, 0 ≤ ak c o n z
  | 0, z => by simp only [ak]; split_ifs <;> norm_num
  | n + 1, z => by
    simp only [ak]; split_ifs
    · exact le_rfl
    · exact T_nn hc (ak_nn hc o n) z

lemma ak_summable (hc : IsNet c) (o : V) : ∀ n, Summable (ak c o n)
  | 0 => (hasSum_ite_eq o (1 : ℝ)).summable
  | n + 1 => Summable.of_nonneg_of_le (ak_nn hc o (n + 1)) (fun z => by
      simp only [ak]; split_ifs
      · exact T_nn hc (ak_nn hc o n) z
      · exact le_rfl) (T_summable hc (ak_summable hc o n))

lemma fr_nn (hc : IsNet c) (o : V) (n : ℕ) : 0 ≤ fr c o n := T_nn hc (ak_nn hc o n) o

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

lemma fr_partial (hc : IsNet c) (o : V) (n : ℕ) :
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

lemma fr_sum_le (hc : IsNet c) (o : V) (n : ℕ) : ∑ k ∈ Finset.range n, fr c o k ≤ 1 := by
  have := fr_partial hc o n
  have : 0 ≤ ∑' z, ak c o n z := tsum_nonneg (ak_nn hc o n)
  linarith

lemma fr_summable (hc : IsNet c) (o : V) : Summable (fr c o) :=
  summable_of_sum_range_le (fr_nn hc o) (fr_sum_le hc o)

lemma renewal (hc : IsNet c) (o : V) (n : ℕ) (z : V) :
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

lemma green_succ (hc : IsNet c) (o : V) (N : ℕ) :
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

lemma green_nn (hc : IsNet c) (o : V) (N : ℕ) : 0 ≤ green c o N :=
  Finset.sum_nonneg fun n _ => p_nn hc o n o

lemma green_mono (hc : IsNet c) (o : V) : Monotone (green c o) := by
  refine monotone_nat_of_le_succ fun N => ?_
  unfold green
  rw [Finset.sum_range_succ]
  linarith [p_nn hc o N o]

lemma green_bdd (hc : IsNet c) (o : V) (hF : ∑' k, fr c o k < 1) (N : ℕ) :
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

lemma not_bdd (hc : IsNet c) (o : V) (hrec : HasSum (fr c o) 1) (M : ℝ)
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

lemma bdd_of_not_rec (hc : IsNet c) (o : V) (h : ¬ IsRecurrentChain (networkWalk c) o) :
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

lemma not_bdd_of_rec (hc : IsNet c) (o : V) (h : IsRecurrentChain (networkWalk c) o)
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

lemma pd (hc : IsNet c) (o : V) (n : ℕ) (x : V) : pi c x * d c o n x = p c o n x := by
  unfold d; field_simp [(pi_pos hc x).ne']

lemma cd_eq (hc : IsNet c) (o : V) (n : ℕ) (x : V) :
    (Summable fun y => c x y * d c o n y) ∧ ∑' y, c x y * d c o n y = p c o (n + 1) x := by
  have e : (fun y => c x y * d c o n y) = fun y => p c o n y * networkWalk c y x := by
    funext y; unfold d; rw [nw_eq, c_sym hc x y]; ring
  rw [e]; exact ⟨T_row hc (p_summable hc o n) x, rfl⟩

lemma d_nn (hc : IsNet c) (o : V) (n : ℕ) (x : V) : 0 ≤ d c o n x :=
  div_nonneg (p_nn hc o n x) (pi_pos hc x).le

lemma d_le (hc : IsNet c) (o : V) : ∀ n x, d c o n x ≤ 1 / pi c o
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

lemma u_nn (hc : IsNet c) (o : V) (N : ℕ) (x : V) : 0 ≤ u c o N x :=
  Finset.sum_nonneg fun n _ => d_nn hc o n x

lemma u_le (hc : IsNet c) (o : V) (N : ℕ) (x : V) : u c o N x ≤ N * (1 / pi c o) := by
  unfold u
  calc ∑ n ∈ Finset.range N, d c o n x ≤ ∑ n ∈ Finset.range N, 1 / pi c o :=
        Finset.sum_le_sum fun n _ => d_le hc o n x
    _ = N * (1 / pi c o) := by simp

lemma pi_u (hc : IsNet c) (o : V) (N : ℕ) (x : V) :
    pi c x * u c o N x = ∑ n ∈ Finset.range N, p c o n x := by
  unfold u; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => pd hc o n x

lemma pu_summable (hc : IsNet c) (o : V) (N : ℕ) :
    Summable (fun x => pi c x * u c o N x) := by
  simp_rw [pi_u hc]; exact summable_sum fun n _ => p_summable hc o n

lemma green_eq (hc : IsNet c) (o : V) (N : ℕ) : green c o N = pi c o * u c o N o := by
  rw [pi_u hc]; rfl

lemma cu (hc : IsNet c) (o : V) (N : ℕ) (x : V) :
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
lemma ibp (hc : IsNet c) (o : V) (N : ℕ) (h : V → ℝ) (H : ℝ) (hH : ∀ x, |h x| ≤ H) :
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

lemma energy_u (hc : IsNet c) (o : V) (N : ℕ) :
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

lemma ip_d (hc : IsNet c) (o : V) : ∀ m n,
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

lemma p_tendsto (hc : IsNet c) (o : V) (G : ℝ) (hG : ∀ N, green c o N ≤ G) (x : V) :
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

lemma hardy (hc : IsNet c) (o : V) (G : ℝ) (hG : ∀ N, green c o N ≤ G) (f : V → ℝ)
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

theorem transfer {V V' : Type*} (c : V → V → ℝ) (c' : V' → V' → ℝ) (hc : IsNet c)
    (hc' : IsNet c') (φ : V → V') (hφ : IsRoughEmbedding c c' φ) (a : V)
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


end JuschenkoDeLaSalle.IETJ13.LP

namespace JuschenkoDeLaSalle.IETJ13.Integ

open scoped ENNReal


/-- `∑_{k < 2^n} 2^{-n} m {f ≥ (k+1)/2^n}`: the integral of `⌊2^n f⌋ / 2^n`. -/
noncomputable def layerSum {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n

/-- The integral: the supremum of the layer sums. -/
noncomputable def integ {α : Type*} (m : Set α → ℝ≥0∞) (f : α → ℝ) : ℝ := ⨆ n, layerSum m f n


namespace PartB1
open scoped ENNReal



variable {α : Type*} {m : Set α → ℝ≥0∞}

/-! ### Elementary facts about a finitely additive probability -/

lemma fa_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) {S T : Set α} (h : S ⊆ T) :
    m S ≤ m T := by
  have hd : Disjoint S (T \ S) := Set.disjoint_sdiff_right
  have := hm.2 S (T \ S) hd
  rw [Set.union_sdiff_cancel h] at this
  rw [this]
  exact le_self_add

lemma fa_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (S : Set α) :
    m S ≤ 1 := h1 ▸ fa_mono hm (Set.subset_univ S)

lemma fa_ne_top (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (S : Set α) :
    m S ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (fa_le_one hm h1 S)

lemma fa_union_le (hm : Garrido.IsFinitelyAdditiveMeasure m) (S T : Set α) :
    m (S ∪ T) ≤ m S + m T := by
  have hd : Disjoint S (T \ S) := Set.disjoint_sdiff_right
  have := hm.2 S (T \ S) hd
  rw [Set.union_sdiff_self] at this
  rw [this]
  gcongr
  exact fa_mono hm Set.sdiff_subset

lemma fa_toReal_union (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {S T : Set α} (h : Disjoint S T) :
    (m (S ∪ T)).toReal = (m S).toReal + (m T).toReal := by
  rw [hm.2 S T h, ENNReal.toReal_add (fa_ne_top hm h1 S) (fa_ne_top hm h1 T)]

lemma fa_toReal_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {S T : Set α} (h : S ⊆ T) : (m S).toReal ≤ (m T).toReal :=
  ENNReal.toReal_mono (fa_ne_top hm h1 T) (fa_mono hm h)

lemma fa_toReal_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (S : Set α) : (m S).toReal ≤ 1 := by
  have := fa_toReal_mono hm h1 (Set.subset_univ S)
  rwa [h1, ENNReal.toReal_one] at this

/-! ### Bounds on the layer sums -/

lemma layerSum_nonneg (f : α → ℝ) (n : ℕ) : 0 ≤ layerSum m f n := by
  unfold layerSum
  exact Finset.sum_nonneg fun k _ => div_nonneg ENNReal.toReal_nonneg (by positivity)

lemma layerSum_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (f : α → ℝ) (n : ℕ) : layerSum m f n ≤ 1 := by
  unfold layerSum
  calc ∑ k ∈ Finset.range (2 ^ n), (m {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ f a}).toReal / 2 ^ n
      ≤ ∑ _k ∈ Finset.range (2 ^ n), (1 : ℝ) / 2 ^ n := by
        gcongr with k
        exact fa_toReal_le_one hm h1 _
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        field_simp

lemma bddAbove_layerSum (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (f : α → ℝ) : BddAbove (Set.range (layerSum m f)) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact layerSum_le_one hm h1 f n⟩

/-! ### The four easy lemmas -/

theorem integ_indicator (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (S : Set α) : integ m (S.indicator 1) = (m S).toReal := by
  have key : ∀ n, layerSum m (S.indicator 1) n = (m S).toReal := by
    intro n
    unfold layerSum
    have hset : ∀ k ∈ Finset.range (2 ^ n),
        {a | ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ S.indicator 1 a} = S := by
      intro k hk
      have hk' : k + 1 ≤ 2 ^ n := Finset.mem_range.1 hk
      have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / 2 ^ n := by positivity
      have hle : ((k + 1 : ℕ) : ℝ) / 2 ^ n ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast hk'
      push_cast at hpos hle
      ext a
      by_cases ha : a ∈ S
      · simp [ha, hle]
      · simp [ha, hpos]
    rw [Finset.sum_congr rfl fun k hk => by rw [hset k hk], Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    push_cast
    field_simp
  unfold integ
  simp only [key, ciSup_const]

theorem integ_congr (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f g : α → ℝ} (h : m {a | f a ≠ g a} = 0) : integ m f = integ m g := by
  have hle : ∀ (f g : α → ℝ), m {a | f a ≠ g a} = 0 → ∀ c : ℝ,
      m {a | c ≤ f a} ≤ m {a | c ≤ g a} := by
    intro f g h c
    calc m {a | c ≤ f a} ≤ m ({a | c ≤ g a} ∪ {a | f a ≠ g a}) := by
          apply fa_mono hm
          intro a ha
          by_cases hfg : f a = g a
          · left; simp only [Set.mem_ofPred_eq] at ha ⊢; rwa [← hfg]
          · right; exact hfg
      _ ≤ m {a | c ≤ g a} + m {a | f a ≠ g a} := fa_union_le hm _ _
      _ = m {a | c ≤ g a} := by rw [h, add_zero]
  have h' : m {a | g a ≠ f a} = 0 := by
    simpa only [ne_comm] using h
  have heq : ∀ c : ℝ, m {a | c ≤ f a} = m {a | c ≤ g a} := fun c =>
    le_antisymm (hle f g h c) (hle g f h' c)
  unfold integ layerSum
  simp only [heq]

theorem integ_comp_equiv (τ : α ≃ α) (hτ : ∀ S : Set α, m (τ '' S) = m S) (f : α → ℝ) :
    integ m (f ∘ τ) = integ m f := by
  have heq : ∀ c : ℝ, m {a | c ≤ (f ∘ τ) a} = m {a | c ≤ f a} := by
    intro c
    have : {a | c ≤ (f ∘ τ) a} = τ ⁻¹' {a | c ≤ f a} := rfl
    rw [this, ← hτ (τ ⁻¹' {a | c ≤ f a}), Equiv.image_preimage]
  unfold integ layerSum
  simp only [heq]

theorem integ_nonneg_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) : 0 ≤ integ m f ∧ integ m f ≤ 1 :=
  ⟨Real.iSup_nonneg fun n => layerSum_nonneg f n,
    Real.iSup_le (fun n => layerSum_le_one hm h1 f n) zero_le_one⟩

/-! ### `ℕ`-valued layer sums: the integral of a finitely-valued function -/

/-- `∑_{k<N} m{φ ≥ k+1}`: the integral of an `ℕ`-valued function `φ ≤ N`. -/
noncomputable def J (m : Set α → ℝ≥0∞) (φ : α → ℕ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (m {a | k + 1 ≤ φ a}).toReal

lemma J_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {φ ψ : α → ℕ} (h : ∀ a, φ a ≤ ψ a) (N : ℕ) : J m φ N ≤ J m ψ N := by
  unfold J
  exact Finset.sum_le_sum fun k _ => fa_toReal_mono hm h1 fun a ha => le_trans ha (h a)

lemma J_extend (hm : Garrido.IsFinitelyAdditiveMeasure m) {φ : α → ℕ} {N : ℕ}
    (h : ∀ a, φ a ≤ N) (N' : ℕ) (hN' : N ≤ N') : J m φ N' = J m φ N := by
  induction N', hN' using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    unfold J at ih ⊢
    rw [Finset.sum_range_succ, ih]
    have : {a | n + 1 ≤ φ a} = ∅ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact Nat.lt_succ_of_le ((h a).trans hn)
    rw [this, hm.1, ENNReal.toReal_zero, add_zero]

lemma sum_level (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (A : Set α) (φ : α → ℕ) (N : ℕ) :
    ∑ k ∈ Finset.range N, (m {a | a ∈ A ∧ φ a = k}).toReal =
      (m {a | a ∈ A ∧ φ a < N}).toReal := by
  induction N with
  | zero => simp [hm.1]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, ← fa_toReal_union hm h1]
    · congr 2
      ext a
      by_cases ha : a ∈ A <;> (simp [ha]; try omega)
    · rw [Set.disjoint_left]
      rintro a ⟨_, ha⟩ ⟨_, hb⟩
      omega

/-- Adding a `{0,1}`-valued function adds the measure of its support. -/
lemma J_add_le_one (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    (φ χ : α → ℕ) (N : ℕ) (hχ : ∀ a, χ a ≤ 1) (h : ∀ a, φ a + χ a ≤ N) :
    J m (φ + χ) N = J m φ N + (m {a | 1 ≤ χ a}).toReal := by
  have hterm : ∀ k, (m {a | k + 1 ≤ (φ + χ) a}).toReal =
      (m {a | k + 1 ≤ φ a}).toReal + (m {a | a ∈ {a | 1 ≤ χ a} ∧ φ a = k}).toReal := by
    intro k
    rw [← fa_toReal_union hm h1]
    · congr 2
      ext a
      have := hχ a
      simp only [Pi.add_apply, Set.mem_ofPred_eq, Set.mem_union]
      omega
    · rw [Set.disjoint_left]
      rintro a ha ⟨hb, hc⟩
      simp only [Set.mem_ofPred_eq] at ha hb
      omega
  unfold J
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, sum_level hm h1]
  congr 3
  ext a
  simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
  intro ha
  have := h a
  omega

lemma J_zero (hm : Garrido.IsFinitelyAdditiveMeasure m) (N : ℕ) : J m 0 N = 0 := by
  unfold J
  refine Finset.sum_eq_zero fun k _ => ?_
  have : {a : α | k + 1 ≤ (0 : α → ℕ) a} = ∅ := by
    ext a; simp
  rw [this, hm.1, ENNReal.toReal_zero]

/-- Additivity of `J` (induction on a bound for `ψ`). -/
lemma J_add (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1) (N : ℕ) :
    ∀ (M : ℕ) (φ ψ : α → ℕ), (∀ a, ψ a ≤ M) → (∀ a, φ a + ψ a ≤ N) →
      J m (φ + ψ) N = J m φ N + J m ψ N := by
  intro M
  induction M with
  | zero =>
    intro φ ψ hψ _
    have hψ0 : ψ = 0 := funext fun a => Nat.le_zero.1 (hψ a)
    subst hψ0
    rw [add_zero, J_zero hm, add_zero]
  | succ M ih =>
    intro φ ψ hψ h
    have hsplit : ψ = (fun a => min (ψ a) M) + (fun a => ψ a - M) :=
      funext fun a => by simp only [Pi.add_apply]; omega
    have hχ : ∀ a, (fun a => ψ a - M) a ≤ 1 := fun a => by
      have := hψ a; try dsimp only
      omega
    rw [hsplit, ← add_assoc, J_add_le_one hm h1 _ _ N hχ, ih φ _ (fun a => min_le_right _ _),
      J_add_le_one hm h1 _ _ N hχ]
    · ring
    all_goals
      intro a; have := h a; have := hψ a
      try dsimp only [Pi.add_apply]
      omega

/-! ### The layer sums through `J` -/

lemma layerSum_eq (f : α → ℝ) (n : ℕ) :
    layerSum m f n = J m (fun a => ⌊2 ^ n * f a⌋₊) (2 ^ n) / 2 ^ n := by
  unfold layerSum J
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [← Nat.cast_succ, Nat.le_floor_iff' (Nat.succ_ne_zero k), div_le_iff₀ (by positivity),
    mul_comm]

lemma floor_le_pow {f : α → ℝ} (hf1 : ∀ a, f a ≤ 1) (n : ℕ) (a : α) :
    ⌊2 ^ n * f a⌋₊ ≤ 2 ^ n := by
  apply Nat.floor_le_of_le
  push_cast
  have : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith [hf1 a]

lemma layerSum_mono (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) : Monotone (layerSum m f) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [layerSum_eq, layerSum_eq]
  set φ : α → ℕ := fun a => ⌊2 ^ n * f a⌋₊ with hφdef
  have hφ : ∀ a, φ a ≤ 2 ^ n := floor_le_pow hf1 n
  have h2 : ∀ a, (φ + φ) a ≤ ⌊2 ^ (n + 1) * f a⌋₊ := by
    intro a
    apply Nat.le_floor
    have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * f a by have := hf a; positivity)
    simp only [Pi.add_apply, hφdef]
    push_cast
    rw [pow_succ]
    linarith
  have key : 2 * J m φ (2 ^ n) ≤ J m (fun a => ⌊2 ^ (n + 1) * f a⌋₊) (2 ^ (n + 1)) := by
    calc 2 * J m φ (2 ^ n) = J m φ (2 ^ (n + 1)) + J m φ (2 ^ (n + 1)) := by
          rw [J_extend hm hφ (2 ^ (n + 1)) (Nat.pow_le_pow_right (by norm_num) (by omega))]
          ring
      _ = J m (φ + φ) (2 ^ (n + 1)) :=
          (J_add hm h1 _ (2 ^ n) φ φ hφ fun a => by have := hφ a; rw [pow_succ]; omega).symm
      _ ≤ _ := J_mono hm h1 h2 _
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_div_iff₀ hp (by positivity)]
  have e : J m φ (2 ^ n) * (2 : ℝ) ^ (n + 1) = 2 * J m φ (2 ^ n) * 2 ^ n := by
    rw [pow_succ]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right key hp.le

/-! ### Additivity -/

theorem integ_add (hm : Garrido.IsFinitelyAdditiveMeasure m) (h1 : m Set.univ = 1)
    {f g : α → ℝ} (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a) (hfg : ∀ a, f a + g a ≤ 1) :
    integ m (f + g) = integ m f + integ m g := by
  have hfg0 : ∀ a, 0 ≤ (f + g) a := fun a => add_nonneg (hf a) (hg a)
  have hf1 : ∀ a, f a ≤ 1 := fun a => by linarith [hfg a, hg a]
  have hg1 : ∀ a, g a ≤ 1 := fun a => by linarith [hfg a, hf a]
  have hfg1 : ∀ a, (f + g) a ≤ 1 := hfg
  have tf := tendsto_atTop_ciSup (layerSum_mono hm h1 hf hf1) (bddAbove_layerSum hm h1 f)
  have tg := tendsto_atTop_ciSup (layerSum_mono hm h1 hg hg1) (bddAbove_layerSum hm h1 g)
  have tfg := tendsto_atTop_ciSup (layerSum_mono hm h1 hfg0 hfg1) (bddAbove_layerSum hm h1 (f + g))
  have hbound : ∀ n, layerSum m f n + layerSum m g n ≤ layerSum m (f + g) n ∧
      layerSum m (f + g) n ≤ layerSum m f n + layerSum m g n + (1 / 2) ^ n := by
    intro n
    rw [layerSum_eq, layerSum_eq, layerSum_eq]
    set φ : α → ℕ := fun a => ⌊2 ^ n * f a⌋₊ with hφdef
    set ψ : α → ℕ := fun a => ⌊2 ^ n * g a⌋₊ with hψdef
    set χ : α → ℕ := fun a => ⌊2 ^ n * (f + g) a⌋₊ with hχdef
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    have hlow : ∀ a, (φ + ψ) a ≤ χ a := by
      intro a
      apply Nat.le_floor
      have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * f a by have := hf a; positivity)
      have := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * g a by have := hg a; positivity)
      simp only [Pi.add_apply, hφdef, hψdef]
      push_cast
      linarith
    have hup : ∀ a, χ a ≤ (φ + ψ + 1) a := by
      intro a
      have hlt : χ a < φ a + ψ a + 2 := by
        apply (Nat.floor_lt (by have := hfg0 a; positivity)).2
        have := Nat.lt_floor_add_one ((2 : ℝ) ^ n * f a)
        have := Nat.lt_floor_add_one ((2 : ℝ) ^ n * g a)
        simp only [Pi.add_apply, hφdef, hψdef]
        push_cast
        linarith
      simp only [Pi.add_apply, Pi.one_apply]
      omega
    have hχ : ∀ a, χ a ≤ 2 ^ n := floor_le_pow hfg1 n
    have hφ : ∀ a, φ a ≤ 2 ^ n := floor_le_pow hf1 n
    have hφψ : ∀ a, φ a + ψ a ≤ 2 ^ n := fun a => le_trans (hlow a) (hχ a)
    have hadd := J_add hm h1 (2 ^ n) (2 ^ n) φ ψ (floor_le_pow hg1 n) hφψ
    have h_lower : J m φ (2 ^ n) + J m ψ (2 ^ n) ≤ J m χ (2 ^ n) :=
      hadd ▸ J_mono hm h1 hlow (2 ^ n)
    have h_upper : J m χ (2 ^ n) ≤ J m φ (2 ^ n) + J m ψ (2 ^ n) + 1 := by
      rw [← J_extend hm hχ (2 ^ n + 1) (by omega)]
      calc J m χ (2 ^ n + 1) ≤ J m (φ + ψ + 1) (2 ^ n + 1) := J_mono hm h1 hup _
        _ = J m (φ + ψ) (2 ^ n + 1) + (m {a | 1 ≤ (1 : α → ℕ) a}).toReal :=
            J_add_le_one hm h1 _ _ _ (fun a => le_refl _)
              (fun a => by have := hφψ a; simp only [Pi.add_apply, Pi.one_apply]; omega)
        _ ≤ J m (φ + ψ) (2 ^ n + 1) + 1 := by gcongr; exact fa_toReal_le_one hm h1 _
        _ = J m φ (2 ^ n) + J m ψ (2 ^ n) + 1 := by
            rw [J_extend hm (N := 2 ^ n) (fun a => by simpa only [Pi.add_apply] using hφψ a)
              (2 ^ n + 1) (by omega), hadd]
    rw [one_div_pow, ← add_div, ← add_div]
    exact ⟨div_le_div_of_nonneg_right h_lower hp.le, div_le_div_of_nonneg_right h_upper hp.le⟩
  have hd : Filter.Tendsto (fun n => layerSum m (f + g) n - (layerSum m f n + layerSum m g n))
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => by linarith [(hbound n).1]) (fun n => by linarith [(hbound n).2])
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have := tendsto_nhds_unique (tfg.sub (tf.add tg)) hd
  unfold integ
  linarith

end PartB1

end JuschenkoDeLaSalle.IETJ13.Integ

namespace JuschenkoDeLaSalle.IETJ13

open Classical
open scoped ENNReal Pointwise
open Integ Integ.PartB1

/-! ## Part 1a: the walk of a symmetric measure on `W(X)` is recurrent -/

section Rec

variable {X : Type*} [MetricSpace X]

/-- The ball network: unit conductance between points at distance at most `R`. -/
noncomputable def ballNet (R : ℝ) (x y : X) : ℝ := if y ∈ Metric.closedBall x R then 1 else 0

lemma ballNet_tsum (hX : HasBoundedGeometry X) {R : ℝ} (hR : 0 < R) (x : X) :
    ∑' z, ballNet R x z = ((Metric.closedBall x R).ncard : ℝ) := by
  obtain ⟨N, hN⟩ := hX R hR
  have hfin := (hN x).1
  rw [tsum_eq_sum (s := hfin.toFinset) (fun z hz => by
    simp only [Set.Finite.mem_toFinset] at hz; simp [ballNet, hz])]
  rw [Set.ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  simp only [Set.Finite.mem_toFinset] at hz
  simp [ballNet, hz]

lemma ballNet_isNet (hX : HasBoundedGeometry X) {R : ℝ} (hR : 0 < R) :
    LP.IsNet (ballNet R : X → X → ℝ) := by
  refine ⟨fun x y => by unfold ballNet; split_ifs <;> norm_num, fun x y => ?_,
    fun x => ⟨x, by simp [ballNet, hR.le]⟩, fun x => ?_⟩
  · simp only [ballNet, Metric.mem_closedBall, dist_comm]
  · obtain ⟨N, hN⟩ := hX R hR
    have hfin := (hN x).1
    apply summable_of_ne_finset_zero (s := hfin.toFinset)
    intro z hz
    simp only [Set.Finite.mem_toFinset] at hz
    simp [ballNet, hz]

lemma networkWalk_ballNet (hX : HasBoundedGeometry X) {R : ℝ} (hR : 0 < R) :
    networkWalk (ballNet R : X → X → ℝ) = ballKernel X R := by
  funext x y
  unfold networkWalk
  rw [ballNet_tsum hX hR]
  simp only [ballNet, ballKernel]
  split_ifs <;> simp

variable (μ : ↥(wobbling X) →₀ ℝ)

lemma wk_eq (x y : X) :
    walkKernel (μ : ↥(wobbling X) → ℝ) x y =
      ∑ g ∈ μ.support, if g • x = y then μ g else 0 := by
  unfold walkKernel
  rw [tsum_eq_sum (s := μ.support)]
  intro g hg
  split_ifs
  · exact Finsupp.notMem_support_iff.1 hg
  · rfl

variable {μ}

lemma wk_nonneg (hμ : ThompsonAmenability.IsProbability μ) (x y : X) :
    0 ≤ walkKernel (μ : ↥(wobbling X) → ℝ) x y := by
  rw [wk_eq]
  exact Finset.sum_nonneg fun g _ => by split_ifs; exacts [hμ.1 g, le_rfl]

lemma wk_symm (hs : IsSymmetric μ) (x y : X) :
    walkKernel (μ : ↥(wobbling X) → ℝ) x y = walkKernel (μ : ↥(wobbling X) → ℝ) y x := by
  rw [wk_eq, wk_eq]
  have hmem : ∀ g ∈ μ.support, g⁻¹ ∈ μ.support := fun g hg => by
    rw [Finsupp.mem_support_iff] at *; rw [hs]; exact hg
  refine Finset.sum_nbij' (·⁻¹) (·⁻¹) hmem hmem (fun g _ => inv_inv g) (fun g _ => inv_inv g) ?_
  intro g _
  have e : (g⁻¹ • y = x) ↔ (g • x = y) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp only [e, hs g]

lemma wk_sum_one (hμ : ThompsonAmenability.IsProbability μ) :
    ∑ g ∈ μ.support, μ g = 1 := hμ.2

lemma wk_summable (x : X) : Summable (walkKernel (μ : ↥(wobbling X) → ℝ) x) := by
  have : walkKernel (μ : ↥(wobbling X) → ℝ) x =
      fun y => ∑ g ∈ μ.support, if g • x = y then μ g else 0 := funext (wk_eq μ x)
  rw [this]
  refine summable_sum fun g _ => ?_
  exact (hasSum_ite_eq (g • x) (μ g)).summable.congr fun y => by
    by_cases h : g • x = y
    · subst h; simp
    · simp [h, Ne.symm h]

lemma wk_tsum (hμ : ThompsonAmenability.IsProbability μ) (x : X) :
    ∑' y, walkKernel (μ : ↥(wobbling X) → ℝ) x y = 1 := by
  have : walkKernel (μ : ↥(wobbling X) → ℝ) x =
      fun y => ∑ g ∈ μ.support, if g • x = y then μ g else 0 := funext (wk_eq μ x)
  rw [this, Summable.tsum_finsetSum]
  · rw [← wk_sum_one hμ]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [tsum_eq_single (g • x)]
    · simp
    · intro y hy; simp [Ne.symm hy]
  · intro g _
    exact (hasSum_ite_eq (g • x) (μ g)).summable.congr fun y => by
      by_cases h : g • x = y
      · subst h; simp
      · simp [h, Ne.symm h]

lemma wk_le_one (hμ : ThompsonAmenability.IsProbability μ) (x y : X) :
    walkKernel (μ : ↥(wobbling X) → ℝ) x y ≤ 1 := by
  rw [wk_eq, ← wk_sum_one hμ]
  exact Finset.sum_le_sum fun g _ => by split_ifs; exacts [le_rfl, hμ.1 g]

lemma wk_pos (hμ : ThompsonAmenability.IsProbability μ) (x : X) :
    ∃ y, 0 < walkKernel (μ : ↥(wobbling X) → ℝ) x y := by
  have : ∃ g ∈ μ.support, 0 < μ g := by
    by_contra h
    push Not at h
    have : ∑ g ∈ μ.support, μ g ≤ 0 := Finset.sum_nonpos h
    rw [wk_sum_one hμ] at this
    norm_num at this
  obtain ⟨g, hg, hpos⟩ := this
  refine ⟨g • x, lt_of_lt_of_le hpos ?_⟩
  rw [wk_eq]
  have := Finset.single_le_sum (f := fun h : ↥(wobbling X) => if h • x = g • x then μ h else 0)
    (fun h _ => by split_ifs; exacts [hμ.1 h, le_rfl]) hg
  simpa using this

lemma wk_isNet (hμ : ThompsonAmenability.IsProbability μ) (hs : IsSymmetric μ) :
    LP.IsNet (walkKernel (μ : ↥(wobbling X) → ℝ) : X → X → ℝ) :=
  ⟨wk_nonneg hμ, wk_symm hs, wk_pos hμ, wk_summable⟩

lemma networkWalk_wk (hμ : ThompsonAmenability.IsProbability μ) :
    networkWalk (walkKernel (μ : ↥(wobbling X) → ℝ) : X → X → ℝ) =
      walkKernel (μ : ↥(wobbling X) → ℝ) := by
  funext x y
  unfold networkWalk
  rw [wk_tsum hμ, div_one]

lemma wk_dist {C : ℝ} (hC : ∀ g ∈ μ.support, ∀ x : X, dist (g • x) x ≤ C) {x y : X}
    (h : 0 < walkKernel (μ : ↥(wobbling X) → ℝ) x y) : dist y x ≤ C := by
  rw [wk_eq] at h
  obtain ⟨g, hg, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  have hgx : g • x = y := by by_contra hc; simp [hc] at hne
  rw [← hgx]; exact hC g hg x

lemma exists_disp (μ : ↥(wobbling X) →₀ ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ μ.support, ∀ x : X, dist (g • x) x ≤ C := by
  have hg : ∀ g : ↥(wobbling X), ∃ C : ℝ, ∀ x : X, dist (g • x) x ≤ C := fun g => g.2
  choose Cg hCg using hg
  refine ⟨∑ g ∈ μ.support, |Cg g|, Finset.sum_nonneg fun g _ => abs_nonneg _, ?_⟩
  intro g hg x
  calc dist (g • x) x ≤ Cg g := hCg g x
    _ ≤ |Cg g| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f := fun g => |Cg g|) (fun g _ => abs_nonneg _) hg

lemma dist_swap_le (x₀ x₁ x : X) : dist (Equiv.swap x₀ x₁ x) x ≤ dist x₀ x₁ := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; rw [dist_comm]
  · subst h2; exact le_rfl
  · simp

theorem isRecurrentAction (hX : HasBoundedGeometry X) (x₀ : X) (h : IsRecurrentSpace X x₀) :
    IsRecurrentAction (↥(wobbling X)) X := by
  intro μ hμ hs x₁
  by_contra hnot
  obtain ⟨C, hC0, hC⟩ := exists_disp μ
  set D := dist x₀ x₁
  set R : ℝ := C + 2 * D + 1 with hRdef
  have hR : 0 < R := by have := dist_nonneg (x := x₀) (y := x₁); positivity
  set φ : X → X := ⇑(Equiv.swap x₀ x₁) with hφ
  have hφφ : ∀ x, φ (φ x) = x := fun x => Equiv.swap_apply_self _ _ _
  have hφinj : Function.Injective φ := (Equiv.swap x₀ x₁).injective
  have hdφ : ∀ x y, dist (φ x) (φ y) ≤ dist x y + 2 * D := by
    intro x y
    calc dist (φ x) (φ y) ≤ dist (φ x) x + dist x y + dist y (φ y) := dist_triangle4 _ _ _ _
      _ ≤ D + dist x y + D := by
          gcongr
          · exact dist_swap_le x₀ x₁ x
          · rw [dist_comm]; exact dist_swap_le x₀ x₁ y
      _ = dist x y + 2 * D := by ring
  have hc'pos : ∀ x y, 0 < walkKernel (μ : ↥(wobbling X) → ℝ) x y →
      0 < ballNet R (φ x) (φ y) := by
    intro x y hxy
    have h1 := wk_dist hC hxy
    have h2 := hdφ y x
    simp only [ballNet, Metric.mem_closedBall]
    rw [if_pos (by linarith)]
    norm_num
  have hrough : IsRoughEmbedding (walkKernel (μ : ↥(wobbling X) → ℝ)) (ballNet R) φ := by
    refine ⟨1, 1, fun x y => [φ x, φ y], ?_, ?_⟩
    · intro x y hxy hpos
      have hne : φ x ≠ φ y := fun e => hxy (hφinj e)
      have hb := hc'pos x y hpos
      have hb1 : ballNet R (φ x) (φ y) = 1 := by
        unfold ballNet at hb ⊢; split_ifs at hb ⊢ <;> first | rfl | norm_num at hb
      have hle := wk_le_one hμ x y
      refine ⟨le_rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
      · simp [hne]
      · intro e he
        simp only [pathEdges, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
          List.mem_singleton] at he
        subst he; exact hb
      · simp only [pathEdges, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hb1]
        rw [one_mul, add_zero, div_one]
        rw [le_div_iff₀ hpos]; simpa using hle
    · intro u v _
      have hsub : {p : X × X | p.1 ≠ p.2 ∧ 0 < walkKernel (μ : ↥(wobbling X) → ℝ) p.1 p.2 ∧
          (u, v) ∈ pathEdges [φ p.1, φ p.2]} ⊆ {(φ u, φ v)} := by
        rintro ⟨a, b⟩ ⟨_, _, hab⟩
        simp only [pathEdges, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
          List.mem_singleton, Prod.mk.injEq] at hab
        obtain ⟨rfl, rfl⟩ := hab
        simp [hφφ]
      refine ⟨?_, (Set.finite_singleton _).subset hsub⟩
      calc _ ≤ ({(φ u, φ v)} : Set (X × X)).ncard :=
            Set.ncard_le_ncard hsub (Set.finite_singleton _)
        _ = 1 := Set.ncard_singleton _
  have key := LP.transfer _ _ (wk_isNet hμ hs) (ballNet_isNet hX hR) φ hrough x₁
    (by rwa [networkWalk_wk hμ])
  rw [networkWalk_ballNet hX hR] at key
  have hφx : φ x₁ = x₀ := Equiv.swap_apply_right _ _
  rw [hφx] at key
  exact key (h R hR)

end Rec

/-! ## Part 1b: extensive amenability gives an amenable lamplighter action -/

section Lamp

variable {G X : Type*} [Group G] [MulAction G X]

/-- The support of a lamp configuration. -/
def supp (f : Multiplicative (X →₀ ZMod 2)) : Set X := ↑(Multiplicative.toAdd f).support

lemma supp_finite (f : Multiplicative (X →₀ ZMod 2)) : (supp f).Finite := Finset.finite_toSet _

lemma toAdd_smul (p : Lamplighter G X) (f : Multiplicative (X →₀ ZMod 2)) :
    Multiplicative.toAdd (p • f) = Multiplicative.toAdd p.left +
      Finsupp.mapDomain (fun x => p.right • x) (Multiplicative.toAdd f) := rfl

lemma supp_mapDomain (g : G) (f : X →₀ ZMod 2) :
    (↑(Finsupp.mapDomain (fun x => g • x) f).support : Set X) = (fun x => g • x) '' ↑f.support := by
  rw [Finsupp.mapDomain_support_of_injective (MulAction.injective g), Finset.coe_image]

lemma toAdd_inl_smul (a : Multiplicative (X →₀ ZMod 2)) (c : Multiplicative (X →₀ ZMod 2)) :
    Multiplicative.toAdd ((SemidirectProduct.inl a : Lamplighter G X) • c) =
      Multiplicative.toAdd a + Multiplicative.toAdd c := by
  rw [toAdd_smul]
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, one_smul]
  rw [show (fun x : X => x) = id from rfl, Finsupp.mapDomain_id]

/-- Configurations supported in `E`. -/
def Cf (E : Set X) : Set (Multiplicative (X →₀ ZMod 2)) := {f | supp f ⊆ E}

lemma smul_mem_Cf (p : Lamplighter G X) {E : Set X} (hp : supp p.left ⊆ E)
    (f : Multiplicative (X →₀ ZMod 2)) :
    p • f ∈ Cf E ↔ f ∈ Cf ((fun x => p.right • x) ⁻¹' E) := by
  simp only [Cf, Set.mem_setOf_eq, supp, toAdd_smul]
  set a := Multiplicative.toAdd p.left
  set b := Finsupp.mapDomain (fun x => p.right • x) (Multiplicative.toAdd f)
  have hb : (↑b.support : Set X) ⊆ E ↔ (↑(Multiplicative.toAdd f).support : Set X) ⊆
      (fun x => p.right • x) ⁻¹' E := by
    rw [supp_mapDomain, Set.image_subset_iff]
  rw [← hb]
  have ha : (↑a.support : Set X) ⊆ E := hp
  constructor
  · intro h
    have e : b = (a + b) - a := by abel
    rw [e]
    intro x hx
    have := Finsupp.support_sub hx
    rcases Finset.mem_union.1 this with h1 | h1
    · exact h h1
    · exact ha h1
  · intro h x hx
    rcases Finset.mem_union.1 (Finsupp.support_add hx) with h1 | h1
    · exact ha h1
    · exact h h1

lemma Cf_finite (E : Finset X) : (Cf (E : Set X)).Finite := by
  apply Set.Finite.of_finite_image (f := fun f : Multiplicative (X →₀ ZMod 2) =>
    fun x : E => Multiplicative.toAdd f x)
  · exact Set.toFinite _
  · intro f hf f' hf' e
    apply Multiplicative.toAdd.injective
    ext x
    by_cases hx : x ∈ E
    · exact congrFun e ⟨x, hx⟩
    · have h1 : x ∉ (Multiplicative.toAdd f).support := fun h => hx (hf h)
      have h2 : x ∉ (Multiplicative.toAdd f').support := fun h => hx (hf' h)
      rw [Finsupp.notMem_support_iff] at h1 h2
      rw [h1, h2]

lemma one_mem_Cf (E : Set X) : (1 : Multiplicative (X →₀ ZMod 2)) ∈ Cf E := by
  simp [Cf, supp]

lemma Cf_ncard_pos (E : Finset X) : 0 < (Cf (E : Set X)).ncard :=
  (Set.ncard_pos (Cf_finite E)).2 ⟨1, one_mem_Cf _⟩

/-- The uniform probability on the configurations supported in `E`. -/
noncomputable def nu (E : Finset X) (S : Set (Multiplicative (X →₀ ZMod 2))) : ℝ :=
  ((S ∩ Cf (E : Set X)).ncard : ℝ) / (Cf (E : Set X)).ncard

lemma nu_nonneg (E : Finset X) (S) : 0 ≤ nu E S := by unfold nu; positivity

lemma nu_le_one (E : Finset X) (S) : nu E S ≤ 1 := by
  unfold nu
  rw [div_le_one (by exact_mod_cast Cf_ncard_pos E)]
  exact_mod_cast Set.ncard_le_ncard Set.inter_subset_right (Cf_finite E)

lemma nu_union (E : Finset X) {S T : Set (Multiplicative (X →₀ ZMod 2))} (h : Disjoint S T) :
    nu E (S ∪ T) = nu E S + nu E T := by
  unfold nu
  rw [← add_div, Set.union_inter_distrib_right, Set.ncard_union_eq
    (h.mono Set.inter_subset_left Set.inter_subset_left)
    ((Cf_finite E).subset Set.inter_subset_right) ((Cf_finite E).subset Set.inter_subset_right)]
  push_cast; rfl

lemma nu_univ (E : Finset X) : nu E Set.univ = 1 := by
  unfold nu
  rw [Set.univ_inter, div_self]
  exact_mod_cast (Cf_ncard_pos E).ne'

lemma nu_empty (E : Finset X) : nu E ∅ = 0 := by simp [nu]

/-- Translating a finite set of `X` by `g`. -/
def act (g : G) (E : Finset X) : Finset X := E.map (MulAction.toPerm g).toEmbedding

lemma coe_act_inv (g : G) (E : Finset X) :
    ((act g⁻¹ E : Finset X) : Set X) = (fun x => g • x) ⁻¹' (E : Set X) := by
  ext x
  simp only [act, Finset.coe_map, Set.mem_image, Finset.mem_coe, Set.mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g • x, hx, by simp⟩

lemma smul_inter_Cf (p : Lamplighter G X) {E : Finset X} (hp : supp p.left ⊆ E)
    (S : Set (Multiplicative (X →₀ ZMod 2))) :
    p • S ∩ Cf (E : Set X) = p • (S ∩ Cf (act p.right⁻¹ E : Set X)) := by
  ext f
  rw [Set.smul_set_inter, Set.mem_inter_iff, Set.mem_inter_iff]
  refine and_congr Iff.rfl ?_
  rw [Set.mem_smul_set_iff_inv_smul_mem, coe_act_inv, ← smul_mem_Cf p hp, smul_inv_smul]

lemma nu_smul (p : Lamplighter G X) {E : Finset X} (hp : supp p.left ⊆ E)
    (S : Set (Multiplicative (X →₀ ZMod 2))) :
    nu E (p • S) = nu (act p.right⁻¹ E) S := by
  unfold nu
  have h1 := smul_inter_Cf p hp S
  have h2 := smul_inter_Cf p hp Set.univ
  rw [Set.smul_set_univ, Set.univ_inter, Set.univ_inter] at h2
  rw [h1, h2, ← Set.image_smul, ← Set.image_smul,
    Set.ncard_image_of_injective _ (MulAction.injective p),
    Set.ncard_image_of_injective _ (MulAction.injective p)]

lemma fa_compl_zero {α : Type*} {m : Set α → ℝ≥0∞} (hm : Garrido.IsFinitelyAdditiveMeasure m)
    (h1 : m Set.univ = 1) {A : Set α} (hA : m A = 1) : m Aᶜ = 0 := by
  have := hm.2 A Aᶜ disjoint_compl_right
  rw [Set.union_compl_self, h1, hA] at this
  have h' : (1 : ℝ≥0∞) + m Aᶜ = 1 + 0 := by rw [add_zero]; exact this.symm
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h'

theorem isAmenableAction_lamplighter (h : IsExtensivelyAmenable G X) :
    IsAmenableAction (Lamplighter G X) (Multiplicative (X →₀ ZMod 2)) := by
  obtain ⟨m, hm, -, h1, hinv, hsup⟩ := h
  refine ⟨fun S => ENNReal.ofReal (integ m fun E => nu E S), ⟨?_, ?_⟩, ?_, ?_⟩
  · have : (fun E : Finset X => nu E ∅) = (∅ : Set (Finset X)).indicator 1 := by
      funext E; simp [nu_empty]
    simp only [this, integ_indicator hm h1, hm.1, ENNReal.toReal_zero, ENNReal.ofReal_zero]
  · intro S T hST
    have : (fun E : Finset X => nu E (S ∪ T)) = (fun E => nu E S) + (fun E => nu E T) := by
      funext E; simp [nu_union E hST]
    simp only [this]
    rw [integ_add hm h1 (fun E => nu_nonneg E S) (fun E => nu_nonneg E T)
      (fun E => by rw [← nu_union E hST]; exact nu_le_one E _)]
    exact ENNReal.ofReal_add (integ_nonneg_le_one hm h1 (nu_nonneg · S) (nu_le_one · S)).1
      (integ_nonneg_le_one hm h1 (nu_nonneg · T) (nu_le_one · T)).1
  · have : (fun E : Finset X => nu E Set.univ) = (Set.univ : Set (Finset X)).indicator 1 := by
      funext E; simp [nu_univ]
    simp only [this, integ_indicator hm h1, h1, ENNReal.toReal_one, ENNReal.ofReal_one]
  · intro p S
    dsimp only
    congr 1
    set τ : Finset X ≃ Finset X := Equiv.finsetCongr (MulAction.toPerm p.right⁻¹ : Equiv.Perm X)
    have hτ : ∀ T : Set (Finset X), m (τ '' T) = m T := by
      intro T
      have e : (τ : Finset X → Finset X) =
          fun E => E.map (MulAction.toPerm p.right⁻¹ : Equiv.Perm X).toEmbedding := by
        funext E; rfl
      rw [e]; exact hinv _ T
    rw [← integ_comp_equiv τ hτ (fun E => nu E S)]
    apply integ_congr hm h1
    set E₀ := (Multiplicative.toAdd p.left).support
    have hz : m {E | E₀ ⊆ E}ᶜ = 0 :=
      fa_compl_zero hm h1 (hsup E₀ (Set.subset_univ _))
    refine le_antisymm (le_trans (fa_mono hm ?_) hz.le) zero_le
    intro E hE
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    intro hsub
    apply hE
    show nu E (p • S) = nu (τ E) S
    rw [nu_smul p (fun x hx => Finset.mem_coe.2 (hsub hx))]
    rfl

end Lamp

/-! ## Part 3: a Lipschitz binary tree makes the lamplighter action non-amenable -/

section Tree

/-- Two-bit codes of the three letters. -/
def code (s : Fin 3) : List Bool := [decide (s = 2), decide (s = 1)]

lemma code_injective : Function.Injective code := by
  unfold code; decide

/-- A word (newest letter first) as a binary word (oldest letter first). -/
def enc : List (Fin 3) → List Bool
  | [] => []
  | s :: w => enc w ++ code s

lemma enc_length (w : List (Fin 3)) : (enc w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons s w ih => simp [enc, ih, code]; ring

lemma enc_injective : Function.Injective enc := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons t v =>
      have := congrArg List.length h
      simp [enc, code] at this
  | cons s u ih =>
    intro v h
    cases v with
    | nil =>
      have := congrArg List.length h
      simp [enc, code] at this
    | cons t v =>
      have hl := congrArg List.length h
      simp only [enc, List.length_append, enc_length, code, List.length_cons,
        List.length_nil] at hl
      have hl' : (enc u).length = (enc v).length := by rw [enc_length, enc_length]; omega
      obtain ⟨h1, h2⟩ := List.append_inj h hl'
      rw [ih h1, code_injective h2]

lemma tw_left (u v : List Bool) :
    ((u.zip (u ++ v)).takeWhile fun p => decide (p.1 = p.2)).length = u.length := by
  induction u with
  | nil => simp
  | cons a u ih => simp [List.zip_cons_cons, List.takeWhile_cons, ih]

lemma tw_right (u v : List Bool) :
    (((u ++ v).zip u).takeWhile fun p => decide (p.1 = p.2)).length = u.length := by
  induction u with
  | nil => simp
  | cons a u ih => simp [List.zip_cons_cons, List.takeWhile_cons, ih]

lemma btd_left (u v : List Bool) : binaryTreeDist u (u ++ v) = v.length := by
  unfold binaryTreeDist
  rw [tw_left, List.length_append]; omega

lemma btd_right (u v : List Bool) : binaryTreeDist (u ++ v) u = v.length := by
  unfold binaryTreeDist
  rw [tw_right, List.length_append]; omega

/-- Reduced words of `ℤ/2 * ℤ/2 * ℤ/2`, newest letter first. -/
abbrev RW := {w : List (Fin 3) // w.IsChain (· ≠ ·)}

/-- Right multiplication by the generator `s`. -/
def rr (s : Fin 3) (w : RW) : RW :=
  if h : w.1.head? = some s then ⟨w.1.tail, w.2.tail⟩
  else ⟨s :: w.1, List.isChain_cons.2 ⟨fun y hy => by
    rintro rfl; exact h (Option.mem_def.1 hy), w.2⟩⟩

lemma rr_cons_of_head (s : Fin 3) (l : List (Fin 3)) (hl : (s :: l).IsChain (· ≠ ·)) :
    rr s ⟨s :: l, hl⟩ = ⟨l, hl.tail⟩ := by
  simp [rr]

lemma head_ne_of_chain {s : Fin 3} {l : List (Fin 3)} (hl : (s :: l).IsChain (· ≠ ·)) :
    l.head? ≠ some s := by
  intro h
  have := (List.isChain_cons.1 hl).1 s h
  exact this rfl

lemma rr_invol (s : Fin 3) : Function.Involutive (rr s) := by
  rintro ⟨l, hl⟩
  by_cases h : l.head? = some s
  · obtain ⟨l', rfl⟩ : ∃ l', l = s :: l' := by
      cases l with
      | nil => simp at h
      | cons a l' => simp at h; exact ⟨l', by rw [h]⟩
    rw [rr_cons_of_head]
    unfold rr
    rw [dif_neg (head_ne_of_chain hl)]
  · have : rr s ⟨l, hl⟩ = ⟨s :: l, List.isChain_cons.2 ⟨fun y hy => by
        rintro rfl; exact h (Option.mem_def.1 hy), hl⟩⟩ := by
      simp [rr, h]
    rw [this, rr_cons_of_head]

lemma btd_rr (s : Fin 3) (w : RW) : binaryTreeDist (enc (rr s w).1) (enc w.1) = 2 := by
  obtain ⟨l, hl⟩ := w
  by_cases h : l.head? = some s
  · obtain ⟨l', rfl⟩ : ∃ l', l = s :: l' := by
      cases l with
      | nil => simp at h
      | cons a l' => simp at h; exact ⟨l', by rw [h]⟩
    rw [rr_cons_of_head]
    simp only [enc]
    rw [btd_left]; rfl
  · have : (rr s ⟨l, hl⟩).1 = s :: l := by simp [rr, h]
    rw [this]
    simp only [enc]
    rw [btd_right]; rfl

/-- The heads `A_s`. -/
def headSet (s : Fin 3) : Set RW := {w | w.1.head? = some s}

lemma preimage_headSet (s : Fin 3) : rr s ⁻¹' headSet s = (headSet s)ᶜ := by
  ext ⟨l, hl⟩
  simp only [Set.mem_preimage, headSet, Set.mem_compl_iff, Set.mem_setOf_eq]
  by_cases h : l.head? = some s
  · obtain ⟨l', rfl⟩ : ∃ l', l = s :: l' := by
      cases l with
      | nil => simp at h
      | cons a l' => simp at h; exact ⟨l', by rw [h]⟩
    rw [rr_cons_of_head]
    simp only [List.head?_cons, not_true_eq_false, iff_false]
    exact head_ne_of_chain hl
  · have : (rr s ⟨l, hl⟩).1 = s :: l := by simp [rr, h]
    rw [this]; simp [h]

variable {X : Type*} [MetricSpace X]

section Embedded

variable (f : List Bool → X) (hf : Function.Injective f)

/-- The reduced words placed in `X`. -/
def ψ (w : RW) : X := f (enc w.1)

include hf in
lemma ψ_injective : Function.Injective (ψ f) := fun u v h =>
  Subtype.ext (enc_injective (hf h))

/-- The involution of `X` induced by `rr s`, the identity off the image of `ψ`. -/
noncomputable def tau (s : Fin 3) (x : X) : X :=
  if h : ∃ w, ψ f w = x then ψ f (rr s h.choose) else x

include hf in
lemma tau_ψ (s : Fin 3) (w : RW) : tau f s (ψ f w) = ψ f (rr s w) := by
  have h : ∃ w', ψ f w' = ψ f w := ⟨w, rfl⟩
  rw [tau, dif_pos h, ψ_injective f hf h.choose_spec]

include hf in
lemma tau_invol (s : Fin 3) : Function.Involutive (tau f s) := by
  intro x
  by_cases h : ∃ w, ψ f w = x
  · obtain ⟨w, rfl⟩ := h
    rw [tau_ψ f hf, tau_ψ f hf, rr_invol]
  · have hx : tau f s x = x := by rw [tau, dif_neg h]
    rw [hx, hx]

/-- `tau s` as a permutation. -/
noncomputable def sig (s : Fin 3) : Equiv.Perm X := Function.Involutive.toPerm _ (tau_invol f hf s)

lemma sig_mem {C : ℝ} (hC : ∀ u v, dist (f u) (f v) ≤ C * binaryTreeDist u v) (s : Fin 3) :
    sig f hf s ∈ wobbling X := by
  refine ⟨max (C * 2) 0, fun x => ?_⟩
  show dist (tau f s x) x ≤ _
  by_cases h : ∃ w, ψ f w = x
  · obtain ⟨w, rfl⟩ := h
    rw [tau_ψ f hf]
    have := hC (enc (rr s w).1) (enc w.1)
    rw [btd_rr] at this
    exact le_trans (by simpa [ψ] using this) (le_max_left _ _)
  · rw [tau, dif_neg h, dist_self]; exact le_max_right _ _

end Embedded

/-- The lit lamps on the tree. -/
def Dset (f : List Bool → X) (c : Multiplicative (X →₀ ZMod 2)) : Set RW := ψ f ⁻¹' supp c

lemma Dset_finite (f : List Bool → X) (hf : Function.Injective f) (c) : (Dset f c).Finite :=
  (supp_finite c).preimage (ψ_injective f hf).injOn

/-- The proportion of lit tree lamps lying in `A`. -/
noncomputable def phi (f : List Bool → X) (A : Set RW) (c : Multiplicative (X →₀ ZMod 2)) : ℝ :=
  ((Dset f c ∩ A).ncard : ℝ) / (Dset f c).ncard

lemma phi_nonneg (f : List Bool → X) (A c) : 0 ≤ phi f A c := by unfold phi; positivity

lemma phi_le_one (f : List Bool → X) (hf : Function.Injective f) (A c) : phi f A c ≤ 1 := by
  unfold phi
  rcases Nat.eq_zero_or_pos (Dset f c).ncard with h | h
  · rw [h]; simp
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left (Dset_finite f hf c)

lemma phi_union (f : List Bool → X) (hf : Function.Injective f) {A B : Set RW}
    (h : Disjoint A B) (c) : phi f (A ∪ B) c = phi f A c + phi f B c := by
  unfold phi
  rw [← add_div, Set.inter_union_distrib_left, Set.ncard_union_eq
    (h.mono Set.inter_subset_right Set.inter_subset_right)
    ((Dset_finite f hf c).subset Set.inter_subset_left)
    ((Dset_finite f hf c).subset Set.inter_subset_left)]
  push_cast; rfl

theorem part3_core (f : List Bool → X) (C : ℝ) (hf : Function.Injective f)
    (hC : ∀ u v, dist (f u) (f v) ≤ C * binaryTreeDist u v) :
    ¬ IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2)) := by
  rintro ⟨m, hm, h1, hinv⟩
  set ν : Set RW → ℝ := fun A => integ m (phi f A) with hν
  have hν0 : ∀ A, 0 ≤ ν A := fun A =>
    (integ_nonneg_le_one hm h1 (phi_nonneg f A) (phi_le_one f hf A)).1
  have hνu : ∀ A B, Disjoint A B → ν (A ∪ B) = ν A + ν B := by
    intro A B hAB
    simp only [hν]
    rw [show phi f (A ∪ B) = phi f A + phi f B from funext (phi_union f hf hAB)]
    exact integ_add hm h1 (phi_nonneg f A) (phi_nonneg f B)
      (fun c => by rw [← phi_union f hf hAB]; exact phi_le_one f hf _ c)
  -- invariance under the three involutions
  have hνr : ∀ (s : Fin 3) (A : Set RW), ν (rr s ⁻¹' A) = ν A := by
    intro s A
    set h : ↥(wobbling X) := ⟨sig f hf s, sig_mem f hf hC s⟩
    set p : Lamplighter ↥(wobbling X) X := SemidirectProduct.inr h
    have hτ : ∀ S, m ((MulAction.toPerm p : Equiv.Perm _) '' S) = m S := by
      intro S
      have : ((MulAction.toPerm p : Equiv.Perm _) '' S) = p • S := by
        rw [← Set.image_smul]; rfl
      rw [this]; exact hinv p S
    have hcomp : phi f (rr s ⁻¹' A) ∘ (MulAction.toPerm p : Equiv.Perm _) = phi f A := by
      funext c
      have hsupp : supp (p • c) = tau f s '' supp c := by
        simp only [supp, toAdd_smul]
        rw [show p.left = 1 from rfl, toAdd_one, zero_add, supp_mapDomain]
        rfl
      have hD : Dset f (p • c) = rr s ⁻¹' Dset f c := by
        ext w
        simp only [Dset, Set.mem_preimage, hsupp]
        rw [(tau_invol f hf s).image_eq_preimage_symm, Set.mem_preimage, tau_ψ f hf]
      have hpre : ∀ T : Set RW, (rr s ⁻¹' T).ncard = T.ncard := by
        intro T
        rw [← (rr_invol s).image_eq_preimage_symm,
          Set.ncard_image_of_injective _ (rr_invol s).injective]
      show phi f (rr s ⁻¹' A) (p • c) = phi f A c
      unfold phi
      rw [hD, ← Set.preimage_inter, hpre, hpre]
    simp only [hν]
    rw [← hcomp, integ_comp_equiv _ hτ]
  have hhalf : ∀ s : Fin 3, ν Set.univ = 2 * ν (headSet s) := by
    intro s
    have := hνu (headSet s) (headSet s)ᶜ disjoint_compl_right
    rw [Set.union_compl_self, ← preimage_headSet, hνr] at this
    rw [this]; ring
  have hpos : 0 < ν Set.univ := by
    set w₀ : RW := ⟨[], List.IsChain.nil⟩
    set y : X := ψ f w₀
    set N : Set (Multiplicative (X →₀ ZMod 2)) := {c | Multiplicative.toAdd c y ≠ 0}
    set q : Lamplighter ↥(wobbling X) X :=
      SemidirectProduct.inl (Multiplicative.ofAdd (Finsupp.single y 1))
    have hq : ∀ c : Multiplicative (X →₀ ZMod 2),
        Multiplicative.toAdd (q • c) = Finsupp.single y (1 : ZMod 2) + Multiplicative.toAdd c :=
      fun c => toAdd_inl_smul _ c
    have hqZ : q • Nᶜ = N := by
      ext c
      constructor
      · rintro ⟨z, hz, rfl⟩
        simp only [N, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz ⊢
        rw [hq, Finsupp.add_apply, Finsupp.single_eq_same, hz]
        decide
      · intro hc
        refine ⟨q • c, ?_, ?_⟩
        · simp only [N, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hc ⊢
          rw [hq, Finsupp.add_apply, Finsupp.single_eq_same]
          revert hc; generalize Multiplicative.toAdd c y = a; revert a; decide
        · apply Multiplicative.toAdd.injective
          rw [hq, hq, ← add_assoc, ← Finsupp.single_add,
            show (1 + 1 : ZMod 2) = 0 from rfl, Finsupp.single_zero, zero_add]
    have hmN : m N ≠ 0 := by
      intro h0
      have e1 := hinv q Nᶜ
      rw [hqZ, h0] at e1
      have e2 := hm.2 N Nᶜ disjoint_compl_right
      rw [Set.union_compl_self, h1, h0, ← e1, add_zero] at e2
      exact one_ne_zero e2
    have hphi : phi f Set.univ = {c | (Dset f c).Nonempty}.indicator 1 := by
      funext c
      unfold phi
      rw [Set.inter_univ]
      by_cases hne : (Dset f c).Nonempty
      · rw [Set.indicator_of_mem (show c ∈ {c | (Dset f c).Nonempty} from hne), div_self]
        · rfl
        · exact_mod_cast ((Set.ncard_pos (Dset_finite f hf c)).2 hne).ne'
      · rw [Set.indicator_of_notMem (show c ∉ {c | (Dset f c).Nonempty} from hne)]
        rw [Set.not_nonempty_iff_eq_empty] at hne
        simp [hne]
    have hsub : N ⊆ {c | (Dset f c).Nonempty} := by
      intro c hc
      exact ⟨w₀, show y ∈ supp c from Finsupp.mem_support_iff.2 hc⟩
    simp only [hν, hphi, integ_indicator hm h1]
    refine lt_of_lt_of_le ?_ (fa_toReal_mono hm h1 hsub)
    exact ENNReal.toReal_pos hmN (fa_ne_top hm h1 N)
  have hdisj : ∀ s t : Fin 3, s ≠ t → Disjoint (headSet s) (headSet t) := by
    intro s t hst
    rw [Set.disjoint_left]
    intro w hs ht
    simp only [headSet, Set.mem_setOf_eq] at hs ht
    rw [hs] at ht
    exact hst (Option.some.inj ht)
  have hsum : ν Set.univ ≥ ν (headSet 0) + ν (headSet 1) + ν (headSet 2) := by
    have e1 := hνu (headSet 0) (headSet 1) (hdisj 0 1 (by decide))
    have e2 := hνu (headSet 0 ∪ headSet 1) (headSet 2)
      (Disjoint.union_left (hdisj 0 2 (by decide)) (hdisj 1 2 (by decide)))
    have e3 := hνu (headSet 0 ∪ headSet 1 ∪ headSet 2) (headSet 0 ∪ headSet 1 ∪ headSet 2)ᶜ
      disjoint_compl_right
    rw [Set.union_compl_self] at e3
    rw [e3, e2, e1]
    linarith [hν0 (headSet 0 ∪ headSet 1 ∪ headSet 2)ᶜ]
  have h0 := hhalf 0
  have h1' := hhalf 1
  have h2 := hhalf 2
  linarith

end Tree

theorem part1 {X : Type*} [MetricSpace X] (hX : HasBoundedGeometry X) :
    ∀ x₀ : X, IsRecurrentSpace X x₀ →
      IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2)) :=
  fun x₀ h => isAmenableAction_lamplighter
    (JMMS.isExtensivelyAmenable_of_isRecurrentAction (isRecurrentAction hX x₀ h))

theorem part3 {X : Type*} [MetricSpace X] (hX : HasBoundedGeometry X) :
    ContainsLipschitzBinaryTree X →
      ¬ IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2)) := by
  rintro ⟨f, C, hf, hC⟩
  exact part3_core f C hf hC

end JuschenkoDeLaSalle.IETJ13

end

section

/-! JdlS Theorem 1.4, part 2, with monotone controls: a space with bounded geometry that coarsely
embeds in `ℤ²` (with the standard notion of coarse embedding) is recurrent. Parts 1, 2 and 5 below
are copied from `Solutions/IET/Lemma52.lean`. -/

open IntervalExchange

namespace JuschenkoDeLaSalle.IETJ2

open Classical

/-! ## Part 1: generic Markov-chain bookkeeping -/

section Markov

variable {V : Type*} (P : V → V → ℝ) (x : V)

/-- The (sub-probability) of being at `y` at time `t` without having visited `x` at times
`1, …, t`, the chain being at `x` at time `0`. -/
noncomputable def av : ℕ → V → ℝ
  | 0, y => if y = x then 1 else 0
  | t + 1, y => if y = x then 0 else ∑' z, av t z * P z y

variable {P}

lemma hasSum_of_fiber {α β : Type*} (K : α × β → ℝ) (hK : 0 ≤ K) (s : α → ℝ)
    (hs : ∀ a, HasSum (fun b => K (a, b)) (s a)) (hsum : Summable s) (g : β → ℝ)
    (hg : ∀ b, HasSum (fun a => K (a, b)) (g b)) : HasSum g (∑' a, s a) := by
  have hKs : Summable K := by
    rw [summable_prod_of_nonneg hK]
    refine ⟨fun a => (hs a).summable, ?_⟩
    simpa [(hs _).tsum_eq] using hsum
  have h1 : HasSum K (∑' a, s a) := by
    have := hKs.hasSum
    rwa [hKs.tsum_prod' (fun a => (hs a).summable), tsum_congr fun a => (hs a).tsum_eq] at this
  have h2 : HasSum (K ∘ (Equiv.prodComm β α)) (∑' a, s a) :=
    (Equiv.hasSum_iff (Equiv.prodComm β α)).mpr h1
  exact h2.prod_fiberwise fun b => hg b

variable (hP0 : ∀ a b, 0 ≤ P a b) (hP1 : ∀ a, HasSum (P a) 1)
include hP0

lemma av_nonneg : ∀ t y, 0 ≤ av P x t y
  | 0, y => by simp only [av]; split_ifs <;> norm_num
  | t + 1, y => by
    simp only [av]
    split_ifs
    · exact le_rfl
    · exact tsum_nonneg fun z => mul_nonneg (av_nonneg t z) (hP0 z y)

include hP1

lemma P_le_one (a b : V) : P a b ≤ 1 :=
  le_hasSum (hP1 a) b fun c _ => hP0 a c

lemma summable_F (t : ℕ) (ih : Summable (av P x t)) :
    Summable (fun p : V × V => av P x t p.1 * P p.1 p.2) := by
  have hK : 0 ≤ (fun p : V × V => av P x t p.1 * P p.1 p.2) := by
    intro p
    exact mul_nonneg (av_nonneg x hP0 t p.1) (hP0 _ _)
  refine (summable_prod_of_nonneg hK).mpr ⟨fun a => ?_, ?_⟩
  · exact (hP1 a).summable.mul_left (av P x t a)
  refine ih.congr fun a => ?_
  show av P x t a = ∑' y, av P x t a * P a y
  rw [tsum_mul_left, (hP1 a).tsum_eq, mul_one]

/-- Summability of `av t` and the identity `∑ (av (t+1)) + f_t = ∑ (av t)`. -/
lemma av_summable : ∀ t, Summable (av P x t)
  | 0 => by
    refine summable_of_ne_finset_zero (s := {x}) fun y hy => ?_
    simp only [Finset.mem_singleton] at hy
    simp [av, hy]
  | t + 1 => by
    have ih := av_summable t
    have hF := summable_F x hP0 hP1 t ih
    have hG : Summable (fun y => ∑' z, av P x t z * P z y) := hF.prod_symm.prod
    refine Summable.of_nonneg_of_le (fun y => av_nonneg x hP0 (t + 1) y) (fun y => ?_) hG
    simp only [av]
    split_ifs
    · exact tsum_nonneg fun z => mul_nonneg (av_nonneg x hP0 t z) (hP0 z y)
    · exact le_rfl

lemma av_step (t : ℕ) :
    ∑' y, av P x (t + 1) y + ∑' z, av P x t z * P z x = ∑' y, av P x t y := by
  have ih := av_summable x hP0 hP1 t
  have hF := summable_F x hP0 hP1 t ih
  have hG : Summable (fun y => ∑' z, av P x t z * P z y) := hF.prod_symm.prod
  have e1 := hG.tsum_eq_add_tsum_ite x
  have e2 : ∑' y, av P x (t + 1) y = ∑' y, if y = x then 0 else ∑' z, av P x t z * P z y :=
    tsum_congr fun y => rfl
  rw [e2, add_comm, ← e1]
  rw [Summable.tsum_comm' (f := fun z y => av P x t z * P z y) hF
    (fun z => (hP1 z).summable.mul_left (av P x t z))
    (fun y => (hF.prod_symm.prod_factor y))]
  exact tsum_congr fun z => by rw [tsum_mul_left, (hP1 z).tsum_eq, mul_one]

omit hP0 hP1 in
lemma avoidProb_eq_av : ∀ k y, avoidProb P x (k + 1) y = av P x (k + 1) y
  | 0, y => by
    simp only [avoidProb, av]
    split_ifs with h
    · rfl
    · rw [tsum_eq_single x]
      · simp
      · intro z hz; simp [hz]
  | k + 1, y => by
    simp only [avoidProb]
    rw [show av P x (k + 2) y = if y = x then 0 else ∑' z, av P x (k + 1) z * P z y from rfl]
    split_ifs
    · rfl
    · exact tsum_congr fun z => by rw [avoidProb_eq_av k z]

omit hP0 hP1 in
lemma firstReturnProb_eq (t : ℕ) : firstReturnProb P x t = ∑' z, av P x t z * P z x := by
  cases t with
  | zero =>
    simp only [firstReturnProb, av]
    rw [tsum_eq_single x]
    · simp
    · intro z hz; simp [hz]
  | succ k =>
    simp only [firstReturnProb]
    exact tsum_congr fun z => by rw [avoidProb_eq_av x k z]

lemma partial_sum (t : ℕ) :
    ∑ n ∈ Finset.range t, firstReturnProb P x n = 1 - ∑' y, av P x t y := by
  induction t with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, av]
    rw [tsum_eq_single x]
    · simp
    · intro z hz; simp [hz]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, firstReturnProb_eq x, ← av_step x hP0 hP1 t]
    ring

/-- The path-sum description of `av`. -/
lemma path_hasSum : ∀ (t : ℕ) (y : V),
    HasSum (fun ω : Fin (t + 1) → V =>
      if (ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ ({x} : Set V)) ∧ ω (Fin.last t) = y
      then MarkovMixing.pathWeightC P ω else 0) (av P x t y)
  | 0, y => by
    by_cases hy : y = x
    · subst hy
      have : (fun ω : Fin 1 → V =>
          if (ω 0 = y ∧ ∀ i : Fin 1, i ≠ 0 → ω i ∉ ({y} : Set V)) ∧ ω (Fin.last 0) = y
          then MarkovMixing.pathWeightC P ω else 0) = fun ω => if ω = fun _ => y then 1 else 0 := by
        funext ω
        have hw : MarkovMixing.pathWeightC P ω = 1 := by simp [MarkovMixing.pathWeightC]
        have e : (ω = fun _ => y) ↔ ω 0 = y := by
          constructor
          · intro h; rw [h]
          · intro h; funext i; rw [Subsingleton.elim i 0, h]
        rw [hw]
        have : Fin.last 0 = 0 := rfl
        simp only [this]
        by_cases h : ω 0 = y
        · have h' : ω = fun _ => y := e.mpr h
          rw [if_pos h', if_pos]
          refine ⟨⟨h, fun i hi => absurd (Subsingleton.elim i 0) hi⟩, h⟩
        · have h' : ¬ ω = fun _ => y := fun h' => h (e.mp h')
          rw [if_neg h', if_neg]
          exact fun hh => h hh.2
      rw [this]
      have : av P y 0 y = 1 := by simp [av]
      rw [this]
      exact hasSum_ite_eq _ _
    · have : av P x 0 y = 0 := by simp [av, hy]
      rw [this]
      convert hasSum_zero with ω
      split_ifs with h
      · exact absurd (h.2.symm.trans (show ω (Fin.last 0) = x from h.1.1)) hy
      · rfl
  | t + 1, y => by
    by_cases hy : y = x
    · subst hy
      have : av P y (t + 1) y = 0 := by simp [av]
      rw [this]
      convert hasSum_zero with ω
      split_ifs with h
      · exact absurd h.2 (h.1.2 _ (Fin.last_pos.ne'))
      · rfl
    have ih := path_hasSum t
    -- the paths of length `t`, weighted by the last step to `y`
    let g : (Fin (t + 1) → V) → ℝ := fun ω' =>
      (if ω' 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω' i ∉ ({x} : Set V)
        then MarkovMixing.pathWeightC P ω' else 0) * P (ω' (Fin.last t)) y
    have hg : HasSum g (∑' z, av P x t z * P z y) := by
      refine hasSum_of_fiber (fun p : V × (Fin (t + 1) → V) =>
          (if (p.2 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → p.2 i ∉ ({x} : Set V)) ∧
            p.2 (Fin.last t) = p.1 then MarkovMixing.pathWeightC P p.2 else 0) * P p.1 y)
        ?_ (fun z => av P x t z * P z y) (fun z => (ih z).mul_right _) ?_ g ?_
      · intro p
        refine mul_nonneg ?_ (hP0 _ _)
        dsimp only
        split_ifs
        · exact Finset.prod_nonneg fun i _ => hP0 _ _
        · exact le_rfl
      · refine Summable.of_nonneg_of_le (fun z => mul_nonneg (av_nonneg x hP0 t z) (hP0 z y))
          (fun z => ?_) (av_summable x hP0 hP1 t)
        exact mul_le_of_le_one_right (av_nonneg x hP0 t z) (P_le_one hP0 hP1 z y)
      · intro ω'
        convert hasSum_ite_eq (ω' (Fin.last t)) (g ω') using 1
        funext z
        dsimp only [g]
        by_cases hz : z = ω' (Fin.last t)
        · subst hz; simp
        · simp [hz, Ne.symm hz]
    have key : ∀ (y' : V) (ω' : Fin (t + 1) → V),
        (if ((Fin.snoc (α := fun _ => V) ω' y') 0 = x ∧ ∀ i : Fin (t + 2), i ≠ 0 →
            (Fin.snoc (α := fun _ => V) ω' y') i ∉ ({x} : Set V)) ∧
            (Fin.snoc (α := fun _ => V) ω' y') (Fin.last (t + 1)) = y
          then MarkovMixing.pathWeightC P (Fin.snoc (α := fun _ => V) ω' y') else 0) =
          if y' = y then g ω' else 0 := by
      intro y' ω'
      have hw : MarkovMixing.pathWeightC P (Fin.snoc (α := fun _ => V) ω' y') =
          MarkovMixing.pathWeightC P ω' * P (ω' (Fin.last t)) y' := by
        simp only [MarkovMixing.pathWeightC]
        rw [Fin.prod_univ_castSucc]
        congr 1
        · refine Finset.prod_congr rfl fun i _ => ?_
          rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        · rw [Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last]
      have h0 : (Fin.snoc (α := fun _ => V) ω' y') 0 = ω' 0 := by
        rw [show (0 : Fin (t + 2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
      have hall : (∀ i : Fin (t + 2), i ≠ 0 → (Fin.snoc (α := fun _ => V) ω' y') i ∉ ({x} : Set V))
          ↔ (∀ i : Fin (t + 1), i ≠ 0 → ω' i ∉ ({x} : Set V)) ∧ y' ≠ x := by
        rw [Fin.forall_fin_succ']
        simp [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hw, h0, Fin.snoc_last]
      by_cases hy' : y' = y
      · subst hy'
        simp only [g, if_true]
        by_cases hc : ω' 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω' i ∉ ({x} : Set V)
        · rw [if_pos ⟨⟨hc.1, hall.mpr ⟨hc.2, hy⟩⟩, by simp⟩, if_pos hc]
        · rw [if_neg, if_neg hc, zero_mul]
          exact fun h => hc ⟨h.1.1, (hall.mp h.1.2).1⟩
      · rw [if_neg hy', if_neg]
        exact fun h => hy' h.2
    let e := Fin.snocEquiv (fun _ : Fin (t + 2) => V)
    rw [← e.hasSum_iff]
    have hinj : Function.Injective (fun ω' : Fin (t + 1) → V => (y, ω')) :=
      fun a b h => (Prod.ext_iff.mp h).2
    rw [← hinj.hasSum_iff]
    · convert hg using 1
      · funext ω'
        exact (key y ω').trans (if_pos rfl)
      · simp [av, hy]
    · rintro ⟨y', ω'⟩ hp
      have hy' : y' ≠ y := fun h => hp ⟨ω', by simp [h]⟩
      exact (key y' ω').trans (if_neg hy')

lemma returnTailC_eq [Countable V] [DecidableEq V] (t : ℕ) :
    MarkovMixing.returnTailC P x t = ∑' y, av P x t y := by
  let g : (Fin (t + 1) → V) → ℝ := fun ω =>
    if ω 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ ({x} : Set V)
    then MarkovMixing.pathWeightC P ω else 0
  have hg : HasSum g (∑' y, av P x t y) := by
    refine hasSum_of_fiber (fun p : V × (Fin (t + 1) → V) =>
        if (p.2 0 = x ∧ ∀ i : Fin (t + 1), i ≠ 0 → p.2 i ∉ ({x} : Set V)) ∧
          p.2 (Fin.last t) = p.1 then MarkovMixing.pathWeightC P p.2 else 0)
      ?_ (av P x t) (fun y => by convert path_hasSum x hP0 hP1 t y) (av_summable x hP0 hP1 t) g ?_
    · intro p
      dsimp only
      split_ifs
      · exact Finset.prod_nonneg fun i _ => hP0 _ _
      · exact le_rfl
    · intro ω
      convert hasSum_ite_eq (ω (Fin.last t)) (g ω) using 1
      funext z
      dsimp only [g]
      by_cases hz : z = ω (Fin.last t)
      · subst hz; simp
      · simp [hz, Ne.symm hz]
  unfold MarkovMixing.returnTailC MarkovMixing.setAvoidTailC
  rw [← hg.tsum_eq]
  exact tsum_congr fun ω => by simp only [g]; congr

lemma isRecurrentChain_of_recurrent [Countable V] [DecidableEq V]
    (h : MarkovMixing.Recurrent P x) : IsRecurrentChain P x := by
  have hf : ∀ n, 0 ≤ firstReturnProb P x n := fun n => by
    rw [firstReturnProb_eq x]
    exact tsum_nonneg fun z => mul_nonneg (av_nonneg x hP0 n z) (hP0 z x)
  unfold IsRecurrentChain
  rw [hasSum_iff_tendsto_nat_of_nonneg hf]
  have h2 : Filter.Tendsto (fun t => 1 - MarkovMixing.returnTailC P x t) Filter.atTop
      (nhds (1 - 0)) := tendsto_const_nhds.sub h
  rw [sub_zero] at h2
  refine h2.congr fun t => ?_
  rw [partial_sum x hP0 hP1, returnTailC_eq x hP0 hP1]

end Markov

section Translate

variable {V : Type*} [AddCommGroup V] {P : V → V → ℝ}

lemma av_translate (hT : ∀ a b v : V, P (a + v) (b + v) = P a b) (x v : V) :
    ∀ t y, av P (x + v) t (y + v) = av P x t y
  | 0, y => by simp [av]
  | t + 1, y => by
    simp only [av, add_left_inj]
    split_ifs
    · rfl
    · rw [← (Equiv.addRight v).tsum_eq]
      exact tsum_congr fun z => by simp [av_translate hT x v t z, hT]

lemma isRecurrentChain_translate (hT : ∀ a b v : V, P (a + v) (b + v) = P a b) (x v : V)
    (h : IsRecurrentChain P x) : IsRecurrentChain P (x + v) := by
  unfold IsRecurrentChain at *
  convert h using 1
  funext t
  rw [firstReturnProb_eq, firstReturnProb_eq, ← (Equiv.addRight v).tsum_eq]
  exact tsum_congr fun z => by simp [av_translate hT x v t z, hT]

end Translate

/-! ## Part 2: simple random walk on `ℤ²` -/

section SRW

abbrev Z2 := Fin 2 → ℤ

def adj (u v : Z2) : Prop :=
  ∃ j : Fin 2, (∀ i : Fin 2, i ≠ j → v i = u i) ∧ (v j = u j + 1 ∨ v j = u j - 1)

lemma srw_eq (u v : Z2) : MarkovMixing.srwZ 2 u v = if adj u v then 1 / 4 else 0 := by
  unfold MarkovMixing.srwZ adj
  split_ifs <;> norm_num

lemma adj_symm {u v : Z2} (h : adj u v) : adj v u := by
  obtain ⟨j, h1, h2⟩ := h
  exact ⟨j, fun i hi => (h1 i hi).symm, by omega⟩

lemma adj_translate (u v w : Z2) : adj (u + w) (v + w) ↔ adj u v := by
  unfold adj
  simp only [Pi.add_apply, add_left_inj]
  constructor
  · rintro ⟨j, h1, h2⟩; exact ⟨j, h1, by omega⟩
  · rintro ⟨j, h1, h2⟩; exact ⟨j, h1, by omega⟩

lemma srw_translate (u v w : Z2) :
    MarkovMixing.srwZ 2 (u + w) (v + w) = MarkovMixing.srwZ 2 u v := by
  rw [srw_eq, srw_eq, adj_translate]

lemma srw_symm (u v : Z2) : MarkovMixing.srwZ 2 u v = MarkovMixing.srwZ 2 v u := by
  rw [srw_eq, srw_eq]
  congr 1
  exact propext ⟨adj_symm, adj_symm⟩

lemma srw_nonneg (u v : Z2) : 0 ≤ MarkovMixing.srwZ 2 u v := by
  rw [srw_eq]; split_ifs <;> norm_num

lemma srw_hasSum_zero : HasSum (MarkovMixing.srwZ 2 0) 1 := by
  have hs : ∀ v ∉ ({![1, 0], ![-1, 0], ![0, 1], ![0, -1]} : Finset Z2),
      MarkovMixing.srwZ 2 0 v = 0 := by
    intro v hv
    rw [srw_eq, if_neg]
    rintro ⟨j, h1, h2⟩
    apply hv
    simp only [Finset.mem_insert, Finset.mem_singleton]
    fin_cases j
    · have := h1 1 (by decide)
      simp only [Pi.zero_apply] at this h2
      simp only [Fin.zero_eta] at h2
      rcases h2 with h2 | h2
      · left; funext i; fin_cases i <;> simp [this, h2]
      · right; left; funext i; fin_cases i <;> simp [this, h2]
    · have := h1 0 (by decide)
      simp only [Pi.zero_apply] at this h2
      simp only [Fin.mk_one] at h2
      rcases h2 with h2 | h2
      · right; right; left; funext i; fin_cases i <;> simp [this, h2]
      · right; right; right; funext i; fin_cases i <;> simp [this, h2]
  convert hasSum_sum_of_ne_finset_zero hs using 1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [srw_eq]
  rw [if_pos ⟨0, by decide, by decide⟩, if_pos ⟨0, by decide, by decide⟩,
    if_pos ⟨1, by decide, by decide⟩, if_pos ⟨1, by decide, by decide⟩]
  · norm_num
  · infer_instance

lemma srw_hasSum (u : Z2) : HasSum (MarkovMixing.srwZ 2 u) 1 := by
  have : MarkovMixing.srwZ 2 u = (MarkovMixing.srwZ 2 0) ∘ (Equiv.subRight u) := by
    funext v
    simp only [Function.comp_apply, Equiv.subRight_apply]
    rw [← srw_translate 0 (v - u) u]
    simp
  rw [this, Equiv.hasSum_iff]
  exact srw_hasSum_zero

/-! ### Monotone lattice paths in `ℤ²` -/

lemma sign_cases {d : ℤ} (h : d ≠ 0) : d.sign = 1 ∨ d.sign = -1 := by
  rcases lt_or_gt_of_ne h with h | h
  · right; exact Int.sign_eq_neg_one_of_neg h
  · left; exact Int.sign_eq_one_of_pos h

lemma abs_sign_mul (d : ℤ) (m : ℕ) (h : d = 0 → m = 0) : |d.sign * (m : ℤ)| = m := by
  by_cases hd : d = 0
  · simp [h hd]
  · rcases sign_cases hd with e | e <;> simp [e]

/-- The `k`-th point of the monotone path from `u` to `v`: first along coordinate `0`, then
along coordinate `1`. -/
def pt (u v : Z2) (k : ℕ) : Z2 :=
  ![u 0 + (v 0 - u 0).sign * ((min k (v 0 - u 0).natAbs : ℕ) : ℤ),
    u 1 + (v 1 - u 1).sign * ((k - (v 0 - u 0).natAbs : ℕ) : ℤ)]

def plen (u v : Z2) : ℕ := (v 0 - u 0).natAbs + (v 1 - u 1).natAbs

def lpath (u v : Z2) : List Z2 := (List.range (plen u v + 1)).map (pt u v)

lemma pt_zero (u v : Z2) : pt u v 0 = u := by
  funext i; fin_cases i <;> simp [pt]

lemma pt_plen (u v : Z2) : pt u v (plen u v) = v := by
  funext i
  fin_cases i
  · simp only [pt, plen, Fin.zero_eta, Matrix.cons_val_zero]
    rw [min_eq_right (Nat.le_add_right _ _), Int.sign_mul_natAbs]; ring
  · simp only [pt, plen, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Nat.add_sub_cancel_left, Int.sign_mul_natAbs]; ring

lemma pt_adj (u v : Z2) (k : ℕ) (hk : k < plen u v) : adj (pt u v k) (pt u v (k + 1)) := by
  unfold plen at hk
  by_cases ha : k < (v 0 - u 0).natAbs
  · have hd : v 0 - u 0 ≠ 0 := by intro h; rw [h] at ha; simp at ha
    refine ⟨0, fun i hi => ?_, ?_⟩
    · fin_cases i
      · exact absurd rfl hi
      · simp only [pt, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [show k + 1 - (v 0 - u 0).natAbs = 0 by omega, show k - (v 0 - u 0).natAbs = 0 by omega]
    · simp only [pt, Matrix.cons_val_zero]
      rw [show min (k + 1) (v 0 - u 0).natAbs = k + 1 by omega,
        show min k (v 0 - u 0).natAbs = k by omega]
      rcases sign_cases hd with e | e <;> rw [e] <;> push_cast <;> [left; right] <;> ring
  · have hd : v 1 - u 1 ≠ 0 := by intro h; rw [h] at hk; simp at hk; omega
    refine ⟨1, fun i hi => ?_, ?_⟩
    · fin_cases i
      · simp only [pt, Fin.zero_eta, Matrix.cons_val_zero]
        rw [show min (k + 1) (v 0 - u 0).natAbs = (v 0 - u 0).natAbs by omega,
          show min k (v 0 - u 0).natAbs = (v 0 - u 0).natAbs by omega]
      · exact absurd rfl hi
    · simp only [pt, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [show k + 1 - (v 0 - u 0).natAbs = (k - (v 0 - u 0).natAbs) + 1 by omega]
      rcases sign_cases hd with e | e <;> rw [e] <;> push_cast <;> [left; right] <;> ring

lemma pt_l1 (u v : Z2) (k : ℕ) (hk : k ≤ plen u v) :
    |pt u v k 0 - u 0| + |pt u v k 1 - u 1| = k := by
  unfold plen at hk
  simp only [pt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel_left]
  rw [abs_sign_mul _ _ (fun h => by rw [h]; simp), abs_sign_mul _ _ (fun h => by
    rw [h] at hk; simp at hk; omega)]
  omega

lemma pt_bound (u v : Z2) (k : ℕ) (hk : k ≤ plen u v) (i : Fin 2) :
    |pt u v k i - u i| ≤ |v i - u i| := by
  unfold plen at hk
  fin_cases i
  · simp only [pt, Fin.zero_eta, Matrix.cons_val_zero, add_sub_cancel_left]
    rw [abs_sign_mul _ _ (fun h => by rw [h]; simp), Int.abs_eq_natAbs]
    exact_mod_cast min_le_right _ _
  · simp only [pt, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, add_sub_cancel_left]
    rw [abs_sign_mul _ _ (fun h => by rw [h] at hk; simp at hk; omega), Int.abs_eq_natAbs]
    exact_mod_cast (by omega : k - (v 0 - u 0).natAbs ≤ (v 1 - u 1).natAbs)

lemma lpath_chain (u v : Z2) : (lpath u v).IsChain adj := by
  unfold lpath
  rw [List.isChain_map, List.isChain_range_succ]
  intro m hm
  exact pt_adj u v m hm

lemma lpath_nodup (u v : Z2) : (lpath u v).Nodup := by
  unfold lpath
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
  rw [List.mem_range] at ha hb
  have h1 := pt_l1 u v a (by omega)
  have h2 := pt_l1 u v b (by omega)
  rw [hab] at h1
  exact_mod_cast h1.symm.trans h2

lemma lpath_length (u v : Z2) : (lpath u v).length = plen u v + 1 := by
  simp [lpath]

lemma lpath_head (u v : Z2) : (lpath u v).head? = some u := by
  simp [lpath, List.range_succ_eq_map, pt_zero]

lemma lpath_last (u v : Z2) : (lpath u v).getLast? = some v := by
  simp [lpath, List.range_succ, pt_plen]

lemma lpath_mem (u v w : Z2) (hw : w ∈ lpath u v) (i : Fin 2) : |w i - u i| ≤ |v i - u i| := by
  unfold lpath at hw
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
  rw [List.mem_range] at hk
  exact pt_bound u v k (by omega) i

lemma plen_pos {u v : Z2} (h : u ≠ v) : 1 ≤ plen u v := by
  by_contra h'
  apply h
  have h0 : (v 0 - u 0).natAbs = 0 := by unfold plen at h'; omega
  have h1 : (v 1 - u 1).natAbs = 0 := by unfold plen at h'; omega
  funext i; fin_cases i
  · simp at h0 ⊢; omega
  · simp at h1 ⊢; omega

/-- Edges of a chain are related. -/
lemma pathEdges_of_chain {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.IsChain R → ∀ e ∈ pathEdges l, R e.1 e.2
  | [], _, e, he => by simp [pathEdges] at he
  | [a], _, e, he => by simp [pathEdges] at he
  | a :: b :: l, h, e, he => by
    simp only [pathEdges, List.tail_cons, List.zip_cons_cons, List.mem_cons] at he
    rw [List.isChain_cons_cons] at h
    rcases he with rfl | he
    · exact h.1
    · exact pathEdges_of_chain h.2 e he

lemma pathEdges_length {α : Type*} (l : List α) : (pathEdges l).length = l.length - 1 := by
  simp [pathEdges]

lemma srw_reach (u v : Z2) : Relation.ReflTransGen (fun a b => 0 < MarkovMixing.srwZ 2 a b) u v := by
  have : ∀ k ≤ plen u v, Relation.ReflTransGen (fun a b => 0 < MarkovMixing.srwZ 2 a b) u
      (pt u v k) := by
    intro k
    induction k with
    | zero => intro _; rw [pt_zero]
    | succ k ih =>
      intro hk
      refine (ih (by omega)).tail ?_
      rw [srw_eq, if_pos (pt_adj u v k (by omega))]
      norm_num
  simpa [pt_plen] using this _ le_rfl

lemma srw_isNetwork : IsNetwork (MarkovMixing.srwZ 2) := by
  refine ⟨srw_nonneg, srw_symm, fun u => ⟨u + ![1, 0], ?_⟩, fun u => (srw_hasSum u).summable,
    srw_reach⟩
  rw [srw_eq, if_pos]
  · norm_num
  · refine ⟨0, fun i hi => ?_, Or.inl (by simp)⟩
    fin_cases i
    · exact absurd rfl hi
    · simp

lemma srw_networkWalk : networkWalk (MarkovMixing.srwZ 2) = MarkovMixing.srwZ 2 := by
  funext u v
  rw [networkWalk, (srw_hasSum u).tsum_eq, div_one]

lemma srw_not_transient : ¬ IsTransientNetwork (MarkovMixing.srwZ 2) := by
  rintro ⟨a, ha⟩
  apply ha
  rw [srw_networkWalk]
  have h0 : IsRecurrentChain (MarkovMixing.srwZ 2) (0 : Z2) :=
    isRecurrentChain_of_recurrent (0 : Z2) srw_nonneg srw_hasSum
      (MarkovMixing.polya_recurrence.1 2 (by norm_num) le_rfl)
  have := isRecurrentChain_translate (fun a b v => srw_translate a b v) 0 a h0
  simpa using this

/-! ### Symmetric choice of paths -/

def key (u : Z2) : Lex (ℤ × ℤ) := toLex (u 0, u 1)

lemma key_inj {u v : Z2} (h : key u = key v) : u = v := by
  have h' : (u 0, u 1) = (v 0, v 1) := toLex.injective h
  simp only [Prod.mk.injEq] at h'
  funext i; fin_cases i
  · exact h'.1
  · exact h'.2

def Q (u v : Z2) : List Z2 := if key u < key v then lpath u v else (lpath v u).reverse

lemma Q_swap {u v : Z2} (h : u ≠ v) : Q v u = (Q u v).reverse := by
  unfold Q
  rcases lt_trichotomy (key u) (key v) with h1 | h1 | h1
  · rw [if_pos h1, if_neg (lt_asymm h1)]
  · exact absurd (key_inj h1) h
  · rw [if_neg (lt_asymm h1), if_pos h1, List.reverse_reverse]

lemma plen_symm (u v : Z2) : plen v u = plen u v := by
  unfold plen
  rw [← Int.natAbs_neg (u 0 - v 0), ← Int.natAbs_neg (u 1 - v 1), neg_sub, neg_sub]

lemma Q_spec {u v : Z2} (h : u ≠ v) :
    2 ≤ (Q u v).length ∧ (Q u v).head? = some u ∧ (Q u v).getLast? = some v ∧ (Q u v).Nodup ∧
      (Q u v).IsChain adj ∧ (pathEdges (Q u v)).length = plen u v ∧
      ∀ w ∈ Q u v, ∀ i, |w i - u i| ≤ 2 * |v i - u i| ∧ |w i - v i| ≤ 2 * |v i - u i| := by
  have hp := plen_pos h
  unfold Q
  split_ifs
  · refine ⟨by rw [lpath_length]; omega, lpath_head u v, lpath_last u v, lpath_nodup u v,
      lpath_chain u v, by rw [pathEdges_length, lpath_length]; omega, fun w hw i => ?_⟩
    have h1 := lpath_mem u v w hw i
    have h2 : |w i - v i| ≤ |w i - u i| + |v i - u i| := by
      have := abs_sub_le (w i) (u i) (v i)
      rwa [abs_sub_comm (u i) (v i)] at this
    constructor <;> linarith [abs_nonneg (v i - u i)]
  · refine ⟨by rw [List.length_reverse, lpath_length, plen_symm]; omega, ?_, ?_, ?_, ?_, ?_, fun w hw i => ?_⟩
    · rw [List.head?_reverse, lpath_last]
    · rw [List.getLast?_reverse, lpath_head]
    · exact List.nodup_reverse.mpr (lpath_nodup v u)
    · rw [List.isChain_reverse]
      exact (lpath_chain v u).imp fun a b hab => adj_symm hab
    · rw [pathEdges_length, List.length_reverse, lpath_length, plen_symm]; omega
    · rw [List.mem_reverse] at hw
      have h1 := lpath_mem v u w hw i
      rw [abs_sub_comm (u i) (v i)] at h1
      have h2 : |w i - u i| ≤ |w i - v i| + |v i - u i| := abs_sub_le (w i) (v i) (u i)
      constructor <;> linarith [abs_nonneg (v i - u i)]

lemma srw_of_adj {u v : Z2} (h : adj u v) : MarkovMixing.srwZ 2 u v = 1 / 4 := by
  rw [srw_eq, if_pos h]

end SRW

/-! ### Restricting a chain to an invariant set (from the Theorem 4.2 solution) -/

section Restrict

variable {V : Type*} (P : V → V → ℝ) (O : Set V)

theorem avoidProb_restrict (hP : ∀ x ∈ O, ∀ y ∉ O, P x y = 0) (x₀ : O) :
    ∀ k (y : V), (y ∉ O → avoidProb P x₀ k y = 0) ∧
      ∀ hy : y ∈ O, avoidProb (fun a b : O => P a b) x₀ k ⟨y, hy⟩ = avoidProb P x₀ k y
  | 0, y => by simp [avoidProb]
  | 1, y => by
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have : y ≠ (x₀ : V) := fun h => hy (h ▸ x₀.2)
      simp [avoidProb, this, hP _ x₀.2 y hy]
    · simp only [avoidProb, Subtype.ext_iff]
  | k + 2, y => by
    have ih := avoidProb_restrict hP x₀ (k + 1)
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · have : y ≠ (x₀ : V) := fun h => hy (h ▸ x₀.2)
      simp only [avoidProb, this, if_false]
      refine (tsum_congr fun z => ?_).trans tsum_zero
      by_cases hz : z ∈ O
      · simp [hP z hz y hy]
      · simp [(ih z).1 hz]
    · simp only [avoidProb, Subtype.ext_iff]
      split_ifs with h
      · rfl
      · rw [← tsum_subtype_eq_of_support_subset (s := O)]
        · exact tsum_congr fun z => by rw [(ih z).2 z.2]
        · intro z hz
          by_contra hzO
          exact hz (by simp [(ih z).1 hzO])

theorem firstReturnProb_restrict (hP : ∀ x ∈ O, ∀ y ∉ O, P x y = 0) (x₀ : O) (k : ℕ) :
    firstReturnProb (fun a b : O => P a b) x₀ k = firstReturnProb P x₀ k := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [firstReturnProb]
    rw [← tsum_subtype_eq_of_support_subset (s := O)]
    · exact tsum_congr fun z => by rw [(avoidProb_restrict P O hP x₀ (k + 1) z).2 z.2]
    · intro z hz
      by_contra hzO
      exact hz (by simp [(avoidProb_restrict P O hP x₀ (k + 1) z).1 hzO])

end Restrict

/-! ## Part 5: the rough embedding and the conclusion -/

section Rough

lemma isRoughEmbedding_of {V : Type*} (c : V → V → ℝ) (hc1 : ∀ a b, c a b ≤ 1) (φ : V → Z2)
    (hφ : Function.Injective φ) (L : ℕ)
    (hL : ∀ a b, 0 < c a b → ∀ i, |φ b i - φ a i| ≤ L) :
    IsRoughEmbedding c (MarkovMixing.srwZ 2) φ := by
  let R : ℤ := 2 * L
  let box : Z2 → Finset Z2 := fun w => Fintype.piFinset fun i => Finset.Icc (w i - R) (w i + R)
  have hbox_card : ∀ w, (box w).card = (4 * L + 1) ^ 2 := by
    intro w
    simp only [box, Fintype.card_piFinset, Int.card_Icc, Fin.prod_univ_two]
    have : ∀ i, w i + R + 1 - (w i - R) = ((4 * L + 1 : ℕ) : ℤ) := by
      intro i; simp only [R]; push_cast; ring
    rw [this, this, Int.toNat_natCast, sq]
  refine ⟨8 * (L : ℝ), ((4 * L + 1) ^ 2) ^ 2, fun x y => Q (φ x) (φ y), ?_, ?_⟩
  · intro x y hxy hpos
    have hne : φ x ≠ φ y := hφ.ne hxy
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := Q_spec hne
    refine ⟨h1, h2, h3, h4, fun e he => ?_, ?_, Q_swap hne⟩
    · rw [srw_of_adj (pathEdges_of_chain h5 e he)]; norm_num
    · let l := (pathEdges (Q (φ x) (φ y))).map fun e : Z2 × Z2 => 1 / MarkovMixing.srwZ 2 e.1 e.2
      have hsum : l.sum ≤ l.length • (4 : ℝ) := by
        refine List.sum_le_card_nsmul _ _ fun r hr => ?_
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
        rw [srw_of_adj (pathEdges_of_chain h5 e he)]; norm_num
      rw [List.length_map, h6, nsmul_eq_mul] at hsum
      show l.sum ≤ _
      have hplen : (plen (φ x) (φ y) : ℝ) ≤ 2 * L := by
        have a0 := hL x y hpos 0
        have a1 := hL x y hpos 1
        rw [Int.abs_eq_natAbs] at a0 a1
        unfold plen
        have : (φ y 0 - φ x 0).natAbs + (φ y 1 - φ x 1).natAbs ≤ 2 * L := by omega
        exact_mod_cast this
      have hc : 1 ≤ 1 / c x y := by
        rw [le_div_iff₀ hpos, one_mul]; exact hc1 x y
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      calc _ ≤ _ := hsum
        _ ≤ 2 * L * 4 := by nlinarith
        _ = 8 * L * 1 := by ring
        _ ≤ 8 * L * (1 / c x y) := by apply mul_le_mul_of_nonneg_left hc; positivity
  · intro u v _
    let T : Set V := φ ⁻¹' (box u : Set Z2)
    have hTfin : T.Finite := (box u).finite_toSet.preimage hφ.injOn
    have hsub : {p : V × V | p.1 ≠ p.2 ∧ 0 < c p.1 p.2 ∧
        (u, v) ∈ pathEdges (Q (φ p.1) (φ p.2))} ⊆ T ×ˢ T := by
      rintro ⟨x, y⟩ ⟨hxy, hpos, he⟩
      have hne : φ x ≠ φ y := hφ.ne hxy
      have hu : u ∈ Q (φ x) (φ y) := (List.of_mem_zip he).1
      have hw := (Q_spec hne).2.2.2.2.2.2 u hu
      simp only [Set.mem_prod, Set.mem_preimage, T, box, Finset.mem_coe, Fintype.mem_piFinset,
        Finset.mem_Icc, R]
      refine ⟨fun i => ?_, fun i => ?_⟩ <;>
      · have hb := hL x y hpos i
        have hw1 := abs_le.mp (hw i).1
        have hw2 := abs_le.mp (hw i).2
        have hb' := abs_le.mp hb
        have : |φ y i - φ x i| ≤ L := hb
        have hv := abs_nonneg (φ y i - φ x i)
        constructor <;> linarith
    have hT : T.ncard ≤ (box u).card := by
      have := Set.ncard_le_ncard_of_injOn φ (fun a ha => ha) hφ.injOn (box u).finite_toSet
      rwa [Set.ncard_coe_finset] at this
    refine ⟨?_, (hTfin.prod hTfin).subset hsub⟩
    calc _ ≤ (T ×ˢ T).ncard := Set.ncard_le_ncard hsub (hTfin.prod hTfin)
      _ = T.ncard * T.ncard := Set.ncard_prod
      _ ≤ (box u).card * (box u).card := Nat.mul_le_mul hT hT
      _ = ((4 * L + 1) ^ 2) ^ 2 := by rw [hbox_card]; ring

end Rough

/-! ## Part 6: the `R`-network on a space and the coarse embedding -/

section Space

variable {X : Type*} [MetricSpace X]

/-- The conductances of the `R`-network, restricted to the `R`-component `O` of `x₀`. -/
def comp (R : ℝ) (x₀ : X) : Set X :=
  {y | Relation.ReflTransGen (fun a b : X => dist a b ≤ R) x₀ y}

noncomputable def cond (R : ℝ) (x₀ : X) (a b : comp R x₀) : ℝ :=
  if dist (a : X) b ≤ R then 1 else 0

lemma cond_pos_iff {R : ℝ} {x₀ : X} (a b : comp R x₀) : 0 < cond R x₀ a b ↔ dist (a : X) b ≤ R := by
  unfold cond; split_ifs with h <;> simp [h]

lemma cond_isNetwork (hX : HasBoundedGeometry X) {R : ℝ} (hR : 0 < R) (x₀ : X) :
    IsNetwork (cond R x₀) := by
  have hrel : ∀ y, Relation.ReflTransGen (fun a b : X => dist a b ≤ R) x₀ y → ∀ hy : y ∈ comp R x₀,
      Relation.ReflTransGen (fun a b : comp R x₀ => 0 < cond R x₀ a b)
        ⟨x₀, Relation.ReflTransGen.refl⟩ ⟨y, hy⟩ := by
    intro y hy
    induction hy with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      intro hc
      exact (ih hab).tail ((cond_pos_iff _ _).mpr hbc)
  refine ⟨fun a b => by unfold cond; split_ifs <;> norm_num, fun a b => by simp [cond, dist_comm],
    fun a => ⟨a, (cond_pos_iff a a).mpr (by simpa using hR.le)⟩, fun a => ?_, fun a b => ?_⟩
  · obtain ⟨N, hN⟩ := hX R hR
    refine summable_of_hasFiniteSupport ?_
    refine ((hN a).1.preimage Subtype.val_injective.injOn).subset ?_
    intro z hz
    simp only [Function.mem_support, cond, ne_eq, ite_eq_right_iff, Classical.not_imp] at hz
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_comm]
    exact hz.1
  · have ha := hrel a a.2 a.2
    have hb := hrel b b.2 b.2
    have ha' : Relation.ReflTransGen (fun a b : comp R x₀ => 0 < cond R x₀ a b)
        a ⟨x₀, Relation.ReflTransGen.refl⟩ := by
      have h1 := Relation.reflTransGen_swap.mpr ha
      refine Relation.ReflTransGen.mono (fun u v (h : 0 < cond R x₀ v u) => ?_) _ _ h1
      rw [cond_pos_iff] at h ⊢; rwa [dist_comm]
    exact ha'.trans hb

lemma cond_networkWalk (hX : HasBoundedGeometry X) {R : ℝ} (hR : 0 < R) (x₀ : X) :
    networkWalk (cond R x₀) = fun a b : comp R x₀ => ballKernel X R a b := by
  funext a b
  obtain ⟨N, hN⟩ := hX R hR
  have hS : ∑' z : comp R x₀, cond R x₀ a z = ((Metric.closedBall (a : X) R).ncard : ℝ) := by
    have hsupp : Function.support (fun z : X => if dist (a : X) z ≤ R then (1 : ℝ) else 0) ⊆
        comp R x₀ := by
      intro z hz
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hz
      exact Relation.ReflTransGen.tail a.2 hz.1
    rw [show (fun z : comp R x₀ => cond R x₀ a z) =
      fun z : comp R x₀ => (fun z : X => if dist (a : X) z ≤ R then (1 : ℝ) else 0) z from rfl,
      tsum_subtype_eq_of_support_subset hsupp]
    have e : (fun z : X => if dist (a : X) z ≤ R then (1 : ℝ) else 0) =
        (Metric.closedBall (a : X) R).indicator 1 := by
      funext z
      simp [Set.indicator, Metric.mem_closedBall, dist_comm]
    rw [e, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [tsum_const, nsmul_eq_mul, mul_one, Nat.card_coe_set_eq]
  rw [networkWalk, hS]
  unfold cond ballKernel
  simp only [Metric.mem_closedBall, dist_comm (b : X)]
  split_ifs <;> simp

lemma ballKernel_out {R : ℝ} (x₀ : X) :
    ∀ x ∈ comp R x₀, ∀ y ∉ comp R x₀, ballKernel X R x y = 0 := by
  intro x hx y hy
  unfold ballKernel
  rw [if_neg]
  intro h
  rw [Metric.mem_closedBall, dist_comm] at h
  exact hy (Relation.ReflTransGen.tail hx h)

/-- An injective map to `ℤ²` with bounded jumps along `R`-edges. -/
lemma exists_phi (hX : HasBoundedGeometry X) (f : X → (Fin 2 → ℤ)) (ρm ρp : ℝ → ℝ)
    (hp : Monotone ρp) (hρ : Filter.Tendsto ρm Filter.atTop Filter.atTop)
    (hf : ∀ x y, ρm (dist x y) ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ ρp (dist x y)) (R : ℝ) :
    ∃ φ : X → Z2, Function.Injective φ ∧ ∃ L : ℕ, ∀ a b, dist a b ≤ R → ∀ i, |φ b i - φ a i| ≤ L := by
  -- fibres of `f` are uniformly bounded
  obtain ⟨r0, hr0⟩ := Filter.tendsto_atTop_atTop.mp hρ 1
  set r1 := max r0 1 with hr1
  obtain ⟨N, hN⟩ := hX r1 (lt_of_lt_of_le one_pos (le_max_right _ _))
  have hfib : ∀ v : Z2, (f ⁻¹' {v}).Finite ∧ (f ⁻¹' {v}).ncard ≤ N := by
    intro v
    by_cases hne : (f ⁻¹' {v}).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hsub : f ⁻¹' {v} ⊆ Metric.closedBall x r1 := by
        intro y hy
        rw [Metric.mem_closedBall]
        by_contra hlt
        push Not at hlt
        have h1 := hr0 (dist y x) (le_trans (le_max_left _ _) hlt.le)
        have h2 := (hf y x).1
        rw [show f y = f x by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hy; rw [hx, hy],
          dist_self] at h2
        linarith
      exact ⟨(hN x).1.subset hsub, (Set.ncard_le_ncard hsub (hN x).1).trans (hN x).2⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      simp [hne]
  have hg : ∀ v : Z2, ∃ g : X → ℕ, (∀ x ∈ f ⁻¹' {v}, g x < N) ∧ Set.InjOn g (f ⁻¹' {v}) := by
    intro v
    obtain ⟨hfin, hcard⟩ := hfib v
    have : Finite (f ⁻¹' {v}) := hfin.to_subtype
    let e := Finite.equivFin (f ⁻¹' {v})
    refine ⟨fun x => if h : x ∈ f ⁻¹' {v} then (e ⟨x, h⟩ : ℕ) else 0, fun x hx => ?_, ?_⟩
    · simp only [dif_pos hx]
      have h1 := (e ⟨x, hx⟩).isLt
      have h2 : Nat.card (f ⁻¹' {v}) = (f ⁻¹' {v}).ncard := Nat.card_coe_set_eq _
      omega
    · intro x hx y hy hxy
      simp only [dif_pos hx, dif_pos hy] at hxy
      exact congrArg Subtype.val (e.injective (Fin.ext hxy))
  choose g hgN hginj using hg
  let off : X → ℤ := fun x => (g (f x) x : ℤ)
  have hoff0 : ∀ x, 0 ≤ off x := fun x => Int.natCast_nonneg _
  have hoff1 : ∀ x, off x < N + 1 := fun x => by
    have := hgN (f x) x rfl
    simp only [off]; omega
  let M : ℤ := N + 1
  have hM : 0 < M := by simp only [M]; omega
  let φ : X → Z2 := fun x => ![M * f x 0 + off x, M * f x 1]
  refine ⟨φ, ?_, ?_⟩
  · intro a b h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [φ, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hr : off a = off b := by
      have e1 := congrArg (· % M) h0
      rw [add_comm, Int.add_mul_emod_self_left, add_comm, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (hoff0 _) (hoff1 _), Int.emod_eq_of_lt (hoff0 _) (hoff1 _)] at e1
      exact e1
    have hz0 : f a 0 = f b 0 := by
      rw [hr] at h0
      exact mul_left_cancel₀ hM.ne' (add_right_cancel h0)
    have hz1 : f a 1 = f b 1 := mul_left_cancel₀ hM.ne' h1
    have hfab : f a = f b := by
      funext i; fin_cases i
      · exact hz0
      · exact hz1
    have hb : b ∈ f ⁻¹' {f a} := by simp [hfab]
    refine hginj (f a) rfl hb ?_
    have : off a = off b := hr
    simp only [off, hfab, Nat.cast_inj] at this
    rw [hfab]; exact this
  · let L0 : ℕ := (⌈ρp R⌉).toNat
    refine ⟨(N + 1) * (L0 + 1), fun a b hab i => ?_⟩
    have hfi : |f b i - f a i| ≤ L0 := by
      have h1 : ((|f b i - f a i| : ℤ) : ℝ) ≤ ρp R := by
        have hd : ((|f b i - f a i| : ℤ) : ℝ) = dist (f b i) (f a i) := by
          rw [Int.dist_eq]; push_cast; rfl
        rw [hd]
        calc dist (f b i) (f a i) ≤ dist (f b) (f a) := dist_le_pi_dist _ _ i
          _ = dist (f a) (f b) := dist_comm _ _
          _ ≤ ρp (dist a b) := (hf a b).2
          _ ≤ ρp R := hp hab
      have h2 : |f b i - f a i| ≤ ⌈ρp R⌉ := by
        have := Int.le_ceil (ρp R)
        exact_mod_cast h1.trans this
      exact h2.trans (Int.self_le_toNat _)
    have hfi' := abs_le.mp hfi
    have hb0 := hoff0 b; have hb1 := hoff1 b; have ha0 := hoff0 a; have ha1 := hoff1 a
    have hMM : (M : ℤ) = N + 1 := rfl
    have key : ∀ d : ℤ, |d| ≤ L0 → |M * d| ≤ M * L0 := fun d hd => by
      rw [abs_mul, abs_of_pos hM]; exact mul_le_mul_of_nonneg_left hd hM.le
    have hsplit : φ b i - φ a i = M * (f b i - f a i) + (if i = 0 then off b - off a else 0) := by
      fin_cases i
      · simp [φ]; ring
      · simp [φ]; ring
    have hk := key _ hfi
    have he : |(if i = 0 then off b - off a else 0)| ≤ N + 1 := by
      split_ifs
      · exact abs_le.mpr ⟨by linarith, by linarith⟩
      · simp; omega
    have hsum : M * L0 + (N + 1) = (N + 1) * (L0 + 1) := by rw [hMM]; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith

end Space

theorem part2_monotone {X : Type*} [MetricSpace X] (hX : HasBoundedGeometry X)
    (f : X → (Fin 2 → ℤ)) (ρm ρp : ℝ → ℝ) (hm : Monotone ρm) (hp : Monotone ρp)
    (hρ : Filter.Tendsto ρm Filter.atTop Filter.atTop)
    (hf : ∀ x y, ρm (dist x y) ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ ρp (dist x y)) :
    ∀ x₀ : X, IsRecurrentSpace X x₀ := by
  intro x₀ R hR
  obtain ⟨φ₀, hφ₀, L, hL⟩ := exists_phi hX f ρm ρp hp hρ hf R
  have hx₀ : x₀ ∈ comp R x₀ := Relation.ReflTransGen.refl
  let φ : comp R x₀ → Z2 := fun a => φ₀ a
  have hφ : Function.Injective φ := fun a b h => Subtype.ext (hφ₀ h)
  have hc1 : ∀ a b, cond R x₀ a b ≤ 1 := fun a b => by unfold cond; split_ifs <;> norm_num
  have hrough := isRoughEmbedding_of (cond R x₀) hc1 φ hφ L
    (fun a b hab i => hL a b ((cond_pos_iff a b).mp hab) i)
  have htr := (LyonsPeres.isTransientNetwork_iff_and_isTransientNetwork_of_isRoughEmbedding
    (cond R x₀) (MarkovMixing.srwZ 2) (cond_isNetwork hX hR x₀) srw_isNetwork).2 φ hrough
  have hrec : IsRecurrentChain (networkWalk (cond R x₀)) ⟨x₀, hx₀⟩ := by
    by_contra h
    exact srw_not_transient (htr ⟨_, h⟩)
  rw [cond_networkWalk hX hR] at hrec
  have e : firstReturnProb (fun a b : comp R x₀ => ballKernel X R a b) ⟨x₀, hx₀⟩ =
      firstReturnProb (ballKernel X R) x₀ :=
    funext (firstReturnProb_restrict (ballKernel X R) (comp R x₀) (ballKernel_out x₀) ⟨x₀, hx₀⟩)
  unfold IsRecurrentChain at hrec ⊢
  rwa [e] at hrec

end JuschenkoDeLaSalle.IETJ2

end

section
open IntervalExchange

namespace JuschenkoDeLaSalle

theorem chk_isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarseEmbedding_and_not_of_containsLipschitzBinaryTree
    {X : Type*} [MetricSpace X] (hX : HasBoundedGeometry X) :
    (∀ x₀ : X, IsRecurrentSpace X x₀ →
      IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2))) ∧
    (∀ (f : X → (Fin 2 → ℤ)) (ρm ρp : ℝ → ℝ), Monotone ρm → Monotone ρp →
      Filter.Tendsto ρm Filter.atTop Filter.atTop →
      (∀ x y, ρm (dist x y) ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ ρp (dist x y)) →
      ∀ x₀ : X, IsRecurrentSpace X x₀) ∧
    (ContainsLipschitzBinaryTree X →
      ¬ IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2))) :=
  ⟨IETJ13.part1 hX, fun f ρm ρp hm hp hρ hf => IETJ2.part2_monotone hX f ρm ρp hm hp hρ hf,
    IETJ13.part3 hX⟩

end JuschenkoDeLaSalle
end
end

open IntervalExchange
theorem solution
    {X : Type*} [MetricSpace X] (hX : HasBoundedGeometry X) :
    (∀ x₀ : X, IsRecurrentSpace X x₀ →
      IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2))) ∧
    (∀ (f : X → (Fin 2 → ℤ)) (ρm ρp : ℝ → ℝ), Monotone ρm → Monotone ρp →
      Filter.Tendsto ρm Filter.atTop Filter.atTop →
      (∀ x y, ρm (dist x y) ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ ρp (dist x y)) →
      ∀ x₀ : X, IsRecurrentSpace X x₀) ∧
    (ContainsLipschitzBinaryTree X →
      ¬ IsAmenableAction (Lamplighter ↥(wobbling X) X) (Multiplicative (X →₀ ZMod 2))) :=
  JuschenkoDeLaSalle.chk_isAmenableAction_lamplighter_wobbling_of_isRecurrentSpace_and_isRecurrentSpace_of_coarseEmbedding_and_not_of_containsLipschitzBinaryTree hX
