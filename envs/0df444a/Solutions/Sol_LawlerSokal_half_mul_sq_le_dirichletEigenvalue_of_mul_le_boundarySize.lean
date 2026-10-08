-- Prove2me | solution 1 for LawlerSokal.half_mul_sq_le_dirichletEigenvalue_of_mul_le_boundarySize
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-04T11:37:14.055551+00:00
-- url     : https://prove2.me/submissions/975f1918-56fc-44e6-abd0-17db4bbcc16c

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

section
/-!
# D1: Cheeger's inequality for the Dirichlet eigenvalue (Lawler–Sokal, Theorem 3.1)

For `f` supported in `Ω` with `‖f‖² = 1`, put `a = |f|` and `g = a²`.

* (layer cake) `h ∑_Ω g π ≤ A := ∑_{x ∈ Ω} π(x) ∑_y P(x, y) (g(x) − g(y))₊`, by induction on the
  support of `g`: subtract `m 1_S` with `m` the least positive value and `S = {g > 0}`;
* (AM–GM, `s = 2/h`) `A ≤ (1/h) E⁺ + (h/4) B`, where `E⁺ = ∑_Ω π ∑_y P (a(x) − a(y))₊²` and
  `B = ∑_Ω π ∑_y P 1[a(x) > a(y)] (a(x) + a(y))²`;
* (symmetry) `B ≤ 2 ∑_Ω a² π`, by reversibility;
* `E⁺ = ℰ(a) ≤ ℰ(f)`.

Hence `h ≤ ℰ(f)/h + h/2`, i.e. `h²/2 ≤ ℰ(f)`.
-/

open DurrettProbability MarkovChain

namespace LawlerSokal

namespace D1

variable {X : Type*}

/-- A function on `X × X` vanishing off `Ω × X`, with summable rows, is summable, and its sum is
the finite sum of its row sums. -/
lemma summable_prod_of_rows (Ω : Finset X) (g : X × X → ℝ) (hg : ∀ p : X × X, p.1 ∉ Ω → g p = 0)
    (hrow : ∀ x, Summable (fun y => g (x, y))) :
    Summable g ∧ ∑' p, g p = ∑ x ∈ Ω, ∑' y, g (x, y) := by
  classical
  have hdecomp : g = fun p => ∑ x ∈ Ω, (if p.1 = x then g p else 0) := by
    funext p
    rw [Finset.sum_ite_eq]
    split_ifs with hp
    · rfl
    · exact hg p hp
  have hpiece : ∀ x, Summable (fun p : X × X => if p.1 = x then g p else 0) ∧
      ∑' p : X × X, (if p.1 = x then g p else 0) = ∑' y, g (x, y) := by
    intro x
    have hinj : Function.Injective (fun y : X => (x, y)) := fun a b h => (Prod.mk.inj h).2
    have hsupp : ∀ p ∉ Set.range (fun y : X => (x, y)), (if p.1 = x then g p else 0) = 0 := by
      intro p hp
      split_ifs with h
      · exact absurd ⟨p.2, by ext <;> simp [h]⟩ hp
      · rfl
    have hcomp : ((fun p : X × X => if p.1 = x then g p else 0) ∘ fun y => (x, y)) =
        fun y => g (x, y) := by
      funext y; simp
    refine ⟨(hinj.summable_iff hsupp).mp (by rw [hcomp]; exact hrow x), ?_⟩
    have := hinj.tsum_eq (f := fun p : X × X => if p.1 = x then g p else 0) (by
      intro p hp
      by_contra hc
      exact hp (hsupp p hc))
    rw [← this]
    simp
  constructor
  · rw [hdecomp]
    exact summable_sum fun x _ => (hpiece x).1
  · conv_lhs => rw [hdecomp]
    rw [Summable.tsum_finsetSum fun x _ => (hpiece x).1]
    exact Finset.sum_congr rfl fun x _ => (hpiece x).2

/-- Rows `y ↦ P x y * c y` with `0 ≤ c ≤ K` are summable. -/
lemma summable_row {P : X → X → ℝ} (hP : IsTransition P) (x : X) {c : X → ℝ} (K : ℝ)
    (h0 : ∀ y, 0 ≤ c y) (hK : ∀ y, c y ≤ K) : Summable (fun y => P x y * c y) :=
  Summable.of_nonneg_of_le (fun y => mul_nonneg (hP.1 x y) (h0 y))
    (fun y => mul_le_mul_of_nonneg_left (hK y) (hP.1 x y)) ((hP.2.1 x).mul_right K)

/-- The Dirichlet-form summand is summable for `f` supported in a finite set. -/
lemma summable_dirichlet {P : X → X → ℝ} {π : X → ℝ} (hP : IsTransition P) (hπ : ∀ x, 0 < π x)
    (hrev : IsReversible P π) (Ω : Finset X) (f : X → ℝ) (hf : ∀ x ∉ Ω, f x = 0) :
    Summable (fun p : X × X => (f p.1 - f p.2) ^ 2 * P p.1 p.2 * π p.1) := by
  set G : X × X → ℝ := fun p => f p.1 ^ 2 * P p.1 p.2 * π p.1 with hG
  have hGs : Summable G := by
    refine (summable_prod_of_rows Ω G (fun p hp => by simp [hG, hf p.1 hp]) fun x => ?_).1
    have := (hP.2.1 x).mul_left (f x ^ 2 * π x)
    refine this.congr fun y => ?_
    simp only [hG]; ring
  have hGs' : Summable (G ∘ Prod.swap) :=
    (Equiv.summable_iff (Equiv.prodComm X X)).mpr hGs
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) ((hGs.add hGs').mul_left 2)
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (hP.1 _ _)) (hπ _).le
  · simp only [hG, Function.comp, Prod.fst_swap, Prod.snd_swap]
    have hr := hrev p.1 p.2
    have h1 : (f p.1 - f p.2) ^ 2 ≤ 2 * f p.1 ^ 2 + 2 * f p.2 ^ 2 := by
      nlinarith [sq_nonneg (f p.1 + f p.2)]
    have hw : 0 ≤ P p.1 p.2 * π p.1 := mul_nonneg (hP.1 _ _) (hπ _).le
    calc (f p.1 - f p.2) ^ 2 * P p.1 p.2 * π p.1
        = (f p.1 - f p.2) ^ 2 * (P p.1 p.2 * π p.1) := by ring
      _ ≤ (2 * f p.1 ^ 2 + 2 * f p.2 ^ 2) * (P p.1 p.2 * π p.1) :=
          mul_le_mul_of_nonneg_right h1 hw
      _ = 2 * (f p.1 ^ 2 * P p.1 p.2 * π p.1 + f p.2 ^ 2 * P p.2 p.1 * π p.2) := by
          have e : P p.2 p.1 * π p.2 = P p.1 p.2 * π p.1 := by linarith [hr]
          rw [mul_assoc (f p.2 ^ 2), e]; ring

/-- `ℰ(|f|) ≤ ℰ(f)`. -/
lemma dirichletForm_abs_le {P : X → X → ℝ} {π : X → ℝ} (hP : IsTransition P) (hπ : ∀ x, 0 < π x)
    (hrev : IsReversible P π) (Ω : Finset X) (f : X → ℝ) (hf : ∀ x ∉ Ω, f x = 0) :
    dirichletForm P π (fun x => |f x|) ≤ dirichletForm P π f := by
  unfold dirichletForm
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hs1 := summable_dirichlet hP hπ hrev Ω (fun x => |f x|) (fun x hx => by simp [hf x hx])
  have hs2 := summable_dirichlet hP hπ hrev Ω f hf
  refine Summable.tsum_le_tsum (fun p => ?_) hs1 hs2
  show (|f p.1| - |f p.2|) ^ 2 * P p.1 p.2 * π p.1 ≤ (f p.1 - f p.2) ^ 2 * P p.1 p.2 * π p.1
  have hw : 0 ≤ P p.1 p.2 * π p.1 := mul_nonneg (hP.1 _ _) (hπ _).le
  have h1 : (|f p.1| - |f p.2|) ^ 2 ≤ (f p.1 - f p.2) ^ 2 := by
    have := abs_abs_sub_abs_le_abs_sub (f p.1) (f p.2)
    rw [← sq_abs (|f p.1| - |f p.2|), ← sq_abs (f p.1 - f p.2)]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc (|f p.1| - |f p.2|) ^ 2 * P p.1 p.2 * π p.1
      = (|f p.1| - |f p.2|) ^ 2 * (P p.1 p.2 * π p.1) := by ring
    _ ≤ (f p.1 - f p.2) ^ 2 * (P p.1 p.2 * π p.1) := mul_le_mul_of_nonneg_right h1 hw
    _ = (f p.1 - f p.2) ^ 2 * P p.1 p.2 * π p.1 := by ring

/-- For `a ≥ 0` supported in `Ω`: `ℰ(a) = ∑_{x ∈ Ω} π(x) ∑_y P(x, y) (a(x) − a(y))₊²`. -/
lemma dirichletForm_eq_pos {P : X → X → ℝ} {π : X → ℝ} (hP : IsTransition P)
    (hrev : IsReversible P π) (Ω : Finset X) (a : X → ℝ) (ha0 : ∀ x, 0 ≤ a x)
    (ha : ∀ x ∉ Ω, a x = 0) :
    dirichletForm P π a = ∑ x ∈ Ω, π x * ∑' y, P x y * max (a x - a y) 0 ^ 2 := by
  set Fp : X × X → ℝ := fun p => max (a p.1 - a p.2) 0 ^ 2 * P p.1 p.2 * π p.1 with hFp
  have hrows : ∀ x, Summable (fun y => Fp (x, y)) := by
    intro x
    have := summable_row hP x (c := fun y => max (a x - a y) 0 ^ 2) (a x ^ 2)
      (fun y => sq_nonneg _) (fun y => by
        have h1 : max (a x - a y) 0 ≤ a x := max_le (by linarith [ha0 y]) (ha0 x)
        exact pow_le_pow_left₀ (le_max_right _ _) h1 2)
    refine (this.mul_right (π x)).congr fun y => ?_
    simp only [hFp]; ring
  have hsupp : ∀ p : X × X, p.1 ∉ Ω → Fp p = 0 := by
    intro p hp
    simp only [hFp, ha p.1 hp]
    have : max (0 - a p.2) 0 = 0 := max_eq_right (by linarith [ha0 p.2])
    rw [this]; ring
  obtain ⟨hsum, htsum⟩ := summable_prod_of_rows Ω Fp hsupp hrows
  have hsum' : Summable (Fp ∘ Prod.swap) := (Equiv.summable_iff (Equiv.prodComm X X)).mpr hsum
  have hswap : ∑' p, (Fp ∘ Prod.swap) p = ∑' p, Fp p := (Equiv.prodComm X X).tsum_eq Fp
  have hsplit : (fun p : X × X => (a p.1 - a p.2) ^ 2 * P p.1 p.2 * π p.1) =
      fun p => Fp p + (Fp ∘ Prod.swap) p := by
    funext p
    simp only [hFp, Function.comp, Prod.fst_swap, Prod.snd_swap]
    have hr := hrev p.1 p.2
    have hsq : (a p.1 - a p.2) ^ 2 = max (a p.1 - a p.2) 0 ^ 2 + max (a p.2 - a p.1) 0 ^ 2 := by
      rcases le_total (a p.1) (a p.2) with h | h
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    have e : P p.2 p.1 * π p.2 = P p.1 p.2 * π p.1 := by linarith [hr]
    rw [hsq, mul_assoc (max (a p.2 - a p.1) 0 ^ 2), e]; ring
  unfold dirichletForm
  rw [hsplit, hsum.tsum_add hsum', hswap, htsum]
  rw [show (1 : ℝ) / 2 * (∑ x ∈ Ω, ∑' y, Fp (x, y) + ∑ x ∈ Ω, ∑' y, Fp (x, y)) =
    ∑ x ∈ Ω, ∑' y, Fp (x, y) by ring]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← tsum_mul_left]
  congr 1; funext y; simp only [hFp]; ring

/-- The layer-cake lower bound. -/
lemma layer_cake {P : X → X → ℝ} {π : X → ℝ} (hP : IsTransition P) (hπ : ∀ x, 0 < π x)
    (Ω : Finset X) (h : ℝ)
    (hbd : ∀ U ⊆ Ω, U.Nonempty → h * ∑ x ∈ U, π x ≤ boundarySize P π U) :
    ∀ n : ℕ, ∀ g : X → ℝ, (∀ x, 0 ≤ g x) → (∀ x ∉ Ω, g x = 0) →
      (Ω.filter (fun x => 0 < g x)).card ≤ n →
      h * ∑ x ∈ Ω, g x * π x ≤ ∑ x ∈ Ω, π x * ∑' y, P x y * max (g x - g y) 0 := by
  classical
  have hrhs_nonneg : ∀ g : X → ℝ, (∀ x, 0 ≤ g x) →
      0 ≤ ∑ x ∈ Ω, π x * ∑' y, P x y * max (g x - g y) 0 := by
    intro g _
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hπ x).le
      (tsum_nonneg fun y => mul_nonneg (hP.1 x y) (le_max_right _ _))
  have hbase : ∀ g : X → ℝ, (∀ x, 0 ≤ g x) → (Ω.filter (fun x => 0 < g x)) = ∅ →
      h * ∑ x ∈ Ω, g x * π x ≤ ∑ x ∈ Ω, π x * ∑' y, P x y * max (g x - g y) 0 := by
    intro g hg0 hS
    have : ∑ x ∈ Ω, g x * π x = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      have : ¬ 0 < g x := by
        intro hpos
        have : x ∈ Ω.filter (fun x => 0 < g x) := Finset.mem_filter.mpr ⟨hx, hpos⟩
        rw [hS] at this; simp at this
      rw [le_antisymm (not_lt.mp this) (hg0 x)]; ring
    rw [this, mul_zero]
    exact hrhs_nonneg g hg0
  intro n
  induction n with
  | zero =>
    intro g hg0 _ hcard
    exact hbase g hg0 (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro g hg0 hgΩ hcard
    set S := Ω.filter (fun x => 0 < g x) with hSdef
    rcases S.eq_empty_or_nonempty with hS | hS
    · exact hbase g hg0 hS
    obtain ⟨x₀, hx₀S, hmin⟩ := S.exists_min_image g hS
    set m := g x₀ with hm
    have hx₀ : x₀ ∈ Ω ∧ 0 < g x₀ := Finset.mem_filter.mp hx₀S
    have hmpos : 0 < m := hx₀.2
    have hmemS : ∀ x, x ∈ S ↔ 0 < g x := by
      intro x
      rw [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro hpos
        refine ⟨?_, hpos⟩
        by_contra hx
        rw [hgΩ x hx] at hpos; exact lt_irrefl _ hpos
    have hge : ∀ x, 0 < g x → m ≤ g x := fun x hx => hmin x ((hmemS x).mpr hx)
    set g' : X → ℝ := fun x => if 0 < g x then g x - m else 0 with hg'
    have hg'0 : ∀ x, 0 ≤ g' x := by
      intro x; simp only [hg']; split_ifs with h
      · linarith [hge x h]
      · exact le_refl _
    have hg'Ω : ∀ x ∉ Ω, g' x = 0 := by
      intro x hx; simp only [hg', hgΩ x hx, lt_irrefl, if_false]
    have hcard' : (Ω.filter (fun x => 0 < g' x)).card ≤ n := by
      have hsub : Ω.filter (fun x => 0 < g' x) ⊆ S.erase x₀ := by
        intro x hx
        rw [Finset.mem_filter] at hx
        have hpos : 0 < g x := by
          by_contra hc; simp only [hg', hc, if_false] at hx; exact lt_irrefl _ hx.2
        rw [Finset.mem_erase]
        refine ⟨?_, (hmemS x).mpr hpos⟩
        intro hxx
        have hgx : g x - m = 0 := by rw [hxx, hm, sub_self]
        simp only [hg', hpos, if_true, hgx] at hx; exact lt_irrefl _ hx.2
      calc _ ≤ (S.erase x₀).card := Finset.card_le_card hsub
        _ = S.card - 1 := Finset.card_erase_of_mem hx₀S
        _ ≤ n := by omega
    have ih' := ih g' hg'0 hg'Ω hcard'
    -- the indicator of `S`
    set ind : X → ℝ := fun x => if 0 < g x then 1 else 0 with hind
    have hpt : ∀ x y, max (g x - g y) 0 = m * max (ind x - ind y) 0 + max (g' x - g' y) 0 := by
      intro x y
      simp only [hind, hg']
      by_cases hx : 0 < g x <;> by_cases hy : 0 < g y <;> simp only [hx, hy, if_true, if_false]
      · rw [sub_self, max_self, mul_zero, zero_add]; congr 1; ring
      · have hy0 : g y = 0 := le_antisymm (not_lt.mp hy) (hg0 y)
        rw [hy0, sub_zero, sub_zero, sub_zero, max_eq_left hx.le, max_eq_left zero_le_one,
          max_eq_left (by linarith [hge x hx])]; ring
      · have hx0 : g x = 0 := le_antisymm (not_lt.mp hx) (hg0 x)
        rw [hx0, zero_sub, zero_sub, zero_sub, max_eq_right (by linarith),
          max_eq_right (by norm_num), max_eq_right (by linarith [hge y hy])]; ring
      · rw [le_antisymm (not_lt.mp hx) (hg0 x), le_antisymm (not_lt.mp hy) (hg0 y)]; simp
    have hgsum : ∀ x, g x = m * ind x + g' x := by
      intro x; simp only [hind, hg']
      split_ifs with h
      · ring
      · rw [le_antisymm (not_lt.mp h) (hg0 x)]; ring
    -- split the right-hand side
    have hsumm1 : ∀ x, Summable (fun y => P x y * (m * max (ind x - ind y) 0)) := by
      intro x
      refine summable_row hP x m (fun y => mul_nonneg hmpos.le (le_max_right _ _)) fun y => ?_
      have : max (ind x - ind y) 0 ≤ 1 := by
        simp only [hind]; split_ifs <;> norm_num
      nlinarith
    have hsumm2 : ∀ x, Summable (fun y => P x y * max (g' x - g' y) 0) := by
      intro x
      refine summable_row hP x (g' x) (fun y => le_max_right _ _) fun y => ?_
      exact max_le (by linarith [hg'0 y]) (hg'0 x)
    have hRHS : ∑ x ∈ Ω, π x * ∑' y, P x y * max (g x - g y) 0 =
        m * ∑ x ∈ Ω, π x * ∑' y, P x y * max (ind x - ind y) 0 +
          ∑ x ∈ Ω, π x * ∑' y, P x y * max (g' x - g' y) 0 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      have : (fun y => P x y * max (g x - g y) 0) =
          fun y => P x y * (m * max (ind x - ind y) 0) + P x y * max (g' x - g' y) 0 := by
        funext y; rw [hpt]; ring
      rw [this, (hsumm1 x).tsum_add (hsumm2 x)]
      have : ∑' y, P x y * (m * max (ind x - ind y) 0) = m * ∑' y, P x y * max (ind x - ind y) 0 := by
        rw [← tsum_mul_left]; congr 1; funext y; ring
      rw [this]; ring
    -- the indicator term is the boundary of `S`
    have hbdry : ∑ x ∈ Ω, π x * ∑' y, P x y * max (ind x - ind y) 0 = boundarySize P π S := by
      unfold boundarySize
      have hsub : ∀ x, ∑' y : {y // y ∉ S}, π x * P x y =
          ∑' y, π x * (P x y * (if 0 < g y then 0 else 1)) := by
        intro x
        rw [show (∑' y : {y // y ∉ S}, π x * P x y) =
            ∑' y, ({y | y ∉ S} : Set X).indicator (fun y => π x * P x y) y from
          tsum_subtype ({y | y ∉ S} : Set X) (fun y => π x * P x y)]
        refine tsum_congr fun y => ?_
        simp only [Set.indicator, Set.mem_ofPred_eq, hmemS]
        by_cases hy : 0 < g y <;> simp [hy]
      rw [Finset.sum_congr rfl fun x _ => hsub x]
      rw [hSdef, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with hx
      · rw [tsum_mul_left]
        congr 1
        refine tsum_congr fun y => ?_
        simp only [hind, hx, if_true]
        split_ifs <;> simp
      · simp only [hind, hx, if_false, zero_sub]
        have : ∀ y, max (-(if 0 < g y then (1 : ℝ) else 0)) 0 = 0 := by
          intro y; split_ifs <;> norm_num
        simp [this]
    have hbdS := hbd S (Finset.filter_subset _ _) hS
    rw [hRHS, hbdry]
    have hLHS : h * ∑ x ∈ Ω, g x * π x =
        m * (h * ∑ x ∈ S, π x) + h * ∑ x ∈ Ω, g' x * π x := by
      have : ∑ x ∈ Ω, g x * π x = m * ∑ x ∈ S, π x + ∑ x ∈ Ω, g' x * π x := by
        rw [hSdef, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : 0 < g x
        · simp only [hx, if_true, hg']; ring
        · simp only [hx, if_false, hg']; rw [le_antisymm (not_lt.mp hx) (hg0 x)]; ring
      rw [this]; ring
    rw [hLHS]
    have := mul_le_mul_of_nonneg_left hbdS hmpos.le
    linarith

/-- The symmetry bound: `∑_Ω π ∑_y P 1[a(y) < a(x)] (a(x) + a(y))² ≤ 2 ∑_Ω a² π`. -/
lemma sym_bound {P : X → X → ℝ} {π : X → ℝ} (hP : IsTransition P) (hπ : ∀ x, 0 < π x)
    (hrev : IsReversible P π) (Ω : Finset X) (a : X → ℝ) (ha0 : ∀ x, 0 ≤ a x)
    (haΩ : ∀ x ∉ Ω, a x = 0) :
    ∑ x ∈ Ω, π x * ∑' y, P x y * (if a y < a x then (a x + a y) ^ 2 else 0) ≤
      2 * ∑ x ∈ Ω, a x ^ 2 * π x := by
  set B := ∑ x ∈ Ω, π x * ∑' y, P x y * (if a y < a x then (a x + a y) ^ 2 else 0) with hB
  have hsB : ∀ x, Summable (fun y => P x y * (if a y < a x then (a x + a y) ^ 2 else 0)) := by
    intro x
    refine summable_row hP x (4 * a x ^ 2) (fun y => by split_ifs <;> positivity) fun y => ?_
    split_ifs with hlt
    · nlinarith [ha0 y]
    · positivity
  have hcomp : ∀ x, (fun y => P x y * (if a y < a x then (a x + a y) ^ 2 else 0)) ≤
      fun y => 2 * a x ^ 2 * (P x y * (if a y < a x then 1 else 0)) +
        2 * (P x y * (if a y < a x then a y ^ 2 else 0)) := by
    intro x y
    dsimp only
    have hPxy := hP.1 x y
    split_ifs with hlt
    · nlinarith [sq_nonneg (a x - a y)]
    · simp
  have hs1 : ∀ x, Summable (fun y => P x y * (if a y < a x then (1 : ℝ) else 0)) :=
    fun x => summable_row hP x 1 (fun y => by split_ifs <;> norm_num)
      (fun y => by split_ifs <;> norm_num)
  have hs2 : ∀ x, Summable (fun y => P x y * (if a y < a x then a y ^ 2 else 0)) :=
    fun x => summable_row hP x (a x ^ 2) (fun y => by split_ifs <;> positivity)
      (fun y => by split_ifs with hlt <;> nlinarith [ha0 y])
  have hstep1 : B ≤ ∑ x ∈ Ω, π x * (2 * a x ^ 2 * ∑' y, P x y * (if a y < a x then 1 else 0) +
        2 * ∑' y, P x y * (if a y < a x then a y ^ 2 else 0)) := by
    rw [hB]
    refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hπ x).le
    rw [← tsum_mul_left, ← tsum_mul_left,
      ← ((hs1 x).mul_left _).tsum_add ((hs2 x).mul_left _)]
    exact Summable.tsum_le_tsum (hcomp x) (hsB x) (((hs1 x).mul_left _).add ((hs2 x).mul_left _))
  -- the second sum is finite and swaps by reversibility
  have hfin : ∀ x, ∑' y, P x y * (if a y < a x then a y ^ 2 else 0) =
      ∑ y ∈ Ω, P x y * (if a y < a x then a y ^ 2 else 0) := by
    intro x
    exact tsum_eq_sum fun y hy => by simp [haΩ y hy]
  have hswap : ∑ x ∈ Ω, π x * ∑ y ∈ Ω, P x y * (if a y < a x then a y ^ 2 else 0) =
      ∑ x ∈ Ω, a x ^ 2 * π x * ∑ y ∈ Ω, P x y * (if a x < a y then 1 else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have hr := hrev y x
    split_ifs <;> [skip; simp]
    rw [mul_one]
    calc π y * (P y x * a x ^ 2) = a x ^ 2 * (π y * P y x) := by ring
      _ = a x ^ 2 * (π x * P x y) := by rw [hr]
      _ = a x ^ 2 * π x * P x y := by ring
  have hfin1 : ∀ x ∈ Ω, ∑ y ∈ Ω, P x y * (if a x < a y then (1 : ℝ) else 0) =
      ∑' y, P x y * (if a x < a y then 1 else 0) := by
    intro x _
    refine (tsum_eq_sum fun y hy => ?_).symm
    have : ¬ a x < a y := by rw [haΩ y hy]; exact not_lt.mpr (ha0 x)
    simp [this]
  have hs3 : ∀ x, Summable (fun y => P x y * (if a x < a y then (1 : ℝ) else 0)) :=
    fun x => summable_row hP x 1 (fun y => by split_ifs <;> norm_num)
      (fun y => by split_ifs <;> norm_num)
  have hrow1 : ∀ x, ∑' y, P x y * (if a y < a x then (1 : ℝ) else 0) +
      ∑' y, P x y * (if a x < a y then 1 else 0) ≤ 1 := by
    intro x
    rw [← (hs1 x).tsum_add (hs3 x)]
    refine le_trans (Summable.tsum_le_tsum (fun y => ?_) ((hs1 x).add (hs3 x)) (hP.2.1 x))
      (hP.2.2 x).le
    have hPxy := hP.1 x y
    rcases lt_trichotomy (a y) (a x) with h1 | h1 | h1
    · simp [h1, not_lt.mpr h1.le]
    · simp [h1, hPxy]
    · simp [h1, not_lt.mpr h1.le]
  calc B ≤ _ := hstep1
    _ = ∑ x ∈ Ω, 2 * (a x ^ 2 * π x) * ∑' y, P x y * (if a y < a x then 1 else 0) +
        2 * ∑ x ∈ Ω, π x * ∑ y ∈ Ω, P x y * (if a y < a x then a y ^ 2 else 0) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hfin x]; ring
    _ = ∑ x ∈ Ω, 2 * (a x ^ 2 * π x) * (∑' y, P x y * (if a y < a x then 1 else 0) +
          ∑' y, P x y * (if a x < a y then 1 else 0)) := by
      rw [hswap, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hfin1 x hx]; ring
    _ ≤ ∑ x ∈ Ω, 2 * (a x ^ 2 * π x) * 1 := by
      refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hrow1 x) ?_
      exact mul_nonneg zero_le_two (mul_nonneg (sq_nonneg _) (hπ x).le)
    _ = 2 * ∑ x ∈ Ω, a x ^ 2 * π x := by rw [Finset.mul_sum]; simp

/-- The AM–GM step. -/
lemma amgm_bound {P : X → X → ℝ} {π : X → ℝ} (hP : IsTransition P) (hπ : ∀ x, 0 < π x)
    (Ω : Finset X) (a : X → ℝ) (ha0 : ∀ x, 0 ≤ a x) (h : ℝ) (hpos : 0 < h) :
    ∑ x ∈ Ω, π x * ∑' y, P x y * max (a x ^ 2 - a y ^ 2) 0 ≤
      1 / h * ∑ x ∈ Ω, π x * ∑' y, P x y * max (a x - a y) 0 ^ 2 +
        h / 4 * ∑ x ∈ Ω, π x * ∑' y, P x y * (if a y < a x then (a x + a y) ^ 2 else 0) := by
  have hsA : ∀ x, Summable (fun y => P x y * max (a x ^ 2 - a y ^ 2) 0) := by
    intro x
    refine summable_row hP x (a x ^ 2) (fun y => le_max_right _ _) fun y => ?_
    exact max_le (by nlinarith [sq_nonneg (a y)]) (sq_nonneg _)
  have hsE : ∀ x, Summable (fun y => P x y * max (a x - a y) 0 ^ 2) := by
    intro x
    refine summable_row hP x (a x ^ 2) (fun y => sq_nonneg _) fun y => ?_
    exact pow_le_pow_left₀ (le_max_right _ _) (max_le (by linarith [ha0 y]) (ha0 x)) 2
  have hsB : ∀ x, Summable (fun y => P x y * (if a y < a x then (a x + a y) ^ 2 else 0)) := by
    intro x
    refine summable_row hP x (4 * a x ^ 2) (fun y => by split_ifs <;> positivity) fun y => ?_
    split_ifs with hlt
    · nlinarith [ha0 y]
    · positivity
  have hAMGM : ∀ u v : ℝ, u * v ≤ 1 / h * u ^ 2 + h / 4 * v ^ 2 := by
    intro u v
    have : 0 ≤ (u - h / 2 * v) ^ 2 / h := div_nonneg (sq_nonneg _) hpos.le
    have e : (u - h / 2 * v) ^ 2 / h = 1 / h * u ^ 2 + h / 4 * v ^ 2 - u * v := by
      field_simp; ring
    linarith
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← mul_assoc, ← mul_assoc, mul_comm (1 / h) (π x), mul_comm (h / 4) (π x), mul_assoc,
    mul_assoc, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hπ x).le
  rw [← tsum_mul_left, ← tsum_mul_left, ← ((hsE x).mul_left _).tsum_add ((hsB x).mul_left _)]
  refine Summable.tsum_le_tsum (fun y => ?_) (hsA x)
    (((hsE x).mul_left _).add ((hsB x).mul_left _))
  have hPxy := hP.1 x y
  rcases lt_or_ge (a y) (a x) with hlt | hge
  · simp only [hlt, if_true]
    rw [max_eq_left (by nlinarith [ha0 y]), max_eq_left (by linarith)]
    have := hAMGM (a x - a y) (a x + a y)
    have e : a x ^ 2 - a y ^ 2 = (a x - a y) * (a x + a y) := by ring
    rw [e]
    nlinarith
  · simp only [not_lt.mpr hge, if_false]
    rw [max_eq_right (by nlinarith [ha0 x]), max_eq_right (by linarith)]
    simp

end D1

end LawlerSokal
end

section
open DurrettProbability MarkovChain
open LawlerSokal
open D1 in
theorem solution {X : Type*} [Countable X]
    (P : X → X → ℝ) (π : X → ℝ) (hP : IsTransition P) (hπ : ∀ x, 0 < π x)
    (hrev : IsReversible P π) (Ω : Finset X) (hΩ : Ω.Nonempty) (h : ℝ) (hh : 0 ≤ h)
    (hbd : ∀ U ⊆ Ω, U.Nonempty → h * ∑ x ∈ U, π x ≤ boundarySize P π U) :
    1 / 2 * h ^ 2 ≤ dirichletEigenvalue P π Ω := by
  classical
  -- every admissible `f` has `ℰ(f) ≥ h²/2`
  have key : ∀ f : X → ℝ, (∀ x ∉ Ω, f x = 0) → normSq π f = 1 →
      1 / 2 * h ^ 2 ≤ dirichletForm P π f := by
    intro f hf hnorm
    set a : X → ℝ := fun x => |f x| with ha
    have ha0 : ∀ x, 0 ≤ a x := fun x => abs_nonneg _
    have haΩ : ∀ x ∉ Ω, a x = 0 := fun x hx => by simp [ha, hf x hx]
    have hN : ∑ x ∈ Ω, a x ^ 2 * π x = 1 := by
      rw [← hnorm]; unfold normSq
      rw [tsum_eq_sum (s := Ω) (fun x hx => by simp [hf x hx])]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [ha, sq_abs]
    have hE := dirichletForm_abs_le hP hπ hrev Ω f hf
    rw [dirichletForm_eq_pos hP hrev Ω a ha0 haΩ] at hE
    set Ep := ∑ x ∈ Ω, π x * ∑' y, P x y * max (a x - a y) 0 ^ 2 with hEp
    rcases hh.lt_or_eq with hpos | hzero
    swap
    · subst hzero
      have : 0 ≤ Ep := Finset.sum_nonneg fun x _ => mul_nonneg (hπ x).le
        (tsum_nonneg fun y => mul_nonneg (hP.1 x y) (sq_nonneg _))
      nlinarith
    -- layer cake for `g = a²`
    have hLC := layer_cake hP hπ Ω h hbd _ (fun x => a x ^ 2) (fun x => sq_nonneg _)
      (fun x hx => by simp [haΩ x hx]) le_rfl
    rw [hN, mul_one] at hLC
    -- AM–GM, termwise
    set B := ∑ x ∈ Ω, π x * ∑' y, P x y * (if a y < a x then (a x + a y) ^ 2 else 0) with hB
    have hA_le := amgm_bound hP hπ Ω a ha0 h hpos
    have hB_le := sym_bound hP hπ hrev Ω a ha0 haΩ
    set B := ∑ x ∈ Ω, π x * ∑' y, P x y * (if a y < a x then (a x + a y) ^ 2 else 0) with hB
    rw [hN, mul_one] at hB_le
    -- conclude
    have h1 : h ≤ 1 / h * Ep + h / 4 * 2 := by
      have := hA_le
      have hh4 : h / 4 * B ≤ h / 4 * 2 := mul_le_mul_of_nonneg_left hB_le (by positivity)
      linarith
    have h2 : h ^ 2 / 2 ≤ Ep := by
      have : h * h ≤ h * (1 / h * Ep) + h * (h / 2) := by nlinarith
      have e : h * (1 / h * Ep) = Ep := by field_simp
      nlinarith
    linarith
  -- the admissible set is non-empty
  obtain ⟨x₀, hx₀⟩ := hΩ
  have hne : ∃ e, e ∈ {e | ∃ f : X → ℝ, (∀ x ∉ Ω, f x = 0) ∧ normSq π f = 1 ∧
      dirichletForm P π f = e} := by
    refine ⟨_, fun x => if x = x₀ then 1 / Real.sqrt (π x₀) else 0, ?_, ?_, rfl⟩
    · intro x hx
      have : x ≠ x₀ := fun h => hx (h ▸ hx₀)
      simp [this]
    · unfold normSq
      rw [tsum_eq_single x₀ (fun x hx => by simp [hx])]
      simp only [if_true]
      rw [div_pow, Real.sq_sqrt (hπ x₀).le]
      field_simp [(hπ x₀).ne']
  unfold dirichletEigenvalue
  refine le_csInf hne ?_
  rintro e ⟨f, hf, hn, rfl⟩
  exact key f hf hn
end
