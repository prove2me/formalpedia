-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.restriction_fourier_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:21:56.044359+00:00
-- url     : https://prove2.me/submissions/6074fbc4-ad3d-497c-b98a-9043dae6eb00

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting
import Definitions.Def_HypercliqueAC0_FixedDepth_Switching

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- `±1` sign of a bit. -/
def RFT_sg (b : Bool) : ℝ := if b then 1 else -1

/-- Uniform character `χ_S(x) = ∏_{i ∈ S} (±1)`. -/
def RFT_ch {X : Type} (S : Finset X) (x : X → Bool) : ℝ := ∏ i ∈ S, RFT_sg (x i)

/-- Uniform Fourier coefficient. -/
def RFT_fc {X : Type} [Fintype X] (g : (X → Bool) → ℝ) (S : Finset X) : ℝ :=
  (1 / 2 : ℝ) ^ Fintype.card X * ∑ x, g x * RFT_ch S x

lemma RFT_sg_mul_self (b : Bool) : RFT_sg b * RFT_sg b = 1 := by
  cases b <;> simp [RFT_sg]

lemma RFT_chi_half (b : Bool) : OAI.Problem313.BiasedFourier.chi (1 / 2) b = RFT_sg b := by
  have h : Real.sqrt ((1 / 2 : ℝ) * (1 - 1 / 2)) = 1 / 2 := by
    rw [show (1 / 2 : ℝ) * (1 - 1 / 2) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  cases b <;> simp only [OAI.Problem313.BiasedFourier.chi, h, RFT_sg] <;> norm_num

lemma RFT_weight_half {X : Type} [Fintype X] (x : X → Bool) :
    OAI.Problem313.BiasedFourier.weight (1 / 2) x = (1 / 2 : ℝ) ^ Fintype.card X := by
  unfold OAI.Problem313.BiasedFourier.weight
  rw [← Finset.prod_const_one (s := (Finset.univ : Finset X)), Finset.card_univ.symm,
    ← Finset.prod_const]
  · apply Finset.prod_congr rfl
    intro i _
    cases x i <;> simp [OAI.Problem313.BiasedFourier.scalarWeight] <;> norm_num

lemma RFT_coeff_half {X : Type} [Fintype X] (g : (X → Bool) → ℝ) (S : Finset X) :
    OAI.Problem313.BiasedFourier.coeff (1 / 2) g S = RFT_fc g S := by
  unfold OAI.Problem313.BiasedFourier.coeff RFT_fc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [RFT_weight_half]
  unfold OAI.Problem313.BiasedFourier.char RFT_ch
  simp only [RFT_chi_half]
  ring

lemma RFT_card_fun {X : Type} [Fintype X] :
    (Fintype.card (X → Bool) : ℝ) = 2 ^ Fintype.card X := by
  simp [Fintype.card_fun]

lemma RFT_half_pow_mul {X : Type} [Fintype X] :
    (1 / 2 : ℝ) ^ Fintype.card X * 2 ^ Fintype.card X = 1 := by
  rw [← mul_pow]; norm_num

/-- character as a product over all coordinates -/
lemma RFT_ch_univ {X : Type} [Fintype X] (S : Finset X) (x : X → Bool) :
    RFT_ch S x = ∏ i, (if i ∈ S then RFT_sg (x i) else 1) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter]; rfl

/-- Orthogonality of characters. -/
lemma RFT_orth {X : Type} [Fintype X] (A B : Finset X) :
    ∑ x : X → Bool, RFT_ch A x * RFT_ch B x = if A = B then 2 ^ Fintype.card X else 0 := by
  simp_rw [RFT_ch_univ, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => (if i ∈ A then RFT_sg b else 1) * (if i ∈ B then RFT_sg b else 1))]
  have hb : ∀ i, (∑ b : Bool, (if i ∈ A then RFT_sg b else 1) * (if i ∈ B then RFT_sg b else 1))
      = if (i ∈ A ↔ i ∈ B) then 2 else 0 := by
    intro i
    by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [ha, hb, RFT_sg] <;> norm_num
  simp_rw [hb]
  split_ifs with hAB
  · subst hAB; simp
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ A ↔ i ∈ B) := by
      by_contra hc; push Not at hc; exact hAB (Finset.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma RFT_ch_empty {X : Type} (x : X → Bool) : RFT_ch ∅ x = 1 := by simp [RFT_ch]

lemma RFT_sum_ch {X : Type} [Fintype X] (A : Finset X) :
    ∑ x : X → Bool, RFT_ch A x = if A = ∅ then 2 ^ Fintype.card X else 0 := by
  have := RFT_orth A ∅
  simpa [RFT_ch_empty] using this

/-- Completeness of characters. -/
lemma RFT_compl {X : Type} [Fintype X] (x y : X → Bool) :
    ∑ S : Finset X, RFT_ch S x * RFT_ch S y = if x = y then 2 ^ Fintype.card X else 0 := by
  have h1 : ∀ S : Finset X, RFT_ch S x * RFT_ch S y = ∏ i ∈ S, (RFT_sg (x i) * RFT_sg (y i)) := by
    intro S; unfold RFT_ch; rw [Finset.prod_mul_distrib]
  simp_rw [h1]
  have h2 := Finset.prod_add (fun i => RFT_sg (x i) * RFT_sg (y i)) (fun _ => (1 : ℝ))
    (Finset.univ : Finset X)
  simp only [Finset.prod_const_one, mul_one, Finset.powerset_univ] at h2
  rw [← h2]
  have hb : ∀ i, RFT_sg (x i) * RFT_sg (y i) + 1 = if x i = y i then 2 else 0 := by
    intro i; cases x i <;> cases y i <;> simp [RFT_sg] <;> norm_num
  simp_rw [hb]
  split_ifs with hxy
  · subst hxy; simp
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hc; push Not at hc; exact hxy (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Fourier inversion. -/
lemma RFT_inv {X : Type} [Fintype X] (g : (X → Bool) → ℝ) (y : X → Bool) :
    ∑ S : Finset X, RFT_fc g S * RFT_ch S y = g y := by
  unfold RFT_fc
  have : ∀ S : Finset X, (1 / 2 : ℝ) ^ Fintype.card X * (∑ x, g x * RFT_ch S x) * RFT_ch S y
      = (1 / 2 : ℝ) ^ Fintype.card X * ∑ x, g x * (RFT_ch S x * RFT_ch S y) := by
    intro S; rw [mul_assoc, Finset.sum_mul]; congr 1; apply Finset.sum_congr rfl; intros; ring
  simp_rw [this]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, RFT_compl]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← mul_assoc, mul_comm _ (g y), mul_assoc, RFT_half_pow_mul, mul_one]

/-- Merge free values `x` on `J` with fixed values `z` off `J`. -/
def RFT_pw {X : Type} (J : Finset X) (x z : X → Bool) : X → Bool :=
  fun e => if e ∈ J then x e else z e

lemma RFT_ch_pw {X : Type} (S J : Finset X) (x z : X → Bool) :
    RFT_ch S (RFT_pw J x z) = RFT_ch (S ∩ J) x * RFT_ch (S \ J) z := by
  unfold RFT_ch
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun e => e ∈ J), Finset.filter_mem_eq_inter,
    Finset.filter_notMem_eq_sdiff]
  congr 1
  · apply Finset.prod_congr rfl; intro e he
    simp [RFT_pw, (Finset.mem_inter.1 he).2]
  · apply Finset.prod_congr rfl; intro e he
    simp [RFT_pw, (Finset.mem_sdiff.1 he).2]

/-- Fourier coefficient of a restriction (`J` free, `z` fixed). -/
lemma RFT_fc_restrict {X : Type} [Fintype X] (G : (X → Bool) → ℝ) (J U : Finset X)
    (z : X → Bool) :
    RFT_fc (fun x => G (RFT_pw J x z)) U
      = ∑ S : Finset X, if S ∩ J = U then RFT_fc G S * RFT_ch (S \ J) z else 0 := by
  unfold RFT_fc
  have h1 : ∀ x : X → Bool, G (RFT_pw J x z) * RFT_ch U x =
      ∑ S : Finset X, RFT_fc G S * RFT_ch (S \ J) z * (RFT_ch (S ∩ J) x * RFT_ch U x) := by
    intro x
    rw [← RFT_inv G (RFT_pw J x z), Finset.sum_mul]
    apply Finset.sum_congr rfl; intro S _
    rw [RFT_ch_pw]; unfold RFT_fc; ring
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro S _
  rw [← Finset.mul_sum, RFT_orth]
  unfold RFT_fc
  split_ifs with h
  · rw [mul_comm, mul_assoc, mul_comm (2 ^ _ : ℝ), RFT_half_pow_mul, mul_one]
  · simp

/-- Averaging the squared restricted coefficient over the fixed values. -/
lemma RFT_avg_sq {X : Type} [Fintype X] (G : (X → Bool) → ℝ) (J U : Finset X) :
    (1 / 2 : ℝ) ^ Fintype.card X * ∑ z : X → Bool, (RFT_fc (fun x => G (RFT_pw J x z)) U) ^ 2
      = ∑ S : Finset X, if S ∩ J = U then (RFT_fc G S) ^ 2 else 0 := by
  simp_rw [RFT_fc_restrict, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro S _
  rw [Finset.sum_comm, Finset.mul_sum]
  have key : ∀ S' : Finset X,
      (1 / 2 : ℝ) ^ Fintype.card X * ∑ z : X → Bool,
        (if S ∩ J = U then RFT_fc G S * RFT_ch (S \ J) z else 0) *
          (if S' ∩ J = U then RFT_fc G S' * RFT_ch (S' \ J) z else 0)
        = if S' = S then (if S ∩ J = U then RFT_fc G S * RFT_fc G S else 0) else 0 := by
    intro S'
    by_cases h1 : S ∩ J = U
    · by_cases h2 : S' ∩ J = U
      · simp only [h1, h2, if_true]
        have : ∀ z : X → Bool, RFT_fc G S * RFT_ch (S \ J) z * (RFT_fc G S' * RFT_ch (S' \ J) z)
            = RFT_fc G S * RFT_fc G S' * (RFT_ch (S \ J) z * RFT_ch (S' \ J) z) := by
          intro z; ring
        simp_rw [this]
        rw [← Finset.mul_sum, RFT_orth]
        by_cases h3 : S' = S
        · subst h3; simp only [if_true]
          rw [mul_comm, mul_assoc, mul_comm (2 ^ _ : ℝ), RFT_half_pow_mul, mul_one]
        · have h4 : S \ J ≠ S' \ J := by
            intro h4; apply h3
            rw [← Finset.sdiff_union_inter S' J, ← Finset.sdiff_union_inter S J, h1, h2, h4]
          simp [h3, h4]
      · by_cases h3 : S' = S
        · subst h3; exact absurd h1 h2
        · simp [h2, h3]
    · simp [h1]
  simp_rw [key]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, sq]

/-- Regrouping by `S ∩ J`. -/
lemma RFT_regroup {X : Type} [Fintype X] (J : Finset X) (w : ℕ) (a : Finset X → ℝ) :
    ∑ U : Finset X, (if w < U.card then ∑ S : Finset X, (if S ∩ J = U then a S else 0) else 0)
      = ∑ S : Finset X, if w < (S ∩ J).card then a S else 0 := by
  have : ∀ U : Finset X, (if w < U.card then ∑ S : Finset X, (if S ∩ J = U then a S else 0) else 0)
      = ∑ S : Finset X, (if S ∩ J = U then (if w < (S ∩ J).card then a S else 0) else 0) := by
    intro U
    split_ifs with h
    · apply Finset.sum_congr rfl; intro S _
      split_ifs with h1 h2 <;> first | rfl | (subst h1; exact absurd h h2)
    · symm; apply Finset.sum_eq_zero; intro S _
      split_ifs with h1 h2
      · subst h1; exact absurd h2 h
      · rfl
      · rfl
  simp_rw [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  rw [Finset.sum_ite_eq]; simp

/-- Sum over subsets of a product of "in/out" factors. -/
lemma RFT_subset_sum {X : Type} [Fintype X] (a b : X → ℝ) :
    ∑ J : Finset X, ∏ e, (if e ∈ J then a e else b e) = ∏ e, (a e + b e) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  apply Finset.sum_congr rfl; intro J _
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff,
    Finset.univ_inter]

/-- Star-set probability weight. -/
def RFT_pi {X : Type} [Fintype X] (q : ℝ) (J : Finset X) : ℝ :=
  ∏ e, (if e ∈ J then q else 1 - q)

/-- The restriction with star set `J` and fixed values `z`. -/
def RFT_mk {X : Type} (J : Finset X) (z : X → Bool) : X → Option Bool :=
  fun e => if e ∈ J then none else some (z e)

/-- Per-coordinate split of the star weight according to a uniform bit. -/
def RFT_w2 (q : ℝ) : Option Bool → Bool → ℝ
  | none, _ => q / 2
  | some c, b => if c = b then (1 - q) / 2 else 0

lemma RFT_w2_sum (q : ℝ) (o : Option Bool) : ∑ b : Bool, RFT_w2 q o b = starWeight q o := by
  cases o with
  | none => simp [RFT_w2, starWeight]; ring
  | some c => cases c <;> simp [RFT_w2, starWeight]

lemma RFT_restrictFn_mk {X : Type} (J : Finset X) (z : X → Bool) (f : (X → Bool) → Bool) :
    restrictFn (RFT_mk J z) f = fun x => f (RFT_pw J x z) := by
  funext x
  unfold restrictFn
  congr 1
  funext e
  by_cases he : e ∈ J <;> simp [RFT_mk, RFT_pw, he]

/-- Splitting a random restriction into (fixed values, star set). -/
lemma RFT_decomp {X : Type} [Fintype X] (q : ℝ) (F : (X → Option Bool) → ℝ) :
    ∑ ρ : X → Option Bool, restrictionWeight q ρ * F ρ
      = ∑ z : X → Bool, ∑ J : Finset X,
          (1 / 2 : ℝ) ^ Fintype.card X * RFT_pi q J * F (RFT_mk J z) := by
  have h1 : ∀ ρ : X → Option Bool, restrictionWeight q ρ
      = ∑ z : X → Bool, ∏ e, RFT_w2 q (ρ e) (z e) := by
    intro ρ
    unfold restrictionWeight
    simp_rw [← RFT_w2_sum]
    exact Fintype.prod_sum (fun e b => RFT_w2 q (ρ e) b)
  simp_rw [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro z _
  symm
  have hfg : ∀ J : Finset X, (1 / 2 : ℝ) ^ Fintype.card X * RFT_pi q J * F (RFT_mk J z)
      = (∏ e, RFT_w2 q (RFT_mk J z e) (z e)) * F (RFT_mk J z) := by
    intro J
    congr 1
    unfold RFT_pi
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro e _
    by_cases he : e ∈ J <;> simp [RFT_mk, RFT_w2, he] <;> ring
  apply Finset.sum_bij_ne_zero (fun J _ _ => RFT_mk J z)
  · intros; exact Finset.mem_univ _
  · intro J1 _ _ J2 _ _ h
    ext e
    have := congrFun h e
    by_cases h1 : e ∈ J1 <;> by_cases h2 : e ∈ J2 <;> simp_all [RFT_mk]
  · intro ρ _ hρ
    have hne : ∀ e, ρ e = none ∨ ρ e = some (z e) := by
      intro e
      by_contra hc
      push Not at hc
      apply hρ
      have : ∏ e, RFT_w2 q (ρ e) (z e) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ e)
        rcases h : ρ e with _ | c
        · exact absurd h hc.1
        · have : c ≠ z e := fun h' => hc.2 (h.trans (by rw [h']))
          simp [RFT_w2, this]
      rw [this, zero_mul]
    have hmk : RFT_mk (Finset.univ.filter (fun e => ρ e = none)) z = ρ := by
      funext e
      rcases hne e with h | h <;> simp [RFT_mk, h]
    refine ⟨Finset.univ.filter (fun e => ρ e = none), Finset.mem_univ _, ?_, hmk⟩
    rw [hfg, hmk]; exact hρ
  · intro J _ _
    exact hfg J

lemma RFT_pi_nonneg {X : Type} [Fintype X] {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (J : Finset X) :
    0 ≤ RFT_pi q J := by
  unfold RFT_pi
  apply Finset.prod_nonneg; intro e _
  split_ifs <;> linarith

lemma RFT_pi_sum {X : Type} [Fintype X] (q : ℝ) : ∑ J : Finset X, RFT_pi q J = 1 := by
  unfold RFT_pi
  rw [RFT_subset_sum]; simp

lemma RFT_pi_mgf {X : Type} [Fintype X] (q : ℝ) (S : Finset X) :
    ∑ J : Finset X, RFT_pi q J * (1 / 2 : ℝ) ^ (S ∩ J).card = (1 - q / 2) ^ S.card := by
  have h : ∀ J : Finset X, RFT_pi q J * (1 / 2 : ℝ) ^ (S ∩ J).card
      = ∏ e, (if e ∈ J then q * (if e ∈ S then 1 / 2 else 1) else 1 - q) := by
    intro J
    unfold RFT_pi
    rw [← Finset.prod_const, ← Finset.univ_inter (S ∩ J), ← Finset.prod_ite_mem,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro e _
    by_cases h1 : e ∈ J <;> by_cases h2 : e ∈ S <;> simp [h1, h2]
  simp_rw [h]
  rw [RFT_subset_sum, ← Finset.prod_const, ← Finset.univ_inter S, ← Finset.prod_ite_mem]
  apply Finset.prod_congr rfl; intro e _
  by_cases h2 : e ∈ S <;> simp [h2] <;> ring

lemma RFT_tail_num (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (w m : ℕ)
    (hm : 4 * ((w : ℝ) + 1) ≤ q * m) :
    (2 : ℝ) ^ w * (1 - q / 2) ^ m ≤ 1 / 2 := by
  have h1 : (1 - q / 2) ^ m ≤ Real.exp (-(q / 2)) ^ m := by
    apply pow_le_pow_left₀ (by linarith)
    have := Real.add_one_le_exp (-(q / 2)); linarith
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp (m * -(q / 2)) ≤ Real.exp (-2 * ((w : ℝ) + 1)) := by
    apply Real.exp_le_exp.2; nlinarith
  have h3 : (2 : ℝ) ^ (w + 1) ≤ Real.exp (2 * ((w : ℝ) + 1)) := by
    have : Real.exp (2 * ((w : ℝ) + 1)) = Real.exp 2 ^ (w + 1) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this]
    apply pow_le_pow_left₀ (by norm_num)
    have := Real.add_one_le_exp 2; linarith
  have h4 : Real.exp (-2 * ((w : ℝ) + 1)) * Real.exp (2 * ((w : ℝ) + 1)) = 1 := by
    rw [← Real.exp_add]; simp
  have h5 : 0 ≤ Real.exp (-2 * ((w : ℝ) + 1)) := (Real.exp_pos _).le
  have h6 : (0 : ℝ) ≤ 2 ^ w := by positivity
  calc (2 : ℝ) ^ w * (1 - q / 2) ^ m ≤ 2 ^ w * Real.exp (-2 * ((w : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) h6
    _ ≤ 1 / 2 := by
        rw [pow_succ] at h3
        nlinarith

/-- Chernoff-type bound: the star set meets `S` in more than `w` points with prob. `≥ 1/2`. -/
lemma RFT_prob_half {X : Type} [Fintype X] (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (w : ℕ)
    (S : Finset X) (hS : 4 * ((w : ℝ) + 1) ≤ q * S.card) :
    1 / 2 ≤ ∑ J : Finset X, RFT_pi q J * (if w < (S ∩ J).card then 1 else 0) := by
  have hpt : ∀ J : Finset X, RFT_pi q J * (1 - 2 ^ w * (1 / 2 : ℝ) ^ (S ∩ J).card)
      ≤ RFT_pi q J * (if w < (S ∩ J).card then 1 else 0) := by
    intro J
    apply mul_le_mul_of_nonneg_left _ (RFT_pi_nonneg hq hq1 J)
    split_ifs with h
    · have : (0 : ℝ) ≤ 2 ^ w * (1 / 2) ^ (S ∩ J).card := by positivity
      linarith
    · push Not at h
      have : (2 : ℝ) ^ (S ∩ J).card ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) h
      have h2 : (2 : ℝ) ^ (S ∩ J).card * (1 / 2) ^ (S ∩ J).card = 1 := by
        rw [← mul_pow]; norm_num
      have : (0 : ℝ) ≤ (1 / 2) ^ (S ∩ J).card := by positivity
      nlinarith
  have hsum := Finset.sum_le_sum (fun J (_ : J ∈ (Finset.univ : Finset (Finset X))) => hpt J)
  have : ∑ J : Finset X, RFT_pi q J * (1 - 2 ^ w * (1 / 2 : ℝ) ^ (S ∩ J).card)
      = 1 - 2 ^ w * (1 - q / 2) ^ S.card := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, RFT_pi_sum, ← RFT_pi_mgf, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intros; ring
  have := RFT_tail_num q hq hq1 w S.card hS
  linarith

lemma RFT_sg_ch {X : Type} (i : X) (U : Finset X) (x : X → Bool) :
    RFT_sg (x i) * RFT_ch U x = RFT_ch (if i ∈ U then U.erase i else insert i U) x := by
  unfold RFT_ch
  split_ifs with h
  · rw [← Finset.mul_prod_erase U _ h, ← mul_assoc, RFT_sg_mul_self, one_mul]
  · rw [Finset.prod_insert h]

/-- Depth-`t` decision trees have no Fourier weight above level `t`. -/
lemma RFT_dt_coeff {X : Type} [Fintype X] {t : ℕ} {h : (X → Bool) → Bool}
    (hdt : DTDepthLE t h) : ∀ U : Finset X, t < U.card →
      ∑ x : X → Bool, boolReal h x * RFT_ch U x = 0 := by
  induction hdt with
  | const t b =>
    intro U hU
    have hc : ∀ x : X → Bool, boolReal (fun _ => b) x * RFT_ch U x
        = (if b then 1 else 0) * RFT_ch U x := fun x => rfl
    simp_rw [hc]
    rw [← Finset.mul_sum, RFT_sum_ch]
    have : U ≠ ∅ := by intro h; subst h; simp at hU
    simp [this]
  | query t i h h0 h1 ih0 ih1 =>
    intro U hU
    set V := if i ∈ U then U.erase i else insert i U with hV
    have hVc : t < V.card := by
      rw [hV]; split_ifs with hi
      · rw [Finset.card_erase_of_mem hi]; omega
      · rw [Finset.card_insert_of_notMem hi]; omega
    have key : ∀ x : X → Bool, boolReal h x * RFT_ch U x
        = (1 / 2) * (boolReal (fun x => h (Function.update x i true)) x * RFT_ch U x)
          + (1 / 2) * (boolReal (fun x => h (Function.update x i true)) x * RFT_ch V x)
          + (1 / 2) * (boolReal (fun x => h (Function.update x i false)) x * RFT_ch U x)
          - (1 / 2) * (boolReal (fun x => h (Function.update x i false)) x * RFT_ch V x) := by
      intro x
      rw [hV, ← RFT_sg_ch]
      rcases hx : x i with _ | _
      · have : Function.update x i false = x := by rw [← hx]; exact Function.update_eq_self i x
        have e0 : boolReal (fun x => h (Function.update x i false)) x = boolReal h x := by
          show (if h (Function.update x i false) = true then (1:ℝ) else 0) = _; rw [this]; rfl
        rw [e0]; simp [RFT_sg]; ring
      · have : Function.update x i true = x := by rw [← hx]; exact Function.update_eq_self i x
        have e0 : boolReal (fun x => h (Function.update x i true)) x = boolReal h x := by
          show (if h (Function.update x i true) = true then (1:ℝ) else 0) = _; rw [this]; rfl
        rw [e0]; simp [RFT_sg]; ring
    simp_rw [key]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    rw [ih0 U (by omega), ih0 V hVc, ih1 U (by omega), ih1 V hVc]
    ring

lemma RFT_sum_weight_half {X : Type} [Fintype X] :
    ∑ x : X → Bool, OAI.Problem313.BiasedFourier.weight (1 / 2) x = 1 := by
  simp_rw [RFT_weight_half]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, RFT_card_fun, mul_comm, RFT_half_pow_mul]

/-- Parseval at `p = 1/2`. -/
lemma RFT_parseval {X : Type} [Fintype X] (g : (X → Bool) → ℝ) :
    ∑ U : Finset X, RFT_fc g U ^ 2 = (1 / 2 : ℝ) ^ Fintype.card X * ∑ x, g x ^ 2 := by
  have h1 : ∀ U : Finset X, RFT_fc g U ^ 2 = (1 / 2 : ℝ) ^ Fintype.card X *
      ((1 / 2 : ℝ) ^ Fintype.card X * ∑ x, ∑ y, g x * g y * (RFT_ch U x * RFT_ch U y)) := by
    intro U
    unfold RFT_fc
    rw [sq, mul_mul_mul_comm, Finset.sum_mul_sum, mul_assoc]
    have : ∀ x y : X → Bool, g x * RFT_ch U x * (g y * RFT_ch U y)
        = g x * g y * (RFT_ch U x * RFT_ch U y) := by intros; ring
    simp_rw [this]
  simp_rw [h1, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset X))), ← Finset.mul_sum, RFT_compl]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← mul_assoc, ← Finset.sum_mul]
  have : ∀ x : X → Bool, g x * g x = g x ^ 2 := fun x => (sq _).symm
  simp_rw [this]
  linear_combination ((1 / 2 : ℝ) ^ Fintype.card X * ∑ x, g x ^ 2) * RFT_half_pow_mul (X := X)

/-- Fourier weight above level `w` is at most the indicator of "not depth `w`". -/
lemma RFT_high_le {X : Type} [Fintype X] (w : ℕ) (h : (X → Bool) → Bool) :
    ∑ U : Finset X, (if w < U.card then RFT_fc (boolReal h) U ^ 2 else 0)
      ≤ if ¬ DTDepthLE w h then 1 else 0 := by
  split_ifs with hdt
  · apply le_of_eq
    apply Finset.sum_eq_zero; intro U _
    split_ifs with hU
    · unfold RFT_fc; rw [RFT_dt_coeff hdt U hU]; simp
    · rfl
  · calc ∑ U : Finset X, (if w < U.card then RFT_fc (boolReal h) U ^ 2 else 0)
          ≤ ∑ U : Finset X, RFT_fc (boolReal h) U ^ 2 := by
            apply Finset.sum_le_sum; intro U _; split_ifs <;> [exact le_rfl; positivity]
        _ = ∑ x, OAI.Problem313.BiasedFourier.weight (1 / 2) x * (boolReal h x) ^ 2 := by
            rw [RFT_parseval, Finset.mul_sum]
            simp_rw [RFT_weight_half]
        _ ≤ ∑ x, OAI.Problem313.BiasedFourier.weight (1 / 2) x := by
            apply Finset.sum_le_sum; intro x _
            rw [RFT_weight_half]
            have : (boolReal h x) ^ 2 ≤ 1 := by unfold boolReal; split_ifs <;> norm_num
            have : (0 : ℝ) ≤ (1 / 2) ^ Fintype.card X := by positivity
            nlinarith
        _ = 1 := RFT_sum_weight_half
lemma RFT_rw_nonneg {X : Type} [Fintype X] {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (ρ : X → Option Bool) : 0 ≤ restrictionWeight q ρ := by
  unfold restrictionWeight
  apply Finset.prod_nonneg; intro e _
  cases ρ e <;> simp [starWeight] <;> linarith

/-- Restriction identity: averaged high-level weight of restrictions. -/
lemma RFT_restrict_identity {X : Type} [Fintype X] (q : ℝ) (f : (X → Bool) → Bool) (w : ℕ) :
    ∑ ρ : X → Option Bool, restrictionWeight q ρ *
        ∑ U : Finset X, (if w < U.card then RFT_fc (boolReal (restrictFn ρ f)) U ^ 2 else 0)
      = ∑ J : Finset X, RFT_pi q J *
          ∑ S : Finset X, (if w < (S ∩ J).card then RFT_fc (boolReal f) S ^ 2 else 0) := by
  rw [RFT_decomp, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro J _
  rw [← RFT_regroup]
  simp_rw [← RFT_avg_sq, RFT_restrictFn_mk]
  have : ∀ U : Finset X, (if w < U.card then (1 / 2 : ℝ) ^ Fintype.card X *
      ∑ z : X → Bool, RFT_fc (fun x => boolReal f (RFT_pw J x z)) U ^ 2 else 0)
      = (1 / 2 : ℝ) ^ Fintype.card X *
      ∑ z : X → Bool, (if w < U.card then RFT_fc (fun x => boolReal f (RFT_pw J x z)) U ^ 2
        else 0) := by
    intro U; split_ifs <;> simp
  simp_rw [this, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro U _
  rw [← mul_assoc, mul_comm (RFT_pi q J)]
  rfl

theorem RFT_main {X : Type} [Fintype X] (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (f : (X → Bool) → Bool) (w : ℕ) (D : ℝ)
    (hD : 4 * ((w : ℝ) + 1) ≤ q * D) :
    fourierTailGE (1 / 2) (boolReal f) D ≤
      2 * restrictionProb q (fun ρ => ¬ DTDepthLE w (restrictFn ρ f)) := by
  set a : Finset X → ℝ := fun S => RFT_fc (boolReal f) S ^ 2 with ha
  have hP : ∀ S : Finset X, 0 ≤ ∑ J : Finset X, RFT_pi q J * (if w < (S ∩ J).card then 1 else 0) := by
    intro S; apply Finset.sum_nonneg; intro J _
    apply mul_nonneg (RFT_pi_nonneg hq.le hq1 J); split_ifs <;> norm_num
  calc fourierTailGE (1 / 2) (boolReal f) D
      = ∑ S : Finset X, (if D ≤ (S.card : ℝ) then a S else 0) := by
        unfold fourierTailGE fourierCoeff
        simp_rw [RFT_coeff_half]
        rfl
    _ ≤ ∑ S : Finset X, 2 * ((∑ J : Finset X, RFT_pi q J *
          (if w < (S ∩ J).card then 1 else 0)) * a S) := by
        apply Finset.sum_le_sum; intro S _
        have haS : 0 ≤ a S := sq_nonneg _
        split_ifs with hS
        · have h1 := RFT_prob_half q hq.le hq1 w S (by nlinarith)
          nlinarith
        · have := hP S; positivity
    _ = 2 * ∑ J : Finset X, RFT_pi q J *
          ∑ S : Finset X, (if w < (S ∩ J).card then a S else 0) := by
        rw [← Finset.mul_sum]; congr 1
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro J _
        apply Finset.sum_congr rfl; intro S _
        split_ifs <;> ring
    _ = 2 * ∑ ρ : X → Option Bool, restrictionWeight q ρ *
          ∑ U : Finset X, (if w < U.card then RFT_fc (boolReal (restrictFn ρ f)) U ^ 2 else 0) := by
        rw [RFT_restrict_identity]
    _ ≤ 2 * restrictionProb q (fun ρ => ¬ DTDepthLE w (restrictFn ρ f)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        unfold restrictionProb
        apply Finset.sum_le_sum; intro ρ _
        have h1 := RFT_high_le w (restrictFn ρ f)
        have h2 := RFT_rw_nonneg hq.le hq1 ρ
        calc restrictionWeight q ρ * ∑ U : Finset X,
              (if w < U.card then RFT_fc (boolReal (restrictFn ρ f)) U ^ 2 else 0)
            ≤ restrictionWeight q ρ * (if ¬ DTDepthLE w (restrictFn ρ f) then 1 else 0) :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = _ := by by_cases hd : DTDepthLE w (restrictFn ρ f) <;> simp [hd]

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {X : Type} [Fintype X] (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (f : (X → Bool) → Bool) (w : ℕ) (D : ℝ)
    (hD : 4 * ((w : ℝ) + 1) ≤ q * D) :
    fourierTailGE (1 / 2) (boolReal f) D ≤
      2 * restrictionProb q (fun ρ => ¬ DTDepthLE w (restrictFn ρ f)) :=
  RFT_main q hq hq1 f w D hD

