-- Prove2me | solution 1 for NarrowDNF.Approx.hatami_step_two_small_low_degree_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:14:18.182181+00:00
-- url     : https://prove2.me/submissions/3a95ad21-b14a-4394-9253-13f1a23a6ba1

import Mathlib
import Definitions.Def_NarrowDNF_Approx_Probability
section
set_option autoImplicit false

/-! Base library for the Step II leaf (copied from the q338 Blueprint `HatBP` and `HatPartA`). -/

namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx

variable {n : ℕ}

/-- product weight -/
noncomputable def w (p : ℝ) (x : Cube n) : ℝ := ∏ i, FriedgutCoalition.bern p (x i)

/-- the `p`-biased character value on one bit -/
noncomputable def r (p : ℝ) (b : Bool) : ℝ :=
  if b then Real.sqrt ((1 - p) / p) else -Real.sqrt (p / (1 - p))

noncomputable def chi (p : ℝ) (S : Finset (Fin n)) (x : Cube n) : ℝ := ∏ i ∈ S, r p (x i)

noncomputable def ind (f : Cube n → Bool) (x : Cube n) : ℝ := if f x then 1 else 0

noncomputable def fhat (p : ℝ) (f : Cube n → Bool) (S : Finset (Fin n)) : ℝ :=
  expect p (fun y => ind f y * chi p S y)

/-- Hatami's `F_S` -/
noncomputable def FS (p : ℝ) (f : Cube n → Bool) (S : Finset (Fin n)) (x : Cube n) : ℝ :=
  fhat p f S * chi p S x

def DependsOn {β : Type*} (D : Finset (Fin n)) (g : Cube n → β) : Prop :=
  ∀ x y : Cube n, (∀ i ∈ D, x i = y i) → g x = g y

/-! ## basic helpers -/

lemma sum_prod_cube' {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → Bool → ℝ) :
    ∑ x : ι → Bool, ∏ i, g i (x i) = ∏ i, ∑ b : Bool, g i b := by
  have := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool)) g
  rw [this, Fintype.piFinset_univ]

lemma bern_sum (p : ℝ) : ∑ b : Bool, FriedgutCoalition.bern p b = 1 := by
  simp [FriedgutCoalition.bern]

lemma expect_def (p : ℝ) (c : Cube n → ℝ) :
    expect p c = ∑ x : Cube n, w p x * c x := rfl

lemma bern_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (b : Bool) : 0 < FriedgutCoalition.bern p b := by
  cases b <;> simp [FriedgutCoalition.bern] <;> linarith

lemma bern_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ FriedgutCoalition.bern p b := by
  cases b <;> simp [FriedgutCoalition.bern] <;> linarith

lemma w_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (x : Cube n) : 0 < w p x :=
  Finset.prod_pos (fun i _ => bern_pos p hp hp1 (x i))

lemma w_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : Cube n) : 0 ≤ w p x :=
  Finset.prod_nonneg (fun i _ => bern_nonneg p hp hp1 (x i))

lemma sum_w (p : ℝ) : ∑ x : Cube n, w p x = 1 := by
  unfold w
  rw [sum_prod_cube' (fun _ b => FriedgutCoalition.bern p b)]
  simp only [bern_sum, Finset.prod_const_one]

lemma expect_one (p : ℝ) : expect p (fun _ : Cube n => (1 : ℝ)) = 1 := by
  rw [expect_def]; simp [sum_w]

lemma expect_add (p : ℝ) (c d : Cube n → ℝ) :
    expect p (fun x => c x + d x) = expect p c + expect p d := by
  simp only [expect_def, mul_add, Finset.sum_add_distrib]

lemma expect_sub (p : ℝ) (c d : Cube n → ℝ) :
    expect p (fun x => c x - d x) = expect p c - expect p d := by
  simp only [expect_def, mul_sub, Finset.sum_sub_distrib]

lemma expect_smul (p : ℝ) (a : ℝ) (c : Cube n → ℝ) :
    expect p (fun x => a * c x) = a * expect p c := by
  simp only [expect_def, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by ring)

lemma expect_sum {ι : Type*} (p : ℝ) (s : Finset ι) (c : ι → Cube n → ℝ) :
    expect p (fun x => ∑ i ∈ s, c i x) = ∑ i ∈ s, expect p (c i) := by
  simp only [expect_def, Finset.mul_sum]
  exact Finset.sum_comm

lemma expect_mono (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (c d : Cube n → ℝ) (h : ∀ x, c x ≤ d x) :
    expect p c ≤ expect p d := by
  simp only [expect_def]
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (w_nonneg p hp hp1 x))

lemma expect_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (c : Cube n → ℝ) (h : ∀ x, 0 ≤ c x) :
    0 ≤ expect p c := by
  have := expect_mono p hp hp1 (fun _ => 0) c h
  simpa [expect_def] using this

lemma expect_congr (p : ℝ) (c d : Cube n → ℝ) (h : ∀ x, c x = d x) :
    expect p c = expect p d := by
  have : c = d := funext h
  rw [this]

/-! ## Part A -/

theorem expect_prod_coord (p : ℝ) (A : Finset (Fin n)) (φ : Fin n → Bool → ℝ) :
    expect p (fun x => ∏ i ∈ A, φ i (x i)) = ∏ i ∈ A, (p * φ i true + (1 - p) * φ i false) := by
  classical
  rw [expect_def]
  have h1 : ∀ x : Cube n, w p x * ∏ i ∈ A, φ i (x i) =
      ∏ i, (FriedgutCoalition.bern p (x i) * (if i ∈ A then φ i (x i) else 1)) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
    rfl
  simp only [h1]
  rw [sum_prod_cube' (fun i b => FriedgutCoalition.bern p b * (if i ∈ A then φ i b else 1))]
  have h2 : ∀ i, ∑ b : Bool, FriedgutCoalition.bern p b * (if i ∈ A then φ i b else 1) =
      if i ∈ A then p * φ i true + (1 - p) * φ i false else 1 := by
    intro i
    by_cases hi : i ∈ A <;> simp [hi, FriedgutCoalition.bern] <;> ring
  simp only [h2]
  rw [Finset.prod_ite_mem, Finset.univ_inter]


/-! ### pairing along coordinate `i` -/

lemma sum_pair (i : Fin n) (Φ : Cube n → ℝ) :
    2 * ∑ x : Cube n, Φ x =
      ∑ x : Cube n, (Φ (Function.update x i true) + Φ (Function.update x i false)) := by
  let σ : Cube n → Cube n := fun x => Function.update x i (!x i)
  have hσ : Function.Involutive σ := by
    intro x
    simp only [σ]
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  have h1 : ∑ x : Cube n, Φ (σ x) = ∑ x : Cube n, Φ x :=
    Equiv.sum_comp (Function.Involutive.toPerm σ hσ) Φ
  have h2 : ∀ x, Φ x + Φ (σ x) = Φ (Function.update x i true) + Φ (Function.update x i false) := by
    intro x
    cases hx : x i
    · have : Function.update x i false = x := by rw [← hx]; exact Function.update_eq_self i x
      simp only [σ, hx, Bool.not_false, this]; ring
    · have : Function.update x i true = x := by rw [← hx]; exact Function.update_eq_self i x
      simp only [σ, hx, Bool.not_true, this]
  rw [← Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_add_distrib, h1]
  ring

/-- the weight of the coordinates other than `i` -/
noncomputable def wr (p : ℝ) (i : Fin n) (x : Cube n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, FriedgutCoalition.bern p (x j)

lemma wr_update (p : ℝ) (i : Fin n) (x : Cube n) (b : Bool) :
    wr p i (Function.update x i b) = wr p i x := by
  unfold wr
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma w_update (p : ℝ) (i : Fin n) (x : Cube n) (b : Bool) :
    w p (Function.update x i b) = FriedgutCoalition.bern p b * wr p i x := by
  unfold w
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  rw [← wr_update p i x b]
  rfl

lemma expect_pair (p : ℝ) (i : Fin n) (c : Cube n → ℝ) :
    2 * expect p c = ∑ x : Cube n, wr p i x *
      (p * c (Function.update x i true) + (1 - p) * c (Function.update x i false)) := by
  rw [expect_def, sum_pair i]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [w_update, w_update]
  simp only [FriedgutCoalition.bern]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

theorem expect_mul_eq_zero_of_mean_zero (p : ℝ) (i : Fin n) (G H : Cube n → ℝ)
    (hG : ∀ x, p * G (Function.update x i true) + (1 - p) * G (Function.update x i false) = 0)
    (hH : ∀ x b, H (Function.update x i b) = H x) :
    expect p (fun x => G x * H x) = 0 := by
  have := expect_pair p i (fun x => G x * H x)
  simp only [hH] at this
  have h0 : ∀ x : Cube n, wr p i x * (p * (G (Function.update x i true) * H x) +
      (1 - p) * (G (Function.update x i false) * H x)) = 0 := by
    intro x
    have := hG x
    linear_combination (wr p i x * H x) * this
  simp only [h0, Finset.sum_const_zero] at this
  linarith


/-! ## the characters -/

lemma mul_sqrt_div (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) : a * Real.sqrt (b / a) = Real.sqrt (a * b) := by
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  have hs := Real.mul_self_sqrt (show 0 ≤ b / a by positivity)
  rw [show (a * Real.sqrt (b / a)) * (a * Real.sqrt (b / a)) =
    a ^ 2 * (Real.sqrt (b / a) * Real.sqrt (b / a)) by ring, hs]
  field_simp

lemma p_mul_r_true (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p * r p true = Real.sqrt (p * (1 - p)) := by
  simp only [r, if_true]
  exact mul_sqrt_div p (1 - p) hp (by linarith)

lemma q_mul_r_false (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (1 - p) * r p false = -Real.sqrt (p * (1 - p)) := by
  simp only [r, Bool.false_eq_true, if_false]
  rw [mul_neg, mul_sqrt_div (1 - p) p (by linarith) hp.le, mul_comm]

lemma r_true_sq (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : r p true * r p true = (1 - p) / p := by
  simp only [r, if_true]
  exact Real.mul_self_sqrt (div_nonneg (by linarith) hp.le)

lemma r_false_sq (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : r p false * r p false = p / (1 - p) := by
  simp only [r, Bool.false_eq_true, if_false, neg_mul_neg]
  exact Real.mul_self_sqrt (div_nonneg hp.le (by linarith))

lemma r_true_mul_false (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : r p true * r p false = -1 := by
  simp only [r, if_true, Bool.false_eq_true, if_false, mul_neg]
  rw [← Real.sqrt_mul (div_nonneg (by linarith) hp.le)]
  have : (1 - p) / p * (p / (1 - p)) = 1 := by
    field_simp [show (1 - p) ≠ 0 by linarith, hp.ne']
  rw [this, Real.sqrt_one]

lemma r_mean (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : p * r p true + (1 - p) * r p false = 0 := by
  rw [p_mul_r_true p hp hp1, q_mul_r_false p hp hp1]; ring

lemma r_var (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p * (r p true * r p true) + (1 - p) * (r p false * r p false) = 1 := by
  rw [r_true_sq p hp hp1, r_false_sq p hp hp1]
  field_simp [show (1 - p) ≠ 0 by linarith, hp.ne']
  ring

lemma kernel (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (b c : Bool) :
    1 + r p b * r p c = if b = c then 1 / FriedgutCoalition.bern p c else 0 := by
  have h1 := r_true_sq p hp hp1
  have h2 := r_false_sq p hp hp1
  have h3 := r_true_mul_false p hp hp1
  have hq : (1 - p) ≠ 0 := by linarith
  cases b <;> cases c <;> simp only [FriedgutCoalition.bern, if_true, Bool.false_eq_true,
    if_false, reduceCtorEq] 
  · rw [h2]; field_simp; ring
  · rw [mul_comm, h3]; ring
  · rw [h3]; ring
  · rw [h1]; field_simp; ring

lemma chi_eq_univ (p : ℝ) (S : Finset (Fin n)) (x : Cube n) :
    chi p S x = ∏ i, (if i ∈ S then r p (x i) else 1) := by
  classical
  rw [Finset.prod_ite_mem, Finset.univ_inter]; rfl

lemma expect_chi_mul (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (S T : Finset (Fin n)) :
    expect p (fun x => chi p S x * chi p T x) = if S = T then 1 else 0 := by
  classical
  have h1 : ∀ x : Cube n, chi p S x * chi p T x =
      ∏ i ∈ Finset.univ, (fun i b => (if i ∈ S then r p b else 1) * (if i ∈ T then r p b else 1)) i (x i) := by
    intro x
    rw [chi_eq_univ, chi_eq_univ, ← Finset.prod_mul_distrib]
  rw [expect_congr p _ _ h1, expect_prod_coord p Finset.univ
    (fun i b => (if i ∈ S then r p b else 1) * (if i ∈ T then r p b else 1))]
  have hm := r_mean p hp hp1
  have hv := r_var p hp hp1
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl]
    refine Finset.prod_eq_one (fun i _ => ?_)
    by_cases hi : i ∈ S
    · simp only [hi, if_true]; exact hv
    · simp only [hi, if_false]; ring
  · rw [if_neg hST]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra hc
      push Not at hc
      exact hST (Finset.ext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases hS : i ∈ S
    · have hT : i ∉ T := fun h => hi ⟨fun _ => h, fun _ => hS⟩
      simp only [hS, hT, if_true, if_false, mul_one]; exact hm
    · have hT : i ∈ T := by by_contra h; exact hi ⟨fun h' => absurd h' hS, fun h' => absurd h' h⟩
      simp only [hS, hT, if_true, if_false, one_mul]; exact hm

theorem expect_sq_sum_FS (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool)
    (𝒜 : Finset (Finset (Fin n))) :
    expect p (fun x => (∑ S ∈ 𝒜, FS p f S x) ^ 2) = ∑ S ∈ 𝒜, fhat p f S ^ 2 := by
  classical
  have h1 : ∀ x : Cube n, (∑ S ∈ 𝒜, FS p f S x) ^ 2 =
      ∑ S ∈ 𝒜, ∑ T ∈ 𝒜, (fhat p f S * fhat p f T) * (chi p S x * chi p T x) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
    simp only [FS]; ring
  rw [expect_congr p _ _ h1, expect_sum]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [expect_sum]
  simp only [expect_smul, expect_chi_mul p hp hp1, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos hS, sq]

theorem fourier_inversion (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (x : Cube n) :
    ind f x = ∑ S : Finset (Fin n), FS p f S x := by
  classical
  have h1 : ∀ S : Finset (Fin n), FS p f S x =
      ∑ y : Cube n, w p y * ind f y * ∏ i ∈ S, (r p (y i) * r p (x i)) := by
    intro S
    simp only [FS, fhat, expect_def, Finset.sum_mul, chi, Finset.prod_mul_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have h2 : ∀ y : Cube n, ∑ S : Finset (Fin n), ∏ i ∈ S, (r p (y i) * r p (x i)) =
      if y = x then 1 / w p x else 0 := by
    intro y
    rw [← Finset.powerset_univ, ← Finset.prod_one_add]
    simp only [kernel p hp hp1]
    rw [Fintype.prod_ite_zero]
    by_cases hyx : y = x
    · subst hyx; simp [w, Finset.prod_inv_distrib]
    · have : ¬ ∀ i, y i = x i := fun h => hyx (funext h)
      simp [this, hyx]
  simp only [h2, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have := w_pos p hp hp1 x
  field_simp


lemma ind_nonneg (f : Cube n → Bool) (x : Cube n) : 0 ≤ ind f x := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (f : Cube n → Bool) (x : Cube n) : ind f x ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem FS_dependsOn (p : ℝ) (f : Cube n → Bool) (S : Finset (Fin n)) :
    DependsOn S (FS p f S) := by
  intro x y h
  simp only [FS, chi]
  congr 1
  exact Finset.prod_congr rfl (fun i hi => by rw [h i hi])

lemma chi_update_mem (p : ℝ) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (x : Cube n) (b : Bool) :
    chi p S (Function.update x i b) = r p b * ∏ j ∈ S.erase i, r p (x j) := by
  unfold chi
  rw [← Finset.mul_prod_erase S _ hi, Function.update_self]
  congr 1
  exact Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])

theorem FS_mean_zero (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool)
    (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (x : Cube n) :
    p * FS p f S (Function.update x i true) + (1 - p) * FS p f S (Function.update x i false) = 0 := by
  simp only [FS, chi_update_mem p S i hi]
  linear_combination (fhat p f S * ∏ j ∈ S.erase i, r p (x j)) * r_mean p hp hp1


/-! ## influences -/

lemma expect_coord (p : ℝ) (i : Fin n) (φ : Bool → ℝ) :
    expect p (fun y => φ (y i)) = p * φ true + (1 - p) * φ false := by
  have := expect_prod_coord p {i} (fun _ b => φ b)
  simpa using this

lemma pInfl_two (p : ℝ) (f : Cube n → Bool) (i : Fin n) :
    2 * FriedgutCoalition.pInfl p f i = ∑ x : Cube n, wr p i x *
      (2 * p * (1 - p) * (ind f (Function.update x i true) - ind f (Function.update x i false)) ^ 2) := by
  classical
  have h1 : FriedgutCoalition.pInfl p f i = expect p (fun x =>
      p * (if f x = f (Function.update x i true) then 0 else 1) +
      (1 - p) * (if f x = f (Function.update x i false) then 0 else 1)) := by
    unfold FriedgutCoalition.pInfl
    rw [expect_def]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have := expect_coord p i (fun b => if f x = f (Function.update x i b) then (0 : ℝ) else 1)
    rw [expect_def] at this
    rw [← this, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [mul_assoc]
    congr 2
    by_cases h : f x = f (Function.update x i (y i)) <;> simp [h]
  rw [h1, expect_pair p i]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Function.update_idem, if_true]
  congr 1
  unfold ind
  cases f (Function.update x i true) <;> cases f (Function.update x i false) <;> simp <;> ring

lemma ind_sub_avg (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (i : Fin n) (x : Cube n) :
    ind f x - (p * ind f (Function.update x i true) + (1 - p) * ind f (Function.update x i false)) =
      ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), FS p f S x := by
  classical
  rw [fourier_inversion p hp hp1 f x, fourier_inversion p hp hp1 f (Function.update x i true),
    fourier_inversion p hp hp1 f (Function.update x i false), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have := FS_mean_zero p hp hp1 f S i hi x
    linarith
  · rw [if_neg hi]
    have e : ∀ b, FS p f S (Function.update x i b) = FS p f S x := by
      intro b
      apply FS_dependsOn
      intro j hj
      have : j ≠ i := fun h => hi (h ▸ hj)
      rw [Function.update_of_ne this]
    rw [e, e]
    ring

lemma pInfl_eq (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (i : Fin n) :
    FriedgutCoalition.pInfl p f i = 2 * ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), fhat p f S ^ 2 := by
  classical
  rw [← expect_sq_sum_FS p hp hp1 f]
  rw [expect_congr p (fun x => (∑ S ∈ Finset.univ.filter (fun S => i ∈ S), FS p f S x) ^ 2)
    (fun x => (ind f x - (p * ind f (Function.update x i true) +
      (1 - p) * ind f (Function.update x i false))) ^ 2)
    (fun x => by rw [ind_sub_avg p hp hp1 f i x])]
  have h2 := expect_pair p i (fun x =>
    (ind f x - (p * ind f (Function.update x i true) + (1 - p) * ind f (Function.update x i false))) ^ 2)
  simp only [Function.update_idem] at h2
  have h3 : ∀ x : Cube n, wr p i x * (p * (ind f (Function.update x i true) -
      (p * ind f (Function.update x i true) + (1 - p) * ind f (Function.update x i false))) ^ 2 +
      (1 - p) * (ind f (Function.update x i false) -
      (p * ind f (Function.update x i true) + (1 - p) * ind f (Function.update x i false))) ^ 2) =
      (1 / 2) * (wr p i x * (2 * p * (1 - p) *
        (ind f (Function.update x i true) - ind f (Function.update x i false)) ^ 2)) := by
    intro x; ring
  simp only [h3, ← Finset.mul_sum] at h2
  have h4 := pInfl_two p f i
  linarith

theorem totalPInfl_eq (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) :
    FriedgutCoalition.totalPInfl p f = 2 * ∑ S : Finset (Fin n), (S.card : ℝ) * fhat p f S ^ 2 := by
  classical
  unfold FriedgutCoalition.totalPInfl
  simp only [pInfl_eq p hp hp1, ← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-! ## Part C -/


end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
/-! Blueprint for `NarrowDNF.Approx.hatami_step_two_small_low_degree_mass` (Hatami (11), Bourgain's step),
following O'Donnell, *Analysis of Boolean Functions*, proof of Theorem 10.47 (randomization/symmetrization),
with Hölder replaced by Young's inequality and only the `L⁴` un-symmetrization.

Notation: `c = 2/5`; `ρσ j = ±c` according to the sign bit `σ j` (`rhoOf`); `σ` ranges over the uniform cube
(`p = 1/2`, where `chi (1/2) S σ = ∏_{j∈S} ±1`). -/
/-! ## Definitions -/
/-- general Walsh coefficient `φ̂(S) = E[φ χ_S]` -/
noncomputable def coef (p : ℝ) (φ : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  expect p (fun y => φ y * chi p S y)

/-- the multiplier operator `T_ρ φ = Σ_S ρ^S φ̂(S) χ_S` -/
noncomputable def Top (p : ℝ) (ρ : Fin n → ℝ) (φ : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ S : Finset (Fin n), (∏ j ∈ S, ρ j) * coef p φ S * chi p S x

/-- the sign vector scaled by `c` -/
noncomputable def rhoOf (c : ℝ) (σ : Cube n) : Fin n → ℝ := fun j => if σ j then c else -c

/-- the discrete derivative `L_i 1_f = 1_f - E_i 1_f` -/
noncomputable def gder (p : ℝ) (f : Cube n → Bool) (i : Fin n) (x : Cube n) : ℝ :=
  ind f x - (p * ind f (Function.update x i true) + (1 - p) * ind f (Function.update x i false))

/-- the sets of size at most `K` -/
def low (n K : ℕ) : Finset (Finset (Fin n)) := Finset.univ.filter (fun S => S.card ≤ K)

/-- `Q_i(x) = Σ_{S ∋ i, |S| ≤ K} c^{2|S|} F_S(x)²` -/
noncomputable def Qc (p : ℝ) (f : Cube n → Bool) (K : ℕ) (i : Fin n) (x : Cube n) : ℝ :=
  ∑ S ∈ low n K, ((2 / 5 : ℝ) ^ S.card * (if i ∈ S then FS p f S x else 0)) ^ 2

/-- the notable coordinates `J'_x = {i : Q_i(x) ≥ τ}` -/
noncomputable def Jx (p : ℝ) (f : Cube n → Bool) (K : ℕ) (τ : ℝ) (x : Cube n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => τ ≤ Qc p f K i x)

/-- `V(x) = Σ_{|S| ≤ K} F_S(x)²` -/
noncomputable def Vx (p : ℝ) (f : Cube n → Bool) (K : ℕ) (x : Cube n) : ℝ :=
  ∑ S ∈ low n K, FS p f S x ^ 2

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartO
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
theorem inversion (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (φ : Cube n → ℝ) (x : Cube n) :
    φ x = ∑ S : Finset (Fin n), coef p φ S * chi p S x := by
  classical
  have h1 : ∀ S : Finset (Fin n), coef p φ S * chi p S x =
      ∑ y : Cube n, w p y * φ y * ∏ i ∈ S, (r p (y i) * r p (x i)) := by
    intro S
    simp only [coef, expect_def, Finset.sum_mul, chi, Finset.prod_mul_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have h2 : ∀ y : Cube n, ∑ S : Finset (Fin n), ∏ i ∈ S, (r p (y i) * r p (x i)) =
      if y = x then 1 / w p x else 0 := by
    intro y
    rw [← Finset.powerset_univ, ← Finset.prod_one_add]
    simp only [kernel p hp hp1]
    rw [Fintype.prod_ite_zero]
    by_cases hyx : y = x
    · subst hyx; simp [w, Finset.prod_inv_distrib]
    · have : ¬ ∀ i, y i = x i := fun h => hyx (funext h)
      simp [this, hyx]
  simp only [h2, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have := w_pos p hp hp1 x
  field_simp

end NarrowDNF.Dev.Bg.PartO
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
/-! ## Part O: the operators `T_ρ` -/

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartO
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
lemma expect_Top_mul_left (p : ℝ) (ρ : Fin n → ℝ) (φ ψ : Cube n → ℝ) :
    expect p (fun x => Top p ρ φ x * ψ x) =
      ∑ S : Finset (Fin n), (∏ j ∈ S, ρ j) * coef p φ S * coef p ψ S := by
  simp only [Top, Finset.sum_mul]
  rw [expect_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [show coef p ψ S = expect p (fun y => ψ y * chi p S y) from rfl, ← expect_smul]
  exact expect_congr _ _ _ (fun x => by ring)

end NarrowDNF.Dev.Bg.PartO
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartO
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
theorem expect_Top_mul (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (ρ : Fin n → ℝ) (φ ψ : Cube n → ℝ) :
    expect p (fun x => Top p ρ φ x * ψ x) = expect p (fun x => φ x * Top p ρ ψ x) := by
  rw [expect_Top_mul_left, expect_congr p (fun x => φ x * Top p ρ ψ x)
    (fun x => Top p ρ ψ x * φ x) (fun x => mul_comm _ _), expect_Top_mul_left]
  exact Finset.sum_congr rfl (fun S _ => by ring)

end NarrowDNF.Dev.Bg.PartO
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
alias expect_Top_mul := NarrowDNF.Dev.Bg.PartO.expect_Top_mul

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartO
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
lemma Top_one (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (φ : Cube n → ℝ) (x : Cube n) :
    Top p (fun _ => 1) φ x = φ x := by
  simp only [Top, Finset.prod_const_one, one_mul]
  exact (inversion p hp hp1 φ x).symm

/-- the one-coordinate operator -/
noncomputable def Tj (p : ℝ) (j : Fin n) (t : ℝ) (φ : Cube n → ℝ) (x : Cube n) : ℝ :=
  (p * φ (Function.update x j true) + (1 - p) * φ (Function.update x j false)) +
    t * (φ x - (p * φ (Function.update x j true) + (1 - p) * φ (Function.update x j false)))

lemma chi_avg (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (S : Finset (Fin n)) (j : Fin n) (x : Cube n) :
    p * chi p S (Function.update x j true) + (1 - p) * chi p S (Function.update x j false) =
      if j ∈ S then 0 else chi p S x := by
  by_cases hj : j ∈ S
  · rw [if_pos hj, chi_update_mem p S j hj, chi_update_mem p S j hj]
    linear_combination (∏ i ∈ S.erase j, r p (x i)) * r_mean p hp hp1
  · rw [if_neg hj]
    have e : ∀ b, chi p S (Function.update x j b) = chi p S x := by
      intro b
      unfold chi
      refine Finset.prod_congr rfl (fun i hi => ?_)
      have : i ≠ j := fun h => hj (h ▸ hi)
      rw [Function.update_of_ne this]
    rw [e, e]; ring

lemma Tj_Top (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j : Fin n) (ρ : Fin n → ℝ) (φ : Cube n → ℝ)
    (x : Cube n) :
    Tj p j (ρ j) (Top p (Function.update ρ j 1) φ) x = Top p ρ φ x := by
  classical
  have hm : p * Top p (Function.update ρ j 1) φ (Function.update x j true) +
      (1 - p) * Top p (Function.update ρ j 1) φ (Function.update x j false) =
      ∑ S : Finset (Fin n), (∏ i ∈ S, Function.update ρ j 1 i) * coef p φ S *
        (if j ∈ S then 0 else chi p S x) := by
    simp only [Top, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [← chi_avg p hp hp1 S j x]
    ring
  unfold Tj
  rw [hm]
  unfold Top
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  by_cases hj : j ∈ S
  · rw [if_pos hj, ← Finset.mul_prod_erase S _ hj, ← Finset.mul_prod_erase S ρ hj,
      Function.update_self]
    have : ∏ i ∈ S.erase j, Function.update ρ j 1 i = ∏ i ∈ S.erase j, ρ i :=
      Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    rw [this]; ring
  · rw [if_neg hj]
    have : ∏ i ∈ S, Function.update ρ j 1 i = ∏ i ∈ S, ρ i :=
      Finset.prod_congr rfl (fun i hi => by
        rw [Function.update_of_ne (by rintro rfl; exact hj hi)])
    rw [this]; ring

lemma poly_fact (t : ℝ) (ht : t = 2 / 5 ∨ t = -(2 / 5)) (m y : ℝ) :
    (m + t * (y - m)) ^ 4 + 4 * m ^ 3 * (1 - t) * (y - m) ≤ y ^ 4 := by
  have key : y ^ 4 - ((m + t * (y - m)) ^ 4 + 4 * m ^ 3 * (1 - t) * (y - m)) =
      (y - m) ^ 2 * (6 * (1 - t ^ 2) * m ^ 2 + 4 * (1 - t ^ 3) * m * (y - m) +
        (1 - t ^ 4) * (y - m) ^ 2) := by ring
  have hQ : 0 ≤ 6 * (1 - t ^ 2) * m ^ 2 + 4 * (1 - t ^ 3) * m * (y - m) +
      (1 - t ^ 4) * (y - m) ^ 2 := by
    rcases ht with rfl | rfl
    · nlinarith [sq_nonneg (m + 13 / 35 * (y - m)), sq_nonneg (y - m)]
    · nlinarith [sq_nonneg (m + 19 / 45 * (y - m)), sq_nonneg (y - m)]
  nlinarith [mul_nonneg (sq_nonneg (y - m)) hQ]

lemma pair_ineq (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (t : ℝ) (ht : t = 2 / 5 ∨ t = -(2 / 5))
    (u v : ℝ) :
    p * ((p * u + (1 - p) * v) + t * (u - (p * u + (1 - p) * v))) ^ 4 +
      (1 - p) * ((p * u + (1 - p) * v) + t * (v - (p * u + (1 - p) * v))) ^ 4 ≤
      p * u ^ 4 + (1 - p) * v ^ 4 := by
  set m := p * u + (1 - p) * v with hm
  have hu := mul_le_mul_of_nonneg_left (poly_fact t ht m u) hp.le
  have hv := mul_le_mul_of_nonneg_left (poly_fact t ht m v) (show (0 : ℝ) ≤ 1 - p by linarith)
  have e : p * (4 * m ^ 3 * (1 - t) * (u - m)) + (1 - p) * (4 * m ^ 3 * (1 - t) * (v - m)) = 0 := by
    rw [hm]; ring
  nlinarith

lemma wr_nonneg (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j : Fin n) (x : Cube n) : 0 ≤ wr p j x :=
  Finset.prod_nonneg (fun i _ => (bern_pos p hp hp1 (x i)).le)

lemma Tj_update (p : ℝ) (j : Fin n) (t : ℝ) (φ : Cube n → ℝ) (x : Cube n) (b : Bool) :
    Tj p j t φ (Function.update x j b) =
      (p * φ (Function.update x j true) + (1 - p) * φ (Function.update x j false)) +
        t * (φ (Function.update x j b) -
          (p * φ (Function.update x j true) + (1 - p) * φ (Function.update x j false))) := by
  simp only [Tj, Function.update_idem]

lemma Tj_contract (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (j : Fin n) (t : ℝ)
    (ht : t = 2 / 5 ∨ t = -(2 / 5)) (φ : Cube n → ℝ) :
    expect p (fun x => Tj p j t φ x ^ 4) ≤ expect p (fun x => φ x ^ 4) := by
  have h1 := expect_pair p j (fun x => Tj p j t φ x ^ 4)
  have h2 := expect_pair p j (fun x => φ x ^ 4)
  simp only [Tj_update] at h1
  have h3 : ∑ x : Cube n, wr p j x *
      (p * ((p * φ (Function.update x j true) + (1 - p) * φ (Function.update x j false)) +
        t * (φ (Function.update x j true) -
          (p * φ (Function.update x j true) + (1 - p) * φ (Function.update x j false)))) ^ 4 +
       (1 - p) * ((p * φ (Function.update x j true) + (1 - p) * φ (Function.update x j false)) +
        t * (φ (Function.update x j false) -
          (p * φ (Function.update x j true) + (1 - p) * φ (Function.update x j false)))) ^ 4) ≤
      ∑ x : Cube n, wr p j x * (p * φ (Function.update x j true) ^ 4 +
        (1 - p) * φ (Function.update x j false) ^ 4) :=
    Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
      (pair_ineq p hp hp1 t ht _ _) (wr_nonneg p hp hp1 j x))
  linarith

lemma top_four_aux (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (φ : Cube n → ℝ) (A : Finset (Fin n)) :
    ∀ ρ : Fin n → ℝ, (∀ j ∈ A, ρ j = 2 / 5 ∨ ρ j = -(2 / 5)) → (∀ j, j ∉ A → ρ j = 1) →
      expect p (fun x => Top p ρ φ x ^ 4) ≤ expect p (fun x => φ x ^ 4) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    intro ρ _ h1
    have : ρ = fun _ => 1 := funext fun j => h1 j (by simp)
    subst this
    exact le_of_eq (expect_congr _ _ _ (fun x => by rw [Top_one p hp hp1]))
  | insert j A hj ih =>
    intro ρ hA hout
    have h' := ih (Function.update ρ j 1)
      (fun i hi => by
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        rw [Function.update_of_ne hij]
        exact hA i (Finset.mem_insert_of_mem hi))
      (fun i hi => by
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij]
          exact hout i (by simp [hij, hi]))
    calc expect p (fun x => Top p ρ φ x ^ 4)
        = expect p (fun x => Tj p j (ρ j) (Top p (Function.update ρ j 1) φ) x ^ 4) :=
          expect_congr _ _ _ (fun x => by rw [Tj_Top p hp hp1])
      _ ≤ expect p (fun x => Top p (Function.update ρ j 1) φ x ^ 4) :=
          Tj_contract p hp hp1 j (ρ j) (hA j (Finset.mem_insert_self j A)) _
      _ ≤ _ := h'

theorem expect_Top_pow_four_le (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (σ : Cube n)
    (φ : Cube n → ℝ) :
    expect p (fun x => Top p (rhoOf (2 / 5) σ) φ x ^ 4) ≤ expect p (fun x => φ x ^ 4) := by
  refine top_four_aux p hp hp1 φ Finset.univ _ (fun j _ => ?_) (fun j hj => absurd (Finset.mem_univ j) hj)
  unfold rhoOf
  split_ifs
  · left; rfl
  · right; rfl

end NarrowDNF.Dev.Bg.PartO
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
alias expect_Top_pow_four_le := NarrowDNF.Dev.Bg.PartO.expect_Top_pow_four_le

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartU
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
lemma r_half_sq (b : Bool) : r (1 / 2) b ^ 2 = 1 := by
  cases b <;> simp [r] <;> norm_num

lemma chi_update_not_mem (p : ℝ) (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S) (x : Cube n)
    (b : Bool) : chi p S (Function.update x j b) = chi p S x := by
  unfold chi
  refine Finset.prod_congr rfl (fun i hi => ?_)
  rw [Function.update_of_ne (show i ≠ j from fun h => hj (h ▸ hi))]

lemma expect_const (p : ℝ) (c : ℝ) : expect p (fun _ : Cube n => c) = c := by
  rw [expect_def, ← Finset.sum_mul, sum_w, one_mul]

lemma cs_expect (A B : Cube n → ℝ) :
    expect (1 / 2) (fun x => A x ^ 2 * B x ^ 2) ^ 2 ≤
      expect (1 / 2) (fun x => A x ^ 4) * expect (1 / 2) (fun x => B x ^ 4) := by
  simp only [expect_def]
  have hw : ∀ x : Cube n, 0 ≤ w (1 / 2) x := fun x => w_nonneg _ (by norm_num) (by norm_num) x
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun x _ => mul_nonneg (hw x) (by positivity))
    (fun x _ => mul_nonneg (hw x) (by positivity)) (fun x _ => le_of_eq (by ring))

lemma bonami_U (U : Finset (Fin n)) : ∀ (K : ℕ) (a : Finset (Fin n) → ℝ),
    (∀ S, K < S.card → a S = 0) →
    expect (1 / 2) (fun σ => (∑ S ∈ U.powerset, a S * chi (1 / 2) S σ) ^ 4) ≤
      9 ^ K * (∑ S ∈ U.powerset, a S ^ 2) ^ 2 := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    intro K a _
    simp only [Finset.powerset_empty, Finset.sum_singleton]
    have hc : ∀ σ : Cube n, chi (1 / 2) ∅ σ = 1 := fun σ => by simp [chi]
    simp only [hc, mul_one]
    rw [expect_const]
    have h9 : (1 : ℝ) ≤ 9 ^ K := one_le_pow₀ (by norm_num)
    nlinarith [sq_nonneg (a ∅ ^ 2)]
  | insert j U hj ih =>
    intro K a ha
    set b : Finset (Fin n) → ℝ := fun S => if j ∈ S then 0 else a (insert j S) with hbdef
    have hb : ∀ S, K - 1 < S.card → b S = 0 := by
      intro S hS
      simp only [hbdef]
      split_ifs with hjS
      · rfl
      · apply ha
        rw [Finset.card_insert_of_notMem hjS]
        omega
    have hU : ∀ S ∈ U.powerset, j ∉ S := fun S hS h => hj (Finset.mem_powerset.mp hS h)
    set A : Cube n → ℝ := fun σ => ∑ S ∈ U.powerset, a S * chi (1 / 2) S σ with hA
    set B : Cube n → ℝ := fun σ => ∑ S ∈ U.powerset, b S * chi (1 / 2) S σ with hB
    have hH : ∀ σ : Cube n, ∑ S ∈ (insert j U).powerset, a S * chi (1 / 2) S σ =
        A σ + r (1 / 2) (σ j) * B σ := by
      intro σ
      rw [Finset.sum_powerset_insert hj]
      congr 1
      simp only [hB, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      have := hU S hS
      simp only [hbdef, this, if_false, chi, Finset.prod_insert this]
      ring
    have hsq : ∑ S ∈ (insert j U).powerset, a S ^ 2 =
        ∑ S ∈ U.powerset, a S ^ 2 + ∑ S ∈ U.powerset, b S ^ 2 := by
      rw [Finset.sum_powerset_insert hj]
      congr 1
      refine Finset.sum_congr rfl (fun S hS => ?_)
      simp only [hbdef, hU S hS, if_false]
    simp only [hH, hsq]
    have hpt : ∀ σ : Cube n, (A σ + r (1 / 2) (σ j) * B σ) ^ 4 =
        (A σ ^ 4 + 6 * (A σ ^ 2 * B σ ^ 2) + B σ ^ 4) +
          r (1 / 2) (σ j) * (4 * A σ ^ 3 * B σ + 4 * A σ * B σ ^ 3) := by
      intro σ
      have h := r_half_sq (σ j)
      set ρ := r (1 / 2) (σ j)
      linear_combination (6 * A σ ^ 2 * B σ ^ 2 + 4 * A σ * ρ * B σ ^ 3 + (ρ ^ 2 + 1) * B σ ^ 4) * h
    rw [expect_congr _ _ _ hpt, expect_add]
    have hAinv : ∀ σ b', A (Function.update σ j b') = A σ := by
      intro σ b'
      simp only [hA]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      rw [chi_update_not_mem _ S j (hU S hS)]
    have hBinv : ∀ σ b', B (Function.update σ j b') = B σ := by
      intro σ b'
      simp only [hB]
      refine Finset.sum_congr rfl (fun S hS => ?_)
      rw [chi_update_not_mem _ S j (hU S hS)]
    have hodd : expect (1 / 2) (fun σ => r (1 / 2) (σ j) *
        (4 * A σ ^ 3 * B σ + 4 * A σ * B σ ^ 3)) = 0 := by
      refine expect_mul_eq_zero_of_mean_zero (1 / 2) j (fun σ => r (1 / 2) (σ j))
        (fun σ => 4 * A σ ^ 3 * B σ + 4 * A σ * B σ ^ 3) ?_ ?_
      · intro x
        simp only [Function.update_self]
        exact r_mean (1 / 2) (by norm_num) (by norm_num)
      · intro x b'
        simp only [hAinv, hBinv]
    rw [hodd, add_zero, expect_add, expect_add, expect_smul]
    have hα := ih K a ha
    have hβ := ih (K - 1) b hb
    have hγ := cs_expect A B
    have hγ0 : 0 ≤ expect (1 / 2) (fun σ => A σ ^ 2 * B σ ^ 2) :=
      expect_nonneg _ (by norm_num) (by norm_num) _ (fun σ => by positivity)
    have hα0 : 0 ≤ expect (1 / 2) (fun σ => A σ ^ 4) :=
      expect_nonneg _ (by norm_num) (by norm_num) _ (fun σ => by positivity)
    have hβ0 : 0 ≤ expect (1 / 2) (fun σ => B σ ^ 4) :=
      expect_nonneg _ (by norm_num) (by norm_num) _ (fun σ => by positivity)
    set α := expect (1 / 2) (fun σ => A σ ^ 4)
    set β := expect (1 / 2) (fun σ => B σ ^ 4)
    set γ := expect (1 / 2) (fun σ => A σ ^ 2 * B σ ^ 2)
    have ha0 : 0 ≤ ∑ S ∈ U.powerset, a S ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    have hb0 : 0 ≤ ∑ S ∈ U.powerset, b S ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    set sa := ∑ S ∈ U.powerset, a S ^ 2
    set sb := ∑ S ∈ U.powerset, b S ^ 2
    rcases K with _ | K'
    · have hbz : ∀ S, b S = 0 := by
        intro S
        simp only [hbdef]
        split_ifs with hjS
        · rfl
        · apply ha
          rw [Finset.card_insert_of_notMem hjS]
          omega
      have hsb : sb = 0 := by simp [sb, hbz]
      simp only [hsb, pow_zero, Nat.zero_sub, one_mul] at hα hβ ⊢
      have hβz : β = 0 := by nlinarith
      have hγz : γ = 0 := by
        rw [hβz, mul_zero] at hγ
        nlinarith
      rw [hβz, hγz]
      nlinarith
    · simp only [Nat.add_sub_cancel] at hβ
      have hM : (0 : ℝ) < 9 ^ K' := by positivity
      set M : ℝ := 9 ^ K'
      have h9 : (9 : ℝ) ^ (K' + 1) = 9 * M := by rw [pow_succ]; ring
      rw [h9] at hα ⊢
      have hγ' : γ ^ 2 ≤ (3 * M * sa * sb) ^ 2 := by
        calc γ ^ 2 ≤ α * β := hγ
          _ ≤ (9 * M * sa ^ 2) * (M * sb ^ 2) :=
            mul_le_mul hα hβ hβ0 (by positivity)
          _ = (3 * M * sa * sb) ^ 2 := by ring
      have hγle : γ ≤ 3 * M * sa * sb := by
        have h0 : 0 ≤ 3 * M * sa * sb := by positivity
        nlinarith
      nlinarith [mul_nonneg hM.le hb0, mul_nonneg (mul_nonneg hM.le hb0) hb0]

theorem bonami (K : ℕ) (a : Finset (Fin n) → ℝ) (ha : ∀ S, K < S.card → a S = 0) :
    expect (1 / 2) (fun σ => (∑ S : Finset (Fin n), a S * chi (1 / 2) S σ) ^ 4) ≤
      9 ^ K * (∑ S : Finset (Fin n), a S ^ 2) ^ 2 := by
  have := bonami_U (Finset.univ : Finset (Fin n)) K a ha
  simpa only [Finset.powerset_univ] using this

end NarrowDNF.Dev.Bg.PartU
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
/-! ## Part U: Bonami's lemma on the uniform cube -/
alias bonami := NarrowDNF.Dev.Bg.PartU.bonami

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartD
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
lemma rhoOf_eq (c : ℝ) (σ : Cube n) (j : Fin n) :
    rhoOf c σ j = c * r (1 / 2) (σ j) := by
  unfold rhoOf r
  cases σ j <;> norm_num

theorem prod_rhoOf (c : ℝ) (σ : Cube n) (S : Finset (Fin n)) :
    ∏ j ∈ S, rhoOf c σ j = c ^ S.card * chi (1 / 2) S σ := by
  simp only [rhoOf_eq, Finset.prod_mul_distrib, Finset.prod_const, chi]

end NarrowDNF.Dev.Bg.PartD
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
/-! ## Part D: derivatives and signs -/
alias prod_rhoOf := NarrowDNF.Dev.Bg.PartD.prod_rhoOf

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartD
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
theorem coef_gder (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (i : Fin n)
    (S : Finset (Fin n)) :
    coef p (gder p f i) S = if i ∈ S then fhat p f S else 0 := by
  classical
  unfold coef
  have h1 : ∀ y : Cube n, gder p f i y * chi p S y =
      ∑ T ∈ Finset.univ.filter (fun T => i ∈ T), fhat p f T * (chi p T y * chi p S y) := by
    intro y
    rw [gder, ind_sub_avg p hp hp1 f i y, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    simp only [FS]; ring
  rw [expect_congr p _ _ h1, expect_sum]
  simp only [expect_smul, expect_chi_mul p hp hp1, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

end NarrowDNF.Dev.Bg.PartD
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
alias coef_gder := NarrowDNF.Dev.Bg.PartD.coef_gder

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartD
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
theorem abs_gder_le_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : Cube n → Bool) (i : Fin n)
    (x : Cube n) : |gder p f i x| ≤ 1 := by
  unfold gder ind
  rw [abs_le]
  split_ifs <;> constructor <;> nlinarith

end NarrowDNF.Dev.Bg.PartD
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
alias abs_gder_le_one := NarrowDNF.Dev.Bg.PartD.abs_gder_le_one

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartD
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
lemma expect_abs_gder (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (i : Fin n) :
    expect p (fun x => |gder p f i x|) = FriedgutCoalition.pInfl p f i := by
  have h2 := expect_pair p i (fun x => |gder p f i x|)
  have h3 := pInfl_two p f i
  have key : ∀ x : Cube n,
      p * |gder p f i (Function.update x i true)| +
        (1 - p) * |gder p f i (Function.update x i false)| =
      2 * p * (1 - p) * (ind f (Function.update x i true) - ind f (Function.update x i false)) ^ 2 := by
    intro x
    simp only [gder, Function.update_idem]
    have hq : 0 < 1 - p := by linarith
    unfold ind
    split_ifs
    · simp
    · rw [abs_of_nonneg (by nlinarith), abs_of_nonpos (by nlinarith)]; ring
    · rw [abs_of_nonpos (by nlinarith), abs_of_nonneg (by nlinarith)]; ring
    · simp
  simp only [key] at h2
  linarith

theorem sum_expect_abs_gder (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) :
    ∑ i : Fin n, expect p (fun x => |gder p f i x|) = FriedgutCoalition.totalPInfl p f := by
  unfold FriedgutCoalition.totalPInfl
  exact Finset.sum_congr rfl (fun i _ => expect_abs_gder p hp hp1 f i)

end NarrowDNF.Dev.Bg.PartD
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
alias sum_expect_abs_gder := NarrowDNF.Dev.Bg.PartD.sum_expect_abs_gder

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartM1
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
/-- `b_S(x) = c^{|S|} [i ∈ S] F_S(x)` -/
noncomputable def bS (p : ℝ) (f : Cube n → Bool) (i : Fin n) (S : Finset (Fin n)) (x : Cube n) : ℝ :=
  (2 / 5 : ℝ) ^ S.card * (if i ∈ S then FS p f S x else 0)

/-- `H(x,σ) = Σ_{S ∈ low} b_S(x) χ_S(σ)` -/
noncomputable def Hf (p : ℝ) (f : Cube n → Bool) (K : ℕ) (i : Fin n) (x σ : Cube n) : ℝ :=
  ∑ S : Finset (Fin n), (if S ∈ low n K then bS p f i S x else 0) * chi (1 / 2) S σ

lemma expect_comm (p q : ℝ) (F : Cube n → Cube n → ℝ) :
    expect p (fun x => expect q (fun σ => F x σ)) =
      expect q (fun σ => expect p (fun x => F x σ)) := by
  simp only [expect_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

lemma expect_const (p : ℝ) (c : ℝ) : expect p (fun _ : Cube n => c) = c := by
  rw [expect_def, ← Finset.sum_mul, sum_w, one_mul]

lemma G_eq (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (i : Fin n) (x σ : Cube n) :
    Top p (rhoOf (2 / 5) σ) (gder p f i) x = ∑ S : Finset (Fin n), bS p f i S x * chi (1 / 2) S σ := by
  unfold Top
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [prod_rhoOf, coef_gder p hp hp1]
  unfold bS FS
  split_ifs <;> ring

lemma Q_eq (p : ℝ) (f : Cube n → Bool) (K : ℕ) (i : Fin n) (x : Cube n) :
    Qc p f K i x = ∑ S : Finset (Fin n), (if S ∈ low n K then bS p f i S x else 0) ^ 2 := by
  classical
  have : ∀ S : Finset (Fin n), (if S ∈ low n K then bS p f i S x else 0) ^ 2 =
      if S ∈ low n K then bS p f i S x ^ 2 else 0 := fun S => by split_ifs <;> simp
  simp only [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  rfl

lemma Q_nonneg (p : ℝ) (f : Cube n → Bool) (K : ℕ) (i : Fin n) (x : Cube n) :
    0 ≤ Qc p f K i x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma expect_GH (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (K : ℕ) (i : Fin n)
    (x : Cube n) :
    expect (1 / 2) (fun σ => Top p (rhoOf (2 / 5) σ) (gder p f i) x * Hf p f K i x σ) =
      Qc p f K i x := by
  classical
  have h1 : ∀ σ : Cube n, Top p (rhoOf (2 / 5) σ) (gder p f i) x * Hf p f K i x σ =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        (bS p f i S x * (if T ∈ low n K then bS p f i T x else 0)) *
          (chi (1 / 2) S σ * chi (1 / 2) T σ) := by
    intro σ
    rw [G_eq p hp hp1, Hf, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => by ring))
  rw [expect_congr _ _ _ h1, expect_sum]
  simp only [expect_sum, expect_smul, expect_chi_mul (1 / 2 : ℝ) (by norm_num) (by norm_num)]
  rw [Q_eq]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  split_ifs <;> ring

lemma expect_H4 (p : ℝ) (f : Cube n → Bool) (K : ℕ) (i : Fin n) (x : Cube n) :
    expect (1 / 2) (fun σ => Hf p f K i x σ ^ 4) ≤ 9 ^ K * Qc p f K i x ^ 2 := by
  rw [Q_eq]
  refine bonami K (fun S => if S ∈ low n K then bS p f i S x else 0) (fun S hS => ?_)
  have : S ∉ low n K := by simp [low]; omega
  simp [this]

lemma young (θ g z : ℝ) (hθ : 0 < θ) (hg : |g| ≤ 1) :
    g * z ≤ 3 * θ / 4 * |g| + z ^ 4 / (4 * θ ^ 3) := by
  have ht : 4 * θ ^ 3 * |z| ≤ 3 * θ ^ 4 + z ^ 4 := by
    have hz : z ^ 4 = |z| ^ 4 := by rw [pow_abs]; exact (abs_of_nonneg (by positivity)).symm
    rw [hz]
    have ha := abs_nonneg z
    nlinarith [mul_nonneg (sq_nonneg (|z| - θ))
      (by positivity : (0 : ℝ) ≤ |z| ^ 2 + 2 * θ * |z| + 3 * θ ^ 2)]
  have hgz : g * z ≤ |g| * |z| := by rw [← abs_mul]; exact le_abs_self _
  have key : 4 * θ ^ 3 * (g * z) ≤ 3 * θ ^ 4 * |g| + z ^ 4 := by
    have h0 := abs_nonneg g
    have hθ3 : 0 < θ ^ 3 := by positivity
    have h4 : 0 ≤ z ^ 4 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left ht h0, mul_le_mul_of_nonneg_left hgz hθ3.le,
      mul_le_mul_of_nonneg_right hg h4]
  have heq : 3 * θ / 4 * |g| + z ^ 4 / (4 * θ ^ 3) = (3 * θ ^ 4 * |g| + z ^ 4) / (4 * θ ^ 3) := by
    field_simp
  rw [heq, le_div_iff₀ (by positivity)]
  linarith

theorem key_coord (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (K : ℕ) (i : Fin n)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    expect p (fun x => if Qc p f K i x < θ ^ 4 / 9 ^ K then Qc p f K i x else 0) ≤
      θ * expect p (fun x => |gder p f i x|) := by
  set τ : ℝ := θ ^ 4 / 9 ^ K with hτ
  set Q : Cube n → ℝ := fun x => Qc p f K i x with hQ
  set e : Cube n → ℝ := fun x => if Q x < τ then 1 else 0 with he
  set g : Cube n → ℝ := gder p f i with hg
  set Ψ : Cube n → Cube n → ℝ := fun σ x => e x * Hf p f K i x σ with hΨ
  set a : ℝ := expect p (fun x => if Q x < τ then Q x else 0) with ha
  set Eg : ℝ := expect p (fun x => |g x|) with hEg
  have hph : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hph1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hp0 := hp.le
  have hp10 := hp1.le
  -- a as a double expectation
  have hA : a = expect (1 / 2) (fun σ => expect p (fun x => g x * Top p (rhoOf (2 / 5) σ) (Ψ σ) x)) := by
    have h1 : a = expect p (fun x => expect (1 / 2)
        (fun σ => Top p (rhoOf (2 / 5) σ) g x * Ψ σ x)) := by
      rw [ha]
      refine expect_congr _ _ _ (fun x => ?_)
      have : (fun σ => Top p (rhoOf (2 / 5) σ) g x * Ψ σ x) =
          (fun σ => e x * (Top p (rhoOf (2 / 5) σ) (gder p f i) x * Hf p f K i x σ)) := by
        funext σ; simp only [hΨ, hg]; ring
      rw [this, expect_smul, expect_GH p hp hp1]
      simp only [he, hQ]
      split_ifs <;> simp
    rw [h1, expect_comm]
    refine expect_congr _ _ _ (fun σ => ?_)
    exact expect_Top_mul p hp hp1 _ g (Ψ σ)
  -- the fourth-moment bound
  have hB : expect (1 / 2) (fun σ => expect p (fun x => Ψ σ x ^ 4)) ≤ θ ^ 4 * a := by
    rw [← expect_comm]
    rw [ha, ← expect_smul]
    refine expect_mono p hp0 hp10 _ _ (fun x => ?_)
    have hΨ4 : (fun σ => Ψ σ x ^ 4) = (fun σ => e x * Hf p f K i x σ ^ 4) := by
      funext σ; simp only [hΨ, he]; split_ifs <;> simp
    rw [hΨ4, expect_smul]
    have hH := expect_H4 p f K i x
    have hQ0 : 0 ≤ Q x := Q_nonneg p f K i x
    simp only [he]
    split_ifs with hlt
    · rw [one_mul]
      refine le_trans hH ?_
      have h9 : (0 : ℝ) < 9 ^ K := by positivity
      have : 9 ^ K * Q x < θ ^ 4 := by
        have := hlt; rw [hτ, lt_div_iff₀ h9] at this; linarith
      show 9 ^ K * Q x ^ 2 ≤ θ ^ 4 * Q x
      nlinarith
    · simp
  -- the Young step
  have hC : ∀ σ : Cube n, expect p (fun x => g x * Top p (rhoOf (2 / 5) σ) (Ψ σ) x) ≤
      3 * θ / 4 * Eg + 1 / (4 * θ ^ 3) * expect p (fun x => Ψ σ x ^ 4) := by
    intro σ
    have h1 : expect p (fun x => g x * Top p (rhoOf (2 / 5) σ) (Ψ σ) x) ≤
        expect p (fun x => 3 * θ / 4 * |g x| +
          1 / (4 * θ ^ 3) * Top p (rhoOf (2 / 5) σ) (Ψ σ) x ^ 4) := by
      refine expect_mono p hp0 hp10 _ _ (fun x => ?_)
      have := young θ (g x) (Top p (rhoOf (2 / 5) σ) (Ψ σ) x) hθ
        (abs_gder_le_one p hp0 hp10 f i x)
      rw [one_div_mul_eq_div]; exact this
    rw [expect_add, expect_smul, expect_smul] at h1
    have h2 := expect_Top_pow_four_le p hp hp1 σ (Ψ σ)
    have hk : (0 : ℝ) ≤ 1 / (4 * θ ^ 3) := by positivity
    rw [hEg]
    nlinarith [mul_le_mul_of_nonneg_left h2 hk]
  have hD : a ≤ 3 * θ / 4 * Eg + 1 / (4 * θ ^ 3) * (θ ^ 4 * a) := by
    rw [hA] at hB ⊢
    refine le_trans (expect_mono (1 / 2) hph hph1 _ _ hC) ?_
    rw [expect_add, expect_const, expect_smul]
    have hk : (0 : ℝ) ≤ 1 / (4 * θ ^ 3) := by positivity
    have := mul_le_mul_of_nonneg_left hB hk
    linarith
  have hsimp : 1 / (4 * θ ^ 3) * (θ ^ 4 * a) = θ / 4 * a := by
    field_simp
  rw [hsimp] at hD
  have hEg0 : 0 ≤ Eg := expect_nonneg p hp0 hp10 _ (fun x => abs_nonneg _)
  show a ≤ θ * Eg
  nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (mul_nonneg hθ.le hEg0)]

end NarrowDNF.Dev.Bg.PartM1
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
/-! ## Part M: the three estimates -/
alias key_coord := NarrowDNF.Dev.Bg.PartM1.key_coord

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartM2
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
lemma card_low_subset_le (J : Finset (Fin n)) (K : ℕ) :
    ((low n K).filter (fun S => S ⊆ J)).card ≤ (J.card + 1) ^ K := by
  classical
  have h1 : (low n K).filter (fun S => S ⊆ J) ⊆
      (Finset.range (K + 1)).biUnion (fun j => J.powersetCard j) := by
    intro S hS
    simp only [low, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨S.card, by omega, hS.2, rfl⟩
  refine (Finset.card_le_card h1).trans (Finset.card_biUnion_le.trans ?_)
  simp only [Finset.card_powersetCard]
  rw [add_pow]
  refine Finset.sum_le_sum (fun j hj => ?_)
  simp only [one_pow, mul_one]
  have hjK : j ≤ K := by simpa [Nat.lt_succ_iff] using hj
  calc J.card.choose j ≤ J.card ^ j := Nat.choose_le_pow J.card j
    _ ≤ J.card ^ j * K.choose j := Nat.le_mul_of_pos_right _ (Nat.choose_pos hjK)

lemma sq_le_scaled (K : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ K) (y : ℝ) :
    y ^ 2 ≤ (25 / 4 : ℝ) ^ K * ((2 / 5 : ℝ) ^ S.card * y) ^ 2 := by
  have h1 : (25 / 4 : ℝ) ^ K * ((2 / 5 : ℝ) ^ S.card) ^ 2 = (25 / 4 : ℝ) ^ (K - S.card) := by
    rw [show (25 / 4 : ℝ) ^ K = (25 / 4 : ℝ) ^ (K - S.card) * (25 / 4) ^ S.card by
      rw [← pow_add, Nat.sub_add_cancel hS]]
    rw [mul_assoc, ← pow_mul, mul_comm S.card 2, pow_mul, ← mul_pow]
    rw [show ((25 / 4 : ℝ) * ((2 / 5) ^ 2)) = 1 by norm_num, one_pow, mul_one]
  have h2 : (1 : ℝ) ≤ (25 / 4 : ℝ) ^ (K - S.card) := one_le_pow₀ (by norm_num)
  calc y ^ 2 = 1 * y ^ 2 := by ring
    _ ≤ (25 / 4 : ℝ) ^ (K - S.card) * y ^ 2 := by gcongr
    _ = (25 / 4 : ℝ) ^ K * ((2 / 5 : ℝ) ^ S.card * y) ^ 2 := by rw [← h1]; ring

theorem pointwise_split (p : ℝ) (f : Cube n → Bool) (K : ℕ) (τ N ε₁ : ℝ) (hN : 0 ≤ N)
    (x : Cube n) :
    ∑ S ∈ low n K, (if |FS p f S x| ≤ ε₁ then FS p f S x ^ 2 else 0) ≤
      (25 / 4 : ℝ) ^ K * ∑ i : Fin n, (if Qc p f K i x < τ then Qc p f K i x else 0) +
      (if N ≤ ((Jx p f K τ x).card : ℝ) then Vx p f K x else 0) + (N + 1) ^ K * ε₁ ^ 2 := by
  classical
  set J := Jx p f K τ x with hJ
  set t : Finset (Fin n) → ℝ := fun S => if |FS p f S x| ≤ ε₁ then FS p f S x ^ 2 else 0 with ht
  have ht_le : ∀ S, t S ≤ FS p f S x ^ 2 := by
    intro S; simp only [ht]; split_ifs <;> [exact le_rfl; positivity]
  have ht_nn : ∀ S, 0 ≤ t S := by
    intro S; simp only [ht]; split_ifs <;> positivity
  have ht_eps : ∀ S, t S ≤ ε₁ ^ 2 := by
    intro S; simp only [ht]; split_ifs with h
    · rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    · positivity
  let g : Fin n → Finset (Fin n) → ℝ := fun i S =>
    ((2 / 5 : ℝ) ^ S.card * (if i ∈ S then FS p f S x else 0)) ^ 2
  have hper : ∀ S ∈ low n K, t S ≤ (25 / 4 : ℝ) ^ K *
      ∑ i : Fin n, (if Qc p f K i x < τ then g i S else 0) + (if S ⊆ J then t S else 0) := by
    intro S hS
    have hSK : S.card ≤ K := by simpa [low] using hS
    have hnn : 0 ≤ ∑ i : Fin n, (if Qc p f K i x < τ then g i S else 0) :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> positivity)
    by_cases hSJ : S ⊆ J
    · rw [if_pos hSJ]; nlinarith [pow_pos (show (0:ℝ) < 25/4 by norm_num) K]
    · rw [if_neg hSJ, add_zero]
      obtain ⟨i, hiS, hiJ⟩ := Finset.not_subset.mp hSJ
      have hQ : Qc p f K i x < τ := by
        simpa [hJ, Jx] using hiJ
      have h1 : g i S ≤ ∑ i : Fin n, (if Qc p f K i x < τ then g i S else 0) := by
        have := Finset.single_le_sum (f := fun i => if Qc p f K i x < τ then g i S else 0)
          (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ i)
        simpa [hQ] using this
      have h2 : FS p f S x ^ 2 ≤ (25 / 4 : ℝ) ^ K * g i S := by
        have := sq_le_scaled K S hSK (FS p f S x)
        simpa [g, hiS] using this
      calc t S ≤ FS p f S x ^ 2 := ht_le S
        _ ≤ _ := h2
        _ ≤ _ := by gcongr
  have hsum1 : ∑ S ∈ low n K, ∑ i : Fin n, (if Qc p f K i x < τ then g i S else 0) =
      ∑ i : Fin n, (if Qc p f K i x < τ then Qc p f K i x else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : Qc p f K i x < τ
    · simp only [h, if_true]; rfl
    · simp only [h, if_false, Finset.sum_const_zero]
  have hsum2 : ∑ S ∈ low n K, (if S ⊆ J then t S else 0) ≤
      (if N ≤ (J.card : ℝ) then Vx p f K x else 0) + (N + 1) ^ K * ε₁ ^ 2 := by
    rw [← Finset.sum_filter]
    by_cases hNJ : N ≤ (J.card : ℝ)
    · rw [if_pos hNJ]
      have h1 : ∑ S ∈ (low n K).filter (fun S => S ⊆ J), t S ≤ ∑ S ∈ low n K, t S :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun S _ _ => ht_nn S)
      have h2 : ∑ S ∈ low n K, t S ≤ Vx p f K x := Finset.sum_le_sum (fun S _ => ht_le S)
      have h3 : 0 ≤ (N + 1) ^ K * ε₁ ^ 2 := by positivity
      linarith
    · rw [if_neg hNJ, zero_add]
      have h1 : ∑ S ∈ (low n K).filter (fun S => S ⊆ J), t S ≤
          ((low n K).filter (fun S => S ⊆ J)).card * ε₁ ^ 2 := by
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum (fun S _ => ht_eps S)
      have h2 : (((low n K).filter (fun S => S ⊆ J)).card : ℝ) ≤ ((J.card : ℝ) + 1) ^ K := by
        exact_mod_cast card_low_subset_le J K
      have h3 : ((J.card : ℝ) + 1) ^ K ≤ (N + 1) ^ K :=
        pow_le_pow_left₀ (by positivity) (by linarith) K
      have h4 : (((low n K).filter (fun S => S ⊆ J)).card : ℝ) * ε₁ ^ 2 ≤ (N + 1) ^ K * ε₁ ^ 2 :=
        mul_le_mul_of_nonneg_right (h2.trans h3) (sq_nonneg _)
      linarith
  have htot := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum1] at htot
  linarith

end NarrowDNF.Dev.Bg.PartM2
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
alias pointwise_split := NarrowDNF.Dev.Bg.PartM2.pointwise_split

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartM2
open NarrowDNF.Approx NarrowDNF.Dev.Bg
variable {n : ℕ}
lemma expect_sq_chi (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (a : Finset (Fin n) → ℝ) :
    expect p (fun σ => (∑ S : Finset (Fin n), a S * chi p S σ) ^ 2) =
      ∑ S : Finset (Fin n), a S ^ 2 := by
  classical
  have h1 : ∀ σ : Cube n, (∑ S : Finset (Fin n), a S * chi p S σ) ^ 2 =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n), (a S * a T) * (chi p S σ * chi p T σ) := by
    intro σ
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
    ring
  rw [expect_congr p _ _ h1, expect_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [expect_sum]
  simp only [expect_smul, expect_chi_mul p hp hp1, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), sq]

lemma expect_comm (p q : ℝ) (G : Cube n → Cube n → ℝ) :
    expect p (fun x => expect q (fun σ => G x σ)) =
      expect q (fun σ => expect p (fun x => G x σ)) := by
  simp only [expect_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun x _ => by ring))

lemma sq_expect_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (g : Cube n → ℝ) :
    expect p g ^ 2 ≤ expect p (fun σ => g σ ^ 2) := by
  have h := expect_nonneg p hp hp1 (fun σ => (g σ - expect p g) ^ 2) (fun σ => sq_nonneg _)
  have e : expect p (fun σ => (g σ - expect p g) ^ 2) =
      expect p (fun σ => g σ ^ 2) - 2 * expect p g * expect p g + expect p g ^ 2 := by
    rw [expect_congr p _ (fun σ => (g σ ^ 2 - (2 * expect p g) * g σ) + expect p g ^ 2 * 1)
      (fun σ => by ring)]
    rw [expect_add, expect_sub, expect_smul, expect_smul, expect_one]
    ring
  nlinarith

lemma Top_ind_eq (p : ℝ) (f : Cube n → Bool) (σ x : Cube n) :
    Top p (rhoOf (2 / 5) σ) (ind f) x =
      ∑ S : Finset (Fin n), ((2 / 5 : ℝ) ^ S.card * FS p f S x) * chi (1 / 2) S σ := by
  unfold Top
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [prod_rhoOf]
  have : coef p (ind f) S = fhat p f S := rfl
  rw [this, FS]
  ring

lemma Vx_le (p : ℝ) (f : Cube n → Bool) (K : ℕ) (x : Cube n) :
    Vx p f K x ≤ (25 / 4 : ℝ) ^ K *
      ∑ S : Finset (Fin n), ((2 / 5 : ℝ) ^ S.card * FS p f S x) ^ 2 := by
  unfold Vx
  rw [Finset.mul_sum]
  calc ∑ S ∈ low n K, FS p f S x ^ 2
      ≤ ∑ S ∈ low n K, (25 / 4 : ℝ) ^ K * ((2 / 5 : ℝ) ^ S.card * FS p f S x) ^ 2 :=
        Finset.sum_le_sum (fun S hS => sq_le_scaled K S (by simpa [low] using hS) _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun S _ _ => by positivity)

lemma expect_Vx_sq (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (K : ℕ) :
    expect p (fun x => Vx p f K x ^ 2) ≤ ((25 / 4 : ℝ) ^ K) ^ 2 := by
  have hA : (0 : ℝ) ≤ (25 / 4 : ℝ) ^ K := by positivity
  have hpt : ∀ x, Vx p f K x ^ 2 ≤ ((25 / 4 : ℝ) ^ K) ^ 2 *
      expect (1 / 2) (fun σ => Top p (rhoOf (2 / 5) σ) (ind f) x ^ 4) := by
    intro x
    have hV0 : 0 ≤ Vx p f K x := Finset.sum_nonneg (fun S _ => sq_nonneg _)
    have hE : expect (1 / 2) (fun σ => Top p (rhoOf (2 / 5) σ) (ind f) x ^ 2) =
        ∑ S : Finset (Fin n), ((2 / 5 : ℝ) ^ S.card * FS p f S x) ^ 2 := by
      simp only [Top_ind_eq]
      exact expect_sq_chi (1 / 2) (by norm_num) (by norm_num) _
    have hJ := sq_expect_le (1 / 2) (by norm_num) (by norm_num)
      (fun σ => Top p (rhoOf (2 / 5) σ) (ind f) x ^ 2)
    have h4 : (fun σ => (Top p (rhoOf (2 / 5) σ) (ind f) x ^ 2) ^ 2) =
        (fun σ => Top p (rhoOf (2 / 5) σ) (ind f) x ^ 4) := by
      funext σ; ring
    rw [h4, hE] at hJ
    have hV := Vx_le p f K x
    have hV2 : Vx p f K x ^ 2 ≤ ((25 / 4 : ℝ) ^ K *
        ∑ S : Finset (Fin n), ((2 / 5 : ℝ) ^ S.card * FS p f S x) ^ 2) ^ 2 :=
      pow_le_pow_left₀ hV0 hV 2
    rw [mul_pow] at hV2
    calc Vx p f K x ^ 2 ≤ _ := hV2
      _ ≤ _ := mul_le_mul_of_nonneg_left hJ (by positivity)
  calc expect p (fun x => Vx p f K x ^ 2)
      ≤ expect p (fun x => ((25 / 4 : ℝ) ^ K) ^ 2 *
          expect (1 / 2) (fun σ => Top p (rhoOf (2 / 5) σ) (ind f) x ^ 4)) :=
        expect_mono p hp.le hp1.le _ _ hpt
    _ = ((25 / 4 : ℝ) ^ K) ^ 2 *
          expect (1 / 2) (fun σ => expect p (fun x => Top p (rhoOf (2 / 5) σ) (ind f) x ^ 4)) := by
        rw [expect_smul, expect_comm]
    _ ≤ ((25 / 4 : ℝ) ^ K) ^ 2 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hind : expect p (fun x => ind f x ^ 4) ≤ 1 := by
          have := expect_mono p hp.le hp1.le (fun x => ind f x ^ 4) (fun _ => (1 : ℝ))
            (fun x => pow_le_one₀ (ind_nonneg f x) (ind_le_one f x))
          rwa [expect_one] at this
        have := expect_mono (1 / 2) (by norm_num) (by norm_num)
          (fun σ => expect p (fun x => Top p (rhoOf (2 / 5) σ) (ind f) x ^ 4)) (fun _ => (1 : ℝ))
          (fun σ => (expect_Top_pow_four_le p hp hp1 σ (ind f)).trans hind)
        rwa [expect_one] at this
    _ = ((25 / 4 : ℝ) ^ K) ^ 2 := mul_one _

lemma Qc_nonneg (p : ℝ) (f : Cube n → Bool) (K : ℕ) (i : Fin n) (x : Cube n) :
    0 ≤ Qc p f K i x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma expect_Qc_le (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (K : ℕ) (i : Fin n) :
    expect p (fun x => Qc p f K i x) ≤
      ∑ S : Finset (Fin n), (if i ∈ S then fhat p f S ^ 2 else 0) := by
  classical
  unfold Qc
  rw [expect_sum]
  refine le_trans (Finset.sum_le_sum (fun S _ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (low n K))
      (fun _ _ _ => by split_ifs <;> positivity))
  split_ifs with hi
  · have hE : expect p (fun x => FS p f S x ^ 2) = fhat p f S ^ 2 := by
      simpa using expect_sq_sum_FS p hp hp1 f {S}
    rw [expect_congr p _ (fun x => ((2 / 5 : ℝ) ^ S.card) ^ 2 * FS p f S x ^ 2)
      (fun x => by ring), expect_smul, hE]
    have h1 : ((2 / 5 : ℝ) ^ S.card) ^ 2 ≤ 1 := pow_le_one₀ (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
    nlinarith [sq_nonneg (fhat p f S)]
  · simp [expect_def]

lemma sum_expect_Qc_le (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (K : ℕ) (C : ℝ)
    (hI : FriedgutCoalition.totalPInfl p f ≤ C) :
    ∑ i : Fin n, expect p (fun x => Qc p f K i x) ≤ C / 2 := by
  classical
  refine (Finset.sum_le_sum (fun i _ => expect_Qc_le p hp hp1 f K i)).trans ?_
  rw [Finset.sum_comm]
  have h : ∀ S : Finset (Fin n), ∑ i : Fin n, (if i ∈ S then fhat p f S ^ 2 else 0) =
      (S.card : ℝ) * fhat p f S ^ 2 := by
    intro S
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  simp only [h]
  rw [totalPInfl_eq p hp hp1 f] at hI
  linarith

theorem big_J_term (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (K : ℕ) (C : ℝ)
    (hI : FriedgutCoalition.totalPInfl p f ≤ C) (τ N lam : ℝ) (hτ : 0 < τ) (hN : 0 < N)
    (hlam : 0 < lam) :
    expect p (fun x => if N ≤ ((Jx p f K τ x).card : ℝ) then Vx p f K x else 0) ≤
      lam / 2 * (C / (2 * τ * N)) + ((25 / 4 : ℝ) ^ K) ^ 2 / (2 * lam) := by
  classical
  -- the event bound
  have hev : ∀ x, (if N ≤ ((Jx p f K τ x).card : ℝ) then (1 : ℝ) else 0) ≤
      (1 / (τ * N)) * ∑ i : Fin n, Qc p f K i x := by
    intro x
    have hS0 : 0 ≤ ∑ i : Fin n, Qc p f K i x :=
      Finset.sum_nonneg (fun i _ => Qc_nonneg p f K i x)
    split_ifs with h
    · have h1 : ((Jx p f K τ x).card : ℝ) * τ ≤ ∑ i : Fin n, Qc p f K i x := by
        calc ((Jx p f K τ x).card : ℝ) * τ = ∑ i ∈ Jx p f K τ x, τ := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ i ∈ Jx p f K τ x, Qc p f K i x :=
              Finset.sum_le_sum (fun i hi => by simpa [Jx] using hi)
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => Qc_nonneg p f K i x)
      have h2 : τ * N ≤ ∑ i : Fin n, Qc p f K i x := by nlinarith
      rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    · positivity
  have hEev : expect p (fun x => if N ≤ ((Jx p f K τ x).card : ℝ) then (1 : ℝ) else 0) ≤
      C / (2 * τ * N) := by
    refine (expect_mono p hp.le hp1.le _ _ hev).trans ?_
    rw [expect_smul, expect_sum]
    have := sum_expect_Qc_le p hp hp1 f K C hI
    calc 1 / (τ * N) * ∑ i : Fin n, expect p (fun x => Qc p f K i x)
        ≤ 1 / (τ * N) * (C / 2) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = C / (2 * τ * N) := by field_simp
  have hpt : ∀ x, (if N ≤ ((Jx p f K τ x).card : ℝ) then Vx p f K x else 0) ≤
      lam / 2 * (if N ≤ ((Jx p f K τ x).card : ℝ) then (1 : ℝ) else 0) +
        (1 / (2 * lam)) * Vx p f K x ^ 2 := by
    intro x
    split_ifs
    · have h0 : 0 ≤ (Vx p f K x - lam) ^ 2 / (2 * lam) := by positivity
      have e : (Vx p f K x - lam) ^ 2 / (2 * lam) =
          lam / 2 * 1 + 1 / (2 * lam) * Vx p f K x ^ 2 - Vx p f K x := by
        field_simp; ring
      linarith
    · have : 0 ≤ 1 / (2 * lam) * Vx p f K x ^ 2 := by positivity
      linarith
  refine (expect_mono p hp.le hp1.le _ _ hpt).trans ?_
  rw [expect_add, expect_smul, expect_smul]
  have hV := expect_Vx_sq p hp hp1 f K
  have h1 : lam / 2 * expect p (fun x => if N ≤ ((Jx p f K τ x).card : ℝ) then (1 : ℝ) else 0) ≤
      lam / 2 * (C / (2 * τ * N)) := mul_le_mul_of_nonneg_left hEev (by positivity)
  have h2 : 1 / (2 * lam) * expect p (fun x => Vx p f K x ^ 2) ≤
      1 / (2 * lam) * ((25 / 4 : ℝ) ^ K) ^ 2 := mul_le_mul_of_nonneg_left hV (by positivity)
  have h3 : 1 / (2 * lam) * ((25 / 4 : ℝ) ^ K) ^ 2 = ((25 / 4 : ℝ) ^ K) ^ 2 / (2 * lam) := by ring
  linarith

end NarrowDNF.Dev.Bg.PartM2
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
alias big_J_term := NarrowDNF.Dev.Bg.PartM2.big_J_term

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Bg
theorem total_bound {n : ℕ} (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (K : ℕ) (C : ℝ)
    (hI : FriedgutCoalition.totalPInfl p f ≤ C) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (N lam ε₁ : ℝ) (hN : 0 < N) (hlam : 0 < lam) :
    expect p (fun x => ∑ S ∈ low n K, (if |FS p f S x| ≤ ε₁ then FS p f S x ^ 2 else 0)) ≤
      (25 / 4 : ℝ) ^ K * (θ * C) +
        (lam / 2 * (C / (2 * (θ ^ 4 / 9 ^ K) * N)) + ((25 / 4 : ℝ) ^ K) ^ 2 / (2 * lam)) +
        (N + 1) ^ K * ε₁ ^ 2 := by
  set τ : ℝ := θ ^ 4 / 9 ^ K with hτdef
  have hτ : 0 < τ := by positivity
  have h1 := expect_mono p hp.le hp1.le _ _
    (fun x => pointwise_split p f K τ N ε₁ hN.le x)
  refine h1.trans ?_
  rw [expect_add, expect_add, expect_smul, expect_sum]
  have hc : expect p (fun _ : Cube n => (N + 1) ^ K * ε₁ ^ 2) = (N + 1) ^ K * ε₁ ^ 2 := by
    have := expect_smul p ((N + 1) ^ K * ε₁ ^ 2) (fun _ : Cube n => (1 : ℝ))
    simp only [mul_one] at this
    rw [this, expect_one, mul_one]
  rw [hc]
  have hkey : ∑ i : Fin n, expect p (fun x => if Qc p f K i x < τ then Qc p f K i x else 0)
      ≤ θ * C := by
    calc _ ≤ ∑ i : Fin n, θ * expect p (fun x => |gder p f i x|) :=
          Finset.sum_le_sum (fun i _ => key_coord p hp hp1 f K i θ hθ hθ1)
      _ = θ * FriedgutCoalition.totalPInfl p f := by
          rw [← Finset.mul_sum, sum_expect_abs_gder p hp hp1 f]
      _ ≤ θ * C := mul_le_mul_of_nonneg_left hI hθ.le
  have hbig := big_J_term p hp hp1 f K C hI τ N lam hτ hN hlam
  have h25 : (0 : ℝ) ≤ (25 / 4 : ℝ) ^ K := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hkey h25]

end NarrowDNF.Dev.Bg.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
/-! ## Assembly -/
alias total_bound := NarrowDNF.Dev.Bg.PartA.total_bound

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Bg
theorem poly_le (m : ℕ) (hm : 100 ≤ m) : 6 * (m + 1) ^ 4 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : (m + 1 + 1) ^ 4 ≤ 2 * (m + 1) ^ 4 := by
      have ht : 101 ≤ m + 1 := by omega
      generalize m + 1 = t at ht ⊢
      have h3 : 101 * t ^ 3 ≤ t * t ^ 3 := Nat.mul_le_mul_right _ ht
      have h4 : t ^ 2 ≤ t ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have h5 : t ≤ t ^ 3 := by
        calc t = t ^ 1 := (pow_one t).symm
          _ ≤ t ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
      have h6 : 1 ≤ t ^ 3 := Nat.one_le_pow _ _ (by omega)
      ring_nf; ring_nf at h3; nlinarith
    rw [pow_succ 2 m]; linarith

theorem N_eq (K : ℕ) : ((25 / 4 : ℝ) ^ K) ^ 2 / (((1 / 64 : ℝ) ^ K) ^ 4 / 9 ^ K) =
    ((25 / 4 : ℝ) ^ 2 * 64 ^ 4 * 9) ^ K := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, one_div_pow, ← pow_mul, ← pow_mul,
    mul_comm 2 K, mul_comm 4 K]
  have : (0:ℝ) < (64 : ℝ) ^ (4 * K) := by positivity
  field_simp

theorem M_le : (25 / 4 : ℝ) ^ 2 * 64 ^ 4 * 9 ≤ Real.exp 23 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 23 = Real.exp 1 ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (25 / 4 : ℝ) ^ 2 * 64 ^ 4 * 9 ≤ (2.7182818283 : ℝ) ^ 23 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h.le _

theorem t3_aux (k ε₀ : ℝ) (hk : 0 < k) (hε : 1 ≤ k * ε₀) :
    Real.exp (-(1976 * k ^ 2)) ≤ ε₀ / (3 * k) := by
  have he : Real.exp (-(1976 * k ^ 2)) * Real.exp (1976 * k ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hge := Real.add_one_le_exp (1976 * k ^ 2)
  have hpos := Real.exp_pos (-(1976 * k ^ 2))
  have h1 : Real.exp (-(1976 * k ^ 2)) * (3 * k ^ 2) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hge hpos.le]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem T1 (K : ℕ) (k ε₀ : ℝ) (hk0 : 0 < k) (hε₀ : 0 < ε₀) (hkK : k < K + 1) (hK : 1000 ≤ K) :
    (25 / 4 : ℝ) ^ K * ((1 / 64 : ℝ) ^ K * (k * ε₀)) ≤ ε₀ / (3 * k) := by
  have hpoly : (6 : ℝ) * ((K : ℝ) + 1) ^ 4 ≤ 2 ^ K := by
    exact_mod_cast poly_le K (by omega)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  have hk2 : k ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hk0.le hkK.le 2
  have hK24 : ((K : ℝ) + 1) ^ 2 ≤ ((K : ℝ) + 1) ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
  have hAθ : (25 / 4 : ℝ) ^ K * (1 / 64 : ℝ) ^ K = (25 / 256 : ℝ) ^ K := by
    rw [← mul_pow]; norm_num
  have h2 : (25 / 256 : ℝ) ^ K * 2 ^ K ≤ 1 := by
    rw [← mul_pow]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : (25 / 256 : ℝ) ^ K * (3 * k ^ 2) ≤ 1 := by
    have : 3 * k ^ 2 ≤ (2 : ℝ) ^ K := by
      have : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ 4 := by positivity
      linarith
    have h0 : (0 : ℝ) ≤ (25 / 256 : ℝ) ^ K := by positivity
    linarith [mul_le_mul_of_nonneg_left this h0]
  rw [← mul_assoc, hAθ, le_div_iff₀ (by positivity)]
  have h0 : (0 : ℝ) ≤ (25 / 256 : ℝ) ^ K := by positivity
  generalize (25 / 256 : ℝ) ^ K = a at h0 h3 ⊢
  nlinarith

theorem T2 (K : ℕ) (k ε₀ : ℝ) (hk0 : 0 < k) (hε₀ : 0 < ε₀) (hε : 1 ≤ k * ε₀) (hkK : k < K + 1) :
    3 * k ^ 2 / (20 * ((K : ℝ) + 1) ^ 4) ≤ ε₀ / (6 * k) := by
  have hk4 : k ^ 4 ≤ ((K : ℝ) + 1) ^ 4 := pow_le_pow_left₀ hk0.le hkK.le 4
  have hK0 : 0 < (K : ℝ) + 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  generalize ((K : ℝ) + 1) ^ 4 = b at hk4 ⊢
  have h3 : (0 : ℝ) ≤ k ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hk4 (show (0:ℝ) ≤ 20 * ε₀ by positivity),
    mul_le_mul_of_nonneg_left hε h3]

theorem N1 (K : ℕ) (hK : 1000 ≤ K) :
    5 * ((K : ℝ) + 1) ^ 4 * ((25 / 4 : ℝ) ^ 2 * 64 ^ 4 * 9) ^ K + 1 ≤ Real.exp (24 * K) := by
  have hpoly : (6 : ℝ) * ((K : ℝ) + 1) ^ 4 ≤ 2 ^ K := by
    exact_mod_cast poly_le K (by omega)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) + 1 := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  have e1 : (2 : ℝ) ^ K ≤ Real.exp K := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1]) K
  have e2 : ((25 / 4 : ℝ) ^ 2 * 64 ^ 4 * 9) ^ K ≤ Real.exp (23 * K) := by
    rw [mul_comm (23 : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) M_le K
  have hM1 : 1 ≤ ((25 / 4 : ℝ) ^ 2 * 64 ^ 4 * 9) ^ K := one_le_pow₀ (by norm_num)
  have e3 : Real.exp (24 * K) = Real.exp K * Real.exp (23 * K) := by
    rw [← Real.exp_add]; ring_nf
  rw [e3]
  generalize ((25 / 4 : ℝ) ^ 2 * 64 ^ 4 * 9) ^ K = m at e2 hM1 ⊢
  have h6 : (6 : ℝ) * ((K : ℝ) + 1) ^ 4 ≤ Real.exp K := hpoly.trans e1
  have hp41 : 1 ≤ ((K : ℝ) + 1) ^ 4 := one_le_pow₀ hK1
  have hMK : 0 ≤ m := by linarith
  have ham : 1 ≤ ((K : ℝ) + 1) ^ 4 * m := one_le_mul_of_one_le_of_one_le hp41 hM1
  calc 5 * ((K : ℝ) + 1) ^ 4 * m + 1 ≤ 6 * ((K : ℝ) + 1) ^ 4 * m := by linarith
    _ ≤ Real.exp K * m := mul_le_mul_of_nonneg_right h6 hMK
    _ ≤ Real.exp K * Real.exp (23 * K) := mul_le_mul_of_nonneg_left e2 (Real.exp_pos _).le

theorem T3 (K : ℕ) (k ε₀ N : ℝ) (hk0 : 0 < k) (hε : 1 ≤ k * ε₀) (hKk : (K : ℝ) ≤ k)
    (hN0 : 0 ≤ N) (hN1 : N + 1 ≤ Real.exp (24 * K)) :
    (N + 1) ^ K * Real.exp (-(1000 * k ^ 2)) ^ 2 ≤ ε₀ / (3 * k) := by
  have hNK : (N + 1) ^ K ≤ Real.exp (24 * K) ^ K := pow_le_pow_left₀ (by linarith) hN1 K
  rw [← Real.exp_nat_mul] at hNK
  have hsq : Real.exp (-(1000 * k ^ 2)) ^ 2 = Real.exp (2 * (-(1000 * k ^ 2))) := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hsq]
  have hKK : (K : ℝ) * (24 * K) ≤ 24 * k ^ 2 := by
    have := mul_le_mul hKk hKk (Nat.cast_nonneg _) hk0.le
    calc (K : ℝ) * (24 * K) = 24 * ((K : ℝ) * K) := by ring
      _ ≤ 24 * (k * k) := by linarith
      _ = 24 * k ^ 2 := by ring
  have hprod : (N + 1) ^ K * Real.exp (2 * (-(1000 * k ^ 2))) ≤ Real.exp (-(1976 * k ^ 2)) := by
    calc (N + 1) ^ K * Real.exp (2 * (-(1000 * k ^ 2)))
        ≤ Real.exp ((K : ℝ) * (24 * K)) * Real.exp (2 * (-(1000 * k ^ 2))) :=
          mul_le_mul_of_nonneg_right hNK (Real.exp_pos _).le
      _ = Real.exp ((K : ℝ) * (24 * K) + 2 * (-(1000 * k ^ 2))) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact hprod.trans (t3_aux k ε₀ hk0 hε)

theorem core (K : ℕ) (k ε₀ Cr : ℝ) (hk0 : 0 < k) (hε₀ : 0 < ε₀) (hCk : Cr = k * ε₀)
    (hε : 1 ≤ k * ε₀) (hKk : (K : ℝ) ≤ k) (hkK : k < K + 1) (hK : 1000 ≤ K) :
    (25 / 4 : ℝ) ^ K * ((1 / 64 : ℝ) ^ K * Cr) +
      (3 * k * ((25 / 4 : ℝ) ^ K) ^ 2 / ε₀ / 2 *
          (Cr / (2 * (((1 / 64 : ℝ) ^ K) ^ 4 / 9 ^ K) *
            (5 * ((K : ℝ) + 1) ^ 4 * ((25 / 4 : ℝ) ^ K) ^ 2 / (((1 / 64 : ℝ) ^ K) ^ 4 / 9 ^ K)))) +
        ((25 / 4 : ℝ) ^ K) ^ 2 / (2 * (3 * k * ((25 / 4 : ℝ) ^ K) ^ 2 / ε₀))) +
      (5 * ((K : ℝ) + 1) ^ 4 * ((25 / 4 : ℝ) ^ K) ^ 2 / (((1 / 64 : ℝ) ^ K) ^ 4 / 9 ^ K) + 1) ^ K *
        Real.exp (-(1000 * k ^ 2)) ^ 2 ≤ ε₀ / k := by
  have hNeq : 5 * ((K : ℝ) + 1) ^ 4 * ((25 / 4 : ℝ) ^ K) ^ 2 / (((1 / 64 : ℝ) ^ K) ^ 4 / 9 ^ K) =
      5 * ((K : ℝ) + 1) ^ 4 * ((25 / 4 : ℝ) ^ 2 * 64 ^ 4 * 9) ^ K := by
    rw [mul_div_assoc, N_eq K]
  have hT1 := T1 K k ε₀ hk0 hε₀ hkK hK
  have hT2 := T2 K k ε₀ hk0 hε₀ hε hkK
  have hN0 : 0 ≤ 5 * ((K : ℝ) + 1) ^ 4 * ((25 / 4 : ℝ) ^ 2 * 64 ^ 4 * 9) ^ K := by positivity
  have hT3 := T3 K k ε₀ _ hk0 hε hKk hN0 (N1 K hK)
  have hτ : (0 : ℝ) < ((1 / 64 : ℝ) ^ K) ^ 4 / 9 ^ K := by positivity
  have hA : (0 : ℝ) < (25 / 4 : ℝ) ^ K := by positivity
  have hK0 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hT2a : 3 * k * ((25 / 4 : ℝ) ^ K) ^ 2 / ε₀ / 2 *
          (Cr / (2 * (((1 / 64 : ℝ) ^ K) ^ 4 / 9 ^ K) *
            (5 * ((K : ℝ) + 1) ^ 4 * ((25 / 4 : ℝ) ^ K) ^ 2 / (((1 / 64 : ℝ) ^ K) ^ 4 / 9 ^ K)))) =
      3 * k ^ 2 / (20 * ((K : ℝ) + 1) ^ 4) := by
    generalize ((1 / 64 : ℝ) ^ K) ^ 4 / 9 ^ K = τ at hτ ⊢
    generalize (25 / 4 : ℝ) ^ K = A at hA ⊢
    rw [hCk]; field_simp; ring
  have hT2b : ((25 / 4 : ℝ) ^ K) ^ 2 / (2 * (3 * k * ((25 / 4 : ℝ) ^ K) ^ 2 / ε₀)) =
      ε₀ / (6 * k) := by
    generalize (25 / 4 : ℝ) ^ K = A at hA ⊢
    field_simp; ring
  have hsum : ε₀ / (3 * k) + (ε₀ / (6 * k) + ε₀ / (6 * k)) + ε₀ / (3 * k) = ε₀ / k := by
    field_simp; ring
  rw [hT2a, hT2b, hNeq, hCk]
  linarith

theorem numerics (C : ℕ) (hC : 1 ≤ C) (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀_le : ε₀ ≤ 1 / 1000) :
    let k : ℝ := C / ε₀
    let K : ℕ := ⌊k⌋₊
    let θ : ℝ := (1 / 64 : ℝ) ^ K
    let τ : ℝ := θ ^ 4 / 9 ^ K
    let lam : ℝ := 3 * k * ((25 / 4 : ℝ) ^ K) ^ 2 / ε₀
    let N : ℝ := 5 * ((K : ℝ) + 1) ^ 4 * ((25 / 4 : ℝ) ^ K) ^ 2 / τ
    (25 / 4 : ℝ) ^ K * (θ * C) + (lam / 2 * (C / (2 * τ * N)) + ((25 / 4 : ℝ) ^ K) ^ 2 / (2 * lam)) +
        (N + 1) ^ K * Real.exp (-(1000 * k ^ 2)) ^ 2 ≤ ε₀ / k := by
  intro k K θ τ lam N
  have hCpos : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hk : (1000 : ℝ) ≤ k := by
    show (1000 : ℝ) ≤ (C : ℝ) / ε₀
    rw [le_div_iff₀ hε₀]; nlinarith
  have hk0 : 0 < k := by linarith
  have hCk : (C : ℝ) = k * ε₀ := by
    show (C : ℝ) = C / ε₀ * ε₀
    field_simp
  have hKk : (K : ℝ) ≤ k := Nat.floor_le hk0.le
  have hkK : k < K + 1 := Nat.lt_floor_add_one k
  have hK1000 : 1000 ≤ K := Nat.le_floor (by exact_mod_cast hk)
  exact core K k ε₀ C hk0 hε₀ hCk (hCk ▸ hCpos) hKk hkK hK1000

end NarrowDNF.Dev.Bg.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
alias numerics := NarrowDNF.Dev.Bg.PartA.numerics

/-- the published statement, proved from the stubs -/
theorem hatami_step_two_small_low_degree_mass_dev {n : ℕ} (p : ℝ) (f : Cube n → Bool)
    (hp : 0 < p) (hp_half : p ≤ 1 / 2) (C : ℕ) (hC : 1 ≤ C)
    (hI : FriedgutCoalition.totalPInfl p f ≤ C) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀_le : ε₀ ≤ 1 / 1000) :
    let k : ℝ := C / ε₀
    let ε₁ : ℝ := Real.exp (-(1000 * k ^ 2))
    let r : Bool → ℝ := fun b => if b then Real.sqrt ((1 - p) / p) else -Real.sqrt (p / (1 - p))
    let F : Finset (Fin n) → Cube n → ℝ := fun S x =>
      expect p (fun y => (if f y then 1 else 0) * ∏ i ∈ S, r (y i)) * ∏ i ∈ S, r (x i)
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => (S.card : ℝ) ≤ k),
      expect p (fun x => if |F S x| ≤ ε₁ then F S x ^ 2 else 0) ≤ ε₀ / k := by
  intro k ε₁ r F
  have hp1 : p < 1 := by linarith
  have hk0 : 0 ≤ k := by positivity
  have hF : ∀ S x, F S x = FS p f S x := fun S x => rfl
  have hfilt : Finset.univ.filter (fun S : Finset (Fin n) => (S.card : ℝ) ≤ k) = low n ⌊k⌋₊ := by
    ext S
    simp only [low, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Nat.le_floor_iff hk0).symm
  rw [hfilt]
  simp only [hF]
  rw [← expect_sum]
  have hnum := numerics C hC ε₀ hε₀ hε₀_le
  simp only at hnum
  refine le_trans (total_bound p hp hp1 f ⌊k⌋₊ C hI ((1 / 64 : ℝ) ^ ⌊k⌋₊) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num))
    (5 * ((⌊k⌋₊ : ℝ) + 1) ^ 4 * ((25 / 4 : ℝ) ^ ⌊k⌋₊) ^ 2 /
      (((1 / 64 : ℝ) ^ ⌊k⌋₊) ^ 4 / 9 ^ ⌊k⌋₊))
    (3 * k * ((25 / 4 : ℝ) ^ ⌊k⌋₊) ^ 2 / ε₀) ε₁ (by positivity) (by positivity)) ?_
  exact hnum

end NarrowDNF.Dev.Bg
end

section
set_option autoImplicit false
open NarrowDNF
open NarrowDNF.Dev
open NarrowDNF.Dev.Bg
open NarrowDNF.Approx
variable {n : ℕ}
theorem solution {n : ℕ} (p : ℝ) (f : Cube n → Bool)
    (hp : 0 < p) (hp_half : p ≤ 1 / 2) (C : ℕ) (hC : 1 ≤ C)
    (hI : FriedgutCoalition.totalPInfl p f ≤ C) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀_le : ε₀ ≤ 1 / 1000) :
    let k : ℝ := C / ε₀
    let ε₁ : ℝ := Real.exp (-(1000 * k ^ 2))
    let r : Bool → ℝ := fun b => if b then Real.sqrt ((1 - p) / p) else -Real.sqrt (p / (1 - p))
    let F : Finset (Fin n) → Cube n → ℝ := fun S x =>
      expect p (fun y => (if f y then 1 else 0) * ∏ i ∈ S, r (y i)) * ∏ i ∈ S, r (x i)
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => (S.card : ℝ) ≤ k),
      expect p (fun x => if |F S x| ≤ ε₁ then F S x ^ 2 else 0) ≤ ε₀ / k := by
  exact NarrowDNF.Dev.Bg.hatami_step_two_small_low_degree_mass_dev p f hp hp_half C hC hI ε₀ hε₀ hε₀_le
end
