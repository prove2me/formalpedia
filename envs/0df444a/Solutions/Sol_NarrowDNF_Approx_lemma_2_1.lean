-- Prove2me | solution 1 for NarrowDNF.Approx.lemma_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T10:19:33.098641+00:00
-- url     : https://prove2.me/submissions/e426ea8c-ec5c-46bd-ba40-e85c19181095
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NarrowDNF_Approx_Activation
import Theorems.Thm_NarrowDNF_Approx_hatami_step_two_small_low_degree_mass

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
/-! Blueprint for `NarrowDNF.Approx.lemma_2_1` from the published Step II leaf
`NarrowDNF.Approx.hatami_step_two_small_low_degree_mass` (Hatami 2012, eq. (11)).
Hatami's Steps I, III and IV, with the leaf supplying Step II. -/
/-! ## Basic objects -/
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

/-- point mass of `x_T` -/
noncomputable def mu (p : ℝ) (T : Finset (Fin n)) (x : Cube n) : ℝ :=
  ∏ i ∈ T, FriedgutCoalition.bern p (x i)

def DependsOn {β : Type*} (D : Finset (Fin n)) (g : Cube n → β) : Prop :=
  ∀ x y : Cube n, (∀ i ∈ D, x i = y i) → g x = g y

/-- conditional expectation on the cells of `a` -/
noncomputable def cexp {α : Type*} [DecidableEq α] (p : ℝ) (a : Cube n → α) (G : Cube n → ℝ)
    (x : Cube n) : ℝ :=
  expect p (fun y => if a y = a x then G y else 0) / expect p (fun y => if a y = a x then 1 else 0)

/-- the activations inside `S` only -/
def restrictJ (J : ActivationFamily n) (S : Finset (Fin n)) : ActivationFamily n :=
  fun T z => if T ⊆ S then J T z else false

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
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

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
/-! ## Part A: product-measure basics (any real `p`) -/

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
/-- splitting the cube along `A` -/
lemma expect_split (p : ℝ) (A : Finset (Fin n)) (c : Cube n → ℝ) :
    expect p c = ∑ s : {i // i ∈ A} → Bool, ∑ t : {i // i ∉ A} → Bool,
      (∏ i, FriedgutCoalition.bern p (s i)) * (∏ i, FriedgutCoalition.bern p (t i)) *
        c ((Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ A) (fun _ => Bool)).symm (s, t)) := by
  classical
  rw [expect_def]
  let e := Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ A) (fun _ => Bool)
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
  congr 1
  unfold w
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin n => i ∈ A)]
  congr 1
  · refine Finset.prod_congr (by ext; simp) (fun i _ => ?_)
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply]
  · refine Finset.prod_congr (by ext; simp) (fun i _ => ?_)
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, i.2]

theorem expect_mul_of_disjoint (p : ℝ) (A B : Finset (Fin n)) (g h : Cube n → ℝ)
    (hg : DependsOn A g) (hh : DependsOn B h) (hAB : Disjoint A B) :
    expect p (fun x => g x * h x) = expect p g * expect p h := by
  classical
  rw [expect_split p A, expect_split p A g, expect_split p A h]
  set e := Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ A) (fun _ => Bool) with he
  let G' : ({i // i ∈ A} → Bool) → ℝ := fun s => g (e.symm (s, fun _ => false))
  let H' : ({i // i ∉ A} → Bool) → ℝ := fun t => h (e.symm (fun _ => false, t))
  have hG : ∀ s t, g (e.symm (s, t)) = G' s := by
    intro s t
    apply hg
    intro i hi
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hi]
  have hH : ∀ s t, h (e.symm (s, t)) = H' t := by
    intro s t
    apply hh
    intro i hi
    have hiA : i ∉ A := fun h' => Finset.disjoint_left.mp hAB h' hi
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hiA]
  have hsA : ∑ s : {i // i ∈ A} → Bool, ∏ i, FriedgutCoalition.bern p (s i) = 1 := by
    rw [sum_prod_cube' (fun _ b => FriedgutCoalition.bern p b)]
    simp only [bern_sum, Finset.prod_const_one]
  have hsB : ∑ t : {i // i ∉ A} → Bool, ∏ i, FriedgutCoalition.bern p (t i) = 1 := by
    rw [sum_prod_cube' (fun _ b => FriedgutCoalition.bern p b)]
    simp only [bern_sum, Finset.prod_const_one]
  simp only [hG, hH]
  have e1 : ∀ s : {i // i ∈ A} → Bool, ∑ t : {i // i ∉ A} → Bool,
      (∏ i, FriedgutCoalition.bern p (s i)) * (∏ i, FriedgutCoalition.bern p (t i)) * G' s =
      (∏ i, FriedgutCoalition.bern p (s i)) * G' s := by
    intro s
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsB, mul_one]
  have e2 : ∑ s : {i // i ∈ A} → Bool, ∑ t : {i // i ∉ A} → Bool,
      (∏ i, FriedgutCoalition.bern p (s i)) * (∏ i, FriedgutCoalition.bern p (t i)) * H' t =
      ∑ t : {i // i ∉ A} → Bool, (∏ i, FriedgutCoalition.bern p (t i)) * H' t := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsA, one_mul]
  simp only [e1, e2]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
  ring

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
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

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias expect_mul_eq_zero_of_mean_zero := NarrowDNF.Dev.Hat.PartA.expect_mul_eq_zero_of_mean_zero

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
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

lemma bern_mul_abs_r (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (b : Bool) :
    FriedgutCoalition.bern p b * |r p b| = Real.sqrt (p * (1 - p)) := by
  have h1 := p_mul_r_true p hp hp1
  have h2 := q_mul_r_false p hp hp1
  cases b
  · simp only [FriedgutCoalition.bern, Bool.false_eq_true, if_false]
    rw [show (1 - p) * |r p false| = |(1 - p) * r p false| by
      rw [abs_mul, abs_of_pos (show 0 < 1 - p by linarith)], h2, abs_neg,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  · simp only [FriedgutCoalition.bern, if_true]
    rw [show p * |r p true| = |p * r p true| by rw [abs_mul, abs_of_pos hp], h1,
      abs_of_nonneg (Real.sqrt_nonneg _)]

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

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
/-! ## Part F: the `p`-biased Walsh expansion (`0 < p ≤ 1/2`) -/
alias fourier_inversion := NarrowDNF.Dev.Hat.PartA.fourier_inversion

alias expect_sq_sum_FS := NarrowDNF.Dev.Hat.PartA.expect_sq_sum_FS

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
lemma ind_sq (f : Cube n → Bool) (x : Cube n) : ind f x ^ 2 = ind f x := by
  unfold ind; split_ifs <;> norm_num

lemma ind_nonneg (f : Cube n → Bool) (x : Cube n) : 0 ≤ ind f x := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (f : Cube n → Bool) (x : Cube n) : ind f x ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

theorem sum_fhat_sq_le_one (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) :
    ∑ S : Finset (Fin n), fhat p f S ^ 2 ≤ 1 := by
  rw [← expect_sq_sum_FS p hp hp1 f Finset.univ]
  rw [expect_congr p _ (fun x => ind f x) (fun x => by
    rw [← fourier_inversion p hp hp1 f x, ind_sq])]
  rw [← expect_one (n := n) p]
  exact expect_mono p hp.le hp1.le _ _ (fun x => ind_le_one f x)

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias sum_fhat_sq_le_one := NarrowDNF.Dev.Hat.PartA.sum_fhat_sq_le_one

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem FS_dependsOn (p : ℝ) (f : Cube n → Bool) (S : Finset (Fin n)) :
    DependsOn S (FS p f S) := by
  intro x y h
  simp only [FS, chi]
  congr 1
  exact Finset.prod_congr rfl (fun i hi => by rw [h i hi])

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias FS_dependsOn := NarrowDNF.Dev.Hat.PartA.FS_dependsOn

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
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

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias FS_mean_zero := NarrowDNF.Dev.Hat.PartA.FS_mean_zero

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem mu_mul_abs_FS (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool)
    (S : Finset (Fin n)) (x : Cube n) :
    mu p S x * |FS p f S x| = |fhat p f S| * Real.sqrt (p * (1 - p)) ^ S.card := by
  simp only [FS, mu, chi, abs_mul, Finset.abs_prod]
  rw [show (∏ i ∈ S, FriedgutCoalition.bern p (x i)) * (|fhat p f S| * ∏ i ∈ S, |r p (x i)|) =
    |fhat p f S| * ((∏ i ∈ S, FriedgutCoalition.bern p (x i)) * ∏ i ∈ S, |r p (x i)|) by ring]
  rw [← Finset.prod_mul_distrib]
  simp only [bern_mul_abs_r p hp hp1, Finset.prod_const]

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
lemma expect_abs_chi (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (S : Finset (Fin n)) :
    expect p (fun x => |chi p S x|) = (2 * Real.sqrt (p * (1 - p))) ^ S.card := by
  simp only [chi, Finset.abs_prod]
  rw [expect_prod_coord p S (fun _ b => |r p b|)]
  have h1 := bern_mul_abs_r p hp hp1 true
  have h0 := bern_mul_abs_r p hp hp1 false
  simp only [FriedgutCoalition.bern, if_true, Bool.false_eq_true, if_false] at h1 h0
  rw [h1, h0, Finset.prod_const]
  ring

lemma abs_fhat_le (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (S : Finset (Fin n)) :
    |fhat p f S| ≤ (2 * Real.sqrt (p * (1 - p))) ^ S.card := by
  rw [← expect_abs_chi p hp hp1 S, fhat, expect_def, expect_def]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => ?_))
  rw [abs_mul, abs_of_pos (w_pos p hp hp1 x), abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (w_pos p hp hp1 x).le
  rw [abs_of_nonneg (ind_nonneg f x)]
  exact mul_le_of_le_one_left (abs_nonneg _) (ind_le_one f x)

theorem abs_fhat_mul_le (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool)
    (S : Finset (Fin n)) :
    |fhat p f S| * Real.sqrt (p * (1 - p)) ^ S.card ≤ 2 ^ S.card * p ^ S.card := by
  have hs : Real.sqrt (p * (1 - p)) * Real.sqrt (p * (1 - p)) = p * (1 - p) :=
    Real.mul_self_sqrt (by nlinarith)
  calc |fhat p f S| * Real.sqrt (p * (1 - p)) ^ S.card
      ≤ (2 * Real.sqrt (p * (1 - p))) ^ S.card * Real.sqrt (p * (1 - p)) ^ S.card :=
        mul_le_mul_of_nonneg_right (abs_fhat_le p hp hp1 f S) (by positivity)
    _ = (2 * (p * (1 - p))) ^ S.card := by
        rw [← mul_pow, mul_assoc, hs]
    _ ≤ (2 * p) ^ S.card := by
        apply pow_le_pow_left₀ (by nlinarith)
        nlinarith
    _ = 2 ^ S.card * p ^ S.card := mul_pow _ _ _

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
lemma abs_r_le_true (p : ℝ) (hp : 0 < p) (hp_half : p ≤ 1 / 2) (b : Bool) : |r p b| ≤ |r p true| := by
  cases b
  · simp only [r, Bool.false_eq_true, if_false, if_true, abs_neg]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    have hq : 0 < 1 - p := by linarith
    rw [div_le_div_iff₀ hq hp]
    nlinarith
  · exact le_rfl

theorem pow_le_prob_large (p : ℝ) (hp : 0 < p) (hp_half : p ≤ 1 / 2) (f : Cube n → Bool)
    (S : Finset (Fin n)) (ε₁ : ℝ) (h : ∃ x, ε₁ < |FS p f S x|) :
    p ^ S.card ≤ expect p (fun x => if ε₁ ≤ |FS p f S x| then 1 else 0) := by
  classical
  have hp1 : p < 1 := by linarith
  obtain ⟨x, hx⟩ := h
  have key : ∀ y : Cube n, (∀ i ∈ S, y i = true) → |FS p f S x| ≤ |FS p f S y| := by
    intro y hy
    simp only [FS, chi, abs_mul, Finset.abs_prod]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i hi => ?_)
    rw [hy i hi]
    exact abs_r_le_true p hp hp_half _
  have h1 : expect p (fun y => ∏ i ∈ S, (fun _ (b : Bool) => if b = true then (1 : ℝ) else 0) i (y i))
      = p ^ S.card := by
    rw [expect_prod_coord p S (fun _ (b : Bool) => if b = true then (1 : ℝ) else 0)]
    simp [Finset.prod_const]
  rw [← h1]
  refine expect_mono p hp.le hp1.le _ _ (fun y => ?_)
  simp only
  rw [Finset.prod_ite_zero]
  split_ifs with h2 h3
  · simp
  · exact absurd (hx.le.trans (key y h2)) h3
  · norm_num
  · norm_num

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem mu_le_prob_large (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool)
    (S : Finset (Fin n)) (ε₁ : ℝ) (x : Cube n) (hx : ε₁ ≤ |FS p f S x|) :
    mu p S x ≤ expect p (fun y => if ε₁ ≤ |FS p f S y| then 1 else 0) := by
  classical
  have h1 : expect p (fun y => ∏ i ∈ S, (fun i (b : Bool) => if b = x i then (1 : ℝ) else 0) i (y i))
      = mu p S x := by
    rw [expect_prod_coord p S (fun i (b : Bool) => if b = x i then (1 : ℝ) else 0), mu]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    cases x i <;> simp [FriedgutCoalition.bern]
  rw [← h1]
  refine expect_mono p hp.le hp1.le _ _ (fun y => ?_)
  simp only
  rw [Finset.prod_ite_zero]
  split_ifs with h2 h3
  · simp
  · exact absurd (by rw [FS_dependsOn p f S y x h2]; exact hx) h3
  · norm_num
  · norm_num

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias mu_le_prob_large := NarrowDNF.Dev.Hat.PartA.mu_le_prob_large

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem prob_large_le (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool)
    (S : Finset (Fin n)) (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    expect p (fun x => if ε₁ ≤ |FS p f S x| then 1 else 0) ≤ fhat p f S ^ 2 / ε₁ ^ 2 := by
  have hE : expect p (fun x => FS p f S x ^ 2) = fhat p f S ^ 2 := by
    have := expect_sq_sum_FS p hp hp1 f {S}
    simpa using this
  have h2 : expect p (fun x => (1 / ε₁ ^ 2) * FS p f S x ^ 2) = fhat p f S ^ 2 / ε₁ ^ 2 := by
    rw [expect_smul, hE]; ring
  rw [← h2]
  refine expect_mono p hp.le hp1.le _ _ (fun x => ?_)
  split_ifs with h
  · rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity), one_mul, ← sq_abs (FS p f S x)]
    exact pow_le_pow_left₀ hε₁.le h 2
  · positivity

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias prob_large_le := NarrowDNF.Dev.Hat.PartA.prob_large_le

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem expect_inv_mu (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (T : Finset (Fin n)) :
    expect p (fun x => 1 / mu p T x) = 2 ^ T.card := by
  have h1 : ∀ x : Cube n, 1 / mu p T x =
      ∏ i ∈ T, (fun _ (b : Bool) => 1 / FriedgutCoalition.bern p b) i (x i) := by
    intro x
    simp only [mu, one_div, Finset.prod_inv_distrib]
  rw [expect_congr p _ _ h1, expect_prod_coord p T (fun _ (b : Bool) => 1 / FriedgutCoalition.bern p b)]
  have hq : (1 - p) ≠ 0 := by linarith
  simp only [FriedgutCoalition.bern, if_true, Bool.false_eq_true, if_false]
  rw [Finset.prod_const]
  congr 1
  field_simp
  ring

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

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias totalPInfl_eq := NarrowDNF.Dev.Hat.PartA.totalPInfl_eq

alias expect_inv_mu := NarrowDNF.Dev.Hat.PartA.expect_inv_mu

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
/-! ## Part C -/
lemma cexp_den_pos {α : Type*} [DecidableEq α] (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (a : Cube n → α) (x : Cube n) :
    0 < expect p (fun y => if a y = a x then (1 : ℝ) else 0) := by
  rw [expect_def]
  have h := Finset.single_le_sum (f := fun y => w p y * (if a y = a x then (1 : ℝ) else 0))
    (fun y _ => mul_nonneg (w_pos p hp hp1 y).le (by split_ifs <;> norm_num)) (Finset.mem_univ x)
  simp only [if_true, mul_one] at h
  exact lt_of_lt_of_le (w_pos p hp hp1 x) h

theorem cexp_congr {α : Type*} [DecidableEq α] (p : ℝ) (a : Cube n → α) (G : Cube n → ℝ)
    (x y : Cube n) (h : a x = a y) : cexp p a G x = cexp p a G y := by
  simp only [cexp, h]

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
/-! ## Part C: conditional expectation on cells (`0 < p < 1`) -/
alias cexp_congr := NarrowDNF.Dev.Hat.PartA.cexp_congr

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem cexp_eq_self {α : Type*} [DecidableEq α] (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (a : Cube n → α) (G : Cube n → ℝ) (x : Cube n) (h : ∀ y, a y = a x → G y = G x) :
    cexp p a G x = G x := by
  have hD := cexp_den_pos p hp hp1 a x
  unfold cexp
  rw [div_eq_iff hD.ne', ← expect_smul]
  refine expect_congr p _ _ (fun y => ?_)
  split_ifs with hy
  · rw [h y hy, mul_one]
  · rw [mul_zero]

theorem expect_cexp_mul {α : Type*} [DecidableEq α] (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (a : Cube n → α) (G H : Cube n → ℝ) (hH : ∀ x y, a x = a y → H x = H y) :
    expect p (fun x => cexp p a G x * H x) = expect p (fun x => G x * H x) := by
  set D : Cube n → ℝ := fun x => expect p (fun y => if a y = a x then (1 : ℝ) else 0) with hDdef
  have hDc : ∀ x y, a x = a y → D x = D y := by
    intro x y h; simp only [hDdef, h]
  have hDpos : ∀ x, 0 < D x := fun x => cexp_den_pos p hp hp1 a x
  set c : Cube n → ℝ := fun y => w p y * G y * H y / D y with hc
  have h1 : ∀ x : Cube n, w p x * (cexp p a G x * H x) =
      ∑ y : Cube n, (if a y = a x then w p x * c y else 0) := by
    intro x
    unfold cexp
    rw [expect_def, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    split_ifs with h
    · simp only [hc]
      rw [hH x y h.symm]
      change w p x * ((w p y * G y / D x) * H y) = _
      rw [← hDc y x h]
      ring
    · simp
  rw [expect_def, Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_comm, expect_def]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have h2 : ∑ x : Cube n, (if a y = a x then w p x * c y else 0) = c y * D y := by
    simp only [hDdef, expect_def, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases h : a y = a x
    · rw [if_pos h, if_pos h.symm]; ring
    · rw [if_neg h, if_neg (Ne.symm h)]; ring
  rw [h2, hc]
  have := hDpos y
  field_simp

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias expect_cexp_mul := NarrowDNF.Dev.Hat.PartA.expect_cexp_mul

alias cexp_eq_self := NarrowDNF.Dev.Hat.PartA.cexp_eq_self

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
lemma mu_le_expect (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) (x : Cube n)
    (c : Cube n → ℝ) (hc0 : ∀ y, 0 ≤ c y) (hc : ∀ y, (∀ i ∈ S, y i = x i) → 1 ≤ c y) :
    mu p S x ≤ expect p c := by
  classical
  have h1 : expect p (fun y => ∏ i ∈ S, (fun i (b : Bool) => if b = x i then (1 : ℝ) else 0) i (y i))
      = mu p S x := by
    rw [expect_prod_coord p S (fun i (b : Bool) => if b = x i then (1 : ℝ) else 0), mu]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    cases x i <;> simp [FriedgutCoalition.bern]
  rw [← h1]
  refine expect_mono p hp hp1 _ _ (fun y => ?_)
  simp only
  rw [Finset.prod_ite_zero]
  split_ifs with h2
  · simpa using hc y h2
  · exact hc0 y

theorem abs_cexp_FS_le {α : Type*} [DecidableEq α] (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (f : Cube n → Bool) (S : Finset (Fin n)) (a : Cube n → α) (ha : DependsOn S a) (x : Cube n) :
    |cexp p a (FS p f S) x| ≤ 2 ^ S.card * |FS p f S x| := by
  have hD := cexp_den_pos p hp hp1 a x
  have hmu : mu p S x ≤ expect p (fun y => if a y = a x then (1 : ℝ) else 0) := by
    refine mu_le_expect p hp.le hp1.le S x _ (fun y => by split_ifs <;> norm_num) (fun y hy => ?_)
    rw [if_pos (ha y x hy)]
  have hE : expect p (fun y => |FS p f S y|) = 2 ^ S.card * |FS p f S x| * mu p S x := by
    simp only [FS, abs_mul]
    rw [expect_smul, expect_abs_chi p hp hp1]
    have := mu_mul_abs_FS p hp hp1 f S x
    simp only [FS, abs_mul] at this
    rw [mul_pow, show (2:ℝ) ^ S.card * (|fhat p f S| * |chi p S x|) * mu p S x =
      2 ^ S.card * (mu p S x * (|fhat p f S| * |chi p S x|)) by ring, this]
    ring
  unfold cexp
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
  calc |expect p (fun y => if a y = a x then FS p f S y else 0)|
      ≤ expect p (fun y => |FS p f S y|) := by
        rw [expect_def, expect_def]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun y _ => ?_))
        rw [abs_mul, abs_of_pos (w_pos p hp hp1 y)]
        refine mul_le_mul_of_nonneg_left ?_ (w_pos p hp hp1 y).le
        split_ifs <;> simp
    _ = 2 ^ S.card * |FS p f S x| * mu p S x := hE
    _ ≤ 2 ^ S.card * |FS p f S x| * expect p (fun y => if a y = a x then (1 : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left hmu (by positivity)

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
/-! ## helpers -/
lemma sigma_eq {A B : Finset (Fin n)} (f : A → Bool) (g : B → Bool) (h : A = B)
    (hf : ∀ k (hk : k ∈ A), f ⟨k, hk⟩ = g ⟨k, h ▸ hk⟩) :
    (⟨A, f⟩ : Σ S : Finset (Fin n), S → Bool) = ⟨B, g⟩ := by
  subst h
  congr
  funext ⟨k, hk⟩
  exact hf k hk

lemma sigma_agree {A B : Finset (Fin n)} (f : A → Bool) (g : B → Bool)
    (h : (⟨A, f⟩ : Σ S : Finset (Fin n), S → Bool) = ⟨B, g⟩) :
    ∃ hAB : A = B, ∀ k (hk : k ∈ A), f ⟨k, hk⟩ = g ⟨k, hAB ▸ hk⟩ := by
  obtain ⟨hAB, hh⟩ := Sigma.mk.inj_iff.mp h
  subst hAB
  refine ⟨rfl, fun k hk => ?_⟩
  have := eq_of_heq hh
  exact congrFun this ⟨k, hk⟩

lemma atom_iff (J : ActivationFamily n) (x y : Cube n) :
    atom J x = atom J y ↔
      activeUnion J x = activeUnion J y ∧ ∀ k ∈ activeUnion J x, x k = y k := by
  constructor
  · intro h
    obtain ⟨hAB, hk⟩ := sigma_agree _ _ h
    exact ⟨hAB, fun k hk' => hk k hk'⟩
  · rintro ⟨hA, hk⟩
    exact sigma_eq _ _ hA (fun k hk' => hk k hk')

lemma mem_activeUnion (J : ActivationFamily n) (x : Cube n) (k : Fin n) :
    k ∈ activeUnion J x ↔ ∃ S : Finset (Fin n), J S (fun i => x i) = true ∧ k ∈ S := by
  classical
  simp [activeUnion, Finset.mem_biUnion]

lemma act_sub (J : ActivationFamily n) (x : Cube n) (S : Finset (Fin n))
    (h : J S (fun i => x i) = true) : S ⊆ activeUnion J x :=
  fun k hk => (mem_activeUnion J x k).2 ⟨S, h, hk⟩

lemma act_congr (J : ActivationFamily n) (x y : Cube n) (S : Finset (Fin n))
    (h : ∀ k ∈ S, x k = y k) : J S (fun i => x i) = J S (fun i => y i) := by
  congr 1
  funext k
  exact h k k.2

lemma union_eq_of_iff (J : ActivationFamily n) (x y : Cube n)
    (key : ∀ T, J T (fun i => x i) = true ↔ J T (fun i => y i) = true) :
    activeUnion J x = activeUnion J y := by
  ext k
  rw [mem_activeUnion, mem_activeUnion]
  constructor
  · rintro ⟨T, hT, hk⟩; exact ⟨T, (key T).1 hT, hk⟩
  · rintro ⟨T, hT, hk⟩; exact ⟨T, (key T).2 hT, hk⟩

lemma restrictJ_true (J : ActivationFamily n) (S T : Finset (Fin n)) (z : T → Bool)
    (h : restrictJ J S T z = true) : T ⊆ S ∧ J T z = true := by
  unfold restrictJ at h
  split_ifs at h with hT
  · exact ⟨hT, h⟩

lemma bern_nonneg (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) :
    0 ≤ FriedgutCoalition.bern p b := by
  cases b <;> simp [FriedgutCoalition.bern] <;> linarith

lemma bern_pos (p : ℝ) (h0 : 0 < p) (h1 : p < 1) (b : Bool) :
    0 < FriedgutCoalition.bern p b := by
  cases b <;> simp [FriedgutCoalition.bern] <;> linarith

lemma bern_anti (p : ℝ) (hp : p ≤ 1 / 2) {a b : Bool} (hab : a ≤ b) :
    FriedgutCoalition.bern p b ≤ FriedgutCoalition.bern p a := by
  cases a <;> cases b
  · exact le_refl _
  · simp [FriedgutCoalition.bern]; linarith
  · exact absurd hab (by decide)
  · exact le_refl _

lemma mu_pos (p : ℝ) (h0 : 0 < p) (h1 : p < 1) (T : Finset (Fin n)) (x : Cube n) :
    0 < mu p T x :=
  Finset.prod_pos (fun i _ => bern_pos p h0 h1 _)

lemma w_nonneg (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : Cube n) :
    0 ≤ ∏ i : Fin n, FriedgutCoalition.bern p (x i) :=
  Finset.prod_nonneg (fun i _ => bern_nonneg p h0 h1 _)

lemma expect_add (p : ℝ) (g h : Cube n → ℝ) :
    expect p (fun x => g x + h x) = expect p g + expect p h := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

lemma expect_sub (p : ℝ) (g h : Cube n → ℝ) :
    expect p (fun x => g x - h x) = expect p g - expect p h := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

lemma expect_const_mul (p : ℝ) (c : ℝ) (g : Cube n → ℝ) :
    expect p (fun x => c * g x) = c * expect p g := by
  simp only [expect, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => by ring)

lemma expect_mono (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (g h : Cube n → ℝ) (hgh : ∀ x, g x ≤ h x) :
    expect p g ≤ expect p h :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hgh x) (w_nonneg p h0 h1 x))

lemma expect_nonneg (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (g : Cube n → ℝ) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ expect p g :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (w_nonneg p h0 h1 x) (hg x))

/-! ## Part J -/
theorem atom_restrictJ_congr (J : ActivationFamily n) (S : Finset (Fin n)) (x y : Cube n)
    (h : atom J x = atom J y) : atom (restrictJ J S) x = atom (restrictJ J S) y := by
  rw [atom_iff] at h ⊢
  obtain ⟨hA, hag⟩ := h
  have key : ∀ T, restrictJ J S T (fun i => x i) = true ↔
      restrictJ J S T (fun i => y i) = true := by
    intro T
    unfold restrictJ
    by_cases hT : T ⊆ S
    · simp only [hT, if_true]
      constructor
      · intro hx
        rw [← act_congr J x y T (fun k hk => hag k (act_sub J x T hx hk))]
        exact hx
      · intro hy
        have := act_sub J y T hy
        rw [← hA] at this
        rw [act_congr J x y T (fun k hk => hag k (this hk))]
        exact hy
    · simp [hT]
  refine ⟨union_eq_of_iff _ x y key, fun k hk => ?_⟩
  obtain ⟨T, hT, hkT⟩ := (mem_activeUnion _ _ _).1 hk
  exact hag k (act_sub J x T (restrictJ_true J S T _ hT).2 hkT)

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
/-! ## Part J: restricted activation families -/

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem atom_restrictJ_dependsOn (J : ActivationFamily n) (S : Finset (Fin n)) :
    DependsOn S (atom (restrictJ J S)) := by
  intro x y hxy
  rw [atom_iff]
  have key : ∀ T, restrictJ J S T (fun i => x i) = true ↔
      restrictJ J S T (fun i => y i) = true := by
    intro T
    unfold restrictJ
    by_cases hT : T ⊆ S
    · simp only [hT, if_true]
      rw [act_congr J x y T (fun k hk => hxy k (hT hk))]
    · simp [hT]
  refine ⟨union_eq_of_iff _ x y key, fun k hk => ?_⟩
  obtain ⟨T, hT, hkT⟩ := (mem_activeUnion _ _ _).1 hk
  exact hxy k ((restrictJ_true J S T _ hT).1 hkT)

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem eq_on_of_atom_restrictJ (J : ActivationFamily n) (S T : Finset (Fin n)) (hTS : T ⊆ S)
    (x y : Cube n) (hx : J T (fun i => x i) = true)
    (h : atom (restrictJ J S) y = atom (restrictJ J S) x) : ∀ i ∈ T, y i = x i := by
  rw [atom_iff] at h
  obtain ⟨hA, hag⟩ := h
  intro i hi
  have hR : restrictJ J S T (fun i => x i) = true := by
    unfold restrictJ; simp only [hTS, if_true]; exact hx
  have := act_sub _ x T hR hi
  rw [← hA] at this
  exact hag i this

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

/-! ## Part M: the construction and its estimates -/
/-- parameters and objects of the construction -/
structure Setup (n : ℕ) where
  p : ℝ
  f : Cube n → Bool
  K : ℕ
  ε₁ : ℝ
  δ : ℝ

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
namespace Setup
variable (σ : Setup n)
noncomputable def Sfam : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (fun S => S.card ≤ σ.K ∧ ∃ x, σ.ε₁ < |FS σ.p σ.f S x|)

noncomputable def large (S : Finset (Fin n)) : ℝ :=
  expect σ.p (fun x => if σ.ε₁ ≤ |FS σ.p σ.f S x| then 1 else 0)

/-- Hatami's `b_T` -/
noncomputable def b (T : Finset (Fin n)) : ℝ := by
  classical
  exact ∑ S ∈ σ.Sfam.filter (fun S => T ⊆ S), σ.large S

/-- Hatami's activations (10) -/
noncomputable def J : ActivationFamily n := fun T z => by
  classical
  exact decide (T.card ≤ σ.K ∧ σ.δ * ∏ i : T, FriedgutCoalition.bern σ.p (z i) ≤ σ.b T)

noncomputable def Ft (S : Finset (Fin n)) (x : Cube n) : ℝ :=
  cexp σ.p (atom (restrictJ σ.J S)) (FS σ.p σ.f S) x

noncomputable def g (x : Cube n) : ℝ := ∑ S ∈ σ.Sfam, FS σ.p σ.f S x

noncomputable def gt (x : Cube n) : ℝ := ∑ S ∈ σ.Sfam, σ.Ft S x

end Setup
end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
/-- standing hypotheses on the parameters -/
structure Setup.Good (σ : Setup n) : Prop where
  hp : 0 < σ.p
  hp_half : σ.p ≤ 1 / 2
  hε₁ : 0 < σ.ε₁
  hδ : 0 < σ.δ
  hδ1 : σ.δ ≤ 1

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
/-! ## Part M -/
theorem J_apply (σ : Setup n) (T : Finset (Fin n)) (x : Cube n) :
    σ.J T (fun i => x i) = true ↔ T.card ≤ σ.K ∧ σ.δ * mu σ.p T x ≤ σ.b T := by
  simp only [Setup.J, decide_eq_true_eq, mu]
  rw [Finset.prod_coe_sort T (fun i => FriedgutCoalition.bern σ.p (x i))]

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem J_increasing (σ : Setup n) (hσ : σ.Good) : IncreasingActivations σ.J := by
  intro T z z' hzz'
  cases h : σ.J T z
  · exact Bool.false_le _
  · simp only [Setup.J, decide_eq_true_eq] at h ⊢
    refine le_of_eq (Eq.symm ?_)
    simp only [decide_eq_true_eq]
    refine ⟨h.1, le_trans ?_ h.2⟩
    refine mul_le_mul_of_nonneg_left ?_ hσ.hδ.le
    refine Finset.prod_le_prod (fun i _ => bern_nonneg _ hσ.hp.le (by linarith [hσ.hp_half]) _)
      (fun i _ => bern_anti _ hσ.hp_half (hzz' i))

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem arity_J_le (σ : Setup n) : arity σ.J ≤ σ.K := by
  classical
  unfold arity
  refine Finset.sup_le (fun S hS => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  obtain ⟨z, hz⟩ := hS
  simp only [Setup.J, decide_eq_true_eq] at hz
  exact hz.1

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
lemma large_nonneg (σ : Setup n) (hσ : σ.Good) (S : Finset (Fin n)) : 0 ≤ σ.large S := by
  unfold Setup.large
  exact expect_nonneg _ hσ.hp.le (by linarith [hσ.hp_half]) _ (fun x => by split_ifs <;> norm_num)

lemma b_nonneg (σ : Setup n) (hσ : σ.Good) (T : Finset (Fin n)) : 0 ≤ σ.b T := by
  classical
  unfold Setup.b
  exact Finset.sum_nonneg (fun S _ => large_nonneg σ hσ S)

theorem J_of_large (σ : Setup n) (hσ : σ.Good) (S : Finset (Fin n)) (hS : S ∈ σ.Sfam)
    (x : Cube n) (hx : σ.ε₁ ≤ |FS σ.p σ.f S x|) : σ.J S (fun i => x i) = true := by
  classical
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  rw [J_apply]
  have hcard : S.card ≤ σ.K := by
    unfold Setup.Sfam at hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact hS.1
  refine ⟨hcard, ?_⟩
  have h1 : mu σ.p S x ≤ σ.large S := mu_le_prob_large σ.p hσ.hp hp1 σ.f S σ.ε₁ x hx
  have h2 : σ.large S ≤ σ.b S := by
    unfold Setup.b
    convert Finset.single_le_sum (f := fun S => σ.large S)
      (fun S _ => large_nonneg σ hσ S)
      (Finset.mem_filter.2 ⟨hS, Finset.Subset.refl S⟩)
  have hmu := (mu_pos σ.p hσ.hp hp1 S x).le
  calc σ.δ * mu σ.p S x ≤ 1 * mu σ.p S x := mul_le_mul_of_nonneg_right hσ.hδ1 hmu
    _ = mu σ.p S x := one_mul _
    _ ≤ σ.b S := h1.trans h2

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartC
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
/-! ## helpers -/
lemma Ft_dependsOn (σ : Setup n) (S : Finset (Fin n)) : DependsOn S (σ.Ft S) := by
  intro x y h
  unfold Setup.Ft
  exact PartA.cexp_congr _ _ _ _ _ (PartB.atom_restrictJ_dependsOn σ.J S x y h)

lemma expect_zero' (p : ℝ) : expect p (fun _ : Cube n => (0 : ℝ)) = 0 := by
  simp [expect]

lemma abs_expect_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (c : Cube n → ℝ) :
    |expect p c| ≤ expect p (fun x => |c x|) := by
  rw [PartA.expect_def, PartA.expect_def]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => ?_))
  rw [abs_mul, abs_of_nonneg (PartA.w_nonneg p hp hp1 x)]

lemma mu_union (p : ℝ) (A B : Finset (Fin n)) (h : Disjoint A B) (x : Cube n) :
    mu p (A ∪ B) x = mu p A x * mu p B x := by
  classical
  unfold mu
  exact Finset.prod_union h

/-- the cylinder `{x_T = y_T}` -/
noncomputable def cyl (T : Finset (Fin n)) (y x : Cube n) : ℝ := by
  classical
  exact if ∀ j ∈ T, x j = y j then 1 else 0

lemma cyl_decomp (T : Finset (Fin n)) (x : Cube n) (Ψ : Cube n → ℝ) :
    ∑ y ∈ Finset.univ.filter (fun y : Cube n => ∀ j, j ∉ T → y j = false), cyl T y x * Ψ y =
      Ψ (fun j => if j ∈ T then x j else false) := by
  classical
  rw [Finset.sum_eq_single_of_mem (fun j => if j ∈ T then x j else false)]
  · unfold cyl
    rw [if_pos (fun j hj => by simp [hj]), one_mul]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj; simp [hj]
  · intro y hy hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    unfold cyl
    rw [if_neg, zero_mul]
    intro hc
    apply hne
    funext j
    by_cases hj : j ∈ T
    · simp [hj, hc j hj]
    · simp [hj, hy j hj]

/-! ## (a): the cross term vanishes on `J_T` -/
lemma pair_J_zero_y (σ : Setup n) (hσ : σ.Good) (S₁ S₂ : Finset (Fin n)) (i : Fin n)
    (hi1 : i ∈ S₁) (hi2 : i ∉ S₂) (y : Cube n) (hy : σ.J (S₁ ∩ S₂) (fun j => y j) = true) :
    expect σ.p (fun x => σ.Ft S₁ x * cyl (S₁ ∩ S₂) y x * σ.Ft S₂ x) = 0 := by
  classical
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  set T := S₁ ∩ S₂ with hT
  let K : Cube n → ℝ := fun x => σ.Ft S₂ (fun j => if j ∈ T then y j else x j)
  have h1 : ∀ x, σ.Ft S₁ x * cyl T y x * σ.Ft S₂ x = σ.Ft S₁ x * cyl T y x * K x := by
    intro x
    unfold cyl
    split_ifs with hc
    · have : σ.Ft S₂ x = K x := by
        refine Ft_dependsOn σ S₂ _ _ (fun j _ => ?_)
        by_cases hj : j ∈ T
        · simp [hj, hc j hj]
        · simp [hj]
      rw [this]
    · simp
  have hK : DependsOn (S₂ \ S₁) K := by
    intro x x' hxx'
    refine Ft_dependsOn σ S₂ _ _ (fun j hj => ?_)
    by_cases hjT : j ∈ T
    · simp [hjT]
    · have : j ∉ S₁ := fun h => hjT (Finset.mem_inter.2 ⟨h, hj⟩)
      simp [hjT, hxx' j (Finset.mem_sdiff.2 ⟨hj, this⟩)]
  have hG : DependsOn S₁ (fun x => σ.Ft S₁ x * cyl T y x) := by
    intro x x' hxx'
    simp only
    rw [Ft_dependsOn σ S₁ x x' hxx']
    unfold cyl
    have : (∀ j ∈ T, x j = y j) ↔ (∀ j ∈ T, x' j = y j) := by
      constructor
      · intro h j hj; rw [← hxx' j (Finset.mem_inter.1 hj).1]; exact h j hj
      · intro h j hj; rw [hxx' j (Finset.mem_inter.1 hj).1]; exact h j hj
    simp only [this]
  rw [PartA.expect_congr _ _ _ h1,
    PartA.expect_mul_of_disjoint σ.p S₁ (S₂ \ S₁) _ K hG hK Finset.disjoint_sdiff]
  -- tower
  have hcell : ∀ x x', atom (restrictJ σ.J S₁) x = atom (restrictJ σ.J S₁) x' →
      cyl T y x = cyl T y x' := by
    have key : ∀ x x', atom (restrictJ σ.J S₁) x = atom (restrictJ σ.J S₁) x' →
        (∀ j ∈ T, x j = y j) → ∀ j ∈ T, x' j = y j := by
      intro x x' h hx j hj
      have hJx : σ.J T (fun j => x j) = true := by
        rw [PartB.act_congr σ.J x y T hx]; exact hy
      have := PartB.eq_on_of_atom_restrictJ σ.J S₁ T Finset.inter_subset_left x x' hJx h.symm
      rw [this j hj]; exact hx j hj
    intro x x' h
    unfold cyl
    by_cases hx : ∀ j ∈ T, x j = y j
    · rw [if_pos hx, if_pos (key x x' h hx)]
    · have hx' : ¬ ∀ j ∈ T, x' j = y j := fun h' => hx (key x' x h.symm h')
      rw [if_neg hx, if_neg hx']
  have htower : expect σ.p (fun x => σ.Ft S₁ x * cyl T y x) =
      expect σ.p (fun x => FS σ.p σ.f S₁ x * cyl T y x) := by
    unfold Setup.Ft
    exact PartA.expect_cexp_mul σ.p hσ.hp hp1 _ _ _ hcell
  have hzero : expect σ.p (fun x => FS σ.p σ.f S₁ x * cyl T y x) = 0 := by
    refine PartA.expect_mul_eq_zero_of_mean_zero σ.p i _ _
      (PartA.FS_mean_zero σ.p hσ.hp hp1 σ.f S₁ i hi1) (fun x b => ?_)
    unfold cyl
    have hiT : i ∉ T := fun h => hi2 (Finset.mem_inter.1 h).2
    have : ∀ j ∈ T, Function.update x i b j = x j := by
      intro j hj
      have : j ≠ i := fun h => hiT (h ▸ hj)
      simp [Function.update_of_ne this]
    have hiff : (∀ j ∈ T, Function.update x i b j = y j) ↔ (∀ j ∈ T, x j = y j) :=
      ⟨fun h j hj => by rw [← this j hj]; exact h j hj,
        fun h j hj => by rw [this j hj]; exact h j hj⟩
    by_cases hx : ∀ j ∈ T, x j = y j
    · rw [if_pos (hiff.2 hx), if_pos hx]
    · rw [if_neg (fun h => hx (hiff.1 h)), if_neg hx]
  rw [htower, hzero, zero_mul]

lemma pair_J_zero (σ : Setup n) (hσ : σ.Good) (S₁ S₂ : Finset (Fin n)) (i : Fin n)
    (hi1 : i ∈ S₁) (hi2 : i ∉ S₂) :
    expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x *
      (if σ.J (S₁ ∩ S₂) (fun j => x j) = true then 1 else 0)) = 0 := by
  classical
  set T := S₁ ∩ S₂ with hT
  set P := Finset.univ.filter (fun y : Cube n => ∀ j, j ∉ T → y j = false)
  have h1 : ∀ x, σ.Ft S₁ x * σ.Ft S₂ x * (if σ.J T (fun j => x j) = true then 1 else 0) =
      ∑ y ∈ P, (if σ.J T (fun j => y j) = true then 1 else 0) *
        (σ.Ft S₁ x * cyl T y x * σ.Ft S₂ x) := by
    intro x
    have := cyl_decomp T x (fun y => (if σ.J T (fun j => y j) = true then (1 : ℝ) else 0) *
      (σ.Ft S₁ x * σ.Ft S₂ x))
    have hJ := PartB.act_congr σ.J (fun j => if j ∈ T then x j else false) x T
      (fun j hj => by simp [hj])
    rw [hJ] at this
    rw [mul_comm _ (if σ.J T (fun j => x j) = true then (1 : ℝ) else 0), ← this]
    refine Finset.sum_congr rfl (fun y _ => by ring)
  rw [PartA.expect_congr _ _ _ h1, PartA.expect_sum]
  refine Finset.sum_eq_zero (fun y _ => ?_)
  by_cases hy : σ.J T (fun j => y j) = true
  · simp only [hy, if_true, one_mul]
    exact pair_J_zero_y σ hσ S₁ S₂ i hi1 hi2 y hy
  · simp only [hy, if_false, Bool.false_eq_true, zero_mul]
    exact expect_zero' σ.p

/-! ## (b): the per-pair bound -/
/-- `E[1[¬J_T]/μ_T²]` -/
noncomputable def Q (σ : Setup n) (T : Finset (Fin n)) : ℝ :=
  expect σ.p (fun x => (if σ.J T (fun j => x j) = true then 0 else 1) / mu σ.p T x ^ 2)

lemma Q_nonneg (σ : Setup n) (hσ : σ.Good) (T : Finset (Fin n)) : 0 ≤ Q σ T := by
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  unfold Q
  refine PartA.expect_nonneg _ hσ.hp.le hp1.le _ (fun x => ?_)
  have := PartB.mu_pos σ.p hσ.hp hp1 T x
  split_ifs <;> positivity

lemma abs_FS_le (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (f : Cube n → Bool) (S : Finset (Fin n))
    (x : Cube n) : |FS p f S x| ≤ 2 ^ S.card * p ^ S.card / mu p S x := by
  have hμ := PartB.mu_pos p hp hp1 S x
  rw [le_div_iff₀ hμ, mul_comm, PartA.mu_mul_abs_FS p hp hp1]
  exact PartA.abs_fhat_mul_le p hp hp1 f S

lemma abs_Ft_le (σ : Setup n) (hσ : σ.Good) (S : Finset (Fin n)) (x : Cube n) :
    |σ.Ft S x| ≤ 2 ^ S.card * (2 ^ S.card * σ.p ^ S.card / mu σ.p S x) := by
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  unfold Setup.Ft
  refine (PartA.abs_cexp_FS_le σ.p hσ.hp hp1 σ.f S _ (PartB.atom_restrictJ_dependsOn σ.J S) x).trans ?_
  exact mul_le_mul_of_nonneg_left (abs_FS_le σ.p hσ.hp hp1 σ.f S x) (by positivity)

lemma pair_split (σ : Setup n) (hσ : σ.Good) (S₁ S₂ : Finset (Fin n)) (hne : S₁ ≠ S₂) :
    expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x) =
      expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x *
        (if σ.J (S₁ ∩ S₂) (fun j => x j) = true then 0 else 1)) := by
  have h1 : ∀ x, σ.Ft S₁ x * σ.Ft S₂ x = σ.Ft S₁ x * σ.Ft S₂ x *
      (if σ.J (S₁ ∩ S₂) (fun j => x j) = true then 1 else 0) + σ.Ft S₁ x * σ.Ft S₂ x *
        (if σ.J (S₁ ∩ S₂) (fun j => x j) = true then 0 else 1) := by
    intro x; split_ifs <;> ring
  rw [PartA.expect_congr _ _ _ h1, PartA.expect_add]
  by_cases hsub : S₁ ⊆ S₂
  · have : ¬ S₂ ⊆ S₁ := fun h => hne (Finset.Subset.antisymm hsub h)
    obtain ⟨i, hi2, hi1⟩ := Finset.not_subset.1 this
    have h0 := pair_J_zero σ hσ S₂ S₁ i hi2 hi1
    rw [Finset.inter_comm S₂ S₁] at h0
    have : expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x *
        (if σ.J (S₁ ∩ S₂) (fun j => x j) = true then 1 else 0)) = 0 := by
      exact (PartA.expect_congr _ _ _ (fun x => by ring)).trans h0
    rw [this, zero_add]
  · obtain ⟨i, hi1, hi2⟩ := Finset.not_subset.1 hsub
    rw [pair_J_zero σ hσ S₁ S₂ i hi1 hi2, zero_add]

lemma mu_pair (p : ℝ) (S₁ S₂ : Finset (Fin n)) (x : Cube n) :
    mu p S₁ x * mu p S₂ x = mu p (S₁ ∩ S₂) x ^ 2 * mu p (S₁ \ S₂ ∪ S₂ \ S₁) x := by
  classical
  have e1 : mu p S₁ x = mu p (S₁ \ S₂) x * mu p (S₁ ∩ S₂) x := by
    rw [← mu_union p _ _ (Finset.disjoint_sdiff_inter S₁ S₂), Finset.sdiff_union_inter]
  have e2 : mu p S₂ x = mu p (S₂ \ S₁) x * mu p (S₁ ∩ S₂) x := by
    rw [Finset.inter_comm, ← mu_union p _ _ (Finset.disjoint_sdiff_inter S₂ S₁),
      Finset.sdiff_union_inter]
  rw [mu_union p _ _ disjoint_sdiff_sdiff, e1, e2]
  ring

lemma pair_bound (σ : Setup n) (hσ : σ.Good) (S₁ S₂ : Finset (Fin n)) (hne : S₁ ≠ S₂)
    (h1 : S₁.card ≤ σ.K) (h2 : S₂.card ≤ σ.K) :
    |expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x)| ≤
      2 ^ (6 * σ.K) * (σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ (S₁ ∩ S₂)) := by
  classical
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  have hp := hσ.hp
  set T := S₁ ∩ S₂ with hT
  set D := S₁ \ S₂ ∪ S₂ \ S₁ with hD
  set C : ℝ := 2 ^ S₁.card * 2 ^ S₁.card * σ.p ^ S₁.card *
    (2 ^ S₂.card * 2 ^ S₂.card * σ.p ^ S₂.card) with hC
  have hpt : ∀ x, |σ.Ft S₁ x * σ.Ft S₂ x * (if σ.J T (fun j => x j) = true then 0 else 1)| ≤
      C * ((if σ.J T (fun j => x j) = true then 0 else 1) / mu σ.p T x ^ 2 *
        (1 / mu σ.p D x)) := by
    intro x
    have hN : (0 : ℝ) ≤ (if σ.J T (fun j => x j) = true then 0 else 1) := by
      split_ifs <;> norm_num
    have hμ1 := PartB.mu_pos σ.p hp hp1 S₁ x
    have hμ2 := PartB.mu_pos σ.p hp hp1 S₂ x
    have hμT := PartB.mu_pos σ.p hp hp1 T x
    have hμD := PartB.mu_pos σ.p hp hp1 D x
    have hm := mu_pair σ.p S₁ S₂ x
    rw [abs_mul, abs_mul, abs_of_nonneg hN]
    calc |σ.Ft S₁ x| * |σ.Ft S₂ x| * (if σ.J T (fun j => x j) = true then 0 else 1)
        ≤ (2 ^ S₁.card * (2 ^ S₁.card * σ.p ^ S₁.card / mu σ.p S₁ x)) *
          (2 ^ S₂.card * (2 ^ S₂.card * σ.p ^ S₂.card / mu σ.p S₂ x)) *
            (if σ.J T (fun j => x j) = true then 0 else 1) := by
          refine mul_le_mul_of_nonneg_right ?_ hN
          exact mul_le_mul (abs_Ft_le σ hσ S₁ x) (abs_Ft_le σ hσ S₂ x) (abs_nonneg _)
            (by positivity)
      _ = C * ((if σ.J T (fun j => x j) = true then 0 else 1) / mu σ.p T x ^ 2 *
          (1 / mu σ.p D x)) := by
          rw [hC]
          field_simp
          rw [← hT, ← hD] at hm
          rw [hm]
          ring
  have hdep1 : DependsOn T (fun x => (if σ.J T (fun j => x j) = true then (0 : ℝ) else 1) /
      mu σ.p T x ^ 2) := by
    intro x y hxy
    simp only
    rw [PartB.act_congr σ.J x y T hxy]
    unfold mu
    rw [Finset.prod_congr rfl (fun i hi => by rw [hxy i hi])]
  have hdep2 : DependsOn D (fun x => 1 / mu σ.p D x) := by
    intro x y hxy
    simp only
    unfold mu
    rw [Finset.prod_congr rfl (fun i hi => by rw [hxy i hi])]
  have hdisj : Disjoint T D := by
    rw [hT, hD, Finset.disjoint_union_right]
    constructor
    · exact (Finset.disjoint_sdiff_inter S₁ S₂).symm
    · rw [Finset.inter_comm]; exact (Finset.disjoint_sdiff_inter S₂ S₁).symm
  have hDcard : D.card ≤ S₁.card + S₂.card := by
    calc D.card ≤ (S₁ \ S₂).card + (S₂ \ S₁).card := Finset.card_union_le _ _
      _ ≤ S₁.card + S₂.card :=
        add_le_add (Finset.card_le_card Finset.sdiff_subset) (Finset.card_le_card Finset.sdiff_subset)
  rw [pair_split σ hσ S₁ S₂ hne]
  refine (abs_expect_le σ.p hp.le hp1.le _).trans ?_
  refine (PartA.expect_mono σ.p hp.le hp1.le _ _ hpt).trans ?_
  rw [PartA.expect_smul, PartA.expect_mul_of_disjoint σ.p T D _ _ hdep1 hdep2 hdisj,
    PartA.expect_inv_mu σ.p hp hp1 D]
  have hQ := Q_nonneg σ hσ T
  unfold Q at hQ ⊢
  have hcoef : (2 : ℝ) ^ S₁.card * 2 ^ S₁.card * (2 ^ S₂.card * 2 ^ S₂.card) * 2 ^ D.card ≤
      2 ^ (6 * σ.K) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hpp : 0 ≤ σ.p ^ S₁.card * σ.p ^ S₂.card := by positivity
  calc C * (expect σ.p (fun x => (if σ.J T (fun j => x j) = true then (0 : ℝ) else 1) /
        mu σ.p T x ^ 2) * 2 ^ D.card)
      = ((2 : ℝ) ^ S₁.card * 2 ^ S₁.card * (2 ^ S₂.card * 2 ^ S₂.card) * 2 ^ D.card) *
          (σ.p ^ S₁.card * σ.p ^ S₂.card * expect σ.p (fun x =>
            (if σ.J T (fun j => x j) = true then (0 : ℝ) else 1) / mu σ.p T x ^ 2)) := by
        rw [hC]; ring
    _ ≤ 2 ^ (6 * σ.K) * (σ.p ^ S₁.card * σ.p ^ S₂.card * expect σ.p (fun x =>
            (if σ.J T (fun j => x j) = true then (0 : ℝ) else 1) / mu σ.p T x ^ 2)) :=
        mul_le_mul_of_nonneg_right hcoef (mul_nonneg hpp hQ)

/-! ## (c): the sum -/
/-- `β_T = Σ_{S ∈ Sfam, S ⊇ T} p^{|S|}` -/
noncomputable def beta (σ : Setup n) (T : Finset (Fin n)) : ℝ := by
  classical
  exact ∑ S ∈ σ.Sfam.filter (fun S => T ⊆ S), σ.p ^ S.card

lemma Sfam_mem (σ : Setup n) (S : Finset (Fin n)) (hS : S ∈ σ.Sfam) :
    S.card ≤ σ.K ∧ ∃ x, σ.ε₁ < |FS σ.p σ.f S x| := by
  classical
  unfold Setup.Sfam at hS
  simpa using hS

lemma beta_nonneg (σ : Setup n) (hσ : σ.Good) (T : Finset (Fin n)) : 0 ≤ beta σ T := by
  classical
  unfold beta
  exact Finset.sum_nonneg (fun S _ => pow_nonneg hσ.hp.le _)

lemma beta_le_b (σ : Setup n) (hσ : σ.Good) (T : Finset (Fin n)) : beta σ T ≤ σ.b T := by
  classical
  unfold beta Setup.b
  refine Finset.sum_le_sum (fun S hS => ?_)
  have hS' := (Finset.mem_filter.1 hS).1
  exact PartA.pow_le_prob_large σ.p hσ.hp hσ.hp_half σ.f S σ.ε₁ (Sfam_mem σ S hS').2

lemma beta_zero (σ : Setup n) (T : Finset (Fin n)) (hT : σ.K < T.card) : beta σ T = 0 := by
  classical
  unfold beta
  refine Finset.sum_eq_zero (fun S hS => ?_)
  obtain ⟨hS1, hS2⟩ := Finset.mem_filter.1 hS
  have := (Sfam_mem σ S hS1).1
  have := Finset.card_le_card hS2
  omega

lemma beta_sq_Q_le (σ : Setup n) (hσ : σ.Good) (T : Finset (Fin n)) :
    beta σ T ^ 2 * Q σ T ≤ σ.δ * σ.b T * 2 ^ T.card := by
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  have hβ := beta_nonneg σ hσ T
  have hβb := beta_le_b σ hσ T
  have hδ := hσ.hδ
  unfold Q
  rw [← PartA.expect_smul, ← PartA.expect_inv_mu σ.p hσ.hp hp1 T, ← PartA.expect_smul]
  refine PartA.expect_mono σ.p hσ.hp.le hp1.le _ _ (fun x => ?_)
  have hμ := PartB.mu_pos σ.p hσ.hp hp1 T x
  have hb : 0 ≤ σ.b T := hβ.trans hβb
  by_cases hJ : σ.J T (fun j => x j) = true
  · simp only [hJ, if_true, zero_div, mul_zero]
    positivity
  · simp only [hJ, if_false, Bool.false_eq_true]
    rw [PartB.J_apply] at hJ
    by_cases hK : T.card ≤ σ.K
    · have hlt : σ.b T < σ.δ * mu σ.p T x := by
        by_contra h; exact hJ ⟨hK, le_of_not_gt h⟩
      have h2 : beta σ T ^ 2 ≤ σ.δ * σ.b T * mu σ.p T x := by nlinarith
      have e : σ.δ * σ.b T * (1 / mu σ.p T x) = σ.δ * σ.b T * mu σ.p T x / mu σ.p T x ^ 2 := by
        field_simp
      rw [e, one_div, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 (sq_nonneg _))
    · rw [beta_zero σ T (by omega)]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, one_div]
      positivity

lemma sum_b_two (σ : Setup n) :
    ∑ T : Finset (Fin n), σ.b T * 2 ^ T.card = ∑ S ∈ σ.Sfam, 3 ^ S.card * σ.large S := by
  classical
  unfold Setup.b
  simp_rw [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have : ∀ T : Finset (Fin n), (if T ⊆ S then σ.large S else 0) * 2 ^ T.card =
      if T ∈ S.powerset then 2 ^ T.card * σ.large S else 0 := by
    intro T
    by_cases hT : T ⊆ S
    · rw [if_pos hT, if_pos (Finset.mem_powerset.2 hT)]; ring
    · rw [if_neg hT, if_neg (fun h => hT (Finset.mem_powerset.1 h))]; ring
  rw [Finset.sum_congr rfl (fun T _ => this T), ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_mul]
  have h3 := Finset.sum_pow_mul_eq_add_pow (2 : ℝ) 1 S
  simp only [one_pow, mul_one] at h3
  rw [h3]
  norm_num

lemma sum_three_large (σ : Setup n) (hσ : σ.Good) :
    ∑ S ∈ σ.Sfam, 3 ^ S.card * σ.large S ≤ 3 ^ σ.K / σ.ε₁ ^ 2 := by
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  have hε := hσ.hε₁
  calc ∑ S ∈ σ.Sfam, 3 ^ S.card * σ.large S
      ≤ ∑ S ∈ σ.Sfam, (3 : ℝ) ^ σ.K * (fhat σ.p σ.f S ^ 2 / σ.ε₁ ^ 2) := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Sfam_mem σ S hS).1)
          (PartA.prob_large_le σ.p hσ.hp hp1 σ.f S σ.ε₁ hε) (PartB.large_nonneg σ hσ S)
          (by positivity)
    _ = 3 ^ σ.K / σ.ε₁ ^ 2 * ∑ S ∈ σ.Sfam, fhat σ.p σ.f S ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _ => by ring)
    _ ≤ 3 ^ σ.K / σ.ε₁ ^ 2 * 1 := by
        gcongr
        calc ∑ S ∈ σ.Sfam, fhat σ.p σ.f S ^ 2 ≤ ∑ S : Finset (Fin n), fhat σ.p σ.f S ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun S _ _ => sq_nonneg _)
          _ ≤ 1 := PartA.sum_fhat_sq_le_one σ.p hσ.hp hp1 σ.f
    _ = 3 ^ σ.K / σ.ε₁ ^ 2 := mul_one _

lemma double_sum_le (σ : Setup n) (hσ : σ.Good) :
    ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam, σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ (S₁ ∩ S₂) ≤
      ∑ T : Finset (Fin n), beta σ T ^ 2 * Q σ T := by
  classical
  have hp := hσ.hp
  calc ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam, σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ (S₁ ∩ S₂)
      ≤ ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam, ∑ T : Finset (Fin n),
          (if T ⊆ S₁ then (if T ⊆ S₂ then σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ T else 0)
            else 0) := by
        refine Finset.sum_le_sum (fun S₁ _ => Finset.sum_le_sum (fun S₂ _ => ?_))
        have := Finset.single_le_sum (s := Finset.univ)
          (f := fun T => (if T ⊆ S₁ then (if T ⊆ S₂ then
            σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ T else 0) else 0))
          (fun T _ => by
            have := Q_nonneg σ hσ T
            split_ifs <;> positivity)
          (Finset.mem_univ (S₁ ∩ S₂))
        simp only [Finset.inter_subset_left, Finset.inter_subset_right, if_true] at this
        exact this
    _ = ∑ T : Finset (Fin n), ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam,
          (if T ⊆ S₁ then (if T ⊆ S₂ then σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ T else 0)
            else 0) := by
        rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
        exact Finset.sum_comm
    _ = ∑ T : Finset (Fin n), beta σ T ^ 2 * Q σ T := by
        refine Finset.sum_congr rfl (fun T _ => ?_)
        unfold beta
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun S₁ _ => ?_)
        by_cases h1 : T ⊆ S₁
        · simp only [h1, if_true]
          rw [Finset.sum_mul, Finset.sum_filter]
        · simp only [h1, if_false, Finset.sum_const_zero]

/-- (14): all cross terms together -/
theorem pair_sum_le (σ : Setup n) (hσ : σ.Good) :
    ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam.filter (fun S => S ≠ S₁),
      |expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x)| ≤ 2 ^ (8 * σ.K) * σ.δ / σ.ε₁ ^ 2 := by
  classical
  have hp := hσ.hp
  have hδ := hσ.hδ
  have hε := hσ.hε₁
  have hterm : ∀ S₁ ∈ σ.Sfam, ∀ S₂ ∈ σ.Sfam,
      0 ≤ 2 ^ (6 * σ.K) * (σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ (S₁ ∩ S₂)) := by
    intro S₁ _ S₂ _
    have := Q_nonneg σ hσ (S₁ ∩ S₂)
    positivity
  calc ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam.filter (fun S => S ≠ S₁),
        |expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x)|
      ≤ ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam.filter (fun S => S ≠ S₁),
          2 ^ (6 * σ.K) * (σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ (S₁ ∩ S₂)) := by
        refine Finset.sum_le_sum (fun S₁ hS₁ => Finset.sum_le_sum (fun S₂ hS₂ => ?_))
        obtain ⟨hS₂, hne⟩ := Finset.mem_filter.1 hS₂
        exact pair_bound σ hσ S₁ S₂ (Ne.symm hne) (Sfam_mem σ S₁ hS₁).1 (Sfam_mem σ S₂ hS₂).1
    _ ≤ ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam,
          2 ^ (6 * σ.K) * (σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ (S₁ ∩ S₂)) := by
        refine Finset.sum_le_sum (fun S₁ hS₁ => ?_)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S₂ hS₂ _ => hterm S₁ hS₁ S₂ hS₂)
    _ = 2 ^ (6 * σ.K) * ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam,
          σ.p ^ S₁.card * σ.p ^ S₂.card * Q σ (S₁ ∩ S₂) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S₁ _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ 2 ^ (6 * σ.K) * ∑ T : Finset (Fin n), beta σ T ^ 2 * Q σ T :=
        mul_le_mul_of_nonneg_left (double_sum_le σ hσ) (by positivity)
    _ ≤ 2 ^ (6 * σ.K) * ∑ T : Finset (Fin n), σ.δ * (σ.b T * 2 ^ T.card) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun T _ => ?_)) (by positivity)
        rw [← mul_assoc]
        exact beta_sq_Q_le σ hσ T
    _ = 2 ^ (6 * σ.K) * σ.δ * ∑ S ∈ σ.Sfam, 3 ^ S.card * σ.large S := by
        rw [← Finset.mul_sum, sum_b_two, mul_assoc]
    _ ≤ 2 ^ (6 * σ.K) * σ.δ * (3 ^ σ.K / σ.ε₁ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_three_large σ hσ) (by positivity)
    _ ≤ 2 ^ (6 * σ.K) * σ.δ * (2 ^ (2 * σ.K) / σ.ε₁ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [pow_mul]
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = 2 ^ (8 * σ.K) * σ.δ / σ.ε₁ ^ 2 := by
        rw [show 8 * σ.K = 6 * σ.K + 2 * σ.K by ring, pow_add]
        ring

end NarrowDNF.Dev.Hat.PartC
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias pair_sum_le := NarrowDNF.Dev.Hat.PartC.pair_sum_le

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem gt_measurable (σ : Setup n) (x y : Cube n) (h : atom σ.J x = atom σ.J y) :
    σ.gt x = σ.gt y := by
  unfold Setup.gt
  refine Finset.sum_congr rfl (fun S _ => ?_)
  unfold Setup.Ft
  exact cexp_congr _ _ _ _ _ (atom_restrictJ_congr σ.J S x y h)

lemma Ft_update (σ : Setup n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) (x : Cube n)
    (b : Bool) : σ.Ft S (Function.update x i b) = σ.Ft S x := by
  unfold Setup.Ft
  refine cexp_congr _ _ _ _ _ (atom_restrictJ_dependsOn σ.J S _ _ (fun k hk => ?_))
  have : k ≠ i := fun h => hi (h ▸ hk)
  simp [Function.update_of_ne this]

lemma FS_update (p : ℝ) (f : Cube n → Bool) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (x : Cube n) (b : Bool) : FS p f S (Function.update x i b) = FS p f S x := by
  refine FS_dependsOn p f S _ _ (fun k hk => ?_)
  have : k ≠ i := fun h => hi (h ▸ hk)
  simp [Function.update_of_ne this]

theorem cross_eq (σ : Setup n) (hσ : σ.Good) (S₁ S₂ : Finset (Fin n)) (hne : S₁ ≠ S₂)
    (hcard : S₁.card = S₂.card) :
    expect σ.p (fun x => (FS σ.p σ.f S₁ x - σ.Ft S₁ x) * (FS σ.p σ.f S₂ x - σ.Ft S₂ x)) =
      expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x) := by
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  have hi : ∃ i ∈ S₁, i ∉ S₂ := by
    by_contra hc
    push_neg at hc
    exact hne (Finset.eq_of_subset_of_card_le hc hcard.ge)
  have hj : ∃ j ∈ S₂, j ∉ S₁ := by
    by_contra hc
    push_neg at hc
    exact hne (Finset.eq_of_subset_of_card_le hc hcard.le).symm
  obtain ⟨i, hi1, hi2⟩ := hi
  obtain ⟨j, hj2, hj1⟩ := hj
  have e1 : expect σ.p (fun x => FS σ.p σ.f S₁ x * FS σ.p σ.f S₂ x) = 0 :=
    expect_mul_eq_zero_of_mean_zero σ.p i _ _
      (FS_mean_zero σ.p hσ.hp hp1 σ.f S₁ i hi1)
      (fun x b => FS_update σ.p σ.f S₂ i hi2 x b)
  have e2 : expect σ.p (fun x => FS σ.p σ.f S₁ x * σ.Ft S₂ x) = 0 :=
    expect_mul_eq_zero_of_mean_zero σ.p i _ _
      (FS_mean_zero σ.p hσ.hp hp1 σ.f S₁ i hi1)
      (fun x b => Ft_update σ S₂ i hi2 x b)
  have e3 : expect σ.p (fun x => σ.Ft S₁ x * FS σ.p σ.f S₂ x) = 0 := by
    have := expect_mul_eq_zero_of_mean_zero σ.p j _ _
      (FS_mean_zero σ.p hσ.hp hp1 σ.f S₂ j hj2)
      (fun x b => Ft_update σ S₁ j hj1 x b)
    rw [← this]
    congr 1; funext x; ring
  have : (fun x => (FS σ.p σ.f S₁ x - σ.Ft S₁ x) * (FS σ.p σ.f S₂ x - σ.Ft S₂ x)) =
      fun x => ((FS σ.p σ.f S₁ x * FS σ.p σ.f S₂ x - FS σ.p σ.f S₁ x * σ.Ft S₂ x) -
        σ.Ft S₁ x * FS σ.p σ.f S₂ x) + σ.Ft S₁ x * σ.Ft S₂ x := by
    funext x; ring
  rw [this, expect_add, expect_sub, expect_sub, e1, e2, e3]
  ring

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias cross_eq := NarrowDNF.Dev.Hat.PartB.cross_eq

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartD
open NarrowDNF.Approx NarrowDNF.Dev.Hat NarrowDNF.Dev.Hat.PartA
variable {n : ℕ}
/-- one level: `E[(Σ_{S∈L} D_S)²] ≤ Σ_{S₁∈L} (E[D₁²] + Σ_{S₂ ≠ S₁} |E[F̃₁F̃₂]|)` -/
lemma level_le (σ : Setup n) (hσ : σ.Good) (r : ℕ) :
    expect σ.p (fun x => (∑ S ∈ σ.Sfam.filter (fun S => S.card = r),
        (FS σ.p σ.f S x - σ.Ft S x)) ^ 2) ≤
      ∑ S₁ ∈ σ.Sfam.filter (fun S => S.card = r),
        (expect σ.p (fun x => (FS σ.p σ.f S₁ x - σ.Ft S₁ x) ^ 2) +
          ∑ S₂ ∈ σ.Sfam.filter (fun S => S ≠ S₁),
            |expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x)|) := by
  set L := σ.Sfam.filter (fun S => S.card = r) with hL
  set D : Finset (Fin n) → Cube n → ℝ := fun S x => FS σ.p σ.f S x - σ.Ft S x with hD
  have h1 : expect σ.p (fun x => (∑ S ∈ L, D S x) ^ 2) =
      ∑ S₁ ∈ L, ∑ S₂ ∈ L, expect σ.p (fun x => D S₁ x * D S₂ x) := by
    rw [expect_congr σ.p _ (fun x => ∑ S₁ ∈ L, ∑ S₂ ∈ L, D S₁ x * D S₂ x)
      (fun x => by rw [sq, Finset.sum_mul_sum])]
    rw [expect_sum]
    exact Finset.sum_congr rfl (fun S₁ _ => expect_sum _ _ _)
  change expect σ.p (fun x => (∑ S ∈ L, D S x) ^ 2) ≤ _
  rw [h1]
  refine Finset.sum_le_sum (fun S₁ hS₁ => ?_)
  rw [← Finset.add_sum_erase L _ hS₁]
  have hsq : expect σ.p (fun x => D S₁ x * D S₁ x) =
      expect σ.p (fun x => (FS σ.p σ.f S₁ x - σ.Ft S₁ x) ^ 2) :=
    expect_congr σ.p _ _ (fun x => by simp only [hD]; ring)
  rw [hsq]
  refine add_le_add le_rfl ?_
  calc ∑ S₂ ∈ L.erase S₁, expect σ.p (fun x => D S₁ x * D S₂ x)
      = ∑ S₂ ∈ L.erase S₁, expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x) := by
        refine Finset.sum_congr rfl (fun S₂ hS₂ => ?_)
        have hne : S₂ ≠ S₁ := Finset.ne_of_mem_erase hS₂
        have hS₂L := Finset.mem_of_mem_erase hS₂
        have c1 := (Finset.mem_filter.1 hS₁).2
        have c2 := (Finset.mem_filter.1 hS₂L).2
        exact cross_eq σ hσ S₁ S₂ (Ne.symm hne) (c1.trans c2.symm)
    _ ≤ ∑ S₂ ∈ L.erase S₁, |expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x)| :=
        Finset.sum_le_sum (fun _ _ => le_abs_self _)
    _ ≤ ∑ S₂ ∈ σ.Sfam.filter (fun S => S ≠ S₁),
          |expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x)| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
        intro S₂ hS₂
        exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 (Finset.mem_of_mem_erase hS₂)).1,
          Finset.ne_of_mem_erase hS₂⟩

/-- assembling (13) and (14) through the level decomposition -/
theorem g_sub_gt_le (σ : Setup n) (hσ : σ.Good) :
    expect σ.p (fun x => (σ.g x - σ.gt x) ^ 2) ≤
      (σ.K + 1) * (∑ S ∈ σ.Sfam, expect σ.p (fun x => (FS σ.p σ.f S x - σ.Ft S x) ^ 2) +
        2 ^ (8 * σ.K) * σ.δ / σ.ε₁ ^ 2) := by
  have hp0 : 0 ≤ σ.p := hσ.hp.le
  have hp1 : σ.p ≤ 1 := by linarith [hσ.hp_half]
  set D : Finset (Fin n) → Cube n → ℝ := fun S x => FS σ.p σ.f S x - σ.Ft S x with hD
  have hmaps : ∀ S ∈ σ.Sfam, S.card ∈ Finset.range (σ.K + 1) := by
    intro S hS
    unfold Setup.Sfam at hS
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.mem_filter.1 hS).2.1)
  -- pointwise level decomposition and Cauchy–Schwarz
  have hpt : ∀ x, (σ.g x - σ.gt x) ^ 2 ≤
      (σ.K + 1 : ℝ) * ∑ r ∈ Finset.range (σ.K + 1),
        (∑ S ∈ σ.Sfam.filter (fun S => S.card = r), D S x) ^ 2 := by
    intro x
    have hsplit : σ.g x - σ.gt x = ∑ r ∈ Finset.range (σ.K + 1),
        ∑ S ∈ σ.Sfam.filter (fun S => S.card = r), D S x := by
      rw [Finset.sum_fiberwise_of_maps_to hmaps]
      simp only [Setup.g, Setup.gt, hD, Finset.sum_sub_distrib]
    rw [hsplit]
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range (σ.K + 1))
      (f := fun r => ∑ S ∈ σ.Sfam.filter (fun S => S.card = r), D S x)
    simpa [Finset.card_range] using this
  have hK : (0 : ℝ) ≤ σ.K + 1 := by positivity
  calc expect σ.p (fun x => (σ.g x - σ.gt x) ^ 2)
      ≤ expect σ.p (fun x => (σ.K + 1 : ℝ) * ∑ r ∈ Finset.range (σ.K + 1),
          (∑ S ∈ σ.Sfam.filter (fun S => S.card = r), D S x) ^ 2) :=
        expect_mono σ.p hp0 hp1 _ _ hpt
    _ = (σ.K + 1) * ∑ r ∈ Finset.range (σ.K + 1), expect σ.p (fun x =>
          (∑ S ∈ σ.Sfam.filter (fun S => S.card = r), D S x) ^ 2) := by
        rw [expect_smul, expect_sum]
    _ ≤ (σ.K + 1) * ∑ r ∈ Finset.range (σ.K + 1),
          ∑ S₁ ∈ σ.Sfam.filter (fun S => S.card = r),
            (expect σ.p (fun x => (FS σ.p σ.f S₁ x - σ.Ft S₁ x) ^ 2) +
              ∑ S₂ ∈ σ.Sfam.filter (fun S => S ≠ S₁),
                |expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x)|) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r _ => ?_)) hK
        exact level_le σ hσ r
    _ = (σ.K + 1) * (∑ S ∈ σ.Sfam, expect σ.p (fun x => (FS σ.p σ.f S x - σ.Ft S x) ^ 2) +
          ∑ S₁ ∈ σ.Sfam, ∑ S₂ ∈ σ.Sfam.filter (fun S => S ≠ S₁),
            |expect σ.p (fun x => σ.Ft S₁ x * σ.Ft S₂ x)|) := by
        rw [Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_add_distrib]
    _ ≤ (σ.K + 1) * (∑ S ∈ σ.Sfam, expect σ.p (fun x => (FS σ.p σ.f S x - σ.Ft S x) ^ 2) +
          2 ^ (8 * σ.K) * σ.δ / σ.ε₁ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl (pair_sum_le σ hσ)) hK

end NarrowDNF.Dev.Hat.PartD
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias g_sub_gt_le := NarrowDNF.Dev.Hat.PartD.g_sub_gt_le

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem f_sub_g (σ : Setup n) (hσ : σ.Good) :
    expect σ.p (fun x => (ind σ.f x - σ.g x) ^ 2) =
      ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam), fhat σ.p σ.f S ^ 2 := by
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  have : ∀ x, ind σ.f x - σ.g x =
      ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam), FS σ.p σ.f S x := by
    intro x
    rw [fourier_inversion σ.p hσ.hp hp1 σ.f x, Setup.g,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S => S ∈ σ.Sfam)]
    have : Finset.univ.filter (fun S => S ∈ σ.Sfam) = σ.Sfam := by ext; simp
    rw [this]
    ring
  simp only [this]
  exact expect_sq_sum_FS σ.p hσ.hp hp1 σ.f _

lemma J_cell (σ : Setup n) (S : Finset (Fin n)) (x y : Cube n)
    (h : atom (restrictJ σ.J S) x = atom (restrictJ σ.J S) y) :
    σ.J S (fun i => x i) = true ↔ σ.J S (fun i => y i) = true := by
  constructor
  · intro hx
    have := eq_on_of_atom_restrictJ σ.J S S (Finset.Subset.refl S) x y hx h.symm
    rw [act_congr σ.J y x S this] at *
    exact hx
  · intro hy
    have := eq_on_of_atom_restrictJ σ.J S S (Finset.Subset.refl S) y x hy h
    rw [act_congr σ.J x y S this] at *
    exact hy

lemma Ft_self (σ : Setup n) (hσ : σ.Good) (S : Finset (Fin n)) (x : Cube n)
    (hx : σ.J S (fun i => x i) = true) : σ.Ft S x = FS σ.p σ.f S x := by
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  unfold Setup.Ft
  exact cexp_eq_self σ.p hσ.hp hp1 _ _ x (fun y hy =>
    FS_dependsOn σ.p σ.f S y x (eq_on_of_atom_restrictJ σ.J S S (Finset.Subset.refl S) x y hx hy))

/-- (13): diagonal terms -/
theorem diag_le (σ : Setup n) (hσ : σ.Good) (S : Finset (Fin n)) (hS : S ∈ σ.Sfam) :
    expect σ.p (fun x => (FS σ.p σ.f S x - σ.Ft S x) ^ 2) ≤
      expect σ.p (fun x => if |FS σ.p σ.f S x| ≤ σ.ε₁ then FS σ.p σ.f S x ^ 2 else 0) := by
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  set F : Cube n → ℝ := FS σ.p σ.f S with hF
  set G : Cube n → ℝ := σ.Ft S with hG
  set U : Cube n → ℝ := fun x => if σ.J S (fun i => x i) = true then 0 else 1 with hU
  have hpt : ∀ x, (F x - G x) ^ 2 =
      (U x * F x ^ 2 + U x * G x ^ 2) - 2 * (F x * (U x * G x)) := by
    intro x
    by_cases hx : σ.J S (fun i => x i) = true
    · have : G x = F x := Ft_self σ hσ S x hx
      simp only [hU, hx, if_true, this]; ring
    · simp only [hU, hx, Bool.false_eq_true, if_false]; ring
  have hcross : expect σ.p (fun x => F x * (U x * G x)) =
      expect σ.p (fun x => U x * G x ^ 2) := by
    have := expect_cexp_mul σ.p hσ.hp hp1 (atom (restrictJ σ.J S)) F (fun x => U x * G x)
      (fun x y hxy => by
        have h1 : G x = G y := cexp_congr _ _ _ _ _ hxy
        have h2 := J_cell σ S x y hxy
        simp only [hU, h1]
        by_cases hx : σ.J S (fun i => x i) = true
        · rw [if_pos hx, if_pos (h2.1 hx)]
        · rw [if_neg hx, if_neg (fun hy => hx (h2.2 hy))])
    rw [← this]
    congr 1; funext x
    show G x * (U x * G x) = U x * G x ^ 2
    ring
  have h1 : expect σ.p (fun x => (F x - G x) ^ 2) =
      expect σ.p (fun x => U x * F x ^ 2) - expect σ.p (fun x => U x * G x ^ 2) := by
    rw [funext hpt, expect_sub, expect_add, expect_const_mul, hcross]
    ring
  rw [h1]
  have h2 : 0 ≤ expect σ.p (fun x => U x * G x ^ 2) :=
    expect_nonneg _ hσ.hp.le hp1.le _ (fun x => by
      simp only [hU]; split_ifs <;> positivity)
  have h3 : expect σ.p (fun x => U x * F x ^ 2) ≤
      expect σ.p (fun x => if |F x| ≤ σ.ε₁ then F x ^ 2 else 0) := by
    refine expect_mono _ hσ.hp.le hp1.le _ _ (fun x => ?_)
    by_cases hx : σ.J S (fun i => x i) = true
    · simp only [hU, hx, if_true, zero_mul]; split_ifs <;> positivity
    · have : |F x| ≤ σ.ε₁ := by
        by_contra hc
        exact hx (J_of_large σ hσ S hS x (le_of_lt (lt_of_not_ge hc)))
      simp only [hU, hx, this, if_true, Bool.false_eq_true, if_false, one_mul]
      exact le_refl _
  linarith

lemma Sfam_card (σ : Setup n) (S : Finset (Fin n)) (hS : S ∈ σ.Sfam) : S.card ≤ σ.K := by
  classical
  unfold Setup.Sfam at hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  exact hS.1

lemma prob_J_le (σ : Setup n) (hσ : σ.Good) (T : Finset (Fin n)) :
    prob σ.p (fun x : Cube n => σ.J T (fun i => x i) = true) ≤ σ.b T / σ.δ * 2 ^ T.card := by
  classical
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  rw [← expect_inv_mu σ.p hσ.hp hp1 T, ← expect_const_mul]
  unfold prob FriedgutCoalition.wProb expect
  refine Finset.sum_le_sum (fun x _ => ?_)
  have hμ := mu_pos σ.p hσ.hp hp1 T x
  have hw := w_nonneg σ.p hσ.hp.le hp1.le x
  have hb := b_nonneg σ hσ T
  have hδ := hσ.hδ
  split_ifs with hJ
  · have h1 := ((J_apply σ T x).1 hJ).2
    have h2 : 1 ≤ σ.b T / σ.δ * (1 / mu σ.p T x) := by
      rw [div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
      linarith
    nlinarith
  · exact mul_nonneg hw (by positivity)

lemma prob_J_zero (σ : Setup n) (T : Finset (Fin n)) (hT : σ.K < T.card) :
    prob σ.p (fun x : Cube n => σ.J T (fun i => x i) = true) = 0 := by
  classical
  unfold prob FriedgutCoalition.wProb
  refine Finset.sum_eq_zero (fun x _ => ?_)
  rw [if_neg]
  intro h
  have := ((J_apply σ T x).1 h).1
  omega

/-- load bound: `Λ ≤ K 3^K / (δ ε₁²)` -/
theorem load_J_le (σ : Setup n) (hσ : σ.Good) :
    load σ.p σ.J ≤ σ.K * 3 ^ σ.K / (σ.δ * σ.ε₁ ^ 2) := by
  classical
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  have hδ := hσ.hδ
  have hε := hσ.hε₁
  have step1 : ∀ T : Finset (Fin n), (T.card : ℝ) *
      prob σ.p (fun x : Cube n => σ.J T (fun i => x i) = true) ≤
        σ.K * (σ.b T / σ.δ * 2 ^ T.card) := by
    intro T
    by_cases hT : T.card ≤ σ.K
    · have hprob0 : 0 ≤ prob σ.p (fun x : Cube n => σ.J T (fun i => x i) = true) := by
        unfold prob FriedgutCoalition.wProb
        exact Finset.sum_nonneg (fun x _ => by
          split_ifs
          · exact w_nonneg σ.p hσ.hp.le hp1.le x
          · exact le_refl 0)
      have hb := b_nonneg σ hσ T
      exact mul_le_mul (by exact_mod_cast hT) (prob_J_le σ hσ T) hprob0 (by positivity)
    · rw [prob_J_zero σ T (by omega), mul_zero]
      have := b_nonneg σ hσ T
      positivity
  have step2 : ∑ T : Finset (Fin n), σ.b T * 2 ^ T.card =
      ∑ S ∈ σ.Sfam, 3 ^ S.card * σ.large S := by
    unfold Setup.b
    simp_rw [Finset.sum_filter, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have : ∀ T : Finset (Fin n), (if T ⊆ S then σ.large S else 0) * 2 ^ T.card =
        if T ∈ S.powerset then 2 ^ T.card * σ.large S else 0 := by
      intro T
      by_cases hT : T ⊆ S
      · rw [if_pos hT, if_pos (Finset.mem_powerset.2 hT)]; ring
      · rw [if_neg hT, if_neg (fun h => hT (Finset.mem_powerset.1 h))]; ring
    rw [Finset.sum_congr rfl (fun T _ => this T), ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter, ← Finset.sum_mul]
    have h3 := Finset.sum_pow_mul_eq_add_pow (2 : ℝ) 1 S
    simp only [one_pow, mul_one] at h3
    rw [h3]
    norm_num
  have step3 : ∑ S ∈ σ.Sfam, 3 ^ S.card * σ.large S ≤ 3 ^ σ.K / σ.ε₁ ^ 2 := by
    calc ∑ S ∈ σ.Sfam, 3 ^ S.card * σ.large S
        ≤ ∑ S ∈ σ.Sfam, (3 : ℝ) ^ σ.K * (fhat σ.p σ.f S ^ 2 / σ.ε₁ ^ 2) := by
          refine Finset.sum_le_sum (fun S hS => ?_)
          exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Sfam_card σ S hS))
            (prob_large_le σ.p hσ.hp hp1 σ.f S σ.ε₁ hε) (large_nonneg σ hσ S) (by positivity)
      _ = 3 ^ σ.K / σ.ε₁ ^ 2 * ∑ S ∈ σ.Sfam, fhat σ.p σ.f S ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun S _ => by ring)
      _ ≤ 3 ^ σ.K / σ.ε₁ ^ 2 * 1 := by
          gcongr
          calc ∑ S ∈ σ.Sfam, fhat σ.p σ.f S ^ 2 ≤ ∑ S : Finset (Fin n), fhat σ.p σ.f S ^ 2 :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                  (fun S _ _ => sq_nonneg _)
            _ ≤ 1 := sum_fhat_sq_le_one σ.p hσ.hp hp1 σ.f
      _ = 3 ^ σ.K / σ.ε₁ ^ 2 := mul_one _
  unfold load
  calc ∑ T : Finset (Fin n), (T.card : ℝ) *
        prob σ.p (fun x : Cube n => σ.J T (fun i => x i) = true)
      ≤ ∑ T : Finset (Fin n), (σ.K : ℝ) * (σ.b T / σ.δ * 2 ^ T.card) :=
        Finset.sum_le_sum (fun T _ => step1 T)
    _ = σ.K / σ.δ * ∑ T : Finset (Fin n), σ.b T * 2 ^ T.card := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun T _ => by ring)
    _ ≤ σ.K / σ.δ * (3 ^ σ.K / σ.ε₁ ^ 2) := by
        rw [step2]
        gcongr
    _ = σ.K * 3 ^ σ.K / (σ.δ * σ.ε₁ ^ 2) := by
        field_simp

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
/-! ## rounding and the zero case -/
theorem error_round_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : Cube n → Bool) (G : Cube n → ℝ) :
    error p f (fun x => decide (1 / 2 < G x)) ≤ 4 * expect p (fun x => (ind f x - G x) ^ 2) := by
  classical
  rw [← expect_smul, expect_def]
  unfold error prob FriedgutCoalition.wProb
  refine Finset.sum_le_sum (fun x _ => ?_)
  have hw := w_nonneg p hp hp1 x
  split_ifs with h
  · simp only at h
    have key : 1 ≤ 4 * (ind f x - G x) ^ 2 := by
      unfold ind
      cases hf : f x
      · rw [hf] at h
        have : 1 / 2 < G x := by
          by_contra hc; exact h (decide_eq_false hc).symm
        simp only [Bool.false_eq_true, if_false]
        nlinarith
      · rw [hf] at h
        have : G x ≤ 1 / 2 := by
          by_contra hc; exact h (decide_eq_true (lt_of_not_ge hc)).symm
        simp only [if_true]
        nlinarith
    calc (∏ i, FriedgutCoalition.bern p (x i)) = w p x * 1 := by rw [mul_one]; rfl
      _ ≤ w p x * (4 * (ind f x - G x) ^ 2) := mul_le_mul_of_nonneg_left key hw
  · exact mul_nonneg hw (by positivity)

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias error_round_le := NarrowDNF.Dev.Hat.PartA.error_round_le

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem expect_sq_sub_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (A B G : Cube n → ℝ) :
    expect p (fun x => (A x - G x) ^ 2) ≤
      2 * expect p (fun x => (A x - B x) ^ 2) + 2 * expect p (fun x => (B x - G x) ^ 2) := by
  rw [← expect_smul, ← expect_smul, ← expect_add]
  refine expect_mono p hp hp1 _ _ (fun x => ?_)
  nlinarith [sq_nonneg (A x - 2 * B x + G x)]

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias expect_sq_sub_le := NarrowDNF.Dev.Hat.PartA.expect_sq_sub_le

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
theorem lemma_2_1_zero {n : ℕ} (p a : ℝ) (f : Cube n → Bool)
    (hp : 0 < p) (hp_half : p ≤ 1 / 2) (ha : 0 < a) (ha_one : a ≤ 1)
    (h0 : FriedgutCoalition.totalPInfl p f ≤ 0) :
    ∃ (J : ActivationFamily n) (h : Cube n → Bool),
      IncreasingActivations J ∧ error p f h ≤ a ∧ AdaptiveMeasurable J h ∧
      arity J ≤ 0 ∧ load p J ≤ 1 := by
  classical
  have hp1 : p < 1 := by linarith
  rw [totalPInfl_eq p hp hp1 f] at h0
  have hnn : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))), 0 ≤ (S.card : ℝ) * fhat p f S ^ 2 :=
    fun S _ => by positivity
  have hsum : ∑ S : Finset (Fin n), (S.card : ℝ) * fhat p f S ^ 2 = 0 :=
    le_antisymm (by linarith) (Finset.sum_nonneg hnn)
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at hsum
  have hz : ∀ S : Finset (Fin n), S ≠ ∅ → fhat p f S = 0 := by
    intro S hS
    have h1 := hsum S (Finset.mem_univ S)
    have hc : (0 : ℝ) < S.card := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    have : fhat p f S ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hc.ne'
      · exact h
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hconst : ∀ x : Cube n, ind f x = fhat p f ∅ := by
    intro x
    rw [fourier_inversion p hp hp1 f x, Finset.sum_eq_single (∅ : Finset (Fin n))]
    · simp [FS, chi]
    · intro S _ hS; simp [FS, hz S hS]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hfc : ∀ x y : Cube n, f x = f y := by
    intro x y
    have h := (hconst x).trans (hconst y).symm
    unfold ind at h
    cases hx : f x <;> cases hy : f y <;> simp_all
  refine ⟨fun _ _ => false, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro S z₁ z₂ _; exact le_rfl
  · unfold error prob FriedgutCoalition.wProb
    simp only [ne_eq, not_true_eq_false, if_false, Finset.sum_const_zero]
    exact ha.le
  · intro x y _; exact hfc x y
  · unfold arity
    simp
  · unfold load prob FriedgutCoalition.wProb
    simp

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias lemma_2_1_zero := NarrowDNF.Dev.Hat.PartA.lemma_2_1_zero

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartA
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
/-! ## numerics -/
lemma exp_seven_ge : (768 : ℝ) ≤ Real.exp 7 := by
  have h1 : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2.7 : ℝ) ≤ Real.exp 1 := le_of_lt (lt_trans (by norm_num) Real.exp_one_gt_d9)
  rw [h1]
  calc (768 : ℝ) ≤ 2.7 ^ 7 := by norm_num
    _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) h2 7

theorem numerics (C : ℕ) (hC : 1 ≤ C) (a : ℝ) (ha : 0 < a) (ha_one : a ≤ 1) :
    let ε₀ : ℝ := a / 1000
    let k : ℝ := C / ε₀
    let K : ℕ := ⌊k⌋₊
    let ε₁ : ℝ := Real.exp (-(1000 * k ^ 2))
    let δ : ℝ := ε₀ * ε₁ ^ 2 / ((K + 1) * 2 ^ (8 * K))
    0 < ε₁ ∧ 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ k ∧ (K : ℝ) ≤ k ∧ k < K + 1 ∧
      K ≤ ⌈(10 : ℝ) ^ 3 * (C : ℝ) / a⌉₊ ∧
      K * 3 ^ K / (δ * ε₁ ^ 2) ≤ Real.exp ((10 : ℝ) ^ 10 * a⁻¹ ^ 2 * (C : ℝ) ^ 2) ∧
      4 * (2 * (ε₀ / 2 + ε₀ / k) + 2 * ((K + 1) * (ε₀ / k + 2 ^ (8 * K) * δ / ε₁ ^ 2))) ≤ a := by
  intro ε₀ k K ε₁ δ
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀1 : ε₀ ≤ 1 / 1000 := by simp only [ε₀]; linarith
  have hkε : k * ε₀ = C := by simp only [k]; field_simp
  have hk1 : 1 ≤ k := by
    by_contra h
    push Not at h
    nlinarith
  have hk0 : 0 < k := by linarith
  have hε₁ : 0 < ε₁ := Real.exp_pos _
  have hε₁1 : ε₁ ≤ 1 := by
    simp only [ε₁]; rw [Real.exp_le_one_iff]; nlinarith
  have hKk : (K : ℝ) ≤ k := Nat.floor_le hk0.le
  have hkK : k < K + 1 := Nat.lt_floor_add_one k
  have hden : (1 : ℝ) ≤ (K + 1) * 2 ^ (8 * K) := by
    have : (1 : ℝ) ≤ 2 ^ (8 * K) := one_le_pow₀ (by norm_num)
    nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hδ : 0 < δ := by positivity
  refine ⟨hε₁, hδ, ?_, hk1, hKk, hkK, ?_, ?_, ?_⟩
  · simp only [δ]
    rw [div_le_one (by positivity)]
    have : ε₁ ^ 2 ≤ 1 := pow_le_one₀ hε₁.le hε₁1
    nlinarith
  · have : k = (10 : ℝ) ^ 3 * (C : ℝ) / a := by simp only [k, ε₀]; field_simp; norm_num
    rw [← this]
    exact Nat.floor_le_ceil k
  · have hB : (10 : ℝ) ^ 10 * a⁻¹ ^ 2 * (C : ℝ) ^ 2 = 6000 * k ^ 2 + 4000 * k ^ 2 := by
      simp only [k, ε₀]; field_simp; norm_num
    have hE4 : ε₁ ^ 2 * ε₁ ^ 2 * Real.exp (4000 * k ^ 2) = 1 := by
      simp only [ε₁]
      rw [← pow_add, ← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
      ring_nf
    rw [hB, Real.exp_add, div_le_iff₀ (by positivity)]
    have hδe : Real.exp (6000 * k ^ 2) * Real.exp (4000 * k ^ 2) * (δ * ε₁ ^ 2) =
        Real.exp (6000 * k ^ 2) * ε₀ / ((K + 1) * 2 ^ (8 * K)) := by
      simp only [δ]
      rw [show Real.exp (6000 * k ^ 2) * Real.exp (4000 * k ^ 2) *
          (ε₀ * ε₁ ^ 2 / ((K + 1) * 2 ^ (8 * K)) * ε₁ ^ 2) =
          Real.exp (6000 * k ^ 2) * ε₀ * (ε₁ ^ 2 * ε₁ ^ 2 * Real.exp (4000 * k ^ 2)) /
            ((K + 1) * 2 ^ (8 * K)) by ring, hE4, mul_one]
    rw [hδe, le_div_iff₀ (by positivity)]
    -- the chain
    have h768 : (3 : ℝ) ^ K * 2 ^ (8 * K) ≤ Real.exp (7 * k) := by
      calc (3 : ℝ) ^ K * 2 ^ (8 * K) = 768 ^ K := by
            rw [pow_mul, ← mul_pow]; norm_num
        _ ≤ Real.exp 7 ^ K := pow_le_pow_left₀ (by norm_num) exp_seven_ge K
        _ = Real.exp (7 * K) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (7 * k) := Real.exp_le_exp.mpr (by linarith)
    have hek := Real.add_one_le_exp k
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have h1 : (K : ℝ) * (K + 1) ≤ k * (k + 1) := by nlinarith
    have h2 : k * (k + 1) * k ≤ Real.exp k ^ 3 := by
      have a1 : k ≤ Real.exp k := by linarith
      have a2 : k + 1 ≤ Real.exp k := hek
      calc k * (k + 1) * k ≤ Real.exp k * Real.exp k * Real.exp k := by
            gcongr
        _ = Real.exp k ^ 3 := by ring
    have h3 : Real.exp k ^ 3 * Real.exp (7 * k) ≤ Real.exp (6000 * k ^ 2) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith
    have hpos7 := Real.exp_pos (7 * k)
    calc (K : ℝ) * 3 ^ K * ((K + 1) * 2 ^ (8 * K))
        = (K * (K + 1)) * (3 ^ K * 2 ^ (8 * K)) := by ring
      _ ≤ (k * (k + 1)) * Real.exp (7 * k) := by
          apply mul_le_mul h1 h768 (by positivity) (by positivity)
      _ ≤ (k * (k + 1)) * Real.exp (7 * k) * (k * ε₀) := by
          rw [hkε]
          exact le_mul_of_one_le_right (by positivity) hC1
      _ = (k * (k + 1) * k) * Real.exp (7 * k) * ε₀ := by ring
      _ ≤ Real.exp k ^ 3 * Real.exp (7 * k) * ε₀ := by gcongr
      _ ≤ Real.exp (6000 * k ^ 2) * ε₀ := by gcongr
  · have h1 : 2 ^ (8 * K) * δ / ε₁ ^ 2 = ε₀ / (K + 1) := by
      simp only [δ]
      field_simp
    rw [h1]
    have hK1 : (0 : ℝ) < K + 1 := by positivity
    have h2 : (K + 1) * (ε₀ / k + ε₀ / (K + 1)) ≤ 3 * ε₀ := by
      rw [mul_add, mul_div_cancel₀ _ hK1.ne']
      have : (K + 1) * (ε₀ / k) ≤ 2 * ε₀ := by
        rw [mul_div_assoc', div_le_iff₀ hk0]
        nlinarith
      linarith
    have h3 : ε₀ / k ≤ ε₀ := div_le_self hε₀.le hk1
    have : ε₀ = a / 1000 := rfl
    nlinarith

end NarrowDNF.Dev.Hat.PartA
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias numerics := NarrowDNF.Dev.Hat.PartA.numerics

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat.PartB
open NarrowDNF.Approx NarrowDNF.Dev.Hat
variable {n : ℕ}
lemma term_not_Sfam (σ : Setup n) (hσ : σ.Good) (S : Finset (Fin n)) (hS : S ∉ σ.Sfam)
    (hK : S.card ≤ σ.K) :
    expect σ.p (fun x => if |FS σ.p σ.f S x| ≤ σ.ε₁ then FS σ.p σ.f S x ^ 2 else 0) =
      fhat σ.p σ.f S ^ 2 := by
  classical
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  have hall : ∀ x, |FS σ.p σ.f S x| ≤ σ.ε₁ := by
    intro x
    by_contra hc
    apply hS
    unfold Setup.Sfam
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hK, x, lt_of_not_ge hc⟩
  have h1 := expect_sq_sum_FS σ.p hσ.hp hp1 σ.f {S}
  simp only [Finset.sum_singleton] at h1
  rw [← h1]
  congr 1
  funext x
  rw [if_pos (hall x)]

lemma split_low (σ : Setup n) (hσ : σ.Good) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ σ.K),
        expect σ.p (fun x => if |FS σ.p σ.f S x| ≤ σ.ε₁ then FS σ.p σ.f S x ^ 2 else 0) =
      ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam ∧ S.card ≤ σ.K), fhat σ.p σ.f S ^ 2 +
      ∑ S ∈ σ.Sfam,
        expect σ.p (fun x => if |FS σ.p σ.f S x| ≤ σ.ε₁ then FS σ.p σ.f S x ^ 2 else 0) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun S => S ∈ σ.Sfam), add_comm]
  congr 1
  · rw [Finset.filter_filter]
    refine Finset.sum_congr ?_ (fun S hS => ?_)
    · ext S; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact term_not_Sfam σ hσ S hS.1 hS.2
  · rw [Finset.filter_filter]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨Sfam_card σ S h, h⟩

lemma high_le (σ : Setup n) (hσ : σ.Good) (k : ℝ) (hk : 0 < k) (hkK : k < σ.K + 1) (C : ℝ)
    (hIC : FriedgutCoalition.totalPInfl σ.p σ.f ≤ C) :
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ S.card ≤ σ.K),
      fhat σ.p σ.f S ^ 2 ≤ C / (2 * k) := by
  have hp1 : σ.p < 1 := by linarith [hσ.hp_half]
  have hT := totalPInfl_eq σ.p hσ.hp hp1 σ.f
  calc ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ S.card ≤ σ.K), fhat σ.p σ.f S ^ 2
      ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ S.card ≤ σ.K),
          (S.card : ℝ) / k * fhat σ.p σ.f S ^ 2 := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hS
        have : (σ.K : ℝ) + 1 ≤ S.card := by exact_mod_cast hS
        have h1 : 1 ≤ (S.card : ℝ) / k := by rw [le_div_iff₀ hk]; linarith
        nlinarith [sq_nonneg (fhat σ.p σ.f S)]
    _ ≤ ∑ S : Finset (Fin n), (S.card : ℝ) / k * fhat σ.p σ.f S ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun S _ _ => by positivity)
    _ = FriedgutCoalition.totalPInfl σ.p σ.f / (2 * k) := by
        rw [hT, mul_div_mul_left _ _ (two_ne_zero), Finset.sum_div]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        field_simp
    _ ≤ C / (2 * k) := by gcongr

lemma notSfam_split (σ : Setup n) :
    ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam), fhat σ.p σ.f S ^ 2 ≤
      ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam ∧ S.card ≤ σ.K), fhat σ.p σ.f S ^ 2 +
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ S.card ≤ σ.K), fhat σ.p σ.f S ^ 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun S => S.card ≤ σ.K), Finset.filter_filter,
    Finset.filter_filter]
  refine add_le_add (le_of_eq ?_) ?_
  · rfl
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun S hS => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢; exact hS.2)
      (fun S _ _ => sq_nonneg _)

/-- the case `I_p(f) > 0` -/
theorem lemma_2_1_pos {n : ℕ} (p a : ℝ) (f : Cube n → Bool)
    (hp : 0 < p) (hp_half : p ≤ 1 / 2) (ha : 0 < a) (ha_one : a ≤ 1)
    (hI : 0 < FriedgutCoalition.totalPInfl p f) :
    let C_f : ℕ := ⌈FriedgutCoalition.totalPInfl p f⌉₊
    let d : ℕ := ⌈(10 : ℝ) ^ 3 * (C_f : ℝ) / a⌉₊
    let L : ℝ := Real.exp ((10 : ℝ) ^ 10 * a⁻¹ ^ 2 * (C_f : ℝ) ^ 2)
    ∃ (J : ActivationFamily n) (h : Cube n → Bool),
      IncreasingActivations J ∧ error p f h ≤ a ∧ AdaptiveMeasurable J h ∧
      arity J ≤ d ∧ load p J ≤ L := by
  intro C_f d L
  have hp1 : p < 1 := by linarith
  have hC : 1 ≤ C_f := by
    have : (0 : ℝ) < C_f := lt_of_lt_of_le hI (Nat.le_ceil _)
    exact_mod_cast this
  have hIC : FriedgutCoalition.totalPInfl p f ≤ C_f := Nat.le_ceil _
  obtain ⟨hε₁, hδ, hδ1, hk1, hKk, hkK, hKd, hload, herr⟩ := numerics C_f hC a ha ha_one
  set ε₀ : ℝ := a / 1000 with hε₀
  set k : ℝ := C_f / ε₀ with hk
  set K : ℕ := ⌊k⌋₊ with hK
  set ε₁ : ℝ := Real.exp (-(1000 * k ^ 2)) with hε₁def
  set δ : ℝ := ε₀ * ε₁ ^ 2 / ((K + 1) * 2 ^ (8 * K)) with hδdef
  let σ : Setup n := ⟨p, f, K, ε₁, δ⟩
  have hσ : σ.Good := ⟨hp, hp_half, hε₁, hδ, hδ1⟩
  -- the leaf (Hatami (11))
  have hleaf := NarrowDNF.Approx.hatami_step_two_small_low_degree_mass p f hp hp_half C_f hC hIC ε₀
    (by positivity) (by rw [hε₀]; linarith)
  simp only at hleaf
  -- split the leaf sum
  have hlow : ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam ∧ S.card ≤ K), fhat p f S ^ 2 +
      ∑ S ∈ σ.Sfam, expect p (fun x => if |FS p f S x| ≤ ε₁ then FS p f S x ^ 2 else 0) ≤
      ε₀ / k := by
    have hfilt : Finset.univ.filter (fun S : Finset (Fin n) => (S.card : ℝ) ≤ k) =
        Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ K) := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hK, Nat.le_floor_iff (by linarith)]
    have hleaf' : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => (S.card : ℝ) ≤ k),
        expect p (fun x => if |FS p f S x| ≤ ε₁ then FS p f S x ^ 2 else 0) ≤ ε₀ / k := hleaf
    rw [hfilt] at hleaf'
    exact (split_low σ hσ).symm.le.trans hleaf'
  have hhigh : ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ S.card ≤ K),
      fhat p f S ^ 2 ≤ ε₀ / 2 := by
    have hk0 : 0 < k := by linarith
    have := high_le σ hσ k hk0 hkK C_f hIC
    have hε0 : 0 < ε₀ := by rw [hε₀]; positivity
    have hCpos : (0 : ℝ) < C_f := by exact_mod_cast hC
    have e : (C_f : ℝ) / (2 * k) = ε₀ / 2 := by
      rw [hk]; field_simp
    rw [e] at this
    exact this
  have hfg : expect p (fun x => (ind f x - σ.g x) ^ 2) ≤ ε₀ / 2 + ε₀ / k := by
    have h1 := f_sub_g σ hσ
    have h2 := notSfam_split σ
    have h3 : 0 ≤ ∑ S ∈ σ.Sfam,
        expect p (fun x => if |FS p f S x| ≤ ε₁ then FS p f S x ^ 2 else 0) :=
      Finset.sum_nonneg (fun S _ => expect_nonneg p hp.le hp1.le _
        (fun x => by split_ifs <;> positivity))
    have h1' : expect p (fun x => (ind f x - σ.g x) ^ 2) =
        ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam), fhat p f S ^ 2 := h1
    have h2' : ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam), fhat p f S ^ 2 ≤
      ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam ∧ S.card ≤ K), fhat p f S ^ 2 +
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => ¬ S.card ≤ K), fhat p f S ^ 2 := h2
    rw [h1']
    linarith
  have hggt : expect p (fun x => (σ.g x - σ.gt x) ^ 2) ≤
      (K + 1) * (ε₀ / k + 2 ^ (8 * K) * δ / ε₁ ^ 2) := by
    have h1 := g_sub_gt_le σ hσ
    have h2 : ∑ S ∈ σ.Sfam, expect σ.p (fun x => (FS σ.p σ.f S x - σ.Ft S x) ^ 2) ≤
        ∑ S ∈ σ.Sfam,
          expect p (fun x => if |FS p f S x| ≤ ε₁ then FS p f S x ^ 2 else 0) :=
      Finset.sum_le_sum (fun S hS => diag_le σ hσ S hS)
    have h3 : 0 ≤ ∑ S ∈ Finset.univ.filter (fun S => S ∉ σ.Sfam ∧ S.card ≤ K), fhat p f S ^ 2 :=
      Finset.sum_nonneg (fun S _ => sq_nonneg _)
    have h1' : expect p (fun x => (σ.g x - σ.gt x) ^ 2) ≤
      (K + 1) * (∑ S ∈ σ.Sfam, expect σ.p (fun x => (FS σ.p σ.f S x - σ.Ft S x) ^ 2) +
        2 ^ (8 * K) * δ / ε₁ ^ 2) := h1
    refine h1'.trans ?_
    gcongr
    linarith
  refine ⟨σ.J, fun x => decide (1 / 2 < σ.gt x), J_increasing σ hσ, ?_, ?_, ?_, ?_⟩
  · calc error p f (fun x => decide (1 / 2 < σ.gt x))
          ≤ 4 * expect p (fun x => (ind f x - σ.gt x) ^ 2) :=
            error_round_le p hp.le hp1.le f σ.gt
      _ ≤ 4 * (2 * expect p (fun x => (ind f x - σ.g x) ^ 2) +
            2 * expect p (fun x => (σ.g x - σ.gt x) ^ 2)) := by
            gcongr; exact expect_sq_sub_le p hp.le hp1.le _ _ _
      _ ≤ 4 * (2 * (ε₀ / 2 + ε₀ / k) + 2 * ((K + 1) * (ε₀ / k + 2 ^ (8 * K) * δ / ε₁ ^ 2))) := by
            gcongr
      _ ≤ a := herr
  · intro x y hxy
    show decide (1 / 2 < σ.gt x) = decide (1 / 2 < σ.gt y)
    rw [gt_measurable σ x y hxy]
  · exact le_trans (arity_J_le σ) hKd
  · exact le_trans (load_J_le σ hσ) hload

end NarrowDNF.Dev.Hat.PartB
end

section
set_option autoImplicit false
namespace NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
alias lemma_2_1_pos := NarrowDNF.Dev.Hat.PartB.lemma_2_1_pos

/-! ## Assembly -/
theorem lemma_2_1_dev {n : ℕ} (p a : ℝ) (f : Cube n → Bool)
    (hp : 0 < p) (hp_half : p ≤ 1 / 2) (ha : 0 < a) (ha_one : a ≤ 1) :
    let C_f : ℕ := ⌈FriedgutCoalition.totalPInfl p f⌉₊
    let d : ℕ := ⌈(10 : ℝ) ^ 3 * (C_f : ℝ) / a⌉₊
    let L : ℝ := Real.exp ((10 : ℝ) ^ 10 * a⁻¹ ^ 2 * (C_f : ℝ) ^ 2)
    ∃ (J : ActivationFamily n) (h : Cube n → Bool),
      IncreasingActivations J ∧ error p f h ≤ a ∧ AdaptiveMeasurable J h ∧
      arity J ≤ d ∧ load p J ≤ L := by
  intro C_f d L
  by_cases hI : FriedgutCoalition.totalPInfl p f ≤ 0
  · obtain ⟨J, h, h1, h2, h3, h4, h5⟩ := lemma_2_1_zero p a f hp hp_half ha ha_one hI
    refine ⟨J, h, h1, h2, h3, le_trans h4 (Nat.zero_le _), le_trans h5 ?_⟩
    exact Real.one_le_exp (by positivity)
  · exact lemma_2_1_pos p a f hp hp_half ha ha_one (lt_of_not_ge hI)

end NarrowDNF.Dev.Hat
end

section
set_option autoImplicit false
open NarrowDNF
open NarrowDNF.Dev
open NarrowDNF.Dev.Hat
open NarrowDNF.Approx
variable {n : ℕ}
theorem solution {n : ℕ} (p a : ℝ) (f : Cube n → Bool)
    (hp : 0 < p) (hp_half : p ≤ 1 / 2) (ha : 0 < a) (ha_one : a ≤ 1) :
    let C_f : ℕ := ⌈FriedgutCoalition.totalPInfl p f⌉₊
    let d : ℕ := ⌈(10 : ℝ) ^ 3 * (C_f : ℝ) / a⌉₊
    let L : ℝ := Real.exp ((10 : ℝ) ^ 10 * a⁻¹ ^ 2 * (C_f : ℝ) ^ 2)
    ∃ (J : ActivationFamily n) (h : Cube n → Bool),
      IncreasingActivations J ∧ error p f h ≤ a ∧ AdaptiveMeasurable J h ∧
      arity J ≤ d ∧ load p J ≤ L := by
  exact NarrowDNF.Dev.Hat.lemma_2_1_dev p a f hp hp_half ha ha_one
end
