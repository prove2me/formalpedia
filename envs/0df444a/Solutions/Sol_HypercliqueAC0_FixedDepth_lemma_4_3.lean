-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:28:44.932094+00:00
-- url     : https://prove2.me/submissions/670673c3-f808-4ed7-87c4-660e83bb5123

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section
set_option linter.unusedSectionVars false
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

local notation "sw" => OAI.Problem313.BiasedFourier.scalarWeight
local notation "chi" => OAI.Problem313.BiasedFourier.chi

section Generic
variable {X : Type*} [Fintype X]

lemma L43_weight_eq (p : ℝ) (x : X → Bool) : weight p x = ∏ e, sw p (x e) := rfl

/-- factor of a character -/
def L43_phi (p : ℝ) (S : Finset X) (e : X) (b : Bool) : ℝ := if e ∈ S then chi p b else 1

lemma L43_char_eq (p : ℝ) (S : Finset X) (x : X → Bool) :
    character p S x = ∏ e, L43_phi p S e (x e) := by
  unfold character OAI.Problem313.BiasedFourier.char L43_phi
  rw [Finset.prod_ite_mem, Finset.univ_inter]

lemma L43_coeff_eq (p : ℝ) (g : (X → Bool) → ℝ) (S : Finset X) :
    fourierCoeff p g S = ∑ x, weight p x * g x * character p S x := rfl

/-- discrete derivative along J -/
def L43_delta (J : Finset X) (g : (X → Bool) → ℝ) (y : X → Bool) : ℝ :=
  ∑ U ∈ J.powerset, (-1 : ℝ) ^ (J \ U).card *
    g (fun e => if e ∈ J then decide (e ∈ U) else y e)

lemma L43_prod_split (J : Finset X) (F : X → ℝ) :
    ∏ e, F e = (∏ e ∈ J, F e) * ∏ e ∈ Finset.univ \ J, F e := by
  rw [mul_comm, Finset.prod_sdiff (Finset.subset_univ J)]

lemma L43_delta_prod (J : Finset X) (φ : X → Bool → ℝ) (y : X → Bool) :
    L43_delta J (fun x => ∏ e, φ e (x e)) y =
      ∏ e, (if e ∈ J then φ e true - φ e false else φ e (y e)) := by
  unfold L43_delta
  rw [L43_prod_split J]
  have h1 : ∏ e ∈ J, (if e ∈ J then φ e true - φ e false else φ e (y e)) =
      ∏ e ∈ J, (φ e true + -φ e false) := by
    apply Finset.prod_congr rfl; intro e he; simp [he, sub_eq_add_neg]
  have h2 : ∏ e ∈ Finset.univ \ J, (if e ∈ J then φ e true - φ e false else φ e (y e)) =
      ∏ e ∈ Finset.univ \ J, φ e (y e) := by
    apply Finset.prod_congr rfl; intro e he
    simp only [Finset.mem_sdiff] at he; simp [he.2]
  rw [h1, h2, Finset.prod_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.mem_powerset] at hU
  beta_reduce
  rw [L43_prod_split J]
  have h3 : ∏ e ∈ J, φ e (if e ∈ J then decide (e ∈ U) else y e) =
      (∏ e ∈ U, φ e true) * ∏ e ∈ J \ U, φ e false := by
    rw [mul_comm, ← Finset.prod_sdiff hU]
    congr 1
    · apply Finset.prod_congr rfl; intro e he
      simp only [Finset.mem_sdiff] at he; simp [he.1, he.2]
    · apply Finset.prod_congr rfl; intro e he
      simp [hU he, he]
  have h4 : ∏ e ∈ Finset.univ \ J, φ e (if e ∈ J then decide (e ∈ U) else y e) =
      ∏ e ∈ Finset.univ \ J, φ e (y e) := by
    apply Finset.prod_congr rfl; intro e he
    simp only [Finset.mem_sdiff] at he; simp [he.2]
  rw [h3, h4, Finset.prod_neg]
  ring

variable {p : ℝ}

lemma L43_sigma_sq (hp : 0 < p) (hp1 : p < 1) :
    Real.sqrt (p * (1 - p)) * Real.sqrt (p * (1 - p)) = p * (1 - p) :=
  Real.mul_self_sqrt (by nlinarith)

lemma L43_sigma_pos (hp : 0 < p) (hp1 : p < 1) : 0 < Real.sqrt (p * (1 - p)) :=
  Real.sqrt_pos.mpr (by nlinarith)

lemma L43_chi_mul (hp : 0 < p) (hp1 : p < 1) (a b : Bool) :
    chi p a * chi p b = ((if a then 1 else 0) - p) * ((if b then 1 else 0) - p) / (p * (1 - p)) := by
  unfold OAI.Problem313.BiasedFourier.chi
  rw [div_mul_div_comm, Real.mul_self_sqrt (by nlinarith)]
lemma L43_sw_chi_chi (hp : 0 < p) (hp1 : p < 1) (a b : Bool) :
    sw p a * (1 + chi p a * chi p b) = if a = b then 1 else 0 := by
  have h1p : (1 - p) ≠ 0 := by linarith
  have hp0 : p ≠ 0 := hp.ne'
  rw [L43_chi_mul hp hp1]
  cases a <;> cases b <;> simp [OAI.Problem313.BiasedFourier.scalarWeight] <;> field_simp <;>
    (try ring_nf) <;> simp
lemma L43_chi_diff_sq (hp : 0 < p) (hp1 : p < 1) :
    (chi p true - chi p false) * (chi p true - chi p false) = p⁻¹ * (1 - p)⁻¹ := by
  rw [sub_mul, mul_sub, mul_sub, L43_chi_mul hp hp1, L43_chi_mul hp hp1, L43_chi_mul hp hp1,
    L43_chi_mul hp hp1]
  have h1p : (1 - p) ≠ 0 := by linarith
  have hp0 : p ≠ 0 := hp.ne'
  simp; field_simp; ring
lemma L43_inversion (hp : 0 < p) (hp1 : p < 1) (g : (X → Bool) → ℝ) (y : X → Bool) :
    g y = ∑ S, fourierCoeff p g S * character p S y := by
  simp_rw [L43_coeff_eq, Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ x : X → Bool, ∑ S : Finset X, weight p x * g x * character p S x * character p S y
      = g x * (if x = y then 1 else 0) := by
    intro x
    have : ∑ S : Finset X, character p S x * character p S y =
        ∏ e, (1 + chi p (x e) * chi p (y e)) := by
      rw [Finset.prod_one_add, Finset.powerset_univ]
      apply Finset.sum_congr rfl; intro S _
      simp [character, OAI.Problem313.BiasedFourier.char, Finset.prod_mul_distrib]
    calc _ = g x * (weight p x * ∑ S : Finset X, character p S x * character p S y) := by
          rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; ring
      _ = _ := by
          rw [this, L43_weight_eq, ← Finset.prod_mul_distrib]
          simp_rw [L43_sw_chi_chi hp hp1]
          rw [Finset.prod_boole]
          congr 2
          simp [funext_iff]
  simp_rw [key]
  simp

lemma L43_parseval (hp : 0 < p) (hp1 : p < 1) (g : (X → Bool) → ℝ) :
    ∑ S, fourierCoeff p g S ^ 2 = ∑ y, weight p y * g y ^ 2 := by
  have : ∀ y, weight p y * g y ^ 2 =
      ∑ S, fourierCoeff p g S * (weight p y * g y * character p S y) := by
    intro y
    rw [sq, ← mul_assoc]
    conv_lhs => arg 2; rw [L43_inversion hp hp1 g y]
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; ring
  simp_rw [this]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  rw [← Finset.mul_sum, ← L43_coeff_eq, sq]

/-- delta is linear: expand through Fourier inversion -/
lemma L43_delta_expand (hp : 0 < p) (hp1 : p < 1) (J : Finset X) (g : (X → Bool) → ℝ)
    (y : X → Bool) :
    L43_delta J g y = ∑ S, fourierCoeff p g S * L43_delta J (character p S) y := by
  unfold L43_delta
  conv_lhs =>
    arg 2; ext U; rw [L43_inversion hp hp1 g]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  apply Finset.sum_congr rfl; intro U _; ring

/-- zero-indicator on J in product form -/
def L43_zeta (J : Finset X) (e : X) (b : Bool) : ℝ :=
  if e ∈ J then (if b then 0 else 1) else 1

lemma L43_coord (hp : 0 < p) (hp1 : p < 1) (J S S' : Finset X) (e : X) :
    ∑ b : Bool, sw p b * L43_zeta J e b *
      (if e ∈ J then L43_phi p S e true - L43_phi p S e false else L43_phi p S e b) *
      (if e ∈ J then L43_phi p S' e true - L43_phi p S' e false else L43_phi p S' e b) =
    if e ∈ J then (if e ∈ S ∧ e ∈ S' then p⁻¹ else 0) else
      (if (e ∈ S ↔ e ∈ S') then 1 else 0) := by
  have h1p : (1 - p) ≠ 0 := by linarith
  have hp0 : p ≠ 0 := hp.ne'
  have hAA : p * (chi p true * chi p true) = 1 - p := by
    rw [L43_chi_mul hp hp1]; simp; field_simp
  have hBB : (1 - p) * (chi p false * chi p false) = p := by
    rw [L43_chi_mul hp hp1]; simp; field_simp
  have hD : (1 - p) * ((chi p true - chi p false) * (chi p true - chi p false)) = p⁻¹ := by
    rw [L43_chi_diff_sq hp hp1]; field_simp
  have hA : p * chi p true + (1 - p) * chi p false = 0 := by
    rw [OAI.Problem313.BiasedFourier.chi_true, OAI.Problem313.BiasedFourier.chi_false]; ring
  rw [Fintype.sum_bool]
  simp only [L43_phi, L43_zeta]
  generalize chi p true = A at *
  generalize chi p false = B at *
  by_cases hJ : e ∈ J <;> by_cases hS : e ∈ S <;> by_cases hS' : e ∈ S' <;>
    simp [hJ, hS, hS', OAI.Problem313.BiasedFourier.scalarWeight] <;>
    first | linear_combination hD | linear_combination hAA + hBB | linear_combination hA

lemma L43_orth (hp : 0 < p) (hp1 : p < 1) (J S S' : Finset X) :
    ∑ y, weight p y * (∏ e, L43_zeta J e (y e)) * L43_delta J (character p S) y *
      L43_delta J (character p S') y =
    if S = S' ∧ J ⊆ S then (p⁻¹) ^ J.card else 0 := by
  have hc : ∀ T : Finset X, character p T = fun x => ∏ e, L43_phi p T e (x e) := by
    intro T; funext x; exact L43_char_eq p T x
  simp_rw [hc, L43_delta_prod, L43_weight_eq, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun e b => sw p b * L43_zeta J e b *
      (if e ∈ J then L43_phi p S e true - L43_phi p S e false else L43_phi p S e b) *
      (if e ∈ J then L43_phi p S' e true - L43_phi p S' e false else L43_phi p S' e b))]
  simp_rw [L43_coord hp hp1]
  split_ifs with h
  · obtain ⟨rfl, hJ⟩ := h
    have : ∀ e ∈ (Finset.univ : Finset X), (if e ∈ J then (if e ∈ S ∧ e ∈ S then p⁻¹ else 0) else
        (if (e ∈ S ↔ e ∈ S) then (1:ℝ) else 0)) = if e ∈ J then p⁻¹ else 1 := by
      intro e _
      by_cases he : e ∈ J
      · simp [he, hJ he]
      · simp [he]
    rw [Finset.prod_congr rfl this, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  · apply Finset.prod_eq_zero_iff.mpr
    by_cases hSS : S = S'
    · subst hSS
      have : ¬ J ⊆ S := fun h' => h ⟨rfl, h'⟩
      obtain ⟨e, heJ, heS⟩ := Finset.not_subset.mp this
      exact ⟨e, Finset.mem_univ _, by simp [heJ, heS]⟩
    · obtain ⟨e, he⟩ : ∃ e, ¬ (e ∈ S ↔ e ∈ S') := by
        by_contra hc; push Not at hc; exact hSS (Finset.ext hc)
      refine ⟨e, Finset.mem_univ _, ?_⟩
      by_cases heJ : e ∈ J
      · have : ¬ (e ∈ S ∧ e ∈ S') := fun h' => he ⟨fun _ => h'.2, fun _ => h'.1⟩
        simp [heJ, this]
      · simp [heJ, he]

lemma L43_energy (hp : 0 < p) (hp1 : p < 1) (J : Finset X) (g : (X → Bool) → ℝ) :
    ∑ y, weight p y * (∏ e, L43_zeta J e (y e)) * L43_delta J g y ^ 2 =
      (p⁻¹) ^ J.card * ∑ S, (if J ⊆ S then fourierCoeff p g S ^ 2 else 0) := by
  simp_rw [L43_delta_expand hp hp1 J g, sq, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  rw [Finset.sum_comm]
  have : ∀ S', ∑ y, weight p y * (∏ e, L43_zeta J e (y e)) *
      (fourierCoeff p g S * L43_delta J (character p S) y *
        (fourierCoeff p g S' * L43_delta J (character p S') y)) =
      fourierCoeff p g S * fourierCoeff p g S' * (if S = S' ∧ J ⊆ S then (p⁻¹) ^ J.card else 0) := by
    intro S'
    rw [← L43_orth hp hp1 J S S', Finset.mul_sum]
    apply Finset.sum_congr rfl; intro y _; ring
  simp_rw [this]
  by_cases hJ : J ⊆ S
  · simp [hJ]; ring
  · simp [hJ]

lemma L43_sw_nonneg (hp : 0 < p) (hp1 : p < 1) (b : Bool) : 0 ≤ sw p b := by
  cases b <;> simp [OAI.Problem313.BiasedFourier.scalarWeight] <;> linarith

lemma L43_weight_nonneg (hp : 0 < p) (hp1 : p < 1) (y : X → Bool) : 0 ≤ weight p y := by
  rw [L43_weight_eq]; exact Finset.prod_nonneg fun e _ => L43_sw_nonneg hp hp1 _

lemma L43_weight_sum (p : ℝ) : ∑ y : X → Bool, weight p y = 1 := by
  simp_rw [L43_weight_eq]
  rw [← Fintype.prod_sum (fun _ b => sw p b)]
  apply Finset.prod_eq_one; intro e _
  simp [OAI.Problem313.BiasedFourier.scalarWeight]

lemma L43_zeta_nonneg (J : Finset X) (y : X → Bool) : 0 ≤ ∏ e, L43_zeta J e (y e) := by
  apply Finset.prod_nonneg; intro e _
  unfold L43_zeta; split_ifs <;> norm_num

lemma L43_zeta_one (J : Finset X) (y : X → Bool) (hy : ∀ e ∈ J, y e = false) :
    ∏ e, L43_zeta J e (y e) = 1 := by
  apply Finset.prod_eq_one; intro e _
  unfold L43_zeta; split_ifs with h1 h2 <;> simp_all

lemma L43_rel (hp : 0 < p) (hp1 : p < 1) (K : Finset X) (y : X → Bool) :
    ∑ G : X → Bool, weight p G *
      (if (∀ e, (e ∈ K → G e = true → y e = true) ∧ (e ∉ K → G e = y e)) then 1 else 0) ≤
      (p⁻¹) ^ K.card * weight p y := by
  have h1 : ∀ G : X → Bool, weight p G *
      (if (∀ e, (e ∈ K → G e = true → y e = true) ∧ (e ∉ K → G e = y e)) then (1:ℝ) else 0) =
      ∏ e, (sw p (G e) * (if (e ∈ K → G e = true → y e = true) ∧ (e ∉ K → G e = y e)
        then 1 else 0)) := by
    intro G
    rw [Finset.prod_mul_distrib, Finset.prod_boole, L43_weight_eq]
    simp
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun e b => sw p b *
    (if (e ∈ K → b = true → y e = true) ∧ (e ∉ K → b = y e) then (1:ℝ) else 0))]
  have h2 : (p⁻¹) ^ K.card * weight p y = ∏ e, (sw p (y e) * if e ∈ K then p⁻¹ else 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const,
      L43_weight_eq, mul_comm]
  rw [h2]
  apply Finset.prod_le_prod
  · intro e _
    apply Finset.sum_nonneg; intro b _
    apply mul_nonneg (L43_sw_nonneg hp hp1 b); split_ifs <;> norm_num
  · intro e _
    have hpi : 1 ≤ p⁻¹ := one_le_inv₀ hp |>.mpr hp1.le
    rw [Fintype.sum_bool]
    by_cases hK : e ∈ K <;> cases hy : y e <;>
      simp [hK, hy, OAI.Problem313.BiasedFourier.scalarWeight]
    · nlinarith
    · rw [mul_inv_cancel₀ hp.ne']

lemma L43_probEJ (hp : 0 < p) (hp1 : p < 1) (EH J : Finset X) (hJ : J ⊆ EH)
    (I : Finset ℕ) (g : ℕ → (X → Bool) → ℝ) :
    ∑ G : X → Bool, weight p G * (if (∃ y : X → Bool, (∀ e, G e = true → y e = true) ∧
        (∀ e, e ∉ EH → y e = G e) ∧ (∀ e ∈ J, G e = false ∧ y e = false) ∧
        1 ≤ ∑ i ∈ I, L43_delta J (g i) y ^ 2) then 1 else 0) ≤
      (p⁻¹) ^ EH.card * ∑ i ∈ I, ∑ S, (if J ⊆ S then fourierCoeff p (g i) S ^ 2 else 0) := by
  set K := EH \ J with hKdef
  let cond : (X → Bool) → Prop := fun y =>
    (∀ e ∈ J, y e = false) ∧ 1 ≤ ∑ i ∈ I, L43_delta J (g i) y ^ 2
  let rel : (X → Bool) → (X → Bool) → Prop := fun G y =>
    ∀ e, (e ∈ K → G e = true → y e = true) ∧ (e ∉ K → G e = y e)
  have step1 : ∀ G : X → Bool, (if (∃ y : X → Bool, (∀ e, G e = true → y e = true) ∧
        (∀ e, e ∉ EH → y e = G e) ∧ (∀ e ∈ J, G e = false ∧ y e = false) ∧
        1 ≤ ∑ i ∈ I, L43_delta J (g i) y ^ 2) then (1:ℝ) else 0) ≤
      ∑ y, (if cond y then (1:ℝ) else 0) * (if rel G y then 1 else 0) := by
    intro G
    split_ifs with hev
    · obtain ⟨y, h1, h2, h3, h4⟩ := hev
      have hc : cond y := ⟨fun e he => (h3 e he).2, h4⟩
      have hr : rel G y := by
        intro e
        refine ⟨fun _ hG => h1 e hG, fun he => ?_⟩
        rw [hKdef, Finset.mem_sdiff, not_and_or, not_not] at he
        rcases he with he | he
        · exact (h2 e he).symm
        · rw [(h3 e he).1, (h3 e he).2]
      calc (1:ℝ) = (if cond y then (1:ℝ) else 0) * (if rel G y then 1 else 0) := by
            simp [hc, hr]
        _ ≤ _ := Finset.single_le_sum (f := fun y => (if cond y then (1:ℝ) else 0) *
              (if rel G y then 1 else 0)) (fun y _ => by split_ifs <;> norm_num)
              (Finset.mem_univ y)
    · apply Finset.sum_nonneg; intro y _; split_ifs <;> norm_num
  have step3 : ∀ y : X → Bool, (if cond y then (1:ℝ) else 0) * weight p y ≤
      weight p y * (∏ e, L43_zeta J e (y e)) * ∑ i ∈ I, L43_delta J (g i) y ^ 2 := by
    intro y
    split_ifs with hc
    · rw [L43_zeta_one J y hc.1]; nlinarith [hc.2, L43_weight_nonneg hp hp1 y]
    · rw [zero_mul]
      apply mul_nonneg (mul_nonneg (L43_weight_nonneg hp hp1 y) (L43_zeta_nonneg J y))
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
  calc _ ≤ ∑ G : X → Bool, weight p G *
        ∑ y, (if cond y then (1:ℝ) else 0) * (if rel G y then 1 else 0) := by
        apply Finset.sum_le_sum; intro G _
        exact mul_le_mul_of_nonneg_left (step1 G) (L43_weight_nonneg hp hp1 G)
    _ = ∑ y, (if cond y then (1:ℝ) else 0) *
        ∑ G : X → Bool, weight p G * (if rel G y then 1 else 0) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro y _
        apply Finset.sum_congr rfl; intro G _
        ring
    _ ≤ ∑ y, (if cond y then (1:ℝ) else 0) * ((p⁻¹) ^ K.card * weight p y) := by
        apply Finset.sum_le_sum; intro y _
        apply mul_le_mul_of_nonneg_left (L43_rel hp hp1 K y)
        split_ifs <;> norm_num
    _ = (p⁻¹) ^ K.card * ∑ y, (if cond y then (1:ℝ) else 0) * weight p y := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
    _ ≤ (p⁻¹) ^ K.card * ∑ y, weight p y * (∏ e, L43_zeta J e (y e)) *
          ∑ i ∈ I, L43_delta J (g i) y ^ 2 := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => step3 y)
        positivity
    _ = (p⁻¹) ^ K.card * ∑ i ∈ I, ∑ y, weight p y * (∏ e, L43_zeta J e (y e)) *
          L43_delta J (g i) y ^ 2 := by
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = (p⁻¹) ^ K.card * ∑ i ∈ I, (p⁻¹) ^ J.card *
          ∑ S, (if J ⊆ S then fourierCoeff p (g i) S ^ 2 else 0) := by
        simp_rw [L43_energy hp hp1]
    _ = _ := by
        rw [← Finset.mul_sum, ← mul_assoc, ← pow_add, hKdef,
          Finset.card_sdiff_add_card_eq_card hJ]

lemma L43_probEJ' (hp : 0 < p) (hp1 : p < 1) (EH J : Finset X) (hJ : J ⊆ EH)
    (I : Finset ℕ) (g : ℕ → (X → Bool) → ℝ) :
    probability p (fun G => ∃ y : X → Bool, (∀ e, G e = true → y e = true) ∧
        (∀ e, e ∉ EH → y e = G e) ∧ (∀ e ∈ J, G e = false ∧ y e = false) ∧
        1 ≤ ∑ i ∈ I, L43_delta J (g i) y ^ 2) ≤
      (p⁻¹) ^ EH.card * ∑ i ∈ I, ∑ S, (if J ⊆ S then fourierCoeff p (g i) S ^ 2 else 0) := by
  unfold probability expectation
  convert L43_probEJ hp hp1 EH J hJ I g

lemma L43_prob_union {κ : Type*} (hp : 0 < p) (hp1 : p < 1) (E : (X → Bool) → Prop)
    (F : Finset κ) (EJ : κ → (X → Bool) → Prop) (h : ∀ G, E G → ∃ J ∈ F, EJ J G) :
    probability p E ≤ ∑ J ∈ F, probability p (EJ J) := by
  unfold probability expectation
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro G _
  dsimp only
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (L43_weight_nonneg hp hp1 G)
  split_ifs with hE
  · obtain ⟨J, hJ, hJG⟩ := h G hE
    calc (1:ℝ) = (if EJ J G then 1 else 0) := by rw [if_pos hJG]
      _ ≤ _ := Finset.single_le_sum (f := fun J => (if EJ J G then (1:ℝ) else 0))
          (fun _ _ => by split_ifs <;> norm_num) hJ
  · exact Finset.sum_nonneg fun J _ => by split_ifs <;> norm_num

lemma L43_coeff_split (φ : (X → Bool) → ℝ) (E J : Finset X) (hJ : J ⊆ E) :
    multilinearCoeff φ E = ∑ T ∈ (E \ J).powerset, (-1 : ℝ) ^ ((E \ J) \ T).card *
      L43_delta J φ (indicator T) := by
  unfold multilinearCoeff L43_delta
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun V => (V \ J, V ∩ J)) (fun TU => TU.1 ∪ TU.2) ?_ ?_ ?_ ?_ ?_
  · intro V hV
    simp only [Finset.mem_powerset] at hV ⊢
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.sdiff_subset_sdiff hV le_rfl, Finset.inter_subset_right⟩
  · intro TU hTU
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset] at hTU ⊢
    exact Finset.union_subset (hTU.1.trans Finset.sdiff_subset) (hTU.2.trans hJ)
  · intro V _
    exact Finset.sdiff_union_inter V J
  · intro TU hTU
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powerset] at hTU
    obtain ⟨T, U⟩ := TU
    simp only at hTU ⊢
    have hT : ∀ e ∈ T, e ∉ J := fun e he => (Finset.mem_sdiff.mp (hTU.1 he)).2
    ext e
    · simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact h
        · exact absurd (hTU.2 h) h'
      · intro h; exact ⟨Or.inl h, hT e h⟩
    · simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact absurd h' (hT e h)
        · exact h
      · intro h; exact ⟨Or.inr h, hTU.2 h⟩
  · intro V hV
    rw [Finset.mem_powerset] at hV
    have hfun : (fun e => if e ∈ J then decide (e ∈ V ∩ J) else indicator (V \ J) e) =
        indicator V := by
      funext e; by_cases he : e ∈ J <;> simp [he, indicator]
    simp only
    rw [hfun]
    have hcard : (E \ V).card = ((E \ J) \ (V \ J)).card + (J \ (V ∩ J)).card := by
      rw [← Finset.card_filter_add_card_filter_not (s := E \ V) (p := fun e => e ∉ J)]
      congr 2
      · ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
      · ext e; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_inter]
        constructor
        · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨not_not.mp h2, fun h => h1 h.1⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨hJ h1, fun h => h2 ⟨h, h1⟩⟩, not_not.mpr h1⟩
    rw [hcard, pow_add]; ring

lemma L43_exists_delta (φ : (X → Bool) → ℝ) (E J : Finset X) (hJ : J ⊆ E)
    (h : multilinearCoeff φ E ≠ 0) :
    ∃ z : X → Bool, (∀ e ∈ J, z e = false) ∧ L43_delta J φ z ≠ 0 := by
  rw [L43_coeff_split φ E J hJ] at h
  obtain ⟨T, hT, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨indicator T, fun e he => ?_, fun h0 => hne (by rw [h0, mul_zero])⟩
  rw [Finset.mem_powerset] at hT
  have : e ∉ T := fun h' => (Finset.mem_sdiff.mp (hT h')).2 he
  simp [indicator, this]

end Generic

lemma L43_delta_rho {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r)
    (g : (Edge m r → Bool) → ℝ) (J' : Finset (FreeEdge G H)) (z : FreeEdge G H → Bool) :
    L43_delta J' (restricted G H g) z =
      L43_delta (J'.image Subtype.val) g (rho G H z) := by
  unfold L43_delta restricted
  rw [Finset.powerset_image, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro U hU
    rw [Finset.mem_powerset] at hU
    congr 1
    · congr 1
      rw [← Finset.card_image_of_injective _ Subtype.val_injective]
      congr 1
      ext x
      simp only [Finset.mem_image, Finset.mem_sdiff]
      constructor
      · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
        exact ⟨⟨a, ha1, rfl⟩, fun ⟨b, hb, hba⟩ => ha2 (Subtype.ext hba ▸ hb)⟩
      · rintro ⟨⟨a, ha1, rfl⟩, h2⟩
        exact ⟨a, ⟨ha1, fun h => h2 ⟨a, h, rfl⟩⟩, rfl⟩
    · congr 1
      funext e
      unfold rho
      by_cases he : e ∈ H.edges ∧ G e = false
      · have hmem : ∀ A : Finset (FreeEdge G H), e ∈ A.image Subtype.val ↔ ⟨e, he⟩ ∈ A := by
          intro A
          simp only [Finset.mem_image]
          constructor
          · rintro ⟨a, ha, rfl⟩; exact ha
          · intro h; exact ⟨_, h, rfl⟩
        rw [dif_pos he]
        simp only [hmem]
        split_ifs <;> simp_all
      · have hmem : e ∉ J'.image Subtype.val := by
          simp only [Finset.mem_image, not_exists, not_and]
          rintro a _ rfl; exact he a.2
        rw [dif_neg he, if_neg hmem, dif_neg he]
  · intro U _ V _ hUV
    exact Finset.image_injective Subtype.val_injective hUV




lemma L43_span_cover {m r : ℕ} (G : Edge m r → Bool) (H : Hypergraph m r)
    (g : (Edge m r → Bool) → ℝ) (hs : spans G H g) :
    ∃ J : Finset (Edge m r), J ⊆ H.edges ∧ H.vertices ⊆ verticesOf J ∧
      J.card ≤ H.vertices.card ∧
      ∃ y : Edge m r → Bool, (∀ e, G e = true → y e = true) ∧ (∀ e, e ∉ H.edges → y e = G e) ∧
        (∀ e ∈ J, G e = false ∧ y e = false) ∧ L43_delta J g y ≠ 0 := by
  obtain ⟨E, hE, hV⟩ := hs
  have hc : ∀ u : H.vertices, ∃ e ∈ E, u.1 ∈ e.1.1 := by
    intro u
    have := hV u.2
    simp only [verticesOf, Finset.mem_biUnion, Finset.mem_image] at this
    obtain ⟨a, ⟨e, he, rfl⟩, hu⟩ := this
    exact ⟨e, he, hu⟩
  choose pick hpick hmem using hc
  set J' := H.vertices.attach.image pick with hJ'
  have hJ'E : J' ⊆ E := by
    intro e he
    rw [hJ', Finset.mem_image] at he
    obtain ⟨u, _, rfl⟩ := he
    exact hpick u
  obtain ⟨z, hz, hne⟩ := L43_exists_delta (restricted G H g) E J' hJ'E hE
  rw [L43_delta_rho] at hne
  refine ⟨J'.image Subtype.val, ?_, ?_, ?_, rho G H z, ?_, ?_, ?_, hne⟩
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨a, _, rfl⟩ := he
    exact a.2.1
  · intro u hu
    simp only [verticesOf, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨(pick ⟨u, hu⟩).1, ⟨pick ⟨u, hu⟩, Finset.mem_image.mpr ⟨⟨u, hu⟩,
      Finset.mem_attach _ _, rfl⟩, rfl⟩, hmem ⟨u, hu⟩⟩
  · calc (J'.image Subtype.val).card ≤ J'.card := Finset.card_image_le
      _ ≤ H.vertices.attach.card := Finset.card_image_le
      _ = H.vertices.card := Finset.card_attach
  · intro e he
    unfold rho
    split_ifs with h
    · rw [h.2] at he; exact absurd he (by simp)
    · exact he
  · intro e he
    unfold rho
    rw [dif_neg (fun h => he h.1)]
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨a, ha, rfl⟩ := he
    refine ⟨a.2.2, ?_⟩
    unfold rho
    rw [dif_pos a.2]
    exact hz a ha

section Prefix
variable {X : Type} [Fintype X]

lemma L43_delta_const (J : Finset X) (hJ : J.Nonempty) (c : ℝ) (y : X → Bool) :
    L43_delta J (fun _ => c) y = 0 := by
  unfold L43_delta
  have : ∑ U ∈ J.powerset, (-1 : ℝ) ^ (J \ U).card = 0 := by
    have h := Finset.prod_add (fun _ => (1:ℝ)) (fun _ => (-1:ℝ)) J
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const] at h
    rw [← h]
    simp only [add_neg_cancel, Finset.prod_const]
    exact zero_pow (Finset.card_ne_zero.mpr hJ)
  rw [← Finset.sum_mul, this, zero_mul]

lemma L43_delta_add (J : Finset X) (f g : (X → Bool) → ℝ) (y : X → Bool) :
    L43_delta J (fun x => f x + g x) y = L43_delta J f y + L43_delta J g y := by
  unfold L43_delta
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro U _; ring

lemma L43_delta_sum (J : Finset X) (I : Finset ℕ) (f : ℕ → (X → Bool) → ℝ) (y : X → Bool) :
    L43_delta J (fun x => ∑ i ∈ I, f i x) y = ∑ i ∈ I, L43_delta J (f i) y := by
  unfold L43_delta
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma L43_delta_int (J : Finset X) (f : (X → Bool) → ℝ) (hf : ∀ x, ∃ n : ℤ, f x = n)
    (y : X → Bool) : ∃ n : ℤ, L43_delta J f y = n := by
  choose N hN using hf
  refine ⟨∑ U ∈ J.powerset, (-1 : ℤ) ^ (J \ U).card *
    N (fun e => if e ∈ J then decide (e ∈ U) else y e), ?_⟩
  unfold L43_delta
  push_cast
  simp_rw [hN]

lemma L43_telescope (isAnd : Bool) (inputs : List ((X → Bool) → Bool)) (x : X → Bool)
    (j : ℕ) : ∑ i ∈ Finset.Icc 1 j, prefixIncrement isAnd inputs i x =
      boolReal (abstractPrefix isAnd inputs j) x - boolReal (abstractPrefix isAnd inputs 0) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [prefixIncrement, Nat.add_sub_cancel]
    ring

lemma L43_prefix0 (isAnd : Bool) (inputs : List ((X → Bool) → Bool)) :
    boolReal (abstractPrefix isAnd inputs 0) = fun _ => if isAnd then 1 else 0 := by
  funext x
  cases isAnd <;> simp [boolReal, abstractPrefix]

lemma L43_prefix_sq (isAnd : Bool) (inputs : List ((X → Bool) → Bool)) (J : Finset X)
    (hJ : J.Nonempty) (y : X → Bool) (j : ℕ) (_hj1 : 1 ≤ j) (hjt : j ≤ inputs.length)
    (h : L43_delta J (boolReal (abstractPrefix isAnd inputs j)) y ≠ 0) :
    1 ≤ ∑ i ∈ Finset.Icc 1 inputs.length,
      L43_delta J (prefixIncrement isAnd inputs i) y ^ 2 := by
  have hF : boolReal (abstractPrefix isAnd inputs j) = fun x =>
      (if isAnd then (1:ℝ) else 0) + ∑ i ∈ Finset.Icc 1 j, prefixIncrement isAnd inputs i x := by
    funext x
    rw [L43_telescope, L43_prefix0]; ring
  rw [hF, L43_delta_add, L43_delta_const J hJ, zero_add, L43_delta_sum] at h
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hint : ∀ x, ∃ n : ℤ, prefixIncrement isAnd inputs i x = n := by
    intro x
    unfold prefixIncrement boolReal
    refine ⟨(if abstractPrefix isAnd inputs i x then 1 else 0) -
      (if abstractPrefix isAnd inputs (i - 1) x then 1 else 0), ?_⟩
    push_cast; rfl
  obtain ⟨n, hn⟩ := L43_delta_int J _ hint y
  have hn0 : n ≠ 0 := by rintro rfl; exact hne (by rw [hn]; simp)
  have h1 : 1 ≤ L43_delta J (prefixIncrement isAnd inputs i) y ^ 2 := by
    rw [hn, one_le_sq_iff_one_le_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn0
  have hi' : i ∈ Finset.Icc 1 inputs.length := by
    rw [Finset.mem_Icc] at hi ⊢; omega
  exact h1.trans (Finset.single_le_sum (f := fun i =>
    L43_delta J (prefixIncrement isAnd inputs i) y ^ 2) (fun _ _ => sq_nonneg _) hi')

lemma L43_mono (isAnd : Bool) (inputs : List ((X → Bool) → Bool)) (x : X → Bool) (i : ℕ) :
    (isAnd = true → abstractPrefix isAnd inputs (i + 1) x = true →
      abstractPrefix isAnd inputs i x = true) ∧
    (isAnd = false → abstractPrefix isAnd inputs i x = true →
      abstractPrefix isAnd inputs (i + 1) x = true) := by
  have hsub : inputs.take i ⊆ inputs.take (i + 1) :=
    (List.take_prefix_take_left (by omega)).subset
  constructor
  · rintro rfl h
    simp only [abstractPrefix, if_true, List.all_eq_true] at h ⊢
    exact fun f hf => h f (hsub hf)
  · rintro rfl h
    simp only [abstractPrefix, Bool.false_eq_true, if_false, List.any_eq_true] at h ⊢
    obtain ⟨f, hf, hfx⟩ := h
    exact ⟨f, hsub hf, hfx⟩

lemma L43_incr_sq (isAnd : Bool) (inputs : List ((X → Bool) → Bool)) (x : X → Bool) (i : ℕ) :
    prefixIncrement isAnd inputs (i + 1) x ^ 2 =
      (if isAnd then -1 else 1) * prefixIncrement isAnd inputs (i + 1) x := by
  have hm := L43_mono isAnd inputs x i
  unfold prefixIncrement boolReal
  simp only [Nat.add_sub_cancel]
  cases isAnd <;> cases h1 : abstractPrefix _ inputs (i + 1) x <;>
    cases h2 : abstractPrefix _ inputs i x <;> simp_all

lemma L43_incr_sum_le (isAnd : Bool) (inputs : List ((X → Bool) → Bool)) (x : X → Bool)
    (t : ℕ) : ∑ i ∈ Finset.Icc 1 t, prefixIncrement isAnd inputs i x ^ 2 ≤ 1 := by
  have : ∑ i ∈ Finset.Icc 1 t, prefixIncrement isAnd inputs i x ^ 2 =
      (if isAnd then -1 else 1) * ∑ i ∈ Finset.Icc 1 t, prefixIncrement isAnd inputs i x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by rw [Finset.mem_Icc] at hi; omega⟩
    exact L43_incr_sq isAnd inputs x k
  rw [this, L43_telescope]
  unfold boolReal
  cases isAnd <;> split_ifs <;> norm_num

lemma L43_sum_a_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (isAnd : Bool)
    (inputs : List ((X → Bool) → Bool)) :
    ∑ S : Finset X, ∑ i ∈ Finset.Icc 1 inputs.length,
      fourierCoeff p (prefixIncrement isAnd inputs i) S ^ 2 ≤ 1 := by
  calc ∑ S : Finset X, ∑ i ∈ Finset.Icc 1 inputs.length,
        fourierCoeff p (prefixIncrement isAnd inputs i) S ^ 2
        = ∑ i ∈ Finset.Icc 1 inputs.length,
          ∑ S, fourierCoeff p (prefixIncrement isAnd inputs i) S ^ 2 := Finset.sum_comm
    _ = ∑ i ∈ Finset.Icc 1 inputs.length, ∑ y, weight p y *
          prefixIncrement isAnd inputs i y ^ 2 := by
          apply Finset.sum_congr rfl; intro i _
          exact L43_parseval hp hp1 _
    _ = ∑ y, weight p y * ∑ i ∈ Finset.Icc 1 inputs.length,
          prefixIncrement isAnd inputs i y ^ 2 := by
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro y _; rw [Finset.mul_sum]
    _ ≤ ∑ y : X → Bool, weight p y * 1 := by
          apply Finset.sum_le_sum; intro y _
          exact mul_le_mul_of_nonneg_left (L43_incr_sum_le isAnd inputs y _)
            (L43_weight_nonneg hp hp1 y)
    _ = 1 := by simp only [mul_one]; exact L43_weight_sum p

end Prefix

section Counting

lemma L43_card_small {α : Type*} (s : Finset α) (v : ℕ) :
    (s.powerset.filter (fun J => J.card ≤ v)).card ≤
      ∑ j ∈ Finset.range (v + 1), s.card.choose j := by
  calc _ ≤ ((Finset.range (v + 1)).biUnion (fun j => s.powersetCard j)).card := by
        apply Finset.card_le_card
        intro J hJ
        simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
        exact ⟨J.card, by omega, hJ.1, rfl⟩
    _ ≤ ∑ j ∈ Finset.range (v + 1), (s.powersetCard j).card := Finset.card_biUnion_le
    _ = _ := by simp_rw [Finset.card_powersetCard]

lemma L43_choose_sum_le (n v : ℕ) :
    ∑ j ∈ Finset.range (v + 1), n.choose j ≤ (n + 1) ^ v := by
  rw [add_pow]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mem_range] at hj
  simp only [one_pow, mul_one]
  calc n.choose j ≤ n ^ j := Nat.choose_le_pow n j
    _ ≤ n ^ j * v.choose j := Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega))

lemma L43_choose_sum_exp (D v : ℕ) (hv : 1 ≤ v) (hD : v ≤ D) :
    ∑ j ∈ Finset.range (v + 1), (D.choose j : ℝ) ≤ (Real.exp 1 * D / v) ^ v := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  set q : ℝ := v / D with hq
  have hq0 : 0 < q := div_pos hvpos hDpos
  have hq1 : q ≤ 1 := by rw [hq, div_le_one hDpos]; exact_mod_cast hD
  have h1 : q ^ v * ∑ j ∈ Finset.range (v + 1), (D.choose j : ℝ) ≤ Real.exp v := by
    calc q ^ v * ∑ j ∈ Finset.range (v + 1), (D.choose j : ℝ)
        ≤ ∑ j ∈ Finset.range (v + 1), q ^ j * 1 ^ (D - j) * (D.choose j : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro j hj
          rw [Finset.mem_range] at hj
          rw [one_pow, mul_one]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0.le hq1 (by omega))
            (Nat.cast_nonneg _)
      _ ≤ ∑ j ∈ Finset.range (D + 1), q ^ j * 1 ^ (D - j) * (D.choose j : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_subset_range.mpr (by omega)
          · intro j _ _; positivity
      _ = (q + 1) ^ D := (add_pow q 1 D).symm
      _ ≤ Real.exp q ^ D := by
          apply pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp q)
      _ = Real.exp v := by
          rw [← Real.exp_nat_mul, hq]; congr 1; field_simp
  have h2 : Real.exp v = Real.exp 1 ^ v := by rw [← Real.exp_nat_mul, mul_one]
  have hqv : 0 < q ^ v := pow_pos hq0 v
  calc _ ≤ Real.exp v / q ^ v := by rw [le_div_iff₀ hqv, mul_comm]; exact h1
    _ = _ := by rw [h2, hq, div_pow, div_pow, mul_pow]; field_simp

lemma L43_descFact_ge (m v : ℕ) (hvm : v ≤ m) :
    (v.factorial : ℝ) * ((m : ℝ) / v) ^ v ≤ (m.descFactorial v : ℝ) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have key : v.factorial * m ^ v ≤ m.descFactorial v * v ^ v := by
    rw [← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_eq_prod_range]
    have e1 : (∏ i ∈ Finset.range v, (v - i)) * m ^ v =
        ∏ i ∈ Finset.range v, (m * (v - i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, mul_comm]
    have e2 : (∏ i ∈ Finset.range v, (m - i)) * v ^ v =
        ∏ i ∈ Finset.range v, ((m - i) * v) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [e1, e2]
    apply Finset.prod_le_prod' 
    intro i hi
    rw [Finset.mem_range] at hi
    zify [show i ≤ v by omega, show i ≤ m by omega]
    nlinarith
  have key' : (v.factorial : ℝ) * (m : ℝ) ^ v ≤ (m.descFactorial v : ℝ) * (v : ℝ) ^ v := by
    exact_mod_cast key
  rw [div_pow, mul_div_assoc', div_le_iff₀ (pow_pos hvpos v)]
  exact key'

lemma L43_low_count (m v D : ℕ) (hv : 1 ≤ v) (hvm : v ≤ m) (hD : v ≤ D) (hm : 0 < m) :
    (v.factorial : ℝ) * ∑ j ∈ Finset.range (v + 1), (D.choose j : ℝ) ≤
      (m.descFactorial v : ℝ) * (Real.exp 1 * D / m) ^ v := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  calc _ ≤ (v.factorial : ℝ) * (Real.exp 1 * D / v) ^ v :=
        mul_le_mul_of_nonneg_left (L43_choose_sum_exp D v hv hD) (by positivity)
    _ = (v.factorial : ℝ) * ((m : ℝ) / v) ^ v * (Real.exp 1 * D / m) ^ v := by
        rw [mul_assoc, ← mul_pow]; congr 2; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (L43_descFact_ge m v hvm) (by positivity)

lemma L43_emb_count (m v : ℕ) (B : Finset (Fin m)) :
    (Finset.univ.filter (fun ι : Fin v ↪ Fin m => Finset.univ.map ι = B)).card ≤
      v.factorial := by
  by_cases hB : B.card = v
  · calc _ ≤ (Finset.univ.filter (fun ι : Fin v ↪ Fin m => ∀ k, ι k ∈ B)).card := by
          apply Finset.card_le_card
          intro ι hι
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hι ⊢
          intro k; rw [← hι]; simp
      _ = Fintype.card {ι : Fin v ↪ Fin m // ∀ k, ι k ∈ B} := (Fintype.card_subtype _).symm
      _ ≤ Fintype.card (Fin v ↪ B) := by
          apply Fintype.card_le_of_injective
            (fun ι => ⟨fun k => ⟨ι.1 k, ι.2 k⟩, fun a b h => ι.1.injective (by
              simpa using congrArg Subtype.val h)⟩)
          intro a b h
          apply Subtype.ext
          ext k
          exact congrArg (fun f : Fin v ↪ B => ((f k).1 : ℕ)) h
      _ = v.factorial := by
          rw [Fintype.card_embedding_eq, Fintype.card_coe, Fintype.card_fin, hB,
            Nat.descFactorial_self]
  · have : Finset.univ.filter (fun ι : Fin v ↪ Fin m => Finset.univ.map ι = B) = ∅ := by
      apply Finset.filter_false_of_mem
      intro ι _ h
      apply hB; rw [← h]; simp
    rw [this]; simp

end Counting

section Main

/-- edge covers of the image hypergraph with at most v edges -/
def L43_covers {v m r : ℕ} (H₀ : Finset (Edge v r)) (ι : Fin v ↪ Fin m) :
    Finset (Finset (Edge m r)) :=
  (H₀.image (mapEdge ι)).powerset.filter
    (fun J => Finset.univ.map ι ⊆ verticesOf J ∧ J.card ≤ v)

lemma L43_verticesOf_sub {v m r : ℕ} (H₀ : Finset (Edge v r)) (ι : Fin v ↪ Fin m)
    (J : Finset (Edge m r)) (hJ : J ⊆ H₀.image (mapEdge ι)) :
    verticesOf J ⊆ Finset.univ.map ι := by
  intro u hu
  simp only [verticesOf, Finset.mem_biUnion] at hu
  obtain ⟨e, he, hu⟩ := hu
  exact (imageHypergraph H₀ ι).supported e (hJ he) hu

lemma L43_fixed {v m r : ℕ} (hv : 1 ≤ v) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (H₀ : Finset (Edge v r)) (isAnd : Bool) (inputs : List ((Edge m r → Bool) → Bool))
    (ι : Fin v ↪ Fin m) :
    probability p (fun G => ∃ j : ℕ, 1 ≤ j ∧ j ≤ inputs.length ∧
      spans G (imageHypergraph H₀ ι) (boolReal (abstractPrefix isAnd inputs j))) ≤
    (p⁻¹) ^ H₀.card * ∑ S : Finset (Edge m r),
      (∑ i ∈ Finset.Icc 1 inputs.length,
        fourierCoeff p (prefixIncrement isAnd inputs i) S ^ 2) *
      (((L43_covers H₀ ι).filter (fun J => J ⊆ S)).card : ℝ) := by
  set EH := H₀.image (mapEdge ι) with hEH
  set I := Finset.Icc 1 inputs.length
  set g := prefixIncrement isAnd inputs
  have hpinv : 1 ≤ p⁻¹ := one_le_inv₀ hp |>.mpr hp1.le
  calc _ ≤ ∑ J ∈ L43_covers H₀ ι, probability p (fun G => ∃ y : Edge m r → Bool,
        (∀ e, G e = true → y e = true) ∧
        (∀ e, e ∉ EH → y e = G e) ∧ (∀ e ∈ J, G e = false ∧ y e = false) ∧
        1 ≤ ∑ i ∈ I, L43_delta J (g i) y ^ 2) := by
        apply L43_prob_union hp hp1
        intro G hev
        obtain ⟨j, hj1, hjt, hsp⟩ := hev
        obtain ⟨J, hJE, hJV, hJc, y, hy1, hy2, hy3, hy4⟩ := L43_span_cover G _ _ hsp
        have hJmem : J ∈ L43_covers H₀ ι := by
          simp only [L43_covers, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨hJE, hJV, ?_⟩
          have : (imageHypergraph H₀ ι).vertices.card = v := by
            simp [imageHypergraph]
          omega
        have hJne : J.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          rintro rfl
          have hne : (imageHypergraph H₀ ι).vertices.Nonempty := by
            simp only [imageHypergraph, Finset.map_nonempty, Finset.univ_nonempty_iff]
            exact ⟨⟨0, by omega⟩⟩
          obtain ⟨u, hu⟩ := hne
          have := hJV hu
          simp [verticesOf] at this
        exact ⟨J, hJmem, y, hy1, hy2, hy3, L43_prefix_sq isAnd inputs J hJne y j hj1 hjt hy4⟩
    _ ≤ ∑ J ∈ L43_covers H₀ ι, (p⁻¹) ^ EH.card *
        ∑ i ∈ I, ∑ S, (if J ⊆ S then fourierCoeff p (g i) S ^ 2 else 0) := by
        apply Finset.sum_le_sum; intro J hJ
        have hJE : J ⊆ EH := by
          simp only [L43_covers, Finset.mem_filter, Finset.mem_powerset] at hJ; exact hJ.1
        convert L43_probEJ' hp hp1 EH J hJE I g
        all_goals exact rfl
    _ ≤ ∑ J ∈ L43_covers H₀ ι, (p⁻¹) ^ H₀.card *
        ∑ S, (if J ⊆ S then ∑ i ∈ I, fourierCoeff p (g i) S ^ 2 else 0) := by
        apply Finset.sum_le_sum; intro J _
        have hsw : ∑ i ∈ I, ∑ S, (if J ⊆ S then fourierCoeff p (g i) S ^ 2 else 0) =
            ∑ S, (if J ⊆ S then ∑ i ∈ I, fourierCoeff p (g i) S ^ 2 else 0) := by
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro S _
          split_ifs <;> simp
        rw [hsw]
        apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_right₀ hpinv Finset.card_image_le
        · apply Finset.sum_nonneg; intro S _
          split_ifs
          · exact Finset.sum_nonneg fun i _ => sq_nonneg _
          · exact le_rfl
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl; intro S _
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_comm]

lemma L43_low_sum {v m r : ℕ} (H₀ : Finset (Edge v r)) (D : ℕ) (S : Finset (Edge m r))
    (hS : S.card ≤ D) :
    ∑ ι : Fin v ↪ Fin m, ((L43_covers H₀ ι).filter (fun J => J ⊆ S)).card ≤
      v.factorial * ∑ j ∈ Finset.range (v + 1), D.choose j := by
  set P := S.powerset.filter (fun J => J.card ≤ v)
  calc _ ≤ ∑ ι : Fin v ↪ Fin m, (P.filter (fun J => verticesOf J = Finset.univ.map ι)).card := by
        apply Finset.sum_le_sum; intro ι _
        apply Finset.card_le_card
        intro J hJ
        simp only [L43_covers, Finset.mem_filter, Finset.mem_powerset] at hJ
        simp only [P, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨⟨hJ.2, hJ.1.2.2⟩, Finset.Subset.antisymm
          (L43_verticesOf_sub H₀ ι J hJ.1.1) hJ.1.2.1⟩
    _ = ∑ J ∈ P, (Finset.univ.filter
          (fun ι : Fin v ↪ Fin m => Finset.univ.map ι = verticesOf J)).card := by
        simp_rw [Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro J _
        apply Finset.sum_congr rfl; intro ι _
        simp only [eq_comm]
    _ ≤ ∑ J ∈ P, v.factorial := Finset.sum_le_sum fun J _ => L43_emb_count m v _
    _ = P.card * v.factorial := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (∑ j ∈ Finset.range (v + 1), S.card.choose j) * v.factorial :=
        Nat.mul_le_mul_right _ (L43_card_small S v)
    _ ≤ (∑ j ∈ Finset.range (v + 1), D.choose j) * v.factorial := by
        apply Nat.mul_le_mul_right
        exact Finset.sum_le_sum fun j _ => Nat.choose_le_choose j hS
    _ = _ := mul_comm _ _

lemma L43_high {v m r : ℕ} (H₀ : Finset (Edge v r)) (ι : Fin v ↪ Fin m)
    (S : Finset (Edge m r)) :
    ((L43_covers H₀ ι).filter (fun J => J ⊆ S)).card ≤ (H₀.card + 1) ^ v := by
  calc _ ≤ (L43_covers H₀ ι).card := Finset.card_filter_le _ _
    _ ≤ ((H₀.image (mapEdge ι)).powerset.filter (fun J => J.card ≤ v)).card := by
        apply Finset.card_le_card
        intro J hJ
        simp only [L43_covers, Finset.mem_filter] at hJ ⊢
        exact ⟨hJ.1, hJ.2.2⟩
    _ ≤ ∑ j ∈ Finset.range (v + 1), (H₀.image (mapEdge ι)).card.choose j := L43_card_small _ v
    _ ≤ ((H₀.image (mapEdge ι)).card + 1) ^ v := L43_choose_sum_le _ v
    _ ≤ (H₀.card + 1) ^ v := Nat.pow_le_pow_left (by
        have := Finset.card_image_le (s := H₀) (f := mapEdge ι); omega) v

end Main

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution (m r v : ℕ) (hv : 1 ≤ v) (hvm : v < m)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (H₀ : Finset (Edge v r))
    (isAnd : Bool) (inputs : List ((Edge m r → Bool) → Bool))
    (D : ℕ) (hD : v ≤ D) :
    prefixSpanningProbability p H₀ isAnd inputs ≤
      p ^ (-(H₀.card : ℝ)) *
        ((Real.exp 1 * (D : ℝ) / (m : ℝ)) ^ v +
          ((H₀.card : ℝ) + 1) ^ v *
            ∑ i ∈ Finset.Icc 1 inputs.length,
              fourierTailGT p (prefixIncrement isAnd inputs i) D) := by
  set a : Finset (Edge m r) → ℝ := fun S => ∑ i ∈ Finset.Icc 1 inputs.length,
    fourierCoeff p (prefixIncrement isAnd inputs i) S ^ 2 with ha
  set c₁ : ℝ := (Real.exp 1 * (D : ℝ) / (m : ℝ)) ^ v with hc₁def
  set c₂ : ℝ := ((H₀.card : ℝ) + 1) ^ v with hc₂def
  set M : ℝ := (Fintype.card (Fin v ↪ Fin m) : ℝ) with hMdef
  set N : (Fin v ↪ Fin m) → Finset (Edge m r) → ℝ :=
    fun ι S => (((L43_covers H₀ ι).filter (fun J => J ⊆ S)).card : ℝ) with hN
  have hM : M = (m.descFactorial v : ℝ) := by
    rw [hMdef, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
  have hMpos : 0 < M := by
    rw [hM]
    have : m.descFactorial v ≠ 0 := by
      rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
    exact_mod_cast Nat.pos_of_ne_zero this
  have ha0 : ∀ S, 0 ≤ a S := fun S => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hNS : ∀ S : Finset (Edge m r), M⁻¹ * ∑ ι, N ι S ≤
      c₁ + c₂ * (if D < S.card then 1 else 0) := by
    intro S
    by_cases hS : D < S.card
    · rw [if_pos hS, mul_one]
      have h1 : ∑ ι, N ι S ≤ M * c₂ := by
        calc ∑ ι, N ι S ≤ ∑ _ι : Fin v ↪ Fin m, c₂ := by
              apply Finset.sum_le_sum; intro ι _
              simp only [hN, hc₂def]
              exact_mod_cast L43_high H₀ ι S
          _ = M * c₂ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc M⁻¹ * ∑ ι, N ι S ≤ M⁻¹ * (M * c₂) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hMpos.le)
        _ = c₂ := by field_simp
        _ ≤ c₁ + c₂ := by linarith
    · rw [if_neg hS, mul_zero, add_zero]
      have h1 : ∑ ι, N ι S ≤ (v.factorial : ℝ) * ∑ j ∈ Finset.range (v + 1), (D.choose j : ℝ) := by
        have := L43_low_sum H₀ D S (by omega) (m := m)
        simp only [hN]
        exact_mod_cast this
      have h2 := L43_low_count m v D hv hvm.le hD (by omega)
      rw [inv_mul_le_iff₀ hMpos, hM]
      linarith
  have hsum_a : ∑ S, a S ≤ 1 := L43_sum_a_le hp hp1 isAnd inputs
  have htail : ∑ S, (if D < S.card then a S else 0) = ∑ i ∈ Finset.Icc 1 inputs.length,
      fourierTailGT p (prefixIncrement isAnd inputs i) D := by
    unfold fourierTailGT
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro S _
    split_ifs <;> simp [ha]
  have hpow : p ^ (-(H₀.card : ℝ)) = (p⁻¹) ^ H₀.card := by
    rw [Real.rpow_neg hp.le, Real.rpow_natCast, inv_pow]
  have hpp : 0 ≤ (p⁻¹) ^ H₀.card := by positivity
  unfold prefixSpanningProbability jointProbability
  rw [hpow]
  calc M⁻¹ * ∑ ι, _ ≤ M⁻¹ * ∑ ι, (p⁻¹) ^ H₀.card * ∑ S, a S * N ι S := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hMpos.le)
        apply Finset.sum_le_sum; intro ι _
        exact L43_fixed hv p hp hp1 H₀ isAnd inputs ι
    _ = (p⁻¹) ^ H₀.card * ∑ S, a S * (M⁻¹ * ∑ ι, N ι S) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro S _
        apply Finset.sum_congr rfl; intro ι _
        ring
    _ ≤ (p⁻¹) ^ H₀.card * ∑ S, a S * (c₁ + c₂ * (if D < S.card then 1 else 0)) := by
        apply mul_le_mul_of_nonneg_left _ hpp
        exact Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hNS S) (ha0 S)
    _ = (p⁻¹) ^ H₀.card * (c₁ * ∑ S, a S + c₂ * ∑ S, (if D < S.card then a S else 0)) := by
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro S _
        split_ifs <;> ring
    _ ≤ (p⁻¹) ^ H₀.card * (c₁ + c₂ * ∑ i ∈ Finset.Icc 1 inputs.length,
          fourierTailGT p (prefixIncrement isAnd inputs i) D) := by
        rw [htail]
        apply mul_le_mul_of_nonneg_left _ hpp
        have : c₁ * ∑ S, a S ≤ c₁ := mul_le_of_le_one_right hc₁ hsum_a
        linarith

