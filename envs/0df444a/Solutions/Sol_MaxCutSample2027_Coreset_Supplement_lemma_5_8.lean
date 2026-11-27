-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.lemma_5_8
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T01:04:06.947271+00:00
-- url     : https://prove2.me/submissions/55d778a6-6412-4448-8936-dbd2da3578a4

import Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_A_4
import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rSigned
open scoped BigOperators
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 700000

open MaxCutSample2027
open MaxCutSample2027.Coreset
open MaxCutSample2027.Coreset.Supplement

private theorem empirical_sum {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (x : Fin k → V) (f : V → ℝ) : ∑ v, empirical x v * f v = (∑ i, f (x i)) / (k : ℝ) := by
  calc
    _ = (∑ v, ((Finset.univ.filter (fun i => x i = v)).card : ℝ) * f v) / (k : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun v _ => by simp only [empirical]; ring
    _ = _ := by
      congr 1
      rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := x) (fun _ _ => Finset.mem_univ _) (fun i => f (x i))]
      apply Finset.sum_congr rfl
      intro v _
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

private theorem empirical_probability {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (hk : 1 ≤ k) (x : Fin k → V) : IsProbabilityVector (empirical x) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨fun v => div_nonneg (Nat.cast_nonneg _) hk'.le, ?_⟩
  simpa [hk'.ne'] using empirical_sum x (fun _ => 1)

private theorem sample_le {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (f g : (Fin k → V) → ℝ) (h : ∀ x, f x ≤ g x) :
    sampleAverage p k f ≤ sampleAverage p k g := by
  unfold sampleAverage
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x)
    (Finset.prod_nonneg fun i _ => hp (x i))

private theorem sample_smul {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (a : ℝ) (f : (Fin k → V) → ℝ) : sampleAverage p k (fun x => a * f x) = a * sampleAverage p k f := by
  unfold sampleAverage
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
private theorem sample_product {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ) (f : Fin k → V → ℝ) :
    sampleAverage p k (fun x => ∏ i, f i (x i)) = ∏ i, ∑ v, p v * f i v := by
  unfold sampleAverage sampleWeight
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i v => p v * f i v)).symm

private theorem sample_one {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ} (hp : IsProbabilityVector p)
    (i : Fin k) (f : V → ℝ) : sampleAverage p k (fun x => f (x i)) = ∑ v, p v * f v := by
  let h : Fin k → V → ℝ := Function.update (fun _ _ => 1) i f
  have prod (x : Fin k → V) : (∏ j, h j (x j)) = f (x i) := by
    rw [Finset.prod_eq_single i]
    · simp [h]
    · intro j _ hji
      simp [h, hji]
    · simp
  have e := sample_product p h
  simp_rw [prod] at e
  rw [e, Finset.prod_eq_single i]
  · simp [h]
  · intro j _ hji
    simp [h, hji, hp.2]
  · simp

private theorem sample_two {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ} (hp : IsProbabilityVector p)
    (i j : Fin k) (hij : i ≠ j) (f g : V → ℝ) :
    sampleAverage p k (fun x => f (x i) * g (x j)) = (∑ v, p v * f v) * ∑ v, p v * g v := by
  let h : Fin k → V → ℝ := Function.update (Function.update (fun _ _ => 1) i f) j g
  have prod (x : Fin k → V) : (∏ l, h l (x l)) = f (x i) * g (x j) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Finset.prod_eq_single i]
    · simp [h, hij]
    · intro l hl hli
      simp [h, hli, (Finset.mem_erase.mp hl).1]
    · simp [hij]
  have e := sample_product p h
  simp_rw [prod] at e
  rw [e, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Finset.prod_eq_single i]
  · simp [h, hij]
  · intro l hl hli
    simp [h, hli, (Finset.mem_erase.mp hl).1, hp.2]
  · simp [hij]

private theorem sample_const {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : IsProbabilityVector p) (a : ℝ) : sampleAverage p k (fun _ => a) = a := by
  have h := sample_product (k := k) p (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one, hp.2] at h
  change (∑ x : Fin k → V, sampleWeight p x * 1) = 1 at h
  simp only [mul_one] at h
  unfold sampleAverage
  rw [← Finset.sum_mul, h, one_mul]

private theorem sample_sum {V I : Type*} [Fintype V] [Fintype I] {k : ℕ} (p : V → ℝ)
    (f : I → (Fin k → V) → ℝ) : sampleAverage p k (fun x => ∑ i, f i x) = ∑ i, sampleAverage p k (f i) := by
  simp only [sampleAverage, Finset.mul_sum]
  exact Finset.sum_comm

private theorem sample_empirical {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} {p : V → ℝ}
    (hp : IsProbabilityVector p) (hk : 1 ≤ k) (v : V) : sampleAverage p k (fun x => empirical x v) = p v := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have empirical_indicator (x : Fin k → V) : empirical x v = ((∑ i, if x i = v then 1 else 0) : ℝ) / (k : ℝ) := by
    rw [empirical, Finset.sum_boole]
  have h (i : Fin k) : sampleAverage p k (fun x => if x i = v then 1 else 0) = p v := by
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using
      sample_one hp i (fun u => if u = v then 1 else 0)
  simp only [empirical_indicator, div_eq_inv_mul, sample_smul, sample_sum, h, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hk'.ne']

private theorem sample_add {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (f g : (Fin k → V) → ℝ) : sampleAverage p k (fun x => f x + g x) = sampleAverage p k f + sampleAverage p k g := by
  simp only [sampleAverage, mul_add, Finset.sum_add_distrib]
private theorem sign_flip_value (b : Bool) : signValue (!b) = -signValue b := by cases b <;> norm_num [signValue]
private theorem abs_sign_value (b : Bool) : |signValue b| = 1 := by cases b <;> norm_num [signValue]

private def flipCoord {k : ℕ} (i : Fin k) (σ : Fin k → Bool) : Fin k → Bool :=
  Function.update σ i (!σ i)

private theorem flipCoord_involutive {k : ℕ} (i : Fin k) : Function.Involutive (flipCoord i) := by
  intro σ
  funext j
  by_cases h : j = i
  · subst j; simp [flipCoord]
  · simp [flipCoord, Function.update_of_ne h]

private theorem sign_card (k : ℕ) : (Fintype.card (Fin k → Bool) : ℝ) = (2 : ℝ) ^ k := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
  norm_num

private theorem sign_product_sum {k : ℕ} (i j : Fin k) :
    (∑ σ : Fin k → Bool, signValue (σ i) * signValue (σ j)) = if i = j then (2 : ℝ) ^ k else 0 := by
  classical
  by_cases h : i = j
  · subst j
    have value (b : Bool) : signValue b * signValue b = 1 := by cases b <;> norm_num [signValue]
    simp only [ite_true, value, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sign_card]
  · rw [if_neg h]
    let perm : (Fin k → Bool) ≃ (Fin k → Bool) :=
      ⟨flipCoord i, flipCoord i, flipCoord_involutive i, flipCoord_involutive i⟩
    let f (σ : Fin k → Bool) := signValue (σ i) * signValue (σ j)
    have hsum : (∑ σ, f (flipCoord i σ)) = ∑ σ, f σ := Fintype.sum_equiv perm _ _ (fun _ => rfl)
    have neg (σ : Fin k → Bool) : f (flipCoord i σ) = -f σ := by
      simp [f, flipCoord, Function.update_of_ne (Ne.symm h), sign_flip_value]
    simp only [neg, Finset.sum_neg_distrib] at hsum
    change (∑ σ, f σ) = 0
    linarith

private theorem sign_squared {k : ℕ} (a : Fin k → ℝ) :
    (∑ σ : Fin k → Bool, (∑ i, signValue (σ i) * a i) ^ 2) = (2 : ℝ) ^ k * ∑ i, a i ^ 2 := by
  classical
  calc
    _ = ∑ σ : Fin k → Bool, ∑ i, ∑ j,
          (signValue (σ i) * signValue (σ j)) * (a i * a j) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, ∑ j, (∑ σ : Fin k → Bool, signValue (σ i) * signValue (σ j)) * (a i * a j) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      simp only [sign_product_sum, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, pow_two]

private theorem sqrt_average_le {I : Type*} [Fintype I] (w b : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, w i * Real.sqrt (b i)) ≤ Real.sqrt ((∑ i, w i) * ∑ i, w i * b i) := by
  have h : (∑ i, w i * Real.sqrt (b i)) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * b i := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (hb i))
    intro i _
    rw [mul_pow, Real.sq_sqrt (hb i)]
    ring_nf
    exact le_rfl
  have hnonneg : 0 ≤ (∑ i, w i) * ∑ i, w i * b i :=
    mul_nonneg (Finset.sum_nonneg fun i _ => hw i) (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hb i))
  exact (sq_le_sq₀ (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)).mp (by simpa only [Real.sq_sqrt hnonneg] using h)

private theorem sign_absolute {k : ℕ} (a : Fin k → ℝ) :
    signAverage k (fun σ => |∑ i, signValue (σ i) * a i|) ≤ Real.sqrt (∑ i, a i ^ 2) := by
  let c : ℝ := (2 : ℝ) ^ k
  have hc : 0 < c := by dsimp [c]; positivity
  have hb := sqrt_average_le (fun _ : Fin k → Bool => 1 / c)
    (fun σ => (∑ i, signValue (σ i) * a i) ^ 2) (fun _ => by positivity) (fun _ => sq_nonneg _)
  simp only [Real.sqrt_sq_eq_abs, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, sign_card, sign_squared] at hb
  have hden : (2 : ℝ) ^ k * (1 / c) = 1 := mul_div_cancel₀ _ hc.ne'
  have hden' : (1 / c) * (2 : ℝ) ^ k = 1 := by rw [mul_comm]; exact hden
  rw [hden, one_mul, ← mul_assoc (1 / c) ((2 : ℝ) ^ k), hden', one_mul] at hb
  change (∑ σ : Fin k → Bool, |∑ i, signValue (σ i) * a i|) / c ≤ _
  convert hb using 1 <;> first | rfl | ring

private theorem signAverage_sum' {k : ℕ} {I : Type*} [Fintype I] (f : I → (Fin k → Bool) → ℝ) :
    signAverage k (fun σ => ∑ i, f i σ) = ∑ i, signAverage k (f i) := by
  unfold signAverage
  rw [← Finset.sum_div, Finset.sum_comm]

private theorem sign_smul {k : ℕ} (c : ℝ) (f : (Fin k → Bool) → ℝ) :
    signAverage k (fun σ => c * f σ) = c * signAverage k f := by
  unfold signAverage
  rw [← Finset.mul_sum]
  ring

private theorem sign_le {k : ℕ} {f g : (Fin k → Bool) → ℝ} (h : ∀ σ, f σ ≤ g σ) :
    signAverage k f ≤ signAverage k g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => h σ) (by positivity)
private theorem matrix_sign_parts {k r : ℕ} (f : (Fin k → Bool) → ℝ)
    (g : (Fin k → Fin r → Bool) → ℝ) :
    matrixSignAverage k (r + 1) (fun σ => f (fun i => σ i 0) + g (fun i j => σ i j.succ)) =
      signAverage k f + matrixSignAverage k r g := by
  classical
  let e : (Fin k → Fin (r + 1) → Bool) ≃ (Fin k → Bool) × (Fin k → Fin r → Bool) :=
    { toFun := fun σ => (fun i => σ i 0, fun i j => σ i j.succ)
      invFun := fun p i => Fin.cons (p.1 i) (p.2 i)
      left_inv := by
        intro σ
        funext i j
        exact Fin.cases rfl (fun _ => rfl) j
      right_inv := by rintro ⟨x, y⟩; rfl }
  have sc : (Fintype.card (Fin k → Bool) : ℝ) = (2 : ℝ) ^ k := by simp
  have mc : (Fintype.card (Fin k → Fin r → Bool) : ℝ) = (2 : ℝ) ^ (k * r) := by
    simp [pow_mul, Nat.mul_comm k r]
  have fsum : (∑ x : (Fin k → Bool) × (Fin k → Fin r → Bool), f x.1) =
      (∑ x, f x) * (2 : ℝ) ^ (k * r) := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => mul_comm ((2 : ℝ) ^ (k * r)) (f σ)
  have gsum : (∑ x : (Fin k → Bool) × (Fin k → Fin r → Bool), g x.2) =
      (∑ x, g x) * (2 : ℝ) ^ k := by
    rw [Fintype.sum_prod_type]
    simp [nsmul_eq_mul, mul_comm]
  have hsum : (∑ σ : Fin k → Fin (r + 1) → Bool, (f (fun i => σ i 0) + g (fun i j => σ i j.succ))) =
      ∑ x : (Fin k → Bool) × (Fin k → Fin r → Bool), (f x.1 + g x.2) := by
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  unfold matrixSignAverage signAverage
  simp only []
  rw [hsum, Finset.sum_add_distrib,
    fsum, gsum, Nat.mul_add, Nat.mul_one, pow_add]
  have a : (2 : ℝ) ^ (k * r) ≠ 0 := by positivity
  have b : (2 : ℝ) ^ k ≠ 0 := by positivity
  field_simp

private theorem matrix_sign_le {k r : ℕ} {f g : (Fin k → Fin r → Bool) → ℝ}
    (h : ∀ σ, f σ ≤ g σ) : matrixSignAverage k r f ≤ matrixSignAverage k r g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => h σ) (by positivity)

private theorem matrix_sign_sum {k r : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → (Fin k → Fin r → Bool) → ℝ) :
    matrixSignAverage k r (fun σ => ∑ i, f i σ) =
      ∑ i, matrixSignAverage k r (f i) := by
  unfold matrixSignAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    (r : ℕ) (hr : 2 ≤ r)
    : expectedSignedR r k (K A p) p ≤
      6 * Real.sqrt 2 * H A p * Real.sqrt (Real.log (2 * (r : ℝ)) / (k : ℝ)) := by
  classical
  let L := K A p
  let μ (v : V) := ∑ u, p u * L u v ^ 2
  let B (x : Fin k → V) (v : V) := ∑ i, L (x i) v ^ 2
  let f (x : Fin k → V) (v : V) := Real.sqrt (B x v) / (k : ℝ)
  let g (v : V) := Real.sqrt (μ v) / Real.sqrt (k : ℝ)
  have hpp : IsProbabilityVector p := ⟨fun v => (hp.1 v).le, hp.2⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hB (x : Fin k → V) (v : V) : 0 ≤ B x v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hμ (v : V) : 0 ≤ μ v := Finset.sum_nonneg fun u _ => mul_nonneg (hpp.1 u) (sq_nonneg _)
  have hweight (x : Fin k → V) : 0 ≤ sampleWeight p x := Finset.prod_nonneg fun i _ => hpp.1 (x i)
  have normalize (v : V) : Real.sqrt ((k : ℝ) * μ v) / (k : ℝ) = g v := by
    dsimp only [g]
    rw [Real.sqrt_mul hk'.le]
    have hne := (Real.sqrt_pos.2 hk').ne'
    field_simp [hk'.ne', hne]
    rw [Real.sq_sqrt hk'.le, mul_comm]
  have ordinary (v : V) : sampleAverage p k (fun x => f x v) ≤ g v := by
    have total : (∑ x : Fin k → V, sampleWeight p x) = 1 := by
      simpa only [sampleAverage, mul_one] using sample_const (k := k) hpp 1
    have moment : (∑ x : Fin k → V, sampleWeight p x * B x v) = (k : ℝ) * μ v := by
      change sampleAverage p k (fun x => ∑ i, L (x i) v ^ 2) = _
      rw [sample_sum]
      have h (i : Fin k) : sampleAverage p k (fun x => L (x i) v ^ 2) = μ v :=
        sample_one hpp i (fun u => L u v ^ 2)
      simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h := sqrt_average_le (sampleWeight p) (fun x => B x v) hweight (fun x => hB x v)
    rw [total, moment, one_mul] at h
    change (∑ x : Fin k → V, sampleWeight p x * (Real.sqrt (B x v) / (k : ℝ))) ≤ g v
    simp only [← mul_div_assoc, ← Finset.sum_div]
    rw [← normalize v]
    exact div_le_div_of_nonneg_right h hk'.le
  have restricted (j : Fin k) (v : V) :
      sampleAverage p k (fun x => (if x j = v then 1 else 0) * f x v) ≤ p v * g v := by
    let indicator (u : V) : ℝ := if u = v then 1 else 0
    let weight (x : Fin k → V) := sampleWeight p x * indicator (x j)
    have indicator_nonneg (u : V) : 0 ≤ indicator u := by dsimp [indicator]; split <;> norm_num
    have weight_nonneg (x : Fin k → V) : 0 ≤ weight x := mul_nonneg (hweight x) (indicator_nonneg _)
    have eval_indicator : ∑ u, p u * indicator u = p v := by
      simp [indicator, mul_ite]
    have total : (∑ x : Fin k → V, weight x) = p v := by
      change sampleAverage p k (fun x => indicator (x j)) = p v
      rw [sample_one hpp, eval_indicator]
    have moment_term (i : Fin k) :
        sampleAverage p k (fun x => indicator (x j) * L (x i) v ^ 2) ≤ p v * μ v := by
      by_cases h : i = j
      · subst i
        have hz (x : Fin k → V) : indicator (x j) * L (x j) v ^ 2 = 0 := by
          by_cases hx : x j = v <;> simp [indicator, L, K, hx, hA.2.1]
        simp only [hz, sample_const hpp]
        exact mul_nonneg (hpp.1 v) (hμ v)
      · rw [sample_two hpp j i (Ne.symm h) indicator (fun u => L u v ^ 2), eval_indicator]
    have moment : (∑ x : Fin k → V, weight x * B x v) ≤ (k : ℝ) * (p v * μ v) := by
      change (∑ x : Fin k → V, (sampleWeight p x * indicator (x j)) * ∑ i, L (x i) v ^ 2) ≤ _
      simp only [mul_assoc, Finset.mul_sum]
      rw [Finset.sum_comm]
      calc
        _ ≤ ∑ _i : Fin k, p v * μ v := Finset.sum_le_sum fun i _ => moment_term i
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have cond := sqrt_average_le weight (fun x => B x v) weight_nonneg (fun x => hB x v)
    rw [total] at cond
    have sqbound := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left moment (hpp.1 v))
    have factor : Real.sqrt (p v * ((k : ℝ) * (p v * μ v))) = p v * Real.sqrt ((k : ℝ) * μ v) := by
      rw [show p v * ((k : ℝ) * (p v * μ v)) = p v ^ 2 * ((k : ℝ) * μ v) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hpp.1 v)]
    rw [factor] at sqbound
    have h := div_le_div_of_nonneg_right (cond.trans sqbound) hk'.le
    simp only [mul_div_assoc, normalize] at h
    simpa only [sampleAverage, f, ← mul_div_assoc, weight, mul_assoc, indicator, Finset.sum_div] using h
  have self_sample (v : V) : sampleAverage p k (fun x => empirical x v * f x v) ≤ p v * g v := by
    have empirical_indicator (x : Fin k → V) : empirical x v = ((∑ i, if x i = v then 1 else 0) : ℝ) / (k : ℝ) := by
      rw [empirical, Finset.sum_boole]
    simp only [empirical_indicator, div_eq_inv_mul, mul_assoc, Finset.sum_mul, sample_smul, sample_sum]
    calc
      _ ≤ (k : ℝ)⁻¹ * (∑ _j : Fin k, p v * g v) := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => restricted j v) (inv_nonneg.mpr hk'.le)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
        rw [inv_mul_cancel₀ hk'.ne', one_mul]
  let ell := Real.sqrt (2 * Real.log (2 * (r : ℝ)))
  have ell_one : 1 ≤ ell := by
    have r2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have r4 : (4 : ℝ) ≤ 2 * (r : ℝ) := by linarith
    have rpos : (0 : ℝ) < 2 * (r : ℝ) := by linarith
    have invb' : (2 * (r : ℝ))⁻¹ ≤ (4 : ℝ)⁻¹ := (inv_le_inv₀ rpos (by norm_num : (0 : ℝ) < 4)).2 r4
    have logb := Real.one_sub_inv_le_log_of_pos rpos
    calc
      (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ ell := Real.sqrt_le_sqrt (by
        have hfour : (4 : ℝ)⁻¹ = 1 / 4 := by norm_num
        rw [hfour] at invb'
        linarith only [invb', logb])
  let b (x y : Fin k → V) (v : V) := p v + empirical x v + empirical y v
  have hb (x y : Fin k → V) (v : V) : 0 ≤ b x y v :=
    add_nonneg (add_nonneg (hpp.1 v) ((empirical_probability hk x).1 v)) ((empirical_probability hk y).1 v)
  let fst (x : Fin k → V) (v : V) (τ : Fin k → Bool) :=
    |∑ i, signValue (τ i) * L (x i) v|
  let rst (x : Fin k → V) (v : V) (σ : Fin k → Fin r → Bool) :=
    sSup (Set.range fun j : Fin r => |∑ i, signValue (σ i j) * L (x i) v|)
  let dom (x : Fin k → V) (v : V) (σ : Fin k → Fin (r + 1) → Bool) :=
    fst x v (fun i => σ i 0) + rst x v (fun i j => σ i j.succ)
  have dom_bound (x : Fin k → V) (v : V) (σ : Fin k → Fin (r + 1) → Bool) (j : Fin r) :
      |∑ i, (signValue (σ i 0) + signValue (σ i j.succ)) * L (x i) v| ≤ dom x v σ := by
    simp only [add_mul, Finset.sum_add_distrib]
    apply (abs_add_le _ _).trans
    unfold dom rst fst
    apply add_le_add_right _ _
    exact le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩
  have instant (x y : Fin k → V) (σ : Fin k → Fin (r + 1) → Bool) :
      signedMaximumR r L p x y σ ≤ ∑ v, b x y v * dom x v σ / (k : ℝ) := by
    have hne : (boxR r p x y).Nonempty := ⟨0, by intro v; simpa using hb x y v⟩
    unfold signedMaximumR
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨c, hc, rfl⟩
    let S (v : V) (j : Fin r) := ∑ i, (signValue (σ i 0) + signValue (σ i j.succ)) * L (x i) v
    have expanded :
        (∑ i, ∑ j : Fin r, (signValue (σ i 0) + signValue (σ i j.succ)) * matVec L (c j) (x i)) =
        ∑ v, ∑ j, c j v * S v j := by
      unfold matVec S
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      conv_lhs => enter [2, j]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    change |(∑ i, ∑ j : Fin r, (signValue (σ i 0) + signValue (σ i j.succ)) * matVec L (c j) (x i)) / (k : ℝ)| ≤ _
    rw [expanded, abs_div, abs_of_pos hk', ← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ hk'.le
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro v _
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ j, |c j v| * dom x v σ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (dom_bound x v σ j) (abs_nonneg _)
      _ = (∑ j, |c j v|) * dom x v σ := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (hc v)
          ((abs_nonneg _).trans (dom_bound x v σ ⟨0, by omega⟩))
  have average_dom (x : Fin k → V) (v : V) :
      matrixSignAverage k (r + 1) (dom x v) ≤ (2 * ell) * Real.sqrt (B x v) := by
    unfold dom
    rw [matrix_sign_parts]
    have common : signAverage k (fst x v) ≤ Real.sqrt (B x v) := sign_absolute (fun i => L (x i) v)
    have hd : sSup (Set.range (fun _ : Fin r => Real.sqrt (B x v))) = Real.sqrt (B x v) := by
      let _ : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
      simp
    have massart := lemma_A_4 k r hk (by omega : 1 ≤ r) (fun i _ => L (x i) v)
    change matrixSignAverage k r (rst x v) ≤ ell * sSup (Set.range (fun _ : Fin r => Real.sqrt (B x v))) at massart
    rw [hd] at massart
    have needed := mul_le_mul_of_nonneg_right ell_one (Real.sqrt_nonneg (B x v))
    linarith
  have signed_bound (x y : Fin k → V) :
      matrixSignAverage k (r + 1) (signedMaximumR r L p x y) ≤
        ∑ v, b x y v * ((2 * ell) * f x v) := by
    have h := matrix_sign_le (instant x y)
    rw [matrix_sign_sum (fun v σ => b x y v * dom x v σ / (k : ℝ))] at h
    apply h.trans
    apply Finset.sum_le_sum
    intro v _
    have hw (σ : Fin k → Fin (r + 1) → Bool) : b x y v * dom x v σ / (k : ℝ) =
        (b x y v / (k : ℝ)) * dom x v σ := by ring
    simp only [hw, matrixSignAverage, ← Finset.mul_sum, mul_div_assoc]
    have bound := mul_le_mul_of_nonneg_left (average_dom x v) (div_nonneg (hb x y v) hk'.le)
    convert bound using 1 <;> first | rfl | (dsimp only [f]; ring)
  have average_y (x : Fin k → V) (v : V) :
      sampleAverage p k (fun y => b x y v * f x v) = (2 * p v + empirical x v) * f x v := by
    have rewrite (y : Fin k → V) : b x y v * f x v =
        (p v + empirical x v) * f x v + f x v * empirical y v := by dsimp [b]; ring
    simp_rw [rewrite, sample_add, sample_const hpp, sample_smul, sample_empirical hpp hk]
    ring
  unfold expectedSignedR
  have houter : sampleAverage p k (fun x => sampleAverage p k (fun y =>
      matrixSignAverage k (r + 1) (signedMaximumR r L p x y))) ≤
      (2 * ell) * sampleAverage p k (fun x => ∑ v, (2 * p v + empirical x v) * f x v) := by
    rw [← sample_smul]
    apply sample_le hpp.1
    intro x
    refine (sample_le hpp.1 _ _ (signed_bound x)).trans_eq ?_
    rw [sample_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    have h (y) : b x y v * (2 * ell * f x v) = (2 * ell) * (b x y v * f x v) := by ring
    simp_rw [h, sample_smul, average_y]
  refine houter.trans ?_
  have ell_n : 0 ≤ ell := Real.sqrt_nonneg _
  have core : sampleAverage p k (fun x => ∑ v, (2 * p v + empirical x v) * f x v) ≤
      3 * H A p / Real.sqrt (k : ℝ) := by
    rw [sample_sum]
    have each (v : V) : sampleAverage p k (fun x => (2 * p v + empirical x v) * f x v) ≤ 3 * (p v * g v) := by
      simp only [add_mul, sample_add, sample_smul]
      have h := mul_le_mul_of_nonneg_left (ordinary v) (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (hpp.1 v))
      linarith [self_sample v]
    calc
      _ ≤ ∑ v, 3 * (p v * g v) := Finset.sum_le_sum fun v _ => each v
      _ = _ := by simp only [g, H, μ, L, ← Finset.mul_sum, ← mul_div_assoc, ← Finset.sum_div]
  refine (mul_le_mul_of_nonneg_left core (by positivity : 0 ≤ 2 * ell)).trans_eq ?_
  have hlog : 0 ≤ Real.log (2 * (r : ℝ)) := by
    apply Real.log_nonneg
    have h : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  rw [show ell = Real.sqrt 2 * Real.sqrt (Real.log (2 * (r : ℝ))) from Real.sqrt_mul (by norm_num) _,
    Real.sqrt_div hlog]
  ring
