-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.truncatedLog_minor_global_denominator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:36:11.203382+00:00
-- url     : https://prove2.me/submissions/38df41bf-892a-4c93-aacf-8932eae4c98c

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

namespace E103TL

def Z : Subring ℂ := GaussianInt.toComplex.range

theorem mem_Z_iff (x : ℂ) : x ∈ Z ↔ ∃ g : GaussianInt, x = (g : ℂ) := by
  constructor
  · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩; exact ⟨g, rfl⟩

theorem I_mem : Complex.I ∈ Z := ⟨⟨0, 1⟩, by simp [GaussianInt.toComplex_def]⟩

theorem int_mem (n : ℤ) : (n : ℂ) ∈ Z := ⟨(n : GaussianInt), by simp⟩

theorem nat_mem (n : ℕ) : (n : ℂ) ∈ Z := by exact_mod_cast int_mem n

/-- `P` has all coefficients in `N⁻¹ ℤ[i]`. -/
def PI (N : ℕ) (P : Polynomial ℂ) : Prop := ∀ n, (N : ℂ) * P.coeff n ∈ Z

theorem PI_zero (N : ℕ) : PI N 0 := fun n => by simp [Z.zero_mem]

theorem PI_add {N : ℕ} {P Q : Polynomial ℂ} (hP : PI N P) (hQ : PI N Q) : PI N (P + Q) :=
  fun n => by rw [Polynomial.coeff_add, mul_add]; exact Z.add_mem (hP n) (hQ n)

theorem PI_sum {ι : Type*} (s : Finset ι) {N : ℕ} (P : ι → Polynomial ℂ)
    (h : ∀ i ∈ s, PI N (P i)) : PI N (∑ i ∈ s, P i) := by
  intro n
  rw [Polynomial.finsetSum_coeff, Finset.mul_sum]
  exact Z.sum_mem fun i hi => h i hi n

theorem PI_mul {M N : ℕ} {P Q : Polynomial ℂ} (hP : PI M P) (hQ : PI N Q) : PI (M * N) (P * Q) := by
  intro n
  rw [Polynomial.coeff_mul, Finset.mul_sum]
  refine Z.sum_mem fun x _ => ?_
  have : ((M * N : ℕ) : ℂ) * (P.coeff x.1 * Q.coeff x.2) =
      ((M : ℂ) * P.coeff x.1) * ((N : ℂ) * Q.coeff x.2) := by push_cast; ring
  rw [this]; exact Z.mul_mem (hP _) (hQ _)

theorem PI_one : PI 1 (1 : Polynomial ℂ) := by
  intro n
  rw [Polynomial.coeff_one]
  split_ifs <;> simp [Z.one_mem, Z.zero_mem]

theorem PI_pow {N : ℕ} {P : Polynomial ℂ} (hP : PI N P) (k : ℕ) : PI (N ^ k) (P ^ k) := by
  induction k with
  | zero => simpa using PI_one
  | succ k ih => rw [pow_succ, pow_succ]; exact PI_mul ih hP

theorem PI_dvd {N N' : ℕ} {P : Polynomial ℂ} (hP : PI N P) (h : N ∣ N') : PI N' P := by
  obtain ⟨k, rfl⟩ := h
  intro n
  have : ((N * k : ℕ) : ℂ) * P.coeff n = (k : ℂ) * ((N : ℂ) * P.coeff n) := by push_cast; ring
  rw [this]; exact Z.mul_mem (nat_mem k) (hP n)

theorem PI_onet (h : ℕ) : PI 1 ((1 + Polynomial.X) ^ h) := by
  have h1 : PI 1 (1 + Polynomial.X : Polynomial ℂ) := by
    intro n
    rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X]
    split_ifs <;> simp [Z.one_mem, Z.zero_mem, Z.add_mem]
  simpa using PI_pow h1 h

theorem PI_center (p : ℤ) (q : ℕ) (hq : q ≠ 0) (j : ℕ) (T : ℕ) :
    PI (q * Nat.lcmUpto T)
      (Polynomial.C ((j : ℂ) * (2 * Complex.I * (p : ℂ) / (q : ℂ))) +
        OAI.PiExponent.InterpolationMatrix.truncatedLog T) := by
  intro n
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  rw [Polynomial.coeff_add, Polynomial.coeff_C, OAI.PiExponent.InterpolationMatrix.truncatedLog,
    PowerSeries.coeff_trunc, PowerSeries.coeff_log]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [if_true]
    have : ((q * Nat.lcmUpto T : ℕ) : ℂ) * ((j : ℂ) * (2 * Complex.I * (p : ℂ) / (q : ℂ)) +
        (if 0 < T then 0 else 0)) =
        (2 * (j * Nat.lcmUpto T : ℕ) * p : ℂ) * Complex.I := by
      simp only [ite_self, add_zero]; push_cast; field_simp
    rw [this]
    exact Z.mul_mem (Z.mul_mem (Z.mul_mem (nat_mem 2) (nat_mem _)) (int_mem p)) I_mem
  · have hn0 : n ≠ 0 := hn.ne'
    simp only [hn0, if_false, zero_add]
    split_ifs with hT
    · have hdvd : n ∣ Nat.lcmUpto T := by
        unfold Nat.lcmUpto
        exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hn, hT.le⟩)
      obtain ⟨k, hk⟩ := hdvd
      have : ((q * Nat.lcmUpto T : ℕ) : ℂ) * (algebraMap ℚ ℂ ((-1 : ℚ) ^ (n + 1) / n)) =
          ((q * k : ℕ) : ℂ) * ((-1 : ℤ) ^ (n + 1) : ℤ) := by
        rw [hk]
        have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
        simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]
        push_cast
        field_simp
      rw [this]
      exact Z.mul_mem (nat_mem _) (int_mem _)
    · simp [Z.zero_mem]

end E103TL

open scoped BigOperators

namespace E103TL

variable {m : ℕ} (w : Fin m → ℕ)

def Good (a : Fin m → ℕ) (P : MvPolynomial (Fin m) (Polynomial ℂ)) : Prop :=
  ∀ b : Fin m →₀ ℕ, (P.coeff b ≠ 0 → ∀ i, b i ≤ a i) ∧ PI (∏ i, w i ^ (a i - b i)) (P.coeff b)

theorem Good_C {P : Polynomial ℂ} (hP : PI 1 P) : Good w 0 (MvPolynomial.C P) := by
  intro b
  rw [MvPolynomial.coeff_C]
  split_ifs with hb
  · subst hb
    refine ⟨fun _ i => by simp, ?_⟩
    simpa using hP
  · exact ⟨fun h => absurd rfl h, PI_zero _⟩

theorem Good_mul {a a' : Fin m → ℕ} {P Q : MvPolynomial (Fin m) (Polynomial ℂ)}
    (hP : Good w a P) (hQ : Good w a' Q) : Good w (a + a') (P * Q) := by
  intro b
  rw [MvPolynomial.coeff_mul]
  constructor
  · intro hne
    obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h1 := (hP x.1).1 (left_ne_zero_of_mul hxne)
    have h2 := (hQ x.2).1 (right_ne_zero_of_mul hxne)
    intro i
    rw [← hx]
    simp only [Finsupp.coe_add, Pi.add_apply]
    exact Nat.add_le_add (h1 i) (h2 i)
  · refine PI_sum _ _ fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hxne : P.coeff x.1 * Q.coeff x.2 = 0
    · rw [hxne]; exact PI_zero _
    · have h1 := (hP x.1).1 (left_ne_zero_of_mul hxne)
      have h2 := (hQ x.2).1 (right_ne_zero_of_mul hxne)
      have e : ∏ i, w i ^ ((a + a') i - b i) =
          (∏ i, w i ^ (a i - x.1 i)) * ∏ i, w i ^ (a' i - x.2 i) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← pow_add, ← hx]
        congr 1
        simp only [Pi.add_apply, Finsupp.coe_add]
        have := h1 i; have := h2 i; omega
      rw [e]
      exact PI_mul (hP x.1).2 (hQ x.2).2

theorem Good_one : Good w 0 (1 : MvPolynomial (Fin m) (Polynomial ℂ)) := by
  simpa using Good_C w PI_one

theorem Good_pow {a : Fin m → ℕ} {P : MvPolynomial (Fin m) (Polynomial ℂ)}
    (hP : Good w a P) (k : ℕ) : Good w (k • a) (P ^ k) := by
  induction k with
  | zero => simpa using Good_one w
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact Good_mul w ih hP

theorem Good_prod (s : Finset (Fin m)) (a : Fin m → Fin m → ℕ)
    (P : Fin m → MvPolynomial (Fin m) (Polynomial ℂ)) (h : ∀ i ∈ s, Good w (a i) (P i)) :
    Good w (∑ i ∈ s, a i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good_one w
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk]
    exact Good_mul w (h k (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Good_lin (i : Fin m) {c : Polynomial ℂ} (hc : PI (w i) c) :
    Good w (Pi.single i 1) (MvPolynomial.C c + MvPolynomial.X i) := by
  classical
  intro b
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C, MvPolynomial.coeff_X']
  by_cases hb0 : (0 : Fin m →₀ ℕ) = b
  · subst hb0
    have hs : Finsupp.single i 1 ≠ (0 : Fin m →₀ ℕ) := by simp
    rw [if_pos rfl, if_neg hs, add_zero]
    refine ⟨fun _ k => by simp, ?_⟩
    have e : ∏ k, w k ^ ((Pi.single i 1 : Fin m → ℕ) k - (0 : Fin m →₀ ℕ) k) = w i := by
      simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.sub_zero]
      rw [Finset.prod_eq_single i]
      · simp
      · intro k _ hk; simp [Pi.single_apply, hk]
      · simp
    rw [e]; exact hc
  · rw [if_neg hb0, zero_add]
    split_ifs with hb
    · subst hb
      refine ⟨fun _ k => ?_, ?_⟩
      · by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_apply, hk, Finsupp.single_apply, Ne.symm hk]
      · have e : ∏ k, w k ^ ((Pi.single i 1 : Fin m → ℕ) k - (Finsupp.single i 1 : Fin m →₀ ℕ) k) = 1 := by
          refine Finset.prod_eq_one fun k _ => ?_
          by_cases hk : k = i
          · subst hk; simp
          · simp [Pi.single_apply, hk, Finsupp.single_apply, Ne.symm hk]
        rw [e]; exact PI_one
    · exact ⟨fun h => absurd rfl h, PI_zero _⟩

end E103TL

open scoped BigOperators

namespace E103TL

theorem entry_good {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (T : Fin m → ℕ) (j s : ℕ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ) :
    (OAI.PiExponent.InterpolationMatrix.entry
        (OAI.PiExponent.MatrixArithmetic.rationalCenters p q)
        (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i)) j s b h a ≠ 0 →
        ∀ i, b i ≤ a i) ∧
      ((∏ i, (q i * Nat.lcmUpto (T i)) ^ (a i - b i) : ℕ) : ℂ) *
        OAI.PiExponent.InterpolationMatrix.entry
          (OAI.PiExponent.MatrixArithmetic.rationalCenters p q)
          (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i)) j s b h a ∈ Z := by
  classical
  set w : Fin m → ℕ := fun i => q i * Nat.lcmUpto (T i) with hw
  have hG : Good w a (OAI.PiExponent.InterpolationMatrix.monomialImage
      (OAI.PiExponent.MatrixArithmetic.rationalCenters p q)
      (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i)) j h a) := by
    unfold OAI.PiExponent.InterpolationMatrix.monomialImage
    have h1 := Good_C w (PI_onet h)
    have h2 := Good_prod w Finset.univ (fun i => a i • (Pi.single i 1 : Fin m → ℕ)) _
      (fun i _ => Good_pow w (Good_lin w i (PI_center (p i) (q i) (by have := hq i; omega) j (T i)))
        (a i))
    have h3 := Good_mul w h1 h2
    have e : (0 : Fin m → ℕ) + ∑ i, a i • (Pi.single i 1 : Fin m → ℕ) = a := by
      funext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [e] at h3
    exact h3
  have hb := hG (OAI.PiExponent.InterpolationMatrix.exponentVector b)
  have hev : ∀ i, (OAI.PiExponent.InterpolationMatrix.exponentVector b) i = b i := by
    intro i; simp [OAI.PiExponent.InterpolationMatrix.exponentVector]
  constructor
  · intro hne i
    have hne' : (OAI.PiExponent.InterpolationMatrix.monomialImage
      (OAI.PiExponent.MatrixArithmetic.rationalCenters p q)
      (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i)) j h a).coeff
        (OAI.PiExponent.InterpolationMatrix.exponentVector b) ≠ 0 := by
      intro h0
      apply hne
      unfold OAI.PiExponent.InterpolationMatrix.entry
      rw [h0, Polynomial.coeff_zero]
    have := hb.1 hne' i
    rwa [hev] at this
  · have := hb.2 s
    simp only [hev] at this
    unfold OAI.PiExponent.InterpolationMatrix.entry
    convert this using 2

end E103TL

open scoped BigOperators

theorem solution
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (T : Fin m → ℕ) (j s h : ι → ℕ) (b a : ι → Fin m → ℕ)
    (hdet : (Matrix.of (fun r c : ι =>
      OAI.PiExponent.InterpolationMatrix.entry
        (OAI.PiExponent.MatrixArithmetic.rationalCenters p q)
        (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i))
        (j r) (s r) (b r) (h c) (a c))).det ≠ 0) :
    (∀ i, (∑ r, b r i) ≤ ∑ c, a c i) ∧
      ∃ g : GaussianInt,
        ((∏ i, (q i ^ ((∑ c, a c i) - (∑ r, b r i)) *
          Nat.lcmUpto (T i) ^ (∑ c, a c i)) : ℕ) : ℂ) *
          (Matrix.of (fun r c : ι =>
            OAI.PiExponent.InterpolationMatrix.entry
              (OAI.PiExponent.MatrixArithmetic.rationalCenters p q)
              (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i))
              (j r) (s r) (b r) (h c) (a c))).det = (g : ℂ) := by
  set E : Matrix ι ι ℂ := Matrix.of (fun r c : ι =>
      OAI.PiExponent.InterpolationMatrix.entry
        (OAI.PiExponent.MatrixArithmetic.rationalCenters p q)
        (fun i => OAI.PiExponent.InterpolationMatrix.truncatedLog (T i))
        (j r) (s r) (b r) (h c) (a c)) with hE
  have hgood := fun r c => E103TL.entry_good p q hq T (j r) (s r) (b r) (h c) (a c)
  -- a permutation with nonzero diagonal product forces `b (σ c) ≤ a c`
  have hperm : ∀ σ : Equiv.Perm ι, (∏ c, E (σ c) c) ≠ 0 → ∀ c i, b (σ c) i ≤ a c i := by
    intro σ hσ c i
    have hne : E (σ c) c ≠ 0 := fun h0 => hσ (Finset.prod_eq_zero (Finset.mem_univ c) h0)
    exact (hgood (σ c) c).1 hne i
  have hsumle : ∀ σ : Equiv.Perm ι, (∏ c, E (σ c) c) ≠ 0 → ∀ i, (∑ r, b r i) ≤ ∑ c, a c i := by
    intro σ hσ i
    rw [← Equiv.sum_comp σ (fun r => b r i)]
    exact Finset.sum_le_sum fun c _ => hperm σ hσ c i
  rw [Matrix.det_apply] at hdet
  obtain ⟨σ0, -, hσ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  have hσ0' : (∏ c, E (σ0 c) c) ≠ 0 := by
    intro h0; apply hσ0; rw [h0, smul_zero]
  have hle := hsumle σ0 hσ0'
  refine ⟨hle, ?_⟩
  rw [← E103TL.mem_Z_iff, Matrix.det_apply, Finset.mul_sum]
  refine E103TL.Z.sum_mem fun σ _ => ?_
  by_cases hσ : (∏ c, E (σ c) c) = 0
  · rw [hσ, smul_zero, mul_zero]; exact E103TL.Z.zero_mem
  have hp := hperm σ hσ
  set w : Fin m → ℕ := fun i => q i * Nat.lcmUpto (T i)
  have hN : (∏ c, ∏ i, w i ^ (a c i - b (σ c) i)) =
      ∏ i, w i ^ ((∑ c, a c i) - (∑ r, b r i)) := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_pow_eq_pow_sum, Finset.sum_tsub_distrib _ (fun c _ => hp c i),
      Equiv.sum_comp σ (fun r => b r i)]
  have hD : (∏ i, (q i ^ ((∑ c, a c i) - (∑ r, b r i)) * Nat.lcmUpto (T i) ^ (∑ c, a c i))) =
      (∏ c, ∏ i, w i ^ (a c i - b (σ c) i)) * ∏ i, Nat.lcmUpto (T i) ^ (∑ r, b r i) := by
    rw [hN, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [w, mul_pow]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (hle i)]
  have hmem : ((∏ c, ∏ i, w i ^ (a c i - b (σ c) i) : ℕ) : ℂ) * ∏ c, E (σ c) c ∈ E103TL.Z := by
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine E103TL.Z.prod_mem fun c _ => ?_
    have := (hgood (σ c) c).2
    simpa [hE, w] using this
  rw [hD, Nat.cast_mul, Units.smul_def, mul_smul_comm]
  refine E103TL.Z.zsmul_mem ?_ _
  have e : (((∏ c, ∏ i, w i ^ (a c i - b (σ c) i) : ℕ) : ℂ) *
      ((∏ i, Nat.lcmUpto (T i) ^ (∑ r, b r i) : ℕ) : ℂ)) * ∏ c, E (σ c) c =
      (((∏ c, ∏ i, w i ^ (a c i - b (σ c) i) : ℕ) : ℂ) * ∏ c, E (σ c) c) *
        ((∏ i, Nat.lcmUpto (T i) ^ (∑ r, b r i) : ℕ) : ℂ) := by ring
  rw [e]
  exact E103TL.Z.mul_mem hmem (E103TL.nat_mem _)
