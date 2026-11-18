-- Prove2me | solution 1 for KoanaKPaths.Main.sign_determinant_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:09:35.972144+00:00
-- url     : https://prove2.me/submissions/c267802d-7d44-4fd6-86ce-4c7958bf606c

import Definitions.Def_KoanaKPaths_Main_Estimator

open scoped BigOperators
namespace KoanaKPaths.Main.SignMoments

lemma mean_add {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun w => f w + g w) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

lemma mean_mul {Ω : Type} [Fintype Ω] (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun w => a * f w) = a * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

lemma mean_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (a : ℝ) :
    uniformMean (fun _ : Ω => a) = a := by
  simp [uniformMean]

lemma mean_mono {Ω : Type} [Fintype Ω] {f g : Ω → ℝ} (h : ∀ w, f w ≤ g w) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => h w) (by positivity)

lemma mean_sum {Ω I : Type} [Fintype Ω] [Fintype I] (f : I → Ω → ℝ) :
    uniformMean (fun w => ∑ i, f i w) = ∑ i, uniformMean (f i) := by
  simp only [uniformMean, ← Finset.sum_div]
  congr 1
  exact Finset.sum_comm


end KoanaKPaths.Main.SignMoments


open scoped BigOperators
namespace KoanaKPaths.Main.SignMoments

lemma sign_sq (b : Bool) : (sgn b : ℝ) ^ 2 = 1 := by cases b <;> norm_num [sgn]
lemma sign_not (b : Bool) : (sgn (!b) : ℝ) = -(sgn b : ℝ) := by cases b <;> norm_num [sgn]

def flipLabel {n k : ℕ} (v : Fin n) (r : Fin k) (σ : Labels n k) : Labels n k :=
  Function.update σ v (Function.update (σ v) r (!(σ v r)))

lemma flipLabel_involutive {n k : ℕ} (v : Fin n) (r : Fin k) :
    Function.Involutive (flipLabel v r) := by
  intro σ
  funext a b
  by_cases ha : a = v <;> by_cases hb : b = r <;> simp [flipLabel, ha, hb]

lemma mean_cancel {Ω : Type} [Fintype Ω] (e : Ω ≃ Ω) (f : Ω → ℝ)
    (h : ∀ w, f (e w) = -f w) : uniformMean f = 0 := by
  have hs := e.sum_comp f
  simp_rw [h, Finset.sum_neg_distrib] at hs
  have hz : ∑ w, f w = 0 := by linarith
  simp [uniformMean, hz]

def permProd {n k : ℕ} (τ : Fin k → Fin n) (σ : Labels n k) (p : Equiv.Perm (Fin k)) : ℝ :=
  ∏ j, (sgn (σ (τ j) (p j)) : ℝ)

lemma permProd_sq {n k : ℕ} (τ : Fin k → Fin n) (σ : Labels n k) (p : Equiv.Perm (Fin k)) :
    permProd τ σ p ^ 2 = 1 := by
  simp [permProd, ← Finset.prod_pow, sign_sq]

lemma permProd_flip_same {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ)
    (σ : Labels n k) (p : Equiv.Perm (Fin k)) (j : Fin k) :
    permProd τ (flipLabel (τ j) (p j) σ) p = -permProd τ σ p := by
  classical
  have hprod :
      (∏ s ∈ Finset.univ.erase j, (sgn (flipLabel (τ j) (p j) σ (τ s) (p s)) : ℝ)) =
        ∏ s ∈ Finset.univ.erase j, (sgn (σ (τ s) (p s)) : ℝ) := by
    apply Finset.prod_congr rfl
    intro s hs
    have hsj : s ≠ j := (Finset.mem_erase.mp hs).1
    have hne : τ s ≠ τ j := fun h => hsj (hτ h)
    simp [flipLabel, hne]
  unfold permProd
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ (fun s => (sgn (σ (τ s) (p s)) : ℝ)) (Finset.mem_univ j), hprod]
  simp [flipLabel, sign_not]

lemma permProd_flip_other {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ)
    (σ : Labels n k) (p q : Equiv.Perm (Fin k)) (j : Fin k) (hpq : p j ≠ q j) :
    permProd τ (flipLabel (τ j) (p j) σ) q = permProd τ σ q := by
  classical
  apply Finset.prod_congr rfl
  intro s _
  by_cases hsj : s = j
  · subst s
    simp [flipLabel, Ne.symm hpq]
  · have hne : τ s ≠ τ j := fun h => hsj (hτ h)
    simp [flipLabel, hne]

lemma permProd_orthogonal {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ)
    (p q : Equiv.Perm (Fin k)) :
    uniformMean (fun σ : Labels n k => permProd τ σ p * permProd τ σ q) = if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp only [↓reduceIte, ← pow_two, permProd_sq, mean_const]
  · rw [if_neg hpq]
    have hne : ∃ j, p j ≠ q j := by
      by_contra! h
      exact hpq (Equiv.ext h)
    obtain ⟨j, hj⟩ := hne
    let e : Labels n k ≃ Labels n k :=
      ⟨flipLabel (τ j) (p j), flipLabel (τ j) (p j), flipLabel_involutive _ _, flipLabel_involutive _ _⟩
    apply mean_cancel e
    intro σ
    change permProd τ (flipLabel (τ j) (p j) σ) p *
      permProd τ (flipLabel (τ j) (p j) σ) q = _
    rw [permProd_flip_same τ hτ, permProd_flip_other τ hτ σ p q j hj]
    ring

lemma det_second {n k : ℕ} (τ : Fin k → Fin n) (hτ : Function.Injective τ) :
    uniformMean (fun σ : Labels n k => (detD σ τ : ℝ) ^ 2) = (Nat.factorial k : ℝ) := by
  classical
  have hexp (σ : Labels n k) : (detD σ τ : ℝ) =
      ∑ p : Equiv.Perm (Fin k), ((Equiv.Perm.sign p : ℤ) : ℝ) * permProd τ σ p := by
    simp [detD, Matrix.det_apply', permProd]
  have hsign (p : Equiv.Perm (Fin k)) : (((Equiv.Perm.sign p : ℤ) : ℝ)) ^ 2 = 1 := by
    have hz : (Equiv.Perm.sign p : ℤ)^2 = 1 :=
      congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_sq (Equiv.Perm.sign p))
    exact_mod_cast hz
  simp_rw [hexp, pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [mean_sum]
  simp_rw [mean_sum]
  have hterm (p q : Equiv.Perm (Fin k)) :
      uniformMean (fun σ : Labels n k =>
        (((Equiv.Perm.sign p : ℤ) : ℝ) * permProd τ σ p) *
          (((Equiv.Perm.sign q : ℤ) : ℝ) * permProd τ σ q)) = if p = q then 1 else 0 := by
    have heq : (fun σ : Labels n k =>
        (((Equiv.Perm.sign p : ℤ) : ℝ) * permProd τ σ p) *
          (((Equiv.Perm.sign q : ℤ) : ℝ) * permProd τ σ q)) =
        (fun σ => (((Equiv.Perm.sign p : ℤ) : ℝ) * ((Equiv.Perm.sign q : ℤ) : ℝ)) *
          (permProd τ σ p * permProd τ σ q)) := by funext σ; ring
    rw [heq, mean_mul, permProd_orthogonal τ hτ p q]
    split_ifs with h
    · subst q
      simpa only [mul_one, ← pow_two] using hsign p
    · simp
  simp_rw [hterm]
  simp [Fintype.card_perm]


lemma det_zero_noninjective {n k : ℕ} (τ : Fin k → Fin n)
    (hτ : ¬ Function.Injective τ) (σ : Labels n k) : detD σ τ = 0 := by
  classical
  by_contra hdet
  apply hτ
  intro a b he
  by_contra hne
  apply hdet
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [Matrix.of_apply, he]

lemma tensor_first {n k : ℕ} (c : (Fin k → Fin n) → ℤ) (hc : IsZeroOneTensor c) :
    uniformMean (fun σ : Labels n k => (psiFrobSq c σ : ℝ)) =
      (Nat.factorial k : ℝ) * (tensorN c : ℝ) := by
  classical
  have hsq (τ : Fin k → Fin n) : (c τ)^2 = c τ := by
    rcases hc τ with h | h <;> simp [h]
  have hterm (τ : Fin k → Fin n) :
      uniformMean (fun σ : Labels n k => ((Psi c σ τ)^2 : ℤ)) =
        if Function.Injective τ then (c τ : ℝ) * (Nat.factorial k : ℝ) else 0 := by
    by_cases hτ : Function.Injective τ
    · rw [if_pos hτ]
      simp_rw [Psi, mul_pow, hsq, Int.cast_mul, Int.cast_pow]
      rw [mean_mul, det_second τ hτ]
    · simp [Psi, det_zero_noninjective τ hτ, hτ, uniformMean]
  simp_rw [psiFrobSq, Int.cast_sum]
  rw [mean_sum]
  simp_rw [hterm]
  simp only [tensorN, Int.cast_sum, Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  split_ifs <;> ring

end KoanaKPaths.Main.SignMoments

theorem solution (n k : ℕ)
    (τ : Fin k → Fin n) (hτ : Function.Injective τ) :
    KoanaKPaths.Main.uniformMean (fun σ : KoanaKPaths.Main.Labels n k =>
      (KoanaKPaths.Main.detD σ τ : ℝ)^2) = (Nat.factorial k : ℝ) := by
  exact KoanaKPaths.Main.SignMoments.det_second τ hτ
