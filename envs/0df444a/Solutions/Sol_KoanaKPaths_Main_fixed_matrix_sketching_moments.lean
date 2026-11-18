-- Prove2me | solution 1 for KoanaKPaths.Main.fixed_matrix_sketching_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:59:52.417112+00:00
-- url     : https://prove2.me/submissions/0db3bfac-a7c7-42e8-999a-4ae61110c6bf

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

lemma mean_pi_succ {α : Type} [Fintype α] (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    uniformMean f = uniformMean (fun a : α =>
      uniformMean (fun r : Fin n → α => f (Fin.cons a r))) := by
  have hs := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α))
    (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)
  rw [Fintype.sum_prod_type] at hs
  simp only [uniformMean, Fintype.card_fun, Fintype.card_fin, ← Finset.sum_div]
  rw [← hs]
  simp only [Nat.cast_pow, pow_succ, Nat.cast_mul]
  ring

lemma mean_bool (f : Bool → ℝ) : uniformMean f = (f true + f false) / 2 := by
  simp [uniformMean, Fintype.sum_bool]

lemma mean_sign_succ (n : ℕ) (f : (Fin (n+1) → Bool) → ℝ) :
    uniformMean f = (uniformMean (fun r => f (Fin.cons true r)) +
      uniformMean (fun r => f (Fin.cons false r))) / 2 := by
  rw [mean_pi_succ, mean_bool]

def signedSum {d : ℕ} (z : Fin d → ℝ) (r : Fin d → Bool) : ℝ :=
  ∑ u, (sgn (r u) : ℝ) * z u

def energy {d : ℕ} (z : Fin d → ℝ) : ℝ := ∑ u, z u ^ 2

lemma signedSum_cons {d : ℕ} (z : Fin (d+1) → ℝ) (b : Bool) (r : Fin d → Bool) :
    signedSum z (Fin.cons b r) = (sgn b : ℝ) * z 0 + signedSum (fun i => z i.succ) r := by
  simp [signedSum, Fin.sum_univ_succ]

lemma energy_succ {d : ℕ} (z : Fin (d+1) → ℝ) :
    energy z = z 0 ^ 2 + energy (fun i => z i.succ) := by
  simp [energy, Fin.sum_univ_succ]

lemma scalar_second (d : ℕ) (z : Fin d → ℝ) :
    uniformMean (fun r : Fin d → Bool => signedSum z r ^ 2) = energy z := by
  induction d with
  | zero => simp [signedSum, energy, uniformMean]
  | succ d ih =>
    rw [mean_sign_succ]
    simp only [signedSum_cons, sgn, Bool.false_eq_true, ↓reduceIte, Int.cast_one,
      Int.cast_neg, one_mul, neg_mul]
    rw [← mean_add]
    simp_rw [show ∀ x y : ℝ, (x+y)^2 + (-x+y)^2 = 2*x^2 + 2*y^2 by intros; ring]
    rw [mean_add, mean_const, mean_mul, ih, energy_succ]
    ring

lemma scalar_fourth (d : ℕ) (z : Fin d → ℝ) :
    uniformMean (fun r : Fin d → Bool => signedSum z r ^ 4) ≤ 3 * energy z ^ 2 := by
  induction d with
  | zero => simp [signedSum, energy, uniformMean]
  | succ d ih =>
    rw [mean_sign_succ]
    simp only [signedSum_cons, sgn, Bool.false_eq_true, ↓reduceIte, Int.cast_one,
      Int.cast_neg, one_mul, neg_mul]
    rw [← mean_add]
    simp_rw [show ∀ x y : ℝ, (x+y)^4 + (-x+y)^4 = 2*x^4 + (12*x^2)*y^2 + 2*y^4 by intros; ring]
    rw [mean_add, mean_add, mean_const, mean_mul, mean_mul, scalar_second, energy_succ]
    have h := ih (fun i => z i.succ)
    nlinarith [sq_nonneg (z 0 ^ 2)]


lemma mean_mul_right {Ω : Type} [Fintype Ω] (f : Ω → ℝ) (a : ℝ) :
    uniformMean (fun w => f w * a) = uniformMean f * a := by
  simpa only [mul_comm] using mean_mul a f

lemma mean_head {α : Type} [Fintype α] [Nonempty α] (n : ℕ) (f : α → ℝ) :
    uniformMean (fun r : Fin (n+1) → α => f (r 0)) = uniformMean f := by
  rw [mean_pi_succ]
  simp only [Fin.cons_zero, mean_const]

lemma mean_tail {α : Type} [Fintype α] [Nonempty α] (n : ℕ)
    (f : (Fin n → α) → ℝ) :
    uniformMean (fun r : Fin (n+1) → α => f (fun i => r i.succ)) = uniformMean f := by
  rw [mean_pi_succ]
  simp only [Fin.cons_succ, mean_const]

lemma mean_head_mul_tail {α : Type} [Fintype α] [Nonempty α] (n : ℕ)
    (f : α → ℝ) (g : (Fin n → α) → ℝ) :
    uniformMean (fun r : Fin (n+1) → α => f (r 0) * g (fun i => r i.succ)) =
      uniformMean f * uniformMean g := by
  rw [mean_pi_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, mean_mul, mean_mul_right]

def columnSq {ℓ d : ℕ} (z : Fin d → ℝ) (R : Fin ℓ → Fin d → Bool) : ℝ :=
  ∑ a, signedSum z (R a) ^ 2

lemma columnSq_succ {ℓ d : ℕ} (z : Fin d → ℝ) (R : Fin (ℓ+1) → Fin d → Bool) :
    columnSq z R = signedSum z (R 0) ^ 2 + columnSq z (fun i => R i.succ) := by
  simp [columnSq, Fin.sum_univ_succ]

lemma column_first (ℓ d : ℕ) (z : Fin d → ℝ) :
    uniformMean (fun R : Fin ℓ → Fin d → Bool => columnSq z R) = (ℓ : ℝ) * energy z := by
  induction ℓ with
  | zero => simp [columnSq, uniformMean]
  | succ ℓ ih =>
    simp_rw [columnSq_succ]
    rw [mean_add, mean_head ℓ (fun r : Fin d → Bool => signedSum z r ^ 2),
      mean_tail ℓ (columnSq z), scalar_second, ih]
    push_cast
    ring

lemma column_second (ℓ d : ℕ) (z : Fin d → ℝ) :
    uniformMean (fun R : Fin ℓ → Fin d → Bool => columnSq z R ^ 2) ≤
      ((ℓ : ℝ) ^ 2 + 2 * ℓ) * energy z ^ 2 := by
  induction ℓ with
  | zero => simp [columnSq, uniformMean]
  | succ ℓ ih =>
    simp_rw [columnSq_succ, show ∀ x y : ℝ, (x+y)^2 = x^2 + 2*(x*y) + y^2 by intros; ring]
    rw [mean_add, mean_add, mean_mul]
    rw [mean_head ℓ (fun r : Fin d → Bool => (signedSum z r ^ 2)^2),
      mean_tail ℓ (fun R => columnSq z R ^ 2),
      mean_head_mul_tail ℓ (fun r : Fin d → Bool => signedSum z r ^ 2) (columnSq z),
      scalar_second, column_first]
    have h := scalar_fourth d z
    have heq : (fun r : Fin d → Bool => (signedSum z r ^ 2) ^ 2) =
        (fun r : Fin d → Bool => signedSum z r ^ 4) := by funext r; ring
    rw [heq]
    push_cast
    nlinarith

lemma mean_cauchy {Ω : Type} [Fintype Ω] [Nonempty Ω] (f g : Ω → ℝ) :
    uniformMean (fun w => f w * g w) ^ 2 ≤
      uniformMean (fun w => f w ^ 2) * uniformMean (fun w => g w ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hc : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  simp only [uniformMean, div_pow]
  rw [div_mul_div_comm]
  simpa only [pow_two] using div_le_div_of_nonneg_right h (sq_nonneg (Fintype.card Ω : ℝ))

lemma correlation_bound {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (f g : Ω → ℝ) (C a b : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : uniformMean (fun w => f w ^ 2) ≤ C * a ^ 2)
    (hg : uniformMean (fun w => g w ^ 2) ≤ C * b ^ 2) :
    uniformMean (fun w => f w * g w) ≤ C * a * b := by
  have h := mean_cauchy f g
  have hn : 0 ≤ uniformMean (fun w => f w ^ 2) :=
    le_trans (by simp [uniformMean]) (mean_mono fun w => sq_nonneg (f w))
  have hu := mul_le_mul hf hg (by unfold uniformMean; positivity : 0 ≤ uniformMean (fun w => g w ^ 2)) (by positivity)
  have hprod : 0 ≤ C * a * b := by positivity
  nlinarith

lemma finite_matrix_moments (ℓ d t : ℕ) (X : Fin d → Fin t → ℝ) :
    uniformMean (fun R : Fin ℓ → Fin d → Bool => realFrobSq (signMul R X)) =
        (ℓ : ℝ) * realFrobSq X ∧
      uniformMean (fun R : Fin ℓ → Fin d → Bool => realFrobSq (signMul R X) ^ 2) ≤
        ((ℓ : ℝ) ^ 2 + 2 * ℓ) * realFrobSq X ^ 2 := by
  have heq (R : Fin ℓ → Fin d → Bool) :
      realFrobSq (signMul R X) = ∑ b, columnSq (fun u => X u b) R := by
    unfold realFrobSq signMul columnSq signedSum
    exact Finset.sum_comm
  have hX : realFrobSq X = ∑ b, energy (fun u => X u b) := by
    unfold realFrobSq energy
    exact Finset.sum_comm
  constructor
  · simp_rw [heq]
    rw [mean_sum]
    simp_rw [column_first, ← Finset.mul_sum, ← hX]
  · have hs (f : Fin t → ℝ) : (∑ b, f b)^2 = ∑ b, ∑ c, f b * f c := by
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    simp_rw [heq, hs]
    rw [mean_sum]
    simp_rw [mean_sum]
    calc
      _ ≤ ∑ b : Fin t, ∑ c : Fin t,
          (((ℓ : ℝ)^2 + 2*ℓ) * energy (fun u => X u b) * energy (fun u => X u c)) := by
        apply Finset.sum_le_sum
        intro b _
        apply Finset.sum_le_sum
        intro c _
        apply correlation_bound _ _ _ _ _ (by positivity)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        · exact column_second ℓ d _
        · exact column_second ℓ d _
      _ = ((ℓ : ℝ)^2 + 2*ℓ) * realFrobSq X ^ 2 := by
        rw [hX, hs]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro c _
        ring

end KoanaKPaths.Main.SignMoments

theorem solution (ℓ d t : ℕ) (X : Fin d → Fin t → ℝ) :
    KoanaKPaths.Main.uniformMean (fun R : Fin ℓ → Fin d → Bool =>
      KoanaKPaths.Main.realFrobSq (KoanaKPaths.Main.signMul R X)) =
        (ℓ : ℝ) * KoanaKPaths.Main.realFrobSq X ∧
      KoanaKPaths.Main.uniformMean (fun R : Fin ℓ → Fin d → Bool =>
        KoanaKPaths.Main.realFrobSq (KoanaKPaths.Main.signMul R X) ^ 2) ≤
        ((ℓ : ℝ)^2 + 2*ℓ) * KoanaKPaths.Main.realFrobSq X ^ 2 := by
  exact KoanaKPaths.Main.SignMoments.finite_matrix_moments ℓ d t X
