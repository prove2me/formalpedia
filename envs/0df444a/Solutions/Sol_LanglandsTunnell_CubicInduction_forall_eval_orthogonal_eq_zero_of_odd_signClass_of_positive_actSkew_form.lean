-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b6336b21-3a9e-5c7f-87eb-74b8893c3020

import Mathlib
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_eval_eq_det_pow_mul_entry_of_odd_signClass_of_actStable
import Theorems.Thm_LanglandsTunnell_CubicInduction_form_eq_zero_of_rotationCasimir_eigen_ne_of_actSkew
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_diag_row_eq_and_harmonic_split
import Theorems.Thm_LanglandsTunnell_CubicInduction_eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic
import Theorems.Thm_LanglandsTunnell_CubicInduction_eval_inducedPicture_act_eq_zero_of_forall_eval_orthogonal_eq_zero
import Theorems.Thm_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form

set_option autoImplicit false

open LanglandsTunnell.CubicInduction

namespace OddNH

noncomputable def actP (ν : Fin 3 → ℂ) (c d : Fin 3) (p : MvPolynomial (Fin 3 × Fin 3) ℂ) : MvPolynomial (Fin 3 × Fin 3) ℂ :=
  (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p

theorem actP_add (ν : Fin 3 → ℂ) (c d : Fin 3) (p q : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    actP ν c d (p + q) = actP ν c d p + actP ν c d q := by
  simp only [actP, map_add, mul_add, Finset.sum_add_distrib]
  ring

theorem actP_smul (ν : Fin 3 → ℂ) (c d : Fin 3) (z : ℂ) (p : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    actP ν c d (z • p) = z • actP ν c d p := by
  simp only [actP, smul_add, Finset.smul_sum]
  congr 1
  · rw [mul_smul_comm]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Derivation.map_smul, mul_smul_comm]

theorem actP_sub (ν : Fin 3 → ℂ) (c d : Fin 3) (p q : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    actP ν c d (p - q) = actP ν c d p - actP ν c d q := by
  rw [sub_eq_add_neg, actP_add, ← neg_one_smul ℂ q, actP_smul, neg_one_smul, ← sub_eq_add_neg]

noncomputable def OmP (ν : Fin 3 → ℂ) (P : MvPolynomial (Fin 3 × Fin 3) ℂ) : MvPolynomial (Fin 3 × Fin 3) ℂ :=
  (actP ν 0 1 (actP ν 0 1 P - actP ν 1 0 P) - actP ν 1 0 (actP ν 0 1 P - actP ν 1 0 P)) +
    (actP ν 0 2 (actP ν 0 2 P - actP ν 2 0 P) - actP ν 2 0 (actP ν 0 2 P - actP ν 2 0 P)) +
    (actP ν 1 2 (actP ν 1 2 P - actP ν 2 1 P) - actP ν 2 1 (actP ν 1 2 P - actP ν 2 1 P))

theorem OmP_sub (ν : Fin 3 → ℂ) (P Q : MvPolynomial (Fin 3 × Fin 3) ℂ) : OmP ν (P - Q) = OmP ν P - OmP ν Q := by
  simp only [OmP, actP_sub]
  abel

theorem actP_vanish (ν : Fin 3 → ℂ) (c d : Fin 3) (P : MvPolynomial (Fin 3 × Fin 3) ℂ)
    (hP : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0) :
    ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (actP ν c d P) = 0 :=
  fun o ho => eval_inducedPicture_act_eq_zero_of_forall_eval_orthogonal_eq_zero ν c d P hP o ho

theorem OmP_vanish (ν : Fin 3 → ℂ) (P : MvPolynomial (Fin 3 × Fin 3) ℂ)
    (hP : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0) :
    ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (OmP ν P) = 0 := by
  have hsub : ∀ A B : MvPolynomial (Fin 3 × Fin 3) ℂ,
      (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) A = 0) →
      (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) B = 0) →
      ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (A - B) = 0 := by
    intro A B hA hB o ho; rw [map_sub, hA o ho, hB o ho, sub_zero]
  have hadd : ∀ A B : MvPolynomial (Fin 3 × Fin 3) ℂ,
      (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) A = 0) →
      (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) B = 0) →
      ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (A + B) = 0 := by
    intro A B hA hB o ho; rw [map_add, hA o ho, hB o ho, add_zero]
  have h1 : ∀ c d : Fin 3, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (actP ν c d P) = 0 :=
    fun c d => actP_vanish ν c d P hP
  have h2 : ∀ a b c d : Fin 3, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (actP ν a b (actP ν c d P - actP ν d c P)) = 0 :=
    fun a b c d => actP_vanish ν a b _ (hsub _ _ (h1 c d) (h1 d c))
  unfold OmP
  exact hadd _ _ (hadd _ _ (hsub _ _ (h2 0 1 0 1) (h2 1 0 0 1)) (hsub _ _ (h2 0 2 0 2) (h2 2 0 0 2)))
    (hsub _ _ (h2 1 2 1 2) (h2 2 1 1 2))

theorem actP_det_pow (ν : Fin 3 → ℂ) (c d : Fin 3) (n : ℕ) (P : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    actP ν c d ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det ^ n * P) =
      (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det ^ n * actP ν c d P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_comm (_ ^ n), mul_assoc, mul_assoc, ← ih]
    exact inducedPicture_act_det_mul ν c d _

theorem eval_detX (o : Fin 3 → Fin 3 → ℝ) :
    MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det =
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

theorem perm_orth (τ : Equiv.Perm (Fin 3)) :
    ∀ i j : Fin 3, ∑ a : Fin 3, (fun a b : Fin 3 => if τ a = b then (1 : ℝ) else 0) a i *
      (fun a b : Fin 3 => if τ a = b then (1 : ℝ) else 0) a j = if i = j then 1 else 0 := by
  intro i j
  simp only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single_of_mem (τ.symm i) (Finset.mem_univ _)]
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · intro a _ ha
    have : τ a ≠ i := fun h' => ha (by rw [← h', Equiv.symm_apply_apply])
    simp [this]

theorem perm_det_ne_zero (τ : Equiv.Perm (Fin 3)) :
    (Matrix.of fun i j : Fin 3 => (((fun a b : Fin 3 => if τ a = b then (1 : ℝ) else 0) i j : ℝ) : ℂ)).det ≠ 0 := by
  have : (Matrix.of fun i j : Fin 3 => (((fun a b : Fin 3 => if τ a = b then (1 : ℝ) else 0) i j : ℝ) : ℂ)) =
      (τ.toPEquiv.toMatrix : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    simp only [Matrix.of_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq]
    by_cases h : τ i = j
    · simp [h]
    · have h' : ¬ j = τ i := fun e => h e.symm
      simp [h, h']
  rw [this, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

end OddNH

namespace OddNH

theorem O4w (ν : Fin 3 → ℂ) (m a : Fin 3) :
    ∃ p₃ : MvPolynomial (Fin 3) ℂ, p₃.IsHomogeneous 3 ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p₃)) = 0 ∧
      actP ν a a (MvPolynomial.X (m, a)) =
        MvPolynomial.C ((ν 0 + ν 1 + ν 2 + 2 * ν m) / 5) * MvPolynomial.X (m, a) *
            (∑ c : Fin 3, MvPolynomial.X (c, a) ^ 2) +
          MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, a) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p₃ := by
  obtain ⟨h1, h2, h3⟩ := inducedPicture_act_diag_row_eq_and_harmonic_split ν m a
  refine ⟨MvPolynomial.X m * ∑ c : Fin 3,
      MvPolynomial.C ((ν c + (![1, 0, -1] : Fin 3 → ℂ) c + (if c < m then (1 : ℂ) else if m < c then (-1 : ℂ) else 0)) -
        (ν 0 + ν 1 + ν 2 + 2 * ν m) / 5) * MvPolynomial.X c ^ 2, ?_, ?_, ?_⟩
  · have hs : (∑ c : Fin 3,
        MvPolynomial.C ((ν c + (![1, 0, -1] : Fin 3 → ℂ) c + (if c < m then (1 : ℂ) else if m < c then (-1 : ℂ) else 0)) -
          (ν 0 + ν 1 + ν 2 + 2 * ν m) / 5) * MvPolynomial.X c ^ 2 : MvPolynomial (Fin 3) ℂ).IsHomogeneous 2 :=
      MvPolynomial.IsHomogeneous.sum _ _ _ fun c _ => by
        have h := (MvPolynomial.isHomogeneous_C (Fin 3)
          ((ν c + (![1, 0, -1] : Fin 3 → ℂ) c + (if c < m then (1 : ℂ) else if m < c then (-1 : ℂ) else 0)) -
            (ν 0 + ν 1 + ν 2 + 2 * ν m) / 5)).mul ((MvPolynomial.isHomogeneous_X ℂ c).pow 2)
        exact h
    have h := (MvPolynomial.isHomogeneous_X ℂ m).mul hs
    exact h
  · exact h3
  · exact h1.trans h2

end OddNH

theorem solution
    (σ σ₃ : ℝ) (b₀ c₀ : Fin 3) (hb₀ : b₀ ≠ 0) (hc₀ : c₀ ≠ 0) (hbc : b₀ ≠ c₀)
    (ν : Fin 3 → ℂ) (hν0 : ν 0 = -1 / 2 + σ * Complex.I) (hνb : ν b₀ = 1 / 2 + σ * Complex.I)
    (hνc : ν c₀ = σ₃ * Complex.I)
    (ε : Fin 3 → Fin 2) (hodd : ε 0 ≠ ε b₀)
    (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ))
    (β : MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ → ℂ) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    (∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W) →
    (∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P ∈ W) →
    (∀ P ∈ W, ∀ τ : Fin 3 → Fin 2, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => (((∑ c : Fin 3, (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) ij.1 c * o c ij.2) : ℝ) : ℂ)) P =
          (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P) →
    (∀ (z : ℂ), ∀ P₁ ∈ W, ∀ P₂ ∈ W, ∀ Q ∈ W, β (z • P₁ + P₂) Q = z * β P₁ Q + β P₂ Q) →
    (∀ P ∈ W, ∀ Q ∈ W, β Q P = (starRingEnd ℂ) (β P Q)) →
    (∀ P ∈ W, (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0) → ∀ Q ∈ W, β P Q = 0) →
    (∀ P ∈ W, (∃ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) ∧ MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P ≠ 0) → 0 < (β P P).re) →
    (∀ P ∈ W, ∀ Q ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        β (MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P)
          (MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) Q) = β P Q) →
    (∀ P ∈ W, ∀ Q ∈ W, ∀ c d : Fin 3, β (act ν c d P) Q = -β P (act ν c d Q)) →
    ∀ P ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) P = 0 := by
  intro act hact hrst hiso hlin hherm hnull hpos hinv hskew P hP o ho
  by_contra hne

  obtain ⟨m, hm, j, Q, hQ, hQread⟩ :=
    exists_mem_eval_eq_det_pow_mul_entry_of_odd_signClass_of_actStable σ σ₃ b₀ c₀ hb₀ hc₀ hbc ν hν0 hνb hνc
      ε hodd W hact hrst hiso ⟨P, hP, o, ho, hne⟩

  set u : MvPolynomial (Fin 3 × Fin 3) ℂ := (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det ^ (ε c₀ : ℕ) * MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (MvPolynomial.X m : MvPolynomial (Fin 3) ℂ) with hu
  have hu_eval : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) u = (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ (ε c₀ : ℕ) * ((o m j : ℝ) : ℂ) := by
    intro o ho
    rw [hu, map_mul, map_pow, OddNH.eval_detX, MvPolynomial.aeval_X, MvPolynomial.eval_X]
  have hQu : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (Q - u) = 0 := by
    intro o ho; rw [map_sub, hQread o ho, hu_eval o ho, sub_self]

  obtain ⟨p₃, hp₃hom, hp₃harm, h4⟩ := OddNH.O4w ν m j
  set lam : ℂ := (ν 0 + ν 1 + ν 2 + 2 * ν m) / 5 with hlam

  have hA : OddNH.actP ν j j Q ∈ W := hact Q hQ j j
  set R : MvPolynomial (Fin 3 × Fin 3) ℂ := OddNH.actP ν j j Q - lam • Q with hR
  have hRW : R ∈ W := W.sub_mem hA (W.smul_mem lam hQ)
  set Rp : MvPolynomial (Fin 3 × Fin 3) ℂ := (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det ^ (ε c₀ : ℕ) * MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p₃ with hRp

  have hsumsq : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (∑ c : Fin 3, MvPolynomial.X (c, j) ^ 2) = 1 := by
    intro o ho
    simp only [map_sum, map_pow, MvPolynomial.eval_X]
    have := ho j j
    simp only [if_true] at this
    have h' : ∑ c : Fin 3, ((o c j : ℝ) : ℂ) ^ 2 = (((∑ a : Fin 3, o a j * o a j) : ℝ) : ℂ) := by
      push_cast; exact Finset.sum_congr rfl fun c _ => by ring
    rw [h', this]; norm_num
  have hRRp : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (R - Rp) = 0 := by
    intro o ho
    have h1 : MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (OddNH.actP ν j j Q) = MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (OddNH.actP ν j j u) := by
      rw [← sub_eq_zero, ← map_sub, ← OddNH.actP_sub]
      exact OddNH.actP_vanish ν j j _ hQu o ho
    have h2 : OddNH.actP ν j j u = (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det ^ (ε c₀ : ℕ) *
        (MvPolynomial.C lam * MvPolynomial.X (m, j) * (∑ c : Fin 3, MvPolynomial.X (c, j) ^ 2) +
          MvPolynomial.aeval (fun b : Fin 3 => (MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p₃) := by
      rw [hu, OddNH.actP_det_pow, MvPolynomial.aeval_X, h4]
    rw [map_sub, hR, hRp, map_sub, MvPolynomial.smul_eval, h1, h2, map_mul, map_mul, map_add, map_mul, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, hsumsq o ho, map_pow, OddNH.eval_detX, hQread o ho]
    ring

  have hΩR : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (OddNH.OmP ν R) = -(((3 : ℕ) : ℂ) * (((3 : ℕ) : ℂ) + 1)) * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) R := by
    intro o ho
    have hv := OddNH.OmP_vanish ν (R - Rp) hRRp o ho
    rw [OddNH.OmP_sub, map_sub, sub_eq_zero] at hv
    have hR' : MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) R = MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Rp := by
      have := hRRp o ho; rwa [map_sub, sub_eq_zero] at this
    rw [hv, hR', hRp]
    exact eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic ν 3 p₃ hp₃hom hp₃harm j (ε c₀ : ℕ) o ho
  have hXm_harm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
      (MvPolynomial.X m : MvPolynomial (Fin 3) ℂ))) = 0 := by
    simp [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite]
  have hΩQ : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (OddNH.OmP ν Q) = -(((1 : ℕ) : ℂ) * (((1 : ℕ) : ℂ) + 1)) * MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q := by
    intro o ho
    have hv := OddNH.OmP_vanish ν (Q - u) hQu o ho
    rw [OddNH.OmP_sub, map_sub, sub_eq_zero] at hv
    have hQ' : MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q = MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) u := by
      have := hQu o ho; rwa [map_sub, sub_eq_zero] at this
    rw [hv, hQ', hu]
    exact eval_rotationCasimir_det_pow_mul_columnRealisation_eq_of_harmonic ν 1 (MvPolynomial.X m : MvPolynomial (Fin 3) ℂ)
      (MvPolynomial.isHomogeneous_X ℂ m) hXm_harm j (ε c₀ : ℕ) o ho

  have hκ : (-(((3 : ℕ) : ℂ) * (((3 : ℕ) : ℂ) + 1))) ≠ -(((1 : ℕ) : ℂ) * (((1 : ℕ) : ℂ) + 1)) := by norm_num
  have hβRQ : β R Q = 0 :=
    form_eq_zero_of_rotationCasimir_eigen_ne_of_actSkew ν W β _ _ hκ R Q hRW hQ hact hlin hherm hnull hpos hskew
      hΩR hΩQ

  have hAeq : OddNH.actP ν j j Q = lam • Q + R := by rw [hR]; abel
  have hβAQ : β (OddNH.actP ν j j Q) Q = lam * β Q Q := by
    rw [hAeq, hlin lam Q hQ R hRW Q hQ, hβRQ, add_zero]
  have hsk : β (OddNH.actP ν j j Q) Q = - β Q (OddNH.actP ν j j Q) := hskew Q hQ Q hQ j j
  have hhe : β Q (OddNH.actP ν j j Q) = (starRingEnd ℂ) (β (OddNH.actP ν j j Q) Q) := hherm _ hA Q hQ
  have hre0 : (lam * β Q Q).re = 0 := by
    rw [← hβAQ]
    have h := hsk; rw [hhe] at h
    have := congrArg Complex.re h
    simp at this
    linarith

  have hQQim : (β Q Q).im = 0 := by
    have := congrArg Complex.im (hherm Q hQ Q hQ)
    simp at this
    linarith
  have hQQpos : 0 < (β Q Q).re := by
    refine hpos Q hQ ⟨fun a b => if (Equiv.swap m j) a = b then (1 : ℝ) else 0, OddNH.perm_orth _, ?_⟩
    rw [hQread _ (OddNH.perm_orth _)]
    refine mul_ne_zero (pow_ne_zero _ (OddNH.perm_det_ne_zero _)) ?_
    simp [Equiv.swap_apply_left]
  have hlamre : lam.re = 0 := by
    have : (lam * β Q Q).re = lam.re * (β Q Q).re := by rw [Complex.mul_re, hQQim, mul_zero, sub_zero]
    rw [this] at hre0
    rcases mul_eq_zero.1 hre0 with h | h
    · exact h
    · exact absurd h hQQpos.ne'

  have h5 : (ν 0 + ν 1 + ν 2 + 2 * ν m).re = 0 := by
    have : ν 0 + ν 1 + ν 2 + 2 * ν m = 5 * lam := by rw [hlam]; ring
    rw [this, Complex.mul_re, hlamre]
    simp
  have key : ∀ b c m' : Fin 3, b ≠ 0 → c ≠ 0 → b ≠ c → m' ≠ c →
      (b = 1 ∧ c = 2 ∧ (m' = 0 ∨ m' = 1)) ∨ (b = 2 ∧ c = 1 ∧ (m' = 0 ∨ m' = 2)) := by decide
  rcases key b₀ c₀ m hb₀ hc₀ hbc hm with ⟨hb1, hc2, hm'⟩ | ⟨hb2, hc1, hm'⟩
  · rw [hb1] at hνb; rw [hc2] at hνc
    rcases hm' with hm0 | hm1
    · rw [hm0, hν0, hνb, hνc] at h5; simp at h5; norm_num at h5
    · rw [hm1, hν0, hνb, hνc] at h5; simp at h5; norm_num at h5
  · rw [hb2] at hνb; rw [hc1] at hνc
    rcases hm' with hm0 | hm2
    · rw [hm0, hν0, hνb, hνc] at h5; simp at h5; norm_num at h5
    · rw [hm2, hν0, hνb, hνc] at h5; simp at h5; norm_num at h5

end S_LanglandsTunnell_CubicInduction_forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_forall_eval_orthogonal_eq_zero_of_odd_signClass_of_positive_actSkew_form (solution)
