-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.finite_geometry_batch_23
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T06:22:04.192926+00:00
-- url     : https://prove2.me/submissions/12452242-a585-441b-9c22-6154695a6095

import Definitions.Def_SidorenkoCertificateBundleB
set_option linter.unusedVariables false
section
variable [p0 : OAI.SidorenkoCounterexample.ProofCertificate_0617]
  [p1 : OAI.SidorenkoCounterexample.ProofCertificate_0618]
  [p2 : OAI.SidorenkoCounterexample.ProofCertificate_0619]
  [p3 : OAI.SidorenkoCounterexample.ProofCertificate_0627]
  [p4 : OAI.SidorenkoCounterexample.ProofCertificate_0628]
  [p5 : OAI.SidorenkoCounterexample.ProofCertificate_0629]
  [p6 : OAI.SidorenkoCounterexample.ProofCertificate_0632]
  [p7 : OAI.SidorenkoCounterexample.ProofCertificate_0635]
  [p8 : OAI.SidorenkoCounterexample.ProofCertificate_0636]
  [p9 : OAI.SidorenkoCounterexample.ProofCertificate_0652]
  [p10 : OAI.SidorenkoCounterexample.ProofCertificate_0653]
include p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10

namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
section Forms
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end Forms
section Pullback
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end Pullback
section MatrixForms
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
end MatrixForms
end SidorenkoCounterexample
namespace SidorenkoCounterexample
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FiniteLayer
variable (K : Type) [Field K] (D : ℕ)
variable [Fintype K] [DecidableEq K]
noncomputable instance : Fintype (SymMatrix K D) := Fintype.ofFinite _
end FiniteLayer
instance (q : OddPrime) : Fact q.val.Prime := ⟨q.property.1⟩
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Border
variable {K : Type} [Field K]
end Border
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {A B : Type} [Fintype A] [Fintype B]
theorem certificate_proof_0654 (e : A ≃ B) (f : B → ℝ) :
    uniformMean (f ∘ e) = uniformMean f := by
  unfold uniformMean
  dsimp only [Function.comp_def]
  rw [Fintype.card_congr e, Equiv.sum_comp e f]

private instance certificate_instance_0654 : OAI.SidorenkoCounterexample.ProofCertificate_0654 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0654 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0655 (f : A × B → ℝ) :
    uniformMean f = uniformMean fun a => uniformMean fun b => f (a,b) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp_rw [← Finset.sum_div]
  ring

private instance certificate_instance_0655 : OAI.SidorenkoCounterexample.ProofCertificate_0655 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0655 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4

theorem certificate_proof_0656 [Nonempty A] (c : ℝ) : uniformMean (fun _ : A => c) = c := by
  simp [uniformMean, (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := A)) :
    (Fintype.card A : ℝ) ≠ 0)]

private instance certificate_instance_0656 : OAI.SidorenkoCounterexample.ProofCertificate_0656 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0656 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3

theorem certificate_proof_0657 (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

private instance certificate_instance_0657 : OAI.SidorenkoCounterexample.ProofCertificate_0657 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0657 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3

theorem certificate_proof_0658 (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

private instance certificate_instance_0658 : OAI.SidorenkoCounterexample.ProofCertificate_0658 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0658 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3

theorem certificate_proof_0659 (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]

private instance certificate_instance_0659 : OAI.SidorenkoCounterexample.ProofCertificate_0659 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0659 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3

theorem certificate_proof_0660 {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    uniformMean f ≤ uniformMean g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun a _ => h a

private instance certificate_instance_0660 : OAI.SidorenkoCounterexample.ProofCertificate_0660 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0660 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4

theorem certificate_proof_0661 {f : A → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f :=
  div_nonneg (Finset.sum_nonneg fun a _ => h a) (Nat.cast_nonneg _)

private instance certificate_instance_0661 : OAI.SidorenkoCounterexample.ProofCertificate_0661 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0661 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3

theorem certificate_proof_0662 (f : A → ℝ) :
    |uniformMean f| ≤ uniformMean fun a => |f a| := by
  unfold uniformMean
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card A from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs ..) (Nat.cast_nonneg _)

private instance certificate_instance_0662 : OAI.SidorenkoCounterexample.ProofCertificate_0662 := by
  constructor
  intro q0 q1 q2
  exact @certificate_proof_0662 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2

theorem certificate_proof_0663 [Nonempty A] {f : A → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) :
    uniformMean f ≤ c := by
  simpa only [uniformMean_const] using uniformMean_mono h

private instance certificate_instance_0663 : OAI.SidorenkoCounterexample.ProofCertificate_0663 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0663 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0664 (p : A → Prop) [DecidablePred p] :
    uniformMean (fun a => if p a then 1 else 0) =
      (Fintype.card {a // p a} : ℝ) / Fintype.card A := by
  simp [uniformMean, Fintype.card_subtype, Finset.sum_boole]

private instance certificate_instance_0664 : OAI.SidorenkoCounterexample.ProofCertificate_0664 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0664 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3

end Mean
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Scalar
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0665 (ξ : ℤ) (a : K) : 0 ≤ characterSignIndicator ξ a := by
  unfold characterSignIndicator; split <;> norm_num

private instance certificate_instance_0665 : OAI.SidorenkoCounterexample.ProofCertificate_0665 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0665 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0666 (ξ : ℤ) (a : K) : characterSignIndicator ξ a ≤ 1 := by
  unfold characterSignIndicator; split <;> norm_num

private instance certificate_instance_0666 : OAI.SidorenkoCounterexample.ProofCertificate_0666 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0666 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0667 {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) (a : K) :
    2 * characterSignIndicator ξ a =
      (if a = 0 then 0 else 1) + (ξ : ℝ) * (quadraticChar K a : ℝ) := by
  by_cases ha : a = 0
  · rcases hξ with rfl | rfl <;> simp [characterSignIndicator, ha]
  · rcases quadraticChar_dichotomy ha with hc | hc <;>
      rcases hξ with rfl | rfl <;> norm_num [characterSignIndicator, hc, ha]

private instance certificate_instance_0667 : OAI.SidorenkoCounterexample.ProofCertificate_0667 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0667 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6

omit [Field K] in
theorem certificate_proof_0668 (b : K) :
    uniformMean (fun a : K => if a = b then 1 else 0) = 1 / (Fintype.card K : ℝ) := by
  simp [uniformMean]

private instance certificate_instance_0668 : OAI.SidorenkoCounterexample.ProofCertificate_0668 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0668 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3

theorem certificate_proof_0669 :
    uniformMean (fun a : K => if a = 0 then 0 else 1) = 1 - 1 / (Fintype.card K : ℝ) := by
  have h := uniformMean_sub (fun _ : K => (1 : ℝ)) (fun a => if a = 0 then 1 else 0)
  simp only [uniformMean_const, uniformMean_singleton] at h
  rw [← h]
  apply uniformMean_congr
  intro a; split <;> simp_all

private instance certificate_instance_0669 : OAI.SidorenkoCounterexample.ProofCertificate_0669 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0669 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3

theorem certificate_proof_0670 (hK : ringChar K ≠ 2) :
    uniformMean (fun a : K => (quadraticChar K a : ℝ)) = 0 := by
  unfold uniformMean
  have h : (∑ a : K, (quadraticChar K a : ℝ)) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hK
  rw [h, zero_div]

private instance certificate_instance_0670 : OAI.SidorenkoCounterexample.ProofCertificate_0670 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0670 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4

theorem certificate_proof_0671 (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    uniformMean (characterSignIndicator (K := K) ξ) =
      (1 - 1 / (Fintype.card K : ℝ)) / 2 := by
  have h := uniformMean_congr (characterSignIndicator_formula (K := K) hξ)
  rw [uniformMean_mul, uniformMean_add, uniformMean_nonzero,
    uniformMean_mul, uniformMean_character hK, mul_zero, add_zero] at h
  linarith

 
private instance certificate_instance_0671 : OAI.SidorenkoCounterexample.ProofCertificate_0671 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0671 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6

omit [DecidableEq K] in
theorem certificate_proof_0672 (c b : K) (hc : c ≠ 0) (f : K → ℝ) :
    uniformMean (fun a => f (c * (a-b))) = uniformMean f :=
  uniformMean_equiv (scalarAffineEquiv c b hc) f

private instance certificate_instance_0672 : OAI.SidorenkoCounterexample.ProofCertificate_0672 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6
  exact @certificate_proof_0672 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6

end Scalar
section MatrixSign
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
theorem certificate_proof_0673 {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
    (hM : M.val.det ≠ 0) :
    uniformMean (fun a => if (symmetricBorder M z a).val.det = 0 then 1 else 0) =
      1 / (Fintype.card K : ℝ) := by
  simp_rw [symmetricBorder_det M z _ hM, mul_eq_zero, hM, false_or, sub_eq_zero]
  exact uniformMean_singleton _

private instance certificate_instance_0673 : OAI.SidorenkoCounterexample.ProofCertificate_0673 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0673 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0674 {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
    (hM : M.val.det ≠ 0) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    uniformMean (fun a => characterSignIndicator ξ (symmetricBorder M z a).val.det) =
      (1 - 1 / (Fintype.card K : ℝ)) / 2 := by
  simp_rw [symmetricBorder_det M z _ hM]
  rw [uniformMean_affine _ _ hM, uniformMean_characterSignIndicator hK hξ]

private instance certificate_instance_0674 : OAI.SidorenkoCounterexample.ProofCertificate_0674 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0674 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0675 (n : ℕ) : 0 ≤ symmetricSingularProb (K := K) n := by
  apply uniformMean_nonneg; intro M; split <;> norm_num

private instance certificate_instance_0675 : OAI.SidorenkoCounterexample.ProofCertificate_0675 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0675 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4

theorem certificate_proof_0676 : symmetricSingularProb (K := K) 0 = 0 := by
  unfold symmetricSingularProb
  simp [Matrix.det_isEmpty, uniformMean]

private instance certificate_instance_0676 : OAI.SidorenkoCounterexample.ProofCertificate_0676 := by
  constructor
  intro q0 q1 q2 q3
  exact @certificate_proof_0676 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3

theorem certificate_proof_0677 (n : ℕ) :
    symmetricSingularProb (K := K) (n+1) ≤
      symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ) := by
  classical
  unfold symmetricSingularProb
  rw [← uniformMean_equiv (symmetricBorderEquiv (K := K) n).symm,
    uniformMean_prod]
  dsimp only [Function.comp_def, symmetricBorderEquiv, Equiv.coe_fn_symm_mk]
  calc
    _ ≤ uniformMean (fun M : SymMatrix K n =>
        (if M.val.det = 0 then 1 else 0) + 1 / (Fintype.card K : ℝ)) := by
      apply uniformMean_mono
      intro M
      rw [uniformMean_prod]
      by_cases hM : M.val.det = 0
      · simp only [hM, ite_true]
        apply le_trans (show uniformMean (fun z => uniformMean (fun a =>
          if (symmetricBorder M z a).val.det = 0 then 1 else 0)) ≤ 1 from
          uniformMean_bound fun z => uniformMean_bound fun a => by split <;> norm_num)
        have : (0 : ℝ) ≤ 1 / (Fintype.card K : ℝ) := by positivity
        linarith
      · simp only [hM, ite_false, zero_add]
        simp_rw [border_singularMean M _ hM]
        exact le_of_eq (uniformMean_const _)
    _ = _ := by rw [uniformMean_add, uniformMean_const]

private instance certificate_instance_0677 : OAI.SidorenkoCounterexample.ProofCertificate_0677 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0677 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4

theorem certificate_proof_0678 (n : ℕ) :
    symmetricSingularProb (K := K) n ≤ n / (Fintype.card K : ℝ) := by
  induction n with
  | zero => simp [symmetricSingularProb_zero]
  | succ n ih =>
    calc
      _ ≤ symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ) :=
        symmetricSingularProb_succ n
      _ ≤ n / (Fintype.card K : ℝ) + 1 / (Fintype.card K : ℝ) := by linarith
      _ = _ := by push_cast; ring

private instance certificate_instance_0678 : OAI.SidorenkoCounterexample.ProofCertificate_0678 := by
  constructor
  intro q0 q1 q2 q3 q4
  exact @certificate_proof_0678 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4

theorem certificate_proof_0679 (n : ℕ) (ξ : ℤ) : 0 ≤ symmetricSignProb (K := K) n ξ :=
  uniformMean_nonneg fun _ => characterSignIndicator_nonneg ..

private instance certificate_instance_0679 : OAI.SidorenkoCounterexample.ProofCertificate_0679 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0679 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0680 (n : ℕ) (ξ : ℤ) : symmetricSignProb (K := K) n ξ ≤ 1 :=
  uniformMean_bound fun _ => characterSignIndicator_le_one ..

private instance certificate_instance_0680 : OAI.SidorenkoCounterexample.ProofCertificate_0680 := by
  constructor
  intro q0 q1 q2 q3 q4 q5
  exact @certificate_proof_0680 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5

theorem certificate_proof_0681 (n : ℕ) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    |symmetricSignProb (K := K) (n+1) ξ - 1/2| ≤
      symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ) := by
  classical
  have hq : (0 : ℝ) ≤ 1 / (Fintype.card K : ℝ) := by positivity
  unfold symmetricSignProb
  rw [← uniformMean_equiv (symmetricBorderEquiv (K := K) n).symm, uniformMean_prod]
  dsimp only [Function.comp_def, symmetricBorderEquiv, Equiv.coe_fn_symm_mk]
  rw [← uniformMean_const (A := SymMatrix K n) (1/2), ← uniformMean_sub]
  calc
    _ ≤ uniformMean (fun M : SymMatrix K n =>
      |uniformMean (fun za : (Fin n → K) × K =>
        characterSignIndicator ξ (symmetricBorder M za.1 za.2).val.det) - 1/2|) :=
      abs_uniformMean_le _
    _ ≤ uniformMean (fun M : SymMatrix K n =>
        (if M.val.det = 0 then 1 else 0) + 1 / (Fintype.card K : ℝ)) := by
      apply uniformMean_mono
      intro M
      rw [uniformMean_prod]
      by_cases hM : M.val.det = 0
      · simp only [hM, ite_true]
        have h0 := uniformMean_nonneg (fun z : Fin n → K =>
          uniformMean_nonneg fun a => characterSignIndicator_nonneg ξ
            (symmetricBorder M z a).val.det)
        have h1 := uniformMean_bound (fun z : Fin n → K =>
          uniformMean_bound fun a => characterSignIndicator_le_one ξ
            (symmetricBorder M z a).val.det)
        apply abs_le.mpr
        constructor <;> linarith
      · simp only [hM, ite_false, zero_add]
        simp_rw [border_signMean M _ hM hK hξ]
        rw [uniformMean_const]
        apply abs_le.mpr
        constructor <;> linarith
    _ = _ := by rw [uniformMean_add, uniformMean_const]; rfl

private instance certificate_instance_0681 : OAI.SidorenkoCounterexample.ProofCertificate_0681 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0681 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0682 (n : ℕ) (hn : 0 < n) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    |symmetricSignProb (K := K) n ξ - 1/2| ≤ n / (Fintype.card K : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  calc
    _ ≤ symmetricSingularProb (K := K) m + 1 / (Fintype.card K : ℝ) :=
      symmetricSignProb_succ_error m hK hξ
    _ ≤ m / (Fintype.card K : ℝ) + 1 / (Fintype.card K : ℝ) := by
      have := symmetricSingularProb_bound (K := K) m
      linarith
    _ = _ := by push_cast; ring

private instance certificate_instance_0682 : OAI.SidorenkoCounterexample.ProofCertificate_0682 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8
  exact @certificate_proof_0682 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8

end MatrixSign
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
section NondegSign
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
theorem certificate_proof_0683 (B : LinearMap.BilinForm K V)
    (hBs : B.IsSymm) (hB : B.Nondegenerate)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) :
    discriminantSign B hBs = quadraticChar K (B.toMatrix b).det := by
  simpa only [LinearMap.compl₁₂_id_id] using
    discriminantSign_pullback B hBs hB LinearMap.id Function.surjective_id b

private instance certificate_instance_0683 : OAI.SidorenkoCounterexample.ProofCertificate_0683 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14
  exact @certificate_proof_0683 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14

end NondegSign
section SumForms
variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
theorem certificate_proof_0684 (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) (x y : V × W) :
    orthogonalSumForm A B x y = A x.1 y.1 + B x.2 y.2 := rfl

private instance certificate_instance_0684 : OAI.SidorenkoCounterexample.ProofCertificate_0684 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0684 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0685 (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) (hA : A.IsSymm) (hB : B.IsSymm) :
    (orthogonalSumForm A B).IsSymm := by
  constructor
  intro x y
  simp only [orthogonalSumForm_apply, hA.eq x.1 y.1, hB.eq x.2 y.2]

private instance certificate_instance_0685 : OAI.SidorenkoCounterexample.ProofCertificate_0685 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0685 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0686 (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) (hA : A.Nondegenerate) (hB : B.Nondegenerate) :
    (orthogonalSumForm A B).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hA.1
      intro y
      simpa using hx (y, 0)
    · apply hB.1
      intro y
      simpa using hx (0, y)
  · intro x hx
    apply Prod.ext
    · apply hA.2
      intro y
      simpa using hx (y, 0)
    · apply hB.2
      intro y
      simpa using hx (0, y)

private instance certificate_instance_0686 : OAI.SidorenkoCounterexample.ProofCertificate_0686 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0686 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0687 (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (b : Basis ι K V) (c : Basis κ K W) :
    (orthogonalSumForm A B).toMatrix (b.prod c) =
      Matrix.fromBlocks (A.toMatrix b) 0 0 (B.toMatrix c) := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Basis.prod_apply]

private instance certificate_instance_0687 : OAI.SidorenkoCounterexample.ProofCertificate_0687 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17
  exact @certificate_proof_0687 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 q16 q17

variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
theorem certificate_proof_0688 (A B : LinearMap.BilinForm K V)
    (hA : A.IsSymm) (hB : B.IsSymm) (hS : (A+B).Nondegenerate)
    (hdim : finrank K (V ⧸ A.ker) + finrank K (V ⧸ B.ker) = finrank K V) :
    discriminantSign (A+B) (hA.add hB) = discriminantSign A hA * discriminantSign B hB := by
  classical
  let AQ := radicalQuotientForm A hA
  let BQ := radicalQuotientForm B hB
  let C := orthogonalSumForm AQ BQ
  have hCs : C.IsSymm := orthogonalSumForm_isSymm _ _
    (radicalQuotientForm_isSymm A hA) (radicalQuotientForm_isSymm B hB)
  have hC : C.Nondegenerate := orthogonalSumForm_nondegenerate _ _
    (radicalQuotientForm_nondegenerate A hA) (radicalQuotientForm_nondegenerate B hB)
  let f : V →ₗ[K] (V ⧸ A.ker) × (V ⧸ B.ker) := A.ker.mkQ.prod B.ker.mkQ
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    change f x = 0 at hx
    have ha : A x = 0 := (Submodule.Quotient.mk_eq_zero A.ker).mp (congrArg Prod.fst hx)
    have hb : B x = 0 := (Submodule.Quotient.mk_eq_zero B.ker).mp (congrArg Prod.snd hx)
    apply hS.1
    intro y
    simp only [LinearMap.add_apply, ha, hb, LinearMap.zero_apply, add_zero]
  have hfs : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      simpa only [Module.finrank_prod] using hdim.symm)).mp hfi
  have he : C.compl₁₂ f f = A+B := by ext x y; rfl
  let b := Module.finBasis K (V ⧸ A.ker)
  let c := Module.finBasis K (V ⧸ B.ker)
  have hs := discriminantSign_pullback C hCs hC f hfs (b.prod c)
  simp only [he] at hs
  rw [hs]
  change quadraticChar K ((orthogonalSumForm AQ BQ).toMatrix (b.prod c)).det = _
  rw [orthogonalSumForm_matrix, Matrix.det_fromBlocks_zero₂₁, map_mul]
  rfl

private instance certificate_instance_0688 : OAI.SidorenkoCounterexample.ProofCertificate_0688 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13
  exact @certificate_proof_0688 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13

end SumForms
section PairSign
variable {K n : Type} [Field K] [Fintype n] [DecidableEq n]
variable [Fintype K] [DecidableEq K]
theorem certificate_proof_0689 (r : ℕ) (hdim : Fintype.card n = 2*r)
    (A B : Matrix n n K) (hAs : A.IsSymm) (hBs : B.IsSymm)
    (hB : B.det ≠ 0) (hAr : A.rank = r) (hCr : (A-B).rank = r) :
    quadraticChar K B.det = quadraticChar K ((-1 : K)^r) *
      discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hAs) *
      discriminantSign (A-B).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hAs.sub hBs)) := by
  classical
  have hAs' := Matrix.isSymm_toBilin'_iff_isSymm.mpr hAs
  have hCs' := Matrix.isSymm_toBilin'_iff_isSymm.mpr (hBs.sub hAs)
  have hadd : A.toBilin' + (B-A).toBilin' = B.toBilin' := by
    rw [← map_add, add_sub_cancel]
  have hBs' := Matrix.isSymm_toBilin'_iff_isSymm.mpr hBs
  have hBnd : B.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hB
  have hdim' : finrank K ((n → K) ⧸ A.toBilin'.ker) +
      finrank K ((n → K) ⧸ (B-A).toBilin'.ker) = finrank K (n → K) := by
    rw [matrix_radical_quotient_rank, matrix_radical_quotient_rank,
      show B-A = -(A-B) by abel, matrix_rank_neg, hAr, hCr, Module.finrank_pi, hdim]
    omega
  have hs := discriminantSign_add A.toBilin' (B-A).toBilin' hAs' hCs'
    (hadd.symm ▸ hBnd) hdim'
  simp only [hadd] at hs
  have hb := discriminantSign_nondegenerate B.toBilin' hBs' hBnd (Pi.basisFun K n)
  have hb' : discriminantSign B.toBilin' hBs' = quadraticChar K B.det := by
    simpa only [show B.toBilin'.toMatrix (Pi.basisFun K n) = B from
      LinearMap.BilinForm.toMatrix'_toBilin' B] using hb
  rw [hb'] at hs
  have hn := discriminantSign_neg (A-B).toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hAs.sub hBs))
  rw [matrix_radical_quotient_rank, hCr] at hn
  have hneg : -(A-B).toBilin' = (B-A).toBilin' := by
    rw [show B-A = -(A-B) by abel, map_neg]
  simp only [hneg] at hn
  rw [hs, hn]
  ring

private instance certificate_instance_0689 : OAI.SidorenkoCounterexample.ProofCertificate_0689 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15
  exact @certificate_proof_0689 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15

end PairSign
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
section RadicalCount
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K] in
theorem certificate_proof_0690 (U : Submodule K V) (C : SymForm K (V ⧸ U)) :
    (C.val.compl₁₂ U.mkQ U.mkQ).ker = U ↔ C.val.Nondegenerate := by
  constructor
  · intro h
    apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    apply bot_unique
    intro x hx
    obtain ⟨y, rfl⟩ := U.mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero U).mpr
    rw [← h]
    apply LinearMap.mem_ker.mpr
    ext z
    exact congrArg (fun f => f (U.mkQ z)) hx
  · intro h
    rw [pullback_ker C.val h U.mkQ U.mkQ_surjective, Submodule.ker_mkQ]

private instance certificate_instance_0690 : OAI.SidorenkoCounterexample.ProofCertificate_0690 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7
  exact @certificate_proof_0690 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7

theorem certificate_proof_0691 (U : Submodule K V)
    (C : SymForm K (V ⧸ U)) (hC : C.val.Nondegenerate) :
    discriminantSign (C.val.compl₁₂ U.mkQ U.mkQ)
      (pullback_isSymm C.val C.property U.mkQ) = discriminantSign C.val C.property := by
  rw [discriminantSign_pullback C.val C.property hC U.mkQ U.mkQ_surjective
    (Module.finBasis K (V ⧸ U)),
    discriminantSign_nondegenerate C.val C.property hC (Module.finBasis K (V ⧸ U))]

private instance certificate_instance_0691 : OAI.SidorenkoCounterexample.ProofCertificate_0691 := by
  constructor
  intro c0 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  exact @certificate_proof_0691 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10

theorem certificate_proof_0692 {r : ℕ} (hV : finrank K V = r)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    Nat.card {C : SymForm K V // C.val.Nondegenerate ∧ discriminantSign C.val C.property = ξ} =
      Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} := by
  rw [Nat.card_congr (nonsingularSignedMatrixEquiv (K := K) (V := V) ξ), hV]
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl _)
  intro M
  simp only [Equiv.refl_apply, and_iff_left_iff_imp]
  intro h
  apply mt quadraticChar_eq_zero_iff.mpr
  rw [h]
  rcases hξ with rfl | rfl <;> norm_num

private instance certificate_instance_0692 : OAI.SidorenkoCounterexample.ProofCertificate_0692 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0692 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

theorem certificate_proof_0693 (U : Submodule K V) {r : ℕ}
    (hU : finrank K (V ⧸ U) = r) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    Nat.card {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} =
      Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} := by
  rw [Nat.card_congr (signedRadicalFiberEquiv U ξ)]
  exact nonsingularSignedForm_card hU hξ

private instance certificate_instance_0693 : OAI.SidorenkoCounterexample.ProofCertificate_0693 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  exact @certificate_proof_0693 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12

end RadicalCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section RankCard
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]
theorem certificate_proof_0694 (k : ℕ) (_hk : k ≤ finrank K V)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    Nat.card {B : SymForm K V // finrank K B.val.ker = k ∧ discriminantSign B.val B.property = ξ} =
      Nat.card (DimSubspace K V k) *
        Nat.card {M : SymMatrix K (finrank K V - k) // quadraticChar K M.val.det = ξ} := by
  classical
  let : Finite V := Module.finite_of_finite K
  let : Fintype (DimSubspace K V k) := Fintype.ofFinite _
  rw [Nat.card_congr (signedNullityFiberEquiv k ξ), Nat.card_sigma]
  have hf (U : DimSubspace K V k) :
      Nat.card {B : SymForm K V // B.val.ker = U.val ∧ discriminantSign B.val B.property = ξ} =
        Nat.card {M : SymMatrix K (finrank K V - k) // quadraticChar K M.val.det = ξ} := by
    apply signedRadicalFiber_card U.val _ hξ
    have := U.val.finrank_quotient_add_finrank
    rw [U.property] at this
    omega
  simp only [hf, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_id]

private instance certificate_instance_0694 : OAI.SidorenkoCounterexample.ProofCertificate_0694 := by
  constructor
  intro q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  exact @certificate_proof_0694 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11

end RankCard
section LayerCard
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end LayerCard
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section Binary
variable {K : Type} [Field K] [Fintype K]
end Binary
section Norms
variable {K E : Type} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable [Fintype K]
end Norms
section Equivalences
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
variable [FiniteDimensional K E] [FiniteDimensional K F] [Fintype K] [DecidableEq K]
end Equivalences
section Classification
variable {K E F : Type} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
  [Fintype K] [DecidableEq K]
end Classification
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section LinearMean
variable {K U W : Type} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [Fintype U] [Fintype W]
end LinearMean
section Forms
variable {K V : Type} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
end Forms
end SidorenkoCounterexample
end
end OAI

theorem solution : OAI.SidorenkoCounterexample.ProofCertificate_0654 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0655 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0656 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0657 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0658 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0659 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0660 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0661 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0662 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0663 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0664 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0665 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0666 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0667 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0668 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0669 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0670 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0671 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0672 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0673 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0674 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0675 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0676 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0677 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0678 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0679 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0680 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0681 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0682 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0683 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0684 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0685 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0686 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0687 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0688 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0689 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0690 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0691 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0692 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0693 ∧
  OAI.SidorenkoCounterexample.ProofCertificate_0694 := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end

