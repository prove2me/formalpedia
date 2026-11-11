-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.upperRound_inverse_bounds_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:56.24726+00:00
-- url     : https://prove2.me/submissions/2122778a-4230-4b1b-aade-e48cbd4ccbfc

import Mathlib
import Definitions.Def_Q238K004

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_CutMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma bilinear_symm (M : Matrix V V ℝ) (hM : M.IsHermitian) (x y : V → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  have ht : Mᵀ=M := (isHermitian_iff_isSymm.mp hM).eq
  simpa only [ht] using dotProduct_transpose_mulVec M x y

omit [DecidableEq V] in
lemma quad_add_scaled (M : Matrix V V ℝ) (hM : M.IsHermitian) (x u : V → ℝ) (t : ℝ) :
    quad M (x+t • u)=quad M x+2*t*(u ⬝ᵥ (M *ᵥ x))+t^2*quad M u := by
  simp only [quad,mulVec_add,mulVec_smul,add_dotProduct,smul_dotProduct,
    dotProduct_add,dotProduct_smul,smul_eq_mul]
  rw [bilinear_symm M hM x u]
  ring

omit [DecidableEq V] in
lemma quad_nonneg (M : Matrix V V ℝ) (hM : M.PosSemidef) (x : V → ℝ) : 0≤quad M x := by
  simpa only [star_trivial,quad] using hM.dotProduct_mulVec_nonneg x

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_QuadSmulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V]

lemma quad_smul_matrix (M : Matrix V V ℝ) (x : V → ℝ) (t : ℝ) :
    quad (t • M) x=t*quad M x := by
  simp only [quad,smul_mulVec,dotProduct_smul,smul_eq_mul]

end

open Matrix
open scoped Matrix MatrixOrder

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SqNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma quad_one (x : V → ℝ) : quad (1 : Matrix V V ℝ) x=sqNorm x := by
  simp only [quad,one_mulVec,dotProduct,sqNorm,pow_two]

omit [DecidableEq V] in
lemma quad_sub_matrix (A B : Matrix V V ℝ) (x : V → ℝ) :
    quad (A-B) x=quad A x-quad B x := by simp [quad,sub_mulVec,dotProduct_sub]

omit [DecidableEq V] in
lemma quad_entry_perturb (A B : Matrix V V ℝ) (e : ℝ) (he : 0≤e)
    (hentry : ∀ i j, |A i j-B i j|≤e) (x : V → ℝ) :
    |quad A x-quad B x|≤(Fintype.card V:ℝ)*e*sqNorm x := by
  have hc : (∑ i, |x i|)^2≤(Fintype.card V:ℝ)*sqNorm x := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V) (fun _ => (1:ℝ))
      (fun i => |x i|)
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
      sq_abs,sqNorm] using hh
  rw [←quad_sub_matrix]
  change |∑ i, x i * ∑ j, (A i j-B i j)*x j| ≤ _
  calc
    _ ≤ ∑ i, |x i * ∑ j, (A i j-B i j)*x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x i| * |∑ j, (A i j-B i j)*x j| := by simp only [abs_mul]
    _ ≤ ∑ i, |x i| * (∑ j, e * |x j|) := by
      gcongr with i hi
      calc
        _ ≤ ∑ j, |(A i j-B i j)*x j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by apply Finset.sum_le_sum; intro j _; rw [abs_mul]; gcongr; exact hentry i j
    _ = e*(∑ i, |x i|)^2 := by rw [←Finset.mul_sum,←Finset.sum_mul]; ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc he]

omit [DecidableEq V] in
lemma posSemidef_of_quad (M : Matrix V V ℝ) (hM : M.IsHermitian)
    (h : ∀ x, 0≤quad M x) : M.PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  exact ⟨hM,by simpa only [star_trivial,quad] using h⟩

end

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma posDef_mul_inverse_vec (A : Matrix V V ℝ) (hA : A.PosDef) (x : V → ℝ) :
    A *ᵥ (A⁻¹ *ᵥ x)=x := by
  rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),one_mulVec]

lemma quad_inverse_vec (A : Matrix V V ℝ) (hA : A.PosDef) (x : V → ℝ) :
    quad A (A⁻¹ *ᵥ x)=quad A⁻¹ x := by
  unfold quad
  rw [posDef_mul_inverse_vec A hA x,dotProduct_comm]

lemma inverse_antitone (A B : Matrix V V ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hBA : (B-A).PosSemidef) : (A⁻¹-B⁻¹).PosSemidef := by
  apply posSemidef_of_quad _ (hA.inv.isHermitian.sub hB.inv.isHermitian)
  intro x
  have hh := quad_nonneg A hA.posSemidef ((A⁻¹ *ᵥ x)+(-1:ℝ) • (B⁻¹ *ᵥ x))
  rw [quad_add_scaled A hA.isHermitian,quad_inverse_vec A hA x] at hh
  rw [posDef_mul_inverse_vec A hA x,dotProduct_comm (B⁻¹ *ᵥ x) x] at hh
  change 0≤quad A⁻¹ x+2*(-1)*quad B⁻¹ x+(-1)^2*quad A (B⁻¹ *ᵥ x) at hh
  have hb := quad_nonneg _ hBA (B⁻¹ *ᵥ x)
  rw [quad_sub_matrix,quad_inverse_vec B hB x] at hb
  rw [quad_sub_matrix]
  nlinarith

lemma inv_smul_real (A : Matrix V V ℝ) (hA : A.PosDef) (t : ℝ) (ht : t≠0) :
    (t • A)⁻¹=t⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_smul_comm,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    mul_inv_cancel₀ ht,one_smul]

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CenterUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma upperRound_above (A Q : Matrix V V ℝ) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (e : ℝ) (he : 0≤e) (hentry : ∀ i j, |Q i j-A i j|≤e) :
    (upperRound Q e-A).PosSemidef := by
  apply posSemidef_of_quad _ ((hQ.add ((isHermitian_one).smul (IsSelfAdjoint.all _))).sub hA)
  intro x
  have hh := (abs_le.mp (quad_entry_perturb Q A e he hentry x)).1
  have hadd (B C : Matrix V V ℝ) : quad (B+C) x=quad B x+quad C x := by
    simp only [quad,add_mulVec,dotProduct_add]
  simp only [quad_sub_matrix,hadd,quad_smul_matrix,quad_one]
  linarith

lemma upperRound_relative (A Q : Matrix V V ℝ) (hA : A.IsHermitian) (hQ : Q.IsHermitian)
    (e m ε : ℝ) (he : 0≤e) (hε : 0≤ε)
    (hentry : ∀ i j, |Q i j-A i j|≤e)
    (hm : (A-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)*e≤ε*m) :
    ((1+ε) • A-upperRound Q e).PosSemidef := by
  apply posSemidef_of_quad _ ((hA.smul (IsSelfAdjoint.all _)).sub
    (hQ.add ((isHermitian_one).smul (IsSelfAdjoint.all _))))
  intro x
  have hq := (abs_le.mp (quad_entry_perturb Q A e he hentry x)).2
  have hb := quad_nonneg _ hm x
  have hs : 0≤ sqNorm x := Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [quad_sub_matrix,quad_smul_matrix,quad_one] at hb
  have hb' := mul_le_mul_of_nonneg_left (show m*sqNorm x≤quad A x by linarith) hε
  have hp := mul_le_mul_of_nonneg_right hprecision hs
  have hadd (B C : Matrix V V ℝ) : quad (B+C) x=quad B x+quad C x := by
    simp only [quad,add_mulVec,dotProduct_add]
  simp only [quad_sub_matrix,quad_smul_matrix,hadd,quad_one]
  nlinarith

lemma upperRound_pos (A Q : Matrix V V ℝ) (hA : A.PosDef) (hQ : Q.IsHermitian)
    (e : ℝ) (he : 0≤e) (hentry : ∀ i j, |Q i j-A i j|≤e) :
    (upperRound Q e).PosDef := by
  have hh := hA.add_posSemidef (upperRound_above A Q hA.isHermitian hQ e he hentry)
  have heq : A+(upperRound Q e-A)=upperRound Q e := by abel
  rwa [heq] at hh

lemma upperRound_inverse_bounds_s238_oai (A Q : Matrix V V ℝ) (hA : A.PosDef) (hQ : Q.IsHermitian)
    (e m ε : ℝ) (he : 0≤e) (hε : 0≤ε) (hε1 : ε<1)
    (hentry : ∀ i j, |Q i j-A i j|≤e)
    (hm : (A-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)*e≤ε*m) :
    (A⁻¹-(upperRound Q e)⁻¹).PosSemidef ∧
    ((upperRound Q e)⁻¹-(1-ε) • A⁻¹).PosSemidef := by
  have hR := upperRound_pos A Q hA hQ e he hentry
  have hrel := upperRound_relative A Q hA.isHermitian hQ e m ε he hε hentry hm hprecision
  have hl : 0<1-ε := by linarith
  have hinf : ((1/(1-ε)) • A-upperRound Q e).PosSemidef := by
    apply posSemidef_of_quad _ ((hA.isHermitian.smul (IsSelfAdjoint.all _)).sub hR.isHermitian)
    intro x
    have hh := quad_nonneg _ hrel x
    have hqm := quad_nonneg A hA.posSemidef x
    have hc : 1+ε≤1/(1-ε) := (le_div_iff₀ hl).mpr (by nlinarith [sq_nonneg ε])
    have hx := mul_le_mul_of_nonneg_right hc hqm
    rw [quad_sub_matrix,quad_smul_matrix] at hh ⊢
    linarith
  constructor
  · exact inverse_antitone A _ hA hR (upperRound_above A Q hA.isHermitian hQ e he hentry)
  · have hh := inverse_antitone _ _ hR (hA.smul (one_div_pos.mpr hl)) hinf
    rw [inv_smul_real _ hA _ (one_div_ne_zero hl.ne'),one_div,inv_inv] at hh
    exact hh

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.upperRound_inverse_bounds_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Ellipsoid.upperRound_inverse_bounds_s238_oai.{u_1}
