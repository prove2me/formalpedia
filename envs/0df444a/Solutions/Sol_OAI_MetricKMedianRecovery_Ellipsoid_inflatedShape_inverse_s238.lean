-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_inverse_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:50.872304+00:00
-- url     : https://prove2.me/submissions/a989a768-efc0-47aa-9008-220971b6e60b

import Mathlib
import Definitions.Def_Q238K004
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_cutShape_pos_s238

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
lemma cutMatrix_pos (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) : (cutMatrix d M u).PosDef := by
  have hα : 0<(d^2-1)/d^2 := div_pos (by nlinarith) (by positivity)
  have hβ : 0≤2*(d+1)/d^2 := by positivity
  have hh : (vecMulVec (M *ᵥ u) (M *ᵥ u)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (M *ᵥ u)
  exact (hM.smul hα).add_posSemidef (hh.smul hβ)

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

lemma quad_smul_vec (M : Matrix V V ℝ) (x : V → ℝ) (t : ℝ) :
    quad M (t • x)=t^2*quad M x := by
  simp only [quad,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

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

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma inv_smul_real (A : Matrix V V ℝ) (hA : A.PosDef) (t : ℝ) (ht : t≠0) :
    (t • A)⁻¹=t⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [smul_mul_smul_comm,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    mul_inv_cancel₀ ht,one_smul]

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_NormalizedDual
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
lemma hermitian_vecMul (H : Matrix V V ℝ) (hH : H.IsHermitian) (a : V → ℝ) :
    a ᵥ* H=H *ᵥ a := by
  have ht : Hᵀ=H := (isHermitian_iff_isSymm.mp hH).eq
  simpa only [ht] using (vecMul_transpose H a)

lemma rank_one_shape_inverse (H : Matrix V V ℝ) (hH : H.PosDef) (a : V → ℝ)
    (c : ℝ) (hc : 1+c*quad H a≠0) :
    (H⁻¹+c • vecMulVec a a)⁻¹=
      H-(c/(1+c*quad H a)) • vecMulVec (H *ᵥ a) (H *ᵥ a) := by
  apply Matrix.inv_eq_right_inv
  have hv : H⁻¹ *ᵥ (H *ᵥ a)=a := by
    rw [mulVec_mulVec,nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),one_mulVec]
  rw [mul_sub,add_mul,add_mul,nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
    smul_mul_assoc,mul_smul_comm,mul_smul_comm,smul_mul_assoc,
    mul_vecMulVec,hv,vecMulVec_mul,hermitian_vecMul H hH.isHermitian a,
    vecMulVec_mul_vecMulVec,vecMulVec_smul,smul_smul]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply]
  unfold quad at hc ⊢
  field_simp
  ring

lemma dual_normal_properties (H : Matrix V V ℝ) (hH : H.PosDef) (a : V → ℝ) (ha : a≠0) :
    0<quad H a ∧ quad H⁻¹ (normalizedDual H a)=1 ∧
    H⁻¹ *ᵥ normalizedDual H a=(1/Real.sqrt (quad H a)) • a := by
  have hq : 0<quad H a := by
    simpa only [quad,star_trivial] using hH.dotProduct_mulVec_pos ha
  have hs : Real.sqrt (quad H a)≠0 := (Real.sqrt_pos.2 hq).ne'
  have hv : H⁻¹ *ᵥ (H *ᵥ a)=a := by
    rw [mulVec_mulVec,nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),one_mulVec]
  refine ⟨hq,?_,?_⟩
  · rw [normalizedDual,quad_smul_vec]
    have he : quad H⁻¹ (H *ᵥ a)=quad H a := by
      unfold quad
      rw [hv,dotProduct_comm]
    rw [he,div_pow,one_pow,Real.sq_sqrt hq.le]
    field_simp
  · simp only [normalizedDual,mulVec_smul,hv]

lemma cutShape_inverse (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a : V → ℝ) (ha : a≠0) :
    cutShape d H a=(cutMatrix d H⁻¹ (normalizedDual H a))⁻¹ := by
  obtain ⟨hq,hu,hv⟩ := dual_normal_properties H hH a ha
  have hd0 : d≠0 := by linarith
  have hdm : d-1≠0 := by linarith
  have hdp : d+1≠0 := by linarith
  have hds : d^2-1≠0 := by nlinarith
  have hs : Real.sqrt (quad H a)≠0 := (Real.sqrt_pos.2 hq).ne'
  have he : cutMatrix d H⁻¹ (normalizedDual H a)=
      ((d^2-1)/d^2) • (H⁻¹+(2/((d-1)*quad H a)) • vecMulVec a a) := by
    unfold cutMatrix
    rw [hv,smul_vecMulVec,vecMulVec_smul,smul_smul,smul_smul,smul_add,smul_smul]
    congr 1
    congr 1
    have hs2 := Real.sq_sqrt hq.le
    field_simp
    nlinarith
  have hc : 1+2/((d-1)*quad H a)*quad H a≠0 := by
    have hh : 1+2/((d-1)*quad H a)*quad H a=(d+1)/(d-1) := by field_simp <;> ring
    rw [hh]
    exact div_ne_zero hdp hdm
  have hinner : (H⁻¹+(2/((d-1)*quad H a)) • vecMulVec a a).PosDef := by
    have hp := cutMatrix_pos d hd H⁻¹ hH.inv (normalizedDual H a)
    rw [he] at hp
    have hscale : (0:ℝ)<d^2/(d^2-1) := div_pos (by positivity) (by nlinarith)
    have hh := hp.smul hscale
    have hid : d^2/(d^2-1)*((d^2-1)/d^2)=(1:ℝ) := by field_simp
    simpa only [smul_smul,hid,one_smul] using hh
  rw [he,inv_smul_real _ hinner _ (div_ne_zero hds (pow_ne_zero _ hd0)),
    rank_one_shape_inverse H hH a _ hc]
  have hcoeff : 2/((d+1)*quad H a) =
      (2/((d-1)*quad H a))/(1+2/((d-1)*quad H a)*quad H a) := by
    apply (eq_div_iff hc).mpr
    field_simp
    ring
  simp only [cutShape,inv_div,hcoeff]

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InflationPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma inflation_bounds (d : ℝ) (hd : 1≤d) :
    (7/8:ℝ)≤1-1/(8*d^2) ∧ 1-1/(8*d^2)≤1 := by
  have he : 1/(8*d^2)≤1/8 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  constructor <;> linarith [show 0≤1/(8*d^2) by positivity]

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

lemma inflatedShape_inverse_s238_oai (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a : V → ℝ) (ha : a≠0) :
    ((1/(1-1/(8*d^2))) • cutShape d H a)⁻¹ =
      (1-1/(8*d^2)) • cutMatrix d H⁻¹ (normalizedDual H a) := by
  have hl : 0<1-1/(8*d^2) := by
    have hh := inflation_bounds d hd.le
    linarith
  rw [inv_smul_real _ (cutShape_pos_s238 d hd H hH a ha) _ (one_div_ne_zero hl.ne'),
    one_div,inv_inv,cutShape_inverse d hd H hH a ha,
    nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr
      (cutMatrix_pos d hd H⁻¹ hH.inv (normalizedDual H a)).det_pos.ne')]

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_inverse_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_inverse_s238_oai.{u_1}
