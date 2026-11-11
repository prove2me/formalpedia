-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:52.056207+00:00
-- url     : https://prove2.me/submissions/ed65bd57-3576-45b8-9036-a7f87f1b7659

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

omit [DecidableEq V] in
lemma quad_cutMatrix (d : ℝ) (M : Matrix V V ℝ) (u x : V → ℝ) :
    quad (cutMatrix d M u) x = (d^2-1)/d^2*quad M x+
      (2*(d+1)/d^2)*(x ⬝ᵥ (M *ᵥ u))^2 := by
  simp only [quad,cutMatrix,add_mulVec,smul_mulVec,dotProduct_add,
    dotProduct_smul,vecMulVec_mulVec,op_smul_eq_smul,smul_eq_mul]
  rw [dotProduct_comm (M *ᵥ u) x]
  ring

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

lemma quad_smul_vec (M : Matrix V V ℝ) (x : V → ℝ) (t : ℝ) :
    quad M (t • x)=t^2*quad M x := by
  simp only [quad,mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

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

omit [DecidableEq V] in
lemma quad_sub_matrix (A B : Matrix V V ℝ) (x : V → ℝ) :
    quad (A-B) x=quad A x-quad B x := by simp [quad,sub_mulVec,dotProduct_sub]

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RealVector
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

omit [DecidableEq V] in
lemma real_mulVec (H : Matrix V V ℚ) (x : V → ℚ) :
    realVector (H *ᵥ x)=realMatrix H *ᵥ realVector x := by
  ext i
  simp only [realVector,realMatrix,mulVec,dotProduct,Rat.cast_sum,Rat.cast_mul]

omit [DecidableEq V] in
lemma real_quad (H : Matrix V V ℚ) (x : V → ℚ) :
    (rationalQuad H x:ℝ)=quad (realMatrix H) (realVector x) := by
  simp only [rationalQuad,quad,realVector,realMatrix,mulVec,dotProduct,
    Rat.cast_sum,Rat.cast_mul]

omit [DecidableEq V] in
lemma real_cutShape (d : ℚ) (H : Matrix V V ℚ) (a : V → ℚ) :
    realMatrix (rationalCutShape d H a)=cutShape (d:ℝ) (realMatrix H) (realVector a) := by
  have hm := real_mulVec H a
  ext i j
  simp only [realMatrix,rationalCutShape,cutShape,Matrix.smul_apply,smul_eq_mul,
    Matrix.sub_apply,vecMulVec_apply,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_pow,
    Rat.cast_one,Rat.cast_ofNat,Rat.cast_add,real_quad]
  rw [←hm]
  rfl

end

open Matrix
open scoped Matrix

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

lemma inflation_pos (n : ℕ) (hn : 1≤n) : 0<1-1/(8*(n:ℝ)^2) := by
  have hp : (1:ℝ)≤n := by exact_mod_cast hn
  have hb : 1/(8*(n:ℝ)^2)<1 := (div_lt_one (by positivity)).mpr (by nlinarith)
  linarith

omit [DecidableEq V] in
lemma quad_cauchy_unit (M : Matrix V V ℝ) (hM : M.PosSemidef) (u x : V → ℝ)
    (hu : quad M u=1) : (x ⬝ᵥ (M *ᵥ u))^2≤quad M x := by
  let b := x ⬝ᵥ (M *ᵥ u)
  have hh := quad_nonneg M hM (x+(-b) • u)
  rw [quad_add_scaled M hM.isHermitian,hu,bilinear_symm M hM.isHermitian u x] at hh
  change 0≤quad M x+2*(-b)*b+(-b)^2*1 at hh
  change b^2≤quad M x
  nlinarith

omit [DecidableEq V] in
lemma cutMatrix_spectral (d : ℝ) (hd : 2≤d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) (hu : quad M u=1) :
    (cutMatrix d M u-(3/4:ℝ) • M).PosSemidef ∧
    ((3:ℝ) • M-cutMatrix d M u).PosSemidef := by
  have hd0 : 0<d := by linarith
  have hc := (cutMatrix_pos d (by linarith) M hM u).isHermitian
  have hhi : (3/4:ℝ)≤(d^2-1)/d^2 := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hlo : (d^2-1)/d^2+2*(d+1)/d^2≤3 := by
    rw [←add_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hb : 0≤2*(d+1)/d^2 := by positivity
  constructor
  · apply posSemidef_of_quad _ (hc.sub (hM.isHermitian.smul (IsSelfAdjoint.all _)))
    intro x
    have hq := quad_nonneg M hM.posSemidef x
    have hh := mul_le_mul_of_nonneg_right hhi hq
    have hp := mul_nonneg hb (sq_nonneg (x ⬝ᵥ (M *ᵥ u)))
    rw [quad_sub_matrix,quad_smul_matrix,quad_cutMatrix]
    nlinarith
  · apply posSemidef_of_quad _ ((hM.isHermitian.smul (IsSelfAdjoint.all _)).sub hc)
    intro x
    have hq := quad_nonneg M hM.posSemidef x
    have hh := mul_le_mul_of_nonneg_right hlo hq
    have hp := mul_le_mul_of_nonneg_left (quad_cauchy_unit M hM.posSemidef u x hu) hb
    rw [quad_sub_matrix,quad_smul_matrix,quad_cutMatrix]
    nlinarith

lemma inflation_bounds (d : ℝ) (hd : 1≤d) :
    (7/8:ℝ)≤1-1/(8*d^2) ∧ 1-1/(8*d^2)≤1 := by
  have he : 1/(8*d^2)≤1/8 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  constructor <;> linarith [show 0≤1/(8*d^2) by positivity]

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalInflatedShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma real_smul_matrix (r : ℚ) (A : Matrix V V ℚ) :
    realMatrix (r • A)=(r:ℝ) • realMatrix A := by
  ext i j
  simp only [realMatrix,Matrix.smul_apply,smul_eq_mul,Rat.cast_mul]

omit [DecidableEq V] in
lemma real_inflatedShape (H : Matrix V V ℚ) (a : V → ℚ) :
    realMatrix (rationalInflatedShape H a)=
      (1/(1-1/(8*(Fintype.card V:ℝ)^2))) • cutShape (Fintype.card V) (realMatrix H) (realVector a) := by
  simp only [rationalInflatedShape,real_smul_matrix,real_cutShape,Rat.cast_div,
    Rat.cast_sub,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_natCast]

omit [Fintype V] [DecidableEq V] in
lemma realVector_ne_zero (a : V → ℚ) (ha : a≠0) : realVector a≠0 := by
  intro he
  apply ha
  ext i
  apply Rat.cast_injective (α:=ℝ)
  simpa only [realVector,Pi.zero_apply,Rat.cast_zero] using congrFun he i

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FormTrans
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

omit [Fintype V] [DecidableEq V] in
lemma form_le_trans (A B C : Matrix V V ℝ) (hAB : (B-A).PosSemidef) (hBC : (C-B).PosSemidef) :
    (C-A).PosSemidef := by
  have hh := hAB.add hBC
  have he : B-A+(C-B)=C-A := by abel
  rwa [he] at hh

omit [Fintype V] [DecidableEq V] in
lemma form_scalar_mono (H : Matrix V V ℝ) (hH : H.PosSemidef) (r s : ℝ) (hrs : r ≤ s) :
    (s • H-r • H).PosSemidef := by
  simpa only [sub_smul] using hH.smul (sub_nonneg.mpr hrs)

lemma cutShape_lower (d : ℝ) (hd : 2≤d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a : V → ℝ) (ha : a≠0) : (cutShape d H a-(1/3:ℝ) • H).PosSemidef := by
  have hu := (dual_normal_properties H hH a ha).2.1
  have hc := cutMatrix_pos d (by linarith) H⁻¹ hH.inv (normalizedDual H a)
  have hs := (cutMatrix_spectral d hd H⁻¹ hH.inv (normalizedDual H a) hu).2
  have hh := inverse_antitone _ _ hc (hH.inv.smul (by norm_num : (0:ℝ)<3)) hs
  rw [inv_smul_real _ hH.inv _ (by norm_num : (3:ℝ)≠0),
    nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
    ←cutShape_inverse d (by linarith) H hH a ha] at hh
  simpa only [one_div] using hh

lemma inflatedShape_lower_s238_oai (H : Matrix V V ℚ) (a : V → ℚ) (hn : 2≤Fintype.card V)
    (hH : (realMatrix H).PosDef) (ha : a≠0) :
    (realMatrix (rationalInflatedShape H a)-(1/3:ℝ) • realMatrix H).PosSemidef := by
  have hn' : 2≤(Fintype.card V:ℝ) := by exact_mod_cast hn
  have hc := cutShape_pos_s238 _ (by linarith : 1<(Fintype.card V:ℝ)) _ hH _ (realVector_ne_zero a ha)
  have hl := inflation_bounds (Fintype.card V) (by linarith)
  have hl0 := inflation_pos (Fintype.card V) (by omega)
  have hrs : (1:ℝ)≤1/(1-1/(8*(Fintype.card V:ℝ)^2)) := (le_div_iff₀ hl0).mpr (by linarith [hl.2])
  have hh := form_scalar_mono _ hc.posSemidef 1 _ hrs
  rw [one_smul] at hh
  rw [real_inflatedShape]
  exact form_le_trans _ _ _ (cutShape_lower _ hn' _ hH _ (realVector_ne_zero a ha)) hh

end

open Matrix
open scoped Matrix

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower_s238_oai.{u_1}
