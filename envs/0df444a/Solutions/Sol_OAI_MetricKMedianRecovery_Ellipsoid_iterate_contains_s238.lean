-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:21:25.38696+00:00
-- url     : https://prove2.me/submissions/124fc723-9485-4eac-bba1-21d0b6c2fe5c

import Mathlib
import Definitions.Def_Q238K014
import Definitions.Def_Q238K015
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_cutShape_pos_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_inflatedShape_inverse_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_iterate_pos_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_rationalRootUpper_bounds_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_shape_center_contains_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_GridFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*}

lemma gridFloor_bounds (D : ℕ) (hD : 0<D) (q : ℚ) :
    q-1/(D:ℚ)≤gridFloor D q ∧ gridFloor D q≤q := by
  have hDp : 0<(D:ℚ) := by exact_mod_cast hD
  have hlo := Int.floor_le ((D:ℚ)*q)
  have hhi := Int.lt_floor_add_one ((D:ℚ)*q)
  constructor
  · apply (le_div_iff₀ hDp).mpr
    have he : (q-1/(D:ℚ))*(D:ℚ)=(D:ℚ)*q-1 := by field_simp
    rw [he]
    linarith
  · apply (div_le_iff₀ hDp).mpr
    simpa only [mul_comm] using hlo

lemma gridFloor_error (D : ℕ) (hD : 0<D) (q : ℚ) :
    |(gridFloor D q:ℝ)-(q:ℝ)|≤1/(D:ℝ) := by
  have hh := gridFloor_bounds D hD q
  have h : |gridFloor D q-q|≤1/(D:ℚ) := by
    apply abs_le.mpr
    constructor <;> linarith [show (0:ℚ)≤1/(D:ℚ) by positivity]
  have hr := (Rat.cast_le (K:=ℝ)).mpr h
  simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using hr

lemma realMatrix_symm (A : Matrix V V ℚ) (hA : A.IsSymm) : (realMatrix A).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  ext i j
  exact congrArg (fun q : ℚ => (q:ℝ)) (hA.apply i j)

lemma gridMatrix_symm (D : ℕ) (A : Matrix V V ℚ) (hA : A.IsSymm) :
    (gridMatrix D A).IsSymm := by
  ext i j
  exact congrArg (gridFloor D) (hA.apply i j)

lemma gridMatrix_error (D : ℕ) (hD : 0<D) (A : Matrix V V ℚ) :
    ∀ i j, |realMatrix (gridMatrix D A) i j-realMatrix A i j|≤1/(D:ℝ) := by
  intro i j
  exact gridFloor_error D hD (A i j)

end

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

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_NormalizedDual
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

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
lemma quad_le_of_sub (A B : Matrix V V ℝ) (h : (B-A).PosSemidef) (x : V → ℝ) :
    quad A x≤quad B x := by
  have hh := quad_nonneg _ h x
  rw [quad_sub_matrix] at hh
  linarith

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

lemma upperRound_pos (A Q : Matrix V V ℝ) (hA : A.PosDef) (hQ : Q.IsHermitian)
    (e : ℝ) (he : 0≤e) (hentry : ∀ i j, |Q i j-A i j|≤e) :
    (upperRound Q e).PosDef := by
  have hh := hA.add_posSemidef (upperRound_above A Q hA.isHermitian hQ e he hentry)
  have heq : A+(upperRound Q e-A)=upperRound Q e := by abel
  rwa [heq] at hh

lemma real_gridShape (D : ℕ) (A : Matrix V V ℚ) :
    realMatrix (gridShape D A)=upperRound (realMatrix (gridMatrix D A)) (1/(D:ℝ)) := by
  ext i j
  simp only [gridShape,realMatrix,upperRound,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast]
  congr 1
  rw [div_eq_mul_inv,one_div]
  congr 1
  by_cases h : i=j <;> simp [Matrix.one_apply,h]

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
lemma rational_symm_of_real (A : Matrix V V ℚ) (hA : (realMatrix A).IsHermitian) : A.IsSymm := by
  have hh := (isHermitian_iff_isSymm.mp hA)
  ext i j
  exact Rat.cast_injective (hh.apply i j : (A j i:ℝ)=(A i j:ℝ))

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

omit [DecidableEq V] in
lemma real_stepCenter (H : Matrix V V ℚ) (a c : V → ℚ) :
    realVector (rationalStepCenter H a c)=centerUpdate (Fintype.card V) (realMatrix H)
      (realVector a) (realVector c) (rationalRootUpper (32*Fintype.card V) (rationalQuad H a)) := by
  have hh := real_mulVec H a
  ext i
  simp only [rationalStepCenter,realVector,centerUpdate,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast]
  congr 2
  exact congrArg (fun v : V → ℝ => v i) hh

omit [Fintype V] [DecidableEq V] in
lemma realVector_ne_zero (a : V → ℚ) (ha : a≠0) : realVector a≠0 := by
  intro he
  apply ha
  ext i
  apply Rat.cast_injective (α:=ℝ)
  simpa only [realVector,Pi.zero_apply,Rat.cast_zero] using congrFun he i

lemma rational_step_contains (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a c : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0)
    (x : V → ℝ) (hx : quad (realMatrix H)⁻¹ (x-realVector c)≤1)
    (hcut : realVector a ⬝ᵥ (x-realVector c)≤0) :
    quad (realMatrix (rationalStepShape D H a))⁻¹
      (x-realVector (rationalStepCenter H a c))≤1 := by
  have hn' : 1<(Fintype.card V:ℝ) := by exact_mod_cast (show 1<Fintype.card V by omega)
  have hq : 0<(rationalQuad H a:ℝ) := by
    rw [real_quad]
    exact (dual_normal_properties _ hH _ (realVector_ne_zero a ha)).1
  have hr := rationalRootUpper_bounds_s238 (32*Fintype.card V) (by omega) (rationalQuad H a)
    ((Rat.cast_pos (K:=ℝ)).mp hq)
  have hrr : (32*Fintype.card V:ℕ)=(32:ℝ)*(Fintype.card V:ℝ) := by push_cast; rfl
  rw [hrr,real_quad] at hr
  have hc := shape_center_contains_s238 _ hn' _ hH _ (realVector c) x (realVector_ne_zero a ha)
    _ hr.1 hr.2 hx hcut
  have hA : (realMatrix (rationalInflatedShape H a)).PosDef := by
    rw [real_inflatedShape]
    exact (cutShape_pos_s238 _ hn' _ hH _ (realVector_ne_zero a ha)).smul
      (one_div_pos.mpr (inflation_pos _ (by omega)))
  have hsym := realMatrix_symm _ (gridMatrix_symm D _ (rational_symm_of_real _ hA.isHermitian))
  have herr := gridMatrix_error D hD (rationalInflatedShape H a)
  have hR := upperRound_pos _ _ hA hsym _ (by positivity) herr
  have ho := inverse_antitone _ _ hA hR (upperRound_above _ _ hA.isHermitian hsym _ (by positivity) herr)
  rw [←real_gridShape] at ho
  have hh := quad_le_of_sub _ _ ho (x-realVector (rationalStepCenter H a c))
  rw [real_inflatedShape,inflatedShape_inverse_s238 _ hn' _ hH _ (realVector_ne_zero a ha),real_stepCenter] at hh
  simpa only [rationalStepShape,real_stepCenter] using hh.trans hc

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.state_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma badRow_some {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) (r : Row n)
    (hr : badRow rows c=some r) : r∈rows ∧ r.bound < r.value c := by
  have hb := List.find?_some (p:=fun q : Row n => decide (q.bound<q.value c)) hr
  exact ⟨List.mem_of_find?_eq_some hr,of_decide_eq_true hb⟩

lemma badRow_nonzero {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) (r : Row n)
    (hr : badRow rows c=some r) (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x) :
    r.coeff≠0 := by
  intro he
  obtain ⟨hmem,hbad⟩ := badRow_some rows c r hr
  have hh := hx r hmem
  simp only [Row.RealHolds,Row.realValue,he,Pi.zero_apply,Rat.cast_zero,zero_mul,
    Finset.sum_const_zero] at hh
  have hhq : (0:ℚ) ≤ r.bound := (Rat.cast_nonneg (K:=ℝ)).mp hh
  simp only [Row.value,he,Pi.zero_apply,zero_mul,Finset.sum_const_zero] at hbad
  exact (not_lt_of_ge hhq) hbad

lemma advance_contains {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (x : Fin n → ℝ)
    (hx : ∀ q∈rows, q.RealHolds x)
    (hball : quad (realMatrix S.shape)⁻¹ (x-realVector S.center)≤1) :
    quad (realMatrix (advance D rows S).shape)⁻¹ (x-realVector (advance D rows S).center)≤1 := by
  unfold advance
  split
  · exact hball
  next r hr =>
    have ha := badRow_nonzero rows S.center r hr x hx
    rw [ite_eq_right ha]
    apply rational_step_contains D hD S.shape r.coeff S.center (by simpa using hn) hS ha x hball
    obtain ⟨hmem,hbad⟩ := badRow_some rows S.center r hr
    have hh := hx r hmem
    have hh' : (r.bound:ℝ)<(r.value S.center:ℝ) := Rat.cast_lt.mpr hbad
    have he : realVector r.coeff ⬝ᵥ (x-realVector S.center)=r.realValue x-(r.value S.center:ℝ) := by
      simp only [realVector,dotProduct,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,
        Row.realValue,Row.value,Rat.cast_sum,Rat.cast_mul]
    rw [he]
    exact sub_nonpos.mpr (hh.trans hh'.le)

lemma iterate_contains_s238_oai {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (x : Fin n → ℝ)
    (hx : ∀ q∈rows, q.RealHolds x)
    (hball : quad (realMatrix S.shape)⁻¹ (x-realVector S.center)≤1) (t : ℕ) :
    quad (realMatrix (iterate D rows S t).shape)⁻¹ (x-realVector (iterate D rows S t).center)≤1 := by
  induction t with
  | zero => exact hball
  | succ t ih => exact advance_contains D hD rows _ hn (iterate_pos_s238 D hD rows S hn hS t) x hx ih

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238_oai := @OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238_oai
