-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:59.561882+00:00
-- url     : https://prove2.me/submissions/5606a4ba-fd3d-4763-b489-b01f3fafe59b

import Mathlib
import Definitions.Def_Q238K004
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_cutShape_pos_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_inflatedShape_lower_s238

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

lemma stepShape_lower (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0) :
    (realMatrix (rationalStepShape D H a)-(1/3:ℝ) • realMatrix H).PosSemidef := by
  have hn' : 1<(Fintype.card V:ℝ) := by exact_mod_cast (show 1<Fintype.card V by omega)
  have hp : (realMatrix (rationalInflatedShape H a)).PosDef := by
    rw [real_inflatedShape]
    exact (cutShape_pos_s238 _ hn' _ hH _ (realVector_ne_zero a ha)).smul
      (one_div_pos.mpr (inflation_pos _ (by omega)))
  have hsym := realMatrix_symm _ (gridMatrix_symm D _ (rational_symm_of_real _ hp.isHermitian))
  have hh := upperRound_above _ _ hp.isHermitian hsym _ (by positivity)
    (gridMatrix_error D hD (rationalInflatedShape H a))
  rw [←real_gridShape] at hh
  exact form_le_trans _ _ _ (inflatedShape_lower_s238 H a hn hH ha) hh

lemma stepShape_pos_s238_oai (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0) :
    (realMatrix (rationalStepShape D H a)).PosDef := by
  have hh := (hH.smul (by norm_num : (0:ℝ)<1/3)).add_posSemidef
    (stepShape_lower D hD H a hn hH ha)
  have he : (1/3:ℝ) • realMatrix H+(realMatrix (rationalStepShape D H a)-(1/3:ℝ) • realMatrix H)=realMatrix (rationalStepShape D H a) := by abel
  rwa [he] at hh

end

open Matrix
open scoped Matrix

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_s238_oai.{u_1}
