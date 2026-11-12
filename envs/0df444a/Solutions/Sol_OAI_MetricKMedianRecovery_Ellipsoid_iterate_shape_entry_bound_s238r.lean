-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:28:50.479396+00:00
-- url     : https://prove2.me/submissions/d5c1658e-6df3-4ede-8267-df0bfdcb25cb

import Mathlib
import Definitions.Def_Q238L009
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_advance_pos_lower_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_inflatedShape_inverse_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_inflatedShape_lower_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_iterate_pos_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_robust_spectral_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_stepShape_pos_bounds_s238r

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
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma quad_single (M : Matrix V V ℝ) (i : V) : quad M (Pi.single i 1)=M i i := by
  simp [quad]

lemma entry_bound_of_diagonal (M : Matrix V V ℝ) (hM : M.PosSemidef) (K : ℝ)
    (hdiag : ∀ i, M i i≤K) : ∀ i j, |M i j|≤K := by
  intro i j
  have he : (Pi.single j 1) ⬝ᵥ (M *ᵥ (Pi.single i 1))=M i j := by
    simp only [single_one_dotProduct,mulVec_single_one]
    exact (isHermitian_iff_isSymm.mp hM.isHermitian).apply _ _
  have hp := quad_nonneg M hM ((Pi.single i 1)+(1:ℝ) • (Pi.single j 1))
  have hm := quad_nonneg M hM ((Pi.single i 1)+(-1:ℝ) • (Pi.single j 1))
  rw [quad_add_scaled M hM.isHermitian,quad_single,quad_single,he] at hp hm
  exact abs_le.mpr ⟨by linarith [hdiag i,hdiag j],by linarith [hdiag i,hdiag j]⟩

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
lemma form_le_smul (A B : Matrix V V ℝ) (h : (B-A).PosSemidef) (r : ℝ) (hr : 0 ≤ r) :
    (r • B-r • A).PosSemidef := by
  simpa only [smul_sub] using h.smul hr

omit [Fintype V] [DecidableEq V] in
lemma form_scalar_mono (H : Matrix V V ℝ) (hH : H.PosSemidef) (r s : ℝ) (hrs : r ≤ s) :
    (s • H-r • H).PosSemidef := by
  simpa only [sub_smul] using hH.smul (sub_nonneg.mpr hrs)

lemma stepShape_upper (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0) (m : ℝ)
    (hm : (realMatrix (rationalInflatedShape H a)-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)/(D:ℝ)≤(1/(8*(Fintype.card V:ℝ)^2))*m) :
    ((2:ℝ) • realMatrix H-realMatrix (rationalStepShape D H a)).PosSemidef := by
  have hn' : 2≤(Fintype.card V:ℝ) := by exact_mod_cast hn
  obtain ⟨hp,hhi,hlo⟩ := stepShape_pos_bounds_s238r D hD H a hn hH ha m hm hprecision
  rw [real_inflatedShape,inflatedShape_inverse_s238r _ (by linarith) _ hH _ (realVector_ne_zero a ha)] at hhi hlo
  have hs := (robust_spectral_s238r _ hn' _ _ hH.inv _
    (dual_normal_properties _ hH _ (realVector_ne_zero a ha)).2.1 hlo hhi).1
  have hh := inverse_antitone _ _ (hH.inv.smul (by norm_num : (0:ℝ)<1/2)) hp.inv hs
  rw [inv_smul_real _ hH.inv _ (by norm_num : (1/2:ℝ)≠0),
    nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),
    nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')] at hh
  norm_num at hh ⊢
  exact hh

end

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma gridDenominator_pos (n T : ℕ) (hn : 0<n) : 0<gridDenominator n T := by
  unfold gridDenominator
  positivity

lemma gridDenominator_precision (n T : ℕ) (hn : 0<n) :
    2*(n:ℝ)/(gridDenominator n T:ℝ)=1/(8*(n:ℝ)^2)*(1/3:ℝ)^(T+1) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  simp only [gridDenominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,_root_.one_div_pow]
  field_simp
  ring

omit [Fintype V] in
lemma iterate_lower (H : ℕ → Matrix V V ℝ) (h0 : (H 0-1).PosSemidef)
    (hh : ∀ t, (H (t+1)-(1/3:ℝ) • H t).PosSemidef) :
    ∀ t, (H t-(1/3:ℝ)^t • (1:Matrix V V ℝ)).PosSemidef := by
  intro t
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    have hs := form_le_smul _ _ ih (1/3) (by norm_num)
    rw [smul_smul,←pow_succ'] at hs
    exact form_le_trans _ _ _ hs (hh t)

lemma inflatedShape_precision (H : Matrix V V ℚ) (a : V → ℚ) (hn : 2≤Fintype.card V)
    (hH : (realMatrix H).PosDef) (ha : a≠0) (t T : ℕ) (ht : t≤T)
    (hlo : (realMatrix H-(1/3:ℝ)^t • (1:Matrix V V ℝ)).PosSemidef) :
    (realMatrix (rationalInflatedShape H a)-(1/3:ℝ)^(T+1) • (1:Matrix V V ℝ)).PosSemidef := by
  have hs := form_le_smul _ _ hlo (1/3) (by norm_num)
  rw [smul_smul,←pow_succ'] at hs
  have ht' : (1/3:ℝ)^(T+1)≤(1/3:ℝ)^(t+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hm := form_scalar_mono (1:Matrix V V ℝ) Matrix.PosSemidef.one _ _ ht'
  exact form_le_trans _ _ _ hm (form_le_trans _ _ _ hs (inflatedShape_lower_s238r H a hn hH ha))

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma iterate_shape_lower {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (h0 : (realMatrix S.shape-1).PosSemidef) (t : ℕ) :
    (realMatrix (iterate D rows S t).shape-(1/3:ℝ)^t • (1:Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  apply iterate_lower (fun t => realMatrix (iterate D rows S t).shape) h0 _ t
  intro k
  exact (advance_pos_lower_s238r D hD rows _ hn (iterate_pos_s238r D hD rows S hn hS k)).2

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma realMatrix_one {V : Type*} [DecidableEq V] :
    realMatrix (1:Matrix V V ℚ)=(1:Matrix V V ℝ) := by
  ext i j
  by_cases h : i=j <;> simp [realMatrix,Matrix.one_apply,h]

lemma initial_realShape (n : ℕ) (R : ℚ) :
    realMatrix (initialState n R).shape=(R:ℝ)^2 • (1:Matrix (Fin n) (Fin n) ℝ) := by
  simp only [initialState,real_smul_matrix,realMatrix_one,Rat.cast_pow]

lemma initial_pos (n : ℕ) (R : ℚ) (hR : 0<R) :
    (realMatrix (initialState n R).shape).PosDef := by
  rw [initial_realShape]
  exact Matrix.PosDef.one.smul (sq_pos_of_pos (Rat.cast_pos.mpr hR))

lemma initial_shape_lower (n : ℕ) (R : ℚ) (hR : 1≤R) :
    (realMatrix (initialState n R).shape-1).PosSemidef := by
  rw [initial_realShape]
  have hRr : (1:ℝ)≤(R:ℝ) := by exact_mod_cast hR
  simpa only [one_smul] using form_scalar_mono (1:Matrix (Fin n) (Fin n) ℝ)
    Matrix.PosSemidef.one 1 ((R:ℝ)^2) (by nlinarith)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Grid
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.state_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma advance_upper {n : ℕ} (T t : ℕ) (ht : t≤T) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef)
    (hlo : (realMatrix S.shape-(1/3:ℝ)^t • (1:Matrix (Fin n) (Fin n) ℝ)).PosSemidef) :
    ((2:ℝ) • realMatrix S.shape-realMatrix (advance (gridDenominator n T) rows S).shape).PosSemidef := by
  unfold advance
  split
  · simpa only [one_smul] using form_scalar_mono _ hS.posSemidef 1 2 (by norm_num)
  · split_ifs with ha
    · simpa only [one_smul] using form_scalar_mono _ hS.posSemidef 1 2 (by norm_num)
    · apply stepShape_upper _ (gridDenominator_pos n T (by omega)) _ _ (by simpa using hn) hS ha
        ((1/3:ℝ)^(T+1))
        (inflatedShape_precision _ _ (by simpa using hn) hS ha t T ht hlo)
      simpa only [Fintype.card_fin] using (gridDenominator_precision n T (by omega)).le

lemma iterate_shape_upper {n : ℕ} (T : ℕ) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (h0 : (realMatrix S.shape-1).PosSemidef)
    (t : ℕ) (ht : t≤T) :
    ((2:ℝ)^t • realMatrix S.shape-realMatrix (iterate (gridDenominator n T) rows S t).shape).PosSemidef := by
  induction t with
  | zero => simp only [iterate,pow_zero,one_smul,sub_self]; exact PosSemidef.zero
  | succ t ih =>
    have hi := ih (by omega)
    have hp := iterate_pos_s238r _ (gridDenominator_pos n T (by omega)) rows S hn hS t
    have hl := iterate_shape_lower _ (gridDenominator_pos n T (by omega)) rows S hn hS h0 t
    have ha := advance_upper T t (by omega) rows _ hn hp hl
    have hs := form_le_smul _ _ hi 2 (by norm_num)
    rw [smul_smul,←pow_succ'] at hs
    exact form_le_trans _ _ _ ha hs

lemma iterate_shape_entry_bound_s238r_oai (n T R : ℕ) (rows : List (Row n)) (hn : 2≤n) (hR : 1≤R)
    (t : ℕ) (ht : t≤T) (i j : Fin n) :
    |(iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j|≤(2:ℚ)^t*(R:ℚ)^2 := by
  have hRq : (1:ℚ)≤R := by exact_mod_cast hR
  have hp := iterate_pos_s238r _ (gridDenominator_pos n T (by omega)) rows _ hn
    (initial_pos n R (by positivity)) t
  have hb := iterate_shape_upper T rows _ hn (initial_pos n R (by positivity))
    (initial_shape_lower n R hRq) t ht
  rw [initial_realShape,smul_smul] at hb
  have hd (k : Fin n) : realMatrix (iterate (gridDenominator n T) rows (Ellipsoid.initialState n R) t).shape k k
      ≤(2:ℝ)^t*(R:ℝ)^2 := by
    have hh := hb.diag_nonneg (i:=k)
    simpa only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
      Rat.cast_natCast,sub_nonneg] using hh
  have hh := entry_bound_of_diagonal _ hp.posSemidef _ hd i j
  change |((iterate (gridDenominator n T) rows (Ellipsoid.initialState n R) t).shape i j:ℝ)|≤_ at hh
  exact_mod_cast hh

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238r_oai := @OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238r_oai
