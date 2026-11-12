-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:29:51.410582+00:00
-- url     : https://prove2.me/submissions/4ea5f6d4-6454-474e-bf4d-ad6539bee6c1

import Mathlib
import Definitions.Def_Q238L020
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_advance_pos_lower_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_inflatedShape_inverse_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_inflatedShape_lower_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_iterate_contains_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_iterate_pos_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_robust_cut_det_s238r
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

lemma det_bound_of_diameters (M : Matrix V V ℝ) (hM : M.PosDef)
    (z : V → ℝ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ i, quad M (z+r • Pi.single i 1)≤1 ∧
      quad M (z+(-r) • Pi.single i 1)≤1) :
    M.det ≤ (Fintype.card V).factorial * (1/r^2)^(Fintype.card V) := by
  have hdiag (i : V) : M i i≤1/r^2 := by
    have hh := hball i
    rw [quad_add_scaled M hM.isHermitian,quad_single] at hh
    rw [quad_add_scaled M hM.isHermitian,quad_single] at hh
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith [quad_nonneg M hM.posSemidef z]
  have he := entry_bound_of_diagonal M hM.posSemidef (1/r^2) hdiag
  have hd := Matrix.det_le (abv:=AbsoluteValue.abs) he
  simpa only [AbsoluteValue.abs_apply,abs_of_pos hM.det_pos,nsmul_eq_mul] using hd

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

lemma robust_block_growth (n : ℕ) (hn : 1≤n) : (2:ℝ)≤(1+1/(2*(n:ℝ)))^(2*n) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have hq : (0:ℝ)≤1/(2*(n:ℝ)) := by positivity
  have hh := one_add_mul_le_pow (le_trans (show (-2:ℝ)≤0 by norm_num) hq) (2*n)
  have he : (2*n:ℕ)*(1/(2*(n:ℝ)))=1 := by push_cast; field_simp
  simpa only [he,one_add_one_eq_two] using hh

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

lemma rational_step_growth (D : ℕ) (hD : 0<D) (H : Matrix V V ℚ) (a : V → ℚ)
    (hn : 2≤Fintype.card V) (hH : (realMatrix H).PosDef) (ha : a≠0) (m : ℝ)
    (hm : (realMatrix (rationalInflatedShape H a)-m • (1:Matrix V V ℝ)).PosSemidef)
    (hprecision : 2*(Fintype.card V:ℝ)/(D:ℝ)≤(1/(8*(Fintype.card V:ℝ)^2))*m) :
    (1+1/(2*(Fintype.card V:ℝ)))*(realMatrix H)⁻¹.det≤
      (realMatrix (rationalStepShape D H a))⁻¹.det := by
  have hn' : 1<(Fintype.card V:ℝ) := by exact_mod_cast (show 1<Fintype.card V by omega)
  have hh := (stepShape_pos_bounds_s238r D hD H a hn hH ha m hm hprecision).2.2
  rw [real_inflatedShape,inflatedShape_inverse_s238r _ hn' _ hH _ (realVector_ne_zero a ha)] at hh
  exact robust_cut_det_s238r _ _ hH.inv _ (dual_normal_properties _ hH _ (realVector_ne_zero a ha)).2.1 hn hh

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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.state_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma badRow_none {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) :
    badRow rows c=none ↔ ∀ r∈rows, r.Holds c := by
  simp only [badRow,List.find?_eq_none,decide_eq_true_eq,not_lt,Row.Holds]

lemma badRow_some {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) (r : Row n)
    (hr : badRow rows c=some r) : r∈rows ∧ r.bound < r.value c := by
  have hb := List.find?_some (p:=fun q : Row n => decide (q.bound<q.value c)) hr
  exact ⟨List.mem_of_find?_eq_some hr,of_decide_eq_true hb⟩

lemma advance_eq_self {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n)
    (h : ∀ r∈rows, r.Holds S.center) : advance D rows S=S := by
  simp only [advance,(badRow_none rows S.center).mpr h]

lemma iterate_stable {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n)
    (t k : ℕ) (ht : ∀ r∈rows, r.Holds (iterate D rows S t).center) :
    iterate D rows S (t+k)=iterate D rows S t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,iterate,ih,advance_eq_self D rows _ ht]

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_IterationBlocks
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

lemma growth_up_to (f : ℕ → ℝ) (g : ℝ) (hg : 0≤g) (T : ℕ)
    (hf : ∀ t<T, g*f t≤f (t+1)) : g^T*f 0≤f T := by
  have h (k : ℕ) (hk : k≤T) : g^k*f 0≤f k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ = g*(g^k*f 0) := by rw [pow_succ]; ring
        _ ≤ g*f k := mul_le_mul_of_nonneg_left (ih (by omega)) hg
        _ ≤ _ := hf k (by omega)
  exact h T le_rfl

lemma iterate_invalid_before {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n)
    (T t : ℕ) (ht : t≤T)
    (hT : ¬∀ r∈rows, r.Holds (iterate D rows S T).center) :
    ¬∀ r∈rows, r.Holds (iterate D rows S t).center := by
  intro hh
  have he := iterate_stable D rows S t (T-t) hh
  rw [Nat.add_sub_of_le ht] at he
  exact hT (he.symm ▸ hh)

lemma iterate_determinant_growth {n : ℕ} (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (h0 : (realMatrix S.shape-1).PosSemidef)
    (T : ℕ) (hT : ¬∀ r∈rows, r.Holds (iterate (gridDenominator n T) rows S T).center)
    (x : Fin n → ℝ) (hx : ∀ r∈rows, r.RealHolds x) :
    (1+1/(2*(n:ℝ)))^T*(realMatrix S.shape)⁻¹.det≤
      (realMatrix (iterate (gridDenominator n T) rows S T).shape)⁻¹.det := by
  let D := gridDenominator n T
  have hD := gridDenominator_pos n T (by omega)
  have hg : 0≤1+1/(2*(n:ℝ)) := by positivity
  apply growth_up_to (fun t => (realMatrix (iterate D rows S t).shape)⁻¹.det) _ hg T
  intro t ht
  let St := iterate D rows S t
  have hbad : ¬∀ r∈rows, r.Holds St.center := iterate_invalid_before D rows S T t ht.le hT
  have hrow : ∃ r, badRow rows St.center=some r := by
    cases he : badRow rows St.center with
    | none => exact (hbad ((badRow_none rows St.center).mp he)).elim
    | some r => exact ⟨r,rfl⟩
  obtain ⟨r,hr⟩ := hrow
  have ha := badRow_nonzero rows St.center r hr x hx
  have hp := iterate_pos_s238r D hD rows S hn hS t
  have hlo := iterate_shape_lower D hD rows S hn hS h0 t
  have hpre := inflatedShape_precision St.shape r.coeff (by simpa using hn) hp ha t T ht.le hlo
  have hpr : 2*(Fintype.card (Fin n):ℝ)/(D:ℝ)≤
      (1/(8*(Fintype.card (Fin n):ℝ)^2))*(1/3:ℝ)^(T+1) := by
    simpa only [Fintype.card_fin,D] using (gridDenominator_precision n T (by omega)).le
  have hh := rational_step_growth D hD St.shape r.coeff (by simpa using hn) hp ha
    ((1/3:ℝ)^(T+1)) hpre hpr
  change (1+1/(2*(n:ℝ)))*(realMatrix St.shape)⁻¹.det≤
    (realMatrix (advance D rows St).shape)⁻¹.det
  simpa only [advance,hr,ite_eq_right ha,Fintype.card_fin] using hh

lemma iterate_block_growth {n : ℕ} (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (h0 : (realMatrix S.shape-1).PosSemidef)
    (L : ℕ) (hT : ¬∀ r∈rows, r.Holds (iterate (gridDenominator n (2*n*L)) rows S (2*n*L)).center)
    (x : Fin n → ℝ) (hx : ∀ r∈rows, r.RealHolds x) :
    (2:ℝ)^L*(realMatrix S.shape)⁻¹.det≤
      (realMatrix (iterate (gridDenominator n (2*n*L)) rows S (2*n*L)).shape)⁻¹.det := by
  have hh := iterate_determinant_growth rows S hn hS h0 (2*n*L) hT x hx
  have hb := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (robust_block_growth n (by omega)) L
  rw [←pow_mul] at hb
  exact (mul_le_mul_of_nonneg_right hb hS.inv.det_pos.le).trans hh

lemma factorial_bit_bound (n : ℕ) : (n.factorial:ℝ)≤(2:ℝ)^(n*n) := by
  have h : n.factorial≤2^(n*n) := by
    calc
      _ ≤ n^n := Nat.factorial_le_pow n
      _ ≤ (2^n)^n := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = _ := by rw [pow_mul]
  exact_mod_cast h

lemma determinant_budget (n p s : ℕ) (R r : ℝ) (hR : 0<R) (hr : 0 < r)
    (hRp : R≤(2:ℝ)^s) (hrp : 1/r≤(2:ℝ)^p) :
    (n.factorial:ℝ)*(1/r^2)^n < (2:ℝ)^(iterationBlocks n p s)*(1/R^2)^n := by
  have hratio : R/r≤(2:ℝ)^(p+s) := by
    calc
      _ = (1/r)*R := by ring
      _ ≤ (2:ℝ)^p*2^s := mul_le_mul hrp hRp hR.le (by positivity)
      _ = _ := (pow_add _ _ _).symm
  have hp := pow_le_pow_left₀ (div_nonneg hR.le hr.le) hratio (2*n)
  have hall := mul_le_mul (factorial_bit_bound n) hp (by positivity) (by positivity)
  have he : (2:ℝ)^(n*n)*((2:ℝ)^(p+s))^(2*n)=(2:ℝ)^(n*n+2*n*(p+s)) := by
    rw [←pow_mul,←pow_add]
    congr 1
    ring
  rw [he] at hall
  have hlt : (2:ℝ)^(n*n+2*n*(p+s))<(2:ℝ)^(iterationBlocks n p s) := by
    apply pow_lt_pow_right₀ (by norm_num)
    exact Nat.lt_succ_self _
  have hbound := hall.trans_lt hlt
  have heq : (n.factorial:ℝ)*(1/r^2)^n=
      ((n.factorial:ℝ)*(R/r)^(2*n))*(1/R^2)^n := by
    simp only [pow_mul,div_pow,one_pow]
    field_simp
  rw [heq]
  exact mul_lt_mul_of_pos_right hbound (by positivity)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialState
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

lemma initial_inverse (n : ℕ) (R : ℚ) (hR : 0<R) :
    (realMatrix (initialState n R).shape)⁻¹=
      (1/(R:ℝ)^2) • (1:Matrix (Fin n) (Fin n) ℝ) := by
  rw [initial_realShape,inv_smul_real _ Matrix.PosDef.one _
    (pow_ne_zero _ (Rat.cast_ne_zero.mpr hR.ne')),inv_one,one_div]

lemma initial_inverse_det (n : ℕ) (R : ℚ) (hR : 0<R) :
    (realMatrix (initialState n R).shape)⁻¹.det=(1/(R:ℝ)^2)^n := by
  rw [initial_inverse n R hR,Matrix.det_smul,Matrix.det_one,mul_one,Fintype.card_fin]

lemma weakSolve_complete_diameters_s238r_oai {n : ℕ} (rows : List (Row n)) (hn : 2≤n)
    (R : ℚ) (hR : 1≤R) (p s : ℕ) (r : ℝ) (hr : 0 < r)
    (hRp : (R:ℝ)≤(2:ℝ)^s) (hrp : 1/r≤(2:ℝ)^p)
    (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x)
    (hdiam : ∀ i, (∀ q∈rows, q.RealHolds (x+r • Pi.single i 1)) ∧
      (∀ q∈rows, q.RealHolds (x+(-r) • Pi.single i 1)))
    (hinit : ∀ i, quad (realMatrix (initialState n R).shape)⁻¹
      (x+r • Pi.single i 1-realVector (initialState n R).center)≤1 ∧
      quad (realMatrix (initialState n R).shape)⁻¹
      (x+(-r) • Pi.single i 1-realVector (initialState n R).center)≤1) :
    ∃ c, weakSolve rows R p s=some c := by
  let T := iterationBudget n p s
  let D := gridDenominator n T
  let S := initialState n R
  have hRq : 0<R := lt_of_lt_of_le (by norm_num) hR
  have hRr : 0<(R:ℝ) := Rat.cast_pos.mpr hRq
  have hS := initial_pos n R hRq
  have h0 := initial_shape_lower n R hR
  have hD := gridDenominator_pos n T (by omega)
  have hvalid : ∀ q∈rows, q.Holds (iterate D rows S T).center := by
    by_contra hbad
    have hdet := iterate_block_growth rows S hn hS h0 (iterationBlocks n p s) hbad x hx
    have hM := (iterate_pos_s238r D hD rows S hn hS T).inv
    have hd := det_bound_of_diameters _ hM
      (x-realVector (iterate D rows S T).center) r hr (fun i => ?_)
    · have hb := determinant_budget n p s (R:ℝ) r hRr hr hRp hrp
      rw [initial_inverse_det n R hRq] at hdet
      simp only [Fintype.card_fin] at hd
      exact (not_lt_of_ge (hdet.trans hd)) hb
    · have hp := iterate_contains_s238r D hD rows S hn hS (x+r • Pi.single i 1) (hdiam i).1 (hinit i).1 T
      have hm := iterate_contains_s238r D hD rows S hn hS (x+(-r) • Pi.single i 1) (hdiam i).2 (hinit i).2 T
      have he (v : Fin n → ℝ) : x+v-realVector (iterate D rows S T).center=
          (x-realVector (iterate D rows S T).center)+v := by abel
      simpa only [he] using And.intro hp hm
  refine ⟨(iterate D rows S T).center,?_⟩
  exact ite_eq_left ((badRow_none _ _).mpr hvalid)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238r_oai := @OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238r_oai
