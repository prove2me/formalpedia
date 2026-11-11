-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.shape_center_contains_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:57.067076+00:00
-- url     : https://prove2.me/submissions/e2af3e53-a004-4e5f-89b4-137ccfa2c3ce

import Mathlib
import Definitions.Def_Q238K004

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_KindRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open scoped InnerProductSpace

lemma scalar_cut_bound (d s t : ℝ) (hd : 1<d) (hs : s≤1) (ht0 : t≤0) (ht1 : -1≤t) :
    (d^2-1)/d^2*(s+2*t/(d+1)+(1/(d+1))^2)+
      (2*(d+1)/d^2)*(t+1/(d+1))^2 ≤ 1 := by
  have hd0 : d≠0 := by linarith
  have hdp : d+1≠0 := by linarith
  have heq : (d^2-1)/d^2*(s+2*t/(d+1)+(1/(d+1))^2)+
      (2*(d+1)/d^2)*(t+1/(d+1))^2 =
        ((d^2-1)*s+2*(d+1)*(t^2+t)+1)/d^2 := by
    field_simp
    ring
  rw [heq]
  apply (div_le_one (sq_pos_of_ne_zero hd0)).mpr
  have htn : t^2+t≤0 := by
    have hh := mul_nonpos_of_nonpos_of_nonneg ht0 (show 0≤t+1 by linarith)
    nlinarith
  have hh1 := mul_nonneg (show 0≤d^2-1 by nlinarith) (sub_nonneg.mpr hs)
  have hh2 := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*(d+1) by linarith) htn
  nlinarith

end MetricKMedianRecovery.Ellipsoid

end OAI
end

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

omit [DecidableEq V] in

lemma matrix_cut_contains (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u x : V → ℝ) (hu : quad M u=1) (hx : quad M x≤1)
    (hcut : u ⬝ᵥ (M *ᵥ x)≤0) :
    quad (cutMatrix d M u) (x+(1/(d+1)) • u) ≤ 1 := by
  let t := u ⬝ᵥ (M *ᵥ x)
  have ht : -1≤t := by
    have hh := quad_nonneg M hM.posSemidef (x+(-t) • u)
    rw [quad_add_scaled M hM.isHermitian,hu] at hh
    change 0≤quad M x+2*(-t)*t+(-t)^2*1 at hh
    nlinarith
  have hh := scalar_cut_bound d (quad M x) t hd hx hcut ht
  rw [quad_cutMatrix,quad_add_scaled M hM.isHermitian,hu]
  have he : (x+(1/(d+1)) • u) ⬝ᵥ (M *ᵥ u) = t+1/(d+1) := by
    rw [add_dotProduct,smul_dotProduct,bilinear_symm M hM.isHermitian x u]
    change t+(1/(d+1))*quad M u=t+1/(d+1)
    rw [hu,mul_one]
  rw [he]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

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

lemma quad_perturb (M : Matrix V V ℝ) (hM : M.PosSemidef) (x e : V → ℝ)
    (δ : ℝ) (hδ : 0<δ) (hx : quad M x≤1) (he : quad M e≤δ^2) :
    quad M (x+e)≤(1+δ)^2 := by
  let b := x ⬝ᵥ (M *ᵥ e)
  have hh := quad_nonneg M hM (e+(-δ) • x)
  rw [quad_add_scaled M hM.isHermitian] at hh
  change 0≤quad M e+2*(-δ)*b+(-δ)^2*quad M x at hh
  have hqx := mul_le_mul_of_nonneg_left hx (sq_nonneg δ)
  have hb : b≤δ := by nlinarith
  have hform := quad_add_scaled M hM.isHermitian x e 1
  simp only [one_smul,one_pow,one_mul,mul_one] at hform
  rw [bilinear_symm M hM.isHermitian e x] at hform
  change quad M (x+e)=quad M x+2*b+quad M e at hform
  nlinarith

lemma quad_cut_unit (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (u : V → ℝ)
    (hu : quad M u=1) : quad (cutMatrix d M u) u=(d+1)^2/d^2 := by
  have hd0 : d≠0 := by linarith
  rw [quad_cutMatrix]
  change (d^2-1)/d^2*quad M u+(2*(d+1)/d^2)*(quad M u)^2=_
  rw [hu]
  field_simp
  ring

lemma center_inflation_scalar (d : ℝ) (hd : 1≤d) :
    (1-1/(8*d^2))*(1+1/(32*d^2))^2≤1 := by
  have hd0 : 0<d := by linarith
  have hz : 0<1/(32*d^2) := by positivity
  have he : 1/(8*d^2)=4*(1/(32*d^2)) := by ring
  rw [he]
  nlinarith [sq_nonneg (1/(32*d^2)),pow_nonneg hz.le 3]

lemma approximate_center_contains (d : ℝ) (hd : 1<d) (M : Matrix V V ℝ) (hM : M.PosDef)
    (u x : V → ℝ) (hu : quad M u=1) (hx : quad M x≤1)
    (hcut : u ⬝ᵥ (M *ᵥ x)≤0) (ρ : ℝ)
    (hρlo : 1-1/(32*d)≤ρ) (hρhi : ρ≤1) :
    quad ((1-1/(8*d^2)) • cutMatrix d M u) (x+(ρ/(d+1)) • u)≤1 := by
  have hd0 : 0<d := by linarith
  have hdp : d+1≠0 := by linarith
  let δ := 1/(32*d^2)
  have hδ : 0<δ := by dsimp [δ] <;> positivity
  have hlam : 0≤1-1/(8*d^2) := by
    have hh : 1/(8*d^2)≤1 := (div_le_one (by positivity)).mpr (by nlinarith)
    linarith
  let e := ((ρ-1)/(d+1)) • u
  have he : quad (cutMatrix d M u) e≤δ^2 := by
    rw [quad_smul_vec,quad_cut_unit d hd M u hu]
    have heq : ((ρ-1)/(d+1))^2*((d+1)^2/d^2)=((1-ρ)/d)^2 := by
      field_simp
      ring
    rw [heq]
    have hg : 0≤(1-ρ)/d := div_nonneg (by linarith) hd0.le
    have hk : (1-ρ)/d≤δ := by
      apply (div_le_iff₀ hd0).mpr
      have hi : δ*d=1/(32*d) := by dsimp [δ]; field_simp
      rw [hi]
      linarith
    nlinarith
  have hq := quad_perturb (cutMatrix d M u) (cutMatrix_pos d hd M hM u).posSemidef
    (x+(1/(d+1)) • u) e δ hδ (matrix_cut_contains d hd M hM u x hu hx hcut) he
  have hid : x+(ρ/(d+1)) • u=(x+(1/(d+1)) • u)+e := by
    dsimp [e]
    rw [add_assoc,←add_smul]
    congr 2
    ring
  rw [hid,quad_smul_matrix]
  exact (mul_le_mul_of_nonneg_left hq hlam).trans (center_inflation_scalar d hd.le)

end

open Matrix
open scoped Matrix MatrixOrder

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

lemma sqrt_ratio (d q t : ℝ) (hd : 1≤d) (hq : 0<q)
    (htlo : Real.sqrt q≤t) (hthi : t≤(1+1/(32*d))*Real.sqrt q) :
    1-1/(32*d)≤Real.sqrt q/t ∧ Real.sqrt q/t≤1 := by
  have hs : 0<Real.sqrt q := Real.sqrt_pos.2 hq
  have ht : 0<t := hs.trans_le htlo
  have hδ : 0≤1/(32*d) := by positivity
  have hδ1 : 1/(32*d)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  constructor
  · apply (le_div_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left hthi (show 0≤1-1/(32*d) by linarith)
    have he : (1-1/(32*d))*((1+1/(32*d))*Real.sqrt q) =
        (1-(1/(32*d))^2)*Real.sqrt q := by ring
    rw [he] at hh
    have hz := mul_nonneg (sq_nonneg (1/(32*d))) hs.le
    nlinarith
  · exact (div_le_one ht).mpr htlo

end

open Matrix
open scoped Matrix

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

lemma shape_center_contains_s238_oai (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a c x : V → ℝ) (ha : a≠0) (t : ℝ)
    (htlo : Real.sqrt (quad H a)≤t) (hthi : t≤(1+1/(32*d))*Real.sqrt (quad H a))
    (hx : quad H⁻¹ (x-c)≤1) (hcut : a ⬝ᵥ (x-c)≤0) :
    quad ((1-1/(8*d^2)) • cutMatrix d H⁻¹ (normalizedDual H a))
      (x-centerUpdate d H a c t)≤1 := by
  obtain ⟨hq,hu,hv⟩ := dual_normal_properties H hH a ha
  let u := normalizedDual H a
  have hs : 0<Real.sqrt (quad H a) := Real.sqrt_pos.mpr hq
  have ht : 0<t := hs.trans_le htlo
  have hr := sqrt_ratio d (quad H a) t hd.le hq htlo hthi
  have hc : u ⬝ᵥ (H⁻¹ *ᵥ (x-c))≤0 := by
    rw [bilinear_symm _ hH.inv.isHermitian]
    change (x-c) ⬝ᵥ (H⁻¹ *ᵥ normalizedDual H a)≤0
    rw [hv,dotProduct_smul,smul_eq_mul,dotProduct_comm]
    exact mul_nonpos_of_nonneg_of_nonpos (one_div_nonneg.mpr hs.le) hcut
  have hh := approximate_center_contains d hd H⁻¹ hH.inv u (x-c) hu hx hc
    (Real.sqrt (quad H a)/t) hr.1 hr.2
  have he : x-centerUpdate d H a c t=(x-c)+((Real.sqrt (quad H a)/t)/(d+1)) • u := by
    ext i
    simp only [centerUpdate,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,u,normalizedDual]
    field_simp
    ring
  rwa [he]

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.shape_center_contains_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Ellipsoid.shape_center_contains_s238_oai.{u_1}
