-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.Ellipsoid.robust_spectral_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:53.982932+00:00
-- url     : https://prove2.me/submissions/7065719e-3861-476b-961b-abd8fb37b7f2

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

omit [DecidableEq V] in
lemma quad_le_of_sub (A B : Matrix V V ℝ) (h : (B-A).PosSemidef) (x : V → ℝ) :
    quad A x≤quad B x := by
  have hh := quad_nonneg _ h x
  rw [quad_sub_matrix] at hh
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

omit [DecidableEq V] in

lemma robust_spectral_s238_oai (d : ℝ) (hd : 2≤d) (M R : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) (hu : quad M u=1)
    (hRlo : (R-(1-1/(8*d^2)) • ((1-1/(8*d^2)) • cutMatrix d M u)).PosSemidef)
    (hRhi : ((1-1/(8*d^2)) • cutMatrix d M u-R).PosSemidef) :
    (R-(1/2:ℝ) • M).PosSemidef ∧ ((3:ℝ) • M-R).PosSemidef := by
  let lam : ℝ := 1-1/(8*d^2)
  have hlb := inflation_bounds d (by linarith)
  have hl0 : 0≤lam := by dsimp [lam] <;> linarith
  have hl1 : lam≤1 := hlb.2
  have hll : (7/8:ℝ)≤lam := hlb.1
  have hcpos := cutMatrix_pos d (by linarith) M hM u
  have hRherm : R.IsHermitian := by
    have hh := hRlo.isHermitian.add ((hcpos.isHermitian.smul (IsSelfAdjoint.all (1-1/(8*d^2)))).smul (IsSelfAdjoint.all (1-1/(8*d^2))))
    simpa only [sub_add_cancel] using hh
  obtain ⟨hc1,hc2⟩ := cutMatrix_spectral d hd M hM u hu
  constructor
  · apply posSemidef_of_quad _ (hRherm.sub (hM.isHermitian.smul (IsSelfAdjoint.all _)))
    intro x
    have hh := quad_le_of_sub _ _ hRlo x
    have hcut := quad_le_of_sub _ _ hc1 x
    have hqm := quad_nonneg M hM.posSemidef x
    simp only [quad_smul_matrix] at hh hcut
    have hl2 : (1/2:ℝ)≤lam^2*(3/4) := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hcut (sq_nonneg lam)
    have h2 := mul_le_mul_of_nonneg_right hl2 hqm
    rw [quad_sub_matrix,quad_smul_matrix]
    change lam* (lam*quad (cutMatrix d M u) x) ≤quad R x at hh
    nlinarith
  · apply posSemidef_of_quad _ ((hM.isHermitian.smul (IsSelfAdjoint.all _)).sub hRherm)
    intro x
    have hh := quad_le_of_sub _ _ hRhi x
    have hcut := quad_le_of_sub _ _ hc2 x
    have hqc := quad_nonneg _ hcpos.posSemidef x
    simp only [quad_smul_matrix] at hh hcut
    have h1 := mul_le_mul_of_nonneg_right hl1 hqc
    rw [quad_sub_matrix,quad_smul_matrix]
    change quad R x≤lam*quad (cutMatrix d M u) x at hh
    linarith

end MetricKMedianRecovery.Ellipsoid

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.Ellipsoid.robust_spectral_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.Ellipsoid.robust_spectral_s238_oai.{u_1}
