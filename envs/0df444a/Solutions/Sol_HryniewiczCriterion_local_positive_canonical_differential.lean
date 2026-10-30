-- Prove2me | solution 1 for HryniewiczCriterion.local_positive_canonical_differential
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T17:48:05.161004+00:00
-- url     : https://prove2.me/submissions/eec0317e-a9e9-4e94-8216-dbf60ffecb44

import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Definitions.Def_BirkhoffGlobalSection_MovingFrameAlgebra
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic

-- Generic Hamiltonian/frame matrix calculations adapted with credit to Mazecto,
-- accepted homogeneous_frame_flow_split and submission 893234ef-5ec2-4f4b-b415-f79ec1030002.
-- The C2 local completion and projected-flow assembly are derived for this contribution.

set_option Elab.async false

namespace BirkhoffGlobalSection.ContinuousHomogenization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Projection to the tangent hyperplane along the radial direction. -/
noncomputable def tangentProjection (ell : E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (ell x)⁻¹ • ell.smulRight x

lemma tangentProjection_apply (ell : E →L[ℝ] ℝ) (x v : E) :
    tangentProjection ell x v = v - (ell v / ell x) • x := by
  simp [tangentProjection, div_eq_inv_mul, mul_smul]

lemma projection_tangent (ell : E →L[ℝ] ℝ) (x : E) (hr : ell x ≠ 0) (v : E) :
    ell (tangentProjection ell x v) = 0 := by
  rw [tangentProjection_apply, map_sub, map_smul]
  simp [smul_eq_mul, hr]

lemma projection_radial (ell : E →L[ℝ] ℝ) (x : E) (hr : ell x ≠ 0) :
    tangentProjection ell x x = 0 := by
  rw [tangentProjection_apply]
  simp [hr]

lemma projection_eq_self (ell : E →L[ℝ] ℝ) (x v : E) (hv : ell v = 0) :
    tangentProjection ell x v = v := by
  rw [tangentProjection_apply, hv]
  simp

/-- The canonical positive bilinear form associated to a positive tangent
Hessian and a positively transverse radial direction. -/
noncomputable def radialHomogenization (B : (E →L[ℝ] E →L[ℝ] ℝ))
    (ell : E →L[ℝ] ℝ) (x : E) : (E →L[ℝ] E →L[ℝ] ℝ) :=
  B.bilinearComp (tangentProjection ell x) (tangentProjection ell x) +
    (ell x)⁻¹ • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp ell ell

lemma radialHomogenization_apply (B : (E →L[ℝ] E →L[ℝ] ℝ))
    (ell : E →L[ℝ] ℝ) (x v w : E) :
    radialHomogenization B ell x v w =
      B (tangentProjection ell x v) (tangentProjection ell x w) + ell v * ell w / ell x := by
  simp [radialHomogenization, ContinuousLinearMap.bilinearComp_apply, div_eq_inv_mul, mul_assoc, mul_left_comm]

lemma radial_identity (B : (E →L[ℝ] E →L[ℝ] ℝ))
    (ell : E →L[ℝ] ℝ) (x : E) (hr : ell x ≠ 0) (w : E) :
    radialHomogenization B ell x x w = ell w := by
  rw [radialHomogenization_apply, projection_radial ell x hr]
  simp [hr]

lemma tangent_identity (B : (E →L[ℝ] E →L[ℝ] ℝ))
    (ell : E →L[ℝ] ℝ) (x v w : E) (hv : ell v = 0) :
    radialHomogenization B ell x v w = B v w - (B v x / ell x) * ell w := by
  rw [radialHomogenization_apply, projection_eq_self ell x v hv, tangentProjection_apply]
  simp only [map_sub, map_smul, smul_eq_mul, hv, zero_mul, zero_div, add_zero]
  simp only [div_eq_mul_inv]
  ac_rfl

lemma same_tangent_restriction (B : (E →L[ℝ] E →L[ℝ] ℝ))
    (ell : E →L[ℝ] ℝ) (x v w : E) (hv : ell v = 0) (hw : ell w = 0) :
    radialHomogenization B ell x v w = B v w := by
  rw [tangent_identity B ell x v w hv, hw]
  simp

lemma symmetric (B : (E →L[ℝ] E →L[ℝ] ℝ))
    (hB : ∀ v w, B v w = B w v) (ell : E →L[ℝ] ℝ) (x : E) :
    ∀ v w, radialHomogenization B ell x v w = radialHomogenization B ell x w v := by
  intro v w
  rw [radialHomogenization_apply, radialHomogenization_apply, hB]
  rw [mul_comm (ell v) (ell w)]

lemma positive (B : (E →L[ℝ] E →L[ℝ] ℝ))
    (ell : E →L[ℝ] ℝ) (x : E) (hr : 0 < ell x)
    (hB : ∀ v : E, ell v = 0 → v ≠ 0 → 0 < B v v) :
    ∀ v : E, v ≠ 0 → 0 < radialHomogenization B ell x v v := by
  intro v hv
  rw [radialHomogenization_apply]
  have hp := projection_tangent ell x hr.ne' v
  have hn : 0 ≤ ell v * ell v / ell x := div_nonneg (mul_self_nonneg _) hr.le
  by_cases hP : tangentProjection ell x v = 0
  · have he : ell v ≠ 0 := by
      intro he
      rw [projection_eq_self ell x v he] at hP
      exact hv hP
    have hq : 0 < ell v * ell v / ell x := div_pos (mul_self_pos.mpr he) hr
    simpa [hP] using hq
  · exact add_pos_of_pos_of_nonneg (hB _ hp hP) hn

/-- On tangent directions the two associated Hamiltonian linear systems differ
only by a multiple of the Hamiltonian vector. -/
lemma shear_identity (B : (E →L[ℝ] E →L[ℝ] ℝ)) (ell : E →L[ℝ] ℝ)
    (x v : E) (hv : ell v = 0) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : (E →L[ℝ] ℝ) →L[ℝ] F) :
    J (radialHomogenization B ell x v) = J (B v) - (B v x / ell x) • J ell := by
  have h : radialHomogenization B ell x v = B v - (B v x / ell x) • ell := by
    ext w
    simpa using tangent_identity B ell x v w hv
  rw [h, map_sub, map_smul]

lemma quotient_identity (B : (E →L[ℝ] E →L[ℝ] ℝ)) (ell : E →L[ℝ] ℝ)
    (x v : E) (hv : ell v = 0) {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (J : (E →L[ℝ] ℝ) →L[ℝ] F) (L : F →L[ℝ] G) (hL : L (J ell) = 0) :
    L (J (radialHomogenization B ell x v)) = L (J (B v)) := by
  rw [shear_identity B ell x v hv J, map_sub, map_smul, hL, smul_zero, sub_zero]

section Companion

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- The normalized Hamiltonian vector is a second solution of the canonical
positive linear system. Together with the radial solution it gives the
identity block in the return matrix. -/
lemma rescaled_companion (B : ℝ → (N →L[ℝ] N →L[ℝ] ℝ))
    (ell : ℝ → N →L[ℝ] ℝ) (x X : ℝ → N)
    (J : (N →L[ℝ] ℝ) →L[ℝ] N) (t : ℝ)
    (hr : ell t (x t) ≠ 0) (horth : ell t (X t) = 0) (hXpoint : X t = J (ell t))
    (hX : HasDerivAt X (J (B t (X t))) t)
    (hrd : HasDerivAt (fun s => ell s (x s)) (B t (X t) (x t)) t) :
    HasDerivAt (fun s => (ell s (x s))⁻¹ • X s)
      (J (radialHomogenization (B t) (ell t) (x t)
        ((ell t (x t))⁻¹ • X t))) t := by
  have hd := (hrd.inv hr).smul hX
  convert hd using 1
  · rfl
  · rw [map_smul, map_smul, shear_identity (B t) (ell t) (x t) (X t) horth J,
      ← hXpoint, smul_sub, smul_smul]
    have hc : (ell t (x t))⁻¹ * (B t (X t) (x t) / ell t (x t)) =
        B t (X t) (x t) / (ell t (x t)) ^ 2 := by
      simp [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm]
    rw [hc]
    simp only [neg_div, neg_smul, sub_eq_add_neg]
    rfl

lemma radial_solution (B : ℝ → (N →L[ℝ] N →L[ℝ] ℝ))
    (ell : ℝ → N →L[ℝ] ℝ) (x : ℝ → N)
    (J : (N →L[ℝ] ℝ) →L[ℝ] N) (t : ℝ)
    (hr : ell t (x t) ≠ 0) (hx : HasDerivAt x (J (ell t)) t) :
    HasDerivAt x (J (radialHomogenization (B t) (ell t) (x t) (x t))) t := by
  have he : radialHomogenization (B t) (ell t) (x t) (x t) = ell t := by
    ext w
    exact radial_identity (B t) (ell t) (x t) hr w
  rwa [he]

/-- Removing the Hamiltonian shear from an original tangent variation gives
an actual solution of the canonical positive system. -/
lemma projected_variation (B : ℝ → (N →L[ℝ] N →L[ℝ] ℝ))
    (ell : ℝ → N →L[ℝ] ℝ) (x X v : ℝ → N) (n : ℝ → ℝ)
    (J : (N →L[ℝ] ℝ) →L[ℝ] N) (t : ℝ)
    (hr : ell t (x t) ≠ 0) (horthX : ell t (X t) = 0)
    (horthv : ell t (v t) = 0) (hXpoint : X t = J (ell t))
    (hX : HasDerivAt X (J (B t (X t))) t)
    (hv : HasDerivAt v (J (B t (v t))) t)
    (hrd : HasDerivAt (fun s => ell s (x s)) (B t (X t) (x t)) t)
    (hnd : HasDerivAt n (B t (v t) (x t)) t) :
    HasDerivAt (fun s => v s - (n s / ell s (x s)) • X s)
      (J (radialHomogenization (B t) (ell t) (x t)
        (v t - (n t / ell t (x t)) • X t))) t := by
  have hb := hnd.div hrd hr
  have hq := hv.sub (hb.smul hX)
  have horth : ell t (v t - (n t / ell t (x t)) • X t) = 0 := by
    simp [map_sub, map_smul, horthv, horthX]
  convert hq using 1
  · rfl
  · rw [shear_identity (B t) (ell t) (x t) _ horth J, ← hXpoint]
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have he : (B t (v t - (n t / ell t (x t)) • X t) (x t) / ell t (x t)) =
        (B t (v t) (x t) * ell t (x t) - n t * B t (X t) (x t)) /
          (ell t (x t)) ^ 2 := by
      simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      field_simp
      <;> ring
    simp only [map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at he
    rw [he]
    simp only [Pi.div_apply, sub_add_eq_sub_sub]


end Companion

end BirkhoffGlobalSection.ContinuousHomogenization

namespace HryniewiczCriterion.LocalC2
open HryniewiczCriterion
open scoped ContDiff
lemma clm_apply_eq_sum (L : R4 →L[ℝ] ℝ) (v : R4) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) +
      v 2 * L (Pi.single 2 1) + v 3 * L (Pi.single 3 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, Fin.sum_univ_four, smul_eq_mul]

/-- The linear map `L ↦ J ∇L`: `jvec L = (-L e₁, L e₀, -L e₃, L e₂)`. -/
noncomputable def jvec : (R4 →L[ℝ] ℝ) →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ![-(ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 0 1 : R4),
      -(ContinuousLinearMap.apply ℝ ℝ (Pi.single 3 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 2 1 : R4)] i

lemma jvec_apply (L : R4 →L[ℝ] ℝ) :
    jvec L = ![-L (Pi.single 1 1), L (Pi.single 0 1), -L (Pi.single 3 1), L (Pi.single 2 1)] := by
  ext i; fin_cases i <;> simp [jvec]

lemma hamiltonianVectorField_eq (H : R4 → ℝ) :
    hamiltonianVectorField H = fun y => jvec (fderiv ℝ H y) := by
  funext y; rw [jvec_apply]; rfl

lemma omega0_jvec_left (L : R4 →L[ℝ] ℝ) (q : R4) : omega0 (jvec L) q = -L q := by
  rw [clm_apply_eq_sum L q, jvec_apply]; simp [omega0]; ring

lemma omega0_jvec_right (L : R4 →L[ℝ] ℝ) (p : R4) : omega0 p (jvec L) = L p := by
  rw [clm_apply_eq_sum L p, jvec_apply]; simp [omega0] <;> ring

lemma apply_jvec_add (L M : R4 →L[ℝ] ℝ) : L (jvec M) + M (jvec L) = 0 := by
  rw [clm_apply_eq_sum L, clm_apply_eq_sum M, jvec_apply, jvec_apply]; simp; ring

lemma apply_jvec_self (L : R4 →L[ℝ] ℝ) : L (jvec L) = 0 := by
  have := apply_jvec_add L L; linarith


lemma hasFDerivAt_hvf_local (H : R4 → ℝ) (y : R4) (hH : ContDiffAt ℝ 2 H y) :
    HasFDerivAt (hamiltonianVectorField H)
      (jvec.comp (fderiv ℝ (fderiv ℝ H) y)) y := by
  rw [hamiltonianVectorField_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ H) y :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact jvec.hasFDerivAt.comp y hd.hasFDerivAt

lemma fderiv_hvf_local (H : R4 → ℝ) (y : R4) (hH : ContDiffAt ℝ 2 H y) :
    fderiv ℝ (hamiltonianVectorField H) y = jvec.comp (fderiv ℝ (fderiv ℝ H) y) :=
  (hasFDerivAt_hvf_local H y hH).fderiv

lemma D2_symm_local (H : R4 → ℝ) (y : R4) (hH : ContDiffAt ℝ 2 H y) (v w : R4) :
    fderiv ℝ (fderiv ℝ H) y v w = fderiv ℝ (fderiv ℝ H) y w v :=
  hH.isSymmSndFDerivAt (by norm_num) v w

lemma omega0_derivative {v w : ℝ → R4} {a b : R4} {t : ℝ}
    (hv : HasDerivAt v a t) (hw : HasDerivAt w b t) :
    HasDerivAt (fun s => omega0 (v s) (w s)) (omega0 a (w t) + omega0 (v t) b) t := by
  have h := fun i => hasDerivAt_pi.1 hv i
  have k := fun i => hasDerivAt_pi.1 hw i
  have key := ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
    ((h 3).mul (k 2))
  have key2 := key.congr_of_eventuallyEq (f₁ := fun s => omega0 (v s) (w s))
    (Filter.Eventually.of_forall fun _ => rfl)
  exact key2.congr_deriv (by simp only [omega0]; ring)

lemma symplectic_pairing_constant
    (B : ℝ → (R4 →L[ℝ] R4 →L[ℝ] ℝ))
    (hB : ∀ t v w, B t v w = B t w v)
    (v w : ℝ → R4)
    (hv : ∀ t, HasDerivAt v (jvec (B t (v t))) t)
    (hw : ∀ t, HasDerivAt w (jvec (B t (w t))) t) (t : ℝ) :
    omega0 (v t) (w t) = omega0 (v 0) (w 0) := by
  have hd : ∀ s, HasDerivAt (fun u => omega0 (v u) (w u)) 0 s := by
    intro s
    have h := omega0_derivative (hv s) (hw s)
    convert h using 1
    rw [omega0_jvec_left, omega0_jvec_right, hB s]
    ring
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0

lemma linearizedFlow_hasDerivAt_local (H : R4 → ℝ) (x : ℝ → R4)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) (v : R4) (t : ℝ) :
    HasDerivAt (fun s => Y s v) (jvec (fderiv ℝ (fderiv ℝ H) (x t) (Y t v))) t := by
  have h := (hY.2 t).clm_apply (hasDerivAt_const t v)
  simpa [fderiv_hvf_local H (x t) (hH t)] using h

lemma omega0_linearizedFlow_local (H : R4 → ℝ) (x : ℝ → R4)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) (v w : R4) (t : ℝ) :
    omega0 (Y t v) (Y t w) = omega0 v w := by
  have h := symplectic_pairing_constant (fun s => fderiv ℝ (fderiv ℝ H) (x s))
    (fun s => D2_symm_local H (x s) (hH s)) (fun s => Y s v) (fun s => Y s w)
    (linearizedFlow_hasDerivAt_local H x hH Y hY v)
    (linearizedFlow_hasDerivAt_local H x hH Y hY w) t
  simpa only [hY.1, ContinuousLinearMap.id_apply] using h

lemma dH_linearizedFlow_local (H : R4 → ℝ) (x : ℝ → R4)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField H (x t)) t)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) (v : R4) (t : ℝ) :
    fderiv ℝ H (x t) (Y t v) = fderiv ℝ H (x 0) v := by
  have hd : ∀ s, HasDerivAt (fun u => fderiv ℝ H (x u) (Y u v)) 0 s := by
    intro s
    have hdiff : DifferentiableAt ℝ (fderiv ℝ H) (x s) :=
      ((hH s).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hell := hdiff.hasFDerivAt.comp_hasDerivAt s (hx s)
    have h := hell.clm_apply (linearizedFlow_hasDerivAt_local H x hH Y hY v s)
    refine h.congr_deriv ?_
    rw [hamiltonianVectorField_eq, Function.comp_apply, D2_symm_local H (x s) (hH s), add_comm]
    exact apply_jvec_add _ _
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa only [hY.1, ContinuousLinearMap.id_apply] using hc

end HryniewiczCriterion.LocalC2

namespace HryniewiczCriterion.LocalC2
open HryniewiczCriterion BirkhoffGlobalSection.ContinuousHomogenization
open scoped ContDiff

noncomputable def completedHessian (H : R4 → ℝ) (y : R4) : R4 →L[ℝ] R4 →L[ℝ] ℝ :=
  radialHomogenization (fderiv ℝ (fderiv ℝ H) y) (fderiv ℝ H y) y

lemma radial_pair_derivative (H : R4 → ℝ) (x : ℝ → R4) (t : ℝ)
    (hH : ContDiffAt ℝ 2 H (x t))
    (hx : HasDerivAt x (hamiltonianVectorField H (x t)) t) :
    HasDerivAt (fun s => fderiv ℝ H (x s) (x s))
      (fderiv ℝ (fderiv ℝ H) (x t) (hamiltonianVectorField H (x t)) (x t)) t := by
  have hd : DifferentiableAt ℝ (fderiv ℝ H) (x t) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := (hd.hasFDerivAt.comp_hasDerivAt t hx).clm_apply hx
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, hamiltonianVectorField_eq, apply_jvec_self, add_zero]

lemma completed_radial_solution (H : R4 → ℝ) (x : ℝ → R4) (t : ℝ)
    (hr : fderiv ℝ H (x t) (x t) ≠ 0)
    (hx : HasDerivAt x (hamiltonianVectorField H (x t)) t) :
    HasDerivAt x (jvec (completedHessian H (x t) (x t))) t := by
  apply radial_solution (fun s => fderiv ℝ (fderiv ℝ H) (x s))
    (fun s => fderiv ℝ H (x s)) x jvec t hr
  simpa only [hamiltonianVectorField_eq] using hx

lemma completed_companion_solution (H : R4 → ℝ) (x : ℝ → R4) (t : ℝ)
    (hH : ContDiffAt ℝ 2 H (x t)) (hr : fderiv ℝ H (x t) (x t) ≠ 0)
    (hx : HasDerivAt x (hamiltonianVectorField H (x t)) t) :
    HasDerivAt (fun s => (fderiv ℝ H (x s) (x s))⁻¹ • hamiltonianVectorField H (x s))
      (jvec (completedHessian H (x t)
        ((fderiv ℝ H (x t) (x t))⁻¹ • hamiltonianVectorField H (x t)))) t := by
  apply rescaled_companion (fun s => fderiv ℝ (fderiv ℝ H) (x s))
    (fun s => fderiv ℝ H (x s)) x (fun s => hamiltonianVectorField H (x s)) jvec t hr
  · rw [hamiltonianVectorField_eq]; exact apply_jvec_self _
  · rw [hamiltonianVectorField_eq]
  · exact (hasFDerivAt_hvf_local H (x t) hH).comp_hasDerivAt t hx
  · exact radial_pair_derivative H x t hH hx

lemma completed_projected_solution (H : R4 → ℝ) (x : ℝ → R4)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField H (x t)) t)
    (hr : ∀ t, fderiv ℝ H (x t) (x t) ≠ 0)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y)
    (v : R4) (hv : fderiv ℝ H (x 0) v = 0) (t : ℝ) :
    HasDerivAt (fun s => Y s v -
        (omega0 (x s) (Y s v) / fderiv ℝ H (x s) (x s)) • hamiltonianVectorField H (x s))
      (jvec (completedHessian H (x t) (Y t v -
        (omega0 (x t) (Y t v) / fderiv ℝ H (x t) (x t)) • hamiltonianVectorField H (x t)))) t := by
  have horth : ∀ s, fderiv ℝ H (x s) (Y s v) = 0 := fun s => by
    rw [dH_linearizedFlow_local H x hH hx Y hY v s, hv]
  apply projected_variation (fun s => fderiv ℝ (fderiv ℝ H) (x s))
    (fun s => fderiv ℝ H (x s)) x (fun s => hamiltonianVectorField H (x s))
    (fun s => Y s v) (fun s => omega0 (x s) (Y s v)) jvec t (hr t)
  · rw [hamiltonianVectorField_eq]; exact apply_jvec_self _
  · exact horth t
  · rw [hamiltonianVectorField_eq]
  · exact (hasFDerivAt_hvf_local H (x t) (hH t)).comp_hasDerivAt t (hx t)
  · exact linearizedFlow_hasDerivAt_local H x hH Y hY v t
  · exact radial_pair_derivative H x t (hH t) (hx t)
  · have hd := omega0_derivative (hx t) (linearizedFlow_hasDerivAt_local H x hH Y hY v t)
    refine hd.congr_deriv ?_
    rw [hamiltonianVectorField_eq, omega0_jvec_left, omega0_jvec_right, horth t]
    ring

lemma completedHessian_positive (H : R4 → ℝ) (y : R4)
    (hH : ContDiffAt ℝ 2 H y) (hr : 0 < fderiv ℝ H y y)
    (hB : ∀ v : R4, fderiv ℝ H y v = 0 → v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) y v v) :
    (∀ v w, completedHessian H y v w = completedHessian H y w v) ∧
    (∀ v : R4, v ≠ 0 → 0 < completedHessian H y v v) := by
  exact ⟨symmetric _ (D2_symm_local H y hH) _ _, positive _ _ _ hr hB⟩

end HryniewiczCriterion.LocalC2

namespace HryniewiczCriterion.LocalC2
open HryniewiczCriterion Matrix
lemma clm_apply_eq_sum' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : R4 →L[ℝ] E)
    (v : R4) : L v = ∑ n, v n • L (Pi.single n 1) := by
  have hv : v = ∑ n, v n • (Pi.single n 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul]

/-- The Hessian matrix `Hm k l = D²H(y)(e_l)(e_k)`. -/
noncomputable def hessMat (B : R4 →L[ℝ] R4 →L[ℝ] ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun k l => B (Pi.single l 1) (Pi.single k 1)

lemma bilin_eq_sum (B : R4 →L[ℝ] R4 →L[ℝ] ℝ) (v w : R4) :
    B v w = ∑ k, ∑ l, w k * hessMat B k l * v l := by
  rw [clm_apply_eq_sum' B v]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [clm_apply_eq_sum' (B (Pi.single l 1)) w, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [hessMat]; ring

lemma jvec_eq_mul (B : R4 →L[ℝ] R4 →L[ℝ] ℝ) (v : R4) (k : Fin 4) :
    jvec (B v) k = ((symplJ4 * hessMat B) *ᵥ v) k := by
  rw [jvec_apply]
  have e : ∀ m, B v (Pi.single m 1) = ∑ l, hessMat B m l * v l := by
    intro m; rw [bilin_eq_sum]
    simp [Pi.single_apply]
  fin_cases k <;>
    simp [e, symplJ4, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

lemma hessMat_posDef (B : R4 →L[ℝ] R4 →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) : (hessMat B).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun v hv => ?_
  · ext k l; simp [hessMat, hsymm]
  · have := hpos v hv
    rw [bilin_eq_sum] at this
    simpa [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
      using this


lemma completedHessian_matrix_continuous (H : R4 → ℝ) (x : ℝ → R4)
    (hxc : Continuous x) (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hr : ∀ t, 0 < fderiv ℝ H (x t) (x t)) :
    ∀ i j, Continuous fun t => hessMat (completedHessian H (x t)) i j := by
  have hellc : Continuous fun t => fderiv ℝ H (x t) :=
    continuous_iff_continuousAt.mpr fun t =>
      ((hH t).continuousAt_fderiv (by norm_num)).comp hxc.continuousAt
  have hBc : Continuous fun t => fderiv ℝ (fderiv ℝ H) (x t) :=
    continuous_iff_continuousAt.mpr fun t =>
      (((hH t).fderiv_right (m := 1) (by norm_num)).continuousAt_fderiv
        (by norm_num)).comp hxc.continuousAt
  have hrc : Continuous fun t => fderiv ℝ H (x t) (x t) := hellc.clm_apply hxc
  have hproj (v : R4) : Continuous fun t =>
      BirkhoffGlobalSection.ContinuousHomogenization.tangentProjection (fderiv ℝ H (x t)) (x t) v := by
    simp only [BirkhoffGlobalSection.ContinuousHomogenization.tangentProjection_apply]
    exact continuous_const.sub (((hellc.clm_apply continuous_const).div hrc
      (fun t => (hr t).ne')).smul hxc)
  intro i j
  change Continuous fun t => completedHessian H (x t) (Pi.single j 1) (Pi.single i 1)
  simp only [completedHessian, BirkhoffGlobalSection.ContinuousHomogenization.radialHomogenization_apply]
  exact ((hBc.clm_apply (hproj _)).clm_apply (hproj _)).add
    (((hellc.clm_apply continuous_const).mul (hellc.clm_apply continuous_const)).div hrc
      (fun t => (hr t).ne'))

lemma completedHessian_matrix_posDef (H : R4 → ℝ) (y : R4)
    (hH : ContDiffAt ℝ 2 H y) (hr : 0 < fderiv ℝ H y y)
    (hB : ∀ v : R4, fderiv ℝ H y v = 0 → v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) y v v) :
    (hessMat (completedHessian H y)).PosDef := by
  exact hessMat_posDef _ (completedHessian_positive H y hH hr hB).1
    (completedHessian_positive H y hH hr hB).2

end HryniewiczCriterion.LocalC2

-- Generic Hamiltonian/frame matrix calculations adapted with credit to Mazecto,
-- accepted homogeneous_frame_flow_split and submission 893234ef-5ec2-4f4b-b415-f79ec1030002.
-- The C2 local completion and projected-flow assembly are derived for this contribution.

namespace HryniewiczCriterion.CanonicalMatrix
open HryniewiczCriterion Matrix

def col (F : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : R4 := fun k => F k i

lemma transpose_omega_mul_apply (F : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (F.transpose * omegaMat * F) i j = omega0 (col F i) (col F j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, omegaMat, omega0, col]; ring

lemma inverse_identities (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) :
    F⁻¹ * F = 1 ∧ F * F⁻¹ = 1 ∧ F⁻¹ * symplJ4 = symplJ4 * F.transpose := by
  have hJΩ : symplJ4 * omegaMat = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [symplJ4, omegaMat, Matrix.mul_apply, Fin.sum_univ_four]
  have hΩJ : omegaMat * symplJ4 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [symplJ4, omegaMat, Matrix.mul_apply, Fin.sum_univ_four]
  let G := symplJ4 * F.transpose * omegaMat
  have hGF : G * F = 1 := by
    dsimp [G]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc F.transpose, hF, hJΩ]
  have hInv : F⁻¹ = G := Matrix.inv_eq_left_inv hGF
  refine ⟨by rw [hInv, hGF], ?_, ?_⟩
  · rw [hInv]; exact mul_eq_one_comm.mp hGF
  · rw [hInv]
    dsimp [G]
    rw [Matrix.mul_assoc, hΩJ, Matrix.mul_one]

lemma omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma mulVec_eq_cols (F : Matrix (Fin 4) (Fin 4) ℝ) (c : R4) :
    F.mulVec c = c 0 • col F 0 + c 1 • col F 1 + c 2 • col F 2 + c 3 • col F 3 := by
  ext i; simp [mulVec, dotProduct, Fin.sum_univ_four, col]; ring

lemma frame_coordinates_pairing (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (v : R4) :
    omega0 (col F 0) v = (F⁻¹.mulVec v) 1 ∧
      omega0 (col F 1) v = -(F⁻¹.mulVec v) 0 := by
  let c := F⁻¹.mulVec v
  have hc : F.mulVec c = v := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, (inverse_identities F hF).2.1, Matrix.one_mulVec]
  have hp : ∀ i j, omega0 (col F i) (col F j) = omegaMat i j := by
    intro i j
    rw [← transpose_omega_mul_apply, hF]
  have h0 : omega0 (col F 0) v = c 1 := by
    calc _ = omega0 (col F 0) (F.mulVec c) := congrArg (omega0 (col F 0)) hc.symm
         _ = c 1 := by rw [mulVec_eq_cols, omega0_lin_right]; simp [hp, omegaMat]
  have h1 : omega0 (col F 1) v = -c 0 := by
    calc _ = omega0 (col F 1) (F.mulVec c) := congrArg (omega0 (col F 1)) hc.symm
         _ = -c 0 := by rw [mulVec_eq_cols, omega0_lin_right]; simp [hp, omegaMat]
  exact ⟨h0, h1⟩

lemma reconstruct_transverse (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (v : R4)
    (h0 : omega0 (col F 0) v = 0) (h1 : omega0 (col F 1) v = 0) :
    v = (F⁻¹.mulVec v) 2 • col F 2 + (F⁻¹.mulVec v) 3 • col F 3 := by
  have hp := frame_coordinates_pairing F hF v
  have hc0 : (F⁻¹.mulVec v) 0 = 0 := by linarith [hp.2]
  have hc1 : (F⁻¹.mulVec v) 1 = 0 := by linarith [hp.1]
  have hc : F.mulVec (F⁻¹.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, (inverse_identities F hF).2.1, Matrix.one_mulVec]
  rw [mulVec_eq_cols, hc0, hc1] at hc
  simpa using hc.symm

lemma lower_block_det_one (φ : Matrix (Fin 2) (Fin 2) ℝ)
    (hφ : (blockOne φ).transpose * omegaMat * blockOne φ = omegaMat) : φ.det = 1 := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 3) hφ
  simp [Matrix.mul_apply, Fin.sum_univ_four, blockOne, omegaMat] at h
  rw [Matrix.det_fin_two]
  linear_combination h

lemma positive_generator_conjugate
    (F : Matrix (Fin 4) (Fin 4) ℝ) (hF : F.transpose * omegaMat * F = omegaMat)
    (W B : ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (hBc : ∀ i j, Continuous fun t => B t i j) (hBpos : ∀ t, (B t).PosDef)
    (hWd : ∀ t i j, HasDerivAt (fun s => W s i j) ((symplJ4 * B t * W t) i j) t) :
    ∃ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, Continuous fun t => S t i j) ∧ (∀ t, (S t).PosDef) ∧
      ∀ t i j, HasDerivAt (fun s => (F⁻¹ * W s) i j)
        ((symplJ4 * S t * (F⁻¹ * W t)) i j) t := by
  refine ⟨fun t => F.transpose * B t * F, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  · intro t
    have hinj : Function.Injective F.mulVec := by
      intro v w hvw
      have h := congrArg F⁻¹.mulVec hvw
      simpa only [Matrix.mulVec_mulVec, (inverse_identities F hF).1, Matrix.one_mulVec] using h
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hBpos t).conjTranspose_mul_mul_same hinj
  · intro t i j
    have hd : HasDerivAt (fun s => (F⁻¹ * W s) i j)
        ((F⁻¹ * (symplJ4 * B t * W t)) i j) t := by
      simp only [Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun k _ => (hWd t k j).const_mul (F⁻¹ i k)
    have heq : symplJ4 * (F.transpose * B t * F) * (F⁻¹ * W t) =
        F⁻¹ * (symplJ4 * B t * W t) := by
      calc _ = symplJ4 * F.transpose * B t * (F * F⁻¹) * W t := by simp only [Matrix.mul_assoc]
           _ = F⁻¹ * (symplJ4 * B t * W t) := by
             rw [(inverse_identities F hF).2.1, Matrix.mul_one, ← (inverse_identities F hF).2.2]
             simp only [Matrix.mul_assoc]
    rw [← heq] at hd
    exact hd


lemma inverse_mulVec_col (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (j : Fin 4) :
    F⁻¹.mulVec (col F j) = Pi.single j 1 := by
  change col (F⁻¹ * F) j = _
  rw [(inverse_identities F hF).1]
  ext i; simp [col, Matrix.one_apply, Pi.single_apply, eq_comm]

lemma omega0_sub_smul_right (u v w : R4) (a : ℝ) :
    omega0 u (v - a • w) = omega0 u v - a * omega0 u w := by
  simp [omega0]; ring

lemma projected_reconstruction (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (v : R4)
    (hv : omega0 (col F 1) v = 0) :
    v - omega0 (col F 0) v • col F 1 =
      (F⁻¹.mulVec v) 2 • col F 2 + (F⁻¹.mulVec v) 3 • col F 3 := by
  have hp01 : omega0 (col F 0) (col F 1) = 1 := by
    rw [← transpose_omega_mul_apply, hF]; rfl
  have hp11 : omega0 (col F 1) (col F 1) = 0 := by
    rw [← transpose_omega_mul_apply, hF]; rfl
  let q := v - omega0 (col F 0) v • col F 1
  have hq0 : omega0 (col F 0) q = 0 := by
    dsimp [q]; rw [omega0_sub_smul_right, hp01]; ring
  have hq1 : omega0 (col F 1) q = 0 := by
    dsimp [q]; rw [omega0_sub_smul_right, hp11, hv]; ring
  have hc2 : (F⁻¹.mulVec q) 2 = (F⁻¹.mulVec v) 2 := by
    simp [q, Matrix.mulVec_sub, Matrix.mulVec_smul, inverse_mulVec_col F hF, Pi.single_apply]
  have hc3 : (F⁻¹.mulVec q) 3 = (F⁻¹.mulVec v) 3 := by
    simp [q, Matrix.mulVec_sub, Matrix.mulVec_smul, inverse_mulVec_col F hF, Pi.single_apply]
  simpa only [hc2, hc3] using reconstruct_transverse F hF q hq0 hq1

end HryniewiczCriterion.CanonicalMatrix

set_option backward.isDefEq.respectTransparency true

namespace HryniewiczCriterion.LocalCanonical
open HryniewiczCriterion LocalC2 CanonicalMatrix
open scoped ContDiff

lemma omega_smul_left (u v : R4) (a : ℝ) : omega0 (a • u) v = a * omega0 u v := by
  simp [omega0]; ring

lemma col_mul (A B : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    col (A * B) j = A.mulVec (col B j) := rfl

lemma col_clm_mul (Y : R4 →L[ℝ] R4) (F : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    col (LinearMap.toMatrix' (Y : R4 →ₗ[ℝ] R4) * F) j = Y (col F j) := by
  ext i
  have h := congrFun (LocalC2.clm_apply_eq_sum' Y (col F j)) i
  change (∑ k, Y (Pi.single k 1) i * F k j) = Y (col F j) i
  symm
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, mul_comm] using h

/-- Positive local differential model, without any homogeneity hypothesis. -/
noncomputable def completedMatrix (H : R4 → ℝ) (x : ℝ → R4)
    (Y : ℝ → (R4 →L[ℝ] R4)) (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let X := hamiltonianVectorField H (x t)
  let r := fderiv ℝ H (x t) (x t)
  let E : Fin 2 → R4 := fun j => col (homogFrame H (x 0)) j.succ.succ
  fun i j => ![x t, r⁻¹ • X,
    Y t (E 0) - (omega0 (x t) (Y t (E 0)) / r) • X,
    Y t (E 1) - (omega0 (x t) (Y t (E 1)) / r) • X] j i

noncomputable def transverseMatrix (H : R4 → ℝ) (x : ℝ → R4) (T : ℝ)
    (Y : ℝ → (R4 →L[ℝ] R4)) (τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => ((homogFrame H (x (τ * T)))⁻¹ *
    LinearMap.toMatrix' (Y (τ * T) : R4 →ₗ[ℝ] R4) * homogFrame H (x 0)) i.succ.succ j.succ.succ

set_option maxHeartbeats 500000 in
lemma completed_initial_derivative
    (H : R4 → ℝ) (x : ℝ → R4) (T : ℝ) (hT : T ≠ 0)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField H (x t)) t)
    (hr : ∀ t, 0 < fderiv ℝ H (x t) (x t))
    (hB : ∀ t v, fderiv ℝ H (x t) v = 0 → v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) (x t) v v)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y)
    (hFsp : ∀ t, (homogFrame H (x t)).transpose * omegaMat * homogFrame H (x t) = omegaMat) :
    completedMatrix H x Y 0 = homogFrame H (x 0) ∧
    (∀ t j, HasDerivAt (fun s => col (completedMatrix H x Y s) j)
      (LocalC2.jvec (completedHessian H (x t) (col (completedMatrix H x Y t) j))) t) := by

  let F := fun t => homogFrame H (x t)
  let φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun τ i j =>
    ((F (τ * T))⁻¹ * LinearMap.toMatrix' (Y (τ * T) : R4 →ₗ[ℝ] R4) * F 0)
      i.succ.succ j.succ.succ
  let X := fun t => hamiltonianVectorField H (x t)
  let r := fun t => fderiv ℝ H (x t) (x t)
  let E : Fin 2 → R4 := fun j => col (F 0) j.succ.succ
  let q : R4 → ℝ → R4 := fun v t => Y t v - (omega0 (x t) (Y t v) / r t) • X t
  let W : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun t i j =>
    ![x t, (r t)⁻¹ • X t, q (E 0) t, q (E 1) t] j i
  have hF0 : ∀ t, col (F t) 0 = x t := fun _ => rfl
  have hωX : ∀ t, omega0 (x t) (X t) = r t := by
    intro t
    dsimp [X, r]
    rw [LocalC2.hamiltonianVectorField_eq, LocalC2.omega0_jvec_right]
  have hF1 : ∀ t, col (F t) 1 = (r t)⁻¹ • X t := by
    intro t
    change (omega0 (x t) (X t))⁻¹ • X t = _
    rw [hωX]
  have hpair : ∀ t i j, omega0 (col (F t) i) (col (F t) j) = omegaMat i j := by
    intro t i j
    rw [← CanonicalMatrix.transpose_omega_mul_apply, hFsp t]
  have hEω : ∀ j, omega0 (x 0) (E j) = 0 := by
    intro j
    change omega0 (col (F 0) 0) (col (F 0) j.succ.succ) = 0
    rw [hpair]
    fin_cases j <;> rfl
  have hEtan : ∀ j, fderiv ℝ H (x 0) (E j) = 0 := by
    intro j
    have hp : omega0 (col (F 0) 1) (E j) = 0 := by
      change omega0 (col (F 0) 1) (col (F 0) j.succ.succ) = 0
      rw [hpair]
      fin_cases j <;> rfl
    rw [hF1, omega_smul_left] at hp
    dsimp [X] at hp
    rw [LocalC2.hamiltonianVectorField_eq, LocalC2.omega0_jvec_left] at hp
    have hn := (mul_eq_zero.mp hp).resolve_left (inv_ne_zero (hr 0).ne')
    linarith
  have hq0 : ∀ j, q (E j) 0 = E j := by
    intro j
    simp only [q, hY.1, ContinuousLinearMap.id_apply, hEω, zero_div, zero_smul, sub_zero]
  have hW0 : W 0 = F 0 := by
    ext i j
    fin_cases j
    · exact congrFun (hF0 0).symm i
    · exact congrFun (hF1 0).symm i
    · exact congrFun (hq0 0) i
    · exact congrFun (hq0 1) i
  have hWdcol : ∀ t j, HasDerivAt (fun s => col (W s) j)
      (LocalC2.jvec (completedHessian H (x t) (col (W t) j))) t := by
    intro t j
    fin_cases j
    · exact completed_radial_solution H x t (hr t).ne' (hx t)
    · exact completed_companion_solution H x t (hH t) (hr t).ne' (hx t)
    · exact completed_projected_solution H x hH hx (fun t => (hr t).ne') Y hY (E 0) (hEtan 0) t
    · exact completed_projected_solution H x hH hx (fun t => (hr t).ne') Y hY (E 1) (hEtan 1) t
  exact ⟨hW0, hWdcol⟩

set_option maxHeartbeats 500000 in
lemma completed_factorization
    (H : R4 → ℝ) (x : ℝ → R4) (T : ℝ) (hT : T ≠ 0)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField H (x t)) t)
    (hr : ∀ t, 0 < fderiv ℝ H (x t) (x t))
    (hB : ∀ t v, fderiv ℝ H (x t) v = 0 → v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) (x t) v v)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y)
    (hFsp : ∀ t, (homogFrame H (x t)).transpose * omegaMat * homogFrame H (x t) = omegaMat) :
    ∀ t, completedMatrix H x Y t = homogFrame H (x t) * blockOne (transverseMatrix H x T Y (t / T)) := by

  let F := fun t => homogFrame H (x t)
  let φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun τ i j =>
    ((F (τ * T))⁻¹ * LinearMap.toMatrix' (Y (τ * T) : R4 →ₗ[ℝ] R4) * F 0)
      i.succ.succ j.succ.succ
  let X := fun t => hamiltonianVectorField H (x t)
  let r := fun t => fderiv ℝ H (x t) (x t)
  let E : Fin 2 → R4 := fun j => col (F 0) j.succ.succ
  let q : R4 → ℝ → R4 := fun v t => Y t v - (omega0 (x t) (Y t v) / r t) • X t
  let W : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun t i j =>
    ![x t, (r t)⁻¹ • X t, q (E 0) t, q (E 1) t] j i
  have hF0 : ∀ t, col (F t) 0 = x t := fun _ => rfl
  have hωX : ∀ t, omega0 (x t) (X t) = r t := by
    intro t
    dsimp [X, r]
    rw [LocalC2.hamiltonianVectorField_eq, LocalC2.omega0_jvec_right]
  have hF1 : ∀ t, col (F t) 1 = (r t)⁻¹ • X t := by
    intro t
    change (omega0 (x t) (X t))⁻¹ • X t = _
    rw [hωX]
  have hpair : ∀ t i j, omega0 (col (F t) i) (col (F t) j) = omegaMat i j := by
    intro t i j
    rw [← CanonicalMatrix.transpose_omega_mul_apply, hFsp t]
  have hEω : ∀ j, omega0 (x 0) (E j) = 0 := by
    intro j
    change omega0 (col (F 0) 0) (col (F 0) j.succ.succ) = 0
    rw [hpair]
    fin_cases j <;> rfl
  have hEtan : ∀ j, fderiv ℝ H (x 0) (E j) = 0 := by
    intro j
    have hp : omega0 (col (F 0) 1) (E j) = 0 := by
      change omega0 (col (F 0) 1) (col (F 0) j.succ.succ) = 0
      rw [hpair]
      fin_cases j <;> rfl
    rw [hF1, omega_smul_left] at hp
    dsimp [X] at hp
    rw [LocalC2.hamiltonianVectorField_eq, LocalC2.omega0_jvec_left] at hp
    have hn := (mul_eq_zero.mp hp).resolve_left (inv_ne_zero (hr 0).ne')
    linarith
  have hqrepr : ∀ t j, q (E j) t =
      φ (t / T) 0 j • col (F t) 2 + φ (t / T) 1 j • col (F t) 3 := by
    intro t j
    have htan : fderiv ℝ H (x t) (Y t (E j)) = 0 := by
      rw [dH_linearizedFlow_local H x hH hx Y hY, hEtan]
    have horth : omega0 (col (F t) 1) (Y t (E j)) = 0 := by
      rw [hF1, omega_smul_left]
      dsimp [X]
      rw [LocalC2.hamiltonianVectorField_eq, LocalC2.omega0_jvec_left, htan]
      ring
    have heq : q (E j) t = Y t (E j) - omega0 (col (F t) 0) (Y t (E j)) • col (F t) 1 := by
      rw [hF0, hF1]
      dsimp [q]
      rw [smul_smul, div_eq_mul_inv]
    rw [heq, projected_reconstruction (F t) (hFsp t) _ horth]
    have hcoeff : col ((F t)⁻¹ * LinearMap.toMatrix' (Y t : R4 →ₗ[ℝ] R4) * F 0) j.succ.succ =
        (F t)⁻¹.mulVec (Y t (E j)) := by
      rw [Matrix.mul_assoc, col_mul, col_clm_mul]
    have hτ : (t / T) * T = t := div_mul_cancel₀ t hT
    simp only [φ, hτ]
    rw [← hcoeff]
    rfl
  have hWfactor : ∀ t, W t = F t * blockOne (φ (t / T)) := by
    intro t
    ext i j
    fin_cases j
    · simpa [W, Matrix.mul_apply, Fin.sum_univ_four, blockOne, col] using congrFun (hF0 t).symm i
    · simpa [W, Matrix.mul_apply, Fin.sum_univ_four, blockOne, col] using congrFun (hF1 t).symm i
    · simpa [W, Matrix.mul_apply, Fin.sum_univ_four, blockOne, col, mul_comm] using congrFun (hqrepr t 0) i
    · simpa [W, Matrix.mul_apply, Fin.sum_univ_four, blockOne, col, mul_comm] using congrFun (hqrepr t 1) i
  exact hWfactor

set_option maxHeartbeats 800000 in
theorem positive_canonical_differential
    (H : R4 → ℝ) (x : ℝ → R4) (T : ℝ) (hT : T ≠ 0)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField H (x t)) t)
    (hr : ∀ t, 0 < fderiv ℝ H (x t) (x t))
    (hB : ∀ t v, fderiv ℝ H (x t) v = 0 → v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) (x t) v v)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y)
    (hFsp : ∀ t, (homogFrame H (x t)).transpose * omegaMat * homogFrame H (x t) = omegaMat) :
    let F := fun t => homogFrame H (x t)
    let φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun τ i j =>
      ((F (τ * T))⁻¹ * LinearMap.toMatrix' (Y (τ * T) : R4 →ₗ[ℝ] R4) * F 0)
        i.succ.succ j.succ.succ
    (∀ τ, (φ τ).det = 1) ∧
    (∃ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, Continuous fun t => S t i j) ∧ (∀ t, (S t).PosDef) ∧
      ∀ t i j, HasDerivAt (fun s => ((F 0)⁻¹ * F s * blockOne (φ (s / T))) i j)
        ((symplJ4 * S t * ((F 0)⁻¹ * F t * blockOne (φ (t / T)))) i j) t) := by
  let F := fun t => homogFrame H (x t)
  let φ := transverseMatrix H x T Y
  change (∀ τ, (φ τ).det = 1) ∧
    (∃ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, Continuous fun t => S t i j) ∧ (∀ t, (S t).PosDef) ∧
      ∀ t i j, HasDerivAt (fun s => ((F 0)⁻¹ * F s * blockOne (φ (s / T))) i j)
        ((symplJ4 * S t * ((F 0)⁻¹ * F t * blockOne (φ (t / T)))) i j) t)
  let W := completedMatrix H x Y
  obtain ⟨hW0, hWdcol⟩ := completed_initial_derivative H x T hT hH hx hr hB Y hY hFsp
  have hWfactor := completed_factorization H x T hT hH hx hr hB Y hY hFsp
  change W 0 = F 0 at hW0
  change ∀ t, W t = F t * blockOne (φ (t / T)) at hWfactor
  have hWsp : ∀ t, (W t).transpose * omegaMat * W t = omegaMat := by
    intro t
    ext i j
    rw [CanonicalMatrix.transpose_omega_mul_apply]
    have h := symplectic_pairing_constant (fun s => completedHessian H (x s))
      (fun s => (completedHessian_positive H (x s) (hH s) (hr s) (hB s)).1)
      (fun s => col (W s) i) (fun s => col (W s) j)
      (fun s => hWdcol s i) (fun s => hWdcol s j) t
    rw [hW0] at h
    rw [h, ← CanonicalMatrix.transpose_omega_mul_apply, hFsp 0]
  have hdet : ∀ τ, (φ τ).det = 1 := by
    intro τ
    apply lower_block_det_one
    have hfac : W (τ * T) = F (τ * T) * blockOne (φ τ) := by
      simpa only [mul_div_cancel_right₀ τ hT] using hWfactor (τ * T)
    calc _ = (blockOne (φ τ)).transpose *
          ((F (τ * T)).transpose * omegaMat * F (τ * T)) * blockOne (φ τ) := by rw [hFsp]
         _ = (W (τ * T)).transpose * omegaMat * W (τ * T) := by
           rw [hfac, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
         _ = omegaMat := hWsp _
  have hBmcont := completedHessian_matrix_continuous H x
    (continuous_iff_continuousAt.mpr fun t => (hx t).continuousAt) hH hr
  have hBmpos : ∀ t, (hessMat (completedHessian H (x t))).PosDef := fun t =>
    completedHessian_matrix_posDef H (x t) (hH t) (hr t) (hB t)
  have hWd : ∀ t i j, HasDerivAt (fun s => W s i j)
      ((symplJ4 * hessMat (completedHessian H (x t)) * W t) i j) t := by
    intro t i j
    have hd := hasDerivAt_pi.1 (hWdcol t j) i
    have he : LocalC2.jvec (completedHessian H (x t) (col (W t) j)) i =
        (symplJ4 * hessMat (completedHessian H (x t)) * W t) i j := by
      rw [jvec_eq_mul]
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, col]
    rwa [he] at hd
  obtain ⟨S, hSc, hSpos, hSd⟩ := positive_generator_conjugate (F 0) (hFsp 0)
    W (fun t => hessMat (completedHessian H (x t))) hBmcont hBmpos hWd
  refine ⟨hdet, S, hSc, hSpos, ?_⟩
  intro t i j
  simpa only [hWfactor, Matrix.mul_assoc] using hSd t i j


end HryniewiczCriterion.LocalCanonical


open HryniewiczCriterion
open scoped ContDiff

theorem solution
    (H : R4 → ℝ) (x : ℝ → R4) (T : ℝ) (hT : T ≠ 0)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (hamiltonianVectorField H (x t)) t)
    (hr : ∀ t, 0 < fderiv ℝ H (x t) (x t))
    (hB : ∀ t v, fderiv ℝ H (x t) v = 0 → v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ H) (x t) v v)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y)
    (hFsp : ∀ t, (homogFrame H (x t)).transpose * omegaMat * homogFrame H (x t) = omegaMat) :
    let F := fun t => homogFrame H (x t)
    let φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun τ i j =>
      ((F (τ * T))⁻¹ * LinearMap.toMatrix' (Y (τ * T) : R4 →ₗ[ℝ] R4) * F 0)
        i.succ.succ j.succ.succ
    (∀ τ, (φ τ).det = 1) ∧
    (∃ S : ℝ → Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, Continuous fun t => S t i j) ∧ (∀ t, (S t).PosDef) ∧
      ∀ t i j, HasDerivAt (fun s => ((F 0)⁻¹ * F s * blockOne (φ (s / T))) i j)
        ((symplJ4 * S t * ((F 0)⁻¹ * F t * blockOne (φ (t / T)))) i j) t)  := by
  exact HryniewiczCriterion.LocalCanonical.positive_canonical_differential
    H x T hT hH hx hr hB Y hY hFsp
