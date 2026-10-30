-- Prove2me | solution 1 for HryniewiczCriterion.local_C2_variational_transport
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T19:31:17.330993+00:00
-- url     : https://prove2.me/submissions/4d0ad10c-5c20-4eb7-804e-4265b25d8fc0

-- Generic Hamiltonian/frame matrix calculations adapted with credit to Mazecto,
-- accepted homogeneous_frame_flow_split and submission 893234ef-5ec2-4f4b-b415-f79ec1030002.
-- The C2 local completion and projected-flow assembly are derived for this contribution.
import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

set_option Elab.async false

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
open HryniewiczCriterion
open scoped ContDiff
lemma omega0_nondeg {a b : R4} (h : ∀ u, omega0 u a = omega0 u b) : a = b := by
  have e := fun i => h (Pi.single i 1)
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3
  simp [omega0, Pi.single_apply] at e0 e1 e2 e3
  ext i; fin_cases i <;> simp <;> linarith

lemma linearizedFlow_surj (H : R4 → ℝ) (x : ℝ → R4)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) (t : ℝ) :
    Function.Surjective (Y t) := by
  have hinj : Function.Injective (Y t) := by
    refine (injective_iff_map_eq_zero (Y t)).2 fun u hu => ?_
    refine omega0_nondeg fun v => ?_
    have he := omega0_linearizedFlow_local H x hH Y hY v u t
    rw [hu] at he
    rw [← he]; simp [omega0]
  exact LinearMap.injective_iff_surjective.1 hinj

lemma field_transport (H : R4 → ℝ) (x : ℝ → R4)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (HryniewiczCriterion.hamiltonianVectorField H (x t)) t)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) (t : ℝ) :
    Y t (HryniewiczCriterion.hamiltonianVectorField H (x 0)) =
      HryniewiczCriterion.hamiltonianVectorField H (x t) := by
  refine omega0_nondeg fun u => ?_
  obtain ⟨w, rfl⟩ := linearizedFlow_surj H x hH Y hY t u
  rw [omega0_linearizedFlow_local H x hH Y hY]
  simp only [hamiltonianVectorField_eq]
  rw [omega0_jvec_right, omega0_jvec_right, dH_linearizedFlow_local H x hH hx Y hY]
end HryniewiczCriterion.LocalC2

open HryniewiczCriterion
open scoped ContDiff
 theorem solution (H : R4 → ℝ) (x : ℝ → R4)
    (hH : ∀ t, ContDiffAt ℝ 2 H (x t))
    (hx : ∀ t, HasDerivAt x (HryniewiczCriterion.hamiltonianVectorField H (x t)) t)
    (Y : ℝ → (R4 →L[ℝ] R4)) (hY : IsLinearizedFlow H x Y) :
    (∀ v t, fderiv ℝ H (x t) (Y t v) = fderiv ℝ H (x 0) v) ∧
    (∀ t, Y t (HryniewiczCriterion.hamiltonianVectorField H (x 0)) =
      HryniewiczCriterion.hamiltonianVectorField H (x t)) := by
  exact ⟨LocalC2.dH_linearizedFlow_local H x hH hx Y hY,
    LocalC2.field_transport H x hH hx Y hY⟩
