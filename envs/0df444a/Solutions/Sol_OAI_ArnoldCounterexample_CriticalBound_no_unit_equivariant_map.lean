-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.no_unit_equivariant_map
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:00:56.084262+00:00
-- url     : https://prove2.me/submissions/87e84a70-17c5-4b3e-a82f-4db84bade4ef

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Obstruction.lean:L178-L220
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.no_unit_equivariant_map. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_haar_homotopy_invariant
import Theorems.Thm_OAI_ArnoldCounterexample_Forms_contDiff_pullback_form
import Theorems.Thm_OAI_ArnoldCounterexample_Forms_cubeForm_second_radical_on
import Theorems.Thm_OAI_ArnoldCounterexample_Forms_fderiv_circle_equivariant
import Theorems.Thm_OAI_ArnoldCounterexample_Forms_normSq_fderiv

-- ---- from OAI.Geometry.Arnold.Haar ----
namespace OAI

universe uG

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter

open scoped BigOperators
open MeasureTheory Set Filter

namespace ArnoldCounterexample.CriticalBound

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound

end ArnoldCounterexample.CriticalBound

open scoped Matrix.Norms.Operator ContDiff

namespace ArnoldCounterexample.CriticalBound

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instContinuousStarRM
lemma right_expCurve_hasDerivAt (X : RM) (hX : star X = -X) (A : O5) (t : ℝ) :
    HasDerivAt (fun s ↦ ((A * expCurve X hX s : O5) : RM))
      (((A * expCurve X hX t : O5) : RM) * X) t := by
  convert! (hasDerivAt_exp_smul_const X t).const_mul (A : RM) using 1
  exact mul_assoc _ _ _

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- from OAI.Geometry.Arnold.Orbit ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample

namespace CriticalBound
open Matrix

lemma complexMat_mul (A B : RM) : complexMat (A * B) = complexMat A * complexMat B := by
  ext i j
  simp [complexMat, Matrix.mul_apply]

lemma complexMat_star (A : RM) : complexMat (star A) = star (complexMat A) := by
  ext i j
  simp [complexMat, Matrix.star_apply]

lemma act_mul (A B : RM) (z : CV) : act (A * B) z = act A (act B z) := by
  simp [act, complexMat_mul, Matrix.mulVec_mulVec]

lemma act_smul (A : RM) (a : ℂ) (z : CV) : act A (a • z) = a • act A z := by
  exact Matrix.mulVec_smul _ _ _

lemma act_sub_left (A B : RM) (z : CV) : act (A - B) z = act A z - act B z := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, sub_mul]

lemma act_preserves_hermitian (A : O5) (z w : CV) :
    star (act A z) ⬝ᵥ act A w = star z ⬝ᵥ w := by
  have hA : star (complexMat A) * complexMat A = 1 := by
    rw [← complexMat_star, ← complexMat_mul, A.property.1, complexMat_one]
  calc
    star (act A z) ⬝ᵥ act A w = (star z ᵥ* star (complexMat A)) ⬝ᵥ (complexMat A *ᵥ w) := by
      simp only [act, Matrix.star_mulVec, Matrix.star_eq_conjTranspose]
    _ = star z ⬝ᵥ (star (complexMat A) *ᵥ (complexMat A *ᵥ w)) := (Matrix.dotProduct_mulVec _ _ _).symm
    _ = star z ⬝ᵥ w := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

lemma omega_act (A : O5) (v w : CV) : omega (act A v) (act A w) = omega v w := by
  unfold omega
  exact congrArg (fun a : ℂ ↦ 2 * a.im) (act_preserves_hermitian A v w)

lemma rotGen_skew (a b : Fin 5) : star (rotGen a b) = -rotGen a b := by
  ext i j
  simp [rotGen, Matrix.star_apply, Matrix.single_apply, sub_eq_add_neg, and_comm]

lemma rotGen_act (a b : Fin 5) (z : CV) :
    act (rotGen a b) z = Pi.single b (z a) - Pi.single a (z b) := by
  change (complexMat (Matrix.single b a 1 - Matrix.single a b 1)).mulVec z = _
  have h : complexMat (Matrix.single b a 1 - Matrix.single a b 1) =
      Matrix.single b a (1 : ℂ) - Matrix.single a b 1 := by
    ext i j
    simp [complexMat, Matrix.single_apply, apply_ite Complex.ofReal]
  rw [h, Matrix.sub_mulVec, Matrix.single_mulVec, Matrix.single_mulVec]
  ext i
  simp [Function.update_apply, Pi.single_apply, eq_comm]

end CriticalBound
end ArnoldCounterexample

namespace ArnoldCounterexample.CriticalBound

lemma baseScale_sq : baseScale ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)

lemma base_unit : IsUnitQuadric base := by
  constructor
  · simp [normSquared, base, Fin.sum_univ_succ, Complex.normSq_mul,
      Complex.normSq_ofReal, ← sq, baseScale_sq]
    norm_num
  · simp [quadricPolynomial, base, Fin.sum_univ_succ, mul_pow, Complex.I_sq]

lemma generators_skew (i : Fin 6) : star (generators i) = -generators i := by
  fin_cases i <;> exact rotGen_skew _ _

lemma generators_base (i : Fin 6) : act (generators i) base = velocities i := by
  fin_cases i <;> simp [generators, velocities, rotGen_act, base]

lemma generators_bracket_base (i j : Fin 6) :
    act (generators i * generators j - generators j * generators i) base =
      (bracketCoefficient i j : ℂ) • (Complex.I • base) := by
  rw [act_sub_left, act_mul, act_mul, generators_base, generators_base]
  fin_cases i <;> fin_cases j <;>
    ext k <;> fin_cases k <;>
    simp [generators, velocities, rotGen_act, bracketCoefficient, base,
      ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM
lemma act_star (A : RM) (z : CV) : act A (star z) = star (act A z) := by
  ext i
  simp [act, complexMat, Matrix.mulVec, dotProduct]

lemma act_preserves_bilinear (A : O5) (z w : CV) :
    act A z ⬝ᵥ act A w = z ⬝ᵥ w := by
  simpa only [act_star, star_star] using act_preserves_hermitian A (star z) w

lemma act_preserves_quadricPolynomial (A : O5) (z : CV) :
    quadricPolynomial (act A z) = quadricPolynomial z := by
  simpa only [quadricPolynomial, dotProduct, pow_two] using act_preserves_bilinear A z z

lemma normSquared_eq_re (z : CV) : normSquared z = (star z ⬝ᵥ z).re := by
  simp [normSquared, dotProduct, Complex.normSq, Complex.mul_re]

lemma act_preserves_normSquared (A : O5) (z : CV) :
    normSquared (act A z) = normSquared z := by
  rw [normSquared_eq_re, normSquared_eq_re, act_preserves_hermitian]

lemma act_unit (A : O5) (z : UnitQuadric) : IsUnitQuadric (act A z) := by
  exact ⟨(act_preserves_normSquared A z).trans z.property.1,
    (act_preserves_quadricPolynomial A z).trans z.property.2⟩

lemma orbitProjection_unit (A : O5) : IsUnitQuadric (orbitProjection A) :=
  act_unit A ⟨base, base_unit⟩

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- from OAI.Geometry.Arnold.Symplectic ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

open scoped BigOperators ContDiff

namespace ArnoldCounterexample.Forms

lemma symplectic_apply (n : ℕ) (u v : CSpace n) :
    symplectic n u v = 2 * ∑ i, ((u i).re * (v i).im - (u i).im * (v i).re) := by
  simp [symplectic, _root_.sum_apply, ContinuousLinearMap.bilinearComp_apply]

lemma symplectic_skew (n : ℕ) (u v : CSpace n) :
    symplectic n u v = -symplectic n v u := by
  rw [symplectic_apply, symplectic_apply, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma symplectic_eq (n : ℕ) (u v : CSpace n) :
    symplectic n u v = 2 * (∑ i, star (u i) * v i).im := by
  simp [symplectic_apply, Complex.mul_im, sub_eq_add_neg, Finset.sum_add_distrib]

lemma normSq_contDiff (n : ℕ) : ContDiff ℝ ∞ (normSq n) := by
  unfold normSq
  apply ContDiff.sum
  intro i _
  simpa only [Complex.normSq_apply, reCoord_apply, imCoord_apply] using
    (((reCoord n i).contDiff.mul (reCoord n i).contDiff).add
      ((imCoord n i).contDiff.mul (imCoord n i).contDiff))

lemma symplectic_I_left (n : ℕ) (z v : CSpace n) :
    symplectic n (Complex.I • z) v =
      -2 * ∑ i, ((z i).re * (v i).re + (z i).im * (v i).im) := by
  rw [symplectic_apply]
  have h (i : Fin n) :
      ((Complex.I • z) i).re * (v i).im - ((Complex.I • z) i).im * (v i).re =
        -((z i).re * (v i).re + (z i).im * (v i).im) := by
    simp only [Pi.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
    ring
  simp_rw [h]
  rw [Finset.sum_neg_distrib]
  ring

end ArnoldCounterexample.Forms

end

end OAI

-- ---- from OAI.Geometry.Arnold.Exterior ----
namespace OAI

universe uE uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function

open scoped BigOperators ContDiff
open ContinuousAlternatingMap

namespace ArnoldCounterexample.Forms

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma pairForm_apply {n : ℕ} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (η : E [⋀^Fin n]→L[ℝ] ℝ) (v : Fin (n + 2) → E) :
    pairForm B η v = ∑ i : Fin (n + 2), ∑ j : Fin (n + 1),
      (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ j.val *
        B (v i) ((i.removeNth v) j) * η (j.removeNth (i.removeNth v)) := by
  simp [pairForm, alternatizeUncurryFin_apply, ContinuousLinearMap.smulRightL,
    ← Int.cast_smul_eq_zsmul ℝ,
    smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma pairForm_pullback {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (B : F →L[ℝ] F →L[ℝ] ℝ) (η : F [⋀^Fin n]→L[ℝ] ℝ)
    (L : E →L[ℝ] F) (v : Fin (n + 2) → E) :
    pairForm B η (L ∘ v) =
      pairForm (B.bilinearComp L L) (η.compContinuousLinearMap L) v := by
  simp only [pairForm_apply, ContinuousLinearMap.bilinearComp_apply,
    compContinuousLinearMap_apply, Function.comp_apply]
  rfl

lemma cubeForm_pullback {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ) (L : E →L[ℝ] F) :
    (cubeForm B).compContinuousLinearMap L = cubeForm (B.bilinearComp L L) := by
  have hpair {n : ℕ} (η : F [⋀^Fin n]→L[ℝ] ℝ) :
      (pairForm B η).compContinuousLinearMap L =
        pairForm (B.bilinearComp L L) (η.compContinuousLinearMap L) := by
    ext v
    exact pairForm_pullback B η L v
  simp only [cubeForm, squareForm, hpair]
  congr 3

lemma squareForm_apply (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hskew : ∀ u v, B u v = -B v u) (v : Fin 4 → E) :
    squareForm B v = 8 * (B (v 0) (v 1) * B (v 2) (v 3) -
      B (v 0) (v 2) * B (v 1) (v 3) + B (v 0) (v 3) * B (v 1) (v 2)) := by
  simp only [squareForm, pairForm_apply, constOfIsEmpty_apply]
  simp +decide [Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove]
  rw [hskew (v 1) (v 0), hskew (v 2) (v 0), hskew (v 2) (v 1),
      hskew (v 3) (v 0), hskew (v 3) (v 1), hskew (v 3) (v 2)]
  ring

end ArnoldCounterexample.Forms

end

end OAI

-- ---- from OAI.Geometry.Arnold.Homotopy ----
namespace OAI

universe uE uD uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

open scoped BigOperators ContDiff
open ContinuousAlternatingMap

namespace ArnoldCounterexample.Forms
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pullback of a constant form is closed. -/
lemma pullback_constant_closed {D : Type uD} {F : Type uF}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (θ : F [⋀^Fin n]→L[ℝ] ℝ) (H : D → F)
    (hH : ContDiff ℝ ∞ H) (x : D) :
    extDeriv (fun y ↦ θ.compContinuousLinearMap (fderiv ℝ H y)) x = 0 := by
  have hθ : DifferentiableAt ℝ (fun _ : F ↦ θ) (H x) := differentiableAt_const _
  have hH2 : ContDiffAt ℝ 2 H x := hH.contDiffAt.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hp := extDeriv_pullback hθ hH2 (by simp)
  convert hp using 1
  ext v
  simp [extDeriv, alternatizeUncurryFin_apply]

end ArnoldCounterexample.Forms

end

end OAI

-- ---- from OAI.Geometry.Arnold.Volume ----
namespace OAI

universe uE uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_3
end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

lemma symplectic_velocities (i j : Fin 6) :
    symplectic 5 (velocities i) (velocities j) =
      if (i, j) ∈ ({(0, 1), (2, 3), (4, 5)} : Finset (Fin 6 × Fin 6)) then 1
      else if (j, i) ∈ ({(0, 1), (2, 3), (4, 5)} : Finset (Fin 6 × Fin 6)) then -1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [symplectic_apply, velocities, Fin.sum_univ_succ, Pi.single_apply,
      Complex.mul_re, Complex.mul_im, ← sq, baseScale_sq]

lemma cubeForm_velocities : cubeForm (symplectic 5) velocities = 48 := by
  simp only [cubeForm, pairForm_apply, squareForm_apply _ (symplectic_skew 5)]
  simp +decide [Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove, symplectic_velocities]
  norm_num

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

lemma productSymplectic_skew (u v : ProductSpace) :
    productSymplectic u v = -productSymplectic v u := by
  simp only [productSymplectic_apply, symplectic_skew 5 u.1 v.1,
    symplectic_skew 3 u.2 v.2]
  ring

lemma productNormSq_contDiff : ContDiff ℝ ∞ productNormSq :=
  (normSq_contDiff 5 |>.comp contDiff_fst).add (normSq_contDiff 3 |>.comp contDiff_snd)

lemma productNormSq_fderiv (z v : ProductSpace) :
    fderiv ℝ productNormSq z v = -productSymplectic (Complex.I • z) v := by
  have hn5 := (normSq_contDiff 5).differentiable (by simp)
  have hn3 := (normSq_contDiff 3).differentiable (by simp)
  have hd := ((hn5 z.1).hasFDerivAt.comp z hasFDerivAt_fst).add
    ((hn3 z.2).hasFDerivAt.comp z hasFDerivAt_snd)
  rw [show fderiv ℝ productNormSq z = _ from hd.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', normSq_fderiv, productSymplectic_apply, Prod.smul_fst,
    Prod.smul_snd]
  ring

lemma productNormSq_curve_orthogonal {c : ℝ → ProductSpace} {v : ProductSpace} {t : ℝ}
    (hc : HasDerivAt c v t) (hunit : ∀ s, productNormSq (c s) = 1) :
    productSymplectic (Complex.I • c t) v = 0 := by
  have hd := (productNormSq_contDiff.differentiable (by simp) (c t)).hasFDerivAt.comp_hasDerivAt t hc
  have heq : (fun s ↦ productNormSq (c s)) = fun _ : ℝ ↦ 1 := funext hunit
  dsimp only [Function.comp_def] at hd
  rw [heq] at hd
  have hzero := hd.unique (hasDerivAt_const t 1)
  rw [productNormSq_fderiv] at hzero
  exact neg_eq_zero.mp hzero

lemma normSq_real_smul (n : ℕ) (a : ℝ) (z : CSpace n) :
    normSq n (a • z) = a ^ 2 * normSq n z := by
  simp [normSq, Pi.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal, Finset.mul_sum, sq]

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms

lemma time_slice_hasDerivAt {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : ℝ × E → F) (hH : Differentiable ℝ H) (x : E) (t : ℝ) :
    HasDerivAt (fun s ↦ H (s, x)) (fderiv ℝ H (t, x) (1, 0)) t := by
  exact (hH (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

lemma productNormSq_time_tangent {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ × E → ProductSpace) (hH : ContDiff ℝ ∞ H) (x : E)
    (hunit : ∀ s, productNormSq (H (s, x)) = 1) (t : ℝ) :
    productSymplectic (Complex.I • H (t, x)) (fderiv ℝ H (t, x) (1, 0)) = 0 := by
  apply productNormSq_curve_orthogonal
    (time_slice_hasDerivAt H (hH.differentiable (by simp)) x t) hunit

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

lemma alternating_eq_zero_on_kernel
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (hdim : Module.finrank ℝ E ≤ n)
    (θ : E [⋀^Fin n]→L[ℝ] ℝ) (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    (v : Fin n → E) (hv : ∀ i, L (v i) = 0) : θ v = 0 := by
  apply θ.toAlternatingMap.map_linearDependent
  intro hLI
  let v' : Fin n → L.ker := fun i ↦ ⟨v i, hv i⟩
  have hLI' : LinearIndependent ℝ v' := hLI.of_comp L.ker.subtype
  have htop : L.ker ≠ ⊤ := by
    intro ht
    apply hL
    ext x
    have hx : x ∈ L.ker := by rw [ht]; trivial
    exact hx
  have hc := hLI'.fintype_card_le_finrank
  have hlt := Submodule.finrank_lt htop
  simp only [Fintype.card_fin] at hc
  omega

/-- Six tangent vectors of the unit five-sphere are necessarily dependent. -/
lemma six_form_vanishes_on_unit_sphere
    (θ : CSpace 3 [⋀^Fin 6]→L[ℝ] ℝ) (z : CSpace 3) (hz : normSq 3 z = 1)
    (v : Fin 6 → CSpace 3) (hv : ∀ i, fderiv ℝ (normSq 3) z (v i) = 0) :
    θ v = 0 := by
  apply alternating_eq_zero_on_kernel (L := fderiv ℝ (normSq 3) z) ?_ θ ?_ v hv
  · simp [CSpace, Module.finrank_pi_fintype, Complex.finrank_real_complex]
  · intro h
    have hs := normSq_fderiv 3 z z
    rw [h] at hs
    simp only [_root_.zero_apply, symplectic_I_left] at hs
    have heq : (∑ i : Fin 3, ((z i).re * (z i).re + (z i).im * (z i).im)) = 1 := by
      simpa only [normSq, Complex.normSq_apply] using hz
    rw [heq] at hs
    norm_num at hs

end ArnoldCounterexample.Forms

namespace ArnoldCounterexample.Forms
open ContinuousAlternatingMap

end ArnoldCounterexample.Forms

end

end OAI

-- ---- from OAI.Geometry.Arnold.Obstruction ----
namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_4
lemma symplectic_act (A : O5) :
    (symplectic 5).bilinearComp (actCLM A) (actCLM A) = symplectic 5 := by
  ext u v
  simpa only [ContinuousLinearMap.bilinearComp_apply, actCLM_apply, symplectic_eq,
    omega] using omega_act A u v

lemma cubeForm_orbit (A : O5) :
    cubeForm (symplectic 5) (fun i ↦ act A (velocities i)) = 48 := by
  have h := congrArg (fun θ : CV [⋀^Fin 6]→L[ℝ] ℝ ↦ θ velocities)
    (cubeForm_pullback (symplectic 5) (actCLM A))
  simpa only [compContinuousLinearMap_apply, Function.comp_def, actCLM_apply,
    symplectic_act, cubeForm_velocities] using h

lemma joinHomotopy_contDiff (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (joinHomotopy F) := by
  exact (Real.contDiff_cos.comp contDiff_fst |>.smul (orbitProjection.contDiff.comp contDiff_snd)).prodMk
    (Real.contDiff_sin.comp contDiff_fst |>.smul (hF.comp (orbitProjection.contDiff.comp contDiff_snd)))

lemma joinHomotopy_unit (F : CV → CSpace 3)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1) (t : ℝ) (A : O5) :
    productNormSq (joinHomotopy F (t, A)) = 1 := by
  simp only [productNormSq, joinHomotopy, normSq_real_smul]
  rw [show normSq 5 (orbitProjection A) = 1 from (orbitProjection_unit A).1,
    hunit ⟨orbitProjection A, orbitProjection_unit A⟩]
  nlinarith [Real.sin_sq_add_cos_sq t]

lemma joinHomotopy_fderiv_spatial (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (A B : RM) :
    fderiv ℝ (joinHomotopy F) (t, A) (0, B) =
      (Real.cos t • orbitProjection B,
       Real.sin t • fderiv ℝ F (orbitProjection A) (orbitProjection B)) := by
  have hp : HasDerivAt (fun s : ℝ ↦ (t, A + s • B)) (0, B) 0 := by
    convert (hasDerivAt_const 0 t).prodMk ((hasDerivAt_const 0 A).add
      ((hasDerivAt_id (0 : ℝ)).smul_const B)) using 1 <;> simp
  have hd := (joinHomotopy_contDiff F hF |>.differentiable (by simp) (t, A + 0 • B)).hasFDerivAt.comp_hasDerivAt 0 hp
  have ho : HasDerivAt (fun s : ℝ ↦ orbitProjection (A + s • B)) (orbitProjection B) 0 := by
    convert! orbitProjection.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const 0 A).add ((hasDerivAt_id (0 : ℝ)).smul_const B)) using 1; simp
  have hf := (hF.differentiable (by simp) (orbitProjection (A + 0 • B))).hasFDerivAt.comp_hasDerivAt 0 ho
  have hh := (ho.const_smul (Real.cos t)).prodMk (hf.const_smul (Real.sin t))
  simpa only [Function.comp_def, zero_smul, add_zero, joinHomotopy] using hd.unique hh

lemma joinHomotopy_spatial_tangent (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1)
    (t : ℝ) (A : O5) (X : RM) (hX : star X = -X) :
    productSymplectic (Complex.I • joinHomotopy F (t, A))
      (fderiv ℝ (joinHomotopy F) (t, A) (0, (A : RM) * X)) = 0 := by
  have hd := (joinHomotopy_contDiff F hF |>.differentiable (by simp)
      (t, ((A * expCurve X hX 0 : O5) : RM))).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const 0 t).prodMk (right_expCurve_hasDerivAt X hX A 0))
  have hz := productNormSq_curve_orthogonal hd
    (fun s ↦ joinHomotopy_unit F hunit t (A * expCurve X hX s))
  simpa [expCurve] using hz

lemma joinHomotopy_time_tangent (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1) (t : ℝ) (A : O5) :
    productSymplectic (Complex.I • joinHomotopy F (t, A))
      (fderiv ℝ (joinHomotopy F) (t, A) (1, 0)) = 0 :=
  productNormSq_time_tangent (joinHomotopy F) (joinHomotopy_contDiff F hF) (A : RM)
    (fun s ↦ joinHomotopy_unit F hunit s A) t

lemma joinHomotopy_bracket (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z)
    (t : ℝ) (A : O5) (i j : Fin 6) :
    fderiv ℝ (joinHomotopy F) (t, A)
      (0, (A : RM) * (generators i * generators j - generators j * generators i)) =
    bracketCoefficient i j • (Complex.I • joinHomotopy F (t, A)) := by
  rw [joinHomotopy_fderiv_spatial F hF]
  simp only [orbitProjection_apply, act_mul, generators_bracket_base, act_smul]
  have heq : ((bracketCoefficient i j : ℝ) : ℂ) • (Complex.I • act A base) =
      bracketCoefficient i j • (Complex.I • act A base) := by
    ext k
    simp [Complex.real_smul]
  have hfp : fderiv ℝ F (act A base) (Complex.I • act A base) = Complex.I • F (act A base) :=
    fderiv_circle_equivariant F (hF.differentiable (by simp)) (act A base)
      (hphase ⟨orbitProjection A, orbitProjection_unit A⟩)
  rw [heq, map_smul, hfp]
  ext k <;> simp only [joinHomotopy, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, Complex.real_smul, smul_eq_mul, orbitProjection_apply] <;> ring

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms ContinuousAlternatingMap

lemma haar_mass_pos : 0 < (haar Set.univ).toReal := by
  exact ENNReal.toReal_pos (isOpen_univ.measure_pos haar Set.univ_nonempty).ne'
    (measure_ne_top _ _)

attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_5
lemma productSymplectic_inl :
    productSymplectic.bilinearComp (ContinuousLinearMap.inl ℝ (CSpace 5) (CSpace 3))
      (ContinuousLinearMap.inl ℝ (CSpace 5) (CSpace 3)) = symplectic 5 := by
  ext u v
  simp [productSymplectic_apply]

lemma productSymplectic_inr :
    productSymplectic.bilinearComp (ContinuousLinearMap.inr ℝ (CSpace 5) (CSpace 3))
      (ContinuousLinearMap.inr ℝ (CSpace 5) (CSpace 3)) = symplectic 3 := by
  ext u v
  simp [productSymplectic_apply]

lemma joinHomotopy_zero_cube (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F) (A : O5) :
    cubeForm productSymplectic
      (fun i ↦ fderiv ℝ (joinHomotopy F) (0, A) (0, (A : RM) * generators i)) = 48 := by
  have h := congrArg (fun θ : CV [⋀^Fin 6]→L[ℝ] ℝ ↦ θ (fun i ↦ act A (velocities i)))
    (cubeForm_pullback productSymplectic (ContinuousLinearMap.inl ℝ (CSpace 5) (CSpace 3)))
  simp only [productSymplectic_inl, cubeForm_orbit] at h
  simpa only [joinHomotopy_fderiv_spatial F hF, Real.cos_zero, Real.sin_zero,
    one_smul, zero_smul, orbitProjection_apply, act_mul, generators_base,
    compContinuousLinearMap_apply, Function.comp_def, ContinuousLinearMap.inl_apply] using h

lemma sphere_map_tangent (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1) (A : O5) (i : Fin 6) :
    fderiv ℝ (normSq 3) (F (orbitProjection A))
      (fderiv ℝ F (orbitProjection A) (act A (velocities i))) = 0 := by
  have hf := (hF.differentiable (by simp)
      (orbitProjection ((A * expCurve (generators i) (generators_skew i) 0 : O5) : RM))).hasFDerivAt.comp_hasDerivAt 0
    (orbitProjection.hasFDerivAt.comp_hasDerivAt 0
      (right_expCurve_hasDerivAt (generators i) (generators_skew i) A 0))
  have hn := (normSq_contDiff 3 |>.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 hf
  have heq : (fun t ↦ normSq 3 (F (orbitProjection
      ((A * expCurve (generators i) (generators_skew i) t : O5) : RM)))) =
      fun _ : ℝ ↦ 1 := funext (fun t ↦ hunit
        ⟨orbitProjection ((A * expCurve (generators i) (generators_skew i) t : O5) : RM),
          orbitProjection_unit _⟩)
  dsimp only [Function.comp_def] at hn
  rw [heq] at hn
  have hz := hn.unique (hasDerivAt_const 0 1)
  simpa [expCurve, orbitProjection_apply, act_mul, generators_base] using hz

lemma joinHomotopy_half_pi_cube (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1) (A : O5) :
    cubeForm productSymplectic
      (fun i ↦ fderiv ℝ (joinHomotopy F) (Real.pi / 2, A) (0, (A : RM) * generators i)) = 0 := by
  let v : Fin 6 → CSpace 3 := fun i ↦ fderiv ℝ F (orbitProjection A) (act A (velocities i))
  have h := congrArg (fun θ : CSpace 3 [⋀^Fin 6]→L[ℝ] ℝ ↦ θ v)
    (cubeForm_pullback productSymplectic (ContinuousLinearMap.inr ℝ (CSpace 5) (CSpace 3)))
  rw [productSymplectic_inr] at h
  have hz : cubeForm (symplectic 3) v = 0 := six_form_vanishes_on_unit_sphere _
    (F (orbitProjection A)) (hunit ⟨orbitProjection A, orbitProjection_unit A⟩) v
    (fun i ↦ sphere_map_tangent F hF hunit A i)
  rw [hz] at h
  simpa only [joinHomotopy_fderiv_spatial F hF, Real.cos_pi_div_two, Real.sin_pi_div_two,
    one_smul, zero_smul, orbitProjection_apply, act_mul, generators_base,
    compContinuousLinearMap_apply, Function.comp_def, ContinuousLinearMap.inr_apply, v] using h

/-- The pulled-back third symplectic power along the join homotopy (named so that its
slice contractions can be rewritten by an explicit equation rather than by unfolding). -/
noncomputable def nueTheta (F : CV → CSpace 3) : ℝ × RM → (ℝ × RM) [⋀^Fin 6]→L[ℝ] ℝ :=
  fun p ↦ (cubeForm productSymplectic).compContinuousLinearMap (fderiv ℝ (joinHomotopy F) p)

lemma nue_slice (F : CV → CSpace 3) (t : ℝ) (A : O5) (v : Fin 5 → RM) :
    sliceContraction (nueTheta F) t A v =
      cubeForm productSymplectic (Matrix.vecCons (fderiv ℝ (joinHomotopy F) (t, A) (1, 0))
        (fun k ↦ fderiv ℝ (joinHomotopy F) (t, A) (0, v k))) := by
  simp only [sliceContraction, cylinderContraction_apply, nueTheta,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext k : 1
  refine Fin.cases ?_ (fun l ↦ ?_) k <;> simp

lemma nue_hv (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z)
    (t : ℝ) (A : O5) (i j : Fin 5) :
      sliceContraction (nueTheta F) t A
        (Matrix.vecCons ((A : RM) * (generators i.castSucc * generators j.succ -
          generators j.succ * generators i.castSucc))
          (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * generators k)))) = 0 := by
  have hsplit : ∀ (x : RM) (w : Fin 4 → RM),
      (fun k : Fin 5 ↦ fderiv ℝ (joinHomotopy F) (t, A) (0, Matrix.vecCons x w k)) =
        Matrix.vecCons (fderiv ℝ (joinHomotopy F) (t, A) (0, x))
          (fun k ↦ fderiv ℝ (joinHomotopy F) (t, A) (0, w k)) := by
    intro x w
    ext k : 1
    refine Fin.cases ?_ (fun l ↦ ?_) k <;> simp
  rw [nue_slice, hsplit, joinHomotopy_bracket F hF hphase]
  apply cubeForm_second_radical_on productSymplectic productSymplectic_skew
  · simp only [map_smul, _root_.smul_apply,
      joinHomotopy_time_tangent F hF hunit, smul_zero]
  · intro k
    simp only [map_smul, _root_.smul_apply, Fin.removeNth_apply]
    rw [joinHomotopy_spatial_tangent F hF hunit t A _ (generators_skew _), smul_zero]

/-- The concrete cup-length obstruction: there is no smooth circle-equivariant
map from the literal unit isotropic cone in C5 into the unit sphere in C3.
The obstruction is the nonzero third symplectic power. -/
theorem no_unit_equivariant_map (F : CV → CSpace 3) (hF : ContDiff ℝ ∞ F)
    (hunit : ∀ z : UnitQuadric, normSq 3 (F z) = 1)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → F (a • (z : CV)) = a • F z) :
    False := by
  have hΘ : ContDiff ℝ ∞ (nueTheta F) := contDiff_pullback_form contDiff_const
    ((joinHomotopy_contDiff F hF).fderiv_right (by simp))
  have hclosed (p : ℝ × RM) : extDeriv (nueTheta F) p = 0 :=
    pullback_constant_closed (cubeForm productSymplectic) (joinHomotopy F)
      (joinHomotopy_contDiff F hF) p
  have hi := haar_homotopy_invariant (nueTheta F) hΘ hclosed (nue_hv F hF hunit hphase) 0 (Real.pi / 2)
  have h0 (A : O5) : nueTheta F (0, A) (fun i ↦ (0, (A : RM) * generators i)) = 48 :=
    joinHomotopy_zero_cube F hF A
  have h1 (A : O5) : nueTheta F (Real.pi / 2, A) (fun i ↦ (0, (A : RM) * generators i)) = 0 :=
    joinHomotopy_half_pi_cube F hF hunit A
  simp_rw [h0, h1] at hi
  have hmass : 0 < (haar Set.univ).toReal := haar_mass_pos
  simp only [integral_const, smul_eq_mul, mul_zero] at hi
  change (haar Set.univ).toReal * 48 = 0 at hi
  nlinarith

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample
open CriticalBound

end ArnoldCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap
open ArnoldCounterexample.Forms ContinuousAlternatingMap
attribute [local instance] OAI.ArnoldCounterexample.CriticalBound.instTopologicalSpaceRM_5


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.no_unit_equivariant_map := @_root_.OAI.ArnoldCounterexample.CriticalBound.no_unit_equivariant_map
