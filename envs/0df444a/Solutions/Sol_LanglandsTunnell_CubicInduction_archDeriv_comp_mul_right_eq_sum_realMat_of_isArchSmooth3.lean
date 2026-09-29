-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/34d30b7d-d646-51c5-a424-72a47f563b84

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_archRealLift3_mul_eq_mul_archRealLift3_conj
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_archRealLift3_one_and_ideleNorm_det_archRealLift3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete HeckePair.instSMulCommClassSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instAlgebraSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instOneSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instIsScalarTowerSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instRingSubtypeForallMemSubmoduleHeckeAlgebra HeckePair.instMulSubtypeForallMemSubmoduleHeckeAlgebra FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one HeckePair.convTerm_mk HeckePair.coe_apply_add HeckePair.coe_apply_smul FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add"

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Topology Filter
open LanglandsTunnell.CubicInduction

namespace WsF
namespace CA

abbrev E33 : Type := Fin 3 → Fin 3 → ℝ
abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ

def RM (k : G3) : Matrix (Fin 3) (Fin 3) ℝ := AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ k)

def one33 : E33 := fun a b => if a = b then 1 else 0
def E1 (a b : Fin 3) : E33 := fun a' b' => if a' = a ∧ b' = b then 1 else 0
def uni (i j : Fin 3) (s : ℝ) : E33 := fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

theorem archDeriv_def (i j : Fin 3) (ψ : G3 → ℂ) (g : G3) :
    WhittakerBlock.archDeriv i j ψ g = deriv (fun s : ℝ => ψ (g * WhittakerBlock.archRealLift3 (uni i j s))) 0 := rfl

theorem of_one33 : Matrix.of one33 = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext a b; simp [one33, Matrix.one_apply]

theorem of_uni (i j : Fin 3) (s : ℝ) : Matrix.of (uni i j s) = 1 + s • Matrix.of (E1 i j) := by
  ext a b
  simp only [uni, E1, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]

theorem lift_one33 : WhittakerBlock.archRealLift3 one33 = 1 :=
  LanglandsTunnell.CubicInduction.WhittakerBlock.archRealLift3_one_and_ideleNorm_det_archRealLift3.1

theorem det_one33 : (Matrix.of one33).det ≠ 0 := by
  rw [of_one33, Matrix.det_one]; exact one_ne_zero

theorem continuous_uni (i j : Fin 3) : Continuous (uni i j) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  show Continuous fun s : ℝ => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0
  by_cases h : a = i ∧ b = j
  · simp only [h, and_self, if_true]; exact continuous_const.add continuous_id
  · simp only [h, if_false]; exact continuous_const

theorem eventually_det_uni (i j : Fin 3) : ∀ᶠ s in 𝓝 (0 : ℝ), (Matrix.of (uni i j s)).det ≠ 0 := by
  have hc : Continuous fun s : ℝ => (Matrix.of (uni i j s)).det :=
    ((continuous_uni i j : Continuous fun s => (Matrix.of (uni i j s) : Matrix (Fin 3) (Fin 3) ℝ))).matrix_det
  have h0 : (Matrix.of (uni i j 0)).det ≠ 0 := by
    rw [of_uni, zero_smul, add_zero, Matrix.det_one]; exact one_ne_zero
  exact hc.continuousAt.eventually_ne h0

def Dir (R : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) : E33 := fun a b => (R⁻¹ * Matrix.of (E1 i j) * R) a b

theorem Dir_apply (R : Matrix (Fin 3) (Fin 3) ℝ) (i j a b : Fin 3) : Dir R i j a b = R⁻¹ a i * R j b := by
  unfold Dir
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, E1]
  rw [Fintype.sum_eq_single j (fun d hd => by simp [hd])]
  rw [Fintype.sum_eq_single i (fun c hc => by simp [hc])]
  simp

theorem conj_uni (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.det ≠ 0) (i j : Fin 3) (s : ℝ) :
    (fun a b => (R⁻¹ * Matrix.of (uni i j s) * R) a b) = one33 + s • Dir R i j := by
  have hRR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (isUnit_iff_ne_zero.mpr hR)
  funext a b
  rw [of_uni, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hRR, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    one33, Dir]

theorem Dir_eq_sum (R : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    Dir R i j = ∑ a : Fin 3, ∑ b : Fin 3, Dir R i j a b • E1 a b := by
  funext a' b'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, E1, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_eq_single a' (fun a ha => by simp [Ne.symm ha])]
  rw [Fintype.sum_eq_single b' (fun b hb => by simp [Ne.symm hb])]
  simp

theorem dir_one33 (a b : Fin 3) : (fun a' b' : Fin 3 => if b' = b then one33 a' a else 0) = E1 a b := by
  funext a' b'
  simp only [one33, E1]
  by_cases h1 : b' = b <;> by_cases h2 : a' = a <;> simp [h1, h2]

theorem archDeriv_translate (φ : G3 → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (k : G3) (i j : Fin 3) (g : G3) :
    WhittakerBlock.archDeriv i j (fun x => φ (x * k)) g =
      ∑ a : Fin 3, ∑ b : Fin 3, ((RM k)⁻¹ a i * RM k j b : ℝ) • WhittakerBlock.archDeriv a b φ (g * k) := by

  set F : E33 → ℂ := fun e => φ (g * k * WhittakerBlock.archRealLift3 e) with hF
  have hS : IsOpen {e : E33 | (Matrix.of e).det ≠ 0} :=
    isOpen_ne.preimage (Continuous.matrix_det (continuous_matrix fun a b =>
      (continuous_apply b).comp (continuous_apply a)))
  have hFdiff : DifferentiableAt ℝ F one33 :=
    (((contDiffOn_infty_iff_fderiv_of_isOpen hS).1 (hφ (g * k))).1 one33 det_one33).differentiableAt
      (hS.mem_nhds det_one33)
  have hRdet : (RM k).det ≠ 0 :=
    (LanglandsTunnell.CubicInduction.archRealLift3_mul_eq_mul_archRealLift3_conj k one33 det_one33).1

  have hev : (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 (uni i j s) * k)) =ᶠ[𝓝 0]
      fun s : ℝ => F (one33 + s • Dir (RM k) i j) := by
    filter_upwards [eventually_det_uni i j] with s hs
    have hc := (LanglandsTunnell.CubicInduction.archRealLift3_mul_eq_mul_archRealLift3_conj k (uni i j s) hs).2
    show φ (g * WhittakerBlock.archRealLift3 (uni i j s) * k) =
      φ (g * k * WhittakerBlock.archRealLift3 (one33 + s • Dir (RM k) i j))
    rw [mul_assoc, hc, ← mul_assoc, ← conj_uni (RM k) hRdet i j s]
    rfl
  rw [archDeriv_def]
  show deriv (fun s : ℝ => φ (g * WhittakerBlock.archRealLift3 (uni i j s) * k)) 0 = _
  rw [hev.deriv_eq]

  have hl : HasDerivAt (fun s : ℝ => one33 + s • Dir (RM k) i j) (Dir (RM k) i j) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (Dir (RM k) i j)).const_add one33
    rwa [one_smul] at this
  have hcomp : HasDerivAt (fun s : ℝ => F (one33 + s • Dir (RM k) i j)) (fderiv ℝ F one33 (Dir (RM k) i j)) 0 := by
    have h0 : one33 + (0 : ℝ) • Dir (RM k) i j = one33 := by simp
    have hFd : HasFDerivAt F (fderiv ℝ F one33) (one33 + (0 : ℝ) • Dir (RM k) i j) := by
      rw [h0]; exact hFdiff.hasFDerivAt
    exact hFd.comp_hasDerivAt (0 : ℝ) hl
  rw [hcomp.deriv]

  rw [Dir_eq_sum, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_smul, Dir_apply]
  congr 1
  have h := WhittakerBlock.archDeriv_eq_fderiv hφ a b (g * k) det_one33
  rw [lift_one33, mul_one, dir_one33] at h
  exact h.symm

theorem isArchSmooth3_translate (φ : G3 → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (k : G3) :
    WhittakerBlock.IsArchSmooth3 (fun x => φ (x * k)) := by
  intro g
  have hRdet : (RM k).det ≠ 0 :=
    (LanglandsTunnell.CubicInduction.archRealLift3_mul_eq_mul_archRealLift3_conj k one33 det_one33).1

  let C : E33 → E33 := fun e a b => ((RM k)⁻¹ * Matrix.of e * RM k) a b
  have hC : ContDiff ℝ (⊤ : ℕ∞) C := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    show ContDiff ℝ (⊤ : ℕ∞) fun e : E33 => ((RM k)⁻¹ * Matrix.of e * RM k) a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    refine ContDiff.sum fun d _ => ContDiff.mul (ContDiff.sum fun c _ => ?_) contDiff_const
    exact contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id c) d)
  have hCmaps : Set.MapsTo C {e : E33 | (Matrix.of e).det ≠ 0} {e : E33 | (Matrix.of e).det ≠ 0} := by
    intro e he
    have hRR : (RM k)⁻¹ * RM k = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hRdet)
    have hCe : Matrix.of (C e) = (RM k)⁻¹ * Matrix.of e * RM k := by ext a b; rfl
    show (Matrix.of (C e)).det ≠ 0
    rw [hCe, Matrix.det_mul, Matrix.det_mul, mul_assoc, mul_comm (Matrix.of e).det, ← mul_assoc, ← Matrix.det_mul,
      hRR, Matrix.det_one, one_mul]
    exact he
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * k * WhittakerBlock.archRealLift3 (C e)))
      {e : E33 | (Matrix.of e).det ≠ 0} :=
    (hφ (g * k)).comp hC.contDiffOn (fun e he => hCmaps he)
  refine hcomp.congr (fun e he => ?_)
  have hc := (LanglandsTunnell.CubicInduction.archRealLift3_mul_eq_mul_archRealLift3_conj k e he).2
  show φ (g * WhittakerBlock.archRealLift3 e * k) = φ (g * k * WhittakerBlock.archRealLift3 (C e))
  rw [mul_assoc, hc, ← mul_assoc]
  rfl

end WsF.CA

open WsF.CA in
theorem solution
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (k : AdelicGL 3 (𝓞 ℚ) ℚ)
    (i j : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j (fun x => φ (x * k)) g =
      ∑ a : Fin 3, ∑ b : Fin 3,
        (((AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ k))⁻¹ a i *
            AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ k) j b : ℝ) : ℂ) *
          WhittakerBlock.archDeriv a b φ (g * k) := by
  rw [archDeriv_translate φ hφ k i j g]
  simp only [Complex.real_smul]
  rfl

end
end S_LanglandsTunnell_CubicInduction_archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3 (solution)
