-- Prove2me | solution 1 for LanglandsTunnell.archDerivAt_E_sub_Fm_eq_and_splitTorus_lowering_raising_relations_of_hasArchCharacterAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b3a6109d-0c67-5690-8f33-ee0f6b32a15d

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_AdelicVolume
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_AdelicTraceProducer
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_archDerivAt_E_sub_Fm_eq_and_splitTorus_lowering_raising_relations_of_hasArchCharacterAt

set_option autoImplicit false
open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

namespace MinimalWeightWhittaker
open IsDedekindDomain NumberField MeasureTheory Matrix NumberField.AdelicHaar NumberField.AdelicLevel
open NumberField.AdelicBox NumberField.InfinitePlace.Completion AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.SiegelCovering LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal
open NumberField.AdelicVolume
open scoped Real
section ArchimedeanDerivations
noncomputable section
open NumberField NumberField.InfinitePlace.Completion Matrix
variable {F : Type} [Field F] [NumberField F]

private def mulRightArrayCLM (A : Matrix (Fin 2) (Fin 2) ℝ) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun e => Matrix.of.symm (Matrix.of e * A)
      map_add' := by
        intro a b
        ext i j
        simp [Matrix.mul_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext i j
        simp [Matrix.mul_apply, mul_add, mul_assoc] }

private theorem mulRightArrayCLM_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2 → Fin 2 → ℝ) :
    mulRightArrayCLM A e = Matrix.of.symm (Matrix.of e * A) := rfl

private theorem isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F)
    {e : Fin 2 → Fin 2 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archDerivAt hw d φ (g * archRealLiftAt hw e) =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e (mulRightArrayCLM (archDirMatrix d) e) := by
  have hΦ := hφ g
  have hopen := isOpen_setOf_det_ne_zero
  have hdiff : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrix d 0 : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [of_symm_mul_archFlowMatrix_zero]
    exact ((hΦ.contDiffAt (hopen.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) =
      fun t : ℝ => φ (g * archRealLiftAt hw
        (Matrix.of.symm (Matrix.of e * (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ)))) := by
    funext t
    rw [archFlowAt, mul_assoc, archRealLiftAt_mul_archRealGLAt hw he]
  rw [mulRightArrayCLM_apply]
  show deriv (fun t : ℝ => φ (g * archRealLiftAt hw e * archFlowAt hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrix e d)).deriv

private theorem det_of_of_symm_one : (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))).det ≠ 0 := by
  rw [Equiv.apply_symm_apply, Matrix.det_one]
  exact one_ne_zero

private theorem isArchSmoothAt_archDerivAt_apply_eq_fderiv {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d φ g =
      fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (mulRightArrayCLM (archDirMatrix d) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ))) := by
  rw [← (isArchSmoothAt_archDerivAt_apply_mul_archRealLiftAt hφ) d g det_of_of_symm_one,
      archRealLiftAt_of_symm_one, mul_one]

private def rotationArray (θ : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![Real.cos θ, Real.sin θ], ![-Real.sin θ, Real.cos θ]]

private theorem of_rotationArray (θ : ℝ) :
    Matrix.of (rotationArray θ) = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

private theorem det_of_rotationArray (θ : ℝ) : (Matrix.of (rotationArray θ)).det ≠ 0 := by
  rw [of_rotationArray, Matrix.det_fin_two_of]
  nlinarith [Real.cos_sq_add_sin_sq θ]

private theorem rotationArray_zero : rotationArray 0 = Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationArray, Matrix.one_fin_two]

private theorem hasDerivAt_rotationArray :
    HasDerivAt rotationArray (![![0, 1], ![-1, 0]] : Fin 2 → Fin 2 → ℝ) 0 := by
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;> simp only [rotationArray] <;>
    first
      | simpa using Real.hasDerivAt_cos 0
      | simpa using Real.hasDerivAt_sin 0
      | (have h__af := (Real.hasDerivAt_sin 0).neg; simp at h__af; exact h__af)

private theorem archRealLiftAt_rotationArray {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    archRealLiftAt hw (rotationArray θ) = archRealGLAt hw (GL2Real.rotation θ) := by
  rw [archRealLiftAt_of_det_ne_zero hw (det_of_rotationArray θ)]
  rfl

private theorem rotation_mem_rowIsometrySubgroup₀ (θ : ℝ) : GL2Real.rotation θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  have hc : ((GL2Real.rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
    simp [GL2Real.rotation, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h1 : Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ = 1 := by
    linear_combination Real.cos_sq_add_sin_sq θ
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, Matrix.det_fin_two_of]
    exact h1
  · rw [hc, Matrix.det_fin_two_of, h1, norm_one]
  · intro x y
    rw [hc]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq θ

omit [NumberField F] in
private theorem norm_ringEquivRealOfIsReal_symm {w : InfinitePlace F} (hw : w.IsReal) (x : ℝ) :
    ‖(ringEquivRealOfIsReal hw).symm x‖ = ‖x‖ := by
  rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply]

private def rotationAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) : rowIsometrySubgroup₀ w.Completion :=
  rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw).symm (norm_ringEquivRealOfIsReal_symm hw)
    ⟨GL2Real.rotation θ, rotation_mem_rowIsometrySubgroup₀ θ⟩

private theorem archRealGLAt_rotation {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    archRealGLAt hw (GL2Real.rotation θ) =
      adelicArchGLInclAt F w ((rotationAt hw θ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) := rfl

omit [NumberField F] in

private theorem archWeightCharAt_one_rotationAt {w : InfinitePlace F} (hw : w.IsReal) (θ : ℝ) :
    ((archWeightCharAt hw 1 (rotationAt hw θ) : ℂˣ) : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := by
  have hentry : ∀ i j : Fin 2,
      ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw)
          (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (GL2Real.rotation θ)) : GL (Fin 2) ℝ) :
            Matrix (Fin 2) (Fin 2) ℝ) i j =
        ((GL2Real.rotation θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, RingEquiv.apply_symm_apply]
  show ((archWeightOneℝ (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      (rotationAt hw θ)) ^ (1 : ℤ) : ℂˣ) : ℂ) = _
  rw [zpow_one]
  show firstRowℂ _ = _
  unfold firstRowℂ
  refine Complex.ext ?_ ?_
  · exact hentry 0 0
  · exact hentry 0 1

end
end ArchimedeanDerivations
section SheetMatrices

private theorem splitTorusGL2_mul_unipotentGL2 (a x : ℝ) :
    splitTorusGL2 a * unipotentGL2 x = unipotentGL2 (Real.exp (2 * a) * x) * splitTorusGL2 a := by
  have h2a : Real.exp (2 * a) = Real.exp a * Real.exp a := by
    rw [← Real.exp_add]
    congr 1
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitTorusGL2, unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two, h2a, Real.exp_neg] <;>
    first | done | (field_simp; done) | (field_simp; ring1)

private theorem J_mul_unipotentGL2 (z : ℝ) :
    UpperHalfPlane.J * unipotentGL2 z = unipotentGL2 (-z) * UpperHalfPlane.J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipotentGL2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem one_mul_unipotentGL2_eq (z : ℝ) :
    (1 : GL (Fin 2) ℝ) * unipotentGL2 z = unipotentGL2 (1 * z) * 1 := by
  simp

private theorem J_mul_unipotentGL2_eq (z : ℝ) :
    UpperHalfPlane.J * unipotentGL2 z = unipotentGL2 (-1 * z) * UpperHalfPlane.J := by
  rw [neg_one_mul]
  exact J_mul_unipotentGL2 z

end SheetMatrices
section SheetFlows
variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem sheetDatum_mul_archFlowAt_H
    {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) {g : AdelicGL2 (𝓞 F) F}
    (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .H t
      = archRealGLAt hw (m * splitTorusGL2 (Real.log (y * Real.exp (2 * t)) / 2)) * g := by
  have hlog : Real.log (y * Real.exp (2 * t)) / 2 = Real.log y / 2 + t := by
    rw [Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  show archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archRealGLAt hw (splitTorusGL2 t) = _
  rw [mul_assoc, ← archRealGLAt_mul_comm_of_glArch_eq_one hw (splitTorusGL2 t) hg, ← mul_assoc,
    ← map_mul (archRealGLAt hw) (m * splitTorusGL2 (Real.log y / 2)) (splitTorusGL2 t), mul_assoc,
    ← splitTorusGL2_add, hlog]

private theorem sheetDatum_mul_archFlowAt_E {w : InfinitePlace F} (hw : w.IsReal) {m : GL (Fin 2) ℝ} {ε : ℝ}
    (hm : ∀ z : ℝ, m * unipotentGL2 z = unipotentGL2 (ε * z) * m) {g : AdelicGL2 (𝓞 F) F}
    (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .E x
      = archRealGLAt hw (unipotentGL2 (ε * (y * x))) * (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g) := by
  have hexp : Real.exp (2 * (Real.log y / 2)) = y := by
    rw [show 2 * (Real.log y / 2) = Real.log y by ring, Real.exp_log hy]
  show archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archRealGLAt hw (unipotentGL2 x) = _
  rw [mul_assoc, ← archRealGLAt_mul_comm_of_glArch_eq_one hw (unipotentGL2 x) hg, ← mul_assoc,
    ← map_mul (archRealGLAt hw) (m * splitTorusGL2 (Real.log y / 2)) (unipotentGL2 x), mul_assoc m,
    splitTorusGL2_mul_unipotentGL2, hexp, ← mul_assoc m, hm, mul_assoc,
    map_mul (archRealGLAt hw) (unipotentGL2 (ε * (y * x))) (m * splitTorusGL2 (Real.log y / 2)), mul_assoc]

end SheetFlows
section SheetValues
variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem archDerivAt_H_apply_sheetDatum {w : InfinitePlace F} (hw : w.IsReal) (W : AdelicGL2 (𝓞 F) F → ℂ)
    (m : GL (Fin 2) ℝ) {g : AdelicGL2 (𝓞 F) F} (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y)
    (hdiff : DifferentiableAt ℝ (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y) :
    archDerivAt hw .H W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)
      = 2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y := by
  show deriv (fun t : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .H t)) 0 = _
  have hflow : (fun t : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .H t))
      = fun t : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log (y * Real.exp (2 * t)) / 2)) * g) := by
    funext t
    rw [sheetDatum_mul_archFlowAt_H hw m hg hy t]
  rw [hflow]
  have hc : HasDerivAt (fun t : ℝ => y * Real.exp (2 * t)) (y * (Real.exp (2 * 0) * (2 * 1))) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).exp).const_mul y
  have hy0 : y * Real.exp (2 * 0) = y := by simp
  have hF₀ : HasDerivAt (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g))
      (deriv (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y)
      (y * Real.exp (2 * 0)) := by
    rw [hy0]
    exact hdiff.hasDerivAt
  have h2 := hF₀.scomp (0 : ℝ) hc
  have h3 : deriv (fun t : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log (y * Real.exp (2 * t)) / 2)) * g)) 0
      = (y * (Real.exp (2 * 0) * (2 * 1)))
        • deriv (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y :=
    h2.deriv
  rw [h3]
  simp only [mul_zero, Real.exp_zero, mul_one, one_mul, Complex.real_smul]
  push_cast
  ring

private theorem archDerivAt_E_apply_sheetDatum {w : InfinitePlace F} (hw : w.IsReal) (W : AdelicGL2 (𝓞 F) F → ℂ)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p)
    {m : GL (Fin 2) ℝ} {ε : ℝ} (hm : ∀ z : ℝ, m * unipotentGL2 z = unipotentGL2 (ε * z) * m) {g : AdelicGL2 (𝓞 F) F}
    (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y) :
    archDerivAt hw .E W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)
      = 2 * (Real.pi : ℂ) * Complex.I * ((ε * y : ℝ) : ℂ)
          * W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g) := by
  show deriv (fun x : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .E x)) 0 = _
  have hflow : (fun x : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g * archFlowAt hw .E x))
      = fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (y * x) : ℝ) : ℂ))
          * W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g) := by
    funext x
    rw [sheetDatum_mul_archFlowAt_E hw hm hg hy x, hWψ]
  rw [hflow]
  have h1 : HasDerivAt (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((ε * (y * x) : ℝ) : ℂ)))
      (Complex.exp (2 * Real.pi * Complex.I * ((ε * (y * 0) : ℝ) : ℂ))
        * (2 * Real.pi * Complex.I * ((ε * (y * 1) : ℝ) : ℂ))) 0 :=
    (((((hasDerivAt_id' (0 : ℝ)).const_mul y).const_mul ε).ofReal_comp).const_mul
      (2 * (Real.pi : ℂ) * Complex.I)).cexp
  rw [(h1.mul_const (W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g))).deriv]
  simp

end SheetValues
section SheetAlgebra

private theorem two_mul_deriv_sub_eq_zero_of_J_sheet_lowering (DH DE DF Wh f' fy : ℂ) (y : ℝ) (k : ℤ)
    (hlow : DH - Complex.I * (DE + DF) = 0)
    (hE : DE = 2 * (Real.pi : ℂ) * Complex.I * ((-1 * y : ℝ) : ℂ) * Wh)
    (hwt : DE - DF = (k : ℂ) * Complex.I * Wh) (hH : DH = 2 * (y : ℂ) * f') (hWh : Wh = fy) :
    2 * (y : ℂ) * f' - (4 * (Real.pi : ℂ) * (y : ℂ) + (k : ℂ)) * fy = 0 := by
  rw [hWh] at hE hwt
  push_cast at hE
  have hDF : DF = DE - (k : ℂ) * Complex.I * fy := by linear_combination -hwt
  rw [hH, hDF, hE] at hlow
  linear_combination hlow - (4 * (Real.pi : ℂ) * (y : ℂ) + (k : ℂ)) * fy * Complex.I_mul_I

end SheetAlgebra
section WeightValue
variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem archWeightCharAt_rotationAt_eq_exp {w : InfinitePlace F} (hw : w.IsReal) (k : ℤ) (θ : ℝ) :
    ((archWeightCharAt hw k (rotationAt hw θ) : ℂˣ) : ℂ) = Complex.exp ((k : ℂ) * ((θ : ℂ) * Complex.I)) := by
  have h1 : ((archWeightCharAt hw k (rotationAt hw θ) : ℂˣ) : ℂ)
      = ((archWeightCharAt hw 1 (rotationAt hw θ) : ℂˣ) : ℂ) ^ k := by
    show ((archWeightOneAt hw (rotationAt hw θ) ^ k : ℂˣ) : ℂ)
      = ((archWeightOneAt hw (rotationAt hw θ) ^ (1 : ℤ) : ℂˣ) : ℂ) ^ k
    rw [zpow_one, Units.val_zpow_eq_zpow_val]
  have h2 : (⟨Real.cos θ, Real.sin θ⟩ : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) :=
    Complex.ext (Complex.exp_ofReal_mul_I_re θ).symm (Complex.exp_ofReal_mul_I_im θ).symm
  rw [h1, archWeightCharAt_one_rotationAt, h2, ← Complex.exp_int_mul]

private theorem archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ {w : InfinitePlace F} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAt hw φ) (k : ℤ)
    (hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw k) φ) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw .E φ g - archDerivAt hw .Fm φ g = (k : ℂ) * Complex.I * φ g := by
  have hopen := isOpen_setOf_det_ne_zero
  have hcurve : (fun θ : ℝ => φ (g * archRealLiftAt hw (rotationArray θ))) =
      fun θ : ℝ => Complex.exp ((k : ℂ) * ((θ : ℂ) * Complex.I)) * φ g := by
    funext θ
    rw [archRealLiftAt_rotationArray, archRealGLAt_rotation, hwt (rotationAt hw θ) g,
      archWeightCharAt_rotationAt_eq_exp]
  have hder : HasDerivAt (fun θ : ℝ => Complex.exp ((k : ℂ) * ((θ : ℂ) * Complex.I)) * φ g)
      ((k : ℂ) * Complex.I * φ g) 0 := by
    have h2 := ((((hasDerivAt_id' (0 : ℝ)).ofReal_comp).mul_const Complex.I).const_mul (k : ℂ)).cexp.mul_const (φ g)
    simpa using h2
  have hΦ : HasFDerivAt (fun e' => φ (g * archRealLiftAt hw e'))
      (fderiv ℝ (fun e' => φ (g * archRealLiftAt hw e')) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      (rotationArray 0) := by
    rw [rotationArray_zero]
    exact (((hφ g).contDiffAt (hopen.mem_nhds det_of_of_symm_one)).differentiableAt (by simp)).hasFDerivAt
  have hchain := hΦ.comp_hasDerivAt (0 : ℝ) hasDerivAt_rotationArray
  have hdir : mulRightArrayCLM (archDirMatrix .E) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) -
      mulRightArrayCLM (archDirMatrix .Fm) (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        (![![0, 1], ![-1, 0]] : Fin 2 → Fin 2 → ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [mulRightArrayCLM_apply, archDirMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.of_symm_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one]
  rw [isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ .E g, isArchSmoothAt_archDerivAt_apply_eq_fderiv hφ .Fm g,
    ← _root_.map_sub, hdir]
  have hcomp : (fun e' => φ (g * archRealLiftAt hw e')) ∘ rotationArray =
      fun θ : ℝ => Complex.exp ((k : ℂ) * ((θ : ℂ) * Complex.I)) * φ g := hcurve
  rw [hcomp] at hchain
  exact hchain.unique hder

end WeightValue
section PositiveSheetAlgebra

private theorem two_mul_deriv_add_eq_zero_of_one_sheet_lowering (DH DE DF Wh f' fy : ℂ) (y : ℝ) (k : ℤ)
    (hlow : DH - Complex.I * (DE + DF) = 0)
    (hE : DE = 2 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * Wh)
    (hwt : DE - DF = (k : ℂ) * Complex.I * Wh) (hH : DH = 2 * (y : ℂ) * f') (hWh : Wh = fy) :
    2 * (y : ℂ) * f' + (4 * (Real.pi : ℂ) * (y : ℂ) - (k : ℂ)) * fy = 0 := by
  rw [hWh] at hE hwt
  have hDF : DF = DE - (k : ℂ) * Complex.I * fy := by linear_combination -hwt
  rw [hH, hDF, hE] at hlow
  linear_combination hlow + (4 * (Real.pi : ℂ) * (y : ℂ) - (k : ℂ)) * fy * Complex.I_mul_I

end PositiveSheetAlgebra
section SheetRelations
variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem one_sheet_lowering_relation {w : InfinitePlace F} (hw : w.IsReal) {W : AdelicGL2 (𝓞 F) F → ℂ}
    (hWsm : IsArchSmoothAt hw W) {k : ℤ} (hWk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) W)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p)
    (hlowW : ∀ p : AdelicGL2 (𝓞 F) F,
      archDerivAt hw .H W p - Complex.I * (archDerivAt hw .E W p + archDerivAt hw .Fm W p) = 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : AdelicLevel.glArch (𝓞 F) F g = 1)
    (hf : DifferentiableOn ℝ (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) (Set.Ioi 0))
    {y : ℝ} (hy : 0 < y) :
    2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) y
        + (4 * (Real.pi : ℂ) * (y : ℂ) - (k : ℂ)) * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0 := by
  have hdiff : DifferentiableAt ℝ
      (fun z : ℝ => W (archRealGLAt hw ((1 : GL (Fin 2) ℝ) * splitTorusGL2 (Real.log z / 2)) * g)) y := by
    simpa only [one_mul] using hf.differentiableAt (Ioi_mem_nhds hy)
  have hH := archDerivAt_H_apply_sheetDatum hw W 1 hg hy hdiff
  have hE := archDerivAt_E_apply_sheetDatum hw W hWψ one_mul_unipotentGL2_eq hg hy
  simp only [one_mul] at hH hE
  exact two_mul_deriv_add_eq_zero_of_one_sheet_lowering _ _ _ _ _ _ y k (hlowW _) hE
    (archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ hWsm k hWk _) hH rfl

private theorem J_sheet_lowering_relation {w : InfinitePlace F} (hw : w.IsReal) {W : AdelicGL2 (𝓞 F) F → ℂ}
    (hWsm : IsArchSmoothAt hw W) {k : ℤ} (hWk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) W)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p)
    (hlowW : ∀ p : AdelicGL2 (𝓞 F) F,
      archDerivAt hw .H W p - Complex.I * (archDerivAt hw .E W p + archDerivAt hw .Fm W p) = 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : AdelicLevel.glArch (𝓞 F) F g = 1)
    (hfJ : DifferentiableOn ℝ
      (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) (Set.Ioi 0))
    {y : ℝ} (hy : 0 < y) :
    2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y
        - (4 * (Real.pi : ℂ) * (y : ℂ) + (k : ℂ))
            * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0 :=
  two_mul_deriv_sub_eq_zero_of_J_sheet_lowering _ _ _ _ _ _ y k (hlowW _)
    (archDerivAt_E_apply_sheetDatum hw W hWψ J_mul_unipotentGL2_eq hg hy)
    (archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ hWsm k hWk _)
    (archDerivAt_H_apply_sheetDatum hw W UpperHalfPlane.J hg hy (hfJ.differentiableAt (Ioi_mem_nhds hy))) rfl

end SheetRelations
section RaisedSheetValues
variable (F : Type) [Field F] [NumberField F]
variable {F}

private theorem archRaise_expression_apply_sheetDatum {w : InfinitePlace F} (hw : w.IsReal) (W : AdelicGL2 (𝓞 F) F → ℂ)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p)
    (hDFm : ∀ p, archDerivAt hw .Fm W p = archDerivAt hw .E W p)
    {m : GL (Fin 2) ℝ} {ε : ℝ} (hm : ∀ z : ℝ, m * unipotentGL2 z = unipotentGL2 (ε * z) * m) {g : AdelicGL2 (𝓞 F) F}
    (hg : AdelicLevel.glArch (𝓞 F) F g = 1) {y : ℝ} (hy : 0 < y)
    (hdiff : DifferentiableAt ℝ (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y) :
    archDerivAt hw .H W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)
        + Complex.I * (archDerivAt hw .E W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)
          + archDerivAt hw .Fm W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g))
      = 2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (m * splitTorusGL2 (Real.log z / 2)) * g)) y
          - 4 * (Real.pi : ℂ) * ((ε * y : ℝ) : ℂ)
              * W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g) := by
  rw [hDFm, archDerivAt_H_apply_sheetDatum hw W m hg hy hdiff, archDerivAt_E_apply_sheetDatum hw W hWψ hm hg hy]
  linear_combination (4 * (Real.pi : ℂ) * ((ε * y : ℝ) : ℂ)
    * W (archRealGLAt hw (m * splitTorusGL2 (Real.log y / 2)) * g)) * Complex.I_sq

end RaisedSheetValues
end MinimalWeightWhittaker

open MinimalWeightWhittaker in
theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (W : AdelicGL2 (𝓞 F) F → ℂ) (hWsm : IsArchSmoothAt hw W) (k : ℤ)
    (hWk : HasArchCharacterAt₀ F w (archWeightCharAt hw k) W)
    (hWψ : ∀ (x : ℝ) (p : AdelicGL2 (𝓞 F) F),
      W (archRealGLAt hw (unipotentGL2 x) * p) = Complex.exp (2 * Real.pi * Complex.I * x) * W p) :

    (∀ g : AdelicGL2 (𝓞 F) F,
      archDerivAt hw ArchDir.E W g - archDerivAt hw ArchDir.Fm W g = (k : ℂ) * Complex.I * W g) ∧

    ((∀ p : AdelicGL2 (𝓞 F) F,
        archDerivAt hw ArchDir.H W p
          - Complex.I * (archDerivAt hw ArchDir.E W p + archDerivAt hw ArchDir.Fm W p) = 0) →
      ∀ g : AdelicGL2 (𝓞 F) F, g ∈ finiteAdelicGL2Subgroup F →
        (DifferentiableOn ℝ (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) (Set.Ioi 0) →
          ∀ y : ℝ, 0 < y →
            2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) y
              + (4 * (Real.pi : ℂ) * (y : ℂ) - (k : ℂ))
                  * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0) ∧
        (DifferentiableOn ℝ
            (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) (Set.Ioi 0) →
          ∀ y : ℝ, 0 < y →
            2 * (y : ℂ) * deriv
                (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y
              - (4 * (Real.pi : ℂ) * (y : ℂ) + (k : ℂ))
                  * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0)) ∧

    ((∀ p : AdelicGL2 (𝓞 F) F, archDerivAt hw ArchDir.Fm W p = archDerivAt hw ArchDir.E W p) →
      ∀ g : AdelicGL2 (𝓞 F) F, g ∈ finiteAdelicGL2Subgroup F → ∀ y : ℝ, 0 < y →
        (DifferentiableAt ℝ (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) y →
          archDerivAt hw ArchDir.H W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
              + Complex.I * (archDerivAt hw ArchDir.E W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
                + archDerivAt hw ArchDir.Fm W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))
            = 2 * (y : ℂ) * deriv (fun z : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)) y
                - 4 * (Real.pi : ℂ) * (y : ℂ) * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) ∧
        (DifferentiableAt ℝ
            (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y →
          archDerivAt hw ArchDir.H W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)
              + Complex.I
                * (archDerivAt hw ArchDir.E W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)
                  + archDerivAt hw ArchDir.Fm W
                      (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))
            = 2 * (y : ℂ) * deriv
                  (fun z : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)) y
                - 4 * (Real.pi : ℂ) * ((-1 * y : ℝ) : ℂ)
                    * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) := by
  refine ⟨fun g => archDerivAt_E_sub_Fm_apply_of_hasArchCharacterAt₀ hWsm k hWk g, ?_, ?_⟩
  · intro hlowW g hg
    exact ⟨fun hf y hy => one_sheet_lowering_relation hw hWsm hWk hWψ hlowW hg hf hy,
      fun hfJ y hy => J_sheet_lowering_relation hw hWsm hWk hWψ hlowW hg hfJ hy⟩
  · intro hDFm g hg y hy
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · have e := archRaise_expression_apply_sheetDatum hw W hWψ hDFm one_mul_unipotentGL2_eq hg hy
        (by simpa only [one_mul] using hd)
      simpa only [one_mul] using e
    · exact archRaise_expression_apply_sheetDatum hw W hWψ hDFm J_mul_unipotentGL2_eq hg hy hd

end S_LanglandsTunnell_archDerivAt_E_sub_Fm_eq_and_splitTorus_lowering_raising_relations_of_hasArchCharacterAt
end P2MW
export P2MW.S_LanglandsTunnell_archDerivAt_E_sub_Fm_eq_and_splitTorus_lowering_raising_relations_of_hasArchCharacterAt (solution)
