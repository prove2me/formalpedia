-- Prove2me | solution 1 for GlobalTheory.KSp.map_linearEquiv_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:26:03.525928+00:00
-- url     : https://prove2.me/submissions/5bcaab9d-cbdb-4f61-bd25-eb2beeaf543e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapLinearEquivAddHaarLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_WeilM_smul_map_mulVec_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped NNReal ENNReal
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (T : V ≃ₗ[F] V), μ.map T = (distribHaarChar F (LinearEquiv.det T))⁻¹ • μ := by
  intro F _ _ _ _ _ V _ _ _ _ _ _ _ μ _ T
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable F
  haveI := GlobalTheory.SplitWeil.t2Space F
  set n := Module.finrank F V
  set b := Module.finBasis F V
  set e : V ≃ₗ[F] (Fin n → F) := b.equivFun
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup F V
  have hec : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap

  let E : V ≃L[F] (Fin n → F) := { e with continuous_toFun := hec, continuous_invFun := hes }
  let Em : V ≃ᵐ (Fin n → F) := E.toHomeomorph.toMeasurableEquiv
  have hEm : (Em : V → Fin n → F) = e := rfl
  have hEms : (Em.symm : (Fin n → F) → V) = e.symm := rfl
  let P : Measure (Fin n → F) := Measure.pi fun _ => (Measure.addHaar : Measure F)
  set X := μ.map Em with hX
  haveI : X.IsAddHaarMeasure := E.isAddHaarMeasure_map μ
  set M := LinearMap.toMatrix b b T.toLinearMap
  have hM : ∀ y, M.mulVec (e y) = e (T y) := fun y => by
    simp [M, e, LinearMap.toMatrix_mulVec_repr]
  have hdet : ((LinearEquiv.det T : Fˣ) : F) = M.det := by
    simp [M, LinearMap.det_toMatrix]
  set d := distribHaarChar F (LinearEquiv.det T)
  have key : (d : ℝ≥0∞) • P.map M.mulVec = P :=
    GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure F) M (LinearEquiv.det T) hdet
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by simpa using (distribHaarChar_pos (A := F) (g := LinearEquiv.det T)).ne'
  have hPM : P.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • P := by
    conv_rhs => rw [← key]
    rw [smul_smul, ENNReal.coe_inv (by simpa using hd0), ENNReal.inv_mul_cancel hd0 ENNReal.coe_ne_top,
      one_smul]
  have hXP : X = (Measure.addHaarScalarFactor X P : ℝ≥0∞) • P := Measure.isAddLeftInvariant_eq_smul X P
  have hmv : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hXM : X.map M.mulVec = ((d⁻¹ : ℝ≥0) : ℝ≥0∞) • X := by
    rw [hXP, Measure.map_smul, hPM, smul_comm]
  have hμ : μ = X.map Em.symm := by rw [hX, Measure.map_map Em.symm.measurable Em.measurable]; simp
  have hcomp : (T : V → V) ∘ Em.symm = Em.symm ∘ M.mulVec := by
    funext x
    show T (e.symm x) = e.symm (M.mulVec x)
    apply e.injective
    rw [← hM, e.apply_symm_apply, e.apply_symm_apply]
  have hTm : Measurable (T : V → V) := by
    have : Continuous (T : V → V) := IsModuleTopology.continuous_of_linearMap T.toLinearMap
    exact this.measurable
  calc μ.map T = (X.map Em.symm).map T := by rw [← hμ]
    _ = X.map ((T : V → V) ∘ Em.symm) := Measure.map_map hTm Em.symm.measurable
    _ = X.map (Em.symm ∘ M.mulVec) := by rw [hcomp]
    _ = (X.map M.mulVec).map Em.symm := (Measure.map_map Em.symm.measurable hmv).symm
    _ = (d⁻¹ : ℝ≥0) • μ := by rw [hXM, Measure.map_smul, ← hμ]; rfl
end GlobalTheory.KSp
