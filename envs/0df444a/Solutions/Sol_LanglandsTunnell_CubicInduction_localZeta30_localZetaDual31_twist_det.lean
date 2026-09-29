-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.localZeta30_localZetaDual31_twist_det
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b427d606-f2e2-50b6-8f8e-51c5539286c1

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_localZeta30_localZetaDual31_twist_det

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

namespace TwistZetaSol

open Matrix

section Dets
variable {A : Type*} [CommRing A]

theorem det_embedMat2 (M : Matrix (Fin 2) (Fin 2) A) : (embedMat2 M).det = M.det := by
  simp [embedMat2, Matrix.det_fin_three, Matrix.det_fin_two]

theorem det_iotaGL (h : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.det (iotaGL h) = Matrix.GeneralLinearGroup.det h := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, coe_iotaGL, det_embedMat2]

theorem det_diagUnitGL2 (a : Aˣ) : Matrix.GeneralLinearGroup.det (diagUnitGL2 a) = a := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, coe_diagUnitGL2, Matrix.det_fin_two]

theorem det_iotaGL_diagUnitGL2 (a : Aˣ) : Matrix.GeneralLinearGroup.det (iotaGL (diagUnitGL2 a)) = a := by
  rw [det_iotaGL, det_diagUnitGL2]

theorem det_lowerUnipotent21 (x : A) : Matrix.GeneralLinearGroup.det (lowerUnipotent21 x) = 1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, lowerUnipotent21_coe, Matrix.det_fin_three]

theorem det_longWeyl3 : Matrix.GeneralLinearGroup.det (longWeyl3 : GL (Fin 3) A) = -1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, longWeyl3_coe, Matrix.det_fin_three]

theorem det_weylPrime3 : Matrix.GeneralLinearGroup.det (weylPrime3 : GL (Fin 3) A) = -1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, weylPrime3_coe, Matrix.det_fin_three]

theorem det_transposeInv3 (g : GL (Fin 3) A) :
    Matrix.GeneralLinearGroup.det (transposeInv3 g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_one]
  change (((g⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ * (g : Matrix (Fin 3) (Fin 3) A)).det = 1
  rw [Matrix.det_mul, Matrix.det_transpose, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.det_one]

theorem cg_identity {G : Type*} [CommGroup G] (d' a d : G) : d' * (a * 1 * (d' * d⁻¹))⁻¹ = a⁻¹ * d := by
  rw [mul_one, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_comm d d'⁻¹, mul_assoc d'⁻¹ d a⁻¹,
    mul_inv_cancel_left, mul_comm]

theorem det_dual_arg (a : Aˣ) (x : A) (g : GL (Fin 3) A) :
    Matrix.GeneralLinearGroup.det (longWeyl3 * transposeInv3 (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x *
      (weylPrime3 * transposeInv3 g))) = a⁻¹ * Matrix.GeneralLinearGroup.det g := by
  have hw : Matrix.GeneralLinearGroup.det (longWeyl3 : GL (Fin 3) A) =
      Matrix.GeneralLinearGroup.det (weylPrime3 : GL (Fin 3) A) := by rw [det_longWeyl3, det_weylPrime3]
  simp only [map_mul, det_transposeInv3, det_iotaGL_diagUnitGL2, det_lowerUnipotent21]
  rw [hw]
  exact cg_identity _ _ _

end Dets

end TwistZetaSol

open TwistZetaSol in
theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ))
    {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mA : MeasurableSpace (v.adicCompletion ℚ)}
    (m : Measure (v.adicCompletion ℚ)ˣ) (m₁ : Measure (v.adicCompletion ℚ))
    (W : LocalGL3 v → ℂ) (χv η : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) :
    (∀ s : ℂ, localZeta30 v m (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) η s g =
        ((χv (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * localZeta30 v m W (η * χv) s g) ∧
    (∀ σ₀ : ℝ, IsLocalZeta30ConvergentAbove v m (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) η g σ₀ ↔
        IsLocalZeta30ConvergentAbove v m W (η * χv) g σ₀) ∧
    (∀ s : ℂ, localZetaDual31 v m m₁ (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x) η s g =
        ((χv (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * localZetaDual31 v m m₁ W (η * χv) s g) ∧
    (∀ σ₁ : ℝ,
      IsLocalZeta31ConvergentAbove v m m₁ (dualWhittakerFn3 (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)) η⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ↔
        IsLocalZeta31ConvergentAbove v m m₁ (dualWhittakerFn3 W) (η * χv)⁻¹ (weylPrime3 * transposeInv3 g) σ₁) := by
  set c : ℂ := ((χv (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) with hc
  have hcU : IsUnit c := ⟨(χv (Matrix.GeneralLinearGroup.det g) : ℂˣ), rfl⟩

  have hmain : ∀ s : ℂ, (fun a : (v.adicCompletion ℚ)ˣ =>
      (((χv (Matrix.GeneralLinearGroup.det (iotaGL (diagUnitGL2 a) * g)) : ℂˣ) : ℂ) * W (iotaGL (diagUnitGL2 a) * g)) *
        ((η a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun a => c * (W (iotaGL (diagUnitGL2 a) * g) * (((η * χv) a : ℂˣ) : ℂ) *
        ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    intro s; funext a
    simp only [map_mul, det_iotaGL_diagUnitGL2, MonoidHom.mul_apply, Units.val_mul, hc]
    ring

  have hdual : ∀ s : ℂ, (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      dualWhittakerFn3 (fun x : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W x)
          (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 g)) *
        ((η⁻¹ p.1 : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) =
      fun p => c * (dualWhittakerFn3 W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * (weylPrime3 * transposeInv3 g)) *
        (((η * χv)⁻¹ p.1 : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
    intro s; funext p
    rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, det_dual_arg]
    simp only [map_mul, map_inv, MonoidHom.inv_apply, MonoidHom.mul_apply, mul_inv, Units.val_mul,
      Units.val_inv_eq_inv_val, hc]
    ring
  refine ⟨fun s => ?_, fun σ₀ => ?_, fun s => ?_, fun σ₁ => ?_⟩
  ·
    simp only [localZeta30]
    rw [hmain s, integral_const_mul]
  ·
    simp only [IsLocalZeta30ConvergentAbove]
    refine forall_congr' fun s => forall_congr' fun _ => ?_
    rw [hmain s]
    exact integrable_const_mul_iff hcU _
  ·
    simp only [localZetaDual31, localZeta31]
    have hin : ∀ a : (v.adicCompletion ℚ)ˣ,
        (∫ x : v.adicCompletion ℚ, dualWhittakerFn3 (fun y : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * W y)
            (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) ∂m₁) *
          ((η⁻¹ a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1) =
        c * ((∫ x : v.adicCompletion ℚ, dualWhittakerFn3 W
            (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) ∂m₁) *
          (((η * χv)⁻¹ a : ℂˣ) : ℂ) * ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) := by
      intro a
      have hx : (fun x : v.adicCompletion ℚ => dualWhittakerFn3
            (fun y : LocalGL3 v => ((χv (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * W y)
            (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g))) =
          fun x => (c * (((χv a : ℂˣ) : ℂ))⁻¹) * dualWhittakerFn3 W
            (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * (weylPrime3 * transposeInv3 g)) := by
        funext x
        rw [dualWhittakerFn3_apply, dualWhittakerFn3_apply, det_dual_arg]
        simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, hc]
        ring
      rw [hx, integral_const_mul]
      simp only [MonoidHom.inv_apply, MonoidHom.mul_apply, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, hc]
      ring
    rw [← integral_const_mul]
    exact congrArg _ (funext fun a => hin a)
  ·
    simp only [IsLocalZeta31ConvergentAbove]
    refine forall_congr' fun s => forall_congr' fun _ => ?_
    rw [hdual s]
    exact integrable_const_mul_iff hcU _

end S_LanglandsTunnell_CubicInduction_localZeta30_localZetaDual31_twist_det
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_localZeta30_localZetaDual31_twist_det (solution)
