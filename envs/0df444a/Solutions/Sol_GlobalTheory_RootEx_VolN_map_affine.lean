-- Prove2me | solution 1 for GlobalTheory.RootEx.VolN.map_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:03:16.894885+00:00
-- url     : https://prove2.me/submissions/a2c9ec52-268d-4858-937a-944210417f06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
import Theorems.Thm_GlobalTheory_SplitWeil_integral_comp_mulVec_eq_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.VolN
open GlobalTheory.RootEx.Model
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.RootEx.VolN
theorem _root_.solution {a : Type} [Fintype a] [DecidableEq a] (L : Matrix a a k) (hL : L.det = 1) (b : a → k) :
    Measurable (fun e => L.mulVec e + b) ∧
      (Measure.pi fun _ : a => ν).map (fun e => L.mulVec e + b) = Measure.pi fun _ : a => ν := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let g : GL a k := Matrix.GeneralLinearGroup.mkOfDetNeZero L (hL ▸ one_ne_zero)
  have hg : Matrix.GeneralLinearGroup.det g = 1 := Units.ext hL
  have hc : ∀ M : Matrix a a k, Continuous fun e => M.mulVec e := fun M =>
    continuous_const.matrix_mulVec continuous_id
  let T : (a → k) ≃ₜ (a → k) :=
    { toFun := fun e => g.val.mulVec e
      invFun := fun e => (g⁻¹).val.mulVec e
      left_inv := fun e => by simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      right_inv := fun e => by simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  have h1 : (Measure.pi fun _ : a => ν).map T = Measure.pi fun _ : a => ν := by
    have := Measure.Regular.map (μ := Measure.pi fun _ : a => ν) T
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
    have h2 := integral_comp_mulVec_eq_smul ν g fun x => (f x : ℂ)
    rw [hg, integral_complex_ofReal, integral_complex_ofReal] at h2
    have h3 := integral_map_equiv (μ := Measure.pi fun _ : a => ν) T.toMeasurableEquiv f
    rw [Homeomorph.toMeasurableEquiv_coe] at h3
    rw [h3]
    change ∫ x, f (g.val.mulVec x) ∂_ = _
    simpa [nabs] using h2
  refine ⟨((hc L).add continuous_const).measurable, ?_⟩
  have : (fun e => L.mulVec e + b) = (fun e => e + b) ∘ T := rfl
  rw [this, ← Measure.map_map (measurable_add_const b) T.continuous.measurable, h1, map_add_right_eq_self]
end GlobalTheory.RootEx.VolN
