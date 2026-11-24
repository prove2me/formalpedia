-- Prove2me | solution 1 for GlobalTheory.MinorInt.lintegral_cutEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:58:22.437975+00:00
-- url     : https://prove2.me/submissions/c996afe6-040e-4570-8ca2-f8ba3cd8d4ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt
namespace GlobalTheory.MinorInt
theorem _root_.solution (ι κ : Type*) [Fintype ι] [Fintype κ] :
    ∃ c : ENNReal, c < ⊤ ∧ ∀ g : ((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ) → ENNReal,
      ∫⁻ y, g (cutEquiv ι κ y) = c * ∫⁻ w, g w := by
  let e := (cutEquiv ι κ).toContinuousLinearEquiv
  haveI : BorelSpace (ι → ι → ℂ) := Pi.borelSpace
  haveI : BorelSpace (κ → ι → ℂ) := Pi.borelSpace
  haveI : BorelSpace (κ → ι ⊕ κ → ℂ) := Pi.borelSpace
  haveI : BorelSpace (ι ⊕ κ → ι ⊕ κ → ℂ) := Pi.borelSpace
  haveI : BorelSpace ((ι → ι → ℂ) × (κ → ι → ℂ)) := Prod.borelSpace
  haveI : BorelSpace (((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ)) := Prod.borelSpace
  haveI : (volume : Measure (ι → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ι ⊕ κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ι ⊕ κ → ι ⊕ κ → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure ((ι → ι → ℂ) × (κ → ι → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hmap := Measure.isAddLeftInvariant_eq_smul (Measure.map e volume)
    (volume : Measure (((ι → ι → ℂ) × (κ → ι → ℂ)) × (κ → ι ⊕ κ → ℂ)))
  refine ⟨Measure.addHaarScalarFactor (Measure.map e volume) volume, ENNReal.coe_lt_top,
    fun g => ?_⟩
  have hchg : ∫⁻ y, g (e y) = ∫⁻ w, g w ∂(Measure.map e volume) :=
    (lintegral_map_equiv g e.toHomeomorph.toMeasurableEquiv).symm
  refine hchg.trans ?_
  conv_lhs => rw [hmap]
  rw [lintegral_smul_measure]
  rfl
end GlobalTheory.MinorInt
