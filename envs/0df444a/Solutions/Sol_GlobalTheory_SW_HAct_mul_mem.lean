-- Prove2me | solution 1 for GlobalTheory.SW.HAct.mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:30.92858+00:00
-- url     : https://prove2.me/submissions/ca018bf7-d055-4da4-9aeb-1f6afe8eb02f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_mul
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution {γ γ' : M2 E N} (h : γ ∈ UU E N) (h' : γ' ∈ UU E N) : γ' * γ ∈ UU E N := by
  have h1 : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  have h2 : ccT γ' * Matrix.J (Fin N) E * γ' = Matrix.J (Fin N) E := h'
  change ccT (γ' * γ) * Matrix.J (Fin N) E * (γ' * γ) = Matrix.J (Fin N) E
  rw [ccT_mul]
  calc _ = ccT γ * (ccT γ' * Matrix.J (Fin N) E * γ') * γ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2, h1]
end GlobalTheory.SW.HAct
