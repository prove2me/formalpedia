-- Prove2me | solution 1 for GlobalTheory.SW.HAct.map_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:42.928095+00:00
-- url     : https://prove2.me/submissions/10f4ac0d-bfba-4ec7-b78c-910e9f2735ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_map_ccT

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
theorem _root_.solution (τ : E →+* ℂ) {γ : M2 E N} (h : γ ∈ UU E N) :
    (γ.map τ)ᴴ * Matrix.J (Fin N) ℂ * γ.map τ = Matrix.J (Fin N) ℂ := by
  have h1 : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := h
  have hJ : (Matrix.J (Fin N) E).map τ = Matrix.J (Fin N) ℂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases hij : i = j <;>
      simp [Matrix.J, Matrix.one_apply, hij]
  have h2 := congrArg (fun X => X.map τ) h1
  simp only [Matrix.map_mul, map_ccT, hJ] at h2
  exact h2
end GlobalTheory.SW.HAct
