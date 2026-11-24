-- Prove2me | solution 1 for GlobalTheory.SW.Base.transH_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:46.853075+00:00
-- url     : https://prove2.me/submissions/8ad43e2b-f350-4723-bb40-dff3ce3710db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
omit [IsCMField E]
namespace GlobalTheory.SW.Base
theorem _root_.solution (φ : Matrix (Fin n) (Fin N) E → ℂ) : TransH Ψ (1 : M2 E N) φ φ := by
  intro Z _ z z'
  have h11 : (1 : M2 E N).toBlocks₁₁ = 1 := by rw [← Matrix.fromBlocks_one]; rfl
  have h12 : (1 : M2 E N).toBlocks₁₂ = 0 := by rw [← Matrix.fromBlocks_one]; rfl
  have h21 : (1 : M2 E N).toBlocks₂₁ = 0 := by rw [← Matrix.fromBlocks_one]; rfl
  have h22 : (1 : M2 E N).toBlocks₂₂ = 1 := by rw [← Matrix.fromBlocks_one]; rfl
  have d1 : ∀ τ, hDen Ψ (1 : M2 E N) Z τ = 1 := fun τ => by simp [hDen, h21, h22]
  have d2 : ∀ τ, hDen' Ψ (1 : M2 E N) Z τ = 1 := fun τ => by simp [hDen', h21, h22]
  have a : hAct Ψ (1 : M2 E N) Z = Z := by funext τ; simp [hAct, d1, h11, h12]
  have f : hFac Ψ (1 : M2 E N) Z z z' = 1 := by simp [hFac, d1, h21]
  rw [a, f, one_mul]
  congr 1
  · funext τ; ext k i; simp [d2]
  · funext τ; ext k i; simp [d1]
end GlobalTheory.SW.Base
