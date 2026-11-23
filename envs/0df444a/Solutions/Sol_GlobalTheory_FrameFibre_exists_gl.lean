-- Prove2me | solution 1 for GlobalTheory.FrameFibre.exists_gl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:49.699256+00:00
-- url     : https://prove2.me/submissions/1386f6ca-1291-41cb-a274-99518e46d3be

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Theorems.Thm_GlobalTheory_FrameFibre_exists_matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FrameFibre
variable {E : Type} [Field E] [NumberField E] {r : ℕ}
namespace GlobalTheory.FrameFibre
theorem _root_.solution {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (gam : L ≃ₗ[𝓞 E] L) : ∃ γ : GL (Fin r) E,
      ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ (gam v) := by
  obtain ⟨A, hA⟩ := exists_matrix φ hφ hspan (φ ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := exists_matrix φ hφ hspan (φ ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v, A *ᵥ φ v = φ (gam v) := hA
  have hB' : ∀ v, B *ᵥ φ v = φ (gam.symm v) := hB
  have hAB : A * B = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB', hA', Matrix.one_mulVec,
      LinearEquiv.apply_symm_apply]
  exact ⟨⟨A, B, hAB, mul_eq_one_comm.1 hAB⟩, hA'⟩
end GlobalTheory.FrameFibre
