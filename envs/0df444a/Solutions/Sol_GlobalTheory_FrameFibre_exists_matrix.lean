-- Prove2me | solution 1 for GlobalTheory.FrameFibre.exists_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:11.934887+00:00
-- url     : https://prove2.me/submissions/248d3e44-65ca-415e-87d1-1b9b7d71ce28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameOfPeriodLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsEqNsmulOfDvdPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Theorems.Thm_GlobalTheory_FrameFibre_exists_smul_eq

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
    (ψ : L →ₗ[𝓞 E] (Fin r → E)) : ∃ A : Matrix (Fin r) (Fin r) E, ∀ v, A *ᵥ φ v = ψ v := by
  haveI : IsLocalizedModule (𝓞 E)⁰ φ :=
    { map_units := fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s
      surj := fun u => by
        obtain ⟨c, v, hc, hv⟩ := exists_smul_eq φ hspan u
        exact ⟨(v, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hv⟩
      exists_of_eq := fun h => ⟨1, by rw [hφ h]⟩ }
  have hb := IsLocalizedModule.isBaseChange (𝓞 E)⁰ E φ
  exact ⟨LinearMap.toMatrix' (hb.lift ψ), fun v => by
    rw [LinearMap.toMatrix'_mulVec, hb.lift_eq]⟩
end GlobalTheory.FrameFibre
