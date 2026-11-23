-- Prove2me | solution 1 for GlobalTheory.ZM.levelFactor_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:42.974065+00:00
-- url     : https://prove2.me/submissions/280cbd41-31c5-4df4-932b-0c39996d8fd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelOnFactorOfEighthPowerAbelianScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (c : Fin n → ℤ) (u : Fin m) : π u (∏ i, P i ^ c i) = L (bas c u) := by
  let φ : Λ →+ Additive H := AddMonoidHom.mk' (fun x => Additive.ofMul (L x)) hL
  have hφ : ∀ x, L x = Additive.toMul (φ x) := fun x => rfl
  have hc : bas c u = ∑ i, c i • bas (Pi.single i 1) u := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : (Pi.single i (c i) : Fin n → ℤ) = c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [hs, map_zsmul, Pi.smul_apply]
  rw [map_prod, hc, hφ, map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, hP, map_zsmul, toMul_zsmul]
  rfl
end GlobalTheory.ZM
