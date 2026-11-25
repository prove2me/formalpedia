-- Prove2me | solution 1 for GlobalTheory.mem_range_of_map_eq_of_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:43.278317+00:00
-- url     : https://prove2.me/submissions/fe213c93-35f6-4032-96f3-ac7ff2f0270a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R R' F F' : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] [CommRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F']
    [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F']
    (c : F) (r' : R') (h : algebraMap R' F' r' = algebraMap F F' c) :
    ∃ r : R, algebraMap R F r = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, map_zero _⟩
  rcases ValuationRing.isInteger_or_isInteger R c with h1 | ⟨r, hr⟩
  · exact h1
  have h2 : algebraMap R R' r * r' = 1 := by
    apply IsFractionRing.injective R' F'
    rw [map_mul, h, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R F F', hr,
      ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
  have hu : IsUnit r := IsLocalHom.map_nonunit (f := algebraMap R R') r (IsUnit.of_mul_eq_one _ h2)
  obtain ⟨s, hs⟩ := hu.exists_right_inv
  refine ⟨s, ?_⟩
  have h3 : c⁻¹ * algebraMap R F s = 1 := by rw [← hr, ← map_mul, hs, map_one]
  field_simp at h3
  exact h3
end GlobalTheory
