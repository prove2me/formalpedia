-- Prove2me | solution 1 for GlobalTheory.SS.LinCore.finrank_le_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:18:03.167864+00:00
-- url     : https://prove2.me/submissions/ee3b17e3-8426-4c44-9940-dd6c8ec7db99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplectic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LinCore
open Polynomial
variable {𝕜 V : Type} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [Module ℚ V] [IsScalarTower ℚ 𝕜 V]
omit [CharZero 𝕜] [Module ℚ V] [IsScalarTower ℚ 𝕜 V]
namespace GlobalTheory.SS.LinCore
theorem _root_.solution [FiniteDimensional 𝕜 V] (T f : Module.End 𝕜 V)
    (W : Submodule 𝕜 V) (h1 : ∀ x, f (T x) ∈ W) (h2 : ∀ x, f (T x) = 0 → T x = 0) :
    Module.finrank 𝕜 V ≤ Module.finrank 𝕜 (LinearMap.ker T) + Module.finrank 𝕜 W := by
  let L : LinearMap.range T →ₗ[𝕜] W :=
    (f.domRestrict (LinearMap.range T)).codRestrict W (by
      rintro ⟨_, x, rfl⟩
      exact h1 x)
  have hL : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨_, x, rfl⟩ hx
    exact Subtype.ext (h2 x (congrArg Subtype.val hx))
  have h5 := LinearMap.finrank_le_finrank_of_injective hL
  have h6 := LinearMap.finrank_range_add_finrank_ker T
  omega
end GlobalTheory.SS.LinCore
