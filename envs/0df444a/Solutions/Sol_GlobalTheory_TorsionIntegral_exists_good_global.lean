-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.exists_good_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:26:21.283875+00:00
-- url     : https://prove2.me/submissions/db4a3887-2f29-4fb0-b968-389455f7e679

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.TorsionIntegral
theorem _root_.solution (hL : L.IsLB) (φ : Z ⟶ Y) (z : Z) (y₀ : Y) (hy₀ : ∀ (U : Y.Opens) (y : Y), y₀ ∈ U → y ∈ U)
    (he : ∀ ψ ψ' : Y ⟶ X, φ ≫ ψ = φ ≫ ψ' → ψ = ψ') :
    ∃ J₀ : (Z ⟶ X) → L.ι, Good L z J₀ ∧ ∀ (q : Y ⟶ X) (y : Y), q y ∈ L.U (J₀ (φ ≫ q)) := by
  choose j hj using fun q : Y ⟶ X => exists_chart hL (q y₀)
  have hj' : ∀ (q : Y ⟶ X) (y : Y), q y ∈ L.U (j q) := fun q y => hy₀ (q ⁻¹ᵁ L.U (j q)) y (hj q)
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun q : Y ⟶ X => φ ≫ q) j (fun a b h => congrArg j (he a b h))
    (fun q => hj' q (φ z))
  exact ⟨J, hJ, fun q y => (e q).symm ▸ hj' q y⟩
end GlobalTheory.TorsionIntegral
