-- Prove2me | solution 1 for GlobalTheory.appLE_top_eq_zero_iff_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:23:15.241022+00:00
-- url     : https://prove2.me/submissions/b949fde4-1f56-4bb5-a587-f32899d0abd5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsGenTranslDiffComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_KernelPolarisationTrivialOfSectionsVanishZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_appLE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (a : Γ(X, U)) :
    (r.appLE U ⊤ h).hom a = 0 ↔ ∀ z, gs r z U a = 0 := by
  have e : ∀ z, gs (𝟙 Z) z ⊤ ((r.appLE U ⊤ h).hom a) = gs r z U a := fun z =>
    (gs_appLE r U ⊤ h (𝟙 Z) z trivial a).trans (by rw [Category.id_comp])
  have e0 : ∀ z : Z, gs (𝟙 Z) z ⊤ 0 = 0 := fun z => by
    rw [gs_eq (𝟙 Z) z ⊤ trivial, map_zero, map_zero]
  exact ⟨fun H z => by rw [← e z, H, e0], fun H => fn_ext fun z _ => by rw [e z, H z, e0]⟩
end GlobalTheory
