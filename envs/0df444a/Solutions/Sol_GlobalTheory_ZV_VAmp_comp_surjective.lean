-- Prove2me | solution 1 for GlobalTheory.ZV.VAmp.comp_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:20:18.600189+00:00
-- url     : https://prove2.me/submissions/bf6657b6-216c-4761-b5ed-4427a5450e6b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension

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
noncomputable section
open GlobalTheory GlobalTheory.ZV
variable {K : Type} [Field K] {X Y : Scheme.{0}}
namespace GlobalTheory.ZV
namespace VAmp
theorem _root_.solution {p : X ⟶ Sp K} {M : LB X} {σ τ : Type} {th : σ → M.Sec} (h : VAmp p M th)
    {e : τ → σ} (he : Function.Surjective e) : VAmp p M (fun i => th (e i)) := by
  refine ⟨(he.iSup_comp fun i => Out.nonzeroLocus (th i)).trans h.1, fun i => ⟨(h.2 (e i)).1, ?_⟩⟩
  obtain ⟨r, hr, hF⟩ := (h.2 (e i)).2
  refine ⟨fun j => r (e j), fun j k => hr (e j) k, fun f => ?_⟩
  obtain ⟨F, rfl⟩ := hF f
  obtain ⟨G, rfl⟩ := MvPolynomial.rename_surjective e he F
  exact ⟨G, MvPolynomial.eval₂_rename _ _ _ _⟩
end VAmp
end GlobalTheory.ZV
