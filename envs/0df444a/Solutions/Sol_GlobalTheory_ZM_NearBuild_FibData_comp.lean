-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.FibData.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:53.024106+00:00
-- url     : https://prove2.me/submissions/fb6f3593-7535-4f6d-8085-50b829d24192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Theorems.Thm_GlobalTheory_ZM_NearBuild_good_comp

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
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.NearBuild
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {R R' : Type} [CommRing R] [CommRing R']
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)
variable {b Mat κ β v}
namespace GlobalTheory.ZM.NearBuild
namespace FibData
theorem _root_.solution {m : ℕ} {p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R} {Hh : Type} {hh : Hh → Ix g (N' ^ 2)}
    {Q : Polynomial ℚ} {d : ℕ} (h : FibData b Mat κ β v m p hh Q d) (ρ : R →+* R') :
    FibData b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (fun c a => ρ (p c a)) hh Q d := by
  intro K _ _ x s t hg
  exact h K (x.comp ρ) s t ((good_comp ρ x t).1 hg)
end FibData
end GlobalTheory.ZM.NearBuild
