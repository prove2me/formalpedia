-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.Den.loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:05.138916+00:00
-- url     : https://prove2.me/submissions/40609fda-7cad-43a1-a5e9-84550df1bc35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Theorems.Thm_GlobalTheory_ZM_NearBuild_exists_mem_loc
import Theorems.Thm_GlobalTheory_ZM_NearBuild_densePrimes_localization

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
namespace Den
theorem _root_.solution {q₀ : Ideal R} (h : Den b Mat κ β v q₀) {f : R} (hf : f ∉ q₀) :
    ∃ q₁, Den b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ ∧ q₁.comap (loc f) = q₀ := by
  obtain ⟨q₁, hq₁, hcomap⟩ := exists_mem_loc h.2 hf
  exact ⟨q₁, ⟨densePrimes_localization h.1 f, hq₁⟩, hcomap⟩
end Den
end GlobalTheory.ZM.NearBuild
