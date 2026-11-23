-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.mem_objPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:42.445669+00:00
-- url     : https://prove2.me/submissions/94cde4dc-cac0-4155-bca0-fa3ea9d505cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP

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
theorem _root_.solution {q : Ideal R} : q ∈ objPrimes b Mat κ β v ↔
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s),
      RingHom.ker x = q ∧ Good b Mat κ β v x t := by
  constructor
  · rintro ⟨K, hF, hA, x, t, hk, hs, hth⟩
    exact ⟨K, hF, hA, x, _, t, hk, rfl, hs, hth⟩
  · rintro ⟨K, hF, hA, x, s, t, hk, ⟨rfl, hs, hth⟩⟩
    exact ⟨K, hF, hA, x, t, hk, hs, hth⟩
end GlobalTheory.ZM.NearBuild
