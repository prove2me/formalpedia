-- Prove2me | solution 1 for GlobalTheory.SegreCoord.eq_top_of_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:39:06.078191+00:00
-- url     : https://prove2.me/submissions/7c5cf53c-a8b1-4fa3-9203-021064b90011

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
namespace GlobalTheory.SegreCoord
theorem _root_.solution {J : Ideal T}
    (h : ∀ y : PrimeSpectrum T, ∃ f ∉ y.asIdeal, J.map (algebraMap T (Localization.Away f)) = ⊤) : J = ⊤ := by
  by_contra hJ
  obtain ⟨m, hm, hle⟩ := J.exists_le_maximal hJ
  obtain ⟨f, hf, e⟩ := h ⟨m, hm.isPrime⟩
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) _).1
    ((Ideal.eq_top_iff_one _).1 e)
  rw [one_mul] at ha
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) _).1 ha
  have : f ^ k * f ^ n ∈ m := by
    have e : f ^ k * f ^ n = f ^ k * a := hk
    rw [e]; exact m.mul_mem_left _ (hle a.2)
  rw [← pow_add] at this
  exact hf (hm.isPrime.mem_of_pow_mem _ this)
end GlobalTheory.SegreCoord
