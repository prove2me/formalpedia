-- Prove2me | solution 1 for GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:38.763808+00:00
-- url     : https://prove2.me/submissions/1166c168-1f8f-4660-825b-2b44663808d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.PlaceCompletion
open scoped WithZero
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] (la : HeightOneSpectrum R)
variable {la} {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
namespace GlobalTheory.PlaceCompletion
theorem _root_.solution {j : K →+* K'} {e : ℕ} (ho : OverLa la V j e) (a : K) :
    valV V (j a) = la.valuation K a ^ e := by
  unfold OverLa vV vLa at ho
  obtain ⟨he, hlog⟩ := ho
  by_cases ha : a = 0
  · subst ha
    rw [map_zero, map_zero, map_zero, zero_pow he.ne']
  have h1 : valV V (j a) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero j).2 ha)
  have h2 : la.valuation K a ^ e ≠ 0 := pow_ne_zero e ((Valuation.ne_zero_iff _).2 ha)
  have hk := hlog a
  rw [← WithZero.exp_log h1, ← WithZero.exp_log h2, WithZero.log_pow, WithZero.exp_inj, nsmul_eq_mul]
  linarith
end GlobalTheory.PlaceCompletion
