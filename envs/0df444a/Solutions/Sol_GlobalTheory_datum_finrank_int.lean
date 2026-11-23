-- Prove2me | solution 1 for GlobalTheory.datum_finrank_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:55.63557+00:00
-- url     : https://prove2.me/submissions/ce4c63ca-3953-4987-a134-25e2aada6f73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Theorems.Thm_GlobalTheory_finrank_int_eq_mul_of_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) :
    Module.finrank ℤ D.La = 2 * (Module.finrank ℚ E / 2 * (D.p + D.q)) := by
  haveI := D.fin
  rw [_root_.GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank]
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank E
  have h2 : NumberField.InfinitePlace.nrRealPlaces E = 0 :=
    nrRealPlaces_eq_zero_iff.mpr inferInstance
  rw [h2, zero_add] at h1
  rw [← h1]
  have h3 : 2 * NumberField.InfinitePlace.nrComplexPlaces E / 2 =
      NumberField.InfinitePlace.nrComplexPlaces E := by omega
  rw [h3]; ring
end _root_.GlobalTheory
end GlobalTheory
