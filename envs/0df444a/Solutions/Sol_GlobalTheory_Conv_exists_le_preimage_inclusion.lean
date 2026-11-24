-- Prove2me | solution 1 for GlobalTheory.Conv.exists_le_preimage_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:39:37.859162+00:00
-- url     : https://prove2.me/submissions/1c83487a-49ac-47bd-b155-f51ae11d9717

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_Conv_exists_isUnit_halfRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {Z : Scheme.{0}}
namespace GlobalTheory.Conv
theorem _root_.solution {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT) ⁻¹ᵁ U) :
    ∃ T', ∃ h : T ≤ T', ⊤ ≤ (spMap (Subalgebra.inclusion (halfRing_mono h) :
      halfRing T →+* halfRing T') ≫ yT) ⁻¹ᵁ U := by
  let p : PrimeSpectrum (halfRing T) :=
    spMap (halfIncl T : halfRing T →+* convLaurent) (default : PrimeSpectrum convLaurent)
  have hp : p ∈ (show Set (PrimeSpectrum (halfRing T)) from (yT ⁻¹ᵁ U).carrier) :=
    hU (x := (default : PrimeSpectrum convLaurent)) trivial
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp (yT ⁻¹ᵁ U).isOpen
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr p.asIdeal.zero_mem
  obtain ⟨T', h, hu⟩ := exists_isUnit_halfRing hr0
  refine ⟨T', h, fun q _ => hle (a := spMap (Subalgebra.inclusion (halfRing_mono h) :
      halfRing T →+* halfRing T') q) fun hq => ?_⟩
  exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)
end GlobalTheory.Conv
