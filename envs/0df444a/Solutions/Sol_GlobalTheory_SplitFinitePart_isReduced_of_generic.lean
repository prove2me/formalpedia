-- Prove2me | solution 1 for GlobalTheory.SplitFinitePart.isReduced_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:10:39.450108+00:00
-- url     : https://prove2.me/submissions/e4747ef6-1df8-4e39-92b5-df8698ce5b72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart
namespace GlobalTheory.SplitFinitePart
theorem _root_.solution {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π] [IsReduced (pullback π (spMap (algebraMap R K)))] : IsReduced Z := by
  have : IsDominant (spMap (algebraMap R K)) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.fst π (spMap (algebraMap R K)))
end GlobalTheory.SplitFinitePart
