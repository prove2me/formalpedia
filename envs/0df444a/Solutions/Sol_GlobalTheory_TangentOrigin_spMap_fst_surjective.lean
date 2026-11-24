-- Prove2me | solution 1 for GlobalTheory.TangentOrigin.spMap_fst_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:40.518474+00:00
-- url     : https://prove2.me/submissions/c09700f5-c5c0-499f-9504-8b93eed3cb13

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.TangentOrigin
variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
namespace GlobalTheory.TangentOrigin
theorem _root_.solution : Function.Surjective (spMap fstC) := by
  intro p
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change x.fst ∈ (⊥ : Ideal ℂ) ↔ x ∈ PrimeSpectrum.asIdeal p
  rw [Ideal.mem_bot]
  constructor
  · intro hx
    apply p.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl,
        TrivSqZeroExt.inr_mul_inr]
    rw [this]
    exact Ideal.zero_mem _
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
end GlobalTheory.TangentOrigin
