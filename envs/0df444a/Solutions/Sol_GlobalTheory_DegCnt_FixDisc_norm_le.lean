-- Prove2me | solution 1 for GlobalTheory.DegCnt.FixDisc.norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:40.853918+00:00
-- url     : https://prove2.me/submissions/99c9f1d8-8930-460f-8b2a-4adbfaea8eec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
namespace GlobalTheory.DegCnt.FixDisc
theorem _root_.solution {K : Type} [Field K] [NumberField K] (a : K) (c : ℝ) (h : ∀ σ : K →+* ℂ, ‖σ a‖ ≤ c) :
    ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ c ^ Module.finrank ℚ K := by
  have e := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ a)
  rw [norm_prod, eq_ratCast, Complex.norm_ratCast] at e
  rw [Rat.cast_abs, e, ← AlgHom.card ℚ K ℂ, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => h σ.toRingHom)
end GlobalTheory.DegCnt.FixDisc
