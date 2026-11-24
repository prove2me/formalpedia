-- Prove2me | solution 1 for GlobalTheory.NormCompat.finite_setOf_valuation_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:14:43.675537+00:00
-- url     : https://prove2.me/submissions/f06343c9-b5a5-421e-8764-d6a58298dccc

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntValuationNormEqSumResidueDegreeMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ProdLocalValuesGlobalOverPlacesAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
open GlobalTheory GlobalTheory.NormCompat
namespace GlobalTheory.NormCompat
theorem _root_.solution (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have h0 : v.valuation F (x : F) ≠ 0 := by simp
  rcases lt_or_gt_of_ne hv with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact (one_lt_inv₀ (zero_lt_iff.2 h0)).2 h
  · left
    exact h
end GlobalTheory.NormCompat
