-- Prove2me | solution 1 for GlobalTheory.HeckeOne.ideleNorm_expScalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:16.714803+00:00
-- url     : https://prove2.me/submissions/78a05c51-aaba-49e3-8079-eb134bbb96af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSmoothMulExtensionOfContinuousChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExtensionEmbeddingMixedSymmOfIsComplex
import Theorems.Thm_GlobalTheory_HeckeOne_extensionEmbedding_mixedSymm_of_isReal
import Theorems.Thm_GlobalTheory_HeckeOne_extensionEmbedding_mixedSymm_of_isComplex
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable (K : Type) [Field K] [NumberField K]
namespace GlobalTheory.HeckeOne
theorem _root_.solution (x : ℝ) :
    ideleNorm (mixedIdele K (expScalar K x)) = Real.exp ((Module.finrank ℚ K : ℝ) * x) := by
  have h : ∀ v : InfinitePlace K, ‖(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (algebraMap ℝ (mixedSpace K) (Real.exp x)) v‖ = Real.exp x := by
    intro v
    rcases v.isReal_or_isComplex with hv | hv
    · rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _),
        extensionEmbedding_mixedSymm_of_isReal]
      change ‖Real.exp x‖ = _
      exact Real.norm_of_nonneg (Real.exp_pos x).le
    · rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _),
        extensionEmbedding_mixedSymm_of_isComplex K _ v hv]
      change ‖((Real.exp x : ℝ) : ℂ)‖ = _
      exact Complex.norm_of_nonneg (Real.exp_pos x).le
  change (∏ v : InfinitePlace K, ‖(InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (algebraMap ℝ (mixedSpace K) (Real.exp x)) v‖ ^ v.mult) *
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : v.adicCompletion K)‖) = _
  simp only [h, norm_one, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, Real.exp_nat_mul]
end GlobalTheory.HeckeOne
