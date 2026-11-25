-- Prove2me | solution 1 for GlobalTheory.SW.IsType.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:14:27.269085+00:00
-- url     : https://prove2.me/submissions/0c00b8d4-1346-4980-b443-e0f41b714006

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Theorems.Thm_GlobalTheory_SW_IsType_prod_univ
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
namespace GlobalTheory.SW
namespace IsType
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) : Module.finrank ℚ E = 2 * Ψ.card := by
  have h := hΨ.prod_univ (fun _ => Multiplicative.ofAdd (1 : ℕ))
  have h2 := congrArg Multiplicative.toAdd h
  simp only [Finset.prod_const, toAdd_pow, toAdd_mul, toAdd_ofAdd, smul_eq_mul, Finset.card_univ,
    Embeddings.card, Fintype.card_coe] at h2
  omega
end IsType
end GlobalTheory.SW
