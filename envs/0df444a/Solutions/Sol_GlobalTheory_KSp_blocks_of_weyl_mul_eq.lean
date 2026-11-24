-- Prove2me | solution 1 for GlobalTheory.KSp.blocks_of_weyl_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:29:12.976895+00:00
-- url     : https://prove2.me/submissions/9fd90af3-4aa0-4810-90bc-a268eabc1d59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitUnitarySiegelParabolicBlockRelationsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapTwoSidedMulHaarMatrixQuadraticExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianMatrixColumnPairingAlgebraicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCharacterAbsScalarBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierIntertwinesSiegelLeviOperator
import Theorems.Thm_GlobalTheory_KSp_mem_sieg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] {p q : UG c (stdJ ν E)} (hp : p ∈ sieg c ν) (hq : q ∈ sieg c ν)
    (h : weyl c ν * p = q * weyl c ν) :
    (mat c p).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₁ = (mat c p).toBlocks₂₂ := by
  have h1 : stdJ ν E * mat c p = mat c q * stdJ ν E := congrArg (mat c) h
  rw [← fromBlocks_toBlocks (mat c p), ← fromBlocks_toBlocks (mat c q), (mem_sieg c).mp hp, (mem_sieg c).mp hq,
    stdJ, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h1
  obtain ⟨h11, h12, -, h22⟩ := h1
  refine ⟨?_, ?_, ?_⟩
  · simpa using h22
  · simpa using h11
  · simpa using h12.symm
end GlobalTheory.KSp
