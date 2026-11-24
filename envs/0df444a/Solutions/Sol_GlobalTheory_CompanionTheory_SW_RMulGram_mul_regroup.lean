-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RMulGram.mul_regroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:35.218888+00:00
-- url     : https://prove2.me/submissions/a32cdf35-d2e5-4db7-bf24-b0c1a3a4d94d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightMulActionLaws

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RMulGram
namespace GlobalTheory.CompanionTheory.SW.RMulGram
theorem _root_.solution {A : Type} [CommRing A] {m n : Type} [Fintype m] [Fintype n]
    (P : Matrix n n A) (B : Matrix n m A) (J : Matrix m m A) (C : Matrix m n A)
    (g : Matrix n n A) :
    (P * B) * J * (C * g) = P * ((B * J : Matrix n m A) * C) * g := by
  simp only [Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SW.RMulGram
