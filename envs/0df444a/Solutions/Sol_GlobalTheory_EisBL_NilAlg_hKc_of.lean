-- Prove2me | solution 1 for GlobalTheory.EisBL.NilAlg.hKc_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:43:01.058528+00:00
-- url     : https://prove2.me/submissions/cc1f0e28-e0c1-4d4e-b580-af6915bbfb88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.EisBL.NilAlg
theorem _root_.solution (c : B →+* B) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1) (hJc : (J.map c)ᵀ = ε • J)
    (hJK : J * K = 1) (hKJ : K * J = 1) : (K.map c)ᵀ = ε • K := by
  have hm : (K.map c)ᵀ * (ε • J) = 1 := by
    rw [← hJc, ← transpose_mul, ← Matrix.map_mul, hJK, Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
  calc (K.map c)ᵀ = (K.map c)ᵀ * ((ε • J) * (ε • K)) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε, one_smul, hJK, Matrix.mul_one]
    _ = ((K.map c)ᵀ * (ε • J)) * (ε • K) := (Matrix.mul_assoc _ _ _).symm
    _ = ε • K := by rw [hm, Matrix.one_mul]
end GlobalTheory.EisBL.NilAlg
