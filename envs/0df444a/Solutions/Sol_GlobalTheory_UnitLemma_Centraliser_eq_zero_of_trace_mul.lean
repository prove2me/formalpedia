-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:38.724164+00:00
-- url     : https://prove2.me/submissions/222ee91a-bcc8-4d58-92c6-a10158e3057f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_eq_zero_of_isNilpotent
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_isNilpotent_of_trace_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Centraliser
namespace GlobalTheory.UnitLemma.Centraliser
theorem _root_.solution {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : ∀ y, Algebra.trace K.E B.A (a * y) = 0) : a = 0 := by
  apply eq_zero_of_isNilpotent B hsep
  let bs := Module.finBasis K.E B.A
  have hN : IsNilpotent (Algebra.leftMulMatrix bs a) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace, pow_succ']
    exact ha _
  obtain ⟨m, hm⟩ := hN
  refine ⟨m, Algebra.leftMulMatrix_injective bs ?_⟩
  rw [map_pow, hm, map_zero]
end GlobalTheory.UnitLemma.Centraliser
