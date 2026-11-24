-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.prod_ofFn_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:43.514844+00:00
-- url     : https://prove2.me/submissions/9a099e1d-7f7d-4296-94a2-a4212c304719

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_QminorSwapAdjacent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.QuantumMinorAdjacentSwap
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution {n : ℕ} {ι : Type} [Fintype ι] (a : Fin n → ι → ℂ)
    (T : Fin n → ι → A) :
    (List.ofFn fun k => ∑ c, a k c • T k c).prod =
      ∑ c : Fin n → ι, (∏ k, a k (c k)) • (List.ofFn fun k => T k (c k)).prod := by
  classical
  have h := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_sum (fun k c => a k c • T k c)
  simp only [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply] at h
  exact h
end GlobalTheory.QuantumMinorAdjacentSwap
