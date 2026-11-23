-- Prove2me | solution 1 for GlobalTheory.QuantumMinorAdjacentSwap.eq_zero_of_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:29.410802+00:00
-- url     : https://prove2.me/submissions/b40413fe-4160-46d7-94e8-cc06009238ef

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
open Formalism.REAL
namespace GlobalTheory.QuantumMinorAdjacentSwap
theorem _root_.solution {x : A} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h
  have : x = (2 : ℂ)⁻¹ • ((2 : ℂ) • x) := by rw [smul_smul]; simp
  rw [this, h2, smul_zero]
end GlobalTheory.QuantumMinorAdjacentSwap
