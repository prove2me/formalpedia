-- Prove2me | solution 1 for GlobalTheory.PadicComplexIso.exists_ringEquiv_extending
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:27.118174+00:00
-- url     : https://prove2.me/submissions/725316a5-4b32-474e-a449-b23ab07726e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MkLeContinuumOfDenseRange
import Theorems.Thm_GlobalTheory_PadicComplexIso_exists_ringEquiv_over
import Theorems.Thm_GlobalTheory_PadicComplexIso_mk_padicComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open Cardinal
open GlobalTheory GlobalTheory.PadicComplexIso
namespace GlobalTheory.PadicComplexIso
theorem _root_.solution : ∀ (q : ℕ) [Fact q.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[q]),
    ∃ ι : ℂ ≃+* ℂ_[q], ∀ x : algebraicClosure ℚ ℂ, ι (x : ℂ) = lam x := by
  intro q _ lam
  let _ : Algebra (algebraicClosure ℚ ℂ) ℂ_[q] := lam.toAlgebra
  have _ : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hR : #(algebraicClosure ℚ ℂ) ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℂ)).trans
      (by rw [Cardinal.mkRat, max_self])
  have hK : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨e, he⟩ := exists_ringEquiv_over (algebraicClosure ℚ ℂ) ℂ ℂ_[q] hR hK
    (by rw [Cardinal.mk_complex, mk_padicComplex])
  exact ⟨e, fun x => he x⟩
end GlobalTheory.PadicComplexIso
