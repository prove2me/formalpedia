-- Prove2me | solution 1 for GlobalTheory.CompactHowe.mapDomain_fst_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:59.901183+00:00
-- url     : https://prove2.me/submissions/67e91ece-4da0-4e99-8ce3-2a160e6be433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionScalarMonomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe
namespace GlobalTheory.CompactHowe
theorem _root_.solution {ι : Type} [DecidableEq ι] {N n : ℕ} (k : ι × Fin N × Fin n →₀ ℕ) (τ₀ : ι) :
    Finsupp.mapDomain Prod.fst k τ₀ = ∑ p ∈ k.support, if p.1 = τ₀ then k p else 0 := by
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  rw [Finsupp.single_apply]
end GlobalTheory.CompactHowe
