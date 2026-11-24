-- Prove2me | solution 1 for GlobalTheory.CompactHowe.substF_X_isWeightedHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:32.119904+00:00
-- url     : https://prove2.me/submissions/af8893e9-c2d0-43a6-a245-098caaa8ed78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
import Theorems.Thm_GlobalTheory_CompactHowe_substF_X


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
theorem _root_.solution {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (X p)) (Finsupp.single p.1 1) := by
  rw [substF_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun k _ => IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
  have h1 := isWeightedHomogeneous_X ℂ (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ)) (p.1, k, l)
  have h2 := (isWeightedHomogeneous_C (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
    (h p.1 k p.2.1 * g p.1 l p.2.2)).mul h1
  rwa [zero_add] at h2
end GlobalTheory.CompactHowe
