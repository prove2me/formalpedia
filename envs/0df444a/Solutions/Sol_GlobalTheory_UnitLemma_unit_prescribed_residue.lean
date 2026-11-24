-- Prove2me | solution 1 for GlobalTheory.UnitLemma.unit_prescribed_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:11:39.173995+00:00
-- url     : https://prove2.me/submissions/aa50d6c3-6cf3-436f-b059-987fc0ba7706

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitPrescribedResidueReducedFiniteAlgebra
import Theorems.Thm_GlobalTheory_UnitLemma_exists_unit_residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory
namespace GlobalTheory
namespace UnitLemma
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A)
    (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧
      ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 :=
  fun K B hB m z hz => UnitLemma.exists_unit_residue K B hB m z hz
end UnitLemma
end GlobalTheory
