-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.algebraMap_locRing_eq_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:19.336065+00:00
-- url     : https://prove2.me/submissions/0c9f6093-1e8a-4b72-bbc0-9046acc3af0d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
variable {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
theorem _root_.solution (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ I) : algebraMap _ (locRing I t) a = 0 := by
  have halg : algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) a =
      Ideal.Quotient.mk _ (algebraMap _ (locPt t) a) := rfl
  rw [halg, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha
end GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
