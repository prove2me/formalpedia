-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuotVan.modInv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:44.205151+00:00
-- url     : https://prove2.me/submissions/dc93f558-7491-4840-8b39-381d0a79a62a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_conjCE_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotVan
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q] [T2Space Q]
variable (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [SecondCountableTopology N]
  [SecondCountableTopology M]
namespace GlobalTheory.CompanionTheory.QuotVan
theorem _root_.solution (m m' : M) : modInv N M (m * m') = modInv N M m * modInv N M m' := by
  have h1 := (mulEquivHaarChar_pos (conjCE N (m : Q))).ne'
  have h2 := (mulEquivHaarChar_pos (conjCE N (m' : Q))).ne'
  simp only [modInv, Subgroup.coe_mul, conjCE_mul, mulEquivHaarChar_trans, ENNReal.coe_mul]
  rw [ENNReal.mul_inv (Or.inr ENNReal.coe_ne_top) (Or.inl ENNReal.coe_ne_top), mul_comm]
end GlobalTheory.CompanionTheory.QuotVan
