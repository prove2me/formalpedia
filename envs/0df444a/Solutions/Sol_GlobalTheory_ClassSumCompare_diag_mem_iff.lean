-- Prove2me | solution 1 for GlobalTheory.ClassSumCompare.diag_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:50:29.87268+00:00
-- url     : https://prove2.me/submissions/368b4630-c5d0-4241-9023-57e3eebd95de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulInt
import Theorems.Thm_GlobalTheory_ClassSumCompare_diag_int_mem
import Theorems.Thm_GlobalTheory_ClassSumCompare_mem_hat_of_mem
import Theorems.Thm_GlobalTheory_AdLat_one_tmul_mem_adelicCompletion_fractionalIdeal_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumCompare
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.ClassSumCompare
theorem _root_.solution (x : E) : diagE E x ∈ intAd E ↔ ∃ o : 𝓞 E, (o : E) = x := by
  refine ⟨fun h => ?_, ?_⟩
  · exact (FractionalIdeal.mem_one_iff _).1
      ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff (maximalRealSubfield E) 1 x).1 (mem_hat_of_mem h))
  · rintro ⟨o, rfl⟩; exact diag_int_mem o
end GlobalTheory.ClassSumCompare
