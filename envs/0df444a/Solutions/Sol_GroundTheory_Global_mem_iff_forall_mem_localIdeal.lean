-- Prove2me | solution 1 for GroundTheory.Global.mem_iff_forall_mem_localIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:39.838153+00:00
-- url     : https://prove2.me/submissions/c62c23e8-4640-45ca-ab36-073759d341be

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Theorems.Thm_GroundTheory_Global_mem_iff_forall_valuation_le
import Theorems.Thm_GroundTheory_Global_mem_localIdeal_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    x ∈ I ↔ ∀ v : HeightOneSpectrum (𝓞 K), (x : v.adicCompletion K) ∈ localIdeal I v := by
  rw [mem_iff_forall_valuation_le hI]
  refine forall_congr' fun v ↦ ?_
  rw [mem_localIdeal_iff hI, valuedAdicCompletion_eq_valuation']
end GroundTheory.Global
