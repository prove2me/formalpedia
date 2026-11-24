-- Prove2me | solution 1 for GlobalTheory.SW.HaarLevel.relIndex_perSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:44.457227+00:00
-- url     : https://prove2.me/submissions/c92fc431-e0eb-4b14-b592-4e8496876ed0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Theorems.Thm_GlobalTheory_SW_HaarLevel_incl_inj
import Theorems.Thm_GlobalTheory_SW_HaarLevel_perSub_eq_range
import Theorems.Thm_GlobalTheory_SW_HaarLevel_mem_perSub
import Theorems.Thm_GlobalTheory_SW_HaarLevel_index_nsmul
import Theorems.Thm_GlobalTheory_SW_HaarLevel_nsmul_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.HaarLevel
theorem _root_.solution (R S : ℕ) (hR : 0 < R) :
    (perSub K κ ι (R * S)).relIndex (perSub K κ ι R) =
      S ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) := by
  rw [perSub_eq_range R, ← AddSubgroup.index_comap, ← index_nsmul]
  congr 1
  ext y
  simp only [AddSubgroup.mem_comap, mem_perSub, AddMonoidHom.mem_range, AddMonoidHom.comp_apply,
    nsmulAddMonoidHom_apply]
  refine exists_congr fun z => ?_
  rw [mul_smul, map_nsmul, nsmul_cancel hR, ← map_nsmul, incl_inj.eq_iff]
end GlobalTheory.SW.HaarLevel
