-- Prove2me | solution 1 for GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:44.487866+00:00
-- url     : https://prove2.me/submissions/89ec6596-3316-4885-845f-23ffca081ec4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_sum_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
namespace GroundTheory.Global.AdeleBaseChange
theorem _root_.solution (y : 𝔸[L]) :
    (adeleTensorEquiv K L).symm y = ∑ i, b i ⊗ₜ coord b i y := by
  rw [AlgEquiv.symm_apply_eq]
  exact (adeleTensorEquiv_sum_coord b y).symm
end GroundTheory.Global.AdeleBaseChange
