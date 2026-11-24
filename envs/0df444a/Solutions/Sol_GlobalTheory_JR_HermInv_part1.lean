-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.part1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:14.717451+00:00
-- url     : https://prove2.me/submissions/3b39212d-cc44-4cef-ab7d-b0aae9aa693b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_fixed_mem_range
import Theorems.Thm_GlobalTheory_JR_HermInv_hasInv_iff
import Theorems.Thm_GlobalTheory_JR_HermInv_charpoly_coeff_star
import Theorems.Thm_GlobalTheory_JR_HermInv_mom_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
variable [Unram F E]
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (X : Hn r F E) : ∃ a : Inv r F, HasInv X a := by
  choose p hp using fun i : Fin r => fixed_mem_range (F := F) (charpoly_coeff_star X.1.1 X.1.2 i)
  choose m hm using fun i : Fin r => fixed_mem_range (F := F) (mom_star X i)
  exact ⟨(p, m, X.2.2), (hasInv_iff X _).2 ⟨fun i => (hp i).symm, fun i => (hm i).symm, rfl⟩⟩
end GlobalTheory.JR.HermInv
