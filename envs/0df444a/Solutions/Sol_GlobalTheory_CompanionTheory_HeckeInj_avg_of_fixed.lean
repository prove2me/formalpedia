-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeInj.avg_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:37:00.679034+00:00
-- url     : https://prove2.me/submissions/bde16aac-0060-4f2e-ae9c-a6d9742b415b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_fix_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {G : Type} [Group G]
namespace GlobalTheory.CompanionTheory.HeckeInj
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K L : Subgroup G)
    [Fintype (K ⧸ L.subgroupOf K)] {v : V} (hv : v ∈ fixed ρ K) :
    avg ρ K L v = (Fintype.card (K ⧸ L.subgroupOf K) : ℂ) • v := by
  simp only [avg, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun q _ => fix_of_mem hv (q.out : K).2]
  simp [Nat.cast_smul_eq_nsmul]
end GlobalTheory.CompanionTheory.HeckeInj
