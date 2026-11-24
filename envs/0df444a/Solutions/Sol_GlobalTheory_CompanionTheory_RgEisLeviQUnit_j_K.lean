-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.j_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:22:16.58735+00:00
-- url     : https://prove2.me/submissions/0e5a893e-627a-413c-8835-4ff12fe0fc3d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jM_star
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jQ_val
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jM_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι}
  [Fintype ↥sᶜ] [DecidableEq ↥sᶜ] (A : Ad E R) (ε : ℤˣ) (hσ : ∀ x, A.σ (A.σ x) = x)
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (m : A.U ε ↥sᶜ) (hm : m ∈ A.uK ε ↥sᶜ) : (jQ (s := s) A ε m : A.U ε ι) ∈ A.uK ε ι := by
  have h := Subgroup.mem_subgroupOf.1 hm
  refine Subgroup.mem_subgroupOf.2 ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · exact jM_mem _ _ (fun x y => (h.1 x y).1) r c
  · rw [jQ_val, jG_inv]
    exact jM_mem _ _ (fun x y => (h.1 x y).2) r c
  · have hU := Matrix.mem_unitaryGroup_iff.1 (h.2 w)
    refine Matrix.mem_unitaryGroup_iff.2 ?_
    rw [jQ_val, jG_val, jM_map, jM_star, ← jM_mul emb_inj, hU, jM_one emb_inj]
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
