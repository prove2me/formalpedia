-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.superdiagSum_sigmaMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:11.97468+00:00
-- url     : https://prove2.me/submissions/94316d0c-d6f4-440c-8d1d-b2d5587e3628

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (M : Matrix (Fin n) (Fin n) F) :
    superdiagSum (sigmaMat M) = superdiagSum M := by
  unfold superdiagSum
  rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.revPerm_apply, sigmaMat_apply, Fin.rev_rev]
  have hiff : (Fin.rev a).val = (Fin.rev b).val + 1 ↔ b.val = a.val + 1 := by
    simp only [Fin.val_rev]
    have := a.isLt
    have := b.isLt
    omega
  by_cases h : b.val = a.val + 1
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
end GroundTheory.Automorphic.Whittaker
