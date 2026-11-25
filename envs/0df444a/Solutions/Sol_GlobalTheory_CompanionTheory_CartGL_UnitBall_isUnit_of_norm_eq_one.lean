-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.UnitBall.isUnit_of_norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:53:31.023969+00:00
-- url     : https://prove2.me/submissions/de4dbe49-f385-4876-a48c-00e6503d7f28

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedean
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_mem_ball
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.UnitBall
variable (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
variable {L}
namespace GlobalTheory.CompanionTheory.CartGL.UnitBall
theorem _root_.solution {x : ball L} (h : ‖(x : L)‖ = 1) : IsUnit x := by
  have hx : (x : L) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    exact zero_ne_one h
  have hi : (x : L)⁻¹ ∈ ball L := by
    rw [mem_ball, norm_inv, h, inv_one]
  refine IsUnit.of_mul_eq_one ⟨(x : L)⁻¹, hi⟩ ?_
  apply Subtype.ext
  simp [hx]
end GlobalTheory.CompanionTheory.CartGL.UnitBall
