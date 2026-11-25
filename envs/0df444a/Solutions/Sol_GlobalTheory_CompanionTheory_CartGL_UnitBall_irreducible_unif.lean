-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.UnitBall.irreducible_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:11.097453+00:00
-- url     : https://prove2.me/submissions/b5a0cb0d-0fd6-4332-8b7f-262d38038e6c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanExists
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedean
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_isUnit_of_norm_eq_one
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_norm_eq_one_of_isUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_norm_unif_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_exists_nat_norm
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_UnitBall_unif_coe
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
variable {p : Lˣ}
namespace GlobalTheory.CompanionTheory.CartGL.UnitBall
theorem _root_.solution (hp : IsUnif p) : Irreducible (unif hp) := by
  have h0 := norm_unif_pos p
  refine ⟨fun h => ?_, ?_⟩
  · have := norm_eq_one_of_isUnit h
    rw [unif_coe] at this
    exact absurd this hp.1.ne
  · intro a b hab
    have hab' : (p : L) = (a : L) * (b : L) := by
      have := congrArg (Subtype.val) hab
      simpa [unif_coe] using this
    have ha0 : (a : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, zero_mul])
    have hb0 : (b : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, mul_zero])
    obtain ⟨i, hi⟩ := exists_nat_norm hp ha0 a.2
    obtain ⟨j, hj⟩ := exists_nat_norm hp hb0 b.2
    have hn : ‖(p : L)‖ ^ 1 = ‖(p : L)‖ ^ (i + j) := by
      rw [pow_one, pow_add, ← hi, ← hj, ← norm_mul, ← hab']
    have hij : 1 = i + j := pow_right_injective₀ h0 hp.1.ne hn
    rcases Nat.eq_zero_or_pos i with h | h
    · left
      apply isUnit_of_norm_eq_one
      rw [hi, h, pow_zero]
    · right
      have : j = 0 := by omega
      apply isUnit_of_norm_eq_one
      rw [hj, this, pow_zero]
end GlobalTheory.CompanionTheory.CartGL.UnitBall
