-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.int_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:44.229137+00:00
-- url     : https://prove2.me/submissions/aada2b31-cb64-429c-8209-10db3eb63ec7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
namespace GlobalTheory.AdaptedChain
theorem _root_.solution {x : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (x ^ n)) : V.Ge 0 x := by
  unfold VF.Ge at h ⊢
  rw [V.v.map_pow] at h
  induction hv : V.v x using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [hv] at h
    have h' : ((0 : ℝ) : WithTop ℝ) ≤ ((n • t : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_nsmul]; exact h
    have h'' : (0 : ℝ) ≤ n • t := by exact_mod_cast h'
    rw [nsmul_eq_mul] at h''
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have : 0 ≤ t := by by_contra hc; push_neg at hc; nlinarith
    exact_mod_cast this
end GlobalTheory.AdaptedChain
