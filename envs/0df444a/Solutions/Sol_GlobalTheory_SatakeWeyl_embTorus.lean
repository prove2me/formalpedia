-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.embTorus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:50:21.426746+00:00
-- url     : https://prove2.me/submissions/ad8c628b-1968-44a7-aa8f-74f8e01ca828

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryDiagonalFactorizationAlongEmbedding
import Theorems.Thm_GlobalTheory_SatakeWeyl_emb_mul_diagonal
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_SatakeWeyl_mat_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution : EmbTorus := by
  classical
  intro L _ _ σ n r e ι he hι D D' t t' s s' ht ht' hs hs' hD
  have h1 := emb_mul_diagonal he hι D s hs
  have h2 := emb_mul_diagonal he hι D' s' hs'
  have hZ : (fun a => if a ∈ Set.range e then (1 : L) else D' a) =
      fun a => if a ∈ Set.range e then (1 : L) else D a := by
    funext a
    by_cases ha : a ∈ Set.range e
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha, hD a ha]
  have hz : mat ((ι s)⁻¹ * t) = Matrix.diagonal (fun a => if a ∈ Set.range e then (1 : L) else D a) := by
    rw [mat_mul, ht, ← h1, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  refine ⟨(ι s)⁻¹ * t, by group, ?_, fun g => ?_⟩
  · apply mat_injective
    rw [mat_mul, hz, ← hZ, ht', ← h2]
  · apply mat_injective
    rw [mat_mul, mat_mul (ι g), hz]
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : a = b
    · subst hab
      exact mul_comm _ _
    · by_cases ha : a ∈ Set.range e
      · by_cases hb : b ∈ Set.range e
        · rw [if_pos ha, if_pos hb, one_mul, mul_one]
        · rw [(hι g).2 a b (Or.inr hb), Matrix.one_apply_ne hab, mul_zero, zero_mul]
      · rw [(hι g).2 a b (Or.inl ha), Matrix.one_apply_ne hab, mul_zero, zero_mul]
end GlobalTheory.SatakeWeyl
