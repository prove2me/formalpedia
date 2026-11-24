-- Prove2me | solution 1 for GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:06.405972+00:00
-- url     : https://prove2.me/submissions/7c1090c4-b66b-4fd7-bc76-5be1f1902320

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDotProductMulVecEqOfLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (r k : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε : Fin k → Fin r → ℚ), Mq.det ≠ 0 →
      LinearIndependent ℚ ε → ∀ t : Fin k → ℚ,
      ∃ x : Fin r → ℚ, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = t i := by
  intro r k Mq ε hM hε t
  have hU : IsUnit Mq := (Matrix.isUnit_iff_isUnit_det Mq).2 (Ne.isUnit hM)
  have hinj : Function.Injective Mq.mulVecLin := Matrix.mulVec_injective_iff_isUnit.2 hU
  have hli : LinearIndependent ℚ (fun i => Mq *ᵥ ε i) :=
    hε.map' Mq.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  let U : Matrix (Fin k) (Fin r) ℚ := Matrix.of fun i => Mq *ᵥ ε i
  have hrow : LinearIndependent ℚ U.row := hli
  have hrank : U.rank = Fintype.card (Fin k) := hrow.rank_matrix
  have htop : LinearMap.range U.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    exact hrank
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 htop t
  refine ⟨x, fun i => ?_⟩
  rw [dotProduct_comm, ← hx]
  rfl
end GlobalTheory
