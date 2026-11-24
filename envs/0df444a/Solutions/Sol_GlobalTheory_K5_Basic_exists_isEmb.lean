-- Prove2me | solution 1 for GlobalTheory.K5.Basic.exists_isEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:24:52.741535+00:00
-- url     : https://prove2.me/submissions/ed02b023-d724-46d9-b423-fdd08f124c20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
import Theorems.Thm_GlobalTheory_K5_Basic_qq_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
namespace GlobalTheory.K5.Basic
theorem _root_.solution (T : Tower p Ω) (n : ℕ) : ∃ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι := by
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine ⟨Ideal.Quotient.liftₐ (towerIdeal p n) (aevalTower (aeval (T.ζ n)) (T.qq n)) ?_, ?_, ?_⟩
  · intro a ha
    have : towerIdeal p n ≤
        RingHom.ker (aevalTower (aeval (T.ζ n) : (O0 p)[X] →ₐ[O0 p] Ω) (T.qq n)) := by
      rw [towerIdeal, Ideal.span_le]
      rintro b (rfl | rfl)
      · have := (T.prim n).isRoot_cyclotomic hpos
        simp only [SetLike.mem_coe, RingHom.mem_ker, aevalTower_C]
        rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
        exact this
      · simp [RingHom.mem_ker, qq_pow T]
    exact this ha
  · show aevalTower (aeval (T.ζ n) : (O0 p)[X] →ₐ[O0 p] Ω) (T.qq n) (C X) = _
    simp
  · show aevalTower (aeval (T.ζ n) : (O0 p)[X] →ₐ[O0 p] Ω) (T.qq n) X = _
    simp
end GlobalTheory.K5.Basic
