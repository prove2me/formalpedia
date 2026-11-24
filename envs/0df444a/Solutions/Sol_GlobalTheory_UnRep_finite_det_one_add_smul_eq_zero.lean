-- Prove2me | solution 1 for GlobalTheory.UnRep.finite_det_one_add_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:45:05.484582+00:00
-- url     : https://prove2.me/submissions/3af2d3b7-2f70-4b31-b78a-c2569a194f20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution {E K : Type} [Field E] [Field K] (φ : E →+* K) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) : {l : E | (1 + φ l • G).det = 0}.Finite := by
  let p : Polynomial K := (1 + (Polynomial.X : Polynomial K) • G.map Polynomial.C).det
  have hp : ∀ x : K, p.eval x = (1 + x • G).det := by
    intro x
    have := (Polynomial.evalRingHom x).map_det (1 + (Polynomial.X : Polynomial K) • G.map Polynomial.C)
    rw [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring
  have hp0 : p ≠ 0 := by
    intro h
    have := hp 0
    rw [h] at this
    simp at this
  have hfin : (p.rootSet K).Finite := p.rootSet_finite K
  refine (hfin.preimage φ.injective.injOn).subset fun l hl => ?_
  simp only [Set.mem_preimage, Polynomial.mem_rootSet]
  refine ⟨hp0, ?_⟩
  rw [Polynomial.coe_aeval_eq_eval, hp]
  exact hl
end GlobalTheory.UnRep
