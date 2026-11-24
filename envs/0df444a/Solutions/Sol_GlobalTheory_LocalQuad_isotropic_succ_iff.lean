-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:10.354877+00:00
-- url     : https://prove2.me/submissions/fcb79221-df57-40f9-b1e3-b0476e821b2f

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
variable {k : Type*} [Field k]
namespace GlobalTheory.LocalQuad
theorem _root_.solution {n : ℕ} {a : Fin (n + 1) → k} :
    (∃ x : Fin (n + 1) → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) ↔
      ∃ (t : k) (z : Fin n → k), (t ≠ 0 ∨ z ≠ 0) ∧ a 0 * t ^ 2 + ∑ i, a i.succ * z i ^ 2 = 0 := by
  constructor
  · rintro ⟨x, hx, h⟩
    rw [Fin.sum_univ_succ] at h
    refine ⟨x 0, fun i => x i.succ, ?_, h⟩
    by_contra hc
    push Not at hc
    apply hx
    funext i
    refine Fin.cases hc.1 (fun j => congrFun hc.2 j) i
  · rintro ⟨t, z, hx, h⟩
    refine ⟨Fin.cons t z, ?_, by simpa [Fin.sum_univ_succ] using h⟩
    intro hc
    rcases hx with hx | hx
    · exact hx (by simpa using congrFun hc 0)
    · exact hx (funext fun i => by simpa using congrFun hc i.succ)
end GlobalTheory.LocalQuad
