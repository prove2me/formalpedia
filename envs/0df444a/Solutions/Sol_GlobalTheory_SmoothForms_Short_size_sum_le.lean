-- Prove2me | solution 1 for GlobalTheory.SmoothForms.Short.size_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:51:35.666324+00:00
-- url     : https://prove2.me/submissions/134b7602-682e-4470-924d-b8af089624c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms GlobalTheory.HermClass Module Submodule NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Short
namespace GlobalTheory.SmoothForms.Short
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E]
    {V : Type} [AddCommGroup V] [Module E V] {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ}
    {ν : V → ℝ} {B : ℝ} (H : Sized h Λ N ν B) {ι : Type} (s : Finset ι) (f : ι → V) :
    ν (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := H.smul_le 0 0
    simpa [house] using this
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (H.add_le _ _).trans (by linarith)
end GlobalTheory.SmoothForms.Short
