-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.IsPurePair.of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:29:41.799432+00:00
-- url     : https://prove2.me/submissions/4ed6c2c6-14fb-4a37-aa4f-29f466588311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Theorems.Thm_GlobalTheory_WeilDeligne_map_absSpace_le
import Theorems.Thm_GlobalTheory_WeilDeligne_mem_absSpace_iff
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
namespace GlobalTheory.WeilDeligne
namespace IsPurePair
theorem _root_.solution {q : ℝ} {f N : End ℂ V} {g M : End ℂ V'} (e : V ≃ₗ[ℂ] V')
    (he : ∀ v, e (f v) = g (e v)) (hN : ∀ v, e (N v) = M (e v)) (hp : IsPurePair q f N) :
    IsPurePair q g M := by
  have hpow : ∀ (i : ℕ) v, e ((N ^ i) v) = (M ^ i) (e v) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro v; rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, ih, hN]
  refine ⟨?_, fun i => ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩⟩
  · rw [eq_top_iff, ← LinearEquiv.range e, LinearMap.range_eq_map, ← hp.1, Submodule.map_iSup]
    exact iSup_mono fun i => map_absSpace_le e.toLinearMap he _
  · obtain ⟨v, rfl⟩ := e.surjective v
    rw [SetLike.mem_coe, mem_absSpace_iff e he] at hv
    rw [SetLike.mem_coe, ← hpow, mem_absSpace_iff e he]
    exact (hp.2 i).1 hv
  · obtain ⟨v, rfl⟩ := e.surjective v
    obtain ⟨v', rfl⟩ := e.surjective v'
    rw [SetLike.mem_coe, mem_absSpace_iff e he] at hv hv'
    rw [← hpow, ← hpow] at hvv
    rw [(hp.2 i).2.1 hv hv' (e.injective hvv)]
  · obtain ⟨v, rfl⟩ := e.surjective v
    rw [SetLike.mem_coe, mem_absSpace_iff e he] at hv
    obtain ⟨u, hu, rfl⟩ := (hp.2 i).2.2 hv
    exact ⟨e u, (mem_absSpace_iff e he _ u).mpr hu, (hpow i u).symm⟩
end IsPurePair
end GlobalTheory.WeilDeligne
