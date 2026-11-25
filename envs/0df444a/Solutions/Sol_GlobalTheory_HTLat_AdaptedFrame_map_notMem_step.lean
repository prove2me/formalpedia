-- Prove2me | solution 1 for GlobalTheory.HTLat.AdaptedFrame.map_notMem_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:47:33.203819+00:00
-- url     : https://prove2.me/submissions/236faf2c-bcee-43a8-9b10-dc8533bf62c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Theorems.Thm_GlobalTheory_HTLat_step_mono
import Theorems.Thm_GlobalTheory_HTLat_mem_step_succ
import Theorems.Thm_GlobalTheory_HTLat_map_step
import Theorems.Thm_GlobalTheory_HTLat_AdaptedFrame_notMem_step
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct NNReal NumberField Pointwise
open GlobalTheory.EigenSplit
open GlobalTheory GlobalTheory.HTLat
variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
variable {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U'] [IsScalarTower O C U']
namespace GlobalTheory.HTLat
namespace AdaptedFrame
theorem _root_.solution (al : U →ₗ[C] U') {U₁ : Submodule C U} {j : ℕ}
    (F : AdaptedFrame (LinearMap.ker al ⊓ U₁) U₁ N j) (i : Fin N) (hi : j ≤ i) :
    (al ∘ F.f) i ∉ step C (al ∘ F.f) i := by
  rw [← map_step]
  rintro ⟨y, hy, e⟩
  have hU : ∀ k, k ≤ N → step C F.f k ≤ U₁ := fun k hk => (step_mono F.f hk).trans F.step_N.le
  have h1 : F.f i - y ∈ step C F.f j := by
    rw [F.step_j]
    refine ⟨?_, U₁.sub_mem (hU _ i.2 (mem_step_succ F.f i)) (hU _ i.2.le hy)⟩
    change al (F.f i - y) = 0
    rw [map_sub, e]
    exact sub_self _
  exact F.notMem_step i (by simpa using Submodule.add_mem _ (step_mono F.f hi h1) hy)
end AdaptedFrame
end GlobalTheory.HTLat
