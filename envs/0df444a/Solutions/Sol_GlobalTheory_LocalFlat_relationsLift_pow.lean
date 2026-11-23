-- Prove2me | solution 1 for GlobalTheory.LocalFlat.relationsLift_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:02.227147+00:00
-- url     : https://prove2.me/submissions/6cfb927a-5a54-4678-8814-3db6b1de0772

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_LocalFlat_range_lTensor_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open GlobalTheory.LocalFlat
variable {A : Type u} [CommRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]
namespace GlobalTheory.LocalFlat
theorem _root_.solution {π : A} (h : RelationsLift (Ideal.span {π}) M)
    (hreg : IsSMulRegular M π) (k : ℕ) : RelationsLift (Ideal.span {π} ^ k) M := by
  induction k with
  | zero =>
    intro F _ _ f x _
    refine range_lTensor_le LinearMap.id _ (by simp) ⟨x, by simp⟩
  | succ k ih =>
    intro F _ _ f x hx
    obtain ⟨x₁, hx₁⟩ := h F f x
      (Submodule.smul_mono_left (Ideal.pow_le_self k.succ_ne_zero) hx)
    let G : Submodule A (F × A) := ker (f ∘ₗ fst A F A - π • snd A F A)
    have hG : ∀ g : G, f g.1.1 = π * g.1.2 := fun g => by
      have : f g.1.1 - π * g.1.2 = 0 := g.2
      exact sub_eq_zero.mp this
    let s : G →ₗ[A] F := fst A F A ∘ₗ G.subtype
    let g : G →ₗ[A] A := snd A F A ∘ₗ G.subtype
    have hs : range s = Submodule.comap f (Ideal.span {π}) := by
      ext v
      simp only [mem_range, Submodule.mem_comap, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨_, hG y⟩
      · rintro ⟨c, hc⟩
        exact ⟨⟨(v, c), by simp [G, hc]⟩, rfl⟩
    have hx₂ : x ∈ range (s.lTensor M) := by
      rw [lTensor_range, hs]
      exact ⟨x₁, hx₁⟩
    obtain ⟨x₂, rfl⟩ := hx₂
    have hfs : f ∘ₗ s = π • g := by
      ext y
      exact hG y
    rw [← lTensor_comp_apply, hfs, lTensor_smul, LinearMap.smul_apply, map_smul, Ideal.span_singleton_pow,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨m, -, hm⟩ := hx
    rw [pow_succ', mul_smul] at hm
    obtain ⟨x₃, rfl⟩ := ih G g x₂ (by
      rw [← hreg hm]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) k)
        Submodule.mem_top)
    rw [← lTensor_comp_apply]
    refine range_lTensor_le _ _ (fun y => ?_) ⟨x₃, rfl⟩
    have := y.2
    change f (s y) ∈ Ideal.span {π} ^ (k + 1)
    rw [← comp_apply, hfs, pow_succ']
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self π) this
end GlobalTheory.LocalFlat
