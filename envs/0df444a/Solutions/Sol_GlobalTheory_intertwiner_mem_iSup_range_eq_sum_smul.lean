-- Prove2me | solution 1 for GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:03:56.452606+00:00
-- url     : https://prove2.me/submissions/667d6ad5-b604-4ea2-91ec-24471e9adc6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwinerMemISupRangeEqSumSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Representation
namespace GlobalTheory
theorem _root_.solution (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hS : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id)
    (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ)
    (hinj : Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)))
    (ψ : π.IntertwiningMap ρ)
    (hψ : LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap) :
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  classical
  let Φ : (Fin m → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
  have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by
    intro w; simp [Φ, LinearMap.sum_apply]
  have hΦinj : Function.Injective Φ := by
    intro a b h; apply hinj; simpa [hΦ] using h
  have hle : (⨆ j, LinearMap.range (φ j).toLinearMap) ≤ LinearMap.range Φ := by
    refine iSup_le fun j => ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Pi.single j n, ?_⟩
    rw [hΦ]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hmem : ∀ n, ψ.toLinearMap n ∈ LinearMap.range Φ := fun n =>
    hle (hψ ⟨n, rfl⟩)
  let e := LinearEquiv.ofInjective Φ hΦinj
  let Wm : N →ₗ[ℂ] (Fin m → N) := e.symm.toLinearMap ∘ₗ ψ.toLinearMap.codRestrict _ hmem
  have hW : ∀ n, Φ (Wm n) = ψ n := by
    intro n
    simp only [Wm, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 : e (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ⟨ψ.toLinearMap n, hmem n⟩ := e.apply_symm_apply _
    have h3 := congrArg Subtype.val h2
    change Φ (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ψ n
    rw [← LinearEquiv.ofInjective_apply Φ (h := hΦinj)]
    exact h3
  have hWg : ∀ g n, Wm (π g n) = fun j => π g (Wm n j) := by
    intro g n
    apply hΦinj
    rw [hW, hΦ, ψ.isIntertwining, ← hW, hΦ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(φ j).isIntertwining]
  have hc : ∀ j, ∃ c : ℂ, ∀ n, Wm n j = c • n := by
    intro j
    let θ : π.IntertwiningMap π :=
      (LinearMap.proj j ∘ₗ Wm).intertwiningMap_of_isIntertwiningMap π π (by
        intro g v
        simp [hWg])
    obtain ⟨c, hc⟩ := hS θ
    refine ⟨c, fun n => ?_⟩
    have h1 : Wm n j = θ.toLinearMap n := rfl
    rw [h1, hc]
    simp
  choose c hc using hc
  refine ⟨c, fun n => ?_⟩
  rw [← hW, hΦ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, map_smul]
end GlobalTheory
