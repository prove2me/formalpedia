-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.isTestRep_tensorRep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:26:04.356797+00:00
-- url     : https://prove2.me/submissions/70f093c7-a361-4066-a35c-014bbf060e61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_smul
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_sum
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_map_sum
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_mul_prod
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_fibre
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_isTest_sum_fn
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_decomp
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_tensorRep_eq
import Theorems.Thm_GlobalTheory_JR_WeilProd_tensorRep_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilProd Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd
open TensorTest
namespace GlobalTheory.JR.WeilProd
theorem _root_.solution {G H X Y : Type} [Group G] [Group H] [TopologicalSpace X] [TopologicalSpace Y]
    (W₁ : G → (X → ℂ) → X → ℂ) (W₂ : H → (Y → ℂ) → Y → ℂ) :
    IsTestRep W₁ → IsTestRep W₂ → IsTestRep (tensorRep W₁ W₂) ∧ ∀ f : X × Y → ℂ, IsTest f →
      (∀ u, IsTest (fun v => f (u, v))) ∧ ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
  intro hW₁ hW₂
  have hslice : ∀ f : X × Y → ℂ, IsTest f → ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y) := by
    intro f hf h y
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have e : (fun u => W₂ h (fun v => f (u, v)) y) = ∑ φ ∈ s, W₂ h φ y • a φ := by
      funext u
      have h1 : (fun v => f (u, v)) = ∑ φ ∈ s, a φ u • φ := by
        funext v; rw [hfs (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
      rw [h1, map_sum hW₂ h s (fun φ => a φ u) (fun φ => φ) hb, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun φ _ => ?_
      simp [smul_eq_mul, mul_comm]
    rw [e]
    exact isTest_sum s _ fun φ hφ => isTest_smul _ (ha φ hφ)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun f hf => ⟨isTest_fibre hf, hslice f hf⟩⟩
  · intro gh f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh]
    exact isTest_sum_fn s _ fun φ hφ => isTest_mul_prod (hW₁.1 _ _ (ha φ hφ)) (hW₂.1 _ _ (hb φ hφ))
  · intro f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs 1]
    funext p
    rw [hfs p]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_one, Prod.snd_one]
    rw [hW₁.2.1 _ (ha φ hφ), hW₂.2.1 _ (hb φ hφ)]
  · intro gh gh' f hf
    obtain ⟨s, a, ha, hb, hfs⟩ := decomp hf
    have hs' : ∀ p, tensorRep W₁ W₂ gh' f p = ∑ φ ∈ s, W₁ gh'.1 (a φ) p.1 * W₂ gh'.2 φ p.2 := fun p => by
      rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs gh']
    rw [tensorRep_eq hW₁ hW₂ s a (fun φ => φ) ha hb f hfs (gh * gh'),
      tensorRep_eq hW₁ hW₂ s (fun φ => W₁ gh'.1 (a φ)) (fun φ => W₂ gh'.2 φ) (fun φ hφ => hW₁.1 _ _ (ha φ hφ))
        (fun φ hφ => hW₂.1 _ _ (hb φ hφ)) _ hs' gh]
    funext p
    refine Finset.sum_congr rfl fun φ hφ => ?_
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [hW₁.2.2.1 _ _ _ (ha φ hφ), hW₂.2.2.1 _ _ _ (hb φ hφ)]
  · intro gh c f f' hf hf'
    funext p
    have e2 : (fun u => W₂ gh.2 (fun v => (c • f + f') (u, v)) p.2) =
        c • (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) + (fun u => W₂ gh.2 (fun v => f' (u, v)) p.2) := by
      funext u
      show W₂ gh.2 (c • (fun v => f (u, v)) + fun v => f' (u, v)) p.2 = _
      rw [hW₂.2.2.2 gh.2 c _ _ (isTest_fibre hf u) (isTest_fibre hf' u)]
      rfl
    rw [tensorRep_apply, e2, hW₁.2.2.2 gh.1 c _ _ (hslice f hf _ _) (hslice f' hf' _ _)]
    rfl
end GlobalTheory.JR.WeilProd
