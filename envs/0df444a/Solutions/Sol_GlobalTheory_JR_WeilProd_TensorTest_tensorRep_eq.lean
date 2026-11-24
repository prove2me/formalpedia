-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.TensorTest.tensorRep_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:10:16.617469+00:00
-- url     : https://prove2.me/submissions/0afb366f-4f4e-40e0-a260-9ff3ef681f90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProduct
import Theorems.Thm_GlobalTheory_JR_WeilProd_TensorTest_map_sum
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd GlobalTheory.JR.WeilProd.TensorTest
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
namespace GlobalTheory.JR.WeilProd.TensorTest
theorem _root_.solution {G H : Type} [Group G] [Group H] {W₁ : G → (X → ℂ) → X → ℂ}
    {W₂ : H → (Y → ℂ) → Y → ℂ} (hW₁ : IsTestRep W₁) (hW₂ : IsTestRep W₂) {ι : Type} (s : Finset ι)
    (A : ι → X → ℂ) (B : ι → Y → ℂ) (hA : ∀ j ∈ s, IsTest (A j)) (hB : ∀ j ∈ s, IsTest (B j))
    (f : X × Y → ℂ) (hf : ∀ p : X × Y, f p = ∑ j ∈ s, A j p.1 * B j p.2) (gh : G × H) :
    tensorRep W₁ W₂ gh f = fun p => ∑ j ∈ s, W₁ gh.1 (A j) p.1 * W₂ gh.2 (B j) p.2 := by
  funext p
  have h1 : ∀ u, (fun v => f (u, v)) = ∑ j ∈ s, A j u • B j := by
    intro u; funext v; rw [hf (u, v)]; simp [Finset.sum_apply, smul_eq_mul]
  have h2 : (fun u => W₂ gh.2 (fun v => f (u, v)) p.2) = ∑ j ∈ s, W₂ gh.2 (B j) p.2 • A j := by
    funext u
    rw [h1 u, map_sum hW₂ gh.2 s _ _ hB, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [smul_eq_mul, mul_comm]
  rw [tensorRep_apply, h2, map_sum hW₁ gh.1 s _ _ hA, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [smul_eq_mul, mul_comm]
end GlobalTheory.JR.WeilProd.TensorTest
