-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.hconv_biinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:01.959828+00:00
-- url     : https://prove2.me/submissions/4bbefd2a-6459-4eaa-96e8-fd2c3bdb0e5c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_finsum_out_translate
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_isHk_right
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_isHk_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeMul
theorem _root_.solution {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {k₁ k₂ : GL ι F} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (g : GL ι F) :
    hconv K e₁ e₂ (k₁ * g * k₂) = hconv K e₁ e₂ g := by
  have hφ : ∀ x, ∀ k ∈ K, (fun y => e₁ y * e₂ (y⁻¹ * g)) (x * k) = (fun y => e₁ y * e₂ (y⁻¹ * g)) x := by
    intro x k hk'
    show e₁ (x * k) * e₂ ((x * k)⁻¹ * g) = e₁ x * e₂ (x⁻¹ * g)
    rw [isHk_right h₁ x hk', mul_inv_rev, mul_assoc, isHk_left h₂ _ (K.inv_mem hk')]
  have ht := finsum_out_translate K (fun y => e₁ y * e₂ (y⁻¹ * g)) hφ k₁⁻¹
  unfold hconv
  rw [← ht]
  refine finsum_congr fun q => ?_
  show e₁ q.out * e₂ (q.out⁻¹ * (k₁ * g * k₂)) = e₁ (k₁⁻¹ * q.out) * e₂ ((k₁⁻¹ * q.out)⁻¹ * g)
  rw [isHk_left h₁ _ (K.inv_mem hk₁), ← mul_assoc, isHk_right h₂ _ hk₂]
  simp [mul_assoc]
end GlobalTheory.CompanionTheory.HeckeMul
