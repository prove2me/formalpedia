-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.sum_unip_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:02:52.601387+00:00
-- url     : https://prove2.me/submissions/5389a572-849c-4b34-8109-1c6e0f1fd941

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_unip_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspVan
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open Classical
namespace GlobalTheory.CompanionTheory.TyFin.CuspVan
theorem _root_.solution {t : ℕ} (bb : ι → Fin t) (hs : Function.Surjective bb) (ht : 2 ≤ t)
    (τ : FDRep ℂ (GL ι K)) (hτ : IsCuspidal K τ) :
    ∑ v ∈ Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb), τ.ρ v = 0 := by
  set Y := Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb) with hY
  apply LinearMap.ext
  intro w
  apply hτ t bb hs ht
  intro y hy
  have himg : Y.image (fun v => y * v) = Y := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact unip_mul bb hy hv
    · rw [Finset.card_image_of_injective _ (mul_right_injective y)]
  have h1 : ∑ v ∈ Y, τ.ρ (y * v) = ∑ v ∈ Y, τ.ρ v := by
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (fun a _ b _ h => mul_right_injective y h)]
  rw [LinearMap.sum_apply, map_sum, ← LinearMap.sum_apply, ← h1, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul]
  rfl
end GlobalTheory.CompanionTheory.TyFin.CuspVan
