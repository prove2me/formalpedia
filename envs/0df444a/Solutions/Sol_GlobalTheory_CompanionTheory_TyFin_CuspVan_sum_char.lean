-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.sum_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:56.434324+00:00
-- url     : https://prove2.me/submissions/7ae22df3-28ba-4614-ad11-29091eb318e9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_sum_unip_rho

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
    (τ : FDRep ℂ (GL ι K)) (hτ : IsCuspidal K τ) (g : GL ι K) :
    ∑ v ∈ Finset.univ.filter (fun v : GL ι K => v ∈ unip K bb), τ.character (g * v) = 0 := by
  have h := congrArg (fun P => LinearMap.trace ℂ τ (τ.ρ g * P)) (sum_unip_rho bb hs ht τ hτ)
  simp only [mul_zero, map_zero, Finset.mul_sum, map_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [FDRep.character, map_mul]
end GlobalTheory.CompanionTheory.TyFin.CuspVan
