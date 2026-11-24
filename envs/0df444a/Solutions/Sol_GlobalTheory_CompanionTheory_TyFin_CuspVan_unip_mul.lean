-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.unip_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:44:14.621505+00:00
-- url     : https://prove2.me/submissions/7b02e615-f8f9-46a0-a588-bbded6e9b776

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing

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
namespace GlobalTheory.CompanionTheory.TyFin.CuspVan
theorem _root_.solution {s : ℕ} (b : ι → Fin s) {x y : GL ι K} (hx : x ∈ unip K b) (hy : y ∈ unip K b) :
    x * y ∈ unip K b := by
  refine ⟨mul_mem hx.1 hy.1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hx.2 i i rfl, if_pos rfl, one_mul]
    exact hy.2 i j hij
  · intro k _ hk
    rcases lt_trichotomy (b k) (b i) with h | h | h
    · rw [hx.1.1 i k h, zero_mul]
    · rw [hx.2 i k h.symm, if_neg (Ne.symm hk), zero_mul]
    · rw [hy.1.1 k j (hij ▸ h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
end GlobalTheory.CompanionTheory.TyFin.CuspVan
