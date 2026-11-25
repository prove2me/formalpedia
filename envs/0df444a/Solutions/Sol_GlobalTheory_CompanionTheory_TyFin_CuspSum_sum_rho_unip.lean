-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_rho_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:49.462926+00:00
-- url     : https://prove2.me/submissions/b5a4d930-bca3-4c77-864d-6902185a9865

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZero
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspSum_unip_mul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspSum_unip_inv_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspSum
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
open Classical
namespace GlobalTheory.CompanionTheory.TyFin.CuspSum
theorem _root_.solution (τ : FDRep ℂ (GL ι K)) (hc : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ)
    (b : ι → Fin s) (hb : Function.Surjective b) (hs : 2 ≤ s) :
    (∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0) = 0 := by
  set P : Module.End ℂ τ := ∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0
    with hP
  have hfix : ∀ a ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b, τ.ρ a * P = P := by
    intro a ha
    rw [hP, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft a)
      (fun v : GL ι K => if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hiff : a * v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b ↔ v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
      refine ⟨fun h => ?_, unip_mul_mem b ha⟩
      simpa using unip_mul_mem b (unip_inv_mem b ha) h
    simp only [Equiv.coe_mulLeft, hiff]
    split_ifs
    · rw [map_mul]
    · rw [mul_zero]
  refine LinearMap.ext fun w => ?_
  exact hc s b hb hs (P w) fun a ha => LinearMap.congr_fun (hfix a ha) w
end GlobalTheory.CompanionTheory.TyFin.CuspSum
