-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:24:59.682932+00:00
-- url     : https://prove2.me/submissions/0ba20716-14cb-46da-a458-d58bd8214f9f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_sum_eq_zero_of_translates
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_colGeR_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_isPat_colGe
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_unip_subset_patSet
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_patChar_mul_unip

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d j : ℕ}
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
theorem _root_.solution (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin d) K → ℂ)
    (hs : ∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) :
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  classical
  rw [colGeR_zero]
  unfold wh
  have h1 : (1 : GL (Fin d) K) ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) := by
    refine ⟨one_mem _, fun i l _ => ?_⟩
    simp [Matrix.one_apply]
  have hP := isPat_colGe d j
  have hN : ∀ v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j), ∀ u : GL (Fin d) K,
      u * v ∈ patSet K (colGe d j) ↔ u ∈ patSet K (colGe d j) := by
    intro v hv u
    have hv' : v ∈ GlobalTheory.CompanionTheory.PatGrp.patSubgroup (K := K) hP := unip_subset_patSet hv
    exact (GlobalTheory.CompanionTheory.PatGrp.patSubgroup (K := K) hP).mul_mem_cancel_right hv'
  have key := sum_eq_zero_of_translates (patSet K (colGe d j))
    (Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j)) h1 hN
    (fun u => (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹) χ
    (fun u hu v hv => by simp only [patChar_mul_unip ψ₀ hu hv]) (by simpa using hs)
  rw [key, mul_zero]
end GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
