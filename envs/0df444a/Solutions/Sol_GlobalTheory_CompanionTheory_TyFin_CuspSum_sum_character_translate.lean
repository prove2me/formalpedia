-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspSum.sum_character_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:04:17.325032+00:00
-- url     : https://prove2.me/submissions/64cfa2db-b9e0-49f3-8c7e-7c646316c8a1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZero
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspSum_sum_rho_unip
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspSum_twoBlock_surjective

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
namespace GlobalTheory.CompanionTheory.TyFin.CuspSum
theorem _root_.solution :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ j → j < d → IsCuspidal K τ → ∀ u : GL (Fin d) K,
    (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.character (u * v) else 0) = 0 := by
  intro K _ _ _ d j τ hj hjd hc u
  classical
  have h0 := sum_rho_unip τ hc (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) (twoBlock_surjective hj hjd) le_rfl
  have h1 : LinearMap.trace ℂ τ (τ.ρ u * ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.ρ v else 0) = 0 := by
    rw [h0, mul_zero, map_zero]
  rw [Finset.mul_sum, map_sum] at h1
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) h1
  split_ifs
  · rw [FDRep.character, map_mul]
  · rw [mul_zero, map_zero]
end GlobalTheory.CompanionTheory.TyFin.CuspSum
