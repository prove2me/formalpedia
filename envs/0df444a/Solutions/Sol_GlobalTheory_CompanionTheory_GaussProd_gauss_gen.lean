-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussProd.gauss_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:10:42.086321+00:00
-- url     : https://prove2.me/submissions/1ac766c3-d91f-44a7-a292-b91b2eca5818

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumDiagonalFactor
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussProd_chi_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussProd_trace_diag
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussProd_sum_fun_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussProd
namespace GlobalTheory.CompanionTheory.GaussProd
theorem _root_.solution {Q : Type} [CommRing Q] [Fintype Q] (τ : Q →+* Q) (χ : AddChar Q ℂ) (m n : ℕ)
    (d : Fin n → Q) (e : Fin m → Q) :
    (∑ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y)))) =
      ∏ i : Fin n, ∏ l : Fin m, ∑ w : Q, χ (e l * d i * (τ w * w)) := by
  let f : Fin n → Fin m → Q → ℂ := fun i l w => χ (e l * d i * (τ w * w))
  have hterm : ∀ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y))) =
        ∏ l, ∏ i, f i l (y l i) := by
    intro y
    rw [trace_diag, chi_sum, Finset.prod_comm (s := Finset.univ) (t := Finset.univ)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [chi_sum]
  exact (Fintype.sum_equiv Matrix.of.symm _ _ fun y => hterm y).trans (sum_fun_prod m n f)
end GlobalTheory.CompanionTheory.GaussProd
