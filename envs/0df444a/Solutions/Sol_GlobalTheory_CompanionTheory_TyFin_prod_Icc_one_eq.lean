-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.prod_Icc_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:11:31.540939+00:00
-- url     : https://prove2.me/submissions/a3223e43-56bf-4188-b7aa-02490b60737f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimensionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquarefreeDimensionFormula
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution (f : ℕ → ℤ) (d : ℕ) (h : 1 ≤ d) :
    ∏ i ∈ Finset.Icc 1 d, f i = (∏ i ∈ Finset.Ico 1 d, f i) * f d := by
  have e : Finset.Icc 1 d = Finset.Ico 1 (d + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [e, Finset.prod_Ico_succ_top h]
end GlobalTheory.CompanionTheory.TyFin
