-- Prove2me | solution 1 for GlobalTheory.Mem.An.primesAPInterval_of_tzRat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:14:35.33131+00:00
-- url     : https://prove2.me/submissions/af1d4fd6-a988-4a31-9937-1443c91af5d4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimesAPIntervalOfTzRat
import Theorems.Thm_GlobalTheory_Mem_An_tzRat_ratClass
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_shortIntervalLowerBound
import Theorems.Thm_Formalism_HermitianLattices_GlobalBoundRefinements_shortIntervalImpliesProgressions_statement
import Theorems.Thm_Formalism_HermitianLattices_GlobalBoundRefinements_shortIntervalLowerBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
namespace GlobalTheory.Mem.An
theorem _root_.solution (h : TZRat) :
    ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ PrimesAPInterval C₀ Cr cr c := by
  obtain ⟨C₀, Cr, cr, cb, h0, h1, h2, h3, H⟩ := tzRat_ratClass h
  obtain ⟨C₀', c, hC, hc, H'⟩ :=
    Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalImpliesProgressions_statement Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound C₀ Cr cr cb h0 h1 h2 h3 H
  exact ⟨C₀', Cr, cr, c, hC, h1, h2, hc, H'⟩
end GlobalTheory.Mem.An
