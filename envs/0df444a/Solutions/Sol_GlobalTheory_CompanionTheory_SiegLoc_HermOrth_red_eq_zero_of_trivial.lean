-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_eq_zero_of_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:14.09242+00:00
-- url     : https://prove2.me/submissions/99959b5c-02ca-4a11-a8ad-0e915434f62c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_add__abfcc11f156d
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_cT_single__6160197039d8
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SiegLoc_HermOrth_trace_single_mul__b40bc346e0d6
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_trace_nondeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.HermOrth
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.HermOrth
theorem _root_.solution {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ)
    (n k : ℕ) (y : Matrix (Fin n) (Fin n) R) (hy : cT σ y = y)
    (h : ∀ b : Matrix (Fin n) (Fin n) R, cT σ b = b →
      ψ k (Ideal.Quotient.mk _ (Matrix.trace (b * y))) = 1) :
    red ϖ k y = 0 := by
  have hσσ : ∀ a, σ (σ a) = a := hR.1
  ext i j
  simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, Matrix.zero_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply GlobalTheory.CompanionTheory.SiegLoc.trace_nondeg hR hψ k (y i j)
  intro t
  have hyji : σ (y i j) = y j i := by
    have hentry := congrFun (congrFun hy j) i
    simpa [PositivityTheory.PfSWUS.Loc.cT] using hentry
  have hb : PositivityTheory.PfSWUS.Loc.cT σ (Matrix.single j i t + Matrix.single i j (σ t)) =
      Matrix.single j i t + Matrix.single i j (σ t) := by
    rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single',
      hσσ, add_comm]
  have htr := h _ hb
  rw [Matrix.add_mul, Matrix.trace_add, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul',
    GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul'] at htr
  rw [map_mul σ, hyji]
  exact htr
end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
