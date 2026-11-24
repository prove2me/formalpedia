-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.isOpen_convex_Om4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:01:40.483844+00:00
-- url     : https://prove2.me/submissions/8481151a-0875-4ce1-8251-503abe787f2b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_mem_Om4
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_isOpen_hp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_convex_hp
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisGal_open_convex2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (N r : ℝ) : IsOpen (Om4 N r) ∧ Convex ℝ (Om4 N r) := by
  have h := open_convex2 (Ω := {x : ℝ × ℝ | r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1})
    0 (-1) (N - 1) (-1) (-1) (2 * N - 1) r fun x => by
      simp only [affR, Set.mem_setOf_eq]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have h' := (isOpen_hp (-1) 0 (1 / 2) 0)
  have h'' := (convex_hp (-1) 0 (1 / 2) 0)
  have e : Om4 N r = {x : ℝ × ℝ | r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1} ∩
      {x | 0 < affR (-1) 0 (1 / 2) x} := by
    ext x
    rw [mem_Om4]
    simp only [affR, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨h₁, by linarith⟩
    · rintro ⟨h₁, h₂⟩; exact ⟨h₁, by linarith⟩
  rw [e]
  exact ⟨h.1.inter h', h.2.inter h''⟩
end GlobalTheory.CompanionTheory.RgEisGal
