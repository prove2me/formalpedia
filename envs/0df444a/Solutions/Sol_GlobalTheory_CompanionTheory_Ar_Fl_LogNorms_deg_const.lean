-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Fl.LogNorms.deg_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:31:43.065866+00:00
-- url     : https://prove2.me/submissions/7fa51510-5ef8-464d-820a-ae618a113d35

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_AdelicLattices_FactPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open NumberField
open GlobalTheory.CompanionTheory.Ar.Fl.LogNorms
variable {k : Type} [Field k] [NumberField k]
namespace GlobalTheory.CompanionTheory.Ar.Fl.LogNorms
theorem _root_.solution (t : ℝ) : deg (⟨fun _ => t, fun _ _ => 0⟩ : LogNorms k) = -t := by
  have h : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  simp [deg, finSum, Embeddings.card]
  field_simp
end GlobalTheory.CompanionTheory.Ar.Fl.LogNorms
