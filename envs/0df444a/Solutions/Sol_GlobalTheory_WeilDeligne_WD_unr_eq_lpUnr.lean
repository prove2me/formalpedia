-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.unr_eq_lpUnr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:21:47.645897+00:00
-- url     : https://prove2.me/submissions/7c7e170e-4a60-4c1a-869c-4048529d833a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
import Theorems.Thm_GlobalTheory_WeilDeligne_Unram_exists_diag
import Theorems.Thm_GlobalTheory_WeilDeligne_Unram_diag_eq_diag
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpUnr_spec
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_frobEig_ne_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_frobEig_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne.WD
open Unram
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (a : WD h) (ha : unr a) : a = lpUnr h (frobEig a) := by
  classical
  have h1 := (lpUnr_spec (h := h) _ (frobEig_ne_zero a ha)).2.1
  obtain ⟨n, c, hc⟩ := exists_diag ha
  rw [lpUnr] at h1 ⊢
  refine hc.trans (diag_eq_diag ?_)
  rw [← frobEig_diag (h := h), ← frobEig_diag (h := h), h1, hc]
end GlobalTheory.WeilDeligne.WD
