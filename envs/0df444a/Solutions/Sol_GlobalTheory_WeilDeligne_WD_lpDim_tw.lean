-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.lpDim_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:38:19.393792+00:00
-- url     : https://prove2.me/submissions/d3867d75-0f4f-47d2-af1d-4cbaab90b752

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.WD
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} [IsAlgClosure E Ω]
variable {h : IsPlaceOver A w}
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (a : WD h) (s : ℝ) : lpDim (lpTw a s) = lpDim a := by
  induction a using ind
  rw [lpTw_mk, lpDim_mk, lpDim_mk]
end GlobalTheory.WeilDeligne.WD
