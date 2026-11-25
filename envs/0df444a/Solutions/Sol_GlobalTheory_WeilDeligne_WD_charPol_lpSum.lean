-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.charPol_lpSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:38:07.935828+00:00
-- url     : https://prove2.me/submissions/6e15c4e1-1ae0-4ae2-ab9f-e5976fe2342e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.WD
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} [IsAlgClosure E Ω]
variable {h : IsPlaceOver A w}
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (a b : WD h) (σ : Weil h) :
    charPol (lpSum a b) σ = charPol a σ * charPol b σ := by
  induction a using ind
  induction b using ind
  rw [lpSum_mk, charPol_mk, charPol_mk, charPol_mk, WDRep.sum_ρ, LinearMap.charpoly_prodMap]
end GlobalTheory.WeilDeligne.WD
