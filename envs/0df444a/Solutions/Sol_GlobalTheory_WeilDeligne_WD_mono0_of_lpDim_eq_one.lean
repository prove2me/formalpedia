-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.mono0_of_lpDim_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:37:01.92764+00:00
-- url     : https://prove2.me/submissions/a3e9ab35-bd4f-4d8a-a5f4-828251a00c02

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
theorem _root_.solution {χ : WD h} (hχ : lpDim χ = 1) : mono0 χ := by
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff]
    have h1 := b.nilpotent.charpoly_eq_X_pow_finrank
    have h2 := LinearMap.aeval_self_charpoly b.N
    rwa [h1, hχ, pow_one, aeval_X] at h2
end GlobalTheory.WeilDeligne.WD
