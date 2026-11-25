-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.exists_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:10:46.927798+00:00
-- url     : https://prove2.me/submissions/e1b0942c-2d92-4f71-9c9b-bff358d783cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_quotientMk_eq

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
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]
open GlobalTheory.WeilDeligne.WD
variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (x : WD h) : ∃ (n : ℕ) (a : WDRep h (Fin n → ℂ)), mk a = x := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  exact ⟨a.1, a.2, (quotientMk_eq a).symm⟩
end GlobalTheory.WeilDeligne.WD
