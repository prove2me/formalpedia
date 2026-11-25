-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WDRep.iso_zero_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:13:03.654803+00:00
-- url     : https://prove2.me/submissions/857b7fc1-9124-4da4-954b-be01d1d5db21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LpCharCompatibilities

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
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
open GlobalTheory.WeilDeligne.WDRep
namespace GlobalTheory.WeilDeligne.WDRep
theorem _root_.solution (a : WDRep h V) (c : WDRep h V') [Subsingleton V] (b : WDRep h V'') [Subsingleton V''] :
    (a.tensor c).Iso b := by
  haveI : Subsingleton (V ⊗[ℂ] V') := by
    refine ⟨fun x y => ?_⟩
    have key : ∀ z : V ⊗[ℂ] V', z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [key x, key y]
  exact ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
end GlobalTheory.WeilDeligne.WDRep
