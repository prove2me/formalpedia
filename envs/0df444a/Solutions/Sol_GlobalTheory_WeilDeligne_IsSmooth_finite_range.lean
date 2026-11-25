-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.IsSmooth.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:02:00.747274+00:00
-- url     : https://prove2.me/submissions/e4b417e7-140c-4462-99b4-e1dfd25a7612

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Theorems.Thm_GlobalTheory_WeilDeligne_compactSpace_Ine


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
namespace GlobalTheory.WeilDeligne
namespace IsSmooth
theorem _root_.solution {h : IsPlaceOver A w} {M : Type*} [Monoid M] {f : Weil h →* M}
    (hf : IsSmooth f) : (Set.range fun σ : Ine (F := E) A => f (ineIncl h σ)).Finite := by
  have := compactSpace_Ine (E := E) A
  have : Finite (Ine (F := E) A ⧸ (f.comp (ineIncl h)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hf
  refine (Set.finite_range (QuotientGroup.lift (f.comp (ineIncl h)).ker (f.comp (ineIncl h))
    le_rfl)).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨QuotientGroup.mk σ, rfl⟩
end IsSmooth
end GlobalTheory.WeilDeligne
