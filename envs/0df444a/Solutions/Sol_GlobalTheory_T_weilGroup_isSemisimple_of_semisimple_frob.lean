-- Prove2me | solution 1 for GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:05:16.213981+00:00
-- url     : https://prove2.me/submissions/c5142c2c-9421-44b9-8f1d-29fb15002a78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrob
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrobStatement
import Theorems.Thm_GlobalTheory_WeilDeligne_isSemisimple_of_isSemisimple_frob


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V), IsSmooth ρ → ∀ φ : Weil h, deg φ = 1 → End.IsSemisimple (ρ φ) → ∀ σ : Weil h, End.IsSemisimple (ρ σ) := by
  first | exact @GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob | exact GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob | (intros; apply GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob <;> assumption)
end _root_.GlobalTheory.T
