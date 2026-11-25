-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.VirtualTrace.trace_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:17.593535+00:00
-- url     : https://prove2.me/submissions/99acfead-30d8-4fed-bfec-38fe852d72ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEqOfTracePowersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MultiplicativeVirtualCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.VirtualTrace
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
namespace GlobalTheory.WeilDeligne.VirtualTrace
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (σ : Weil h) (k : ℕ) :
    LinearMap.trace ℂ _ ((WD.std a).2.ρ σ ^ k) = LinearMap.trace ℂ V (a.ρ σ ^ k) := by
  show LinearMap.trace ℂ _ (((Module.finBasis ℂ V).equivFun.conjAlgEquiv ℂ (a.ρ σ)) ^ k) = _
  rw [← map_pow]
  exact LinearMap.trace_conj' _ _
end GlobalTheory.WeilDeligne.VirtualTrace
