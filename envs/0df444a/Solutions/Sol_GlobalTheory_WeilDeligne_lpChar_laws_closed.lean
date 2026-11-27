-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.lpChar_laws_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:01.251912+00:00
-- url     : https://prove2.me/submissions/ddc0dbe8-15e9-4fe2-980a-d56376ee4e8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LpCharCompatibilities
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_laws

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
namespace GlobalTheory.WeilDeligne
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (a b c : WD h) (s : ℝ),
    (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) ∧
    (a.lpTw s).lpChar c = (a.lpChar c).lpTw s ∧
    a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s ∧
    (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) ∧
    (WD.lpZero h).lpChar c = WD.lpZero h ∧
    (c.unr → c.lpDim = 1 → c.frobEig = {1} → a.lpChar c = a) :=
  fun _ _ _ _ _ _ _ _ _ _ a b c s => WD.lpChar_laws a b c s
end GlobalTheory.WeilDeligne
