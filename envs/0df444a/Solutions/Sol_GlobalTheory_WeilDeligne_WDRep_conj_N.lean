-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WDRep.conj_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:52.295481+00:00
-- url     : https://prove2.me/submissions/f7213947-4d7a-4696-b17c-32a4dc46f094

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff

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
open GlobalTheory.WeilDeligne.WDRep
variable {h : IsPlaceOver A w}
variable {V V' V'' V''' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
  [AddCommGroup V'''] [Module ℂ V'''] [FiniteDimensional ℂ V''']
namespace GlobalTheory.WeilDeligne.WDRep
theorem _root_.solution (a : WDRep h V) (σ : Weil h) :
    a.ρ σ * a.N * a.ρ σ⁻¹ = ((normV w : ℕ) : ℂ) ^ deg σ • a.N := by
  rw [a.comm, smul_mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
end GlobalTheory.WeilDeligne.WDRep
