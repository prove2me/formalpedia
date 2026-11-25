-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WDRep.map_N_eigenspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:54:39.274526+00:00
-- url     : https://prove2.me/submissions/0deaafdc-1748-4d06-9fc6-21046f724b1f

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
theorem _root_.solution (a : WDRep h V) {φ : Weil h} (hφ : deg φ = 1) {α : ℂ} {v : V}
    (hv : v ∈ End.eigenspace (a.ρ φ) α) :
    a.N v ∈ End.eigenspace (a.ρ φ) (((normV w : ℕ) : ℂ) * α) := by
  rw [End.mem_eigenspace_iff] at hv ⊢
  rw [a.comm_apply, hv, hφ, zpow_one, map_smul, smul_smul]
end GlobalTheory.WeilDeligne.WDRep
