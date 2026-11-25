-- Prove2me | solution 1 for GlobalTheory.CMVal.isCond_iff_expAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:35:21.574531+00:00
-- url     : https://prove2.me/submissions/67442482-6998-47c6-9097-3145a6b3832a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EntireEqOfEqOnHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Theorems.Thm_Formalism_L2_Host_unif_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal
open Neutral.B1 (finiteSingle)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)
open Formalism.L2.Host (atFin atInf unif unif_spec IsUnitAt IsUnifAt upF aboveInf)
variable (E : Type) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}
variable {I : Type} [Fintype I]
namespace GlobalTheory.CMVal
theorem _root_.solution (χ : HChar E) {𝔣 : Ideal (𝓞 E)} (h𝔣 : 𝔣 ≠ ⊥) :
    χ.IsCond 𝔣 ↔ ∀ v, ExpAt χ v (multiplicity v.asIdeal 𝔣) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (n : ℕ), ¬ v.asIdeal ^ (n + 1) ∣ 𝔣 ↔ multiplicity v.asIdeal 𝔣 ≤ n := fun v n => by
    have hf : FiniteMultiplicity v.asIdeal 𝔣 :=
      FiniteMultiplicity.of_prime_left v.prime h𝔣
    rw [hf.pow_dvd_iff_le_multiplicity]
    omega
  constructor
  · intro h v n
    rw [h.2 v n, key]
  · intro h
    exact ⟨h𝔣, fun v n => by rw [key]; exact h v n⟩
end GlobalTheory.CMVal
