-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.FrobSemisimpleUnique.nilpotent_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:04:41.571156+00:00
-- url     : https://prove2.me/submissions/7683ed9a-b748-4c1d-b83c-cd37574ee635

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNilpotentZpowSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.FrobSemisimpleUnique
namespace GlobalTheory.WeilDeligne.FrobSemisimpleUnique
theorem _root_.solution {R : Type*} [Ring R] {f s : R} (v : Rˣ) (hv : IsNilpotent ((v : R) - 1))
    (hc : Commute (v : R) f) (hf : f = s * v) : IsNilpotent (f - s) ∧ Commute (f - s) s := by
  have hs : s = f * ((v⁻¹ : Rˣ) : R) := by rw [hf, Units.mul_inv_cancel_right]
  have hvs : Commute (v : R) s := by
    rw [hs]
    exact hc.mul_right (Commute.refl v).inv_right.units_val
  have h1 : f - s = s * ((v : R) - 1) := by rw [hf, mul_sub, mul_one]
  have h2 : Commute s ((v : R) - 1) := hvs.symm.sub_right (Commute.one_right _)
  rw [h1]
  exact ⟨h2.isNilpotent_mul_left hv, (Commute.refl s).mul_left h2.symm⟩
end GlobalTheory.WeilDeligne.FrobSemisimpleUnique
