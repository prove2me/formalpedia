-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.eq_of_forall_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:00.650089+00:00
-- url     : https://prove2.me/submissions/45500c1b-eddd-47e4-99f8-5ab11350bdc0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]
variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution {σ τ : Gal(K/ℚ)}
    (h : ∀ x : K, x ^ m = 1 → σ x = τ x) : σ = τ := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ K
  apply (IsCyclotomicExtension.Rat.galEquivZMod m K).injective
  have h₁ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq m K σ hζ.pow_eq_one
  have h₂ := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq m K τ hζ.pow_eq_one
  rw [h _ hζ.pow_eq_one, h₂] at h₁
  rw [Units.ext_iff]
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h₁.symm)
end GroundTheory.Global.Cyclotomic
