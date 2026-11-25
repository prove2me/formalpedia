-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.isArithFrobAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:19.522487+00:00
-- url     : https://prove2.me/submissions/99d0e392-2aa3-48f2-be7c-0a4ab9ef231b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
import Theorems.Thm_GroundTheory_Global_Cyclotomic_finite_quotient
import Theorems.Thm_GroundTheory_Global_Cyclotomic_eq_of_forall_pow_eq_one
import Theorems.Thm_GroundTheory_Global_Cyclotomic_IsArithFrobAt_apply_of_pow_eq_one

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
theorem _root_.solution (hm : ¬ p ∣ m) (σ : Gal(K/ℚ)) :
    IsArithFrobAt ℤ σ P ↔ ∀ x : K, x ^ m = 1 → σ x = x ^ p := by
  refine ⟨fun hσ x hx => IsArithFrobAt.apply_of_pow_eq_one p K P hm hσ hx, fun h => ?_⟩
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : Finite (𝓞 K ⧸ P) := finite_quotient p K P
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  have : σ = τ := eq_of_forall_pow_eq_one (m := m) K fun x hx => by
    rw [h x hx, IsArithFrobAt.apply_of_pow_eq_one p K P hm hτ hx]
  rwa [this]
end GroundTheory.Global.Cyclotomic
