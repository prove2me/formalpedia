-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.existsUnique_isArithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:17:18.858843+00:00
-- url     : https://prove2.me/submissions/319f429a-8b58-4d55-ba30-a89fdadd2cdf

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
theorem _root_.solution (hm : ¬ p ∣ m) : ∃! σ : Gal(K/ℚ), IsArithFrobAt ℤ σ P := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  have : Finite (𝓞 K ⧸ P) := finite_quotient p K P
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(K/ℚ) P
  refine ⟨τ, hτ, fun σ hσ => eq_of_forall_pow_eq_one (m := m) K fun x hx => ?_⟩
  rw [IsArithFrobAt.apply_of_pow_eq_one p K P hm hσ hx,
    IsArithFrobAt.apply_of_pow_eq_one p K P hm hτ hx]
end GroundTheory.Global.Cyclotomic
