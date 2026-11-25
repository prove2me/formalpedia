-- Prove2me | solution 1 for GlobalTheory.PowFix.exists_pos_pow_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:43:47.236841+00:00
-- url     : https://prove2.me/submissions/44187214-b6e1-4554-972c-fe93988f0d89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPosPowGaloisFixingFinset
import Theorems.Thm_GlobalTheory_PowFix_exists_pos_pow_apply_eq
import Theorems.Thm_GlobalTheory_PowFix_pow_apply_eq_of_apply_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.PowFix
namespace GlobalTheory.PowFix
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x := by
  intro E Ω _ _ _ _ _ σ s
  classical
  have hint : ∀ x : Ω, IsIntegral E x := fun x =>
    (Algebra.IsAlgebraic.isAlgebraic (R := E) x).isIntegral
  choose k hk0 hk using fun x : Ω => exists_pos_pow_apply_eq σ x (hint x)
  refine ⟨∏ x ∈ s, k x, Finset.prod_pos fun x _ => hk0 x, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k hx
  rw [hc, pow_mul]
  exact pow_apply_eq_of_apply_eq _ x (hk x) c
end GlobalTheory.PowFix
