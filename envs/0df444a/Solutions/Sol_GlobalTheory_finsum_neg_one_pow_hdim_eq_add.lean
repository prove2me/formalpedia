-- Prove2me | solution 1 for GlobalTheory.finsum_neg_one_pow_hdim_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:57:42.761907+00:00
-- url     : https://prove2.me/submissions/5b9f6f19-fd7b-4719-8080-f5bad0603e87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_P2M_GlobalTheory_cohOn_subsingleton__cbacb3adb2f4
import Theorems.Thm_GlobalTheory_sum_neg_one_pow_hdim_eq_add
import Theorems.Thm_GlobalTheory_finsum_neg_one_pow_hdim_eq_sum
import Theorems.Thm_P2M_GlobalTheory_SheafLES_subsingleton__45c7e9de24f9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS
namespace GlobalTheory
theorem _root_.solution (h₁ : ∀ i, Module.Finite k (coh S.X₁ i))
    (h₃ : ∀ i, Module.Finite k (coh S.X₃ i))
    (hv₁ : ∃ N, ∀ i, N ≤ i → Subsingleton (coh S.X₁ i))
    (hv₃ : ∃ N, ∀ i, N ≤ i → Subsingleton (coh S.X₃ i)) :
    ∑ᶠ i, (-1 : ℤ) ^ i * hdim k S.X₂ i =
      ∑ᶠ i, (-1 : ℤ) ^ i * hdim k S.X₁ i + ∑ᶠ i, (-1 : ℤ) ^ i * hdim k S.X₃ i := by
  obtain ⟨N₁, hv₁⟩ := hv₁
  obtain ⟨N₃, hv₃⟩ := hv₃
  have e₁ : ∀ i, max N₁ N₃ ≤ i → Subsingleton (coh S.X₁ i) := fun i hi ↦ hv₁ i (by omega)
  have e₃ : ∀ i, max N₁ N₃ ≤ i → Subsingleton (coh S.X₃ i) := fun i hi ↦ hv₃ i (by omega)
  rw [finsum_neg_one_pow_hdim_eq_sum k _ _ e₁, finsum_neg_one_pow_hdim_eq_sum k _ _ e₃,
    finsum_neg_one_pow_hdim_eq_sum k S.X₂ (max N₁ N₃)
      fun i hi ↦ cohOn.subsingleton₂ hS ⊤ i (e₁ i hi) (e₃ i hi)]
  exact sum_neg_one_pow_hdim_eq_add k hS _ (fun i _ ↦ h₁ i) (fun i _ ↦ h₃ i) (e₁ _ le_rfl)
end GlobalTheory
