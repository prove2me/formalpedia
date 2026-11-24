-- Prove2me | solution 1 for GlobalTheory.RowSpan.weight_lt_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:18:09.086537+00:00
-- url     : https://prove2.me/submissions/f6e3b427-d7a5-491d-aaeb-a65e3c16fba2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_weight_lt_mul
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
variable {σ : Type} (w : σ → ℕ)
namespace GlobalTheory.RowSpan
theorem _root_.solution (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hf : ∀ ℓ, ∀ m ∈ (f (X ℓ) - X ℓ).support, Finsupp.weight w m < w ℓ) (m : σ →₀ ℕ) :
    ∀ m' ∈ (f (monomial m 1) - monomial m 1).support, Finsupp.weight w m' < Finsupp.weight w m := by
  classical
  have hmon : ∀ m : σ →₀ ℕ, ∀ m' ∈ (monomial m (1 : k)).support, Finsupp.weight w m' ≤ Finsupp.weight w m := by
    intro m m' h
    rw [Finset.mem_singleton.1 (support_monomial_subset h)]
  have hadd : ∀ m₁ m₂ : σ →₀ ℕ,
      (∀ m' ∈ (f (monomial m₁ 1) - monomial m₁ 1).support, Finsupp.weight w m' < Finsupp.weight w m₁) →
      (∀ m' ∈ (f (monomial m₂ 1) - monomial m₂ 1).support, Finsupp.weight w m' < Finsupp.weight w m₂) →
      ∀ m' ∈ (f (monomial (m₁ + m₂) 1) - monomial (m₁ + m₂) 1).support,
        Finsupp.weight w m' < Finsupp.weight w (m₁ + m₂) := by
    intro m₁ m₂ h₁ h₂ m' hm'
    have e : f (monomial (m₁ + m₂) 1) - monomial (m₁ + m₂) 1 =
        (f (monomial m₁ 1) - monomial m₁ 1) * (f (monomial m₂ 1) - monomial m₂ 1) +
          ((f (monomial m₁ 1) - monomial m₁ 1) * monomial m₂ 1 +
            (f (monomial m₂ 1) - monomial m₂ 1) * monomial m₁ 1) := by
      have : (monomial (m₁ + m₂) 1 : MvPolynomial σ k) = monomial m₁ 1 * monomial m₂ 1 := by
        rw [monomial_mul, mul_one]
      rw [this, map_mul]
      ring
    rw [e] at hm'
    rw [map_add]
    rcases Finset.mem_union.1 (support_add hm') with h | h
    · exact weight_lt_mul w h₁ (fun m hm => (h₂ m hm).le) _ h
    · rcases Finset.mem_union.1 (support_add h) with h | h
      · exact weight_lt_mul w h₁ (hmon _) _ h
      · rw [add_comm]
        exact weight_lt_mul w h₂ (hmon _) _ h
  have hzero : ∀ m' ∈ (f (monomial 0 1) - monomial 0 1).support,
      Finsupp.weight w m' < Finsupp.weight w (0 : σ →₀ ℕ) := by
    intro m' h
    simp at h
  induction m using Finsupp.induction_linear with
  | zero => exact hzero
  | add m₁ m₂ h₁ h₂ => exact hadd _ _ h₁ h₂
  | single a e =>
    induction e with
    | zero => simpa using hzero
    | succ e ih =>
      rw [Finsupp.single_add]
      refine hadd _ _ ih ?_
      have := hf a
      rwa [Finsupp.weight_single, one_smul]
end GlobalTheory.RowSpan
