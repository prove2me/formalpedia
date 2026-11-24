-- Prove2me | solution 1 for GlobalTheory.RowSpan.harmK_le_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:17:16.812334+00:00
-- url     : https://prove2.me/submissions/d74ea238-b0c8-4b74-9d41-e2f5eb9377e9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_mem_harmK_iff
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
namespace GlobalTheory.RowSpan
theorem _root_.solution [CharZero k] (cc : T → T) (isX : T → Prop) :
    harmK r n k cc isX (fun _ => 1) ≤
      Submodule.span k (map (algebraMap ℚ k) '' (harmK r n ℚ cc isX (fun _ => 1))) := by
  classical
  intro P hP
  let B := Module.Basis.ofVectorSpace ℚ k
  let L : (k →ₗ[ℚ] ℚ) → MvPolynomial (Letter T r n) k → MvPolynomial (Letter T r n) ℚ := fun φ Q =>
    ∑ m ∈ Q.support, monomial m (φ (coeff m Q))
  have hL : ∀ φ Q m, coeff m (L φ Q) = φ (coeff m Q) := by
    intro φ Q m
    simp only [L, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [notMem_support_iff.1 hm, map_zero]
  have hLd : ∀ φ Q ℓ, pderiv ℓ (L φ Q) = L φ (pderiv ℓ Q) := by
    intro φ Q ℓ
    ext m
    rw [coeff_pderiv, hL, hL, coeff_pderiv, mul_comm, ← smul_eq_mul, ← map_smul, mul_comm (coeff _ Q), Algebra.smul_def]
    simp
  let s := P.support.biUnion fun m => (B.repr (coeff m P)).support
  have e : P = ∑ i ∈ s, B i • map (algebraMap ℚ k) (L (B.coord i) P) := by
    ext m
    simp only [coeff_sum, coeff_smul, coeff_map, hL, smul_eq_mul, Module.Basis.coord_apply]
    nth_rewrite 1 [← B.linearCombination_repr (coeff m P)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (s := s)]
    · exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    · by_cases hm : m ∈ P.support
      · exact Finset.subset_biUnion_of_mem (fun m => (B.repr (coeff m P)).support) hm
      · simp [notMem_support_iff.1 hm]
    · simp
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
  rw [mem_harmK_iff] at hP
  refine (mem_harmK_iff _ _ _).2 fun τ hτ j j' => ?_
  ext m
  simp only [hLd, coeff_sum, hL]
  rw [← map_sum, ← coeff_sum, hP τ hτ j j']
  simp
end GlobalTheory.RowSpan
