-- Prove2me | solution 1 for GlobalTheory.RowSpan.RowStable.component_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:11.45784+00:00
-- url     : https://prove2.me/submissions/1589c2a3-1cfd-49e7-a2b1-f1b564c32689

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_rowAct_X
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
namespace RowStable
theorem _root_.solution [Infinite k] {U : Submodule k (MvPolynomial (Letter T r n) k)} (hU : RowStable U)
    {P : MvPolynomial (Letter T r n) k} (hP : P ∈ U) (a : (Σ σ, Fin (r σ)) →₀ ℕ) :
    weightedHomogeneousComponent (fun ℓ : Letter T r n => Finsupp.single (rowOf ℓ) 1) a P ∈ U := by
  classical
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  let w := fun ℓ : Letter T r n => Finsupp.single (rowOf ℓ) 1
  let Q : MvPolynomial (Σ σ, Fin (r σ)) k :=
    ∑ m ∈ P.support, monomial (Finsupp.weight w m) (φ (monomial m (P.coeff m)))
  have hQ : Q = 0 := by
    refine MvPolynomial.funext_set (fun _ => {0}ᶜ) (fun _ => (Set.finite_singleton 0).infinite_compl) fun x hx => ?_
    let g : ∀ σ, Matrix (Fin (r σ)) (Fin (r σ)) k := fun σ => Matrix.diagonal fun i => x ⟨σ, i⟩
    have hg : ∀ σ, IsUnit (g σ).det := fun σ => by
      rw [Matrix.det_diagonal]
      exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun i _ => hx _ (Set.mem_univ _))
    have hX : ∀ ℓ : Letter T r n, rowAct g (X ℓ) = C (x (rowOf ℓ)) * X ℓ := by
      rintro ⟨σ, i, b⟩
      simp [rowAct_X, g, Matrix.diagonal_apply, apply_ite, ite_mul, rowOf]
    have hm : ∀ (m : Letter T r n →₀ ℕ) (c : k), rowAct g (monomial m c) =
        eval x (monomial (Finsupp.weight w m) (1 : k)) • monomial m c := by
      intro m c
      induction m using Finsupp.induction_linear generalizing c with
      | zero => simp [rowAct]
      | add m₁ m₂ h₁ h₂ =>
        have e1 : (monomial (m₁ + m₂) c : MvPolynomial (Letter T r n) k) = monomial m₁ c * monomial m₂ 1 := by
          rw [monomial_mul, mul_one]
        have e2 : (monomial (Finsupp.weight w (m₁ + m₂)) 1 : MvPolynomial (Σ σ, Fin (r σ)) k) =
            monomial (Finsupp.weight w m₁) 1 * monomial (Finsupp.weight w m₂) 1 := by
          rw [monomial_mul, mul_one, map_add]
        rw [e1, e2, map_mul, map_mul, h₁, h₂, smul_mul_smul_comm]
      | single ℓ e =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, hX, Finsupp.weight_single]
        simp [w, rowAct, smul_eq_C_mul, mul_pow, eval_monomial]
        ring
    have h0 := hφ _ (hU g hg P hP)
    rw [P.as_sum, map_sum, map_sum] at h0
    rw [map_zero, ← h0, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hm, map_smul, smul_eq_mul, eval_monomial, eval_monomial, one_mul, mul_comm]
  have := congrArg (coeff a) hQ
  rw [weightedHomogeneousComponent_apply, map_sum, Finset.sum_filter]
  rw [coeff_zero, coeff_sum] at this
  exact (Finset.sum_congr rfl fun m _ => by rw [coeff_monomial]).trans this
end RowStable
end GlobalTheory.RowSpan
