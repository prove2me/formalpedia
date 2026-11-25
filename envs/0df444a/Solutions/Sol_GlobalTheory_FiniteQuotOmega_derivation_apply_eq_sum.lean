-- Prove2me | solution 1 for GlobalTheory.FiniteQuotOmega.derivation_apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:12.959359+00:00
-- url     : https://prove2.me/submissions/5c513bdc-f187-4f6b-879d-45b8299fae34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JacobianSmulKaehlerEqZero
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_exists_eq_sum_X_mul
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open GlobalTheory GlobalTheory.FiniteQuotOmega
open MvPowerSeries IsLocalRing
open scoped TensorProduct
variable {T Q σ : Type*} [CommRing T] [CommRing Q] [Algebra T Q] [Fintype σ]
namespace GlobalTheory.FiniteQuotOmega
theorem _root_.solution [IsNoetherianRing Q] {M : Type*} [AddCommGroup M] [Module T M]
    [Module Q M] [Module.Finite Q M] (φ : MvPowerSeries σ T →ₐ[T] Q)
    (hφ : Function.Surjective φ) (D : Derivation T Q M) (g : MvPowerSeries σ T) :
    D (φ g) = ∑ j, φ (pderiv T j g) • D (φ (X j)) := by
  classical
  set J : Ideal Q := Ideal.jacobson ⊥ with hJ
  have hX : ∀ i, φ (X i) ∈ J := by
    intro i
    rw [hJ, Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨h, rfl⟩ := hφ y
    have : IsUnit (X i * h + 1 : MvPowerSeries σ T) := by
      rw [isUnit_iff_constantCoeff]; simp
    simpa using this.map φ
  have key : ∀ (n : ℕ) (g : MvPowerSeries σ T),
      D (φ g) - ∑ j, φ (pderiv T j g) • D (φ (X j)) ∈ (J ^ n • ⊤ : Submodule Q M) := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      obtain ⟨k, -, hk⟩ := exists_eq_sum_X_mul (n := 0) (g := g - C (constantCoeff g))
        fun d hd => by
          have : d = 0 := by
            rw [← Finsupp.degree_eq_zero_iff]; omega
          subst this
          simp
      have hg : g = C (constantCoeff g) + ∑ i, X i * k i := by rw [← hk]; ring
      have hC : ∀ c : T, D (φ (C c)) = 0 := fun c => by
        have : φ (C c) = algebraMap T Q c := φ.commutes c
        rw [this, Derivation.map_algebraMap]
      have h1 : ∀ i, ∑ j, φ (pderiv T j (X i * k i)) • D (φ (X j)) =
          φ (X i) • ∑ j, φ (pderiv T j (k i)) • D (φ (X j)) + φ (k i) • D (φ (X i)) := by
        intro i
        simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, add_smul,
          Finset.sum_add_distrib, Finset.smul_sum, mul_smul]
        congr 1
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          simp [pderiv_X_of_ne hj.symm]
        · simp
      have e : D (φ g) - ∑ j, φ (pderiv T j g) • D (φ (X j)) =
          ∑ i, φ (X i) • (D (φ (k i)) - ∑ j, φ (pderiv T j (k i)) • D (φ (X j))) := by
        generalize constantCoeff g = c at hg
        subst hg
        simp only [map_add, hC, zero_add, pderiv_C, map_sum, Finset.sum_smul]
        rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h1, map_mul, Derivation.leibniz, smul_sub]
        abel
      rw [e, pow_succ', mul_smul]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hX i) (ih _)
  rw [← sub_eq_zero, ← Submodule.mem_bot Q,
    ← Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) J le_rfl, Submodule.mem_iInf]
  exact fun n => key n g
end GlobalTheory.FiniteQuotOmega
