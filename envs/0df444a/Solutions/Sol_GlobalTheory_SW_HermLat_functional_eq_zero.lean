-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.functional_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:44:33.181854+00:00
-- url     : https://prove2.me/submissions/1416ff15-807d-49af-975e-9e916b452a7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual
import Theorems.Thm_GlobalTheory_SW_HermLat_cc_cc
import Theorems.Thm_GlobalTheory_SW_HermLat_indep
import Theorems.Thm_GlobalTheory_SW_Base_map_cc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermLat
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.HermLat
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {N : ℕ}
    (L : CM Ψ N N →ₗ[ℂ] ℂ) (h : ∀ X : HermSub E N, L (fun τ => X.1.map τ.1) = 0) : L = 0 := by
  have key : ∀ (τ : Ψ) (a b : Fin N), L (Pi.single τ (Matrix.single a b 1)) = 0 := by
    intro τ a b
    have := indep hΨ (fun τ => L (Pi.single τ (Matrix.single a b 1)))
      (fun τ => L (Pi.single τ (Matrix.single b a 1))) (fun x => by
        have hm : Matrix.single a b x + Matrix.single b a (cc x) ∈ HermSub E N := by
          show ccT _ = _
          ext k l
          simp only [ccT, transpose_apply, map_apply, Matrix.add_apply, Matrix.single_apply, cc_add,
            apply_ite cc, cc_cc, cc_zero, and_comm]
          rw [add_comm]
        rw [← h ⟨_, hm⟩]
        simp only [← smul_eq_mul, ← map_smul, ← map_add, ← map_sum]
        congr 1
        funext σ
        rw [Finset.sum_apply, Finset.sum_eq_single σ]
        · ext k l
          simp [Matrix.single_apply, apply_ite σ.1, Base.map_cc]
        · intro τ _ hτ
          simp [Pi.single_eq_of_ne hτ.symm]
        · simp)
    exact congrFun this τ
  refine LinearMap.pi_ext fun τ Z => ?_
  have hZ : (Pi.single τ Z : CM Ψ N N) =
      ∑ a, ∑ b, Z a b • (Pi.single τ (Matrix.single a b 1) : CM Ψ N N) := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single,
        smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single Z
    · simp [Finset.sum_apply, Pi.single_eq_of_ne hσ]
  rw [hZ]
  simp only [map_sum, map_smul, key, smul_zero, Finset.sum_const_zero]
  simp
end GlobalTheory.SW.HermLat
