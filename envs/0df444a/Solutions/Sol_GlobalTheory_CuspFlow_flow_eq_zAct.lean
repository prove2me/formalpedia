-- Prove2me | solution 1 for GlobalTheory.CuspFlow.flow_eq_zAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:50.640295+00:00
-- url     : https://prove2.me/submissions/28ce060d-ba67-46d3-bd67-859de78d77d0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CuspFlowEqTorusAction
import Theorems.Thm_GlobalTheory_CuspFlow_exists_linear
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_flowMat
import Theorems.Thm_P2M_Formalism_L2_Pj_FJ_emb_cc__a0a14d96c40b
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_emb_cc__bf4bf8966b2b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_TransvectionPeriodicity_emb_kappa


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.CuspFlow
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace GlobalTheory.CuspFlow
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ η : Fin ρ → E, (∑ a, η a • cu.e a) ∈ X.Λ → ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ), (∀ s x, X.flow (∑ a, η a • cu.e a) (fun τ => (s τ : ℂ)) x = zAct X cu (L s) x) ∧ (∀ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ → ∀ s, ∑ k, phZ X cu χ k * L s k = 2 * ∑ τ : X.Ψ, (τ.1 (hq χ η)).re * s τ) ∧ ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  intro E _ _ _ r ρ X cu hb η hη
  obtain ⟨L, hL, hZ⟩ := exists_linear X cu hb η hη
  refine ⟨L, fun s x => ?_, fun χ _ s => ?_, hZ⟩
  · funext τ
    show X.flowMat (∑ a, η a • cu.e a) τ (s τ : ℂ) * mat x τ =
      zMatC X cu.e τ.1 (∑ k, (L s k : ℂ) • (zBas X cu k).map τ.1) * mat x τ
    rw [maxCuspsA_flowMat, ← TransvectionPeriodicity.emb_kappa]
    congr 2
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mcMηc,
      Matrix.of_apply]
    exact (hL s τ a b).symm
  · simp only [phZ, prE, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hκ : τ.1 X.κ0 ≠ 0 := fun h => by
      have := X.κ0_sign τ
      rw [h] at this
      simp at this
    have key : ∑ k, τ.1 (Matrix.trace (χ.transpose * zBas X cu k) / (X.κ0 / 2)) * (L s k : ℂ) =
        2 * (τ.1 (hq χ η) * (s τ : ℂ)) := by
      have e1 : ∀ k, τ.1 (Matrix.trace (χ.transpose * zBas X cu k) / (X.κ0 / 2)) * (L s k : ℂ) =
          ∑ b, ∑ a, 2 / τ.1 X.κ0 * τ.1 (χ a b) * ((L s k : ℂ) * τ.1 (zBas X cu k a b)) := by
        intro k
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
          map_div₀, map_sum, map_mul, map_ofNat, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
        field_simp
      simp only [e1]
      rw [Finset.sum_comm]
      simp only [hq, map_sum, map_mul, Formalism.L2.Pj.FJ.emb_cc', Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (f := fun a b => 2 * (τ.1 (η a) * τ.1 (χ a b) * conj (τ.1 (η b)) * (s τ : ℂ)))]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.mul_sum, hL]
      field_simp
    have h := congrArg Complex.re key
    simpa [Complex.re_sum] using h
end GlobalTheory.CuspFlow
