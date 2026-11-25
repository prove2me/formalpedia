-- Prove2me | solution 1 for GlobalTheory.CuspFlow.exists_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:31.525688+00:00
-- url     : https://prove2.me/submissions/704db440-17af-4a26-b3fb-2d3851a36818

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CuspFlowEqTorusAction
import Theorems.Thm_GlobalTheory_CuspFlow_exists_int_coords
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply
import Theorems.Thm_P2M_Formalism_L2_Pj_FJ_emb_cc__a0a14d96c40b
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_EmbeddingHermitianPairs_emb_cc__bf4bf8966b2b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlowMeanContinuity_exists_basis


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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) :
    ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ),
      (∀ (s : X.Ψ → ℝ) (τ : X.Ψ) (a b : Fin ρ), ∑ k, (L s k : ℂ) * τ.1 (zBas X cu k a b) =
        τ.1 X.κ0 * (s τ : ℂ) * (τ.1 (η a) * conj (τ.1 (η b)))) ∧
      ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  obtain ⟨ω, hω⟩ := FlowMeanContinuity.exists_basis X 0
  have hωp : ∀ j, ω j ∈ X.periods 0 := fun j => by
    have : ω j ∈ RealEmbeddingCharacters.perL X 0 := hω ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose a ha hai hae using fun j => (RealEmbeddingCharacters.mem_periods_iff X 0 _).mp (hωp j)
  choose c hc using fun j => exists_int_coords X cu hb η hη (a j) (ha j) (hai j)
  set n0 : ℕ := X.chiOrd 0 with hn0
  have hn0pos : (n0 : ℝ) ≠ 0 := by
    have := RealEmbeddingCharacters.chiOrd_pos X 0
    positivity
  let L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ) := ω.constr ℝ fun j k => (n0 : ℝ) * (c j k : ℝ)
  have hL : ∀ j k, L (ω j) k = (n0 : ℝ) * (c j k : ℝ) := fun j k => by
    simp only [L, Module.Basis.constr_basis]
  refine ⟨L, fun s τ i i' => ?_, fun la p hp k => ?_⟩
  · have hj : ∀ j, ∑ k, (L (ω j) k : ℂ) * τ.1 (zBas X cu k i i') =
        τ.1 X.κ0 * (ω j τ : ℂ) * (τ.1 (η i) * conj (τ.1 (η i'))) := by
      intro j
      have h1 := congrArg (fun M : Matrix (Fin ρ) (Fin ρ) E => τ.1 (M i i')) (hc j)
      simp only [Matrix.sum_apply, Matrix.smul_apply] at h1
      simp only [map_sum, mcMη, Matrix.of_apply,
        smul_eq_mul, zsmul_eq_mul, map_mul, map_intCast, map_natCast,
        Formalism.L2.Pj.FJ.emb_cc'] at h1
      have h2 : (ω j τ : ℂ) = (X.m : ℂ) * (n0 : ℂ) * τ.1 (a j) := by
        rw [hae j, RealEmbeddingCharacters.emb_real (ha j)]
        simp only [RealEmbeddingCharacters.per]
        push_cast
        rfl
      simp only [hL]
      push_cast
      simp only [mul_assoc (n0 : ℂ)]
      rw [← Finset.mul_sum, h1, h2]
      ring
    have hs : s = ∑ j, ω.repr s j • ω j := (ω.sum_repr s).symm
    generalize ω.repr s = t at hs
    subst hs
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc ((t j : ℝ) : ℂ)]
    rw [← Finset.mul_sum, hj]
    ring
  · obtain ⟨b, hb1, hb2, rfl⟩ := (RealEmbeddingCharacters.mem_periods_iff X la p).mp hp
    have h0 : RealEmbeddingCharacters.per X 0 b ∈ Submodule.span ℤ (Set.range ω) := by
      rw [hω]
      exact (RealEmbeddingCharacters.mem_periods_iff X 0 _).mpr ⟨b, hb1, hb2, rfl⟩
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h0
    have h1 : RealEmbeddingCharacters.per X la b =
        ((X.chiOrd la : ℝ) / (n0 : ℝ)) • RealEmbeddingCharacters.per X 0 b := by
      funext τ
      simp only [RealEmbeddingCharacters.per, Pi.smul_apply, smul_eq_mul, ← hn0]
      push_cast
      field_simp
    refine ⟨X.chiOrd la * ∑ j, d j * c j k, ?_⟩
    rw [h1, ← hd]
    simp only [map_smul, map_sum, map_zsmul, Pi.smul_apply, Finset.sum_apply, hL]
    simp only [smul_eq_mul, zsmul_eq_mul]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
end GlobalTheory.CuspFlow
