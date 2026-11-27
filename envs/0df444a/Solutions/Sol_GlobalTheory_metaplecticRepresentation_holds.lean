-- Prove2me | solution 1 for GlobalTheory.metaplecticRepresentation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:21.302991+00:00
-- url     : https://prove2.me/submissions/c36751ec-4b52-45f7-abb2-ae3a183b2065

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VacuumMatrixCoefficientSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrthogonalSymplecticFixesSiegelPointIStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticCoverWeilRepresentationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerProductEuclideanModelsAgreeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSiegelUpperHalfSpaceNegMulInvSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SymplecticHolPartDetNeZeroAndIsSymmStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzL2EuclideanIdentificationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MetaplecticRepresentationHolds
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_continuous
import Theorems.Thm_CompanionTheory_ThKR_Mp_ker
import Theorems.Thm_GlobalTheory_T_isSiegelUpperHalfSpace_neg_mul_inv_symplectic
import Theorems.Thm_GlobalTheory_T_metaplectic_cover_weil_representation
import Theorems.Thm_GlobalTheory_T_orthogonal_symplectic_fixes_siegel_point_i
import Theorems.Thm_GlobalTheory_T_schrodinger_product_euclidean_models_agree
import Theorems.Thm_GlobalTheory_T_schwartz_L2_euclidean_identification
import Theorems.Thm_GlobalTheory_T_symplectic_holPart_det_ne_zero_and_isSymm
import Theorems.Thm_GlobalTheory_T_vacuum_matrix_coefficient_sq
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : GlobalTheory.Published.MetaplecticRepresentation := by
  intro ι _ _
  obtain ⟨G, iG, tG, tgG, pr, om, omS, φ, hcov, hsurj, ⟨ε, hε1, hker, hεf⟩, hcont, hint, hcompat, hφ, hjc,
    hgauss⟩ := GlobalTheory.T.metaplectic_cover_weil_representation ι
  obtain ⟨e, u, he, hu⟩ := GlobalTheory.T.schwartz_L2_euclidean_identification ι
  have hes : ∀ (ψ : Sch ι) (x : ι → ℝ), e.symm ψ x = ψ (WithLp.toLp 2 x) := by
    intro ψ x
    simpa using (he (e.symm ψ) (WithLp.toLp 2 x)).symm
  have inj : ∀ ψ₁ ψ₂ : Sch ι, ψ₁.toLp 2 = ψ₂.toLp 2 → ψ₁ = ψ₂ := fun ψ₁ ψ₂ h =>
    SchwartzMap.injective_toLp (E := EuclideanSpace ℝ ι) (F := ℂ) 2 volume h
  let Ω : G →* (Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))) :=
    { toFun := fun g => ((u.symm.toContinuousLinearEquiv : L2 ι →L[ℂ] Lp ℂ 2 (volume : Measure (ι → ℝ))).comp
          ((om g).toContinuousLinearEquiv : L2 ι →L[ℂ] L2 ι)).comp
          (u.toContinuousLinearEquiv : Lp ℂ 2 (volume : Measure (ι → ℝ)) →L[ℂ] L2 ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hΩ : ∀ g f, Ω g f = u.symm (om g (u f)) := fun g f => rfl
  let ω : G →* (𝓢(ι → ℝ, ℂ) →L[ℂ] 𝓢(ι → ℝ, ℂ)) :=
    { toFun := fun g => ((e.symm : Sch ι →L[ℂ] 𝓢(ι → ℝ, ℂ)).comp (omS g)).comp (e : 𝓢(ι → ℝ, ℂ) →L[ℂ] Sch ι)
      map_one' := by ext1 f; simp
      map_mul' := fun g h => by ext1 f; simp }
  have hω : ∀ g f, ω g f = e.symm (omS g (e f)) := fun g f => rfl
  have heω : ∀ g f, e (ω g f) = omS g (e f) := fun g f => by rw [hω, e.apply_symm_apply]
  have hφ₀ : ∀ x : ι → ℝ, e.symm φ x = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
    intro x
    rw [hes, hφ]
  refine ⟨G, iG, tG, tgG, pr, Ω, ω, e.symm φ, hsurj, hcov, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hφ₀, ?_, ?_⟩
  · have hk : (pr.ker : Set G) = {1, ε} := by
      ext g
      simp [MonoidHom.mem_ker, hker]
    rw [← SetLike.coe_sort_coe, hk, Nat.card_coe_set_eq, Set.ncard_pair hε1.symm]
  · intro g f
    rw [hΩ, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
  · intro f
    exact u.symm.continuous.comp (hcont (u f))
  · intro g ψ
    rw [hΩ, LinearIsometryEquiv.symm_apply_eq, hu, hu, heω, hcompat]
  · have : (fun x : G × 𝓢(ι → ℝ, ℂ) => ω x.1 x.2) =
        (fun y : Sch ι => e.symm y) ∘ (fun y : G × Sch ι => omS y.1 y.2) ∘ (fun x : G × 𝓢(ι → ℝ, ℂ) => (x.1, e x.2)) := by
      funext x; rfl
    rw [this]
    exact e.symm.continuous.comp (hjc.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
  · intro g w ψ
    apply e.injective
    apply inj
    rw [heω, ← hcompat]
    rw [GlobalTheory.T.schrodinger_product_euclidean_models_agree ι w ψ (e ψ) (e (GlobalTheory.Published.Metaplectic.rho w ψ)) (he ψ) (he _)]
    rw [hint, hcompat]
    rw [GlobalTheory.T.schrodinger_product_euclidean_models_agree ι (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ) (e (ω g ψ))
      (e (GlobalTheory.Published.Metaplectic.rho (GlobalTheory.Published.Metaplectic.act (pr g).1 w) (ω g ψ))) (he _) (he _)]
    rw [heω]
    congr 2
    simp [GlobalTheory.Published.Metaplectic.act, Sum.elim_comp_inl_inr]
  · intro g hg1 hg ψ
    have hgε : g = ε := ((hker g).1 hg1).resolve_left hg
    subst hgε
    have h1 : omS g (e ψ) = -(e ψ) := by
      apply inj
      have hn := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))).map_neg (e ψ)
      simp only [SchwartzMap.toLpCLM_apply] at hn
      rw [← hcompat, hεf, hn]
    rw [hω, h1, map_neg, e.symm_apply_apply]
  · intro g
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨-, hsymm⟩ := GlobalTheory.T.symplectic_holPart_det_ne_zero_and_isSymm ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2
    have hsieg := GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 hdet hsymm
    have hωx : ∀ x : ι → ℝ, ω g (e.symm φ) x = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ
        (-((Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) *
          (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))⁻¹)) *ᵥ
          fun i => (x i : ℂ))) := by
      intro x
      rw [hω, e.apply_symm_apply, hes, hcx]
    simp only [hωx, hφ₀]
    exact GlobalTheory.T.vacuum_matrix_coefficient_sq ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) hdet hsieg c hc
  · intro g horth
    obtain ⟨c, hc, hcx⟩ := hgauss g (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ))
      (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ))
      (fun a b => rfl) (fun a b => rfl)
    have hdet : (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)).det ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hc; exact zero_ne_one hc
    obtain ⟨hP, hq⟩ := GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i ι (pr g).1 (Matrix.of fun a b => ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) (Matrix.of fun a b => ((pr g).1 (.inr a) (.inl b) : ℂ) - I * ((pr g).1 (.inr a) (.inr b) : ℂ)) (fun a b => rfl) (fun a b => rfl) (pr g).2 horth hdet
    refine ⟨c, by rw [hP]; exact hc, ?_⟩
    ext x
    rw [hω, e.apply_symm_apply, hes, hcx, SchwartzMap.smul_apply, smul_eq_mul, hφ₀]
    simp only [PiLp.toLp_apply]
    rw [hq x]
end GlobalTheory
