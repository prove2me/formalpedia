-- Prove2me | solution 1 for GlobalTheory.HeightSubmodular.height_submodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:33.499805+00:00
-- url     : https://prove2.me/submissions/dbee42c9-688f-4681-bb29-b7bc84581522

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexIntegralSpanSupermultiplicativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetReNonneg
import Theorems.Thm_GlobalTheory_HeightSubmodular_gram_det_re_nonneg
import Theorems.Thm_GlobalTheory_HeightSubmodular_div_mul_div_le
import Theorems.Thm_GlobalTheory_GramSubmodular_gram_det_re_nonneg
import Theorems.Thm_GlobalTheory_LatBasisAdapted_exists_basis_adapted_mem
import Theorems.Thm_GlobalTheory_SpanIndex_relIndex_span_ne_zero
import Theorems.Thm_GlobalTheory_T_gramDet_inequalities_closed_forms
import Theorems.Thm_GlobalTheory_T_relIndex_integralSpan_supermultiplicative


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory GlobalTheory.HeightSubmodular
namespace GlobalTheory.HeightSubmodular
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ W₁ W₂, d x (W₁ ⊓ W₂) * d x (W₁ ⊔ W₂) ≤ d x W₁ * d x W₂) := by
  intro r X d hd x hx W₁ W₂
  obtain ⟨a, b, c, w, hli, hmem, h0, h1, h2, h3⟩ :=
    GlobalTheory.LatBasisAdapted.exists_basis_adapted_mem r X W₁ W₂
  have hsub : ∀ {κ : Type} (f : κ → Fin a ⊕ Fin b ⊕ Fin c) (τ : X.Ψ),
      (mat x τ)⁻¹ * (Matrix.of fun k l => τ.1 ((w ∘ f) l k)) =
        ((mat x τ)⁻¹ * Matrix.of fun k l => τ.1 (w l k)).submatrix id f := by
    intro κ f τ
    ext k l
    simp [Matrix.mul_apply]
  have key := fun {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Fin a ⊕ Fin b ⊕ Fin c)
      (hf : Function.Injective f) =>
    hd x hx κ (w ∘ f) (hli.comp f hf) (fun l => hmem (f l))
  have hI := fun {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Fin a ⊕ Fin b ⊕ Fin c)
      (hf : Function.Injective f) =>
    GlobalTheory.SpanIndex.relIndex_span_ne_zero r X κ (w ∘ f) (hli.comp f hf) (fun l => hmem (f l))
  have i1 : Function.Injective (Sum.map id Sum.inl : Fin a ⊕ Fin b → Fin a ⊕ Fin b ⊕ Fin c) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩
  have i2 : Function.Injective (Sum.map id Sum.inr : Fin a ⊕ Fin c → Fin a ⊕ Fin b ⊕ Fin c) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩
  rw [← h0, ← h3, ← h1, ← h2, key _ Sum.inl_injective, key _ i1, key _ i2,
    hd x hx _ w hli hmem]
  apply div_mul_div_le
  · exact Finset.prod_nonneg fun τ _ => gram_det_re_nonneg _
  · exact Finset.prod_nonneg fun τ _ => gram_det_re_nonneg _
  · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro τ _
      exact mul_nonneg (gram_det_re_nonneg _) (gram_det_re_nonneg _)
    · intro τ _
      simp only [hsub]
      exact (GlobalTheory.T.gramDet_inequalities_closed_forms).1 (Fin r) (Fin a) (Fin b) (Fin c) _
  · exact hI _ i1
  · exact hI _ i2
  · exact (GlobalTheory.T.relIndex_integralSpan_supermultiplicative) r X (Fin a) (Fin b) (Fin c) w hli hmem
end GlobalTheory.HeightSubmodular
