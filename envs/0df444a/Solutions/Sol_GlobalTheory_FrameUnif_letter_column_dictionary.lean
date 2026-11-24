-- Prove2me | solution 1 for GlobalTheory.FrameUnif.letter_column_dictionary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:16.293431+00:00
-- url     : https://prove2.me/submissions/807dd34a-7806-42ff-affa-c276e459c7ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RelabelEmbeddingsGoodBijectiveConjCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmTypeLetterFrameColumnDictionary
import Theorems.Thm_GlobalTheory_FrameUnif_exists_letter_equiv
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_Relab_relab_good
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.FrameUnif
namespace GlobalTheory.FrameUnif
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, (∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, (∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < (F.Di k).q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧ (∀ j, ((idx j).2 : ℕ) = if ((idx j).2 : ℕ) < (F.Di k).q then (F.Di k).q - 1 - (e j).2 else (F.Di k).q + (e j).2) ∧ ∀ (x : Frame (M.X k).Ψ r) (v : Fin r → E) j, perFr (M.X k) x v (relab c σ (e j).1) (e j).2 = if ((idx j).2 : ℕ) < (F.Di k).q then hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v) else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2) ∧ (M.X k).p0 = (F.Di k).q ∧ r = (F.Di k).p + (F.Di k).q ∧ cc (-(M.X k).ξ0) = -(-(M.X k).ξ0) ∧ (∀ τ ∈ (M.X k).Ψ, 0 < (τ (-(M.X k).ξ0)).im) ∧ ∀ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), (∀ a, φ a = (M.φ k a : Fin r → E)) → LinearMap.range φ = (M.X k).Λ ∧ (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc ((M.X k).Gm a b) = (M.X k).Gm b a) ∧ (M.X k).Gm.det ≠ 0 ∧ ∀ x y, (((F.Di k).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (φ x) (φ y))) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hB hN k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp, hq⟩ := F.sig k
  obtain ⟨hp0, hty⟩ := hB.type k
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  refine ⟨?_, hp0.trans hq.symm, by rw [hp, hq]; exact hB.rank, ?_, ?_, ?_⟩
  · obtain ⟨f, hf⟩ := exists_letter_equiv (M.X k).Ψ (M.X k).cmType Dw.p Dw.q r hB.rank (relab c σ) hbij Dw.mult
      (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
      (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
    obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, ∀ j,
        (relab c σ (e j).1 ∈ (M.X k).Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
        (relab c σ (e j).1 ∉ (M.X k).Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
          ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
    rw [hq]
    refine ⟨idx, fun j => ?_, fun j => ?_, fun x v j => ?_⟩
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), b]
      · rw [if_pos (by omega), b, hcc]
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), c']
      · rw [if_pos (by omega), c']
    · have h := hi j
      generalize idx j = t at h ⊢
      obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
      dsimp only at h ⊢
      rw [← hp0] at h ⊢
      rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
      · rw [if_neg (by omega)]
        unfold perFr
        rw [dif_pos a, dif_pos hn]
      · rw [if_pos (by omega)]
        unfold perFr
        rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ (M.X k).Ψ from hτ), dif_pos hn]
        rfl
  · have h := (M.X k).ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  · intro τ hτ
    have := hN k τ hτ
    rw [map_neg, Complex.neg_im]
    linarith
  · intro φ hφ
    have hrange : LinearMap.range φ = (M.X k).Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        rw [hφ]
        exact (M.φ k a).2
      · intro hy
        exact ⟨(M.φ k).symm ⟨y, hy⟩, by rw [hφ, LinearEquiv.apply_symm_apply]⟩
    refine ⟨hrange, ?_, ?_, (M.X k).Gm_herm, (M.X k).Gm_det, fun x y => ?_⟩
    · intro a b hab
      rw [hφ, hφ] at hab
      exact (M.φ k).injective (Subtype.ext hab)
    · rw [← LinearMap.coe_range, hrange]
      exact (M.X k).Λ_span
    · rw [hφ, hφ]
      exact hB.ef k x y
end GlobalTheory.FrameUnif
