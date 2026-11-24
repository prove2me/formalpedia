-- Prove2me | solution 1 for GlobalTheory.SW.HermLat.form_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:23.742699+00:00
-- url     : https://prove2.me/submissions/c472df7a-182c-45a5-8253-e369ccc3528a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual
import Theorems.Thm_GlobalTheory_SW_HermLat_form_eq
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
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {N : ℕ} (X : HermSub E N)
    (h : form E N X X = 0) : X = 0 := by
  have h1 := form_eq hΨ X X
  rw [h] at h1
  have hX : ccT X.1 = X.1 := X.2
  have h2 : ∀ τ : Ψ, τ.1 (X.1 * X.1).trace =
      ((∑ a, ∑ b, normSq (τ.1 (X.1 a b)) : ℝ) : ℂ) := fun τ => by
    simp only [Matrix.trace, diag_apply, mul_apply, map_sum, map_mul]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h3 : cc (X.1 a b) = X.1 b a := congrFun (congrFun hX b) a
    rw [← h3, Base.map_cc, Complex.mul_conj]
  simp only [h2] at h1
  have h4 : ∑ τ : Ψ, ∑ a, ∑ b, normSq (τ.1 (X.1 a b)) = 0 := by exact_mod_cast h1.symm
  obtain ⟨τ⟩ : Nonempty Ψ := by
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hσ : σ ∈ Ψ
    · exact ⟨⟨σ, hσ⟩⟩
    · exact ⟨⟨ComplexEmbedding.conjugate σ, by
        by_contra hc; exact hσ ((hΨ σ).2 hc)⟩⟩
  apply Subtype.ext
  ext a b
  have n0 : ∀ (τ : Ψ) a b, 0 ≤ normSq (τ.1 (X.1 a b)) := fun _ _ _ => normSq_nonneg _
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => n0 τ a b).1 h4 τ (Finset.mem_univ _)
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => n0 τ a b).1 h5 a (Finset.mem_univ _)
  have h7 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => n0 τ a b).1 h6 b (Finset.mem_univ _)
  simpa using h7
end GlobalTheory.SW.HermLat
