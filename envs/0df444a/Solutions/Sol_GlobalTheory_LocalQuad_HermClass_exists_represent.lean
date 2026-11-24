-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.exists_represent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:15.053293+00:00
-- url     : https://prove2.me/submissions/10fafc40-231b-4d2a-a3d3-1cb03586b85d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_trans
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_exists_zero_coord_ne_zero
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_mem_real
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Published_exists_cc_eq_neg
import Theorems.Thm_GlobalTheory_Published_exists_sq_real
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LocalQuad.HermClass
theorem _root_.solution (H : Isotropy) {r : ℕ} (hr : 2 ≤ r) {g : Fin r → E}
    (hg : ∀ i, cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0) {c : E} (hc : cc c = c) (hc0 : c ≠ 0)
    (hs : ∀ τ : E →+* ℂ, ∃ i, (0 < (τ (g i)).re ↔ 0 < (τ c).re)) :
    ∃ z : Fin r → E, herm (Matrix.diagonal g) z z = c := by
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  obtain ⟨d, hd⟩ := GlobalTheory.Published.exists_sq_real hθ
  let γ : Fin r → maximalRealSubfield E := fun i => ⟨g i, mem_real (hg i)⟩
  let κ : maximalRealSubfield E := ⟨c, mem_real hc⟩
  have hγ : ∀ i, γ i ≠ 0 := fun i h => hg0 i (congrArg Subtype.val h)
  have hκ : κ ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (hd.symm.trans (congrArg Subtype.val h))
  let a : Option (Fin r ⊕ Fin r) → maximalRealSubfield E :=
    fun o => o.elim (-κ) (Sum.elim γ fun i => -d * γ i)
  have ha : ∀ o, a o ≠ 0 := by
    rintro (_ | i | i)
    · exact neg_ne_zero.mpr hκ
    · exact hγ i
    · exact mul_ne_zero (neg_ne_zero.mpr hd0) (hγ i)
  obtain ⟨x, hx, hx0⟩ := H (maximalRealSubfield E) (Option (Fin r ⊕ Fin r)) a
    (by simp; omega) ha (by
      intro σ
      let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp σ)
      have hτ : ∀ y : maximalRealSubfield E, (τ (y : E)).re = σ y := fun y => by
        have : τ (y : E) = (Complex.ofRealHom.comp σ) y :=
          ComplexEmbedding.lift_algebraMap_apply E _ y
        rw [this]
        simp
      obtain ⟨i, hi⟩ := hs τ
      have e1 : (τ (g i)).re = σ (γ i) := hτ (γ i)
      have e2 : (τ c).re = σ κ := hτ κ
      rw [e1, e2] at hi
      have n1 : σ (γ i) ≠ 0 := (map_ne_zero σ).mpr (hγ i)
      have n2 : σ κ ≠ 0 := (map_ne_zero σ).mpr hκ
      rcases lt_or_gt_of_ne n2 with h | h
      · refine ⟨some (Sum.inl i), none, ?_, ?_⟩
        · exact lt_of_le_of_ne (not_lt.mp fun h' => absurd (hi.mp h') h.not_gt) n1
        · simpa [a] using h
      · refine ⟨none, some (Sum.inl i), ?_, hi.mpr h⟩
        simpa [a] using h)
  obtain ⟨w, hw, hw0⟩ := exists_zero_coord_ne_zero ha hx hx0 none
  rw [Fintype.sum_option, Fintype.sum_sum_type] at hw0
  have hw1 := congrArg (Subtype.val : maximalRealSubfield E → E) hw0
  have hw2 : (w none : E) ≠ 0 := fun h => hw (Subtype.ext h)
  simp [a, γ, κ, hd] at hw1
  refine ⟨fun i => ((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none, ?_⟩
  have hcc : ∀ i, cc (((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none) =
      ((w (some (Sum.inl i)) : E) - w (some (Sum.inr i)) * θ) / w none := by
    intro i
    have : IsCMField.complexConj E θ = -θ := hθ
    simp [cc, this, sub_eq_add_neg]
  simp only [herm, hcc, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have : ∀ i, ((w (some (Sum.inl i)) : E) + w (some (Sum.inr i)) * θ) / w none * g i *
      (((w (some (Sum.inl i)) : E) - w (some (Sum.inr i)) * θ) / w none) =
      (g i * (w (some (Sum.inl i)) : E) ^ 2 -
        θ * θ * g i * (w (some (Sum.inr i)) : E) ^ 2) / (w none : E) ^ 2 := by
    intro i
    field_simp
    ring
  simp only [this, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [div_eq_iff (pow_ne_zero 2 hw2)]
  linear_combination hw1
end GlobalTheory.LocalQuad.HermClass
