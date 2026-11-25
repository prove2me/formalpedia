-- Prove2me | solution 1 for GlobalTheory.FrameOver.encard_overlattices_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:00.943202+00:00
-- url     : https://prove2.me/submissions/9753d4a3-2bf7-4933-9556-0133d62e52e0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSubmoduleAndHomLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeCountBoundFrames
import Theorems.Thm_GlobalTheory_FrameOver_count
import Theorems.Thm_GlobalTheory_FrameOver_hf_comb
import Theorems.Thm_GlobalTheory_FrameOver_det_base
import Theorems.Thm_GlobalTheory_FrameOver_exists_det_one
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameOver
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, 0 ≤ S.a → ({Mh : Submodule L.O S.V | S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧ ∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O}.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp ha
  obtain ⟨U, U', hU, hU', h1, h2⟩ := exists_det_one L S hC hp
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, -, hth, -, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨u, hu⟩ := (GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr).2.2.2 c hc0
  have hϖ0 : (S.ϖ : F) ≠ 0 := fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  set t : E := algebraMap F E S.th⁻¹ with ht
  let g : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim (fun b => t • (p.2 b - p.1 b)) p.1
  let g' : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim p.1 (fun b => t • (p.2 b - p.1 b))
  let B : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.fromBlocks (t • U') 0 (-(t • U)) U
  let B' : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.fromBlocks U (-(t • U)) 0 (t • U')
  have hg : ∀ i, g i = ∑ l, B l i • Sum.elim S.f' S.f l := by
    rintro (i | i)
    · simp [g, B, h1, h2, smul_sub, Finset.smul_sum, smul_smul, sub_eq_add_neg, add_comm]
    · simp [g, B, h1]
  have hg' : ∀ i, g' i = ∑ l, B' l i • Sum.elim S.f S.f' l := by
    rintro (i | i)
    · simp [g', B', h1]
    · simp [g', B', h1, h2, smul_sub, Finset.smul_sum, smul_smul, sub_eq_add_neg, add_comm]
  have hB : B.det = t ^ (r + 1) := by
    simp [B, Matrix.det_fromBlocks_zero₁₂, hU, hU']
  have hB' : B'.det = t ^ (r + 1) := by
    simp [B', Matrix.det_fromBlocks_zero₂₁, hU, hU']
  have hBu : IsUnit B.det := by
    rw [hB]; exact ((IsUnit.mk0 _ (inv_ne_zero hth)).map _).pow _
  have hME : S.ME ≤ Submodule.span E (Set.range g) := by
    have hv : ∀ l, Sum.elim S.f' S.f l ∈ Submodule.span E (Set.range g) := fun l => by
      refine (Submodule.mem_span_range_iff_exists_fun E).2 ⟨fun i => B⁻¹ i l, ?_⟩
      simp only [hg, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, mul_comm (B⁻¹ _ _), ← Matrix.mul_apply,
        Matrix.mul_nonsing_inv B hBu, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, -, rfl⟩; exact hv (Sum.inr i)
    · rintro _ ⟨i, -, rfl⟩; exact hv (Sum.inl i)
  let Φ : S.V →ₗ[E] (Fin (r + 1) ⊕ Fin (r + 1) → E) :=
    LinearMap.pi fun j => GlobalTheory.FrameBasic.hfL L S.Hm (g' j)
  have hdet : (Matrix.of fun i j => Φ (g i) j).det =
      algebraMap F E ((S.ϖ : F) ^ S.a.toNat * ((u : 𝒪[F]) : F)) := by
    have e : (Matrix.of fun i j => Φ (g i) j) = Matrix.of fun i j => hf L S.Hm
        (∑ l, B l i • Sum.elim S.f' S.f l) (∑ l, B' l j • Sum.elim S.f S.f' l) := by
      ext i j
      rw [Matrix.of_apply, Matrix.of_apply, ← hg, ← hg']; rfl
    have e2 : (B'.map L.cj).det = L.cj B'.det := (AlgEquiv.map_det L.cj B').symm
    rw [e, hf_comb L S.herm.1, Matrix.det_mul, Matrix.det_mul, det_base, Matrix.det_transpose, e2,
      hB, hB', ht, map_pow, AlgEquiv.commutes, hc, ← map_pow, ← map_mul, ← map_mul]
    congr 1
    have hθ : S.th = (S.ϖ : F) ^ S.vth := by
      unfold Frames.th Frames.vth
      split_ifs <;> simp
    have hv : vE L S.ϖ (algebraMap F E c) = S.a + 2 * (r + 1) * S.vth := by
      rw [Frames.a, hc]; ring
    rw [← zpow_natCast (S.ϖ : F) S.a.toNat, Int.toNat_of_nonneg ha]
    rw [hv, zpow_add₀ hϖ0, mul_comm _ S.vth, zpow_mul, ← hθ] at hu
    have hn : (2 * (r + 1) : ℤ) = ((2 * (r + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [hn, zpow_natCast] at hu
    have h3 : S.th⁻¹ ^ (r + 1) * S.th ^ (r + 1) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hth, one_pow]
    rw [hu, two_mul, pow_add S.th (r + 1)]
    linear_combination ((S.ϖ : F) ^ S.a * ((u : 𝒪[F]) : F)) *
      (S.th⁻¹ ^ (r + 1) * S.th ^ (r + 1) + 1) * h3
  have hgM : ∀ i, g i ∈ S.Mof p.1 p.2 := by
    rintro (i | i)
    · exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
    · exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have hgM' : ∀ i, g' i ∈ S.Mof p.1 p.2 := by
    rintro (i | i)
    · exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
    · exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  have key := count L S.ϖ_irr g Φ S.a.toNat u hdet
    {Mh : Submodule L.O S.V | S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧
      ∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O}
    (fun P hP => ⟨fun i => hP.1 (hgM i), fun x hx => hME (hP.2.1 x hx),
      fun x hx j => hP.2.2 x hx _ (hP.1 (hgM' j))⟩)
  have hcard : Fintype.card (Fin (r + 1) ⊕ Fin (r + 1)) = 2 * r + 2 := by
    simp only [Fintype.card_sum, Fintype.card_fin]; ring
  rw [hcard] at key
  refine (ENat.toENNReal_le.2 key).trans_eq ?_
  rw [ENat.toENNReal_coe, Nat.cast_pow]
  rfl
end GlobalTheory.FrameOver
