-- Prove2me | solution 1 for GlobalTheory.FramePeriod.isPeriod_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:12.956717+00:00
-- url     : https://prove2.me/submissions/ba61e4f8-eece-4918-b35f-06ffc3327499

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Theorems.Thm_GlobalTheory_FramePeriod_exists_loc
import Theorems.Thm_GlobalTheory_FramePeriod_trace_re
import Theorems.Thm_GlobalTheory_FramePeriod_cmType
import Theorems.Thm_GlobalTheory_FramePeriod_isTypeFn
import Theorems.Thm_GlobalTheory_FramePeriod_allPer_symm
import Theorems.Thm_GlobalTheory_FramePeriod_allPer_bijective
import Theorems.Thm_GlobalTheory_FramePeriod_hermForm_block
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_CMLattice_exists_basis_of_cmType
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_emb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.FramePeriod
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = D.p + D.q → IsTypeFn H D.p D.q ty ∧ ∀ x ∈ FD.GG Ψ Gm D.q, (∃ P : D.La →+ (Fin g → ℂ), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2)) ∧ ∀ P : D.La →+ (Fin g → ℂ), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → IsPeriod D ty P := by
  classical
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos ⟨hφ, hspan, hG, _, hEF⟩ hr
  refine ⟨isTypeFn H _ _ Ψ hΨ g idx ty hty hr, fun x hx => ?_⟩
  have hcm := cmType H Ψ hΨ
  have hloc := fun τ : Ψ => exists_loc τ.1 Gm hG D.q (FD.mat x τ) (hx τ).1 (hx τ).2
  refine ⟨⟨((allPer Gm D.q x idx).toAddMonoidHom.comp
    (CMLattice.embAll Ψ r).toAddMonoidHom).comp φ.toAddMonoidHom, fun v k => rfl⟩, fun P hP => ?_⟩
  have hP' : ∀ v, P v = allPer Gm D.q x idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP v k
  let L := LinearEquiv.ofBijective _ (allPer_bijective Gm D.q x idx fun τ => (hloc τ).1)
  have hL : ∀ y, L y = allPer Gm D.q x idx y := fun _ => rfl
  have := D.fin
  obtain ⟨b, hb⟩ := CMLattice.exists_basis_of_cmType Ψ hcm r (LinearMap.range φ)
    (Module.Finite.iff_fg.1 inferInstance) (by rw [LinearMap.coe_range]; exact hspan)
  have hrange : ∀ z, z ∈ Set.range P ↔ z ∈ Submodule.span ℤ (Set.range (b.map L)) := by
    intro z
    have h1 : Set.range (b.map L) = (L.toLinearMap.restrictScalars ℤ) '' Set.range b := by
      rw [← Set.range_comp]; congr 1
    rw [h1, ← Submodule.map_span, Submodule.mem_map]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨_, (hb _).2 ⟨φ v, ⟨v, rfl⟩, rfl⟩, (hP' v).symm⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨_, ⟨v, rfl⟩, rfl⟩ := (hb _).1 hy
      exact ⟨v, hP' v⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a v k
    have h1 : FD.Data.emb (idx k).1.1 (φ (a • v)) =
        (idx k).1.1 (a : E) • FD.Data.emb (idx k).1.1 (φ v) := by
      funext j
      simp [FD.Data.emb, Algebra.smul_def]
    rw [hP, hP, hty, h1]
    split_ifs
    · rw [FD.hermC_smul_right, ComplexEmbedding.conjugate_coe_eq]
    · rw [mulVec_smul]; rfl
  · intro v w hvw
    rw [hP', hP', ← hL, ← hL] at hvw
    have h1 := L.injective hvw
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Ψ := by
      by_cases h : ComplexEmbedding.conjugate σ ∈ Ψ
      · exact ⟨_, h⟩
      · exact ⟨σ, (hcm σ).2 h⟩
    apply hφ
    funext a
    exact τ.injective (congrFun (congrFun h1 ⟨τ, hτ⟩) a)
  · have h1 : P.range = (Submodule.span ℤ (Set.range (b.map L))).toAddSubgroup := by
      ext z; exact hrange z
    rw [h1]
    exact inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (b.map L))))
  · rw [eq_top_iff, ← (b.map L).span_eq]
    exact Submodule.span_mono fun z hz => (hrange z).2 (Submodule.subset_span hz)
  · choose Hl hH hp hI using fun τ => (hloc τ).2
    refine ⟨Matrix.of fun k l => if (idx k).1 = (idx l).1 then
      ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0, ?_, ?_, ?_⟩
    · ext k l
      simp only [conjTranspose_apply, of_apply]
      by_cases h : (idx k).1 = (idx l).1
      · rw [if_pos h, if_pos h.symm, star_mul', ← h, (hH _).apply]
        congr 1
        exact Complex.conj_ofReal _
      · rw [if_neg h, if_neg (Ne.symm h), star_zero]
    · intro z hz
      rw [hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.re_sum]
      simp only [Complex.re_ofReal_mul]
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
      refine Finset.sum_pos' (fun τ _ => mul_nonneg (by linarith [hpos τ.1 τ.2]) ?_)
        ⟨(idx k).1, Finset.mem_univ _, mul_pos (by linarith [hpos _ (idx k).1.2]) (hp _ _ ?_)⟩
      · by_cases h : (fun a => z (idx.symm (τ, a))) = 0
        · rw [h]; simp [hermForm]
        · exact (hp _ _ h).le
      · intro h
        apply hk
        simpa using congrFun h (idx k).2
    · intro v w
      rw [hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.im_sum, hP', hP']
      have h1 : ((D.EF v w : ℤ) : ℝ) =
          ((Algebra.trace ℚ E (ξ * FD.herm Gm (φ v) (φ w)) : ℚ) : ℝ) := by
        rw [← hEF]; simp
      rw [h1, trace_re Ψ hcm]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [allPer_symm, allPer_symm, Complex.im_ofReal_mul, hI, map_mul, ← FD.hermC_emb]
      have h2 : (τ.1 ξ).re = 0 := by
        have h3 := congrArg Complex.re (FD.emb_cc τ.1 ξ)
        rw [hξ, map_neg, Complex.neg_re, Complex.conj_re] at h3
        linarith
      rw [Complex.mul_re, h2]
      change _ * -(FD.hermC τ.1 Gm (FD.Data.emb τ.1 (φ v)) (FD.Data.emb τ.1 (φ w))).im = _
      ring
end GlobalTheory.FramePeriod
