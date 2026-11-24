-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.final_data_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:09:40.062831+00:00
-- url     : https://prove2.me/submissions/50317794-1036-4628-a13d-786915adabdb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_aeval_segForm
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_segForm_multiHomog
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_aeval_eq_zero_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_joinVec_comp_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_multiHomog_rename_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_blockFnField_joinPt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_isSncModel_joinPt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_mem_mcPts_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SegreChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (r : ℕ) (x' : Fin (r + 1) → Ω) (hG : Gz.IsHomogeneous (d + 1)) (h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0) (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0) (hx' : x' ≠ 0) (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y) (hch : ∀ a l, (∏ k, y ⟨k, E a k⟩) ≠ 0 → x' l ≠ 0 → SncChart (Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪ Set.range (fun k => x' k / x' l))) e (aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz))), ∃ (y' : (Σ _ : Unit, Fin (r + 1)) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin (r + 1)))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0 → z ∈ mcPts J := by
  intro Ω _ _ K _ ι _ y e β N E d Gz r x' hG h0 hβ hx' hF hch
  have hmem : rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz) ∈
      Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)} :=
    Ideal.subset_span rfl
  refine ⟨fun p => x' p.2, Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, ?_,
    blockFnField_joinPt y x' hF, ?_, ?_, isSncModel_joinPt y x' e E Gz hch,
    fun z hz hb => mem_mcPts_span y x' β E Gz hβ z hz hb⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx'
    exact ⟨i, hi⟩
  · refine ⟨{rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, ?_, rfl⟩
    rintro f rfl
    exact ⟨_, multiHomog_rename_inl (segForm_multiHomog E hG)⟩
  · intro hle
    have h1 := aeval_eq_zero_of_mem _ (hle hmem)
    rw [aeval_rename, joinVec_comp_inl, aeval_segForm] at h1
    exact h0 h1
end GlobalTheory.CompanionTheory.Ar.SegreChart
