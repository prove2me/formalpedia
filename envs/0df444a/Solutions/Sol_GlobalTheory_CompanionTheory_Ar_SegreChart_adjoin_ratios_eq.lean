-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.adjoin_ratios_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:35:51.116589+00:00
-- url     : https://prove2.me/submissions/86a91a63-e201-4c07-81b6-6840abb85bec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_seg_ratio_update
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


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
variable {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ}
omit [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c : (k : K ⊕ Unit) → joinIdx ι (fun _ : Unit => Fin (r + 1)) k)
    (a : Fin (N + 1)) (hEa : ∀ k, E a k = c (Sum.inl k)) (hc : ∀ k, y ⟨k, c (Sum.inl k)⟩ ≠ 0) :
    Algebra.adjoin ℚ (Set.range fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k =>
        joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩) =
      Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪
        Set.range (fun k => x' k / x' (c (Sum.inr ())))) := by
  classical
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k | u, i⟩, rfl⟩
    · have h1 := seg_ratio_update y (fun k => c (Sum.inl k)) hc k i
      refine Algebra.subset_adjoin (Or.inl ⟨E.symm (Function.update (fun k => c (Sum.inl k)) k i), ?_⟩)
      simp only [Equiv.apply_symm_apply, hEa]
      exact h1
    · cases u
      exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
  · rw [Algebra.adjoin_le_iff]
    rintro _ (⟨j, rfl⟩ | ⟨i, rfl⟩)
    · rw [SetLike.mem_coe]
      simp only [← Finset.prod_div_distrib]
      refine prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨Sum.inl k, E j k⟩, ?_⟩
      simp only [hEa]
      rfl
    · exact Algebra.subset_adjoin ⟨⟨Sum.inr (), i⟩, rfl⟩
end GlobalTheory.CompanionTheory.Ar.SegreChart
