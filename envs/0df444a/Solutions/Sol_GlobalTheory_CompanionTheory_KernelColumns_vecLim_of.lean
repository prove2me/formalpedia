-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelColumns.vecLim_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:56:26.522379+00:00
-- url     : https://prove2.me/submissions/3c1bfc44-3306-4809-baf7-c7b0763a9ca5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_VecLimOf
import Theorems.Thm_GlobalTheory_CompanionTheory_KernelColumns_exists_delta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelColumns
namespace GlobalTheory.CompanionTheory.KernelColumns
theorem _root_.solution (hCnt : CntBasic) (hCv : CvTest) (hCol : ColOp) (hA : ApproxU) (hVC : VecClose) :
    VecLim := by
  intro X ι _ Φ T y j k ε hΦ hT hk hε
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  set Ω₀ : Set X.G := ⋃ l, tsupport (Φ l j) with hΩ₀
  have hΩ₀c : IsCompact Ω₀ := isCompact_iUnion fun l => (hΦ l j).2.isCompact
  set Ω : Set X.G := Ω₀ * N with hΩ
  have hΩc : IsCompact Ω := hΩ₀c.mul hNc
  set c : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y) with hc
  have hctop : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ ?_)
    · exact hΩc.inv.measure_lt_top.ne
    · exact (hCnt X).1 _ (hΩc.inv.mul hΩc) y
  obtain ⟨δ, hδ, hδc⟩ := exists_delta c hctop ε hε
  choose Wl hWl hWlP using fun l => hA X (Φ l j) δ (hΦ l j) hδ
  refine ⟨N ∩ ⋂ l, Wl l, Filter.inter_mem hN1 (Filter.iInter_mem.2 hWl), ?_⟩
  intro ψ hψ hsupp u hu
  have hsN : tsupport ψ ⊆ N := hsupp.trans Set.inter_subset_left
  have hsl : ∀ l, tsupport ψ ⊆ Wl l := fun l =>
    hsupp.trans (Set.inter_subset_right.trans (Set.iInter_subset _ l))
  have hvec : X.IsVec (fun l j => cv X.μ (Φ l j) ψ) y j (T u) := fun l =>
    (((hCol X ι ψ hψ.1).2 Φ T hΦ hT y j u hu).1 l)
  have hfin := hVC X ι (fun l j => cv X.μ (Φ l j) ψ) Φ Ω δ y j (T u) k hΩc (fun l => by
    have hcv := hCv X (Φ l j) ψ (hΦ l j) hψ.1
    refine ⟨hcv.1, hΦ l j, ?_, ?_, fun z => ((hWlP l ψ hψ (hsl l) z).1)⟩
    · exact hcv.2.1.trans (Set.mul_subset_mul (Set.subset_iUnion (fun l => tsupport (Φ l j)) l) hsN)
    · intro z hz
      exact ⟨z, Set.subset_iUnion (fun l => tsupport (Φ l j)) l (subset_tsupport _ hz), 1, h1N, mul_one z⟩)
    hvec hk
  have hle : ‖T u - k‖ₑ ^ 2 ≤ ENNReal.ofReal ε ^ 2 := by
    refine hfin.trans (le_trans (le_of_eq ?_) hδc)
    rw [hc]; ring
  have hle' : ‖T u - k‖ₑ ≤ ENNReal.ofReal ε := (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hle
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hε.le] at hle'
  exact hle'
end GlobalTheory.CompanionTheory.KernelColumns
