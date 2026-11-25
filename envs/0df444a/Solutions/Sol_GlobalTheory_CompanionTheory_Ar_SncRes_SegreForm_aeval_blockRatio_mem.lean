-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.aeval_blockRatio_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:30:20.937711+00:00
-- url     : https://prove2.me/submissions/6fb68371-f712-4d9d-aaee-c3d25014127b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StandardSmoothChartOfNonzero
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_blockRatio_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncRes GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {N : ℕ} (y : (Σ k, ι k) → Ω) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
namespace GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
theorem _root_.solution [CharZero Ω] (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (β : MRing ι) :
    aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ∈
      Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) := by
  classical
  induction β using MvPolynomial.induction_on with
  | C n => simpa using intCast_mem _ n
  | add p q hp hq => simpa using add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, aeval_X]
    refine mul_mem hp (Algebra.subset_adjoin ⟨E.symm (Function.update (E c₀) i.1 i.2), ?_⟩)
    exact (blockRatio_eq y E c₀ hc i).symm
end GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
