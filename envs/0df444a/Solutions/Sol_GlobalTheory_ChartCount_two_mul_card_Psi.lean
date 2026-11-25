-- Prove2me | solution 1 for GlobalTheory.ChartCount.two_mul_card_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:39:33.853802+00:00
-- url     : https://prove2.me/submissions/c830beb4-165e-453d-a3a3-b047ee8e0fe1

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TamagawaSpecialUnitary_320f37a25cd91d38
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PhaseFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotallyRealDegreeAndChartDimensionEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
open GlobalTheory GlobalTheory.ChartCount
namespace GlobalTheory.ChartCount
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    2 * X.Ψ.card = Module.finrank ℚ E := by
  classical
  have cc2 : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => star_star τ
  have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) := by
    intro a b h
    rw [← cc2 a, h, cc2]
  have hc : (X.Ψ)ᶜ = X.Ψ.map ⟨ComplexEmbedding.conjugate, hinj⟩ := by
    ext τ
    simp only [Finset.mem_compl, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro h
      refine ⟨ComplexEmbedding.conjugate τ, ?_, cc2 τ⟩
      rw [X.cmType, cc2]
      exact h
    · rintro ⟨σ, hσ, rfl⟩
      exact (X.cmType σ).1 hσ
  have h1 := Finset.card_compl X.Ψ
  rw [hc, Finset.card_map, NumberField.Embeddings.card] at h1
  have h2 : X.Ψ.card ≤ Module.finrank ℚ E := by
    rw [← NumberField.Embeddings.card E ℂ]; exact Finset.card_le_univ _
  omega
end GlobalTheory.ChartCount
