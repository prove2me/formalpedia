-- Prove2me | solution 1 for GlobalTheory.Published.UnitaryFiniteCovolume.compactSpace_of_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:53.798469+00:00
-- url     : https://prove2.me/submissions/0681a50b-a356-431e-8181-d87304e019de

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_DefiniteCompactness_ExistsCompactOfDefinite
import Theorems.Thm_GlobalTheory_Published_UnitaryFiniteCovolume_exists_compact_of_definite
import Theorems.Thm_GlobalTheory_UnitaryFrames_isClosed_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.UnitaryFiniteCovolume
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Published.UnitaryFiniteCovolume
theorem _root_.solution {r : ℕ} (X : Data E r) (hd : X.p0 = 0 ∨ X.p0 = r)
    (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (hH : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) :
    CompactSpace H := by
  choose K hK hmem using exists_compact_of_definite X hd
  have hcl : IsClosed (H : Set (X.Ψ → GL (Fin r) ℂ)) := by
    convert GlobalTheory.UnitaryFrames.isClosed_unitary X using 1
    ext g
    exact hH g
  have hc : IsCompact (Set.pi Set.univ fun τ : X.Ψ =>
      Units.embedProduct (Matrix (Fin r) (Fin r) ℂ) ⁻¹' (K τ ×ˢ (MulOpposite.op '' K τ))) :=
    isCompact_univ_pi fun τ => Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hK τ).prod ((hK τ).image MulOpposite.continuous_op))
  refine isCompact_iff_compactSpace.mp (hc.of_isClosed_subset hcl fun g hg τ _ => ?_)
  exact ⟨hmem τ _ ((hH g).1 hg τ), _, hmem τ _ ((hH g⁻¹).1 (H.inv_mem hg) τ), rfl⟩
end GlobalTheory.Published.UnitaryFiniteCovolume
