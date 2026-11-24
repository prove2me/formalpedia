-- Prove2me | solution 1 for GlobalTheory.FinCovol.compactSpace_unitary_of_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:04:42.776944+00:00
-- url     : https://prove2.me/submissions/f6b07a68-4412-42f0-bc1f-cb2758cd9889

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsCompactOrthBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OrthonormalFramesBoundedOfDefinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactSpaceRealUnitaryGroupOfDefinite
import Theorems.Thm_GlobalTheory_FinCovol_isCompact_orth_bounded
import Theorems.Thm_GlobalTheory_UnitaryFrames_unitary_group_frames
import Theorems.Thm_GlobalTheory_orthonormal_frames_bounded_of_definite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.FinCovol
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.FinCovol
theorem _root_.solution :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
      (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by
  intro r X H hH hp
  obtain ⟨R, hR⟩ := GlobalTheory.orthonormal_frames_bounded_of_definite r X hp
  have hx0 : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  obtain ⟨-, -, h⟩ := GlobalTheory.UnitaryFrames.unitary_group_frames.2 r X H hH
  obtain ⟨horth, ι, hc, -, hι⟩ := h (x0F X) hx0
  have hK := (isCompact_orth_bounded r X R).image_of_continuousOn
    (hc.mono fun x hx => hx.1)
  refine ⟨hK.of_isClosed_subset isClosed_univ fun g _ => ?_⟩
  exact ⟨_, ⟨horth g, hR _ (horth g)⟩, hι g⟩
end GlobalTheory.FinCovol
