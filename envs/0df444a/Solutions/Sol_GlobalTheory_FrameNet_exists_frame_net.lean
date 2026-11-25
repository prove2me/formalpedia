-- Prove2me | solution 1 for GlobalTheory.FrameNet.exists_frame_net
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:48:19.452911+00:00
-- url     : https://prove2.me/submissions/d4db06c4-abe3-49d6-9055-d5cdc36783ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
import Theorems.Thm_GlobalTheory_FrameNet_exists_net_card_le
import Theorems.Thm_GlobalTheory_FrameNet_log_le_of_card_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r)
namespace GlobalTheory.FrameNet
theorem _root_.solution (v : Fin r → Fin r → E) (hv : LinearIndependent E v)
    (hint : ∀ i k, IsIntegral ℤ (herm X.Gm (v i) (v k))) {B η : ℝ} (hB : 1 ≤ B) (hη0 : 0 < η)
    (hη : η ≤ 1) :
    ∃ N : Finset (Frame X.Ψ r), (N : Set (Frame X.Ψ r)) ⊆ shortFrames X v B ∧
      (∀ x ∈ shortFrames X v B, ∃ A : Frame X.Ψ r, rmul x A ∈ N ∧
        ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ η) ∧
      (N.card : ℝ) ≤ Real.exp (2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * (fdeg E : ℝ) * (r : ℝ) ^ 3 * Real.log (r * B)) ∧
      Real.log N.card ≤ 2 * (fdeg E : ℝ) * (r : ℝ) ^ 2 * Real.log (6 * (r : ℝ) ^ 2 / η) +
        2 * (fdeg E : ℝ) * (r : ℝ) ^ 3 * Real.log (r * B) := by
  obtain ⟨N, h1, h2, h3⟩ := exists_net_card_le X v hv hint hB hη0 hη
  obtain ⟨h4, h5⟩ := log_le_of_card_le hB hη0 hη h3
  exact ⟨N, h1, h2, h4, h5⟩
end GlobalTheory.FrameNet
