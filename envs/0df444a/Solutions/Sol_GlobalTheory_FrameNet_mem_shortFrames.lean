-- Prove2me | solution 1 for GlobalTheory.FrameNet.mem_shortFrames
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:32.252833+00:00
-- url     : https://prove2.me/submissions/be82cb10-8857-4e9f-8ae5-a5010901b0f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres

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
theorem _root_.solution {v : Fin r → Fin r → E} {B : ℝ} {x : Frame X.Ψ r} :
    x ∈ shortFrames X v B ↔ (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ i, ∑ τ : X.Ψ, X.maj x τ (Data.emb τ.1 (v i)) ≤ B := by
  exact Iff.rfl
end GlobalTheory.FrameNet
