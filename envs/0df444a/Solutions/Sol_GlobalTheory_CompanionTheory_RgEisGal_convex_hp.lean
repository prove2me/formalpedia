-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.convex_hp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:14.874733+00:00
-- url     : https://prove2.me/submissions/fa56d233-a91d-40c1-9f03-3d9387c8c664

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (α β γ r : ℝ) : Convex ℝ {x : ℝ × ℝ | r < affR α β γ x} := by
  have hl : IsLinearMap ℝ (fun x : ℝ × ℝ => α * x.1 + β * x.2) :=
    ⟨fun a b => by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun c a => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  have h := convex_halfSpace_gt hl (r - γ)
  have e : {x : ℝ × ℝ | r < affR α β γ x} = {w : ℝ × ℝ | r - γ < α * w.1 + β * w.2} := by
    ext x
    simp only [Set.mem_setOf_eq, affR]
    constructor <;> intro h' <;> linarith
  rw [e]
  exact h
end GlobalTheory.CompanionTheory.RgEisGal
