-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTwist.eis_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:25:18.345262+00:00
-- url     : https://prove2.me/submissions/20122cd1-ce4d-46cb-bcf4-e4c03c5717f5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistOfSectionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_ch_rat_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_sec_twist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisTwist
open PositivityTheory.RgEis
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K : Subgroup G} {c₀ : G → ℂ}
namespace GlobalTheory.CompanionTheory.RgEisTwist
theorem _root_.solution (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (Λ : G → ℂ)
    (g : G) (w : W) :
    eis Γ K P (c * c₀) ρ Λ g w = c₀ g • eis Γ K P c (twRep h K ρ) Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [sec_twist h, ContinuousLinearMap.smul_apply, ch_rat_mul h hq, smul_comm]
end GlobalTheory.CompanionTheory.RgEisTwist
