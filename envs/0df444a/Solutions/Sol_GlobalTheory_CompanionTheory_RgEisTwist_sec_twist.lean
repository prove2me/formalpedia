-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTwist.sec_twist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:13.244648+00:00
-- url     : https://prove2.me/submissions/be0f5a13-3e7a-43f2-91af-af17e3caffd2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistOfSectionLaw

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
theorem _root_.solution (h : IsCh Γ ⊤ c₀) (ρ : K →* (W →L[ℂ] W)) (P : Subgroup G) (c : G → ℂ) (g : G) :
    sec K P (c * c₀) ρ g = c₀ g • sec K P c (twRep h K ρ) g := by
  unfold sec
  by_cases hk : ∃ k : K, g * (k : G)⁻¹ ∈ P
  · rw [dif_pos hk, dif_pos hk, twRep_apply, Pi.mul_apply, Subgroup.coe_inv, ch_mul h g, smul_smul, smul_smul]
    congr 1
    ring
  · rw [dif_neg hk, dif_neg hk, smul_zero]
end GlobalTheory.CompanionTheory.RgEisTwist
