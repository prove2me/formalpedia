-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTwist.wall_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:44:12.163039+00:00
-- url     : https://prove2.me/submissions/380907bd-fff8-4f32-9922-dda1d1b1d9b8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistOfSectionLaw
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_ch_norm
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_ch_cont
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_eis_twist
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTwist_leftGood_cast

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
theorem _root_.solution (h : IsCh Γ ⊤ c₀) {P P' : Subgroup G} {c : G → ℂ} {η η' β : G → ℝ}
    {ρ : K →* (W →L[ℂ] W)} {L : Submodule ℂ W} {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (L →L[ℂ] secSp K P' c (twRep h K ρ))} {H : ℂ → G → (L →L[ℂ] W)}
    (hw : Wall Γ K P P' c η η' β (twRep h K ρ) L R D Op H) :
    Wall Γ K P P' (c * c₀) η η' β ρ L R D
      (fun z => (castL (secSp_twist h ρ P' c).symm).comp (Op z)) (fun z g => c₀ g • H z g) where
  le := by
    rw [secSp_twist h ρ P c]
    exact hw.le
  pos := hw.pos
  convR := hw.convR
  convL := hw.convL
  dEnt := hw.dEnt
  dNe := hw.dNe
  op := leftGood_cast _ hw.op
  hol g := (hw.hol g).const_smul (c₀ g)
  cont := ((ch_cont h).comp continuous_snd).smul hw.cont
  bdd b a g := by
    obtain ⟨U, hU, M, hM⟩ := hw.bdd b a g
    refine ⟨U, hU, M, fun z h1 h2 g' hg' => ?_⟩
    rw [norm_smul, ch_norm h, one_mul]
    exact hM z h1 h2 g' hg'
  eqR z hz g w := by
    rw [ContinuousLinearMap.smul_apply, hw.eqR z hz g w, eis_twist h, smul_comm]
  eqL z hz g w := by
    rw [ContinuousLinearMap.smul_apply, hw.eqL z hz g w, eis_twist h]
    rfl
end GlobalTheory.CompanionTheory.RgEisTwist
