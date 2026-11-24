-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgTransfer.conv_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:09:32.69065+00:00
-- url     : https://prove2.me/submissions/a268c3fd-7327-4c8c-a478-d7bbe7b6e1c7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CorrESymmCoe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_qk_spec
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_cos_exists
import Theorems.Thm_GlobalTheory_CompanionTheory_RgTransfer_rep_mul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgTransfer
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {G' : Type} [Group G'] [TopologicalSpace G']
variable {Γ K Q : Subgroup G} {Γ' K' : Subgroup G'} {π : Q →* G'} {ι : G' →* Q} {c₀ : G → ℂ}
variable {P : Subgroup G} {P' : Subgroup G'} {c : G → ℂ} {c' : G' → ℂ}
namespace GlobalTheory.CompanionTheory.RgTransfer
theorem _root_.solution (hL : IsLevi Γ K Q Γ' K' π ι c₀) (hP : IsPull Q P P' π c₀ c c') {l : G → ℝ}
    {l' : G' → ℝ} (hl : ∀ (q : Q) (k : K), l ((q : G) * k) = l' (π q))
    (hinv : ∀ γ ∈ Γ', γ ∈ P' → ∀ x, l' (γ * x) = l' x) (hc : Conv Γ' P' l') :
    Conv (Γ ⊓ Q) P l := by
  obtain ⟨φ, hφ⟩ := cos_exists hL hP
  intro g
  have h1 := hc (π (qOf hL g))
  rw [← φ.summable_iff] at h1
  refine h1.congr (fun x => ?_)
  obtain ⟨hq, γ, hγ, hγP, h⟩ := hφ x
  simp only [Function.comp]
  rw [rep_mul hq _ _ (qk_spec hL g), hl, map_mul, h, mul_assoc, hinv γ hγ hγP]
end GlobalTheory.CompanionTheory.RgTransfer
