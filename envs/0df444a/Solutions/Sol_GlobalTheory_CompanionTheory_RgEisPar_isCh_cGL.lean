-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisPar.isCh_cGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:08:00.455123+00:00
-- url     : https://prove2.me/submissions/152b15b0-8fbc-4ae7-9d03-e0f2a68850ad

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_continuous_circle_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_stab_univ_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisPar
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
namespace GlobalTheory.CompanionTheory.RgEisPar
theorem _root_.solution (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (κ : Type) [Fintype κ] [DecidableEq κ] :
    IsCh (A.ratGL κ) ⊤ (A.cGL κ) := by
  obtain ⟨-, hm, hcont, hr, -, hd⟩ := hB E R A hA κ Set.univ
  have htop : ∀ g : GL κ R, g ∈ stab R (Set.univ : Set κ) := fun g => by
    rw [stab_univ_eq_top]; trivial
  have hc : ∀ g : GL κ R, A.cGL κ g = A.χ (bdet Set.univ g) := fun g => by
    rw [hd]; rfl
  refine ⟨fun p _ q _ => ?_, fun p _ => ?_, fun γ hγ _ => ?_, ?_⟩
  · rw [hc, hc, hc, hm p (htop p) q (htop q), map_mul, Circle.coe_mul]
  · rw [hc]; exact Circle.norm_coe _
  · obtain ⟨x, hx⟩ := hr γ (htop γ) hγ
    rw [hc, hx, hA.χi, Circle.coe_one]
  · have hcon : Continuous (bdet (R := R) (Set.univ : Set κ)) := by
      rw [← continuousOn_univ]
      refine hcont.mono fun g _ => htop g
    have : A.cGL κ = fun g => ((A.χ (bdet Set.univ g) : Circle) : ℂ) := funext hc
    rw [this]
    exact (continuous_circle_coe.comp (hA.χcont.comp hcon)).continuousOn
end GlobalTheory.CompanionTheory.RgEisPar
