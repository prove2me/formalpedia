-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisPar.isCh_uC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:08:27.608998+00:00
-- url     : https://prove2.me/submissions/ac91567d-09c5-4cf4-915b-522df68736b2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_continuous_circle_coe

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
theorem _root_.solution (hB : BdetLaw) (A : Ad E R) (hA : A.GoodL) (ε : ℤˣ) {κ : Type} [Fintype κ] [DecidableEq κ] :
    IsCh (A.uΓ ε κ) (A.uQ ε (Set.univ : Set κ)) (A.uC ε κ) := by
  obtain ⟨-, hm, hcont, hr, -, -⟩ := hB E R A hA (κ ⊕ κ) (Sum.inl '' (Set.univ : Set κ))
  refine ⟨fun p hp q hq => ?_, fun p _ => Circle.norm_coe _, fun γ hγ hp => ?_, ?_⟩
  · simp only [Ad.uC, Subgroup.coe_mul, hm p.1 hp q.1 hq, map_mul, Circle.coe_mul]
  · obtain ⟨x, hx⟩ := hr γ.1 hp hγ
    simp only [Ad.uC, hx, hA.χi, Circle.coe_one]
  · exact continuous_circle_coe.comp_continuousOn
      (hA.χcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx))
end GlobalTheory.CompanionTheory.RgEisPar
