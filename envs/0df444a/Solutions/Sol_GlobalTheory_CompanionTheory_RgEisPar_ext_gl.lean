-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisPar.ext_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:40.364527+00:00
-- url     : https://prove2.me/submissions/1f0c3e76-c5fe-479a-bc88-981b7cd24e68

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDet

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
theorem _root_.solution (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (κ : Type) [Fintype κ] [DecidableEq κ]
    (t : Set κ) : IsHt (A.ratGL κ) (A.kGL κ) (stab R t) (A.htGL t) ∧
      ∀ p ∈ stab R t, ∀ k ∈ A.kGL κ, A.htGL t (p * k) = A.lg (bdet t p) := by
  obtain ⟨hc, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL κ t
  haveI : T2Space (GL κ R) := (hT E R A hA κ 1).1
  refine hE (GL κ R) (A.ratGL κ) (A.kGL κ) (stab R t) (fun p => A.lg (bdet t p)) (hA.kcpt κ) hc (hA.iwa κ t) ?_ ?_ hk ?_
  · intro p hp q hq
    simp only [hm p hp q hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn hcont
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p hp hg
    simp only [hx, hA.lgi x]
end GlobalTheory.CompanionTheory.RgEisPar
