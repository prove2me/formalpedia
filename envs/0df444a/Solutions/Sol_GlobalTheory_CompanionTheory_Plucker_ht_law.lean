-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.ht_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:08:34.110133+00:00
-- url     : https://prove2.me/submissions/45783b8c-a35f-43df-bbbd-3b08b757b28f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Plucker
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.GoodL) (ι : Type) [Fintype ι] [DecidableEq ι] (s : Set ι) :
    IsHt (A.ratGL ι) (A.kGL ι) (stab R s) (A.htGL s) ∧
      ∀ p ∈ stab R s, ∀ k ∈ A.kGL ι, A.htGL s (p * k) = A.lg (bdet s p) := by
  obtain ⟨cl, mul, cont, rat, kk, -⟩ := hB E R A hA ι s
  refine hE (GL ι R) (A.ratGL ι) (A.kGL ι) (stab R s) (fun p => A.lg (bdet s p)) (hA.kcpt ι) cl (hA.iwa ι s)
    (fun p hp q hq => ?_) (hA.lgcont.comp_continuousOn cont) (fun p hp hk => kk p hp hk) (fun p hp hΓ => ?_)
  · simp only [mul p hp q hq, hA.lgmul]
  · obtain ⟨x, hx⟩ := rat p hp hΓ
    simp only [hx, hA.lgi x]
end GlobalTheory.CompanionTheory.Plucker
