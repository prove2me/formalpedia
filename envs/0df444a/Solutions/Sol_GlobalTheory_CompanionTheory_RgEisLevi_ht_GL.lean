-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.ht_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:17.929869+00:00
-- url     : https://prove2.me/submissions/ef800e02-2008-4347-b56d-b86a80e1a275

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.Good) (s : Set ι) (p : GL ι R) (hp : p ∈ stab R s)
    (k : GL ι R) (hk : k ∈ A.kGL ι) : A.htGL s (p * k) = A.lg (bdet s p) := by
  have hb := hB E R A hA.toGoodL ι s
  exact (hE (GL ι R) (A.kGL ι) (A.kGL ι) (stab R s) (fun p => A.lg (bdet s p)) (hA.kcpt ι) hb.1 (hA.iwa ι s)
    (fun p hp q hq => by simp only [hb.2.1 p hp q hq, hA.lgmul]) (hA.lgcont.comp_continuousOn hb.2.2.1)
    (fun p hp hk => hb.2.2.2.2.1 p hp hk) (fun p hp hk => hb.2.2.2.2.1 p hp hk)).2 p hp k hk
end GlobalTheory.CompanionTheory.RgEisLevi
