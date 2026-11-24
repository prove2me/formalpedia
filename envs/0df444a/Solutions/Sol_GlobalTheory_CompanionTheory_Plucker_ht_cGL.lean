-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.ht_cGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:46.66134+00:00
-- url     : https://prove2.me/submissions/4d46e427-a5e3-41e4-9e6c-e99d0291ebca

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_stab
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_k
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_bdet_cGL
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_ht_law

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
theorem _root_.solution (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.GoodL) (t₀ : Sub ι m) (g : GL ι R) :
    A.htGL ({t₀} : Set (Sub ι m)) (cGL m g) = A.htGL (t₀.1 : Set ι) g := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hA.iwa ι (t₀.1 : Set ι) g
  rw [map_mul, (ht_law hB hE A hA _ _).2 _ (cGL_stab hp) _ (cGL_k A hk), bdet_cGL, (ht_law hB hE A hA _ _).2 _ hp _ hk]
end GlobalTheory.CompanionTheory.Plucker
