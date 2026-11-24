-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Plucker.cGL_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:08.494583+00:00
-- url     : https://prove2.me/submissions/b8142ed6-b205-408d-87b2-5c20851b9736

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConvergenceGroupOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_cGL_inv_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Plucker_mem_stab

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
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {m : Type} [Fintype m] [DecidableEq m]
namespace GlobalTheory.CompanionTheory.Plucker
theorem _root_.solution {t₀ : Sub ι m} {p : GL ι R} (hp : p ∈ stab R (t₀.1 : Set ι)) :
    cGL m p ∈ stab R ({t₀} : Set (Sub ι m)) := by
  rw [mem_stab] at hp ⊢
  intro r hr c hc
  have hc' : c = t₀ := hc
  subst hc'
  have hr' : r ≠ c := hr
  refine ⟨cmp_eq_zero_of_block _ hr' fun a ha b hb => (hp a ha b hb).1, ?_⟩
  rw [cGL_inv_coe]
  exact cmp_eq_zero_of_block _ hr' fun a ha b hb => (hp a ha b hb).2
end GlobalTheory.CompanionTheory.Plucker
