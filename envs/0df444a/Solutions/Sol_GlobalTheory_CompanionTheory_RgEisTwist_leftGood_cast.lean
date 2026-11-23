-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisTwist.leftGood_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:23.648464+00:00
-- url     : https://prove2.me/submissions/7244c9b8-7135-4754-90f1-5ed16fb3e888

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
theorem _root_.solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {A B : Submodule ℂ W} (e : A = B)
    {Op : ℂ → (X →L[ℂ] A)} {a : ℝ} (hO : LeftGood Op a) :
    LeftGood (fun z => (castL e).comp (Op z)) a := by
  subst e
  have hid : (fun z => (castL (rfl : A = A)).comp (Op z)) = Op := by
    funext z
    ext x
    rfl
  rwa [hid]
end GlobalTheory.CompanionTheory.RgEisTwist
