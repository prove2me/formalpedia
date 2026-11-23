-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisGal.lineHol_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:15.071826+00:00
-- url     : https://prove2.me/submissions/d4c84ddd-c092-4cd4-8667-f7293fa6b862

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DifferentiableAffLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChamberPairThreeFour

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisGal
namespace GlobalTheory.CompanionTheory.RgEisGal
theorem _root_.solution (U : Set (ℂ × ℂ)) : LineHol (fun l : ℂ × ℂ => Complex.exp (l.1 ^ 2 + l.2 ^ 2)) U := by
  intro p v
  apply Differentiable.differentiableOn
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  fun_prop
end GlobalTheory.CompanionTheory.RgEisGal
