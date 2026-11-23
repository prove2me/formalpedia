-- Prove2me | solution 1 for GlobalTheory.AnArc.linearIndependent_Sum_sigma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:34.679539+00:00
-- url     : https://prove2.me/submissions/d7fa40fe-3cf2-477b-be77-41e4456324ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_linearIndependent_Sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable {C : Type*} {I : C → Type*} {j : ℕ} {rep : C → A.X}
namespace GlobalTheory.AnArc
theorem _root_.solution (hj : j ≠ 0) (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c)) (w : ℂ)
    (hs : ∀ c i z, Summable fun μ => A.term j (rep c) (th c i) μ (0, z) * eTwoPi (w * A.exponent j (rep c) μ)) :
    LinearIndependent ℂ fun p : Σ c, I c => A.Sum j (rep p.1) (th p.1 p.2) w :=
  A.linearIndependent_Sum hj (fun p : Σ c, I c => rep p.1) (fun _ _ μ h => congrArg rep (hrep _ _ μ h)) _
    (linearIndepOn_sigma (fun c c' h => hrep c c' 0 (by simpa using h)) hth) w fun p => hs p.1 p.2
end GlobalTheory.AnArc
