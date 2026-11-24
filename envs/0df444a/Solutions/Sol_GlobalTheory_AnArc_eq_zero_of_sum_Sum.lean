-- Prove2me | solution 1 for GlobalTheory.AnArc.eq_zero_of_sum_Sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:57:42.632636+00:00
-- url     : https://prove2.me/submissions/a87ab878-f8fe-495e-a35b-72c4dceeeb2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_linearIndependent_Sum_sigma

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
variable [Fintype C] [∀ c, Fintype (I c)]
namespace GlobalTheory.AnArc
theorem _root_.solution (hj : j ≠ 0) (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c)) {w : ℂ}
    (hs : ∀ c i z, Summable fun μ => A.term j (rep c) (th c i) μ (0, z) * eTwoPi (w * A.exponent j (rep c) μ))
    {r : ∀ c, I c → ℂ} (h : ∀ v, ∑ c, ∑ i, r c i * A.Sum j (rep c) (th c i) w v = 0) (c : C) (i : I c) :
    r c i = 0 :=
  Fintype.linearIndependent_iff.1 (A.linearIndependent_Sum_sigma hj hrep hth w hs) (fun p => r p.1 p.2)
    (funext fun v => by simpa [Finset.sum_apply, Fintype.sum_sigma] using h v) ⟨c, i⟩
end GlobalTheory.AnArc
