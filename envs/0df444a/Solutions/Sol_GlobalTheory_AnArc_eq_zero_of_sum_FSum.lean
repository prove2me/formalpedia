-- Prove2me | solution 1 for GlobalTheory.AnArc.eq_zero_of_sum_FSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:52.644243+00:00
-- url     : https://prove2.me/submissions/bf883d27-7a8b-4f20-9cc5-6cd4e157fcb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv

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
theorem _root_.solution [NeZero j] (hrep : ∀ c c' μ, rep c = rep c' + j • μ → c = c')
    {th : ∀ c, I c → (Fin A.gB → ℂ) → ℂ} (hth : ∀ c, LinearIndependent ℂ (th c))
    {r : ∀ c, I c → LaurentSeries ℂ} (h : ∀ v, ∑ c, ∑ i, r c i * A.FSum j (rep c) (th c i) v = 0) (c : C) (i : I c) :
    r c i = 0 :=
  Fintype.linearIndependent_iff.1 (A.linearIndependent_FSum_sigma hrep hth) (fun p => r p.1 p.2)
    (funext fun v => by simpa [Finset.sum_apply, Fintype.sum_sigma] using h v) ⟨c, i⟩
end GlobalTheory.AnArc
