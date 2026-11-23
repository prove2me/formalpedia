-- Prove2me | solution 1 for GlobalTheory.AnArc.linearIndependent_Sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:59.206828+00:00
-- url     : https://prove2.me/submissions/4f21019b-0bcf-4315-bca6-464ac7fd6f39

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
namespace GlobalTheory.AnArc
theorem _root_.solution {j : ℕ} (hj : j ≠ 0) {ι : Type*} (wt : ι → A.X)
    (hwt : ∀ p p' μ, wt p = wt p' + j • μ → wt p = wt p') (th : ι → (Fin A.gB → ℂ) → ℂ)
    (hth : ∀ α, LinearIndepOn ℂ th {p | wt p = α}) (w : ℂ)
    (hs : ∀ p z, Summable fun μ => A.term j (wt p) (th p) μ (0, z) * eTwoPi (w * A.exponent j (wt p) μ)) :
    LinearIndependent ℂ fun p => A.Sum j (wt p) (th p) w := by
  classical
  refine linearIndependent_iff'.2 fun s r hr => eq_zero_of_sum_filter hth fun p₀ z => ?_
  have := A.sum_coeff_eq_zero hj s wt hwt
    (a := fun p μ => r p * (A.term j (wt p) (th p) μ (0, z) * eTwoPi (w * A.exponent j (wt p) μ)))
    (fun p _ => (hs p z).mul_left _) (fun l _ => ?_) p₀ 0
  · simpa using this
  · refine Eq.trans ?_ (congrFun hr (l, z))
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Sum, ← tsum_mul_left]
    exact tsum_congr fun μ => by rw [A.term_eq_mul_char j _ _ μ l z]; ring
end GlobalTheory.AnArc
