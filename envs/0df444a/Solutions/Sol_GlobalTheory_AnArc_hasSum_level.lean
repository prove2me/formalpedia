-- Prove2me | solution 1 for GlobalTheory.AnArc.hasSum_level
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:44.351346+00:00
-- url     : https://prove2.me/submissions/bbdcd45a-80e0-47a5-b291-4aa9f6774a1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable {A} {T₀ : ℝ} (hT : A.IsConvLine T₀) {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ}
include hT
variable [NeZero j]
omit hT
namespace GlobalTheory.AnArc
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : A.X → E} {a : E} (hf : HasSum f a) :
    HasSum (fun n : ℤ => ∑ μ ∈ A.level j α n, f μ) a := by
  convert hf.tsum_fiberwise (A.exponent j α) using 2 with n
  have : A.exponent j α ⁻¹' {n} = (A.level j α n : Set A.X) := by ext; simp
  rw [this, Finset.tsum_subtype']
end GlobalTheory.AnArc
