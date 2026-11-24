-- Prove2me | solution 1 for GlobalTheory.measure_le_two_pow_mul_covolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:56.153351+00:00
-- url     : https://prove2.me/submissions/83e91aee-1434-4b9f-9d70-17a588db0e3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace GlobalTheory
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hsymm : ∀ x ∈ s, -x ∈ s) (hconv : Convex ℝ s)
    (hL : ∀ x ∈ L, x ≠ 0 → x ∉ s) :
    μ s ≤ ENNReal.ofReal (2 ^ finrank ℝ E * ZLattice.covolume L μ) := by
  by_contra! hlt
  let b := Free.chooseBasis ℤ L
  have fund : IsAddFundamentalDomain L.toAddSubgroup
      (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) μ :=
    ZLattice.isAddFundamentalDomain b μ
  have hc : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain L μ
    (ZLattice.isAddFundamentalDomain b μ)
  have hfin : μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund
    hsymm hconv (by
      rwa [← ENNReal.ofReal_toReal hfin, ← measureReal_def, ← hcov, ← ENNReal.ofReal_ofNat,
        ← ENNReal.ofReal_pow (by norm_num),
        ← ENNReal.ofReal_mul (ZLattice.covolume_pos L μ).le, mul_comm])
  exact hL x x.2 (fun h ↦ hx0 (Subtype.ext h)) hxs
end GlobalTheory
