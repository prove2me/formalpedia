-- Prove2me | solution 1 for GlobalTheory.discreteTopology_periodLattice_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:19.383282+00:00
-- url     : https://prove2.me/submissions/07e75d10-979f-4246-b2ed-3d3f35694800

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Theorems.Thm_GlobalTheory_continuous_periodCoordFst
import Theorems.Thm_GlobalTheory_continuous_periodCoordSnd
import Theorems.Thm_GlobalTheory_intVec_eq_zero_of_periodCoord_lt_one
import Theorems.Thm_GlobalTheory_periodCoordFst_zero
import Theorems.Thm_GlobalTheory_periodCoordSnd_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {τ : Matrix ι ι ℂ}
    (hτ : IsUnit (τ.map Complex.im).det) : DiscreteTopology (periodLattice τ) := by
  apply discreteTopology_of_isOpen_singleton_zero
  have hO : IsOpen ((⋂ i, {w : ι → ℂ | |periodCoordFst τ w i| < 1}) ∩
      ⋂ i, {w : ι → ℂ | |periodCoordSnd τ w i| < 1}) := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun i => ?_)
      (isOpen_iInter_of_finite fun i => ?_)
    · exact isOpen_lt (((continuous_apply i).comp (continuous_periodCoordFst τ)).abs)
        continuous_const
    · exact isOpen_lt (((continuous_apply i).comp (continuous_periodCoordSnd τ)).abs)
        continuous_const
  convert hO.preimage (continuous_subtype_val (p := fun w => w ∈ periodLattice τ)) using 1
  ext ⟨w, hw⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_setOf_eq]
  constructor
  · intro h
    have h0 : w = 0 := congrArg Subtype.val h
    subst h0
    simp [periodCoordFst_zero, periodCoordSnd_zero]
  · rintro ⟨h₁, h₂⟩
    obtain ⟨n, n', rfl⟩ := hw
    obtain ⟨rfl, rfl⟩ := intVec_eq_zero_of_periodCoord_lt_one hτ n n' h₁ h₂
    apply Subtype.ext
    simp [ofIntVec_zero]
end GlobalTheory
