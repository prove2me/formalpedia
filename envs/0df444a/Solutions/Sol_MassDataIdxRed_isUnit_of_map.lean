-- Prove2me | solution 1 for MassDataIdxRed.isUnit_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:45.06626+00:00
-- url     : https://prove2.me/submissions/d83bc9f5-5db9-4adf-829d-83b67bf417c4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GlRedEqOneIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxRed
open Matrix
namespace MassDataIdxRed
theorem _root_.solution {R S : Type} [CommRing R] [IsLocalRing R] [Field S] (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (h : IsUnit (π r)) : IsUnit r := by
  by_contra hr
  have hk : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
  have hm : r ∈ RingHom.ker π := by
    rw [hk]; exact (IsLocalRing.mem_maximalIdeal r).2 hr
  rw [RingHom.mem_ker] at hm
  rw [hm] at h
  exact not_isUnit_zero h
end MassDataIdxRed
