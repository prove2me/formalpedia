-- Prove2me | solution 1 for MassDataIdxRed.glRed_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:39.08806+00:00
-- url     : https://prove2.me/submissions/5e5816b2-a4d7-4c94-93d2-b45005e98428

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GlRedEqOneIff
import Theorems.Thm_MassDataIdxRed_glRed_coe

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
theorem _root_.solution {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hloc : ∀ r, IsUnit (π r) → IsUnit r) :
    Function.Surjective (glRed (ι := ι) π) := by
  intro B
  choose f hf using hπ
  set A0 : Matrix ι ι R := (B : Matrix ι ι S).map f with hA0def
  have hA0 : A0.map π = (B : Matrix ι ι S) := by
    ext i j; simp [A0, hf]
  have hdet : IsUnit A0.det := by
    apply hloc
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA0]
    exact (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  refine ⟨Matrix.nonsingInvUnit A0 hdet, ?_⟩
  apply Units.ext
  rw [glRed_coe]
  exact hA0
end MassDataIdxRed
