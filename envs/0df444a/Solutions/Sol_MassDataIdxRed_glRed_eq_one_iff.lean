-- Prove2me | solution 1 for MassDataIdxRed.glRed_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:12.834028+00:00
-- url     : https://prove2.me/submissions/a7c9d183-b23d-4e56-b202-e4ebe7bfeaa8

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
    (π : R →+* S) (A : GL ι R) :
    glRed π A = 1 ↔ ∀ i j, ((A : Matrix ι ι R) - 1) i j ∈ RingHom.ker π := by
  rw [← Units.val_inj, glRed_coe, Units.val_one]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.map_apply] at hij
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    ext i j
    have hij := h i j
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero] at hij
    rw [Matrix.map_apply, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
end MassDataIdxRed
