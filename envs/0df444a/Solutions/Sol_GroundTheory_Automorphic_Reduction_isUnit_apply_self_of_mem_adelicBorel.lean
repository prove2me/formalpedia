-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.isUnit_apply_self_of_mem_adelicBorel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:27:26.362104+00:00
-- url     : https://prove2.me/submissions/df061472-6ad2-4ab4-9bbd-00056898c2b5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] {n : ℕ}
variable [NumberField K]
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {b : AdelicGLn.AdelicGL K n} (hb : b ∈ adelicBorel)
    (i : Fin n) : IsUnit ((b : Matrix (Fin n) (Fin n) 𝔸[K]) i i) := by
  have hdet : IsUnit (b : Matrix (Fin n) (Fin n) 𝔸[K]).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 b.isUnit
  rw [Matrix.det_of_isUpperTriangular hb] at hdet
  exact isUnit_of_dvd_unit
    (Finset.dvd_prod_of_mem (fun j => (b : Matrix (Fin n) (Fin n) 𝔸[K]) j j) (Finset.mem_univ i)) hdet
end GroundTheory.Automorphic.Reduction
