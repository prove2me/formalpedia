-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.prodFrom_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:56.486078+00:00
-- url     : https://prove2.me/submissions/c046933b-f3f1-470a-a6bf-abbecfe7e7f0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (t : Fin n → Fˣ) (x : Fin n) :
    prodFrom t x.val = (t x : F) * prodFrom t (x.val + 1) := by
  classical
  unfold prodFrom
  have e : (Finset.univ.filter fun y : Fin n => x.val ≤ y.val) =
      insert x (Finset.univ.filter fun y : Fin n => x.val + 1 ≤ y.val) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [e, Finset.prod_insert (by simp)]
end GroundTheory.Automorphic.Whittaker
