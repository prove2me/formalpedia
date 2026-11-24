-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabEq.hform_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:11.66266+00:00
-- url     : https://prove2.me/submissions/9733f3c7-9de3-49a8-bf3e-6dcc0ac9f035

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_hform_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabEq
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.UnitVectorStabEq
theorem _root_.solution (s : A →+* A) (J : Matrix n n A) (x y : n → A) (a : A) :
    Formalism.UG.hform s J x (y - a • x) = Formalism.UG.hform s J x y - a * Formalism.UG.hform s J x x := by
  simp only [hform_eq, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]
end GlobalTheory.UnitVectorStabEq
