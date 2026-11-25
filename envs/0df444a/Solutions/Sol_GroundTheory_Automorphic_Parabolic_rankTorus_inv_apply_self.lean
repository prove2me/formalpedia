-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.rankTorus_inv_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:09.067255+00:00
-- url     : https://prove2.me/submissions/3b3e8686-20a9-4785-8a89-8cc6d4b04d43

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_coe_torusPow
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_torusPow_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {α : Type*} [LinearOrder α] (β : Fin n → α) (e : ℕ)
    (i : Fin n) :
    ((rankTorus F n β e)⁻¹ : GL (Fin n) F) i i =
      (uniformizer F : F) ^ (((e * blockRank β i : ℕ) : ℤ)) := by
  show (((rankTorus F n β e)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = _
  rw [rankTorus, ← torusPow_neg, coe_torusPow, diagonal_apply_eq, Pi.neg_apply, neg_neg]
end GroundTheory.Automorphic.Parabolic
