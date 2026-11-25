-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.rankTorus_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:05.472495+00:00
-- url     : https://prove2.me/submissions/899b0e71-35f5-4d36-a774-e082ee655200

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_coe_torusPow


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
theorem _root_.solution {α : Type*} [LinearOrder α] (β : Fin n → α) (e : ℕ) (i : Fin n) :
    (rankTorus F n β e : GL (Fin n) F) i i =
      (uniformizer F : F) ^ (-((e * blockRank β i : ℕ) : ℤ)) := by
  show ((rankTorus F n β e : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = _
  rw [rankTorus, coe_torusPow, diagonal_apply_eq]
end GroundTheory.Automorphic.Parabolic
