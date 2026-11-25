-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:36:26.375845+00:00
-- url     : https://prove2.me/submissions/4b06e9ae-e58f-42c4-862e-7f92b5f83e7f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_congruenceSubgroup_iwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_jacquetFixedMap_surjective


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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsAdmissible π) {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (jacquetFixedMap F n β π (congruenceSubgroup F n m)) :=
  jacquetFixedMap_surjective hπ (isCompact_congruenceSubgroup F n m)
    (isOpen_congruenceSubgroup F n m) (congruenceSubgroup_iwahoriFactorization β hm)
end GroundTheory.Automorphic.Parabolic
