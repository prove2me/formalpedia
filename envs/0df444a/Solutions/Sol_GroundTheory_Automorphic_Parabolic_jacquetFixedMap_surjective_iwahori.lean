-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:02.322441+00:00
-- url     : https://prove2.me/submissions/14bee671-2de1-4800-b417-ab307654c63a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_iwahori_iwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_iwahori
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isOpen_iwahori
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
variable {β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsAdmissible π) (hβ : Monotone β) :
    Function.Surjective (jacquetFixedMap F n β π (iwahori F n)) :=
  jacquetFixedMap_surjective hπ (isCompact_iwahori F n) (isOpen_iwahori F n)
    (iwahori_iwahoriFactorization hβ)
end GroundTheory.Automorphic.Parabolic
