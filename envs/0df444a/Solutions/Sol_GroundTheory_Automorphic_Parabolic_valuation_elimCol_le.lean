-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.valuation_elimCol_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:28.515891+00:00
-- url     : https://prove2.me/submissions/bf95c4d4-0f62-476d-95ed-09ca10ee4a71

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_antitone
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_one_le_iwahori
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_iwahori_iff


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
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) {h : GL (Fin n) F}
    (hh : h ∈ congruenceSubgroup F n m) (a i k : Fin n) :
    valuation F (elimCol β (h : Matrix (Fin n) (Fin n) F) a i k) ≤ valuation F ϖ ^ m := by
  rw [elimCol_apply]
  split_ifs with hik
  · have hia : i ≠ a := fun hh' => lt_irrefl _ (hh' ▸ hik.2)
    have h1 := ((mem_congruenceSubgroup_iff F n).1 hh).2 i a
    rw [one_apply_ne hia, sub_zero] at h1
    have hdiag := ((mem_iwahori_iff F n).1
      (congruenceSubgroup_one_le_iwahori F n (congruenceSubgroup_antitone F n hm hh))).2.2 a
    rw [map_div₀, hdiag, div_one]
    exact h1
  · rw [map_zero]
    exact zero_le
end GroundTheory.Automorphic.Parabolic
