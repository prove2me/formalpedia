-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_unipotentCompact_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:27.916978+00:00
-- url     : https://prove2.me/submissions/c987475b-ec0b-4b91-9f11-23e5f44efc7d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_conj_apply_mem
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompact

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
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {e : ℕ} {u : unipotentRadical F n β}
    (hb : ∀ i j, (GLnLocal.uniformizer F : F) ^ e * (u : GL (Fin n) F) i j ∈ 𝒪[F])
    (hb' : ∀ i j, (GLnLocal.uniformizer F : F) ^ e * ((u : GL (Fin n) F)⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F]) :
    u ∈ unipotentCompact F n β e := by
  rw [mem_unipotentCompact, mem_integralGL_iff]
  refine ⟨rankTorus_conj_apply_mem u.2 hb, fun i j => ?_⟩
  have : (rankTorus F n β e * u * (rankTorus F n β e)⁻¹)⁻¹ =
      rankTorus F n β e * (u : GL (Fin n) F)⁻¹ * (rankTorus F n β e)⁻¹ := by group
  rw [this]
  exact rankTorus_conj_apply_mem ((unipotentRadical F n β).inv_mem u.2) hb' i j
end GroundTheory.Automorphic.Parabolic
