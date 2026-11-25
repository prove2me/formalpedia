-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_unipotentCompactG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:34:38.153795+00:00
-- url     : https://prove2.me/submissions/fe178570-f071-49a3-816b-9a30c214b1e9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable (γ : Fin n → ℕ)
variable {γ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {e : ℕ} {u : GL (Fin n) F} :
    u ∈ unipotentCompactG γ e ↔ u ∈ unipotentRadical F n γ ∧
      rankTorus F n γ e * u * (rankTorus F n γ e)⁻¹ ∈ integralGL F n := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, mem_unipotentCompact.1 hv⟩
  · rintro ⟨hu, h⟩
    exact ⟨⟨u, hu⟩, mem_unipotentCompact.2 h, rfl⟩
end GroundTheory.Automorphic.Parabolic
