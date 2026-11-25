-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_unipotentCompactG_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:33:35.247348+00:00
-- url     : https://prove2.me/submissions/a8fc02d1-beff-4304-aefa-b173cfccbc1f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompact_of_bound


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
theorem _root_.solution {e : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ unipotentRadical F n γ)
    (hb : EntryBound F e (u : Matrix (Fin n) (Fin n) F))
    (hb' : EntryBound F e ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) :
    u ∈ unipotentCompactG γ e :=
  ⟨⟨u, hu⟩, mem_unipotentCompact_of_bound (u := ⟨u, hu⟩) hb hb', rfl⟩
end GroundTheory.Automorphic.Parabolic
