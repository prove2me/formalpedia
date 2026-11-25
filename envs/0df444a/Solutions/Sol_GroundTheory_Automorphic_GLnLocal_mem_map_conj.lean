-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.mem_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:47.204334+00:00
-- url     : https://prove2.me/submissions/fb493b8e-3236-4042-8410-e35d1d40e2b1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
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
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {g x : GL (Fin n) F} {H : Subgroup (GL (Fin n) F)} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * (MulAut.conj g).toMonoidHom y * g = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [this]
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
end GroundTheory.Automorphic.GLnLocal
