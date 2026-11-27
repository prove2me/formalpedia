-- Prove2me | solution 1 for GroundTheory.Automorphic.GLnLocal.isMaximalCompact_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:43:24.502616+00:00
-- url     : https://prove2.me/submissions/4ee7aceb-f0e9-4fe1-ac75-02213525ff66

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_conj_le_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_map_conj
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_map_conj
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_eq_integralGL_of_isCompact_of_le
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL


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
open ValuativeRel Topology Filter Set
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.GLnLocal
theorem _root_.solution {H : Subgroup (GL (Fin n) F)} :
    IsMaximalCompact H ↔ ∃ g : GL (Fin n) F, H = (integralGL F n).map (MulAut.conj g).toMonoidHom := by
  constructor
  · rintro ⟨hc, hmax⟩
    obtain ⟨g, hg⟩ := exists_conj_le_integralGL F n hc
    refine ⟨g, (hmax _ (isCompact_map_conj F n g (isCompact_integralGL F n))
      fun h hh => (mem_map_conj F n).mpr (hg h hh)).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨isCompact_map_conj F n g (isCompact_integralGL F n), fun H' hH' hle => ?_⟩

    have hK : integralGL F n ≤ H'.map (MulAut.conj g⁻¹).toMonoidHom := fun k hk => by
      rw [mem_map_conj, inv_inv]
      have : g * k * g⁻¹ ∈ (integralGL F n).map (MulAut.conj g).toMonoidHom := by
        rw [mem_map_conj]
        have : g⁻¹ * (g * k * g⁻¹) * g = k := by group
        rwa [this]
      exact hle this
    have heq := eq_integralGL_of_isCompact_of_le F n (isCompact_map_conj F n g⁻¹ hH') hK
    refine le_antisymm (fun h hh => ?_) hle
    rw [mem_map_conj]
    have : g⁻¹ * h * g ∈ H'.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [mem_map_conj, inv_inv]
      have : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      rwa [this]
    rwa [heq] at this
end GroundTheory.Automorphic.GLnLocal
