-- Prove2me | solution 1 for GroundTheory.Automorphic.map_mem_coinvariantsKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:57:15.394083+00:00
-- url     : https://prove2.me/submissions/b821b1a7-3bf9-4f04-9b3b-d6deaa0a0ecb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Function Parabolic
universe u
variable {G : Type*} [Group G] [TopologicalSpace G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
omit [TopologicalSpace G]
namespace GroundTheory.Automorphic
theorem _root_.solution {π : Representation ℂ G W} (p : Representation.IntertwiningMap ρ π)
    (N : Subgroup G) {x : V} (hx : x ∈ Representation.Coinvariants.ker (ρ.comp N.subtype)) :
    p x ∈ Representation.Coinvariants.ker (π.comp N.subtype) := by
  have hle : Representation.Coinvariants.ker (ρ.comp N.subtype) ≤
      (Representation.Coinvariants.ker (π.comp N.subtype)).comap p.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, v⟩, rfl⟩
    simp only [MonoidHom.coe_comp, comp_apply, Subgroup.coe_subtype, SetLike.mem_coe,
      Submodule.mem_comap, map_sub, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Representation.IntertwiningMap.isIntertwining]
    exact Representation.Coinvariants.sub_mem_ker (ρ := π.comp N.subtype) u (p v)
  exact hle hx
end GroundTheory.Automorphic
