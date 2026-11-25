-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.fixedProj_act_of_normalizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:27.791815+00:00
-- url     : https://prove2.me/submissions/bb9044cf-2f37-4e2b-9105-fa0713226dd9

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_sub_fixedProj_mem
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
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {g : G} (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hg' : ∀ k ∈ K, g⁻¹ * k * g ∈ K) (v : V) :
    (fixedProj ρ hρ hKc hKo (ρ g v) : V) = ρ g (fixedProj ρ hρ hKc hKo v) := by
  have hmem : ρ g (fixedProj ρ hρ hKc hKo v : V) ∈ fixedVectors ρ K := by
    intro k hk
    have hk' : k = g * (g⁻¹ * k * g) * g⁻¹ := by group
    rw [hk', map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      (fixedProj ρ hρ hKc hKo v).2 _ (hg' k hk)]
  have hmap : coinvariantsKer ρ K ≤ (coinvariantsKer ρ K).comap (ρ g) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨k, x⟩, rfl⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, SetLike.mem_coe,
      Submodule.mem_comap, map_sub]
    have hk : ρ g (ρ (k : G) x) = ρ (g * (k : G) * g⁻¹) (ρ g x) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [hk]
    exact sub_mem_coinvariantsKer (hg k k.2) (ρ g x)
  have h := (fixedProj_eq_iff hρ hKc hKo (v := ρ g v) (w := ⟨_, hmem⟩)).2 (by
    show ρ g v - ρ g _ ∈ coinvariantsKer ρ K
    rw [← map_sub]
    exact hmap (sub_fixedProj_mem hρ hKc hKo v))
  exact congrArg Subtype.val h
end GroundTheory.Automorphic.Parabolic
