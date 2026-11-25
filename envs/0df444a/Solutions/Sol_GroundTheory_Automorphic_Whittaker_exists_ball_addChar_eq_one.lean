-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_ball_addChar_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:16.756717+00:00
-- url     : https://prove2.me/submissions/ad978cb9-f2dc-480a-b450-13a1ecdb768d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_eq_one_of_forall_norm_zpow_sub_one_lt
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_P2M_GroundTheory_Variant__N1_eq_one_of_forall_norm_zpow_sub_one_lt_cdf30090e0e9
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
open ValuativeRel Topology
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution {ψ₀ : AddChar F ℂ} (hψ : Continuous ψ₀) :
    ∃ γ : (ValueGroupWithZero F)ˣ, ∀ x : F, valuation F x < γ → ψ₀ x = 1 := by
  have hball : {z : ℂ | ‖z - 1‖ < 1} ∈ 𝓝 (ψ₀ 0) := by
    rw [AddChar.map_zero_eq_one]
    have : {z : ℂ | ‖z - 1‖ < 1} = Metric.ball 1 1 := by
      ext z
      simp [dist_eq_norm]
    rw [this]
    exact Metric.ball_mem_nhds 1 one_pos
  obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero F).mem_iff.1
    (hψ.continuousAt.preimage_mem_nhds hball)
  refine ⟨γ, fun x hx => eq_one_of_forall_norm_zpow_sub_one_lt fun m => ?_⟩
  have hmx : m • x ∈ (valuation F).ltAddSubgroup γ :=
    AddSubgroup.zsmul_mem _ (Valuation.mem_ltAddSubgroup_iff.2 hx) m
  have := hγ (Valuation.mem_ltAddSubgroup_iff.1 hmx)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at this
  rwa [AddChar.map_zsmul_eq_zpow] at this
end GroundTheory.Automorphic.Whittaker
