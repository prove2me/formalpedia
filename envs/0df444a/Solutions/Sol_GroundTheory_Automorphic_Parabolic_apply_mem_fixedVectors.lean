-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.apply_mem_fixedVectors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:58.65262+00:00
-- url     : https://prove2.me/submissions/a1fd836b-da8c-42c7-bb5d-51d14f10894c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_sqrtModular_of_mem_integralGL
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_le
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_conj_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_leviIncl
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
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {m : ℕ}
    (f : fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m)) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) :
    ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) k ∈
      fixedVectors σ ((congruenceSubgroup F n m).subgroupOf (levi F n β)) := by
  intro y hy
  rw [Subgroup.mem_subgroupOf] at hy
  have h1 := ((f : parabolicIndSpace F n β σ).2.1 (leviIncl y) k)
  rw [inflateTwist_apply, leviProj_leviIncl,
    sqrtModular_of_mem_integralGL _ (congruenceSubgroup_le F n m hy), one_smul] at h1
  rw [← h1]
  have hc : k⁻¹ * (y : GL (Fin n) F) * k ∈ congruenceSubgroup F n m := by
    simpa using conj_mem_congruenceSubgroup F n ((integralGL F n).inv_mem hk) hy
  have h2 := congrArg (fun x : parabolicIndSpace F n β σ => (x : GL (Fin n) F → W) k)
    (f.2 _ hc)
  simp only [coe_indRep_apply] at h2
  rw [show ((leviIncl y : blockUpper F n β) : GL (Fin n) F) * k = k * (k⁻¹ * (y : GL (Fin n) F) * k)
    by rw [leviIncl_coe]; group]
  exact h2
end GroundTheory.Automorphic.Parabolic
