-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_apply_eq_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:59:36.92883+00:00
-- url     : https://prove2.me/submissions/ad83b42e-cdd9-4406-8ef2-813edb521e3f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Theorems.Thm_P2M_GroundTheory_Automorphic_Parabolic_exists_blockUpper_mul_integralGL__7c8211cc1088
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
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (m : ℕ) (x : GL (Fin n) F) :
    ∃ (p : blockUpper F n β) (c : integralGL F n ⧸ (congruenceSubgroup F n m).subgroupOf
      (integralGL F n)), ∀ f : fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m),
      ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) x =
        sqrtModular F n β p • σ (leviProj F n β p)
          (((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W)
            ((Quotient.out c : integralGL F n) : GL (Fin n) F)) := by
  obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL' (β := β) x
  set K₀ := integralGL F n
  set Km := congruenceSubgroup F n m
  set c : K₀ ⧸ Km.subgroupOf K₀ := QuotientGroup.mk (⟨k, hk⟩ : K₀)
  refine ⟨⟨p, hp⟩, c, fun f => ?_⟩
  have h1 := ((f : parabolicIndSpace F n β σ).2.1 ⟨p, hp⟩ k)
  simp only [inflateTwist_apply] at h1
  rw [h1]
  obtain ⟨y, hyk⟩ := QuotientGroup.mk_out_eq_mul (Km.subgroupOf K₀) (⟨k, hk⟩ : K₀)
  have hym : (((y : K₀)⁻¹ : K₀) : GL (Fin n) F) ∈ Km :=
    Subgroup.mem_subgroupOf.1 ((Km.subgroupOf K₀).inv_mem y.2)
  have h2 := congrArg
    (fun z : parabolicIndSpace F n β σ => (z : GL (Fin n) F → W) ((Quotient.out c : K₀) : GL (Fin n) F))
    (f.2 _ hym)
  simp only [coe_indRep_apply] at h2
  have h3 : ((Quotient.out c : K₀) : GL (Fin n) F) * (((y : K₀)⁻¹ : K₀) : GL (Fin n) F) = k := by
    have : (Quotient.out c : K₀) = ⟨k, hk⟩ * (y : K₀) := hyk
    rw [this]
    simp
  rw [h3] at h2
  rw [h2]
end GroundTheory.Automorphic.Parabolic
