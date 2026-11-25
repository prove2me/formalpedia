-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.bumpFun_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:24:09.557971+00:00
-- url     : https://prove2.me/submissions/d49e4c98-7bed-4f0f-a48a-fb75196cde18

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_bumpFun_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_bumpFun_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_parabolicIndSpace
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
variable {σ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)}
    (hK : IsOpen (K : Set (GL (Fin n) F))) {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ K.map (MulAut.conj x).toMonoidHom →
      inflateTwist F n β σ p v = v) :
    bumpFun σ x K v ∈ parabolicIndSpace F n β σ := by
  refine (mem_parabolicIndSpace σ).2 ⟨fun p₀ g => ?_, K, hK, fun k' hk' g => ?_⟩
  · by_cases h : ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k
    · obtain ⟨p, k, hk, rfl⟩ := h
      have e : (p₀ : GL (Fin n) F) * ((p : GL (Fin n) F) * x * k) =
          ((p₀ * p : blockUpper F n β) : GL (Fin n) F) * x * k := by
        simp only [Subgroup.coe_mul]
        group
      rw [e, bumpFun_apply hv _ hk, bumpFun_apply hv _ hk, ← inflateTwist_apply, map_mul,
        Module.End.mul_apply]
    · have h' : ¬ ∃ p : blockUpper F n β, ∃ k ∈ K,
          (p₀ : GL (Fin n) F) * g = (p : GL (Fin n) F) * x * k := by
        rintro ⟨p, k, hk, he⟩
        refine h ⟨p₀⁻¹ * p, k, hk, ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc g = (p₀ : GL (Fin n) F)⁻¹ * ((p₀ : GL (Fin n) F) * g) := by group
          _ = _ := by rw [he]; group
      rw [bumpFun_eq_zero h', bumpFun_eq_zero h, map_zero, smul_zero]
  · by_cases h : ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k
    · obtain ⟨p, k, hk, rfl⟩ := h
      rw [show (p : GL (Fin n) F) * x * k * k' = (p : GL (Fin n) F) * x * (k * k') by group,
        bumpFun_apply hv _ hk, bumpFun_apply hv _ (K.mul_mem hk hk')]
    · have h' : ¬ ∃ p : blockUpper F n β, ∃ k ∈ K,
          g * k' = (p : GL (Fin n) F) * x * k := by
        rintro ⟨p, k, hk, he⟩
        refine h ⟨p, k * k'⁻¹, K.mul_mem hk (K.inv_mem hk'), ?_⟩
        rw [← mul_assoc, ← he]
        group
      rw [bumpFun_eq_zero h', bumpFun_eq_zero h]
end GroundTheory.Automorphic.Parabolic
