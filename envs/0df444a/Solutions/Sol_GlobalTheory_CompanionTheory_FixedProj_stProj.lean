-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FixedProj.stProj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:31:44.355305+00:00
-- url     : https://prove2.me/submissions/64ff9a47-f5d4-43f8-826e-332b0a946769

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ProjectionStatement
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_inner_left
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open scoped InnerProductSpace
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FixedProj
namespace GlobalTheory.CompanionTheory.FixedProj
theorem _root_.solution : StProj := by
  unfold StProj
  intro G H _ _ _ _ σ hiso K
  let V : Submodule ℂ H :=
    { carrier := {v | ∀ k ∈ K, σ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero _
      smul_mem' := fun c v hv k hk => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [map_smul, hv k hk] }
  have hmem : ∀ v, v ∈ V ↔ ∀ k ∈ K, σ k v = v := fun v => Iff.rfl
  have hVc : IsClosed (V : Set H) := by
    have hV : (V : Set H) = ⋂ k ∈ K, {v | σ k v = v} := by
      ext v
      simp only [Set.mem_iInter]
      exact hmem v
    rw [hV]
    exact isClosed_biInter fun k _ => isClosed_eq (σ k).continuous continuous_id
  haveI : CompleteSpace V := hVc.completeSpace_coe
  have hin : ∀ g v w, inner ℂ (σ g v) w = inner ℂ v (σ g⁻¹ w) := CompanionTheory.D.gk.admitted.FinOfPIAux.inner_left σ hiso
  refine ⟨V.starProjection, ?_, ?_, ?_⟩
  · unfold IsAvg
    refine ⟨?_, ?_, ?_⟩
    · intro v k hk
      exact (hmem _).1 (V.starProjection_apply_mem v) k hk
    · intro v hv
      exact Submodule.starProjection_eq_self_iff.2 ((hmem v).2 hv)
    · intro v k hk
      have horth : σ k v - v ∈ Vᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 : inner ℂ u (σ k v) = inner ℂ u v := by
          have h := hin k⁻¹ u v
          rw [inv_inv, (hmem u).1 hu k⁻¹ (K.inv_mem hk)] at h
          exact h.symm
        rw [inner_sub_right, h1, sub_self]
      have h0 := (Submodule.starProjection_apply_eq_zero_iff V).2 horth
      rw [map_sub, sub_eq_zero] at h0
      exact h0
  · intro u w
    exact Submodule.inner_starProjection_left_eq_right (K := V) u w
  · intro T hT
    have hTσ : ∀ g v, T (σ g v) = σ g (T v) := fun g v =>
      congrArg (fun S : H →L[ℂ] H => S v) (hT g)
    have hTV : ∀ v ∈ V, T v ∈ V := fun v hv k hk => by
      rw [← hTσ, (hmem v).1 hv k hk]
    have hadj : ∀ w ∈ V, ContinuousLinearMap.adjoint T w ∈ V := by
      intro w hw k hk
      apply ext_inner_right ℂ
      intro z
      rw [hin, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hTσ, ← hin,
        (hmem w).1 hw k hk]
    ext v
    have h1 : V.starProjection (T (V.starProjection v)) = T (V.starProjection v) :=
      Submodule.starProjection_eq_self_iff.2 (hTV _ (V.starProjection_apply_mem v))
    have hu : v - V.starProjection v ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal (K := V) v
    have h2 : V.starProjection (T (v - V.starProjection v)) = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff V).2
      rw [Submodule.mem_orthogonal] at hu ⊢
      intro w hw
      rw [← ContinuousLinearMap.adjoint_inner_left]
      exact hu _ (hadj w hw)
    have hv : v = V.starProjection v + (v - V.starProjection v) := by abel
    show T (V.starProjection v) = V.starProjection (T v)
    conv_rhs => rw [hv]
    simp only [map_add]
    rw [h1, h2, add_zero]
end GlobalTheory.CompanionTheory.FixedProj
