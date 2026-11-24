-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSUniq.equiv_of_graph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:24.945847+00:00
-- url     : https://prove2.me/submissions/ca3b0982-89e3-494e-9004-449567097a44

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Closure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_SopNegComm
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsDerivedOnOfIsKMod
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_cyc_stab
import Theorems.Thm_CompanionTheory_D_LK_mem_cyc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset WithLp
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSUniq
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight Cas)
open PI.UpqRep (lowK IsURepOn IsIrredOn UJset IsDS)
open CompanionTheory.D.DSIC (KUnit KStab)
open CompanionTheory.D.LK (Cyc LocFin IsMin IsKMod MultAlg KModExists OrthCyc mem_cyc cyc_stab ev)
open ReciprocityTheory.ChartRestriction.DS (genSub IsDerivedOn)
open ReciprocityTheory.ChartRestriction.DS.USum (sD sE sσ ofP toP lift)
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSUniq
theorem _root_.solution {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {G : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hI : IsIrredOn G σ) (hI' : IsIrredOn G σ')
    (Y : Submodule ℂ (WithLp 2 (H × H'))) (hc : IsClosed (Y : Set (WithLp 2 (H × H'))))
    (hst : ∀ g ∈ G, ∀ y ∈ Y, sσ σ σ' g y ∈ Y) (hn : ∀ y ∈ Y, ‖(ofLp y).1‖ = ‖(ofLp y).2‖)
    {y₀ : WithLp 2 (H × H')} (hy₀ : y₀ ∈ Y) (h0 : y₀ ≠ 0) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ G, ∀ x, U (σ g x) = σ' g (U x) := by
  have : CompleteSpace Y := hc.completeSpace_coe
  have hs : ‖((√2 : ℝ) : ℂ)‖ = √2 := by simp
  have hnorm : ∀ y : Y, √2 * ‖(ofLp (y : WithLp 2 (H × H'))).1‖ = ‖y‖ := fun y => by
    show _ = ‖(y : WithLp 2 (H × H'))‖
    rw [WithLp.prod_norm_eq_of_L2]
    show _ = √(‖(ofLp (y : WithLp 2 (H × H'))).1‖ ^ 2 + ‖(ofLp (y : WithLp 2 (H × H'))).2‖ ^ 2)
    rw [← hn y y.2, ← two_mul, Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
  let f₁ : Y →ₗᵢ[ℂ] H :=
    { toFun := fun y => ((√2 : ℝ) : ℂ) • (ofLp (y : WithLp 2 (H × H'))).1
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp [smul_comm c]
      norm_map' := fun y => by
        show ‖((√2 : ℝ) : ℂ) • (ofLp (y : WithLp 2 (H × H'))).1‖ = _
        rw [norm_smul, hs, hnorm] }
  let f₂ : Y →ₗᵢ[ℂ] H' :=
    { toFun := fun y => ((√2 : ℝ) : ℂ) • (ofLp (y : WithLp 2 (H × H'))).2
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp [smul_comm c]
      norm_map' := fun y => by
        show ‖((√2 : ℝ) : ℂ) • (ofLp (y : WithLp 2 (H × H'))).2‖ = _
        rw [norm_smul, hs, ← hn y y.2, hnorm] }
  have e₁ : ∀ g (hg : g ∈ G) (y : Y), f₁ ⟨_, hst g hg y y.2⟩ = σ g (f₁ y) := fun g hg y =>
    ((σ g).map_smul _ _).symm
  have e₂ : ∀ g (hg : g ∈ G) (y : Y), f₂ ⟨_, hst g hg y y.2⟩ = σ' g (f₂ y) := fun g hg y =>
    ((σ' g).map_smul _ _).symm
  have hy : (⟨y₀, hy₀⟩ : Y) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have s₁ : Function.Surjective f₁ := by
    refine LinearMap.range_eq_top.1 ((hI (LinearMap.range f₁.toLinearMap) f₁.isometry.isClosedEmbedding.isClosed_range
      ?_).resolve_left fun h => hy ?_)
    · rintro g hg _ ⟨y, rfl⟩
      exact ⟨_, e₁ g hg y⟩
    · have : f₁ ⟨y₀, hy₀⟩ ∈ LinearMap.range f₁.toLinearMap := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact f₁.injective (by rw [this, map_zero])
  have s₂ : Function.Surjective f₂ := by
    refine LinearMap.range_eq_top.1 ((hI' (LinearMap.range f₂.toLinearMap) f₂.isometry.isClosedEmbedding.isClosed_range
      ?_).resolve_left fun h => hy ?_)
    · rintro g hg _ ⟨y, rfl⟩
      exact ⟨_, e₂ g hg y⟩
    · have : f₂ ⟨y₀, hy₀⟩ ∈ LinearMap.range f₂.toLinearMap := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact f₂.injective (by rw [this, map_zero])
  let u₁ := LinearIsometryEquiv.ofSurjective f₁ s₁
  let u₂ := LinearIsometryEquiv.ofSurjective f₂ s₂
  have key : ∀ y : Y, (u₁.symm.trans u₂) (f₁ y) = f₂ y := fun y => by
    have : u₁.symm (f₁ y) = y := u₁.symm_apply_apply y
    rw [LinearIsometryEquiv.trans_apply, this]
    rfl
  refine ⟨u₁.symm.trans u₂, fun g hg x => ?_⟩
  obtain ⟨y, rfl⟩ := s₁ x
  rw [← e₁ g hg, key, key, e₂ g hg]
end GlobalTheory.CompanionTheory.DSUniq
