-- Prove2me | solution 1 for GlobalTheory.PlaceModel.exists_map_wave
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:00.19979+00:00
-- url     : https://prove2.me/submissions/07f78a10-bae1-4362-ba8d-9cfb13b0a770

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_neg_mul
import Theorems.Thm_GlobalTheory_PlaceModel_wave_add
import Theorems.Thm_GlobalTheory_PlaceModel_linearIndependent_wave

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}
namespace GlobalTheory.PlaceModel
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (h : IsBichar χ) (hL : L ≤ X) (hL' : L' ≤ Y)
    (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hY : ∀ y ∈ Y, (∀ u ∈ L, χ u y = 1) → y ∈ L')
    (ρ : G → V →ₗ[ℂ] V) (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ f, ρ x (ρ x' f) = ρ (x + x') f)
    (ρY : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ f, ρ y (ρ y' f) = ρ (y + y') f)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Y, ∀ f, ρ x (ρ y f) = χ x y • ρ y (ρ x f))
    (f₀ : V) (hf : ∀ u ∈ L, ρ u f₀ = f₀) (hf' : ∀ u ∈ L', ρ u f₀ = f₀) :
    ∃ T : (G → ℂ) →ₗ[ℂ] V, ∀ x ∈ X, ∀ y ∈ Y, T (wave χ L x y) = ρ x (ρ y f₀) := by
  classical
  have hli := linearIndependent_wave (χ := χ) (X := X) (L := L) (L' := L') h hY
  let B := Module.Basis.span hli
  let T₀ := B.constr ℂ (fun i : (X ⧸ L.addSubgroupOf X) × (Y ⧸ L'.addSubgroupOf Y) =>
    ρ ((i.1.out : X) : G) (ρ ((i.2.out : Y) : G) f₀))
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₀

  have hTv : ∀ i : (X ⧸ L.addSubgroupOf X) × (Y ⧸ L'.addSubgroupOf Y),
      T (wave χ L ((i.1.out : X) : G) ((i.2.out : Y) : G)) =
        ρ ((i.1.out : X) : G) (ρ ((i.2.out : Y) : G) f₀) := by
    intro i
    have e1 : ((B i : Submodule.span ℂ _) : G → ℂ) =
        wave χ L ((i.1.out : X) : G) ((i.2.out : Y) : G) := by
      simp [B]
    have e2 := LinearMap.congr_fun hT (B i)
    rw [LinearMap.comp_apply, Submodule.subtype_apply, e1] at e2
    rw [e2]
    exact Module.Basis.constr_basis B ℂ _ i
  refine ⟨T, fun x hx y hy => ?_⟩
  obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add (L.addSubgroupOf X) (⟨x, hx⟩ : X)
  obtain ⟨l', hl'⟩ := QuotientAddGroup.mk_out_eq_add (L'.addSubgroupOf Y) (⟨y, hy⟩ : Y)
  have hlL : ((l : X) : G) ∈ L := l.2
  have hlL' : ((l' : Y) : G) ∈ L' := l'.2
  have e := hTv (((⟨x, hx⟩ : X) : X ⧸ L.addSubgroupOf X), ((⟨y, hy⟩ : Y) : Y ⧸ L'.addSubgroupOf Y))
  dsimp only at e
  rw [hl, hl'] at e
  change T (wave χ L (x + ((l : X) : G)) (y + ((l' : Y) : G))) =
    ρ (x + ((l : X) : G)) (ρ (y + ((l' : Y) : G)) f₀) at e

  have hρ : ρ (x + ((l : X) : G)) (ρ (y + ((l' : Y) : G)) f₀) = χ ((l : X) : G) y • ρ x (ρ y f₀) := by
    have hlX : ((l : X) : G) ∈ X := hL hlL
    have hlY : ((l' : Y) : G) ∈ Y := hL' hlL'
    rw [← ρY y hy _ hlY, hf' _ hlL', ← ρX x hx _ hlX, ρXY _ hlX y hy, hf _ hlL, map_smul]
  rw [wave_add h hLL' x y hlL hlL', map_smul, hρ] at e
  have hne : χ ((l : X) : G) y ≠ 0 := by
    intro h0
    have h1 := h.neg_mul ((l : X) : G) y
    rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  exact smul_right_injective V hne e
end GlobalTheory.PlaceModel
