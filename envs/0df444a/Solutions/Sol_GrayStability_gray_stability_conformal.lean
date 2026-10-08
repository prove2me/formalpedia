-- Prove2me | solution 1 for GrayStability.gray_stability_conformal
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T15:40:27.223414+00:00
-- url     : https://prove2.me/submissions/2c5bd302-e480-4051-b618-6796e1084ad1

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_GrayStability_smooth_moser_lie_generator
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_ParameterizedCalculus_smooth_scalar_linear_transport
import Theorems.Thm_GrayStability_pullback_family_hasDerivAt
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped ContDiff
open GrayStability

theorem solution {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : ℝ → OneForm n) (hα : IsContactFamilyOn F α) :
    ∃ ψ : ℝ → E n → E n, IsIsotopyOf F ψ ∧
      ∃ lam : ℝ → E n → ℝ, ContDiff ℝ ∞ (fun p : ℝ × E n => lam p.1 p.2) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, 0 < lam t y) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
          pullback (ψ t) (α t) y v = lam t y * α 0 y v := by
  obtain ⟨X, μ, hX, hμ, hsupp, hplane, heq⟩ := smooth_moser_lie_generator F hF α hα
  have htan : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F,
      X t y ∈ tangentSpace F y := by
    intro t ht y hy
    exact (hplane t ht y hy).1
  obtain ⟨ψ, hψ, h0, hbij, hflow, hiso, hDψ⟩ :=
    FlowCalculus.compact_supported_flow_preserves_regular_level F hF X hX hsupp htan
  let q : ℝ → E n → ℝ := fun t y => μ t (ψ t y)
  have hq : ContDiff ℝ ∞ (fun p : ℝ × E n => q p.1 p.2) :=
    hμ.comp (contDiff_fst.prodMk hψ)
  obtain ⟨lam, hlam, _, hpos, htransport⟩ :=
    ParameterizedCalculus.smooth_scalar_linear_transport q hq
  refine ⟨ψ, hiso, lam, hlam, ?_, ?_⟩
  · intro t ht y hy
    exact hpos t y
  · intro t ht y hy v hv
    have hf : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt (fun r => pullback (ψ r) (α r) y v)
          (q s y * pullback (ψ s) (α s) y v) s := by
      intro s hs
      have hmap : ψ s y ∈ levelSet F := (hiso.2.2 s hs).1.mapsTo hy
      have hw := hDψ s hs y hy v hv
      have hd := pullback_family_hasDerivAt α hα.1 X hX ψ hψ h0 hbij hflow s y v
      rw [heq s hs (ψ s y) hmap (fderiv ℝ (ψ s) y v) hw] at hd
      exact hd
    have hinit : pullback (ψ 0) (α 0) y v = α 0 y v := by
      have hid : ψ 0 = id := funext h0
      simp [pullback, hid]
    simpa only [hinit] using htransport y (fun s => pullback (ψ s) (α s) y v) hf t ht
