-- Prove2me | solution 1 for GrayStability.gray_stability_fixing_stationary_points
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T09:49:26.686257+00:00
-- url     : https://prove2.me/submissions/13e67f74-18b9-4577-b6a1-1f1eefa22510

import Definitions.Def_GrayStability_Basic
import Theorems.Thm_GrayStability_smooth_moser_lie_generator
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_ParameterizedCalculus_smooth_scalar_linear_transport
import Theorems.Thm_GrayStability_pullback_family_hasDerivAt
import Mathlib.Analysis.Calculus.ContDiff.Operations

import Theorems.Thm_ContactCalculus_lie_derivative_eq_exterior_on_regular_level
import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open scoped ContDiff
open GrayStability

theorem solution {n c : ℕ} (F : E n → (Fin c → ℝ))
    (hF : IsCompactRegularLevel F) (α : ℝ → OneForm n) (hα : IsContactFamilyOn F α) :
    ∃ ψ : ℝ → E n → E n, IsIsotopyOf F ψ ∧
      (∃ lam : ℝ → E n → ℝ, ContDiff ℝ ∞ (fun p : ℝ × E n => lam p.1 p.2) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, 0 < lam t y) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
          pullback (ψ t) (α t) y v = lam t y * α 0 y v) ∧
      ∀ p ∈ levelSet F,
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ tangentSpace F p, formTimeDeriv α t p v = 0) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t p = p := by
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
  have hconf : ∃ lam : ℝ → E n → ℝ, ContDiff ℝ ∞ (fun p : ℝ × E n => lam p.1 p.2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, 0 < lam t y) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ levelSet F, ∀ v ∈ tangentSpace F y,
        pullback (ψ t) (α t) y v = lam t y * α 0 y v := by
    refine ⟨lam, hlam, ?_, ?_⟩
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
  
  refine ⟨ψ, hiso, hconf, ?_⟩
  intro p hp hstationary
  have hzero : ∀ s ∈ Set.Icc (0 : ℝ) 1, X s p = 0 := by
    intro s hs
    by_contra hne
    obtain ⟨v, hv, hnv⟩ := (hα.2 s hs p hp).2 (X s p) (hplane s hs p hp) hne
    have hη : Differentiable ℝ (α s) :=
      (hα.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    have hXs : Differentiable ℝ (X s) :=
      (hX.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    have hlie := ContactCalculus.lie_derivative_eq_exterior_on_regular_level
      F hF.1 (α s) (X s) hη hXs (fun z hz => (hplane s hs z hz).2)
      p hp (hF.2.2 p hp) v hv.1
    have hh := heq s hs p hp v hv.1
    rw [hstationary s hs v hv.1, hlie, hv.2] at hh
    exact hnv (by linarith)
  obtain ⟨L, hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support
    X hX hsupp 0 1
  have hequal := ODE_solution_unique_of_mem_Icc_right
    (v := X) (s := fun _ => Set.univ) (K := L)
    (f := fun s => ψ s p) (g := fun _ => p) (a := 0) (b := 1)
    (fun s hs => (hL s ⟨hs.1, le_of_lt hs.2⟩).lipschitzOnWith)
    ((hψ.comp (contDiff_id.prodMk contDiff_const)).continuous.continuousOn)
    (fun s _ => (hflow s p).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _)
    continuousOn_const
    (fun s hs => by
      rw [hzero s ⟨hs.1, le_of_lt hs.2⟩]
      exact (hasDerivAt_const s p).hasDerivWithinAt)
    (fun _ _ => Set.mem_univ _) (h0 p)
  exact fun t ht => hequal ht
