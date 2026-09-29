-- Prove2me | solution 1 for Hairer.modelled_sector_pi_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:16.140987+00:00
-- url     : https://prove2.me/submissions/7fc8c5d8-a923-4938-81b2-327fb4d7a1aa

import Definitions.Def_Hairer_Model

set_option autoImplicit false
open scoped Classical DirectSum
open BigOperators
noncomputable section

open Hairer

theorem solution
    {d : ℕ} {s : Fin d → ℕ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {V : ∀ a : A, Submodule ℝ (E a)} {β γ : ℝ}
    (hV : IsSector G V β) (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (hfV : TakesValuesIn V f) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ β := by
  classical
  have hfinite : {a : A | (a : ℝ) ≤ γ}.Finite := by
    simpa only [Set.preimage_ofPred_eq, Subtype.coe_prop, true_and] using
      (hT.locallyFinite γ).preimage (f := fun a : A ↦ (a : ℝ))
        Subtype.val_injective.injOn
  let J := hfinite.toFinset
  have hsupport (x : Pt d) : (f x).support ⊆ J := by
    intro a ha
    have hne : proj a (f x) ≠ 0 := by
      exact DFinsupp.mem_support_iff.mp ha
    have hlt : (a : ℝ) < γ := lt_of_not_ge fun h ↦ hne (hf.vanishing x a h)
    exact hfinite.mem_toFinset.mpr hlt.le
  intro K hK
  obtain ⟨Cpi, hpi⟩ := hmod.pi_bound γ hγ K hK
  obtain ⟨Cf, hnorm, _⟩ := hf.bound K hK
  refine ⟨(J.card : ℝ) * (max Cpi 0 * max Cf 0), ?_⟩
  intro x hx δ hδ hδone η hη
  let φ := scaledTest s δ x η
  have hφ : φ ∈ testFunctions d := scaledTest_mem s hδ x ⟨hη.smooth, hη.compactSupport⟩
  have hsum : ∑ a ∈ (f x).support, incl a (proj a (f x)) = f x :=
    DirectSum.sum_support_of (f x)
  have heval : (Pi x (f x)).eval φ =
      ∑ a ∈ (f x).support, (Pi x (incl a (proj a (f x)))).eval φ := by
    simp only [Distrib.eval, dif_pos hφ]
    simpa only [map_sum, LinearMap.sum_apply] using
      (congrArg (fun v ↦ (Pi x v) ⟨φ, hφ⟩) hsum).symm
  have hterm (a : A) (ha : a ∈ (f x).support) :
      |(Pi x (incl a (proj a (f x)))).eval φ| ≤
        (max Cpi 0 * max Cf 0) * δ ^ β := by
    have hne : proj a (f x) ≠ 0 := by
      exact DFinsupp.mem_support_iff.mp ha
    have hlt : (a : ℝ) < γ := lt_of_not_ge fun h ↦ hne (hf.vanishing x a h)
    have hβa : β ≤ (a : ℝ) := by
      by_contra! h
      have hv := hfV x a
      rw [hV.vanishing a h] at hv
      exact hne (by simpa using hv)
    calc
      _ ≤ Cpi * ‖proj a (f x)‖ * δ ^ (a : ℝ) :=
        hpi a hlt _ x hx δ hδ hδone η hη
      _ ≤ (max Cpi 0 * max Cf 0) * δ ^ β := by
        have hrpow := Real.rpow_le_rpow_of_exponent_ge hδ hδone hβa
        have hn := (hnorm x hx a hlt).trans (le_max_left Cf 0)
        have hc := le_max_left Cpi 0
        have hc0 := le_max_right Cpi 0
        gcongr
  rw [heval]
  calc
    _ ≤ ∑ a ∈ (f x).support, |(Pi x (incl a (proj a (f x)))).eval φ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ (f x).support, (max Cpi 0 * max Cf 0) * δ ^ β :=
      Finset.sum_le_sum hterm
    _ = ((f x).support.card : ℝ) * ((max Cpi 0 * max Cf 0) * δ ^ β) := by
      simp
    _ ≤ (J.card : ℝ) * ((max Cpi 0 * max Cf 0) * δ ^ β) := by
      gcongr
      exact hsupport x
    _ = _ := by ring


#print axioms solution
