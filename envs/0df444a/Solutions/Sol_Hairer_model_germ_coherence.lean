-- Prove2me | solution 1 for Hairer.model_germ_coherence
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:03:37.604893+00:00
-- url     : https://prove2.me/submissions/5e365801-d7c5-42b4-97a1-5ad5e4bbe7ae

import Definitions.Def_Hairer_Model

set_option autoImplicit false
open BigOperators

noncomputable section

namespace Hairer

/-- The scaled distance is nonnegative, including in dimension zero. -/
theorem snorm_nonneg {d : ℕ} (s : Fin d → ℕ) (x : Pt d) : 0 ≤ snorm s x := by
  cases isEmpty_or_nonempty (Fin d) with
  | inl h =>
    let _ := h
    simp [snorm]
  | inr h =>
    let _ := h
    let i : Fin d := Classical.choice h
    unfold snorm
    exact (Real.rpow_nonneg (abs_nonneg (x i)) ((1 : ℝ) / (s i : ℝ))).trans
      (le_ciSup (Set.finite_range (fun j : Fin d ↦
        |x j| ^ ((1 : ℝ) / (s j : ℝ)))).bddAbove i)

/-- A triangular reexpansion preserves truncation below a fixed homogeneity. -/
theorem IsRegularityStructure.map_vanishing
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {Γ : ModelSpace A E ≃ₗ[ℝ] ModelSpace A E} (hΓ : Γ ∈ G)
    {γ : ℝ} {v : ModelSpace A E}
    (hv : ∀ a : A, γ ≤ (a : ℝ) → proj a v = 0) :
    ∀ b : A, γ ≤ (b : ℝ) → proj b (Γ v) = 0 := by
  classical
  intro b hb
  have hsum : ∑ a ∈ v.support, incl a (proj a v) = v := DirectSum.sum_support_of v
  have heq := congrArg (fun w ↦ proj b (Γ w)) hsum
  rw [← heq]
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have hne : proj a v ≠ 0 := DFinsupp.mem_support_iff.mp ha
  have haγ : (a : ℝ) < γ := lt_of_not_ge fun h ↦ hne (hv a h)
  have hab : (a : ℝ) < (b : ℝ) := haγ.trans_le hb
  have hneq : a ≠ b := fun h ↦ (ne_of_lt hab) (congrArg Subtype.val h)
  have ht := hT.triangular Γ hΓ a b (proj a v) hab.le
  simpa [map_sub, proj, incl, DirectSum.component.of, hneq] using ht

end Hairer

open Hairer

theorem solution
    {d : ℕ} {s : Fin d → ℕ} {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ,
      ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → snorm s (x - y) ≤ δ →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(Pi x (f x) - Pi y (f y)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  classical
  have hfinite : {a : A | (a : ℝ) ≤ γ}.Finite := by
    simpa only [Set.preimage_ofPred_eq, Subtype.coe_prop, true_and] using
      (hT.locallyFinite γ).preimage (f := fun a : A ↦ (a : ℝ))
        Subtype.val_injective.injOn
  let J := hfinite.toFinset
  intro K hK
  obtain ⟨Cp, hp⟩ := hmod.pi_bound (max γ 1) (lt_of_lt_of_le zero_lt_one (le_max_right γ 1)) K hK
  obtain ⟨Cf, _, hfbound⟩ := hf.bound K hK
  refine ⟨(J.card : ℝ) * (max Cp 0 * max Cf 0), ?_⟩
  intro x hx y hy δ hδ hδone hxy η hη
  let v := f x - Gam x y (f y)
  have hvan (a : A) (ha : γ ≤ (a : ℝ)) : proj a v = 0 := by
    change proj a (f x - Gam x y (f y)) = 0
    rw [map_sub, hf.vanishing x a ha,
      hT.map_vanishing (hmod.gam_mem x y) (hf.vanishing y) a ha, sub_self]
  have hlt (a : A) (ha : a ∈ v.support) : (a : ℝ) < γ := by
    have hne : proj a v ≠ 0 := DFinsupp.mem_support_iff.mp ha
    exact lt_of_not_ge fun h ↦ hne (hvan a h)
  have hsupport : v.support ⊆ J := by
    intro a ha
    exact hfinite.mem_toFinset.mpr (hlt a ha).le
  let φ := scaledTest s δ x η
  have hφ : φ ∈ testFunctions d := scaledTest_mem s hδ x ⟨hη.smooth, hη.compactSupport⟩
  have hsum : ∑ a ∈ v.support, incl a (proj a v) = v := DirectSum.sum_support_of v
  have heval : (Pi x (f x) - Pi y (f y)).eval φ =
      ∑ a ∈ v.support, (Pi x (incl a (proj a v))).eval φ := by
    rw [hmod.pi_comp x y (f y), ← map_sub]
    simp only [Distrib.eval, dif_pos hφ]
    simpa only [map_sum, LinearMap.sum_apply] using
      (congrArg (fun w ↦ (Pi x w) ⟨φ, hφ⟩) hsum).symm
  have hterm (a : A) (ha : a ∈ v.support) :
      |(Pi x (incl a (proj a v))).eval φ| ≤ (max Cp 0 * max Cf 0) * δ ^ γ := by
    have haγ := hlt a ha
    have hn : ‖proj a v‖ ≤ max Cf 0 * δ ^ (γ - (a : ℝ)) := by
      calc
        _ ≤ Cf * snorm s (x - y) ^ (γ - (a : ℝ)) :=
          hfbound x hx y hy (hxy.trans hδone) a haγ
        _ ≤ max Cf 0 * δ ^ (γ - (a : ℝ)) := by
          have hrpow := Real.rpow_le_rpow (snorm_nonneg s (x - y)) hxy (sub_nonneg.mpr haγ.le)
          have hc := le_max_left Cf 0
          have hc0 := le_max_right Cf 0
          have hpow0 := Real.rpow_nonneg (snorm_nonneg s (x - y)) (γ - (a : ℝ))
          gcongr
    calc
      _ ≤ Cp * ‖proj a v‖ * δ ^ (a : ℝ) :=
        hp a (haγ.trans_le (le_max_left γ 1)) _ x hx δ hδ hδone η hη
      _ ≤ max Cp 0 * (max Cf 0 * δ ^ (γ - (a : ℝ))) * δ ^ (a : ℝ) := by
        have hc := le_max_left Cp 0
        have hc0 := le_max_right Cp 0
        gcongr
      _ = (max Cp 0 * max Cf 0) * δ ^ γ := by
        simp only [mul_assoc, ← Real.rpow_add hδ, sub_add_cancel]
  rw [heval]
  calc
    _ ≤ ∑ a ∈ v.support, |(Pi x (incl a (proj a v))).eval φ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ v.support, (max Cp 0 * max Cf 0) * δ ^ γ := Finset.sum_le_sum hterm
    _ = (v.support.card : ℝ) * ((max Cp 0 * max Cf 0) * δ ^ γ) := by simp
    _ ≤ (J.card : ℝ) * ((max Cp 0 * max Cf 0) * δ ^ γ) := by
      gcongr
    _ = _ := by ring


#print axioms solution
