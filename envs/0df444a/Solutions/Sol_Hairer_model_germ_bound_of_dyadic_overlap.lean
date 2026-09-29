-- Prove2me | solution 1 for Hairer.model_germ_bound_of_dyadic_overlap
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T20:14:04.910114+00:00
-- url     : https://prove2.me/submissions/c59c40a5-e14e-4afa-b520-10a3aadebd9a

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

/-- Model germs tested at scale `δ` agree to order `γ` when their base points
are at distance at most a fixed multiple of `δ`. The separate unit-distance
hypothesis is precisely the range of the modelled increment bound. -/
theorem model_germ_coherence_multiple
    {d : ℕ} {s : Fin d → ℕ} {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (L : ℝ) (hL : 0 ≤ L) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        snorm s (x - y) ≤ 1 → snorm s (x - y) ≤ L * δ →
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
  let B : ℝ := max Cp 0 * max Cf 0
  have hB : 0 ≤ B := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨B * ∑ a ∈ J, L ^ (γ - (a : ℝ)),
    mul_nonneg hB (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg hL _), ?_⟩
  intro x hx y hy δ hδ hδone hxyone hxy η hη
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
      |(Pi x (incl a (proj a v))).eval φ| ≤ B * L ^ (γ - (a : ℝ)) * δ ^ γ := by
    have haγ := hlt a ha
    have hn : ‖proj a v‖ ≤ max Cf 0 * (L * δ) ^ (γ - (a : ℝ)) := by
      calc
        _ ≤ Cf * snorm s (x - y) ^ (γ - (a : ℝ)) :=
          hfbound x hx y hy hxyone a haγ
        _ ≤ max Cf 0 * (L * δ) ^ (γ - (a : ℝ)) :=
          mul_le_mul (le_max_left Cf 0)
            (Real.rpow_le_rpow (snorm_nonneg s (x - y)) hxy (sub_nonneg.mpr haγ.le))
            (Real.rpow_nonneg (snorm_nonneg s (x - y)) _) (le_max_right Cf 0)
    calc
      _ ≤ Cp * ‖proj a v‖ * δ ^ (a : ℝ) :=
        hp a (haγ.trans_le (le_max_left γ 1)) _ x hx δ hδ hδone η hη
      _ ≤ max Cp 0 * (max Cf 0 * (L * δ) ^ (γ - (a : ℝ))) * δ ^ (a : ℝ) := by
        have hc := le_max_left Cp 0
        have hc0 := le_max_right Cp 0
        gcongr
      _ = B * L ^ (γ - (a : ℝ)) * δ ^ γ := by
        rw [Real.mul_rpow hL hδ.le]
        simp only [B, mul_assoc, ← Real.rpow_add hδ, sub_add_cancel]
  rw [heval]
  calc
    _ ≤ ∑ a ∈ v.support, |(Pi x (incl a (proj a v))).eval φ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ v.support, B * L ^ (γ - (a : ℝ)) * δ ^ γ := Finset.sum_le_sum hterm
    _ ≤ ∑ a ∈ J, B * L ^ (γ - (a : ℝ)) * δ ^ γ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsupport
        (fun a _ _ ↦ mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hL _))
          (Real.rpow_nonneg hδ.le _))
    _ = (B * ∑ a ∈ J, L ^ (γ - (a : ℝ))) * δ ^ γ := by
      rw [Finset.mul_sum, Finset.sum_mul]

end Hairer


set_option autoImplicit false
noncomputable section
namespace Hairer

/-- Coordinate control implies control of the anisotropic quasi-norm. -/
theorem snorm_le_of_coord_pow_le {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {R : ℝ} (hR : 0 ≤ R) {x : Pt d} (hx : ∀ i, |x i| ≤ R ^ s i) :
    snorm s x ≤ R := by
  apply Real.iSup_le _ hR
  intro i
  calc
    |x i| ^ ((1 : ℝ) / (s i : ℝ)) ≤ (R ^ s i) ^ ((1 : ℝ) / (s i : ℝ)) :=
      Real.rpow_le_rpow (abs_nonneg _) (hx i) (by positivity)
    _ = R := by
      rw [one_div, Real.pow_rpow_inv_natCast hR (by have := hs i; omega)]

/-- Overlapping coordinate boxes at scales `δ ≤ ρ` have centres at scaled
distance at most `2ρ`. -/
theorem snorm_sub_le_of_box_overlap {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {δ ρ : ℝ} (hδ : 0 ≤ δ) (hδρ : δ ≤ ρ) {x z w : Pt d}
    (hx : ∀ i, |w i - x i| ≤ δ ^ s i)
    (hz : ∀ i, |w i - z i| ≤ ρ ^ s i) :
    snorm s (x - z) ≤ 2 * ρ := by
  have hρ : 0 ≤ ρ := hδ.trans hδρ
  apply snorm_le_of_coord_pow_le hs (mul_nonneg (by norm_num) hρ)
  intro i
  have hsum : |x i - z i| ≤ |w i - x i| + |w i - z i| := by
    have h := abs_add_le (x i - w i) (w i - z i)
    rw [sub_add_sub_cancel, abs_sub_comm (x i) (w i)] at h
    exact h
  change |x i - z i| ≤ (2 * ρ) ^ s i
  calc
    _ ≤ δ ^ s i + ρ ^ s i := hsum.trans (add_le_add (hx i) (hz i))
    _ ≤ ρ ^ s i + ρ ^ s i := add_le_add (pow_le_pow_left₀ hδ hδρ _) le_rfl
    _ = 2 * ρ ^ s i := by ring
    _ ≤ 2 ^ s i * ρ ^ s i := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ _)
      have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (hs i)
      simpa using h
    _ = (2 * ρ) ^ s i := (mul_pow _ _ _).symm

end Hairer

open Hairer

/-- The fine-scale germ estimate for two overlapping boxes at adjacent dyadic
scales. This applies directly to the support geometry of grid-weight products. -/
theorem solution
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ z ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
        (∃ w : Pt d, (∀ i, |w i - x i| ≤ δ ^ s i) ∧
          (∀ i, |w i - z i| ≤ (2 * δ) ^ s i)) →
        ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(Pi x (f x) - Pi z (f z)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ := by
  intro K hK
  obtain ⟨C, hC, hbound⟩ := model_germ_coherence_multiple hT hmod hf 4 (by norm_num) K hK
  refine ⟨C, hC, ?_⟩
  rintro x hx z hz δ hδ hδsmall ⟨w, hwx, hwz⟩ η hη
  have hdist : snorm s (x - z) ≤ 4 * δ := by
    have h := snorm_sub_le_of_box_overlap hs hδ.le
      (show δ ≤ 2 * δ by linarith) hwx hwz
    linarith
  exact hbound x hx z hz δ hδ (by linarith) (hdist.trans (by linarith)) hdist η hη


#print axioms solution
