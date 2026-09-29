-- Prove2me | solution 1 for Hairer.reconstruction_sector_regularity_brversion
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-27T04:51:27.876384+00:00
-- url     : https://prove2.me/submissions/af1ad671-abd5-48aa-8268-3ff36dc79f16

import Definitions.Def_Hairer_Model

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

open Hairer

/-- **Corollary 3.16, Hairer 2014 (B^r-version).**

Sector regularity of the reconstruction with the `C^β_s` bound stated at the
model's test order `r`. Proof: split `ξ = (ξ - Π_x f(x)) + Π_x f(x)`; the first
piece is `O(δ^γ) ≤ O(δ^β)` by the reconstruction hypothesis. Expand `Π_x f(x)`
over the fixed finite set of homogeneities `< γ` (local finiteness of `A`);
components `≥ γ` vanish by `IsModelled.vanishing`, components `< β` vanish by
the sector vanishing together with `TakesValuesIn`; the band `β ≤ a < γ` is
bounded by the model `Π`-bound plus the modelled-distribution bound, and
`δ^a ≤ δ^β` there. -/
theorem solution
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α)
    {V : ∀ a : A, Submodule ℝ (E a)} {β : ℝ} (hV : IsSector G V β)
    (hβ : α ≤ β) (hβneg : β < 0)
    {γ : ℝ} (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) (hfV : TakesValuesIn V f)
    (ξ : Distrib d)
    (hξ : ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ η : Pt d → ℝ, IsTestBall s r η →
        |ξ.eval (scaledTest s δ x η)| ≤ C * δ ^ β := by
  -- `Distrib.eval` distributes over addition and finite sums of distributions.
  have heval0 : ∀ φ : Pt d → ℝ, (0 : Distrib d).eval φ = 0 := by
    intro φ
    by_cases h : φ ∈ testFunctions d
    · simp only [Distrib.eval, dif_pos h]
      exact LinearMap.zero_apply (⟨φ, h⟩ : testFunctions d)
    · simp only [Distrib.eval, dif_neg h]
  have heval_add : ∀ (u v : Distrib d) (φ : Pt d → ℝ),
      (u + v).eval φ = u.eval φ + v.eval φ := by
    intro u v φ
    by_cases h : φ ∈ testFunctions d
    · simp only [Distrib.eval, dif_pos h]
      exact LinearMap.add_apply u v (⟨φ, h⟩ : testFunctions d)
    · simp only [Distrib.eval, dif_neg h, add_zero]
  have heval_sum : ∀ (S : Finset A) (τ : A → Distrib d) (φ : Pt d → ℝ),
      (∑ a ∈ S, τ a).eval φ = ∑ a ∈ S, (τ a).eval φ := by
    intro S τ φ
    induction S using Finset.induction with
    | empty => simp only [Finset.sum_empty, heval0]
    | insert a S haS ih =>
      rw [Finset.sum_insert haS, Finset.sum_insert haS, heval_add, ih]
  -- The fixed finite set of homogeneities below `γ` (local finiteness of `A`).
  have hfin : {a : A | (a : ℝ) < γ}.Finite := by
    have hsub : (Subtype.val : A → ℝ) '' {a : A | (a : ℝ) < γ}
        ⊆ {a : ℝ | a ∈ A ∧ a ≤ γ} := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a.2, ha.le⟩
    have hinj : Set.InjOn (Subtype.val : A → ℝ) {a : A | (a : ℝ) < γ} :=
      fun _ _ _ _ h => Subtype.val_injective h
    exact Set.Finite.of_finite_image (Set.Finite.subset (hT.locallyFinite γ) hsub) hinj
  -- Every `f x` is supported inside this fixed set (components `≥ γ` vanish).
  have hsuppF : ∀ x : Pt d, (f x).support ⊆ hfin.toFinset := by
    intro x a ha
    have haγ : (a : ℝ) < γ := by
      by_contra hcon
      have hle : γ ≤ (a : ℝ) := not_lt.mp hcon
      have h0 : proj a (f x) = 0 := hf.vanishing x a hle
      have hne : proj a (f x) ≠ 0 := DFinsupp.mem_support_iff.mp ha
      exact hne h0
    exact (Set.Finite.mem_toFinset hfin).mpr haγ
  have hdecomp : ∀ x : Pt d, f x = ∑ a ∈ (f x).support, incl a (proj a (f x)) := by
    intro x
    have h := DirectSum.sum_support_of (f x)
    refine h.symm.trans ?_
    apply Finset.sum_congr rfl
    intro a _
    show DirectSum.of E a ((f x) a)
      = DirectSum.lof ℝ A E a (DirectSum.component ℝ A E a (f x))
    rw [DirectSum.lof_eq_of]
    congr 1
  -- Constants from the three hypotheses.
  intro K hK
  obtain ⟨C₁, hC₁⟩ := hξ K hK
  obtain ⟨C₂, hC₂⟩ := hmod.pi_bound γ hγ K hK
  obtain ⟨C₃, hC₃⟩ := hf.bound K hK
  refine ⟨|C₁| + (hfin.toFinset.card : ℝ) * (|C₂| * C₃),
    fun x hx δ hδ0 hδ1 η hη => ?_⟩
  have hC3nn : 0 ≤ C₃ := le_trans (norm_nonneg _) (hC₃.1 x hx ⟨0, hT.zero_mem⟩ hγ)
  have h1 : |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C₁ * δ ^ γ :=
    hC₁ x hx δ hδ0 hδ1 η hη
  have hPi : Pi x (f x) = ∑ a ∈ (f x).support, Pi x (incl a (proj a (f x))) := by
    conv_lhs => rw [hdecomp x]
    rw [map_sum]
  -- Per-component bound `|C₂| * C₃ * δ^β`, uniform over the fixed set.
  have hterm : ∀ a ∈ hfin.toFinset,
      |(Pi x (incl a (proj a (f x)))).eval (scaledTest s δ x η)|
        ≤ |C₂| * C₃ * δ ^ β := by
    intro a haF
    have haγ : (a : ℝ) < γ := (Set.Finite.mem_toFinset hfin).mp haF
    by_cases hab : (a : ℝ) < β
    · -- Sector vanishing kills components below `β`.
      have h0 : proj a (f x) = 0 := by
        have hva : V a = ⊥ := hV.vanishing a hab
        have hmem : proj a (f x) ∈ V a := hfV x a
        rw [hva] at hmem
        exact (Submodule.mem_bot ℝ).mp hmem
      simp only [h0, map_zero, heval0, abs_zero]
      exact mul_nonneg (mul_nonneg (abs_nonneg _) hC3nn) (Real.rpow_nonneg hδ0.le _)
    · -- Band `β ≤ a < γ`: model Π-bound + modelled-distribution bound.
      have hab2 : β ≤ (a : ℝ) := not_lt.mp hab
      have hpb := hC₂ a haγ (proj a (f x)) x hx δ hδ0 hδ1 η hη
      have hnorm : ‖proj a (f x)‖ ≤ C₃ := hC₃.1 x hx a haγ
      have hδa : δ ^ (a : ℝ) ≤ δ ^ β :=
        Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hab2
      have hpos : (0 : ℝ) ≤ δ ^ (a : ℝ) := Real.rpow_nonneg hδ0.le _
      have e1 : C₂ * ‖proj a (f x)‖ * δ ^ (a : ℝ)
          ≤ |C₂| * ‖proj a (f x)‖ * δ ^ (a : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C₂) (norm_nonneg _)) hpos
      have e2 : |C₂| * ‖proj a (f x)‖ * δ ^ (a : ℝ) ≤ |C₂| * C₃ * δ ^ (a : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)) hpos
      have e3 : |C₂| * C₃ * δ ^ (a : ℝ) ≤ |C₂| * C₃ * δ ^ β :=
        mul_le_mul_of_nonneg_left hδa (mul_nonneg (abs_nonneg _) hC3nn)
      exact le_trans hpb (le_trans e1 (le_trans e2 e3))
  have h2 : |(Pi x (f x)).eval (scaledTest s δ x η)|
      ≤ (hfin.toFinset.card : ℝ) * (|C₂| * C₃) * δ ^ β := by
    rw [hPi, heval_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg (hsuppF x) (fun a _ _ => abs_nonneg _)) ?_
    calc ∑ a ∈ hfin.toFinset, |(Pi x (incl a (proj a (f x)))).eval (scaledTest s δ x η)|
          ≤ ∑ _a ∈ hfin.toFinset, (|C₂| * C₃ * δ ^ β) := Finset.sum_le_sum hterm
        _ = (hfin.toFinset.card : ℝ) * (|C₂| * C₃ * δ ^ β) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (hfin.toFinset.card : ℝ) * (|C₂| * C₃) * δ ^ β := by ring
  have htri : |ξ.eval (scaledTest s δ x η)|
      ≤ |(ξ - Pi x (f x)).eval (scaledTest s δ x η)|
        + |(Pi x (f x)).eval (scaledTest s δ x η)| := by
    have e : ξ.eval (scaledTest s δ x η)
        = (ξ - Pi x (f x)).eval (scaledTest s δ x η)
          + (Pi x (f x)).eval (scaledTest s δ x η) := by
      rw [← heval_add]
      congr 1
      exact (sub_add_cancel ξ (Pi x (f x))).symm
    rw [e]
    exact abs_add_le _ _
  have g1 : |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ |C₁| * δ ^ β := by
    refine le_trans h1 ?_
    have hδγ : δ ^ γ ≤ δ ^ β :=
      Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
    have hposγ : (0 : ℝ) ≤ δ ^ γ := Real.rpow_nonneg hδ0.le _
    calc C₁ * δ ^ γ ≤ |C₁| * δ ^ γ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₁) hposγ
      _ ≤ |C₁| * δ ^ β := mul_le_mul_of_nonneg_left hδγ (abs_nonneg _)
  calc |ξ.eval (scaledTest s δ x η)|
      ≤ |(ξ - Pi x (f x)).eval (scaledTest s δ x η)|
          + |(Pi x (f x)).eval (scaledTest s δ x η)| := htri
    _ ≤ |C₁| * δ ^ β + (hfin.toFinset.card : ℝ) * (|C₂| * C₃) * δ ^ β :=
        add_le_add g1 h2
    _ = (|C₁| + (hfin.toFinset.card : ℝ) * (|C₂| * C₃)) * δ ^ β := by ring
