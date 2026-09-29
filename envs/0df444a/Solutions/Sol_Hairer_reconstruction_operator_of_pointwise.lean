-- Prove2me | solution 1 for Hairer.reconstruction_operator_of_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:58:36.779193+00:00
-- url     : https://prove2.me/submissions/a2164e55-98d3-4b2d-a00d-104a0cf068a8

import Definitions.Def_Hairer_Model

set_option autoImplicit false

noncomputable section

namespace Hairer

variable {d : ℕ} {s : Fin d → ℕ} {γ : ℝ}
  {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
  [∀ a : A, NormedSpace ℝ (E a)]
  {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}

/-- The zero function is modelled at every order. -/
theorem IsModelled.zero : IsModelled s γ Gam 0 where
  vanishing := by intros; simp [proj]
  bound := by
    intro K hK
    refine ⟨0, ?_, ?_⟩ <;> intros <;> simp [proj]

/-- Modelled distributions are closed under addition. -/
theorem IsModelled.add {f g : Pt d → ModelSpace A E}
    (hf : IsModelled s γ Gam f) (hg : IsModelled s γ Gam g) :
    IsModelled s γ Gam (f + g) where
  vanishing := by
    intro x a ha
    change proj a (f x + g x) = 0
    rw [map_add, hf.vanishing x a ha, hg.vanishing x a ha, zero_add]
  bound := by
    intro K hK
    obtain ⟨Cf, hfb, hfi⟩ := hf.bound K hK
    obtain ⟨Cg, hgb, hgi⟩ := hg.bound K hK
    refine ⟨Cf + Cg, ?_, ?_⟩
    · intro x hx b hb
      change ‖proj b (f x + g x)‖ ≤ _
      rw [map_add]
      exact (norm_add_le _ _).trans (add_le_add (hfb x hx b hb) (hgb x hx b hb))
    · intro x hx y hy hxy b hb
      have heq : (f + g) x - Gam x y ((f + g) y) =
          (f x - Gam x y (f y)) + (g x - Gam x y (g y)) := by
        simp only [Pi.add_apply, map_add]
        abel
      rw [heq, map_add, add_mul]
      exact (norm_add_le _ _).trans
        (add_le_add (hfi x hx y hy hxy b hb) (hgi x hx y hy hxy b hb))

/-- Scalar multiplication preserves the modelled-distribution bounds. -/
theorem IsModelled.smul {f : Pt d → ModelSpace A E}
    (hf : IsModelled s γ Gam f) (c : ℝ) : IsModelled s γ Gam (c • f) where
  vanishing := by
    intro x a ha
    change proj a (c • f x) = 0
    rw [map_smul, hf.vanishing x a ha, smul_zero]
  bound := by
    intro K hK
    obtain ⟨Cf, hfb, hfi⟩ := hf.bound K hK
    refine ⟨‖c‖ * Cf, ?_, ?_⟩
    · intro x hx b hb
      change ‖proj b (c • f x)‖ ≤ _
      rw [map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left (hfb x hx b hb) (norm_nonneg c)
    · intro x hx y hy hxy b hb
      have heq : (c • f) x - Gam x y ((c • f) y) =
          c • (f x - Gam x y (f y)) := by
        simp only [Pi.smul_apply, map_smul, smul_sub]
      rw [heq, map_smul, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hfi x hx y hy hxy b hb) (norm_nonneg c)

/-- The vector space of modelled distributions for a fixed model and order. -/
def modelledSubmodule (s : Fin d → ℕ) (γ : ℝ)
    (Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E) :
    Submodule ℝ (Pt d → ModelSpace A E) where
  carrier := {f | IsModelled s γ Gam f}
  zero_mem' := IsModelled.zero
  add_mem' := fun hf hg ↦ hf.add hg
  smul_mem' := fun c _ hf ↦ hf.smul c

end Hairer

namespace Hairer

@[simp] theorem Distrib.eval_zero {d : ℕ} (φ : Pt d → ℝ) :
    (0 : Distrib d).eval φ = 0 := by
  simp [Distrib.eval]

@[simp] theorem Distrib.eval_add {d : ℕ} (ξ ζ : Distrib d) (φ : Pt d → ℝ) :
    (ξ + ζ).eval φ = ξ.eval φ + ζ.eval φ := by
  unfold Distrib.eval
  split <;> simp_all

@[simp] theorem Distrib.eval_smul {d : ℕ} (c : ℝ) (ξ : Distrib d) (φ : Pt d → ℝ) :
    (c • ξ).eval φ = c * ξ.eval φ := by
  unfold Distrib.eval
  split <;> simp_all

/-- Families of distributions with one fixed local scaling bound form a vector space. -/
def testBoundSubmodule {d : ℕ} (s : Fin d → ℕ) (r : ℕ) (α : ℝ) :
    Submodule ℝ (Pt d → Distrib d) where
  carrier := {F | ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
      |(F x).eval (scaledTest s δ x η)| ≤ C * δ ^ α}
  zero_mem' := by
    intro K hK
    refine ⟨0, ?_⟩
    intros
    simp
  add_mem' := by
    intro F H hF hH K hK
    obtain ⟨CF, hCF⟩ := hF K hK
    obtain ⟨CH, hCH⟩ := hH K hK
    refine ⟨CF + CH, ?_⟩
    intro x hx δ hδ hδone η hη
    simp only [Pi.add_apply, Distrib.eval_add, add_mul]
    exact (abs_add_le _ _).trans
      (add_le_add (hCF x hx δ hδ hδone η hη) (hCH x hx δ hδ hδone η hη))
  smul_mem' := by
    intro c F hF K hK
    obtain ⟨C, hC⟩ := hF K hK
    refine ⟨|c| * C, ?_⟩
    intro x hx δ hδ hδone η hη
    simp only [Pi.smul_apply, Distrib.eval_smul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC x hx δ hδ hδone η hη) (abs_nonneg c)

/-- A surjective linear relation between vector spaces admits a linear selection. -/
theorem exists_linear_selection
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (P : Submodule ℝ (V × W)) (hP : ∀ v : V, ∃ w : W, (v, w) ∈ P) :
    ∃ L : V →ₗ[ℝ] W, ∀ v, (v, L v) ∈ P := by
  let first : P →ₗ[ℝ] V := (LinearMap.fst ℝ V W).comp P.subtype
  have hsurj : Function.Surjective first := by
    intro v
    obtain ⟨w, hw⟩ := hP v
    exact ⟨⟨(v, w), hw⟩, rfl⟩
  obtain ⟨sectionMap, hsection⟩ :=
    first.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let L := ((LinearMap.snd ℝ V W).comp P.subtype).comp sectionMap
  refine ⟨L, ?_⟩
  intro v
  have hfirst : (sectionMap v).val.1 = v :=
    LinearMap.congr_fun hsection v
  have hmem := (sectionMap v).property
  change ((sectionMap v).val.1, (sectionMap v).val.2) ∈ P at hmem
  change (v, (sectionMap v).val.2) ∈ P
  simpa only [hfirst] using hmem

end Hairer

open Hairer

theorem solution
    {d : ℕ} {s : Fin d → ℕ} {α γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hex : ∀ f : Pt d → ModelSpace A E, IsModelled s γ Gam f →
      ∃ ξ : Distrib d, MemCalpha s α ξ ∧
        ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) :
    ∃ R : (Pt d → ModelSpace A E) → Distrib d,
      (∀ f g : Pt d → ModelSpace A E, IsModelled s γ Gam f → IsModelled s γ Gam g →
        R (f + g) = R f + R g) ∧
      (∀ (c : ℝ) (f : Pt d → ModelSpace A E), IsModelled s γ Gam f →
        R (c • f) = c • R f) ∧
      (∀ f : Pt d → ModelSpace A E, IsModelled s γ Gam f →
        MemCalpha s α (R f) ∧
        ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(R f - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) := by
  classical
  let M := modelledSubmodule s γ Gam
  let regular : (M × Distrib d) →ₗ[ℝ] (Pt d → Distrib d) :=
    { toFun := fun p _ ↦ p.2
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let residual : (M × Distrib d) →ₗ[ℝ] (Pt d → Distrib d) :=
    { toFun := fun p x ↦ p.2 - Pi x (p.1.val x)
      map_add' := by
        intro p q
        funext x
        change p.2 + q.2 - Pi x (p.1.val x + q.1.val x) = _
        rw [map_add]
        change p.2 + q.2 - (Pi x (p.1.val x) + Pi x (q.1.val x)) =
          (p.2 - Pi x (p.1.val x)) + (q.2 - Pi x (q.1.val x))
        abel
      map_smul' := by
        intro c p
        funext x
        change c • p.2 - Pi x (c • p.1.val x) = c • (p.2 - Pi x (p.1.val x))
        rw [map_smul, smul_sub] }
  let P : Submodule ℝ (M × Distrib d) :=
    (testBoundSubmodule s (negReg α) α).comap regular ⊓
      (testBoundSubmodule s r γ).comap residual
  have hP : ∀ f : M, ∃ ξ : Distrib d, (f, ξ) ∈ P := by
    intro f
    obtain ⟨ξ, hreg, herr⟩ := hex f.val f.property
    exact ⟨ξ, hreg, herr⟩
  obtain ⟨L, hL⟩ := exists_linear_selection P hP
  let R : (Pt d → ModelSpace A E) → Distrib d :=
    fun f ↦ if hf : IsModelled s γ Gam f then L ⟨f, hf⟩ else 0
  have hR (f : Pt d → ModelSpace A E) (hf : IsModelled s γ Gam f) :
      R f = L ⟨f, hf⟩ := dif_pos hf
  refine ⟨R, ?_, ?_, ?_⟩
  · intro f g hf hg
    rw [hR (f + g) (hf.add hg), hR f hf, hR g hg]
    exact L.map_add ⟨f, hf⟩ ⟨g, hg⟩
  · intro c f hf
    rw [hR (c • f) (hf.smul c), hR f hf]
    exact L.map_smul c ⟨f, hf⟩
  · intro f hf
    rw [hR f hf]
    exact hL ⟨f, hf⟩


#print axioms solution
