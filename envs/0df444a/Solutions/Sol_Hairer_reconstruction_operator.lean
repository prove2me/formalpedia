-- Prove2me | solution 1 for Hairer.reconstruction_operator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T12:17:31.572734+00:00
-- url     : https://prove2.me/submissions/b34b54b2-5098-4f90-86a3-5fbcdedc3399
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Hairer_Model
import Theorems.Thm_Hairer_reconstruction_existence_pointwise_pos
import Theorems.Thm_Hairer_reconstruction_existence_pointwise_nonpos

set_option autoImplicit false

open scoped Classical DirectSum

noncomputable section

open Hairer

namespace HairerSelection

variable {d : ℕ}

/-- Pairing a sum of distributions with a function. -/
theorem eval_add (ξ ζ : Distrib d) (φ : Pt d → ℝ) :
    (ξ + ζ).eval φ = ξ.eval φ + ζ.eval φ := by
  unfold Distrib.eval
  split <;> simp

/-- Pairing a rescaled distribution with a function. -/
theorem eval_smul (c : ℝ) (ξ : Distrib d) (φ : Pt d → ℝ) :
    (c • ξ).eval φ = c * ξ.eval φ := by
  unfold Distrib.eval
  split <;> simp

/-- Pairing the zero distribution with a function. -/
theorem eval_zero (φ : Pt d → ℝ) : (0 : Distrib d).eval φ = 0 := by
  unfold Distrib.eval
  split <;> simp

variable {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
  [∀ a : A, NormedSpace ℝ (E a)]

/-- The reconstruction bound (3.3) of Hairer, for the germ of `f` and the distribution
`ξ`: on every compact set, `|(ξ - Π_x f(x))(S^δ_{s,x} η)| ≤ C δ^γ` uniformly over
`x ∈ K`, `δ ∈ (0,1]` and `η ∈ B^r_{s,0}`. -/
def ReconBound (s : Fin d → ℕ) (r : ℕ) (γ : ℝ)
    (Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d)
    (f : Pt d → ModelSpace A E) (ξ : Distrib d) : Prop :=
  ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ η : Pt d → ℝ, IsTestBall s r η →
      |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ

section Modelled

variable {s : Fin d → ℕ} {γ : ℝ}
  {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}

/-- The zero function is a modelled distribution. -/
theorem isModelled_zero : IsModelled s γ Gam (0 : Pt d → ModelSpace A E) where
  vanishing := by intro x a _; simp
  bound := by
    refine fun K _ => ⟨0, ?_, ?_⟩
    · intro x _ b _; simp
    · intro x _ y _ _ b _; simp

/-- The sum of two modelled distributions of order `γ` is modelled of order `γ`. -/
theorem isModelled_add {f g : Pt d → ModelSpace A E}
    (hf : IsModelled s γ Gam f) (hg : IsModelled s γ Gam g) :
    IsModelled s γ Gam (f + g) where
  vanishing := by
    intro x a ha
    simp [map_add, hf.vanishing x a ha, hg.vanishing x a ha]
  bound := by
    intro K hK
    obtain ⟨C₁, hb₁, hd₁⟩ := hf.bound K hK
    obtain ⟨C₂, hb₂, hd₂⟩ := hg.bound K hK
    refine ⟨C₁ + C₂, ?_, ?_⟩
    · intro x hx b hb
      have hsum : proj b ((f + g) x) = proj b (f x) + proj b (g x) := by
        show proj b (f x + g x) = _
        rw [map_add]
      rw [hsum]
      exact (norm_add_le _ _).trans (add_le_add (hb₁ x hx b hb) (hb₂ x hx b hb))
    · intro x hx y hy hxy b hb
      have hvec : (f + g) x - Gam x y ((f + g) y)
          = (f x - Gam x y (f y)) + (g x - Gam x y (g y)) := by
        show f x + g x - Gam x y (f y + g y) = _
        rw [map_add]
        abel
      rw [hvec, map_add]
      refine (norm_add_le _ _).trans ?_
      calc ‖proj b (f x - Gam x y (f y))‖ + ‖proj b (g x - Gam x y (g y))‖
          ≤ C₁ * snorm s (x - y) ^ (γ - (b : ℝ)) + C₂ * snorm s (x - y) ^ (γ - (b : ℝ)) :=
            add_le_add (hd₁ x hx y hy hxy b hb) (hd₂ x hx y hy hxy b hb)
        _ = (C₁ + C₂) * snorm s (x - y) ^ (γ - (b : ℝ)) := by ring

/-- A scalar multiple of a modelled distribution of order `γ` is modelled of order `γ`. -/
theorem isModelled_smul {f : Pt d → ModelSpace A E} (c : ℝ)
    (hf : IsModelled s γ Gam f) : IsModelled s γ Gam (c • f) where
  vanishing := by
    intro x a ha
    show proj a (c • f x) = 0
    rw [map_smul, hf.vanishing x a ha, smul_zero]
  bound := by
    intro K hK
    obtain ⟨C, hb, hd⟩ := hf.bound K hK
    refine ⟨|c| * C, ?_, ?_⟩
    · intro x hx b hbg
      have hsmul : proj b ((c • f) x) = c • proj b (f x) := by
        show proj b (c • f x) = _
        rw [map_smul]
      rw [hsmul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hb x hx b hbg) (abs_nonneg c)
    · intro x hx y hy hxy b hbg
      have hvec : (c • f) x - Gam x y ((c • f) y) = c • (f x - Gam x y (f y)) := by
        show c • f x - Gam x y (c • f y) = _
        rw [map_smul, smul_sub]
      rw [hvec, map_smul, norm_smul, Real.norm_eq_abs]
      calc |c| * ‖proj b (f x - Gam x y (f y))‖
          ≤ |c| * (C * snorm s (x - y) ^ (γ - (b : ℝ))) :=
            mul_le_mul_of_nonneg_left (hd x hx y hy hxy b hbg) (abs_nonneg c)
        _ = |c| * C * snorm s (x - y) ^ (γ - (b : ℝ)) := by ring

/-- The modelled distributions of order `γ` form a linear subspace. -/
def modelledSubmodule (s : Fin d → ℕ) (γ : ℝ)
    (Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E) :
    Submodule ℝ (Pt d → ModelSpace A E) where
  carrier := {f | IsModelled s γ Gam f}
  add_mem' hf hg := isModelled_add hf hg
  zero_mem' := isModelled_zero
  smul_mem' c _ hf := isModelled_smul c hf

end Modelled

section Bounds

variable {s : Fin d → ℕ} {α γ : ℝ} {r : ℕ}
  {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}

/-- The zero distribution lies in `C^α_s`. -/
theorem memCalpha_zero : MemCalpha s α (0 : Distrib d) :=
  fun _ _ => ⟨0, fun _ _ _ _ _ _ _ => by simp [eval_zero]⟩

/-- `C^α_s` is stable under sums. -/
theorem memCalpha_add {ξ ζ : Distrib d} (hξ : MemCalpha s α ξ) (hζ : MemCalpha s α ζ) :
    MemCalpha s α (ξ + ζ) := by
  intro K hK
  obtain ⟨C₁, h₁⟩ := hξ K hK
  obtain ⟨C₂, h₂⟩ := hζ K hK
  refine ⟨C₁ + C₂, fun x hx δ hδ hδ1 η hη => ?_⟩
  rw [eval_add]
  calc |ξ.eval (scaledTest s δ x η) + ζ.eval (scaledTest s δ x η)|
      ≤ |ξ.eval (scaledTest s δ x η)| + |ζ.eval (scaledTest s δ x η)| := abs_add_le _ _
    _ ≤ C₁ * δ ^ α + C₂ * δ ^ α :=
        add_le_add (h₁ x hx δ hδ hδ1 η hη) (h₂ x hx δ hδ hδ1 η hη)
    _ = (C₁ + C₂) * δ ^ α := by ring

/-- `C^α_s` is stable under scalar multiples. -/
theorem memCalpha_smul (c : ℝ) {ξ : Distrib d} (hξ : MemCalpha s α ξ) :
    MemCalpha s α (c • ξ) := by
  intro K hK
  obtain ⟨C, hC⟩ := hξ K hK
  refine ⟨|c| * C, fun x hx δ hδ hδ1 η hη => ?_⟩
  rw [eval_smul, abs_mul]
  calc |c| * |ξ.eval (scaledTest s δ x η)| ≤ |c| * (C * δ ^ α) :=
        mul_le_mul_of_nonneg_left (hC x hx δ hδ hδ1 η hη) (abs_nonneg c)
    _ = |c| * C * δ ^ α := by ring

/-- The zero distribution reconstructs the germ of the zero modelled distribution. -/
theorem reconBound_zero : ReconBound s r γ Pi (0 : Pt d → ModelSpace A E) 0 :=
  fun _ _ => ⟨0, fun _ _ _ _ _ _ _ => by simp [eval_zero]⟩

/-- The reconstruction bound is additive in the pair `(f, ξ)`. -/
theorem reconBound_add {f g : Pt d → ModelSpace A E} {ξ ζ : Distrib d}
    (hf : ReconBound s r γ Pi f ξ) (hg : ReconBound s r γ Pi g ζ) :
    ReconBound s r γ Pi (f + g) (ξ + ζ) := by
  intro K hK
  obtain ⟨C₁, h₁⟩ := hf K hK
  obtain ⟨C₂, h₂⟩ := hg K hK
  refine ⟨C₁ + C₂, fun x hx δ hδ hδ1 η hη => ?_⟩
  have hdec : (ξ + ζ - Pi x ((f + g) x)) = (ξ - Pi x (f x)) + (ζ - Pi x (g x)) := by
    show (ξ + ζ - Pi x (f x + g x)) = _
    rw [map_add]
    abel
  rw [hdec, eval_add]
  calc |(ξ - Pi x (f x)).eval (scaledTest s δ x η)
          + (ζ - Pi x (g x)).eval (scaledTest s δ x η)|
      ≤ |(ξ - Pi x (f x)).eval (scaledTest s δ x η)|
        + |(ζ - Pi x (g x)).eval (scaledTest s δ x η)| := abs_add_le _ _
    _ ≤ C₁ * δ ^ γ + C₂ * δ ^ γ :=
        add_le_add (h₁ x hx δ hδ hδ1 η hη) (h₂ x hx δ hδ hδ1 η hη)
    _ = (C₁ + C₂) * δ ^ γ := by ring

/-- The reconstruction bound is homogeneous in the pair `(f, ξ)`. -/
theorem reconBound_smul (c : ℝ) {f : Pt d → ModelSpace A E} {ξ : Distrib d}
    (hf : ReconBound s r γ Pi f ξ) : ReconBound s r γ Pi (c • f) (c • ξ) := by
  intro K hK
  obtain ⟨C, hC⟩ := hf K hK
  refine ⟨|c| * C, fun x hx δ hδ hδ1 η hη => ?_⟩
  have hdec : (c • ξ - Pi x ((c • f) x)) = c • (ξ - Pi x (f x)) := by
    show (c • ξ - Pi x (c • f x)) = _
    rw [map_smul, smul_sub]
  rw [hdec, eval_smul, abs_mul]
  calc |c| * |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ |c| * (C * δ ^ γ) :=
        mul_le_mul_of_nonneg_left (hC x hx δ hδ hδ1 η hη) (abs_nonneg c)
    _ = |c| * C * δ ^ γ := by ring

end Bounds

section Selection

variable {s : Fin d → ℕ} {α γ : ℝ} {r : ℕ}
  {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
  {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}

/-- The pairs `(f, ξ)` with `f ∈ D^γ`, `ξ ∈ C^α_s` and `ξ` reconstructing the germ of
`f` form a linear subspace of `D^γ × C^α_s`. -/
def goodPairs (s : Fin d → ℕ) (α γ : ℝ) (r : ℕ)
    (Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d)
    (Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E) :
    Submodule ℝ ((Pt d → ModelSpace A E) × Distrib d) where
  carrier := {p | IsModelled s γ Gam p.1 ∧ MemCalpha s α p.2 ∧ ReconBound s r γ Pi p.1 p.2}
  add_mem' := by
    rintro p q ⟨hp1, hp2, hp3⟩ ⟨hq1, hq2, hq3⟩
    exact ⟨isModelled_add hp1 hq1, memCalpha_add hp2 hq2, reconBound_add hp3 hq3⟩
  zero_mem' := ⟨isModelled_zero, memCalpha_zero, reconBound_zero⟩
  smul_mem' := by
    rintro c p ⟨hp1, hp2, hp3⟩
    exact ⟨isModelled_smul c hp1, memCalpha_smul c hp2, reconBound_smul c hp3⟩

/-- The defining properties of an element of `goodPairs`. -/
theorem goodPairs_mem (w : goodPairs s α γ r Pi Gam) :
    IsModelled s γ Gam (w : (Pt d → ModelSpace A E) × Distrib d).1 ∧
      MemCalpha s α (w : (Pt d → ModelSpace A E) × Distrib d).2 ∧
      ReconBound s r γ Pi (w : (Pt d → ModelSpace A E) × Distrib d).1
        (w : (Pt d → ModelSpace A E) × Distrib d).2 := w.2

/-- Forgetting the distribution maps `goodPairs` linearly onto `D^γ`. -/
def forgetDistrib (s : Fin d → ℕ) (α γ : ℝ) (r : ℕ)
    (Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d)
    (Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E) :
    goodPairs s α γ r Pi Gam →ₗ[ℝ] modelledSubmodule s γ Gam where
  toFun w := ⟨w.1.1, w.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Linearity is free.** If every modelled distribution of order `γ` admits *some*
reconstruction, then a *linear* choice of reconstructions exists: the pairs
`(f, ξ)` form a linear subspace which surjects onto `D^γ`, and a surjection of vector
spaces admits a linear section. -/
theorem exists_linear_selection
    (hex : ∀ f : Pt d → ModelSpace A E, IsModelled s γ Gam f →
      ∃ ξ : Distrib d, MemCalpha s α ξ ∧ ReconBound s r γ Pi f ξ) :
    ∃ R : (Pt d → ModelSpace A E) → Distrib d,
      (∀ f g : Pt d → ModelSpace A E, IsModelled s γ Gam f → IsModelled s γ Gam g →
        R (f + g) = R f + R g) ∧
      (∀ (c : ℝ) (f : Pt d → ModelSpace A E), IsModelled s γ Gam f →
        R (c • f) = c • R f) ∧
      (∀ f : Pt d → ModelSpace A E, IsModelled s γ Gam f →
        MemCalpha s α (R f) ∧ ReconBound s r γ Pi f (R f)) := by
  have hsurj : LinearMap.range (forgetDistrib s α γ r Pi Gam) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨f, hf⟩
    obtain ⟨ξ, hξ1, hξ2⟩ := hex f hf
    exact ⟨⟨(f, ξ), ⟨hf, hξ1, hξ2⟩⟩, rfl⟩
  obtain ⟨q, hq⟩ := (forgetDistrib s α γ r Pi Gam).exists_rightInverse_of_surjective hsurj
  have hfst : ∀ (f : Pt d → ModelSpace A E) (hf : IsModelled s γ Gam f),
      ((q ⟨f, hf⟩ : goodPairs s α γ r Pi Gam) : (Pt d → ModelSpace A E) × Distrib d).1 = f := by
    intro f hf
    have := congrArg (fun T => (T : modelledSubmodule s γ Gam →ₗ[ℝ] _) ⟨f, hf⟩) hq
    simpa [forgetDistrib] using congrArg Subtype.val this
  refine ⟨fun f => if h : IsModelled s γ Gam f then
      ((q ⟨f, h⟩ : goodPairs s α γ r Pi Gam) : (Pt d → ModelSpace A E) × Distrib d).2
    else 0, ?_, ?_, ?_⟩
  · intro f g hf hg
    have hfg : IsModelled s γ Gam (f + g) := isModelled_add hf hg
    have hsum : (⟨f + g, hfg⟩ : modelledSubmodule s γ Gam) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
    simp only [dif_pos hf, dif_pos hg, dif_pos hfg, hsum, map_add]
    rfl
  · intro c f hf
    have hcf : IsModelled s γ Gam (c • f) := isModelled_smul c hf
    have hsmul : (⟨c • f, hcf⟩ : modelledSubmodule s γ Gam) = c • ⟨f, hf⟩ := rfl
    simp only [dif_pos hf, dif_pos hcf, hsmul, map_smul]
    rfl
  · intro f hf
    have hmem := goodPairs_mem (q ⟨f, hf⟩)
    rw [hfst f hf] at hmem
    simp only [dif_pos hf]
    exact ⟨hmem.2.1, hmem.2.2⟩

end Selection

end HairerSelection

open HairerSelection

/-- **Theorem 3.10 (existence of the reconstruction operator), Hairer 2014**, for an
arbitrary exponent `γ ∈ ℝ`. -/
theorem solution
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : IsLeast A α) (hαneg : α < 0) (γ : ℝ) :
    ∃ R : (Pt d → ModelSpace A E) → Distrib d,
      (∀ f g : Pt d → ModelSpace A E, IsModelled s γ Gam f → IsModelled s γ Gam g →
        R (f + g) = R f + R g) ∧
      (∀ (c : ℝ) (f : Pt d → ModelSpace A E), IsModelled s γ Gam f →
        R (c • f) = c • R f) ∧
      (∀ f : Pt d → ModelSpace A E, IsModelled s γ Gam f →
        MemCalpha s α (R f) ∧
        ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(R f - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) := by
  -- It suffices to reconstruct each modelled distribution separately: linearity is then
  -- obtained by choosing a linear section of the forgetful map on the space of good pairs.
  refine exists_linear_selection (α := α) (γ := γ) (r := r) (Pi := Pi) (Gam := Gam) ?_
  intro f hf
  rcases le_or_gt γ α with hγα | hγα
  · -- Degenerate range `γ ≤ α = min A`: every modelled distribution vanishes.
    have hf0 : f = 0 := by
      funext x
      refine DirectSum.ext_component ℝ fun a => ?_
      have hva : γ ≤ (a : ℝ) := hγα.trans (hα.2 a.2)
      simpa using hf.vanishing x a hva
    subst hf0
    exact ⟨0, memCalpha_zero, reconBound_zero⟩
  · rcases le_or_gt γ 0 with hγ0 | hγpos
    · exact Hairer.reconstruction_existence_pointwise_nonpos hs hT hmod hα hαneg hγα hγ0 hf
    · exact Hairer.reconstruction_existence_pointwise_pos hs hT hmod hα hαneg hγpos hf
