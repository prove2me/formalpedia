-- Prove2me | solution 1 for HunterPDE.Regularity.weakDeriv_diffQuot_comm
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:37:05.058958+00:00
-- url     : https://prove2.me/submissions/7ee759f8-70ae-466a-97f0-9260d73ceae7

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

open MeasureTheory
open scoped ContDiff

namespace HunterPDE.Regularity

open HunterPDE.Shared

variable {n : ℕ}

/-- Translation commutes with `partialDeriv`. -/
lemma partialDeriv_comp_add_core (u : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (e : EuclideanSpace ℝ (Fin n)) :
    partialDeriv (fun x => u (x + e)) i = fun x => partialDeriv u i (x + e) := by
  funext x
  simp only [partialDeriv, fderiv_comp_add_right]

/-- Translation commutes with `iteratedPartial`. -/
lemma iteratedPartial_comp_add_core (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (e : EuclideanSpace ℝ (Fin n)) :
    ∀ l : List (Fin n),
      iteratedPartial (fun x => u (x + e)) l = fun x => iteratedPartial u l (x + e) := by
  intro l
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [iteratedPartial, ih]
    exact partialDeriv_comp_add_core _ i e

/-- Translation commutes with `multiDeriv`. -/
lemma multiDeriv_comp_add_core (u : EuclideanSpace ℝ (Fin n) → ℝ) (α : Fin n → ℕ)
    (e : EuclideanSpace ℝ (Fin n)) :
    multiDeriv (fun x => u (x + e)) α = fun x => multiDeriv u α (x + e) :=
  iteratedPartial_comp_add_core u e _

/-- Smoothness and compact support are preserved by `iteratedPartial`. -/
lemma iteratedPartial_smooth_core (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) :
    ∀ l : List (Fin n),
      ContDiff ℝ ∞ (iteratedPartial u l) ∧ HasCompactSupport (iteratedPartial u l) := by
  intro l
  induction l with
  | nil => exact ⟨hu, huc⟩
  | cons i l ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · show ContDiff ℝ ∞ (fun x => fderiv ℝ (iteratedPartial u l) x (EuclideanSpace.single i 1))
      exact (h1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    · show HasCompactSupport (fun x => fderiv ℝ (iteratedPartial u l) x (EuclideanSpace.single i 1))
      exact (h2.fderiv ℝ).comp_left
        (g := fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) rfl

/-- Translates of locally integrable functions are locally integrable. -/
lemma locallyIntegrable_translate_core (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : LocallyIntegrable u volume) (e : EuclideanSpace ℝ (Fin n)) :
    LocallyIntegrable (fun x => u (x + e)) volume := by
  have h := (locallyIntegrable_map_homeomorph (Homeomorph.addRight e) (f := u)
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))).mp
  have hmap : Measure.map (⇑(Homeomorph.addRight e)) (volume : Measure (EuclideanSpace ℝ (Fin n))) =
      volume := by
    have : (⇑(Homeomorph.addRight e) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
        fun x => x + e := by funext x; rfl
    rw [this]
    exact map_add_right_eq_self volume e
  rw [hmap] at h
  exact h hu

/-- A locally integrable function times a continuous compactly supported one is integrable. -/
lemma integrable_mul_core (u g : EuclideanSpace ℝ (Fin n) → ℝ) (hu : LocallyIntegrable u volume)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => u x * g x) volume := by
  have := hu.integrable_smul_left_of_hasCompactSupport hg hgc
  simpa [mul_comm, smul_eq_mul] using this

end HunterPDE.Regularity

open HunterPDE.Regularity HunterPDE.Shared in
theorem solution {n : ℕ} (i j : Fin n) (h : ℝ) (hh : h ≠ 0)
    (u g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : HunterPDE.Shared.HasWeakDeriv Set.univ (Pi.single i 1) u g) :
    HunterPDE.Shared.HasWeakDeriv Set.univ (Pi.single i 1) (HunterPDE.Regularity.diffQuot j h u)
      (HunterPDE.Regularity.diffQuot j h g) := by
  obtain ⟨hu_loc, hg_loc, hweak⟩ := hg
  rw [locallyIntegrableOn_univ] at hu_loc hg_loc
  set e : EuclideanSpace ℝ (Fin n) := h • EuclideanSpace.single j (1 : ℝ) with he
  have hdq : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      diffQuot j h f = (1 / h) • ((fun x => f (x + e)) - f) := by
    intro f; funext x
    simp only [diffQuot, he, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hu_e := locallyIntegrable_translate_core u hu_loc e
  have hg_e := locallyIntegrable_translate_core g hg_loc e
  refine ⟨?_, ?_, ?_⟩
  · rw [locallyIntegrableOn_univ, hdq]
    exact (hu_e.sub hu_loc).smul _
  · rw [locallyIntegrableOn_univ, hdq]
    exact (hg_e.sub hg_loc).smul _
  · intro φ hφ
    obtain ⟨hφs, hφc, -⟩ := hφ
    simp only [Measure.restrict_univ]
    have hsum : (∑ k, (Pi.single i 1 : Fin n → ℕ) k) = 1 := by simp
    rw [hsum, pow_one]
    -- the derivative of `φ` and of its translate
    obtain ⟨hDs, hDc⟩ := iteratedPartial_smooth_core φ hφs hφc (multiIndexList (Pi.single i 1))
    have hDs' : Continuous (multiDeriv φ (Pi.single i 1)) := hDs.continuous
    have hDc' : HasCompactSupport (multiDeriv φ (Pi.single i 1)) := hDc
    -- the translated test function
    have hφe : IsTestFunction Set.univ (fun x => φ (x + -e)) := by
      refine ⟨hφs.comp (contDiff_id.add contDiff_const), ?_, Set.subset_univ _⟩
      have : (fun x => φ (x + -e)) = φ ∘ ⇑(Homeomorph.addRight (-e)) := by funext x; rfl
      rw [this]
      exact hφc.comp_homeomorph _
    have hw1 := hweak φ ⟨hφs, hφc, Set.subset_univ _⟩
    have hw2 := hweak _ hφe
    simp only [Measure.restrict_univ, hsum, pow_one, neg_one_mul] at hw1 hw2
    rw [multiDeriv_comp_add_core] at hw2
    -- translate the integrals in `hw2`
    have ht1 : ∫ x, g (x + e) * φ x = ∫ x, g x * φ (x + -e) := by
      rw [← integral_add_right_eq_self (fun x => g x * φ (x + -e)) e]
      simp only [add_neg_cancel_right]
    have ht2 : ∫ x, u (x + e) * multiDeriv φ (Pi.single i 1) x =
        ∫ x, u x * multiDeriv φ (Pi.single i 1) (x + -e) := by
      rw [← integral_add_right_eq_self (fun x => u x * multiDeriv φ (Pi.single i 1) (x + -e)) e]
      simp only [add_neg_cancel_right]
    rw [← ht1, ← ht2] at hw2
    -- integrability
    have i1 : Integrable (fun x => g (x + e) * φ x) volume :=
      integrable_mul_core _ _ hg_e hφs.continuous hφc
    have i2 : Integrable (fun x => g x * φ x) volume :=
      integrable_mul_core _ _ hg_loc hφs.continuous hφc
    have i3 : Integrable (fun x => u (x + e) * multiDeriv φ (Pi.single i 1) x) volume :=
      integrable_mul_core _ _ hu_e hDs' hDc'
    have i4 : Integrable (fun x => u x * multiDeriv φ (Pi.single i 1) x) volume :=
      integrable_mul_core _ _ hu_loc hDs' hDc'
    -- expand both sides
    have eL : (fun x => diffQuot j h g x * φ x) =
        fun x => (1 / h) * (g (x + e) * φ x - g x * φ x) := by
      funext x; simp only [diffQuot, he]; ring
    have eR : (fun x => diffQuot j h u x * multiDeriv φ (Pi.single i 1) x) =
        fun x => (1 / h) * (u (x + e) * multiDeriv φ (Pi.single i 1) x -
          u x * multiDeriv φ (Pi.single i 1) x) := by
      funext x; simp only [diffQuot, he]; ring
    rw [eL, eR, integral_const_mul, integral_const_mul, integral_sub i1 i2, integral_sub i3 i4,
      hw1, hw2]
    ring

#print axioms solution
