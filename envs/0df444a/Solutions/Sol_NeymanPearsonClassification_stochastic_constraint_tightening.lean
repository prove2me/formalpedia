-- Prove2me | solution 1 for NeymanPearsonClassification.stochastic_constraint_tightening
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:43:50.853573+00:00
-- url     : https://prove2.me/submissions/85bab7b7-0396-4189-bdc1-bcd621089d0e

import Mathlib
import Definitions.Def_NeymanPearsonClassification_Basic

open MeasureTheory ProbabilityTheory

namespace NeymanPearsonClassification

variable {d M : ℕ}

lemma ga_range (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    {l : Fin M → ℝ} (hl : l ∈ stdSimplex ℝ (Fin M)) (x : EuclideanSpace ℝ (Fin d)) :
    convComb h l x ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨hl0, hl1⟩ := hl
  unfold convComb
  constructor
  · calc (-1 : ℝ) = ∑ j, l j * (-1) := by rw [← Finset.sum_mul, hl1]; ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ((hh j).2 x).1 (hl0 j)
  · calc ∑ j, l j * h j x ≤ ∑ j, l j * 1 := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left ((hh j).2 x).2 (hl0 j)
      _ = 1 := by rw [← Finset.sum_mul, hl1]; ring

lemma ga_meas (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    (l : Fin M → ℝ) : Measurable (convComb h l) := by
  unfold convComb
  exact Finset.measurable_sum _ fun j _ => (hh j).1.const_mul _

lemma ga_int (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ) (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Measurable f)
    (hr : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) : Integrable (fun x => φ (f x)) P := by
  set ψ : ℝ → ℝ := fun u => φ ((Set.projIcc (-1 : ℝ) 1 (by norm_num) u : ℝ)) with hψ
  have hψc : Continuous ψ := hφ.2.2.1.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun u => (Set.projIcc _ _ _ u).2)
  have he : (fun x => φ (f x)) = fun x => ψ (f x) := by
    funext x; simp only [hψ]; rw [Set.projIcc_of_mem _ (hr x)]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.2.2.1
  rw [he]
  refine Integrable.of_bound (hψc.measurable.comp hf).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [hψ]; rw [Set.projIcc_of_mem _ (hr x)]; exact hC _ (hr x)

lemma ga_bdd (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    (Pm Pp : Measure (EuclideanSpace ℝ (Fin d))) (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ) (a : ℝ) :
    BddBelow (phiTypeII Pp φ '' Hphi h Pm φ a) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨f, ⟨⟨l, hl, rfl⟩, _⟩, rfl⟩
  unfold phiTypeII
  refine integral_nonneg fun x => hφ.1 _ ?_
  have := ga_range h hh hl x
  constructor <;> linarith [this.1, this.2]

end NeymanPearsonClassification

open NeymanPearsonClassification in
theorem solution {d M : ℕ} (hM : 2 ≤ M)
    (h : Fin M → EuclideanSpace ℝ (Fin d) → ℝ) (hh : IsBaseFamily h)
    (Pm Pp : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure Pm] [IsProbabilityMeasure Pp]
    (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ)
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1) (ν₀ : ℝ) (hν₀ : 0 < ν₀)
    (hne : (Hphi h Pm φ (α - ν₀)).Nonempty) (ν : ℝ) (hν : ν ∈ Set.Ioo 0 ν₀) :
    minPhiTypeII h Pm Pp φ (α - ν) - minPhiTypeII h Pm Pp φ α ≤ φ 1 * (ν / (ν₀ - ν)) := by
  obtain ⟨hν0, hνν⟩ := hν
  have hneg : ∀ {l : Fin M → ℝ}, l ∈ stdSimplex ℝ (Fin M) → ∀ x,
      -convComb h l x ∈ Set.Icc (-1 : ℝ) 1 := fun hl x => by
    have := ga_range h hh hl x; constructor <;> linarith [this.1, this.2]
  have hφ1 : 0 ≤ φ 1 := hφ.1 1 ⟨by norm_num, le_rfl⟩
  obtain ⟨_, ⟨l0, hl0, rfl⟩, hf0⟩ := hne
  set θ2 : ℝ := ν / ν₀ with hθ2
  set θ1 : ℝ := 1 - θ2 with hθ1
  have h2 : 0 ≤ θ2 := by positivity
  have h2' : θ2 ≤ 1 := by rw [hθ2, div_le_one hν₀]; linarith
  have h1 : 0 ≤ θ1 := by linarith
  have hs : θ1 + θ2 = 1 := by ring
  have hII0 : phiTypeII Pp φ (convComb h l0) ≤ φ 1 := by
    unfold phiTypeII
    have j := ga_int φ hφ Pp (fun x => -convComb h l0 x) (ga_meas h hh l0).neg (hneg hl0)
    calc ∫ x, φ (-convComb h l0 x) ∂Pp ≤ ∫ _x, φ 1 ∂Pp :=
          integral_mono j (integrable_const _) fun x => hφ.2.1 (hneg hl0 x) ⟨by norm_num, le_rfl⟩ (hneg hl0 x).2
      _ = φ 1 := by simp
  have key : ∀ f ∈ Hphi h Pm φ α,
      minPhiTypeII h Pm Pp φ (α - ν) - θ2 * φ 1 ≤ phiTypeII Pp φ f := by
    rintro _ ⟨⟨l1, hl1, rfl⟩, hf1⟩
    have hl : θ1 • l1 + θ2 • l0 ∈ stdSimplex ℝ (Fin M) := convex_stdSimplex ℝ (Fin M) hl1 hl0 h1 h2 hs
    have hcc : ∀ x, convComb h (θ1 • l1 + θ2 • l0) x = θ1 * convComb h l1 x + θ2 * convComb h l0 x := by
      intro x; simp only [convComb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    have i1 := ga_int φ hφ Pm _ (ga_meas h hh l1) (ga_range h hh hl1)
    have i2 := ga_int φ hφ Pm _ (ga_meas h hh l0) (ga_range h hh hl0)
    have j1 := ga_int φ hφ Pp (fun x => -convComb h l1 x) (ga_meas h hh l1).neg (hneg hl1)
    have j2 := ga_int φ hφ Pp (fun x => -convComb h l0 x) (ga_meas h hh l0).neg (hneg hl0)
    have i0 := ga_int φ hφ Pm _ (ga_meas h hh _) (ga_range h hh hl)
    have j0 := ga_int φ hφ Pp (fun x => -convComb h (θ1 • l1 + θ2 • l0) x) (ga_meas h hh _).neg (hneg hl)
    have hI : phiTypeI Pm φ (convComb h (θ1 • l1 + θ2 • l0)) ≤ α - ν := by
      have : phiTypeI Pm φ (convComb h (θ1 • l1 + θ2 • l0)) ≤
          θ1 * phiTypeI Pm φ (convComb h l1) + θ2 * phiTypeI Pm φ (convComb h l0) := by
        unfold phiTypeI
        rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _) (i2.const_mul _)]
        refine integral_mono i0 ((i1.const_mul _).add (i2.const_mul _)) fun x => ?_
        simp only [hcc]
        have := hφ.2.2.2.1.2 (ga_range h hh hl1 x) (ga_range h hh hl0 x) h1 h2 hs
        simpa [smul_eq_mul] using this
      have e1 := mul_le_mul_of_nonneg_left hf1 h1
      have e2 := mul_le_mul_of_nonneg_left hf0 h2
      have : θ1 * α + θ2 * (α - ν₀) = α - ν := by
        rw [hθ1, hθ2]; field_simp; ring
      linarith
    have hII : phiTypeII Pp φ (convComb h (θ1 • l1 + θ2 • l0)) ≤
        θ1 * phiTypeII Pp φ (convComb h l1) + θ2 * phiTypeII Pp φ (convComb h l0) := by
      unfold phiTypeII
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul _) (j2.const_mul _)]
      refine integral_mono j0 ((j1.const_mul _).add (j2.const_mul _)) fun x => ?_
      simp only [hcc]
      have := hφ.2.2.2.1.2 (hneg hl1 x) (hneg hl0 x) h1 h2 hs
      rw [show -(θ1 * convComb h l1 x + θ2 * convComb h l0 x) =
        θ1 • (-convComb h l1 x) + θ2 • (-convComb h l0 x) by simp [smul_eq_mul]; ring]
      simpa [smul_eq_mul] using this
    have hg := (csInf_le (ga_bdd h hh Pm Pp φ hφ _) ⟨_, ⟨⟨_, hl, rfl⟩, hI⟩, rfl⟩).trans hII
    have hnn : 0 ≤ phiTypeII Pp φ (convComb h l1) := by
      unfold phiTypeII
      exact integral_nonneg fun x => hφ.1 _ (hneg hl1 x)
    have e3 : θ1 * phiTypeII Pp φ (convComb h l1) ≤ phiTypeII Pp φ (convComb h l1) := by
      nlinarith
    have e4 := mul_le_mul_of_nonneg_left hII0 h2
    change minPhiTypeII h Pm Pp φ (α - ν) - θ2 * φ 1 ≤ phiTypeII Pp φ (convComb h l1)
    unfold minPhiTypeII at hg ⊢
    linarith
  have hneα : (Hphi h Pm φ α).Nonempty :=
    ⟨_, ⟨⟨l0, hl0, rfl⟩, hf0.trans (by linarith)⟩⟩
  have hle : minPhiTypeII h Pm Pp φ (α - ν) - θ2 * φ 1 ≤ minPhiTypeII h Pm Pp φ α := by
    apply le_csInf (hneα.image _)
    rintro _ ⟨f, hf, rfl⟩; exact key f hf
  have hθle : θ2 ≤ ν / (ν₀ - ν) := by
    rw [hθ2]; exact div_le_div_of_nonneg_left hν0.le (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left hθle hφ1
  nlinarith
