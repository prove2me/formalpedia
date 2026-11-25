-- Prove2me | solution 1 for NeymanPearsonClassification.gamma_antitone_convex
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T17:42:45.24722+00:00
-- url     : https://prove2.me/submissions/6661e97b-1262-49d9-a80d-855e334ae1f3

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
    (φ : ℝ → ℝ) (hφ : IsConvexSurrogate φ) :
    AntitoneOn (minPhiTypeII h Pm Pp φ)
        {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧ (Hphi h Pm φ a).Nonempty} ∧
      ConvexOn ℝ {a : ℝ | a ∈ Set.Icc (0 : ℝ) 1 ∧ (Hphi h Pm φ a).Nonempty}
        (minPhiTypeII h Pm Pp φ) := by
  have hsub : ∀ a b, a ≤ b → Hphi h Pm φ a ⊆ Hphi h Pm φ b := fun a b hab f hf =>
    ⟨hf.1, hf.2.trans hab⟩
  have hneg : ∀ {l : Fin M → ℝ}, l ∈ stdSimplex ℝ (Fin M) → ∀ x,
      -convComb h l x ∈ Set.Icc (-1 : ℝ) 1 := fun hl x => by
    have := ga_range h hh hl x; constructor <;> linarith [this.1, this.2]
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    exact csInf_le_csInf (ga_bdd h hh Pm Pp φ hφ b) (ha.2.image _) (Set.image_mono (hsub a b hab))
  · refine ⟨?_, ?_⟩
    · intro a ha b hb θ1 θ2 h1 h2 hs
      refine ⟨⟨by have := ha.1.1; have := hb.1.1; positivity, ?_⟩, ?_⟩
      · have := ha.1.2; have := hb.1.2
        simp only [smul_eq_mul]; nlinarith
      · rcases le_total a b with hab | hab
        · obtain ⟨f, hf⟩ := ha.2
          refine ⟨f, hsub a _ ?_ hf⟩
          have := mul_le_mul_of_nonneg_left hab h2
          have e : a = θ1 * a + θ2 * a := by linear_combination (-a) * hs
          simp only [smul_eq_mul]; linarith
        · obtain ⟨f, hf⟩ := hb.2
          refine ⟨f, hsub b _ ?_ hf⟩
          have := mul_le_mul_of_nonneg_left hab h1
          have e : b = θ1 * b + θ2 * b := by linear_combination (-b) * hs
          simp only [smul_eq_mul]; linarith
    · intro a ha b hb θ1 θ2 h1 h2 hs
      simp only [smul_eq_mul]
      have key : ∀ f1 ∈ Hphi h Pm φ a, ∀ f2 ∈ Hphi h Pm φ b,
          minPhiTypeII h Pm Pp φ (θ1 * a + θ2 * b) ≤
            θ1 * phiTypeII Pp φ f1 + θ2 * phiTypeII Pp φ f2 := by
        rintro _ ⟨⟨l1, hl1, rfl⟩, hf1⟩ _ ⟨⟨l2, hl2, rfl⟩, hf2⟩
        have hl : θ1 • l1 + θ2 • l2 ∈ stdSimplex ℝ (Fin M) := convex_stdSimplex ℝ (Fin M) hl1 hl2 h1 h2 hs
        have hcc : ∀ x, convComb h (θ1 • l1 + θ2 • l2) x = θ1 * convComb h l1 x + θ2 * convComb h l2 x := by
          intro x; simp only [convComb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
            Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
        have i1 := ga_int φ hφ Pm _ (ga_meas h hh l1) (ga_range h hh hl1)
        have i2 := ga_int φ hφ Pm _ (ga_meas h hh l2) (ga_range h hh hl2)
        have j1 := ga_int φ hφ Pp (fun x => -convComb h l1 x) (ga_meas h hh l1).neg (hneg hl1)
        have j2 := ga_int φ hφ Pp (fun x => -convComb h l2 x) (ga_meas h hh l2).neg (hneg hl2)
        have i0 := ga_int φ hφ Pm _ (ga_meas h hh _) (ga_range h hh hl)
        have j0 := ga_int φ hφ Pp (fun x => -convComb h (θ1 • l1 + θ2 • l2) x) (ga_meas h hh _).neg (hneg hl)
        have hconv := hφ.2.2.2.2
        have hI : phiTypeI Pm φ (convComb h (θ1 • l1 + θ2 • l2)) ≤ θ1 * a + θ2 * b := by
          have : phiTypeI Pm φ (convComb h (θ1 • l1 + θ2 • l2)) ≤
              θ1 * phiTypeI Pm φ (convComb h l1) + θ2 * phiTypeI Pm φ (convComb h l2) := by
            unfold phiTypeI
            rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _) (i2.const_mul _)]
            refine integral_mono i0 ((i1.const_mul _).add (i2.const_mul _)) fun x => ?_
            simp only [hcc]
            have := hφ.2.2.2.1.2 (ga_range h hh hl1 x) (ga_range h hh hl2 x) h1 h2 hs
            simpa [smul_eq_mul] using this
          have := mul_le_mul_of_nonneg_left hf1 h1
          have := mul_le_mul_of_nonneg_left hf2 h2
          linarith
        have hII : phiTypeII Pp φ (convComb h (θ1 • l1 + θ2 • l2)) ≤
            θ1 * phiTypeII Pp φ (convComb h l1) + θ2 * phiTypeII Pp φ (convComb h l2) := by
          unfold phiTypeII
          rw [← integral_const_mul, ← integral_const_mul, ← integral_add (j1.const_mul _) (j2.const_mul _)]
          refine integral_mono j0 ((j1.const_mul _).add (j2.const_mul _)) fun x => ?_
          simp only [hcc]
          have := hφ.2.2.2.1.2 (hneg hl1 x) (hneg hl2 x) h1 h2 hs
          rw [show -(θ1 * convComb h l1 x + θ2 * convComb h l2 x) =
            θ1 • (-convComb h l1 x) + θ2 • (-convComb h l2 x) by simp [smul_eq_mul]; ring]
          simpa [smul_eq_mul] using this
        exact (csInf_le (ga_bdd h hh Pm Pp φ hφ _) ⟨_, ⟨⟨_, hl, rfl⟩, hI⟩, rfl⟩).trans hII
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      have hε2 : 0 < ε / 2 := half_pos hε
      obtain ⟨_, ⟨f1, hf1, rfl⟩, hlt1⟩ := exists_lt_of_csInf_lt (ha.2.image _)
        (lt_add_of_pos_right (minPhiTypeII h Pm Pp φ a) hε2)
      obtain ⟨_, ⟨f2, hf2, rfl⟩, hlt2⟩ := exists_lt_of_csInf_lt (hb.2.image _)
        (lt_add_of_pos_right (minPhiTypeII h Pm Pp φ b) hε2)
      have := key f1 hf1 f2 hf2
      have e1 := mul_le_mul_of_nonneg_left hlt1.le h1
      have e2 := mul_le_mul_of_nonneg_left hlt2.le h2
      have : θ1 * (minPhiTypeII h Pm Pp φ a + ε / 2) + θ2 * (minPhiTypeII h Pm Pp φ b + ε / 2) =
        θ1 * minPhiTypeII h Pm Pp φ a + θ2 * minPhiTypeII h Pm Pp φ b + ε / 2 := by
        linear_combination (ε / 2) * hs
      linarith
