-- Prove2me | solution 1 for MinimaxSLP.ObjExtremal.jensen_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:46:13.378392+00:00
-- url     : https://prove2.me/submissions/dbab7e54-c6f2-4ed2-8b58-124991ddf66c

import Mathlib
import Definitions.Def_MinimaxSLP_ObjExtremal_Model
import Theorems.Thm_MinimaxSLP_ObjExtremal_Qval_homogeneous_superadditive

open MeasureTheory Matrix

namespace MSLP2Jensen
open MinimaxSLP.ObjSDP MinimaxSLP.ObjExtremal

theorem jensen_main {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty)
    (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (hint : ∀ i : Fin d, Integrable (fun ρ : Fin d → ℝ => ρ i) P) :
    Integrable (fun ρ => Qval W T h ρ x) P ∧
    ∫ ρ, Qval W T h ρ x ∂P ≤ Qval W T h (fun i => ∫ ρ, ρ i ∂P) x ∧
    Qval W T h 0 x = 0 := by
  obtain ⟨hhom, hsup⟩ := Qval_homogeneous_superadditive W T h hA3 x hrec
  set Qv : (Fin d → ℝ) → ℝ := fun q => Qval W T h q x with hQv
  have hQv0 : Qv 0 = 0 := by
    have := hhom 2 (by norm_num) 0
    simp only [smul_zero] at this
    show Qval W T h 0 x = 0
    linarith
  -- concavity and continuity
  have hconc : ConcaveOn ℝ Set.univ Qv := by
    refine ⟨convex_univ, fun a _ b _ l m hl hm hlm => ?_⟩
    rcases hl.lt_or_eq with hl | hl
    · rcases hm.lt_or_eq with hm | hm
      · have := hsup (l • a) (m • b)
        show l • Qval W T h a x + m • Qval W T h b x ≤ Qval W T h (l • a + m • b) x
        rw [hhom l hl, hhom m hm] at this
        simpa [smul_eq_mul] using this
      · subst hm
        have : l = 1 := by linarith
        subst this; simp
    · subst hl
      have : m = 1 := by linarith
      subst this; simp
  have hcont : Continuous Qv := by
    have := hconc.continuousOn isOpen_univ
    exact continuousOn_univ.mp this
  -- linear bounds
  obtain ⟨w0, hw0⟩ := hrec
  have hup : ∀ ρ, Qv ρ ≤ ρ ⬝ᵥ w0 := by
    intro ρ
    obtain ⟨π, hπ⟩ := hA3 ρ
    apply csInf_le
    · refine ⟨(h - T *ᵥ x) ⬝ᵥ π, ?_⟩
      rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
      have e1 : (h - T *ᵥ x) ⬝ᵥ π = (Wᵀ *ᵥ π) ⬝ᵥ w := by
        rw [← hw1, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      rw [e1]
      exact dotProduct_le_dotProduct_of_nonneg_right hπ hw2
    · exact ⟨w0, hw0, rfl⟩
  have hsupsum : ∀ (s : Finset (Fin d)) (f : Fin d → Fin d → ℝ),
      ∑ i ∈ s, Qv (f i) ≤ Qv (∑ i ∈ s, f i) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [hQv0]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have := hsup (f a) (∑ i ∈ s, f i)
      show Qv (f a) + ∑ i ∈ s, Qv (f i) ≤ Qv (f a + ∑ i ∈ s, f i)
      have : Qv (f a) + Qv (∑ i ∈ s, f i) ≤ Qv (f a + ∑ i ∈ s, f i) := this
      linarith
  set e : Fin d → Fin d → ℝ := fun i => Pi.single i 1 with he
  set C : Fin d → ℝ := fun i => |w0 i| + |Qv (e i)| + |Qv (-e i)| with hC
  have hscal : ∀ (t : ℝ) (u : Fin d → ℝ), -(|t| * (|Qv u| + |Qv (-u)|)) ≤ Qv (t • u) := by
    intro t u
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have : t • u = (-t) • (-u) := by rw [neg_smul_neg]
      rw [this]
      show _ ≤ Qval W T h ((-t) • -u) x
      rw [hhom (-t) (by linarith)]
      rw [abs_of_neg ht]
      have := neg_abs_le (Qv (-u))
      have := abs_nonneg (Qv u)
      show _ ≤ -t * Qv (-u)
      nlinarith
    · subst ht; simp [hQv0]
    · show _ ≤ Qval W T h (t • u) x
      rw [hhom t ht, abs_of_pos ht]
      have := neg_abs_le (Qv u)
      have := abs_nonneg (Qv (-u))
      show _ ≤ t * Qv u
      nlinarith
  have hlow : ∀ ρ, -(∑ i, |ρ i| * (|Qv (e i)| + |Qv (-e i)|)) ≤ Qv ρ := by
    intro ρ
    have hρ : ρ = ∑ i, ρ i • e i := by
      rw [he]; exact pi_eq_sum_univ' ρ
    have h1 := hsupsum Finset.univ (fun i => ρ i • e i)
    rw [← hρ] at h1
    refine le_trans ?_ h1
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hscal (ρ i) (e i)
  have hbound : ∀ ρ, ‖Qv ρ‖ ≤ ∑ i, |ρ i| * C i := by
    intro ρ
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · refine le_trans ?_ (hlow ρ)
      rw [neg_le_neg_iff]
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      simp only [hC]; linarith [abs_nonneg (w0 i)]
    · refine (hup ρ).trans ?_
      simp only [dotProduct]
      refine Finset.sum_le_sum fun i _ => ?_
      calc ρ i * w0 i ≤ |ρ i| * |w0 i| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ |ρ i| * C i := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          simp only [hC]; linarith [abs_nonneg (Qv (e i)), abs_nonneg (Qv (-e i))]
  have hQint : Integrable Qv P := by
    refine Integrable.mono' (g := fun ρ => ∑ i, |ρ i| * C i) ?_ hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
    exact integrable_finsetSum _ fun i _ => (hint i).abs.mul_const _
  refine ⟨hQint, ?_, hQv0⟩
  have hid : Integrable (fun ρ : Fin d → ℝ => ρ) P := Integrable.of_eval hint
  have hJ := hconc.le_map_integral hcont.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hid hQint
  have hmean : (∫ ρ, ρ ∂P) = fun i => ∫ ρ, ρ i ∂P := by
    funext i; exact eval_integral hint i
  rw [hmean] at hJ
  exact hJ

end MSLP2Jensen

theorem solution {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (hint : ∀ i : Fin d, Integrable (fun ρ : Fin d → ℝ => ρ i) P) :
    Integrable (fun ρ => MinimaxSLP.ObjSDP.Qval W T h ρ x) P ∧
    ∫ ρ, MinimaxSLP.ObjSDP.Qval W T h ρ x ∂P ≤ MinimaxSLP.ObjSDP.Qval W T h (fun i => ∫ ρ, ρ i ∂P) x ∧
    MinimaxSLP.ObjSDP.Qval W T h 0 x = 0 :=
  MSLP2Jensen.jensen_main W T h hA3 x hrec P hint
