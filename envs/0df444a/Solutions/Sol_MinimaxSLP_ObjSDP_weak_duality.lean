-- Prove2me | solution 1 for MinimaxSLP.ObjSDP.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:48:24.626883+00:00
-- url     : https://prove2.me/submissions/034b5b3e-5de4-4bc4-b19e-4cab3a55fbe2

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model
import Theorems.Thm_MinimaxSLP_ObjSDP_recourseSet_bounded

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP.WDAux

lemma recourseSet_isClosed {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (x : Fin n → ℝ) : IsClosed (recourseSet W T h x) := by
  have : recourseSet W T h x = {w | W *ᵥ w = h - T *ᵥ x} ∩ {w | 0 ≤ w} := rfl
  rw [this]
  exact IsClosed.inter (isClosed_eq (Continuous.matrix_mulVec continuous_const continuous_id)
    continuous_const) (isClosed_le continuous_const continuous_id)

/-- `𝒬(q, x) = q′w_q` for a minimiser `w_q ∈ X(x)`. -/
lemma Qval_attained {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) (q : Fin d → ℝ) :
    ∃ wq ∈ recourseSet W T h x, Qval W T h q x = q ⬝ᵥ wq := by
  have hK : IsCompact (recourseSet W T h x) := Metric.isCompact_of_isClosed_isBounded
    (recourseSet_isClosed W T h x) (recourseSet_bounded W T h hA3 x).1
  have hcont : ContinuousOn (fun w : Fin d → ℝ => q ⬝ᵥ w) (recourseSet W T h x) :=
    (Continuous.dotProduct continuous_const continuous_id).continuousOn
  obtain ⟨wq, hwq, hmin⟩ := hK.exists_isMinOn hrec hcont
  have hleast : IsLeast ((fun w => q ⬝ᵥ w) '' recourseSet W T h x) (q ⬝ᵥ wq) :=
    ⟨⟨wq, hwq, rfl⟩, by rintro _ ⟨w, hw, rfl⟩; exact hmin hw⟩
  exact ⟨wq, hwq, hleast.csInf_eq⟩

lemma Qval_continuous {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q) (x : Fin n → ℝ) :
    Continuous fun q => Qval W T h q x := by
  have hK : IsCompact (recourseSet W T h x) := Metric.isCompact_of_isClosed_isBounded
    (recourseSet_isClosed W T h x) (recourseSet_bounded W T h hA3 x).1
  exact hK.continuous_sInf (f := fun q w => q ⬝ᵥ w)
    (Continuous.dotProduct continuous_fst continuous_snd)

end MinimaxSLP.ObjSDP.WDAux

open MinimaxSLP.ObjSDP MinimaxSLP.ObjSDP.WDAux in
theorem solution {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    ∀ v ∈ primalValues W T h α β μ Q x, ∀ u ∈ dualValues6 W T h α β μ Q x, v ≤ u := by
  rintro _ ⟨P, ⟨⟨hprob, hL2⟩, hmean, hsec⟩, rfl⟩ _ ⟨⟨Y, y, y0⟩, ⟨-, hfeas⟩, rfl⟩
  -- integrability of the coordinates and of their products
  have hint1 : ∀ i, Integrable (fun ξ : Fin d → ℝ => ξ i) P := fun i =>
    (hL2 i).integrable (by norm_num)
  have hint2 : ∀ i j, Integrable (fun ξ : Fin d → ℝ => ξ i * ξ j) P := fun i j =>
    (hL2 i).integrable_mul (hL2 j)
  set φ : (Fin d → ℝ) → ℝ := fun q => q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y0 with hφ
  have hφexp : ∀ q : Fin d → ℝ,
      φ q = ∑ i, ∑ j, Y i j * (q i * q j) + ∑ i, y i * q i + y0 := by
    intro q
    simp only [hφ, dotProduct, mulVec, Finset.mul_sum]
    congr 1; congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
    · refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hφint : Integrable φ P := by
    have : φ = fun q => ∑ i, ∑ j, Y i j * (q i * q j) + ∑ i, y i * q i + y0 := funext hφexp
    rw [this]
    refine ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint2 i j).const_mul _).add (integrable_finsetSum _ fun i _ =>
      (hint1 i).const_mul _)).add (integrable_const _)
  have hφval : ∫ q, φ q ∂P = frob Q Y + μ ⬝ᵥ y + y0 := by
    simp_rw [hφexp]
    rw [integral_add, integral_add, integral_finsetSum, integral_finsetSum, integral_const]
    · simp only [probReal_univ, one_smul, smul_eq_mul, one_mul]
      congr 1; congr 1
      · simp only [frob]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => (hint2 i j).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        have : Q i j = ∫ ξ, ξ i * ξ j ∂P := by
          rw [← hsec]; simp [MomentDRO.Conf.secondMomentAbout]
        rw [this]; ring
      · simp only [dotProduct]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul]
        have : μ i = ∫ ξ, ξ i ∂P := by rw [← hmean]; rfl
        rw [this]; ring
    · exact fun i _ => (hint1 i).const_mul _
    · exact fun i _ => integrable_finsetSum _ fun j _ => (hint2 i j).const_mul _
    · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hint2 i j).const_mul _
    · exact integrable_finsetSum _ fun i _ => (hint1 i).const_mul _
    · exact (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hint2 i j).const_mul _).add (integrable_finsetSum _ fun i _ => (hint1 i).const_mul _)
    · exact integrable_const _
  -- the disutility of the recourse value is continuous and bounded below by an integrable function
  set f : (Fin d → ℝ) → ℝ := fun q => disutility α β (Qval W T h q x) with hf
  have hfcont : Continuous f := by
    simp only [hf, disutility]
    have hQ := Qval_continuous W T h hA3 x
    exact Continuous.finset_sup'_apply Finset.univ_nonempty fun k _ =>
      (continuous_const.mul hQ).add continuous_const
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (recourseSet_bounded W T h hA3 x).1
  set k0 : Fin K := 0
  set ℓ : (Fin d → ℝ) → ℝ := fun q => -(α k0 * (R * ∑ i, |q i|)) + β k0 with hℓ
  have hℓint : Integrable ℓ P :=
    ((integrable_finsetSum _ fun i _ => (hint1 i).abs).const_mul R |>.const_mul (α k0)).neg.add
      (integrable_const _)
  have hℓf : ∀ q, ℓ q ≤ f q := by
    intro q
    obtain ⟨wq, hwq, hQ⟩ := Qval_attained W T h hA3 x hrec q
    have h1 : α k0 * Qval W T h q x + β k0 ≤ f q :=
      Finset.le_sup' (fun k => α k * Qval W T h q x + β k) (Finset.mem_univ k0)
    have h2 : -(R * ∑ i, |q i|) ≤ Qval W T h q x := by
      rw [hQ, dotProduct, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hi : |wq i| ≤ R := le_trans (by simpa using norm_le_pi_norm wq i) (hR wq hwq)
      have h3 : |q i * wq i| ≤ R * |q i| := by
        rw [abs_mul, mul_comm R]; exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
      linarith [neg_abs_le (q i * wq i)]
    have h4 := mul_le_mul_of_nonneg_left h2 (hα k0)
    simp only [hℓ]
    linarith
  have hfφ : ∀ q, f q ≤ φ q := fun q => hfeas q
  have hfint : Integrable f P := by
    refine Integrable.mono' (hℓint.abs.add hφint.abs) hfcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_le]; simp only [Pi.add_apply]
    constructor
    · linarith [hℓf q, neg_abs_le (ℓ q), abs_nonneg (φ q)]
    · linarith [hfφ q, le_abs_self (φ q), abs_nonneg (ℓ q)]
  calc ∫ q, disutility α β (Qval W T h q x) ∂P = ∫ q, f q ∂P := rfl
    _ ≤ ∫ q, φ q ∂P := integral_mono hfint hφint hfφ
    _ = frob Q Y + μ ⬝ᵥ y + y0 := hφval
