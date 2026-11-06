-- Prove2me | solution 1 for MinimaxSLP.ObjSDP.dual6_eq_dual8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:40:45.014668+00:00
-- url     : https://prove2.me/submissions/3c0710eb-81ef-4a48-8c3a-d20205ea95ef

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model
import Theorems.Thm_MinimaxSLP_ObjSDP_constraint_iff
import Theorems.Thm_WorstCaseVaR_KnownMoments_quadratic_form_nonneg_iff_posSemidef

open MeasureTheory Matrix

namespace MinimaxSLP.ObjSDP.D68Aux

/-- The quadratic function of the LMI block: `[q;1]′ M [q;1] = q′Yq + q′y + y₀ − a q′w − b`. -/
lemma quadFn_lmiBlock {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) (y0 a b : ℝ)
    (w q : Fin d → ℝ) :
    WorstCaseVaR.KnownMoments.quadFn (lmiBlock Y y y0 a b w) q =
      q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y0 - a * (q ⬝ᵥ w) - b := by
  simp only [WorstCaseVaR.KnownMoments.quadFn, WorstCaseVaR.KnownMoments.liftVec, dotProduct,
    mulVec, Fintype.sum_sum_type, lmiBlock, bordered, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    mul_one, one_mul]
  have e4 : ∑ i, q i * (∑ j, Y i j * q j + 1 / 2 * (y i - a * w i)) =
      ∑ i, q i * ∑ j, Y i j * q j + ∑ i, q i * (1 / 2 * (y i - a * w i)) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have e2 : ∑ i, q i * (1 / 2 * (y i - a * w i)) =
      (1 / 2) * (∑ i, q i * y i) - (1 / 2) * a * ∑ i, q i * w i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have e3 : ∑ j, 1 / 2 * (y j - a * w j) * q j =
      (1 / 2) * (∑ i, q i * y i) - (1 / 2) * a * ∑ i, q i * w i := by
    rw [← e2]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [e4, e2, e3]
  have e5 : ∑ i, q i * ∑ j, Y i j * q j = ∑ i, q i * ∑ j, Y i j * q j := rfl
  ring

lemma lmiBlock_isSymm {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.IsSymm) (y : Fin d → ℝ)
    (y0 a b : ℝ) (w : Fin d → ℝ) : (lmiBlock Y y y0 a b w).IsSymm := by
  unfold lmiBlock bordered
  refine IsSymm.fromBlocks hY ?_ ?_
  · ext i j; simp
  · ext i j; simp

lemma isSymm_of_lmi {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ)
    (y0 a b : ℝ) (w : Fin d → ℝ) (hM : (lmiBlock Y y y0 a b w).PosSemidef) : Y.IsSymm := by
  have h1 := hM.isHermitian.submatrix (Sum.inl : Fin d → Fin d ⊕ Fin 1)
  have e : (lmiBlock Y y y0 a b w).submatrix Sum.inl Sum.inl = Y := by
    ext i j; simp [lmiBlock, bordered]
  rw [e] at h1
  unfold IsHermitian at h1
  rw [conjTranspose_eq_transpose_of_trivial] at h1
  exact h1

/-- The LMI block is PSD iff its quadratic function is nonnegative (for symmetric `Y`). -/
lemma lmi_iff {d : ℕ} (Y : Matrix (Fin d) (Fin d) ℝ) (hY : Y.IsSymm) (y : Fin d → ℝ)
    (y0 a b : ℝ) (w : Fin d → ℝ) :
    (lmiBlock Y y y0 a b w).PosSemidef ↔
      ∀ q : Fin d → ℝ, 0 ≤ q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y0 - a * (q ⬝ᵥ w) - b := by
  rw [← WorstCaseVaR.KnownMoments.quadratic_form_nonneg_iff_posSemidef _
    (lmiBlock_isSymm Y hY y y0 a b w)]
  constructor
  · intro H q
    have := H (WithLp.toLp 2 q)
    rwa [quadFn_lmiBlock] at this
  · intro H q
    rw [quadFn_lmiBlock]
    exact H _

end MinimaxSLP.ObjSDP.D68Aux

open MinimaxSLP.ObjSDP MinimaxSLP.ObjSDP.D68Aux in
theorem solution {n r d K : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (α β : Fin K → ℝ) (hα : ∀ k, 0 ≤ α k)
    (μ : Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (recourseSet W T h x).Nonempty) :
    dualValues6 W T h α β μ Q x = dualValues8 W T h α β μ Q x ∧
      ZD W T h α β μ Q x = ZD8 W T h α β μ Q x := by
  have key : dualValues6 W T h α β μ Q x = dualValues8 W T h α β μ Q x := by
    ext t
    constructor
    · rintro ⟨⟨Y, y, y0⟩, ⟨hY, hC⟩, rfl⟩
      have hk : ∀ k : Fin K, ∃ w ∈ recourseSet W T h x, ∀ q : Fin d → ℝ,
          0 ≤ q ⬝ᵥ (Y *ᵥ q) + q ⬝ᵥ y + y0 - α k * (q ⬝ᵥ w) - β k := by
        intro k
        refine (constraint_iff W T h α β k (hα k) hA3 x hrec Y hY y y0).1 fun q => ?_
        refine le_trans ?_ (hC q)
        exact Finset.le_sup' (fun k => α k * Qval W T h q x + β k) (Finset.mem_univ k)
      choose w hw hwq using hk
      refine ⟨⟨Y, y, y0, w⟩, fun k => ⟨(lmi_iff Y hY y y0 _ _ _).2 (hwq k), ?_, (hw k).2⟩, rfl⟩
      have := (hw k).1
      simp only
      rw [this]; abel
    · rintro ⟨⟨Y, y, y0, w⟩, hF, rfl⟩
      have hY : Y.IsSymm := by
        haveI : Nonempty (Fin K) := ⟨0⟩
        exact isSymm_of_lmi Y y y0 _ _ _ (hF 0).1
      refine ⟨⟨Y, y, y0⟩, ⟨hY, fun q => ?_⟩, rfl⟩
      simp only [disutility]
      refine Finset.sup'_le _ _ fun k _ => ?_
      obtain ⟨hM, hWw, hw0⟩ := hF k
      have hmem : w k ∈ recourseSet W T h x := ⟨by rw [← hWw]; abel, hw0⟩
      exact (constraint_iff W T h α β k (hα k) hA3 x hrec Y hY y y0).2
        ⟨w k, hmem, (lmi_iff Y hY y y0 _ _ _).1 hM⟩ q
  refine ⟨key, ?_⟩
  unfold ZD ZD8
  rw [key]
