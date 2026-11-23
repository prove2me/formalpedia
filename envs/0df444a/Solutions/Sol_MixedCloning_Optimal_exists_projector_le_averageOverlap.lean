-- Prove2me | solution 1 for MixedCloning.Optimal.exists_projector_le_averageOverlap
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:37:34.543802+00:00
-- url     : https://prove2.me/submissions/a6c14b3f-0443-4e5b-b89a-0284185e6136

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MixedCloning.Optimal

private lemma unitary_det_isUnit {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsUnit (U : Op (Fin d)).det := by
  have hUU : (U : Op (Fin d)) * (U : Op (Fin d))ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.property
  have h := congrArg Matrix.det hUU
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  exact ⟨⟨(U : Op (Fin d)).det, star (U : Op (Fin d)).det, h, by simpa [mul_comm] using h⟩, rfl⟩

private lemma baseProjector_isProjector (d r : ℕ) (hrd : r ≤ d) :
    IsProjector r (baseProjector d r) := by
  have hherm : (baseProjector d r).IsHermitian := by
    rw [baseProjector, Matrix.isHermitian_diagonal_iff]
    intro i
    simp only [IsSelfAdjoint]
    split_ifs <;> simp
  have hsq : baseProjector d r * baseProjector d r = baseProjector d r := by
    unfold baseProjector
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp_all
  have hrank : (baseProjector d r).rank = r := by
    rw [baseProjector, Matrix.rank_diagonal]
    let e : Fin r ≃ {i : Fin d // (if d-r ≤ i.val then (1 : ℂ) else 0) ≠ 0} :=
      { toFun := fun j => (⟨⟨d-r+j.val, by omega⟩, by simp⟩ :
          {i : Fin d // (if d-r ≤ i.val then (1 : ℂ) else 0) ≠ 0})
        invFun := fun (i : {i : Fin d // (if d-r ≤ i.val then (1 : ℂ) else 0) ≠ 0}) =>
          (⟨i.val.val-(d-r), by
            have hi : d-r ≤ i.val.val := by simpa using i.property
            omega⟩ : Fin r)
        left_inv := by intro j; ext; simp
        right_inv := by
          intro i
          apply Subtype.ext
          apply Fin.ext
          have hi : d-r ≤ i.val.val := by simpa using i.property
          simp only
          omega }
    rw [← Fintype.card_congr e, Fintype.card_fin]
  exact ⟨hherm, hsq, hrank⟩

private lemma rotatedProjector_isProjector (d r : ℕ) (hrd : r ≤ d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : IsProjector r (rotatedProjector r U) := by
  obtain ⟨hherm, hsq, hrank⟩ := baseProjector_isProjector d r hrd
  have hUU : (U : Op (Fin d))ᴴ * (U : Op (Fin d)) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp U.property
  have hdet : IsUnit (U : Op (Fin d)).det := unitary_det_isUnit U
  have hdetH : IsUnit (U : Op (Fin d))ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact IsUnit.star hdet
  refine ⟨?_, ?_, ?_⟩
  · change ((U : Op (Fin d)) * baseProjector d r * (U : Op (Fin d))ᴴ)ᴴ =
      (U : Op (Fin d)) * baseProjector d r * (U : Op (Fin d))ᴴ
    simp [Matrix.conjTranspose_mul, hherm.eq, Matrix.mul_assoc]
  · change ((U : Op (Fin d)) * baseProjector d r * (U : Op (Fin d))ᴴ) *
      ((U : Op (Fin d)) * baseProjector d r * (U : Op (Fin d))ᴴ) =
        (U : Op (Fin d)) * baseProjector d r * (U : Op (Fin d))ᴴ
    calc
      _ = (U : Op (Fin d)) * baseProjector d r * ((U : Op (Fin d))ᴴ * (U : Op (Fin d))) *
          baseProjector d r * (U : Op (Fin d))ᴴ := by noncomm_ring
      _ = (U : Op (Fin d)) * (baseProjector d r * baseProjector d r) * (U : Op (Fin d))ᴴ := by
        rw [hUU]; noncomm_ring
      _ = _ := by rw [hsq]
  · change ((U : Op (Fin d)) * baseProjector d r * (U : Op (Fin d))ᴴ).rank = r
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdetH,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet, hrank]

private lemma continuous_overlap (d r n m : ℕ) (C : Cloner d n m)
    (hC : QAlgorithms.IsChannel C) :
    Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      overlap d r n m C (rotatedProjector r U)) := by
  obtain ⟨s, E, hE, hCE⟩ := hC
  unfold overlap
  simp_rw [hCE]
  unfold QAlgorithms.krausApply projectorState tensorPower rotatedProjector baseProjector
  fun_prop

private lemma exists_projector_le_averageOverlap_aux (d r n m : ℕ) (hrd : r ≤ d)
    (C : Cloner d n m) (hC : QAlgorithms.IsChannel C) :
    ∃ P : Op (Fin d), IsProjector r P ∧ overlap d r n m C P ≤ averageOverlap d r n m C := by
  have hcont := continuous_overlap d r n m C hC
  have hint : Integrable (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      overlap d r n m C (rotatedProjector r U)) (haar d) :=
    integrableOn_univ.mp (ContinuousOn.integrableOn_compact isCompact_univ hcont.continuousOn)
  obtain ⟨U, -, hU⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hcont.continuousOn
  rw [isMinOn_univ_iff] at hU
  refine ⟨rotatedProjector r U, rotatedProjector_isProjector d r hrd U, ?_⟩
  calc
    overlap d r n m C (rotatedProjector r U) =
        ∫ _V : Matrix.unitaryGroup (Fin d) ℂ,
          overlap d r n m C (rotatedProjector r U) ∂haar d := by simp
    _ ≤ ∫ V, overlap d r n m C (rotatedProjector r V) ∂haar d :=
      integral_mono (integrable_const _) hint hU
    _ = averageOverlap d r n m C := rfl

end MixedCloning.Optimal

theorem solution (d r n m : ℕ) (hrd : r ≤ d)
    (C : MixedCloning.Optimal.Cloner d n m) (hC : QAlgorithms.IsChannel C) :
    ∃ P : MixedCloning.Optimal.Op (Fin d), MixedCloning.Optimal.IsProjector r P ∧
      MixedCloning.Optimal.overlap d r n m C P ≤ MixedCloning.Optimal.averageOverlap d r n m C := by
  exact MixedCloning.Optimal.exists_projector_le_averageOverlap_aux d r n m hrd C hC
