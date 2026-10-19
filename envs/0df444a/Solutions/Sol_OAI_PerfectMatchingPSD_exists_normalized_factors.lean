-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.exists_normalized_factors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:48:07.814786+00:00
-- url     : https://prove2.me/submissions/95fa800d-d2ae-4663-b9a0-f64c471246a5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/DeterminantNormalization.lean:L133-L185
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.exists_normalized_factors. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages

-- ---- from OAI.Combinatorics.MatchingPSD.DeterminantNormalization ----
namespace OAI

universe u_1 u_2 u_3

namespace PerfectMatchingPSD
open Matrix Set
variable {R : Type u_1} {I : Type u_2} {J : Type u_3} [Fintype R] [DecidableEq R]

omit [Fintype R] [DecidableEq R] in
lemma convex_posSemidef : Convex ℝ {A : Matrix R R ℝ | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

lemma hasDerivAt_det_one_add (A : Matrix R R ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  let p : Polynomial ℝ := (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C).det
  have h := p.hasDerivAt 0
  rw [show p.derivative.eval 0 = A.trace from Matrix.derivative_det_one_add_X_smul A] at h
  have he : (fun t : ℝ => (1 + t • A).det) = (fun t => p.eval t) := by
    funext t
    change _ = (Polynomial.evalRingHom t) p
    rw [RingHom.map_det]
    congr 1
    ext i j
    change (if i = j then 1 else 0) + t * A i j =
      Polynomial.eval t ((if i = j then 1 else 0) +
        Polynomial.X * Polynomial.C (A i j))
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    split_ifs <;> simp only [Polynomial.eval_one, Polynomial.eval_zero]
  rwa [he]

lemma hasDerivAt_det_add (D E : Matrix R R ℝ) (hD : IsUnit D) :
    HasDerivAt (fun t : ℝ => (D + t • E).det)
      (D.det * (D⁻¹ * E).trace) 0 := by
  have h := (hasDerivAt_det_one_add (D⁻¹ * E)).const_mul D.det
  have he : (fun t : ℝ => (D + t • E).det) =
      (fun t => D.det * (1 + t • (D⁻¹ * E)).det) := by
    funext t
    rw [← Matrix.det_mul]
    congr 1
    rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc,
      Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det D).mp hD), one_mul]
  rwa [he]

lemma derivative_nonpos_at_right_max {f : ℝ → ℝ} {c : ℝ}
    (h : HasDerivAt f c 0) (hm : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ f 0) : c ≤ 0 := by
  have he : IsLocalMaxOn f (Set.Icc (0 : ℝ) 1) 0 :=
    (show IsMaxOn f (Set.Icc (0 : ℝ) 1) 0 from hm).localize
  have ht : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    simp [segment_eq_Icc]
  simpa using he.hasFDerivWithinAt_nonpos h.hasFDerivAt.hasFDerivWithinAt ht

lemma trace_inv_mul_le_of_det_max (D B : Matrix R R ℝ) (hD : D.PosDef)
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) 1, (D + t • (B - D)).det ≤ D.det) :
    (D⁻¹ * B).trace ≤ (Fintype.card R : ℝ) := by
  have hd : 0 < D.det := hD.det_pos
  have he := derivative_nonpos_at_right_max (hasDerivAt_det_add D (B - D) hD.isUnit)
    (by simpa using hm)
  have ht : (D⁻¹ * (B - D)).trace ≤ 0 := by nlinarith
  rw [mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul D ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit), Matrix.trace_one] at ht
  linarith

lemma exists_regularized_det_max [Fintype I] [Nonempty I]
    (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Matrix R R ℝ, D.PosDef ∧
      D ∈ (fun A => ε • (1 : Matrix R R ℝ) + A) '' convexHull ℝ (Set.range B) ∧
      ∀ i, (D⁻¹ * B i).trace ≤ (Fintype.card R : ℝ) := by
  let S := convexHull ℝ (Set.range B)
  let f : Matrix R R ℝ → Matrix R R ℝ := fun A => ε • (1 : Matrix R R ℝ) + A
  have hc : IsCompact S := (Set.finite_range B).isCompact_convexHull ℝ
  have hn : S.Nonempty := (Set.range_nonempty B).mono (subset_convexHull ℝ _)
  have hf : Continuous f := by fun_prop
  have hp : ∀ A ∈ S, A.PosSemidef :=
    convexHull_min (Set.range_subset_iff.mpr hB) convex_posSemidef
  have hpd : ∀ D ∈ f '' S, D.PosDef := by
    rintro _ ⟨A, hA, rfl⟩
    exact (Matrix.PosDef.one.smul hε).add_posSemidef (hp A hA)
  obtain ⟨D, hDs, hmax⟩ := (hc.image hf).exists_isMaxOn (hn.image f)
    (by fun_prop : ContinuousOn Matrix.det (f '' S))
  refine ⟨D, hpd D hDs, hDs, ?_⟩
  intro i
  have hi : f (B i) ∈ f '' S := ⟨B i, subset_convexHull ℝ _ (Set.mem_range_self i), rfl⟩
  have hs : Convex ℝ (f '' S) := by
    exact (convex_convexHull ℝ (Set.range B)).translate (ε • (1 : Matrix R R ℝ))
  have hm := trace_inv_mul_le_of_det_max D (f (B i)) (hpd D hDs) (by
    intro t ht
    apply hmax
    have he : D + t • (f (B i) - D) = (1 - t) • D + t • f (B i) := by module
    rw [he]
    exact hs hDs hi (sub_nonneg.mpr ht.2) ht.1 (by ring))
  have htr : 0 ≤ (D⁻¹).trace := (hpd D hDs).inv.posSemidef.trace_nonneg
  have he : (D⁻¹ * f (B i)).trace = ε * (D⁻¹).trace + (D⁻¹ * B i).trace := by
    simp [f, mul_add, Matrix.trace_add, Matrix.trace_smul]
  rw [he] at hm
  nlinarith

open scoped MatrixOrder

lemma trace_mul_convexHull_le [Fintype I] (A : Matrix R R ℝ)
    (B : I → Matrix R R ℝ) (m : ℝ) (hB : ∀ i, (A * B i).trace ≤ m)
    {D : Matrix R R ℝ} (hD : D ∈ convexHull ℝ (Set.range B)) :
    (A * D).trace ≤ m := by
  have hc : Convex ℝ {D : Matrix R R ℝ | (A * D).trace ≤ m} := by
    intro X hX Y hY a b ha hb hab
    change (A * (a • X + b • Y)).trace ≤ m
    rw [mul_add, mul_smul_comm, mul_smul_comm, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul]
    change a * (A * X).trace + b * (A * Y).trace ≤ m
    calc
      _ ≤ a * m + b * m := add_le_add
        (mul_le_mul_of_nonneg_left hX ha) (mul_le_mul_of_nonneg_left hY hb)
      _ = m := by rw [← add_mul, hab, one_mul]
  exact convexHull_min (Set.range_subset_iff.mpr hB) hc hD

lemma exists_normalized_factors [Fintype I] [Nonempty I] [Fintype J]
    (A : J → Matrix R R ℝ) (B : I → Matrix R R ℝ)
    (hA : ∀ j, (A j).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    (m : ℝ) (hpair : ∀ j i, (A j * B i).trace ≤ m) :
    ∃ (A' : J → Matrix R R ℝ) (B' : I → Matrix R R ℝ),
      (∀ j, (A' j).PosSemidef) ∧ (∀ i, (B' i).PosSemidef) ∧
      (∀ j i, (A' j * B' i).trace = (A j * B i).trace) ∧
      (∀ j, (A' j).trace ≤ m + 1) ∧
      (∀ i, (B' i).trace ≤ (Fintype.card R : ℝ)) := by
  classical
  let S : ℝ := ∑ j, (A j).trace
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => (hA j).trace_nonneg)
  let ε : ℝ := 1 / (1 + S)
  have hε : 0 < ε := one_div_pos.mpr (by linarith)
  have hεA (j : J) : ε * (A j).trace ≤ 1 := by
    have hj : (A j).trace ≤ S := Finset.single_le_sum
      (fun j _ => (hA j).trace_nonneg) (Finset.mem_univ j)
    change 1 / (1 + S) * (A j).trace ≤ 1
    rw [one_div_mul_eq_div]
    exact (div_le_one (by linarith : 0 < 1 + S)).mpr (by linarith)
  obtain ⟨D, hD, ⟨D₀, hD₀, hDeq⟩, htr⟩ := exists_regularized_det_max B hB ε hε
  let G := CFC.sqrt D
  have hG : G.PosSemidef := (CFC.sqrt_nonneg D).posSemidef
  have hGG : G * G = D := CFC.sqrt_mul_sqrt_self D hD.posSemidef.nonneg
  have huG : IsUnit G := (IsUnit.mul_iff.mp (hGG ▸ hD.isUnit)).1
  have hunit := (Matrix.isUnit_iff_isUnit_det G).mp huG
  have hGinv : G⁻¹.PosSemidef := hG.inv
  have hleft : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hunit
  have hright : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hunit
  have hinv : G⁻¹ * G⁻¹ = D⁻¹ := by
    rw [← hGG, Matrix.mul_inv_rev]
  refine ⟨fun j => G * A j * G, fun i => G⁻¹ * B i * G⁻¹,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa only [hG.isHermitian.eq] using (hA j).conjTranspose_mul_mul_same G
  · intro i
    simpa only [hGinv.isHermitian.eq] using (hB i).conjTranspose_mul_mul_same G⁻¹
  · intro j i
    change (G * A j * G * (G⁻¹ * B i * G⁻¹)).trace = _
    have he : G * A j * G * (G⁻¹ * B i * G⁻¹) = G * (A j * B i) * G⁻¹ := by
      calc
        _ = G * A j * (G * G⁻¹) * B i * G⁻¹ := by simp only [mul_assoc]
        _ = _ := by rw [hright, mul_one]; simp only [mul_assoc]
    rw [he, Matrix.trace_mul_cycle, hleft, one_mul]
  · intro j
    rw [Matrix.trace_mul_cycle, hGG, Matrix.trace_mul_comm, ← hDeq, mul_add, Matrix.trace_add,
      mul_smul_comm, Matrix.trace_smul, mul_one]
    change ε * (A j).trace + (A j * D₀).trace ≤ m + 1
    have hl := trace_mul_convexHull_le (A j) B m (hpair j) hD₀
    linarith [hεA j]
  · intro i
    rw [Matrix.trace_mul_cycle, hinv]
    exact htr i

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open Matrix Set
open scoped MatrixOrder


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.exists_normalized_factors := @_root_.OAI.PerfectMatchingPSD.exists_normalized_factors
