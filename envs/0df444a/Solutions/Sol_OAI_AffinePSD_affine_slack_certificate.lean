-- Prove2me | solution 1 for OAI.AffinePSD.affine_slack_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:45:45.451096+00:00
-- url     : https://prove2.me/submissions/53fb267c-362f-45a6-a567-37915390fa53

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/AffineCertificate.lean:L12-L49
-- (upload_full_project.md Phase 4): solution for node OAI.AffinePSD.affine_slack_certificate. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift
import Theorems.Thm_OAI_AffinePSD_exists_psd_evaluation

-- ---- from OAI.Combinatorics.MatchingPSD.AffineSums ----
namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma affine_sum_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : AffineSubspace ℝ V) (p : I → V) (hp : ∀ i, p i ∈ L)
    (w : I → ℝ) (hw : ∑ i, w i = 1) : ∑ i, w i • p i ∈ L := by
  rw [← Finset.affineCombination_eq_linear_combination univ p w hw]
  exact (affineSpan_le.mpr (Set.range_subset_iff.mpr hp))
    (affineCombination_mem_affineSpan hw p)

lemma affine_sum_apply {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (p : I → V)
    (w : I → ℝ) (hw : ∑ i, w i = 1) :
    f (∑ i, w i • p i) = ∑ i, w i • f (p i) := by
  rw [← Finset.affineCombination_eq_linear_combination univ p w hw,
    Finset.map_affineCombination _ _ _ hw f,
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  rfl

end AffinePSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.AffineCertificate ----
namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma affine_slack_certificate (L : AffineSubspace ℝ (Matrix R R ℝ))
    (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef) (hBL : ∀ i, B i ∈ L)
    (f : Matrix R R ℝ →ᵃ[ℝ] ℝ)
    (hn : ∀ X ∈ L, X.PosSemidef → 0 ≤ f X)
    (i₀ : I) (hz : f (B i₀) = 0) :
    ∃ A : Matrix R R ℝ, A.PosSemidef ∧ ∀ i, (A * B i).trace = f (B i) := by
  classical
  suffices ∃ A : Matrix R R ℝ, A.PosSemidef ∧ evaluation B A = fun i => f (B i) by
    obtain ⟨A, hA, he⟩ := this
    exact ⟨A, hA, fun i => congrFun he i⟩
  apply exists_psd_evaluation B hB
  intro c hc
  let s : ℝ := ∑ i, c i
  let t : ℝ := |s| + 1
  let q : ℝ := s + t
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hq : 0 < q := by dsimp [q, t]; linarith [neg_abs_le s]
  let w : I → ℝ := fun i => (c i + if i = i₀ then t else 0) / q
  have hw : ∑ i, w i = 1 := by
    simp only [w, ← Finset.sum_div, Finset.sum_add_distrib]
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, q, s] using div_self hq.ne'
  have hmatrix : ∑ i, w i • B i = q⁻¹ • ((∑ i, c i • B i) + t • B i₀) := by
    simp only [w, div_eq_inv_mul, mul_smul, ← Finset.smul_sum, add_smul,
      Finset.sum_add_distrib]
    congr 1
    simp
  have hpos : (∑ i, w i • B i).PosSemidef := by
    rw [hmatrix]
    exact (hc.add ((hB i₀).smul ht)).smul (inv_nonneg.mpr hq.le)
  have hnonneg := hn _ (affine_sum_mem L B hBL w hw) hpos
  rw [affine_sum_apply f B w hw] at hnonneg
  have hvalue : ∑ i, w i • f (B i) = (∑ i, c i * f (B i)) / q := by
    simp only [w, smul_eq_mul, add_div, add_mul, Finset.sum_add_distrib,
      div_mul_eq_mul_div, ← Finset.sum_div]
    simp [hz]
  rw [hvalue] at hnonneg
  have hh := (le_div_iff₀ hq).mp hnonneg
  simpa using hh

end AffinePSD

end OAI

-- ---- platform node ----
open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.AffinePSD.affine_slack_certificate := @_root_.OAI.AffinePSD.affine_slack_certificate
