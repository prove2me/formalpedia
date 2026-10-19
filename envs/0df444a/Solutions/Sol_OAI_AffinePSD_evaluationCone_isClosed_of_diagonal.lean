-- Prove2me | solution 1 for OAI.AffinePSD.evaluationCone_isClosed_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:30:21.116334+00:00
-- url     : https://prove2.me/submissions/7a36fc30-7feb-465c-a754-769741128ede

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/DiagonalCone.lean:L13-L50
-- (upload_full_project.md Phase 4): solution for node OAI.AffinePSD.evaluationCone_isClosed_of_diagonal. The node keeps its source
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
import Theorems.Thm_OAI_AffinePSD_diagonal_compression
import Theorems.Thm_OAI_AffinePSD_diagonal_trace_bound
import Theorems.Thm_OAI_AffinePSD_psd_isClosed

-- ---- from OAI.Combinatorics.MatchingPSD.PSDCompression ----
namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

omit [Fintype R] in
lemma sum_diagonal_nonneg (B : I → Matrix R R ℝ) (hB : ∀ i, (B i).PosSemidef)
    (d : R → ℝ) (hs : ∑ i, B i = diagonal d) : ∀ j, 0 ≤ d j := by
  intro j
  have he : ∑ i, B i j j = d j := by
    simpa only [Matrix.sum_apply, Matrix.diagonal_apply_eq] using
      congrArg (fun M : Matrix R R ℝ => M j j) hs
  rw [← he]
  exact Finset.sum_nonneg (fun i _ => (hB i).diag_nonneg)

end AffinePSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PSDTopology ----
namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

omit [Fintype I] in
lemma evaluation_continuous (B : I → Matrix R R ℝ) : Continuous (evaluation B) :=
  (evaluation B).continuous_of_finiteDimensional

end AffinePSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatrixBounds ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

lemma posSemidef_entry_abs_le_trace {A : Matrix R R ℝ} (hA : A.PosSemidef) (i j : R) :
    |A i j| ≤ A.trace := by
  have hi : 0 ≤ A i i := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1)
    simpa using he
  have hj : 0 ≤ A j j := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single j 1)
    simpa using he
  have hsym : A j i = A i j := by
    simpa using congrArg (fun M : Matrix R R ℝ => M i j) hA.isHermitian.eq
  have hplus : -(A i i + A j j)/2 ≤ A i j := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_add, dotProduct_add,
      add_dotProduct, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at he
    rw [hsym] at he
    linarith
  have hminus : A i j ≤ (A i i + A j j)/2 := by
    have he := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
    simp only [star_trivial, Matrix.mulVec_sub, dotProduct_sub,
      sub_dotProduct, Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] at he
    rw [hsym] at he
    linarith
  have hdiag (k : R) : A k k ≤ A.trace := by
    change A k k ≤ ∑ l, A l l
    apply Finset.single_le_sum (f := fun l => A l l)
    · intro l _
      have he := hA.dotProduct_mulVec_nonneg (Pi.single l 1)
      simpa using he
    · exact Finset.mem_univ k
  exact (abs_le.mpr ⟨by linarith, hminus⟩).trans (by linarith [hdiag i, hdiag j])

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.DiagonalCone ----
namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma evaluationCone_isClosed_of_diagonal (B : I → Matrix R R ℝ)
    (hB : ∀ i, (B i).PosSemidef) (d : R → ℝ)
    (hs : ∑ i, B i = diagonal d) : IsClosed (evaluationCone B) := by
  classical
  apply IsSeqClosed.isClosed
  intro u y hu hy
  choose A hA heA using hu
  have hc (k : ℕ) := diagonal_compression B hB d hs (A k) (hA k)
  choose C hC heC hzC using hc
  have heval (k : ℕ) : evaluation B (C k) = u k := (heC k).trans (heA k)
  have hsum : Filter.Tendsto (fun k => ∑ i, u k i) Filter.atTop (nhds (∑ i, y i)) :=
    tendsto_finsetSum _ (fun i _ => (tendsto_pi_nhds.mp hy) i)
  obtain ⟨b, hb⟩ := hsum.bddAbove_range
  have hbound (k : ℕ) : ∑ i, u k i ≤ b := hb (Set.mem_range_self k)
  let a : ℝ := ∑ j, (d j)⁻¹
  have ha : 0 ≤ a := Finset.sum_nonneg (fun j _ =>
    inv_nonneg.mpr (sum_diagonal_nonneg B hB d hs j))
  have htr (k : ℕ) : (C k).trace ≤ a * b := by
    refine (diagonal_trace_bound B hB d hs (C k) (hC k) (hzC k)).trans ?_
    rw [heval]
    exact mul_le_mul_of_nonneg_left (hbound k) ha
  let lo : R → R → ℝ := fun _ _ => -(a * b)
  let hi : R → R → ℝ := fun _ _ => a * b
  have hm (k : ℕ) : C k ∈ Set.Icc lo hi := by
    constructor <;> intro i j
    · exact (abs_le.mp ((PerfectMatchingPSD.posSemidef_entry_abs_le_trace (hC k) i j).trans
        (htr k))).1
    · exact (abs_le.mp ((PerfectMatchingPSD.posSemidef_entry_abs_le_trace (hC k) i j).trans
        (htr k))).2
  obtain ⟨L, hL, φ, hφ, ht⟩ := IsCompact.tendsto_subseq (X := R → R → ℝ) (isCompact_Icc : IsCompact (Set.Icc lo hi)) hm
  have hpsd : Matrix.PosSemidef L := psd_isClosed.mem_of_tendsto ht
    (Filter.Eventually.of_forall (fun k => hC (φ k)))
  refine ⟨L, hpsd, ?_⟩
  have hlim := (evaluation_continuous B).continuousAt.tendsto.comp ht
  have hlim' := hy.comp hφ.tendsto_atTop
  have hEq : evaluation B ∘ (C ∘ φ) = u ∘ φ := by ext k i; exact congrFun (heval (φ k)) i
  have hlim := hlim.congr (fun k => congrFun hEq k)
  exact tendsto_nhds_unique hlim hlim'

end AffinePSD

end OAI

-- ---- platform node ----
open OAI OAI.AffinePSD
open Matrix Finset
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.AffinePSD.evaluationCone_isClosed_of_diagonal := @_root_.OAI.AffinePSD.evaluationCone_isClosed_of_diagonal
