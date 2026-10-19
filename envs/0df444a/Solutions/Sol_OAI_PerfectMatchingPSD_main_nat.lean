-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.main_nat
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:25:46.015997+00:00
-- url     : https://prove2.me/submissions/229cc774-1d0c-4b7d-97ff-8464d9563bf3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Main.lean:L9-L51
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.main_nat. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Parameters
import Theorems.Thm_OAI_MatchingInterpolation_conditional_cell_lower_bound
import Theorems.Thm_OAI_PerfectMatchingPSD_cut_degree_identity
import Theorems.Thm_OAI_PerfectMatchingPSD_global_factors_of_factorization
import Theorems.Thm_OAI_PerfectMatchingPSD_numerical_selection

-- ---- from OAI.Combinatorics.MatchingPSD.CutGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma globalVertices_card (s q : ℕ) :
    Fintype.card (GlobalVertices s q) = 2*s*(q+2)+2 := by
  simp only [GlobalVertices, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  ring

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.FiniteFactorization ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD

lemma crossingCount_pos {n : ℕ} (U : OddCut n) (M : PerfectMatching n) :
    0 < crossingCount U.1 M := by
  obtain ⟨k, hk⟩ := U.2
  have h := cut_degree_identity U.1 M
  omega

lemma slack_nonneg {n : ℕ} (i : Row n) (M : PerfectMatching n) :
    0 ≤ slack i M := by
  classical
  rcases i with e | U
  · simp only [slack]
    split_ifs <;> norm_num
  · have h : 1 ≤ crossingCount U.1 M := crossingCount_pos U M
    have hr : (1 : ℝ) ≤ (crossingCount U.1 M : ℝ) := by exact_mod_cast h
    simpa only [slack, sub_nonneg] using hr

lemma exists_diagonal_factorization {I : Type u_1} {J : Type u_2} [Finite J]
    (S : I → J → ℝ) (hS : ∀ i j, 0 ≤ S i j) :
    ∃ r : ℕ, 0 < r ∧
      ∃ (A : I → Matrix (Fin r) (Fin r) ℝ)
        (B : J → Matrix (Fin r) (Fin r) ℝ),
        (∀ i, (A i).PosSemidef) ∧ (∀ j, (B j).PosSemidef) ∧
        ∀ i j, S i j = Matrix.trace (A i * B j) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFin (Option J)
  let a (i : I) (k : Option J) : ℝ := k.elim 0 (S i)
  let b (j : J) (k : Option J) : ℝ := if k = some j then 1 else 0
  refine ⟨Fintype.card (Option J), by simp,
    (fun i => (Matrix.diagonal (a i)).submatrix e.symm e.symm),
    (fun j => (Matrix.diagonal (b j)).submatrix e.symm e.symm), ?_, ?_, ?_⟩
  · intro i
    apply Matrix.PosSemidef.submatrix
    apply Matrix.PosSemidef.diagonal
    intro k
    cases k with
    | none => exact le_rfl
    | some j => exact hS i j
  · intro j
    apply Matrix.PosSemidef.submatrix
    apply Matrix.PosSemidef.diagonal
    intro k
    dsimp [b]
    split_ifs <;> norm_num
  · intro i j
    rw [Matrix.submatrix_mul_equiv, Matrix.diagonal_mul_diagonal,
      Matrix.submatrix_diagonal _ _ e.symm.injective, Matrix.trace_diagonal]
    dsimp only [Function.comp_def]
    rw [e.symm.sum_comp (fun k => a i k * b j k)]
    simp [a, b]

lemma factor_orders_nonempty (n : ℕ) :
    {r : ℕ | 0 < r ∧ HasFactorization n r}.Nonempty := by
  obtain ⟨r, hr, h⟩ := exists_diagonal_factorization (@slack n) slack_nonneg
  exact ⟨r, hr, h⟩

lemma psdRank_pos (n : ℕ) : 0 < psdRank n :=
  (Nat.sInf_mem (factor_orders_nonempty n)).1

lemma hasFactorization_psdRank (n : ℕ) : HasFactorization n (psdRank n) :=
  (Nat.sInf_mem (factor_orders_nonempty n)).2

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.Parameters ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

lemma index_le_vertexSize (d t : ℕ) : t ≤ vertexSize d t := by
  have ht : t ≤ t^4 := Nat.le_pow (by decide)
  have hc : 1 ≤ 8*(d+1)*(t+2) := by
    have : 0 < 8*(d+1)*(t+2) := by positivity
    omega
  calc
    t ≤ t^4 := ht
    _ ≤ (8*(d+1)*(t+2))*t^4 := by simpa only [one_mul] using Nat.mul_le_mul_right (t^4) hc
    _ ≤ vertexSize d t := by dsimp [vertexSize, blockSize]; nlinarith

lemma vertexSize_succ_bound (d t : ℕ) (ht : 1 ≤ t) :
    vertexSize d (t+1) ≤ 1024*(d+1)*t^5 := by
  have hp : 1 ≤ (d+1)*t^5 := by
    have : 0 < (d+1)*t^5 := by positivity
    omega
  calc
    _ = 8*(d+1)*(t+1)^4*(t+3)+2 := by dsimp [vertexSize, blockSize]; ring
    _ ≤ 8*(d+1)*(2*t)^4*(4*t)+2 := by gcongr <;> omega
    _ = 512*(d+1)*t^5+2 := by ring
    _ ≤ _ := by nlinarith

lemma vertexSize_succ_le_pow6 (d t : ℕ) (ht : 1 ≤ t) (hd : 1024*(d+1) ≤ t) :
    vertexSize d (t+1) ≤ t^6 := by
  calc
    _ ≤ 1024*(d+1)*t^5 := vertexSize_succ_bound d t ht
    _ ≤ t*t^5 := Nat.mul_le_mul_right _ hd
    _ = _ := by ring

lemma bracket_vertexSize (d T n : ℕ) (hn : vertexSize d T ≤ n) :
    ∃ t : ℕ, T ≤ t ∧ vertexSize d t ≤ n ∧ n < vertexSize d (t+1) := by
  classical
  let P := fun t => vertexSize d t ≤ n
  let t := Nat.findGreatest P n
  have hT : T ≤ n := (index_le_vertexSize d T).trans hn
  refine ⟨t, Nat.le_findGreatest (P := P) hT hn, Nat.findGreatest_spec (P := P) hT hn, ?_⟩
  by_contra h
  have hnext : P (t+1) := le_of_not_gt h
  have htn : t+1 ≤ n := (index_le_vertexSize d (t+1)).trans hnext
  exact (Nat.findGreatest_eq_iff.mp (show Nat.findGreatest P n=t from rfl)).2.2
    (Nat.lt_succ_self t) htn hnext

lemma exists_padded_global_equiv {n s q : ℕ} (hn : Even n) (hle : 2*s*(q+2)+2 ≤ n) :
    ∃ k : ℕ, Nonempty ((GlobalVertices s q ⊕ (Fin k × Bool)) ≃ Fin n) := by
  have hg : Even (2*s*(q+2)+2) := ⟨s*(q+2)+1, by ring⟩
  have hd : Even (n-(2*s*(q+2)+2)) := (Nat.even_sub hle).mpr ⟨fun _ => hg, fun _ => hn⟩
  obtain ⟨k,hk⟩ := hd
  refine ⟨k, ⟨Fintype.equivOfCardEq ?_⟩⟩
  rw [Fintype.card_sum, globalVertices_card]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

lemma eventually_pow_lt_half_exp (p : ℕ) :
    ∀ᶠ t : ℕ in atTop, (t:ℝ)^p < (2:ℝ)^t/2 := by
  have ho := isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) p (by norm_num : 1 < (2:ℝ))
  have hb := ho.bound (by norm_num : (0:ℝ) < 1/4)
  filter_upwards [hb] with t ht
  have ht' : (t:ℝ)^p ≤ (1/4)*(2:ℝ)^t := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ (t:ℝ)^p by positivity),
      abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) _)] using ht
  calc
    _ ≤ (1/4)*(2:ℝ)^t := ht'
    _ < _ := by nlinarith [pow_pos (by norm_num : (0:ℝ)<2) t]

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.NumericalBounds ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix
open scoped BigOperators MatrixOrder

lemma blockSize_ge (d t : ℕ) : t^4 ≤ blockSize d t := by
  dsimp [blockSize]
  simpa only [one_mul] using Nat.mul_le_mul_right (t^4) (show 1 ≤ 4*(d+1) by omega)

lemma blockSize_grid (d t : ℕ) : 2*t^4*d ≤ blockSize d t := by
  dsimp [blockSize]
  calc
    2*t^4*d = (2*d)*t^4 := by ring
    _ ≤ 4*(d+1)*t^4 := Nat.mul_le_mul_right _ (by omega)

lemma numerical_smallness (D : ℝ) (t : ℕ) (ht : 1 ≤ t) (hD : 8*(D+1) ≤ (t:ℝ)) :
    16*(t:ℝ)^2*((t:ℝ)*D+1) ≤ 2*(t:ℝ)^4 := by
  have ht1 : (1:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
  calc
    _ ≤ 16*(t:ℝ)^2*((t:ℝ)*(D+1)) := by gcongr; linarith
    _ = 2*(t:ℝ)^3*(8*(D+1)) := by ring
    _ ≤ 2*(t:ℝ)^3*(t:ℝ) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.Main ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

lemma main_nat (p : ℕ) : ∃ n₀ : ℕ, 4 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → Even n → (n:ℝ)^p < (psdRank n:ℝ) := by
  classical
  obtain ⟨d,H,hd,D,hD,hdecode⟩ := conditional_cell_lower_bound (10*(p+1))
  obtain ⟨Te,hTe⟩ := eventually_atTop.mp (eventually_pow_lt_half_exp (6*p))
  let T := 2+H+1024*(d+1)+Fintype.card (SampleIndex d)+⌈8*(D+1)⌉₊+Te
  refine ⟨vertexSize d T+4, by omega, ?_⟩
  intro n hn hneven
  obtain ⟨t,ht,hleft,hright⟩ := bracket_vertexSize d T n (by omega)
  dsimp only [T] at ht
  have ht2 : 2 ≤ t := by omega
  have ht1 : 1 ≤ t := by omega
  have hHt : H ≤ t := by omega
  have hdt : 1024*(d+1) ≤ t := by omega
  have hTt : Fintype.card (SampleIndex d) ≤ t := by omega
  have hDt : 8*(D+1) ≤ (t:ℝ) :=
    (Nat.le_ceil (8*(D+1))).trans (by exact_mod_cast (show ⌈8*(D+1)⌉₊ ≤ t by omega))
  have htet : Te ≤ t := by omega
  have hn6 : n ≤ t^6 := hright.le.trans (vertexSize_succ_le_pow6 d t ht1 hdt)
  have hl : 1 ≤ t^4 := one_le_pow₀ ht1
  have hs : 1 ≤ blockSize d t := hl.trans (blockSize_ge d t)
  have hH : H ≤ 3*blockSize d t+1 := by
    have hts : t ≤ blockSize d t := (Nat.le_pow (by decide : 0 < 4)).trans (blockSize_ge d t)
    omega
  by_contra hnot
  have hrn : (psdRank n:ℝ) ≤ (n:ℝ)^p := le_of_not_gt hnot
  obtain ⟨k,⟨e⟩⟩ := exists_padded_global_equiv hneven hleft
  obtain ⟨Q,B,hQ,hB,htrQ,htrB,hpair⟩ := global_factors_of_factorization
    hneven (by omega : 1 ≤ n) (hasFactorization_psdRank n) e (standardPairing (H := Fin k))
  have hsel : (t:ℝ)*(psdRank n)^4*(Fintype.card (SampleIndex d))*
      ((2*(3*(blockSize d t:ℝ)+1))^(2*(10*(p+1))))⁻¹ ≤
      (1/((psdRank n:ℝ)*((n:ℝ)+1)*(2*(t^4:ℕ))))^2 := by
    simpa only [Nat.cast_pow] using numerical_selection p d t (psdRank n) n
      (Fintype.card (SampleIndex d)) ht2 (psdRank_pos n) hn6 hTt hrn
  have hsmall : 16*(t:ℝ)^2*((t:ℝ)*D+1) ≤ 2*(t^4:ℕ) := by
    simpa only [Nat.cast_pow] using numerical_smallness D t ht1 hDt
  have hlower : (2:ℝ)^t/2 ≤ (psdRank n:ℝ) :=
    hdecode (blockSize d t) t (t^4) (psdRank n) hH hs ht1 (blockSize_grid d t) hl
      (psdRank_pos n) ((n:ℝ)+1) (by positivity) Q B hQ hB htrQ htrB hpair hsel hsmall
  have hn6r : (n:ℝ) ≤ (t:ℝ)^6 := by exact_mod_cast hn6
  have hpow : (n:ℝ)^p ≤ (t:ℝ)^(6*p) := by
    simpa only [pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg n) hn6r p
  exact (not_lt_of_ge hlower) ((hrn.trans hpow).trans_lt (hTe t htet))

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.main_nat := @_root_.OAI.PerfectMatchingPSD.main_nat
