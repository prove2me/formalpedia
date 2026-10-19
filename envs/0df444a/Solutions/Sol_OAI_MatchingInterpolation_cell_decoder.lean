-- Prove2me | solution 1 for OAI.MatchingInterpolation.cell_decoder
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:14:08.95717+00:00
-- url     : https://prove2.me/submissions/fec9cddb-a19a-4fab-b3a5-aaedbd1b8deb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/CellDecoder.lean:L53-L109
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingInterpolation.cell_decoder. The node keeps its source
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
import Theorems.Thm_OAI_MatchingInterpolation_interpolation_matrix_domination
import Theorems.Thm_OAI_MatchingSmoothing_cellAverage_star
import Theorems.Thm_OAI_MatchingSmoothing_predicateAverage_of_constant
import Theorems.Thm_OAI_MatchingSmoothing_triple_pairing_five
import Theorems.Thm_OAI_MatchingSmoothing_triple_pairing_grid
import Theorems.Thm_OAI_PerfectMatchingPSD_domination_decoder

-- ---- from OAI.Combinatorics.MatchingPSD.TableCoordinates ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section TableCoordinates
variable {V : Type u_1} {C : Type u_2} [Fintype V]

lemma tableCoordinate_symm (z : V → C) (a b : C) :
    tableCoordinate z (a,b) = tableCoordinate z (b,a) := by
  funext M
  unfold tableCoordinate
  rw [← Equiv.sum_comp M.1 (fun v => if z v = b ∧ z (M.1 v) = a then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro v _
  simp [M.partner_partner, and_comm]

end TableCoordinates

section ThreeCoordinates
variable {V : Type u_3} [Fintype V]

end ThreeCoordinates

section TableRelation
variable {H : Type u_4} [Fintype H]

end TableRelation
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TablePolynomials ----
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section PredicateAverage
variable {X : Type u_1} [Fintype X]

lemma predicateAverage_apply (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = (∑ x, if P x then f x else 0) / Fintype.card {x // P x} := by
  simp only [predicateAverage, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

end PredicateAverage
end MatchingSmoothing

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ReynoldsAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

end ReynoldsAverage

section TablePolynomial
variable {H : Type u_4} [Fintype H] [DecidableEq H]

end TablePolynomial
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PermutationSmoothing ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Averages
variable {X : Type u_1} {Y : Type u_2} [Fintype X] [Fintype Y]
lemma predicateAverage_eq_expect (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = 𝔼 x : {x // P x}, f x.1 := by
  rw [predicateAverage_apply, Fintype.expect_eq_sum_div_card]
  congr 1
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f

end Averages

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingFibers ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
namespace Pairing
variable {A : Type u_1} {B : Type u_2} {C : Type u_3}

end Pairing

section Coordinates
variable {A : Type u_6} {B : Type u_7} {C : Type u_8} [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable

lemma tableCoordinate_transport (e : A ≃ B) (z : B → C) (c : C × C) (M : Pairing A) :
    tableCoordinate z c (Pairing.transport e M) = tableCoordinate (z ∘ e) c M := by
  unfold tableCoordinate
  rw [← e.sum_comp (fun b => if z b = c.1 ∧ z ((Pairing.transport e M).1 b) = c.2 then (1:ℝ) else 0)]
  simp only [Pairing.transport_apply, Equiv.symm_apply_apply, Function.comp_apply]

end Coordinates
end MatchingSmoothing

namespace MatchingSmoothing.Pairing
variable {A : Type u_9} {B : Type u_10}

end MatchingSmoothing.Pairing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CutGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma tableCoordinate_localcut {V : Type u_5} [Fintype V] (z : V → Fin 3)
    (M : Pairing V) (b : Bool) :
    tableCoordinate (localCutColor b ∘ z) (true,false) M =
      crossVector z M 0 + crossVector z M (if b then 2 else 1) := by
  cases b
  · change _ = tableCoordinate z (0,1) M + tableCoordinate z (0,2) M
    simp only [tableCoordinate, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rcases (show z v=0 ∨ z v=1 ∨ z v=2 by omega) with hv | hv | hv <;>
      rcases (show z (M.1 v)=0 ∨ z (M.1 v)=1 ∨ z (M.1 v)=2 by omega) with hw | hw | hw <;>
      simp [Function.comp_apply, hv, hw, localCutColor]
  · change _ = tableCoordinate z (0,1) M + tableCoordinate z (1,2) M
    rw [tableCoordinate_symm z 1 2]
    simp only [tableCoordinate, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    rcases (show z v=0 ∨ z v=1 ∨ z v=2 by omega) with hv | hv | hv <;>
      rcases (show z (M.1 v)=0 ∨ z (M.1 v)=1 ∨ z (M.1 v)=2 by omega) with hw | hw | hw <;>
      simp [Function.comp_apply, hv, hw, localCutColor]

lemma tableCoordinate_cellwise_cut {I : Type u_6} {C : Type u_7} [Fintype I] [Fintype C]
    (y : I → Bool) (N : I → Pairing C) :
    tableCoordinate (fun v : I × C => y v.1) (true,false) (Pairing.cellwise N) = 0 := by
  apply (tableCoordinate_eq_zero_iff _ _ _).mpr
  rintro ⟨j,c⟩ ⟨h1,h2⟩
  have he : (true : Bool) = false := h1.symm.trans h2
  cases he

lemma localSplit_cut {A : Type u_8} {B : Type u_9} {C : Type u_10} {I : Type u_11} [DecidableEq I]
    (y : I → Bool) (i : I) :
    globalCutColor (A := A) (B := B) (C := C) y ∘ localSplitEquiv i =
      Sum.elim (localCutColor (y i) ∘ threeColor)
        (fun v : {j : I // j ≠ i} × C => y v.1.1) := by
  funext v
  rcases v with (a | c) | ⟨j,c⟩
  · cases a <;> rfl
  · rfl
  · rfl

lemma extendLocal_cut {A : Type u_12} {B : Type u_13} {C : Type u_14} {I : Type u_15} [Fintype A] [Fintype B] [Fintype C]
    [Fintype I] [DecidableEq I] (y : I → Bool) (i : I)
    (M : Pairing ((A ⊕ B) ⊕ C)) (N : {j : I // j ≠ i} → Pairing C) :
    tableCoordinate (globalCutColor y) (true,false) (extendLocal i M N) =
      crossVector threeColor M 0 + crossVector threeColor M (if y i then 2 else 1) := by
  rw [extendLocal, tableCoordinate_transport, localSplit_cut, tableCoordinate_sum,
    tableCoordinate_cellwise_cut (fun j : {j : I // j ≠ i} => y j.1),
    add_zero, tableCoordinate_localcut]

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CellAverages ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable
section CellAverages
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} {I : Type u_4} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

lemma cellAverage_const (i : I) (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ)
    (x : Fin 3 → ℝ) (c : ℝ) (hM : ∃ M : Pairing ((A ⊕ B) ⊕ C), crossVector threeColor M = x)
    [Nonempty (Pairing C)]
    (hf : ∀ M, crossVector threeColor M = x → ∀ N, f (extendLocal i M N) = c) :
    cellAverage i f x = c := by
  apply predicateAverage_of_constant _ _ hM
  intro M hM
  simp only [extensionAverage, hf M hM, Finset.expect_const, Finset.univ_nonempty]

end CellAverages
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatrixBounds ----
namespace OAI

universe u_1 u_2

namespace PerfectMatchingPSD
open Matrix
open scoped MatrixOrder
variable {R : Type u_1} [Fintype R] [DecidableEq R]

omit [Fintype R] [DecidableEq R] in
lemma matrix_sum_psd {X : Type u_2} (s : Finset X) (f : X → Matrix R R ℝ)
    (hf : ∀ x ∈ s, (f x).PosSemidef) : (∑ x ∈ s, f x).PosSemidef :=
  (Finset.sum_nonneg (fun x hx => (hf x hx).nonneg)).posSemidef

end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatrixAverages ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace PerfectMatchingPSD
open Matrix MatchingSmoothing
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable
variable {R : Type u_1} {X : Type u_2} [Fintype R] [DecidableEq R] [Fintype X]

omit [Fintype R] [DecidableEq R] in
lemma matrix_expect_eq (f : X → Matrix R R ℝ) :
    (𝔼 x, f x) = ((Fintype.card X : ℝ)⁻¹) • (∑ x, f x) := by
  ext i j
  simp [Finset.expect, NNRat.smul_def]

omit [Fintype R] [DecidableEq R] in
lemma matrix_expect_apply (f : X → Matrix R R ℝ) (u v : R) :
    (𝔼 x, f x) u v = 𝔼 x, f x u v := by
  rw [matrix_expect_eq, Fintype.expect_eq_sum_div_card]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, div_eq_inv_mul]

omit [Fintype R] [DecidableEq R] in
lemma matrix_expect_psd (f : X → Matrix R R ℝ) (hf : ∀ x, (f x).PosSemidef) :
    (𝔼 x, f x).PosSemidef := by
  rw [matrix_expect_eq]
  exact (matrix_sum_psd Finset.univ f (fun x _ => hf x)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma trace_mul_expect (Q : Matrix R R ℝ) (f : X → Matrix R R ℝ) :
    (Q * (𝔼 x, f x)).trace = 𝔼 x, (Q*f x).trace := by
  rw [matrix_expect_eq, mul_smul_comm, Matrix.trace_smul,
    Finset.mul_sum, Matrix.trace_sum, Fintype.expect_eq_sum_div_card]
  change (Fintype.card X : ℝ)⁻¹ * _ = _ / Fintype.card X
  rw [div_eq_inv_mul]

section CellMatrices
variable {A : Type u_3} {B : Type u_4} {C : Type u_5} {I : Type u_6} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]

omit [Fintype R] [DecidableEq R] in
lemma cellMatrix_apply (i : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (x : Fin 3 → ℝ) (u v : R) :
    cellMatrix i Bf x u v = cellAverage i (fun M => Bf M u v) x := by
  rw [cellAverage, predicateAverage_eq_expect]
  simp only [cellMatrix, extensionMatrix, extensionAverage, matrix_expect_apply]
  apply Finset.expect_congr (by ext; simp)
  intro M _
  rfl

omit [Fintype R] [DecidableEq R] in
lemma cellMatrix_psd (i : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (hB : ∀ M, (Bf M).PosSemidef) (x : Fin 3 → ℝ) :
    (cellMatrix i Bf x).PosSemidef := by
  apply matrix_expect_psd
  intro M
  apply matrix_expect_psd
  intro N
  exact hB _

omit [Fintype R] [DecidableEq R] in
lemma cellMatrix_star (i j : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (x : ℝ) : cellMatrix i Bf ![x,0,0] = cellMatrix j Bf ![x,0,0] := by
  ext u v
  simp only [cellMatrix_apply, cellAverage_star]

lemma trace_cellMatrix (i : I) (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (Q : Matrix R R ℝ) (x : Fin 3 → ℝ) :
    (Q*cellMatrix i Bf x).trace = cellAverage i (fun M => (Q*Bf M).trace) x := by
  rw [cellAverage, predicateAverage_eq_expect, cellMatrix, trace_mul_expect]
  apply Finset.expect_congr (by ext; simp)
  intro M _
  exact trace_mul_expect Q _

end CellMatrices
end PerfectMatchingPSD

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.GoodCells ----
namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma specialPoint_explicit (j : Fin 5) :
    specialPoint j = (![![1,0,0], ![0,1,1], ![3,0,0], ![1,2,0], ![1,0,2]] j : Point) := by
  fin_cases j <;> ext a <;> fin_cases a <;> norm_num [specialPoint, origin, dirP, dirStar, dirA, dirB]

lemma sample_witness {s l d : ℕ} (hs : 1 ≤ s) (hsl : 2*l*d ≤ s) (t : SampleIndex d) :
    ∃ M : Pairing (TripleVertices s), crossVector threeColor M = samplePoint d (2*l) t := by
  rcases t with j | g
  · rw [samplePoint, Sum.elim_inl, specialPoint_explicit]
    exact triple_pairing_five hs j
  · exact triple_pairing_grid hsl g

end MatchingInterpolation

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.CellDecoder ----
namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable

lemma cell_trace_value {s q r : ℕ}
    (Q : (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
    (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ)
    (hpair : ∀ y M, (Q y*B M).trace = tableCoordinate (globalCutColor y) (true,false) M-1)
    (y : Fin q → Bool) (i : Fin q) (x : Point)
    (hx : ∃ M : Pairing (TripleVertices s), crossVector threeColor M=x) :
    (Q y*cellMatrix i B x).trace = cutValue (y i) x := by
  have : Nonempty (Pairing (Fin s × Bool)) := ⟨standardPairing⟩
  rw [trace_cellMatrix]
  apply cellAverage_const i _ x _ hx
  intro M hM N
  rw [hpair, extendLocal_cut, hM]
  rfl

lemma cutValue_p (b : Bool) : cutValue b (origin+dirP) = 0 := by
  cases b <;> norm_num [cutValue, origin, dirP, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
lemma cutValue_star (b : Bool) : cutValue b (origin+dirStar) = 2 := by
  cases b <;> norm_num [cutValue, origin, dirStar, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
lemma cutValue_bit (b : Bool) : cutValue b (if b then origin+dirB else origin+dirA) = 2 := by
  cases b <;> norm_num [cutValue, origin, dirA, dirB, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

lemma cutValue_grid {d : ℕ} {L : ℝ} (hL : 0 ≤ L) (g : GridIndex d) (b : Bool) :
    cutValue b (scaledNode L g) ≤ 2*(d:ℝ)*L := by
  have hk (a : Fin 3) : (g a : ℝ) ≤ (d:ℝ) := by exact_mod_cast (Nat.le_of_lt_succ (g a).isLt)
  have h0 := mul_le_mul_of_nonneg_left (hk 0) hL
  have h1 := mul_le_mul_of_nonneg_left (hk 1) hL
  have h2 := mul_le_mul_of_nonneg_left (hk 2) hL
  cases b <;> norm_num [cutValue, scaledNode, origin, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] <;> nlinarith

lemma origin_star_eq : origin+dirStar = (![3,0,0] : Point) := by
  ext a
  fin_cases a <;> norm_num [origin, dirStar]

lemma cell_decoder {s q l r d : ℕ} (hs : 1 ≤ s) (hq : 1 ≤ q) (hsl : 2*l*d ≤ s)
    (Q : (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
    (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ)
    (hQ : ∀ y, (Q y).PosSemidef) (hB : ∀ M, (B M).PosSemidef)
    (hpair : ∀ y M, (Q y*B M).trace = tableCoordinate (globalCutColor y) (true,false) M-1)
    (P : Fin q → Fin r → Fin r → Point → ℝ)
    (hP : ∀ i u v, P i u v ∈ lowDegree coord d)
    {η m δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hl : 0 < l)
    (hm : ∀ y, (Q y).trace ≤ m)
    (happrox : ∀ i u v t, |cellMatrix i B (samplePoint d (2*l) t) u v-
      P i u v (samplePoint d (2*l) t)| ≤ η)
    (hε : 0 ≤ (q:ℝ)*(weightMass d (2*l)*(2*d*(2*l))+
      (r:ℝ)*(6+weightMass d (2*l))*η*m)+δ*m)
    (hsmall : (q:ℝ)*Real.sqrt ((q:ℝ)*(weightMass d (2*l)*(2*d*(2*l))+
      (r:ℝ)*(6+weightMass d (2*l))*η*m)+δ*m) ≤ 1/4) :
    (2:ℝ)^q/2 ≤ r := by
  let L : ℝ := 2*l
  have hL : 0 < L := by dsimp [L]; positivity
  let C := fun i => cellMatrix i B
  have hC (i : Fin q) (x : Point) : (C i x).PosSemidef := cellMatrix_psd i B hB x
  have hsamp (y : Fin q → Bool) (i : Fin q) (t : SampleIndex d) :
      (Q y*C i (samplePoint d L t)).trace = cutValue (y i) (samplePoint d L t) :=
    cell_trace_value Q B hpair y i _ (sample_witness hs hsl t)
  have hfive (y : Fin q → Bool) (i : Fin q) (j : Fin 5) :
      (Q y*C i (specialPoint j)).trace = cutValue (y i) (specialPoint j) := hsamp y i (.inl j)
  have hp (y : Fin q → Bool) (i : Fin q) : (Q y*C i (origin+dirP)).trace=0 :=
    (hfive y i 1).trans (cutValue_p _)
  have hstar (y : Fin q → Bool) (i : Fin q) : (Q y*C i (origin+dirStar)).trace=2 :=
    (hfive y i 2).trans (cutValue_star _)
  have hgrid (y : Fin q → Bool) (i : Fin q) (g : GridIndex d) :
      (Q y*C i (scaledNode L g)).trace ≤ 2*(d:ℝ)*L :=
    (hsamp y i (.inr g)).le.trans (cutValue_grid hL.le g (y i))
  have hEex (i : Fin q) := interpolation_matrix_domination d (C i) (hC i) (P i) (hP i)
    hL.ne' hη (fun j u v => happrox i u v (.inl j)) (fun g u v => happrox i u v (.inr g))
  choose E hE hdom hEb using hEex
  let i₀ : Fin q := ⟨0,by omega⟩
  let S := C i₀ (origin+dirStar)
  have hcommon (i : Fin q) : C i (origin+dirStar)=S := by
    dsimp only [S,C]
    rw [origin_star_eq]
    exact cellMatrix_star i i₀ B 3
  let T := fun i (b : Bool) => if b then C i (origin+dirB) else C i (origin+dirA)
  have hT (i : Fin q) (b : Bool) : (T i b).PosSemidef := by
    cases b <;> exact hC i _
  have hTdom (i : Fin q) : T i false+T i true ≤ S+(2:ℝ) • C i (origin+dirP)+E i := by
    change C i (origin+dirA)+C i (origin+dirB) ≤ S+(2:ℝ) • C i (origin+dirP)+E i
    rw [← hcommon i]
    exact hdom i
  have hbit (y : Fin q → Bool) (i : Fin q) : (Q y*T i (y i)).trace=2 := by
    cases hy : y i
    · exact (hfive y i 3).trans (by rw [hy]; exact cutValue_bit false)
    · exact (hfive y i 4).trans (by rw [hy]; exact cutValue_bit true)
  have he (y : Fin q → Bool) (i : Fin q) : (Q y*E i).trace ≤
      weightMass d L*(2*(d:ℝ)*L)+(r:ℝ)*(6+weightMass d L)*η*m := by
    simpa only [Fintype.card_fin] using hEb i (Q y) m (2*(d:ℝ)*L) (hm y) (hgrid y i)
  simpa only [Fintype.card_fin] using domination_decoder Q T (fun i => C i (origin+dirP)) E S hQ hT
    (fun i => hC i _) hE (hC i₀ _) hTdom hp (fun y => hstar y i₀) hbit hδ hm he hε hsmall

end MatchingInterpolation

end OAI

-- ---- platform node ----
open OAI OAI.MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators MatrixOrder
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingInterpolation.cell_decoder := @_root_.OAI.MatchingInterpolation.cell_decoder
