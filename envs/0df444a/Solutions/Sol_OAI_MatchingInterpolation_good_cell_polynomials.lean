-- Prove2me | solution 1 for OAI.MatchingInterpolation.good_cell_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:09:32.773664+00:00
-- url     : https://prove2.me/submissions/d044e8c2-1cad-4514-bc34-08beb52d5f26

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/GoodCells.lean:L25-L85
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingInterpolation.good_cell_polynomials. The node keeps its source
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
import Theorems.Thm_OAI_MatchingSmoothing_simultaneous_cross_approximation
import Theorems.Thm_OAI_MatchingSmoothing_triple_pairing_five
import Theorems.Thm_OAI_MatchingSmoothing_triple_pairing_grid
import Theorems.Thm_OAI_PerfectMatchingPSD_posSemidef_entry_abs_le_trace

-- ---- from OAI.Combinatorics.MatchingPSD.TableMoments ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
open Matrix
section TableKernel
variable {H : Type u_1} {C : Type u_2} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableKernel
end MatchingSmoothing

namespace MatchingSmoothing
open Matrix

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma histogram_cast_sum {V : Type u_4} {T : Type u_5} [Fintype V] [DecidableEq T] (f : V → T) (t : T) :
    (histogram f t : ℝ) = ∑ i, if f i = t then 1 else 0 := by
  classical
  simp only [histogram, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

end ThreeTables

section Probability
variable {V : Type u_6} {C : Type u_7} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

end Probability

section TableNormalization
variable {H : Type u_8} {C : Type u_9} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableNormalization

section ThreeTableMoment
variable {H : Type u_10} [Fintype H] [DecidableEq H]

end ThreeTableMoment
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

lemma sum_relabel_left (p : Equiv.Perm A) (M : Pairing A) (N : Pairing B) :
    sum (relabel p M) N = relabel (Equiv.sumCongr p (Equiv.refl B)) (sum M N) := by
  ext v
  cases v <;> rfl

lemma transport_relabel (e : A ≃ B) (p : Equiv.Perm A) (M : Pairing A) :
    transport e (relabel p M) = relabel (e.symm.trans (p.trans e)) (transport e M) := by
  ext b
  simp only [transport_apply, relabel_apply, Equiv.Perm.inv_def,
    Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm,
    Equiv.symm_apply_apply]

end Pairing

section Coordinates
variable {A : Type u_6} {B : Type u_7} {C : Type u_8} [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable

end Coordinates
end MatchingSmoothing

namespace MatchingSmoothing.Pairing
variable {A : Type u_9} {B : Type u_10}

end MatchingSmoothing.Pairing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.GlobalGeometry ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ThreeCellGeometry
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C]

end ThreeCellGeometry

section GlobalExtension
variable {D : Type u_5} {C : Type u_6} {I : Type u_7} [DecidableEq I]

lemma extendLocal_relabel (i : I) (p : Equiv.Perm (D ⊕ C))
    (M : Pairing (D ⊕ C)) (N : {j : I // j ≠ i} → Pairing C) :
    extendLocal i (Pairing.relabel p M) N = Pairing.relabel (liftLocal i p) (extendLocal i M N) := by
  rw [extendLocal, Pairing.sum_relabel_left, Pairing.transport_relabel]
  rfl

end GlobalExtension
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.AdmissibleTables ----
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ColorTransport
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
end ColorTransport

lemma tripleColor_histogram (s : ℕ) :
    histogram (@tripleColor s) = ![2*s+1,2*s+1,2*s] := by
  funext c
  apply Nat.cast_injective (R := ℝ)
  rw [histogram_cast_sum]
  fin_cases c <;> simp [tripleColor, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_mul]; ring

lemma triple_histogram_pos {s : ℕ} (hs : 0 < s) (i : Fin 3) :
    0 < histogram (@tripleColor s) i := by
  rw [tripleColor_histogram]
  fin_cases i <;> simp; omega

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

omit [Fintype A] [Fintype B] in
lemma extensionAverage_relabel (i : I) (p : Equiv.Perm ((A ⊕ B) ⊕ C))
    (f : Pairing ((A ⊕ B) ⊕ (I × C)) → ℝ) (M : Pairing ((A ⊕ B) ⊕ C)) :
    extensionAverage i f (Pairing.relabel p M) =
      extensionAverage i (fun N => f (Pairing.relabel (liftLocal i p) N)) M := by
  simp only [extensionAverage, extendLocal_relabel]

end CellAverages
end MatchingSmoothing

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

lemma expect_abs_bound (f : X → ℝ) {b : ℝ} (hb : 0 ≤ b) (hf : ∀ x, |f x| ≤ b) :
    |𝔼 x, f x| ≤ b := by
  by_cases hX : Nonempty X
  · let := hX
    have h0 (x : X) : -b ≤ f x := (abs_le.mp (hf x)).1
    have h1 (x : X) : f x ≤ b := (abs_le.mp (hf x)).2
    apply abs_le.mpr
    constructor
    · simpa using Finset.expect_le_expect (s := Finset.univ) (fun x _ => h0 x)
    · simpa using Finset.expect_le_expect (s := Finset.univ) (fun x _ => h1 x)
  · have : IsEmpty X := not_nonempty_iff.mp hX
    simpa using hb

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

omit [Fintype A] [Fintype B] in
lemma extensionAverage_sq_bound (i : I)
    (Bf : Pairing ((A ⊕ B) ⊕ (I × C)) → Matrix R R ℝ)
    (hB : ∀ M, (Bf M).PosSemidef) {b : ℝ} (hb : 0 ≤ b)
    (htr : ∀ M, (Bf M).trace ≤ b) (u v : R) (M : Pairing ((A ⊕ B) ⊕ C)) :
    (extensionAverage i (fun N => Bf N u v) M)^2 ≤ b^2 := by
  have he := expect_abs_bound (fun N => Bf (extendLocal i M N) u v) hb
    (fun N => (posSemidef_entry_abs_le_trace (hB _) u v).trans (htr _))
  have hex : extensionAverage i (fun N => Bf N u v) M =
      𝔼 N : {j : I // j ≠ i} → Pairing C, Bf (extendLocal i M N) u v := by
    apply Finset.expect_congr (by ext; simp)
    intro N _
    rfl
  rw [hex]
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hb).mpr he

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

lemma good_cell_polynomials (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ s q l r : ℕ, H ≤ 3*s+1 → 1 ≤ s → 2*l*d ≤ s →
      ∀ (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ M, (B M).PosSemidef) → (∀ M, (B M).trace ≤ (r:ℝ)) →
      ∀ η : ℝ, 0 ≤ η →
      (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ ≤ η^2 →
      ∃ a : Equiv.Perm (GlobalVertices s q),
      ∃ P : Fin q → Fin r → Fin r → Point → ℝ,
        (∀ i u v, P i u v ∈ lowDegree coord d) ∧
        ∀ i u v t, |cellMatrix i (fun M => B (Pairing.relabel a M))
          (samplePoint d (2*l) t) u v-P i u v (samplePoint d (2*l) t)| ≤ η := by
  classical
  obtain ⟨d,H,hd,hmain⟩ := simultaneous_cross_approximation K
  refine ⟨d,H,hd,?_⟩
  intro s q l r hH hs hsl B hB htr η hη hnum
  let J := Fin q × (Fin r × Fin r)
  let T := SampleIndex d
  let M : T → Pairing (TripleVertices s) := fun t => (sample_witness hs hsl t).choose
  have hM (t : T) : crossVector threeColor (M t) = samplePoint d (2*l) t :=
    (sample_witness hs hsl t).choose_spec
  let g (j : J) (a : Equiv.Perm (GlobalVertices s q)) (N : Pairing (TripleVertices s)) : ℝ :=
    extensionAverage j.1 (fun Z => B (Pairing.relabel a Z) j.2.1 j.2.2) N
  have hg (j : J) (a : Equiv.Perm (GlobalVertices s q)) (p : Equiv.Perm (TripleVertices s)) :
      g j (a * liftLocal j.1 p) = fun N => g j a (Pairing.relabel p N) := by
    funext N
    dsimp only [g]
    rw [extensionAverage_relabel]
    simp only [Pairing.relabel_mul]
  have hgb (j : J) (a : Equiv.Perm (GlobalVertices s q)) (N : Pairing (TripleVertices s)) :
      (g j a N)^2 ≤ (r:ℝ)^2 :=
    extensionAverage_sq_bound j.1 _ (fun Z => hB _) (Nat.cast_nonneg r)
      (fun Z => htr _) j.2.1 j.2.2 N
  obtain ⟨a,P,hP,hbound⟩ := hmain (3*s+1) hH (TripleVertices s)
    (Equiv.Perm (GlobalVertices s q)) J T (tripleEquiv s) (fun _ => threeColor)
      (fun _ c => triple_histogram_pos (by omega) c) (fun _ => M)
      (fun j => liftLocal j.1) g hg (r:ℝ) hgb
  refine ⟨a,fun i u v => P (i,u,v),fun i u v => hP (i,u,v),?_⟩
  intro i u v t
  let E (j : J) (t : T) :=
    predicateAverage (fun N => crossVector threeColor N = crossVector threeColor (M t)) (g j a) -
      P j (crossVector threeColor (M t))
  have hjt : (E (i,u,v) t)^2 ≤ ∑ j, ∑ t, (E j t)^2 := by
    exact (Finset.single_le_sum (fun z _ => sq_nonneg (E (i,u,v) z)) (Finset.mem_univ t)).trans
      (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun z _ => sq_nonneg (E j z)))
        (Finset.mem_univ (i,u,v)))
  have hb : (∑ j, ∑ t, (E j t)^2) ≤ η^2 := by
    apply hbound.trans
    have heq : (Fintype.card J : ℝ)*(Fintype.card T)*((2*(3*s+1:ℕ):ℝ)^(2*K))⁻¹*(r:ℝ)^2 =
        (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ := by
      simp only [J, T, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [heq]
    exact hnum
  have hab : |E (i,u,v) t| ≤ η := (sq_le_sq₀ (abs_nonneg _) hη).mp
    (by simpa only [sq_abs] using hjt.trans hb)
  have he : E (i,u,v) t = cellMatrix i (fun Z => B (Pairing.relabel a Z))
      (samplePoint d (2*l) t) u v-P (i,u,v) (samplePoint d (2*l) t) := by
    rw [cellMatrix_apply]
    dsimp only [E, cellAverage, g]
    rw [hM]
  rwa [he] at hab

end MatchingInterpolation

end OAI

-- ---- platform node ----
open OAI OAI.MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingInterpolation.good_cell_polynomials := @_root_.OAI.MatchingInterpolation.good_cell_polynomials
