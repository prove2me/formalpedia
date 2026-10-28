-- Prove2me | solution 1 for LovaszSchrijver.Defect.defect_div_le_NIndex_le_defect
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T05:31:12.864452+00:00
-- url     : https://prove2.me/submissions/4f49a0cf-a997-4e17-a06e-d2a4f22f07d5

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_Basic
import Definitions.Def_LovaszSchrijver_Defect_Index
import Definitions.Def_LovaszSchrijver_Defect_MatrixCone
import Definitions.Def_LovaszSchrijver_Defect_StableSet


-- Complete module: LSDProof.ConeForms

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V]

def linForm (a : V → ℝ) (b : ℝ) : Option V → ℝ :=
  fun o => o.elim b (fun i => -a i)

omit [DecidableEq V] in
lemma linForm_dot (a : V → ℝ) (b : ℝ) (x : Option V → ℝ) :
    linForm a b ⬝ᵥ x = b * x none - a ⬝ᵥ (fun i => x (some i)) := by
  simp [dotProduct, Fintype.sum_option, linForm, Finset.sum_neg_distrib, sub_eq_add_neg]

omit [DecidableEq V] in
lemma dual_cone_of_generators (S : Set (Option V → ℝ)) (u : Option V → ℝ)
    (hu : ∀ x ∈ S, 0 ≤ u ⬝ᵥ x) : u ∈ dualCone (cone S) := by
  intro x hx
  change x ∈ Submodule.span {r : ℝ // 0 ≤ r} S at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hu x hx
  | zero => simp
  | add x y hx hy hxp hyp => simpa [dotProduct_add] using add_nonneg hxp hyp
  | smul r x hx hxp =>
    change 0 ≤ u ⬝ᵥ ((r : ℝ) • x)
    rw [dotProduct_smul]
    exact mul_nonneg r.property hxp

omit [Fintype V] [DecidableEq V] in
lemma q_generator (x : Option V → ℝ) (hx : IsZeroOne x) (h0 : x none = 1) :
    x ∈ (Q : Set (Option V → ℝ)) :=
  PointedCone.subset_hull ⟨hx, h0⟩

lemma e0_dual_Q : Pi.single none (1 : ℝ) ∈ dualCone (Q : Set (Option V → ℝ)) := by
  apply dual_cone_of_generators
  intro x hx
  simp [hx.2]

lemma ei_dual_Q (i : V) : Pi.single (some i) (1 : ℝ) ∈ dualCone (Q : Set (Option V → ℝ)) := by
  apply dual_cone_of_generators
  intro x hx
  simp only [single_dotProduct, one_mul]
  rcases hx.1 (some i) with h | h <;> simp [h]

lemma fi_dual_Q (i : V) :
    Pi.single none (1 : ℝ) - Pi.single (some i) 1 ∈ dualCone (Q : Set (Option V → ℝ)) := by
  apply dual_cone_of_generators
  intro x hx
  simp only [sub_dotProduct, single_dotProduct, one_mul, hx.2]
  rcases hx.1 (some i) with h | h <;> simp [h]

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.ColumnTest

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma dual_Q_nonneg_on_cube (v w : Option V → ℝ) (hv : v ∈ dualCone Q)
    (h0 : 0 ≤ w none) (hw : ∀ i, 0 ≤ w (some i) ∧ w (some i) ≤ w none) :
    0 ≤ v ⬝ᵥ w := by
  classical
  let z : Option V → ℝ := fun o => o.elim 1 (fun i => if v (some i) < 0 then 1 else 0)
  have hz : z ∈ Q := q_generator z (by intro o; cases o <;> simp [z]; exact le_or_gt 0 _) rfl
  have htest := hv z hz
  have htest' : 0 ≤ v none + ∑ i, if v (some i) < 0 then v (some i) else 0 := by
    simpa [dotProduct, Fintype.sum_option, z, mul_ite] using htest
  have hterms : ∀ i, w none * (if v (some i) < 0 then v (some i) else 0) ≤
      v (some i) * w (some i) := by
    intro i
    by_cases hi : v (some i) < 0
    · simp only [if_pos hi]
      nlinarith [(hw i).2]
    · simp only [if_neg hi, mul_zero]
      exact mul_nonneg (le_of_not_gt hi) (hw i).1
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterms i)
  have hp := mul_nonneg h0 htest'
  simp only [Finset.mul_sum, mul_add] at hp
  simp only [dotProduct, Fintype.sum_option]
  nlinarith

lemma mem_M_of_columns (K : Set (Option V → ℝ))
    (Y : Matrix (Option V) (Option V) ℝ) (hs : Y.IsSymm)
    (hd : ∀ i, Y (some i) (some i) = Y none (some i))
    (h0 : Y *ᵥ Pi.single none 1 ∈ K)
    (hi : ∀ i, Y *ᵥ Pi.single (some i) 1 ∈ K)
    (hf : ∀ i, Y *ᵥ (Pi.single none 1 - Pi.single (some i) 1) ∈ K) :
    Y ∈ M K Q := by
  refine ⟨hs, hd, ?_⟩
  intro u hu v hv
  let w := Y.transpose *ᵥ u
  have he (j : Option V) : u ⬝ᵥ (Y *ᵥ Pi.single j 1) = w j := by
    rw [dotProduct_mulVec, dotProduct_single, mul_one]
    exact congrFun (mulVec_transpose Y u).symm j
  have hw0 : 0 ≤ w none := by rw [← he]; exact hu _ h0
  have hw : ∀ i, 0 ≤ w (some i) ∧ w (some i) ≤ w none := by
    intro i
    constructor
    · rw [← he]; exact hu _ (hi i)
    · have h := hu _ (hf i)
      rw [mulVec_sub, dotProduct_sub, he, he] at h
      linarith
  have h := dual_Q_nonneg_on_cube v w hv hw0 hw
  simpa only [w, dotProduct_transpose_mulVec] using h

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.IteratedCones

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V]

lemma N1_zero (K : Set (Option V → ℝ)) : (0 : Option V → ℝ) ∈ N1 K := by
  refine ⟨0, ?_, by ext i; simp [Matrix.col]⟩
  refine ⟨by simp [Matrix.IsSymm], by simp, ?_⟩
  intro u hu v hv
  simp

lemma N1_smul (K : Set (Option V → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    {x : Option V → ℝ} (hx : x ∈ N1 K) : c • x ∈ N1 K := by
  obtain ⟨Y, hY, rfl⟩ := hx
  refine ⟨c • Y, ⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [Matrix.IsSymm, transpose_smul] using congrArg (fun Z => c • Z) hY.1
  · intro i
    simpa using congrArg (fun r : ℝ => c * r) (hY.2.1 i)
  · intro u hu v hv
    simpa [smul_mulVec, dotProduct_smul] using mul_nonneg hc (hY.2.2 u hu v hv)
  · rw [smul_mulVec]

lemma Niter_zero (G : SimpleGraph V) (t : ℕ) : (0 : Option V → ℝ) ∈ Niter t (FR G) := by
  cases t with
  | zero => exact ⟨by simp, by simp⟩
  | succ t => exact N1_zero _

lemma Niter_smul (G : SimpleGraph V) (t : ℕ) (c : ℝ) (hc : 0 ≤ c)
    {x : Option V → ℝ} (hx : x ∈ Niter t (FR G)) : c • x ∈ Niter t (FR G) := by
  cases t with
  | zero =>
    refine ⟨fun i => mul_nonneg hc (hx.1 i), ?_⟩
    intro i j hij
    simpa [smul_eq_mul, mul_add] using mul_le_mul_of_nonneg_left (hx.2 i j hij) hc
  | succ t => exact N1_smul _ c hc hx

lemma dual_N1 (K : Set (Option V → ℝ)) {u : Option V → ℝ}
    (hu : u ∈ dualCone K) : u ∈ dualCone (N1 K) := by
  rintro x ⟨Y, hY, rfl⟩
  exact hY.2.2 u hu _ e0_dual_Q

lemma dual_Niter (K : Set (Option V → ℝ)) {u : Option V → ℝ}
    (hu : u ∈ dualCone K) (t : ℕ) : u ∈ dualCone (Niter t K) := by
  induction t with
  | zero => exact hu
  | succ t ih => exact dual_N1 _ ih

lemma FR_coordinate_dual (G : SimpleGraph V) (i : V) :
    Pi.single (some i) (1 : ℝ) ∈ dualCone (FR G) := by
  intro x hx
  simpa using hx.1 i

lemma FR_edge_dual (G : SimpleGraph V) {i j : V} (hij : G.Adj i j) :
    Pi.single none (1 : ℝ) - Pi.single (some i) 1 - Pi.single (some j) 1 ∈ dualCone (FR G) := by
  intro x hx
  simp only [sub_dotProduct, single_dotProduct, one_mul]
  linarith [hx.2 i j hij]

lemma Niter_FR_bounds (G : SimpleGraph V) (hG : ∀ i, ∃ j, G.Adj i j)
    (t : ℕ) {x : Option V → ℝ} (hx : x ∈ Niter t (FR G)) :
    (∀ i, 0 ≤ x (some i)) ∧ (∀ i j, G.Adj i j → x (some i) + x (some j) ≤ x none) ∧
    (∀ i, x (some i) ≤ x none) := by
  have hn : ∀ i, 0 ≤ x (some i) := fun i => by
    simpa using dual_Niter (FR G) (FR_coordinate_dual G i) t x hx
  have he : ∀ i j, G.Adj i j → x (some i) + x (some j) ≤ x none := by
    intro i j hij
    have h := dual_Niter (FR G) (FR_edge_dual G hij) t x hx
    simp only [sub_dotProduct, single_dotProduct, one_mul] at h
    linarith
  refine ⟨hn, he, fun i => ?_⟩
  obtain ⟨j, hij⟩ := hG i
  linarith [he i j hij, hn j]

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.StableRays

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V]

lemma binary_N1 (K : Set (Option V → ℝ)) (x : Option V → ℝ)
    (hx : x ∈ K) (hb : IsZeroOne x) (h0 : x none = 1) : x ∈ N1 K := by
  let Y : Matrix (Option V) (Option V) ℝ := fun i j => x i * x j
  refine ⟨Y, ⟨?_, ?_, ?_⟩, ?_⟩
  · ext i j
    exact mul_comm _ _
  · intro i
    rcases hb (some i) with h | h <;> simp [Y, h, h0]
  · intro u hu v hv
    have he : u ⬝ᵥ (Y *ᵥ v) = (u ⬝ᵥ x) * (v ⬝ᵥ x) := by
      simp only [dotProduct, mulVec, Y]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [he]
    exact mul_nonneg (hu x hx) (hv x (q_generator x hb h0))
  · rw [mulVec_single_one]
    funext i
    change x i * x none = x i
    rw [h0, mul_one]

omit [Fintype V] in
lemma stable_hom_FR (G : SimpleGraph V) (A : Finset V) (hA : G.IsIndepSet (A : Set V)) :
    hom (chi A) ∈ FR G := by
  refine ⟨fun i => by simp only [hom, Option.elim_some, chi]; split_ifs <;> norm_num, ?_⟩
  intro i j hij
  have hn : ¬(i ∈ A ∧ j ∈ A) := by
    rintro ⟨hi,hj⟩
    exact hA hi hj hij.ne hij
  simp only [hom, Option.elim_some, Option.elim_none, chi]
  split_ifs <;> simp_all

lemma stable_hom_Niter (G : SimpleGraph V) (A : Finset V)
    (hA : G.IsIndepSet (A : Set V)) (t : ℕ) : hom (chi A) ∈ Niter t (FR G) := by
  induction t with
  | zero => exact stable_hom_FR G A hA
  | succ t ih =>
    apply binary_N1 _ _ ih
    · intro o
      cases o with
      | none => simp [hom]
      | some i => by_cases hi : i ∈ A <;> simp [hom, chi, hi]
    · rfl

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.FaceMatrix

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V]

def facePoint (U : Finset V) (p : V → ℝ) : V → ℝ := fun i => if i ∈ U then 1 else p i

def faceTail (p : V → ℝ) : Option V → ℝ := fun o => o.elim 0 p

def faceMatrix (U : Finset V) (p : V → ℝ) : Matrix (Option V) (Option V) ℝ := fun i j =>
  hom (chi U) i * hom (chi U) j + hom (chi U) i * faceTail p j +
    faceTail p i * hom (chi U) j + if i = j then faceTail p i else 0

omit [Fintype V] in
lemma faceMatrix_symm (U : Finset V) (p : V → ℝ) : (faceMatrix U p).IsSymm := by
  ext i j
  change faceMatrix U p j i = faceMatrix U p i j
  unfold faceMatrix
  by_cases h : i = j
  · subst j; rfl
  · simp only [if_neg h, if_neg (Ne.symm h)]
    ring

omit [Fintype V] in
lemma faceMatrix_diag (U : Finset V) (p : V → ℝ) (hp : ∀ i ∈ U, p i = 0) (i : V) :
    faceMatrix U p (some i) (some i) = faceMatrix U p none (some i) := by
  by_cases hi : i ∈ U <;> simp [faceMatrix, hom, chi, faceTail, hi, hp]

lemma faceMatrix_first (U : Finset V) (p : V → ℝ) (hp : ∀ i ∈ U, p i = 0) :
    faceMatrix U p *ᵥ Pi.single none 1 = hom (facePoint U p) := by
  rw [mulVec_single_one]
  funext o
  change faceMatrix U p o none = hom (facePoint U p) o
  cases o with
  | none => simp [faceMatrix, hom, faceTail]
  | some i => by_cases hi : i ∈ U <;> simp [faceMatrix, hom, chi, faceTail, facePoint, hi, hp]

lemma faceMatrix_column_in (U : Finset V) (p : V → ℝ) (hp : ∀ i ∈ U, p i = 0)
    {j : V} (hj : j ∈ U) :
    faceMatrix U p *ᵥ Pi.single (some j) 1 = hom (facePoint U p) := by
  rw [mulVec_single_one]
  funext o
  change faceMatrix U p o (some j) = hom (facePoint U p) o
  cases o with
  | none => simp [faceMatrix, hom, faceTail, chi, hj, hp]
  | some i =>
    by_cases hi : i ∈ U
    · simp [faceMatrix, hom, chi, faceTail, facePoint, hj, hi, hp]
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      simp [faceMatrix, hom, chi, faceTail, facePoint, hj, hi, hp, hij]

lemma faceMatrix_column_out (U : Finset V) (p : V → ℝ) {j : V} (hj : j ∉ U) :
    faceMatrix U p *ᵥ Pi.single (some j) 1 = p j • hom (chi (insert j U)) := by
  rw [mulVec_single_one]
  funext o
  change faceMatrix U p o (some j) = (p j • hom (chi (insert j U))) o
  cases o with
  | none => simp [faceMatrix, hom, faceTail, chi, hj]
  | some i =>
    by_cases hij : i = j
    · subst i; simp [faceMatrix, hom, faceTail, chi, hj]
    · by_cases hi : i ∈ U <;>
        simp [faceMatrix, hom, faceTail, chi, hj, hi, hij, smul_eq_mul]

omit [Fintype V] in
lemma facePoint_difference (U : Finset V) (p : V → ℝ) {j : V} (hj : j ∉ U)
    (hne : 1 - p j ≠ 0) :
    hom (facePoint U p) - p j • hom (chi (insert j U)) =
      (1 - p j) • hom (facePoint U (fun i => if i = j then 0 else p i / (1 - p j))) := by
  funext o
  cases o with
  | none => simp [hom, smul_eq_mul]
  | some i =>
    by_cases hij : i = j
    · subst i; simp [hom, facePoint, chi, hj]
    · by_cases hi : i ∈ U
      · simp [hom, facePoint, chi, hi, hij, smul_eq_mul]
      · simp [hom, facePoint, chi, hi, hij, smul_eq_mul]
        field_simp

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.FaceCube

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma facePoint_FR (G : SimpleGraph V) (U W : Finset V)
    (hU : G.IsIndepSet (U : Set V))
    (hUW : ∀ i ∈ U, ∀ j ∈ W, ¬G.Adj i j)
    (p : V → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1 / 2)
    (hps : ∀ i ∉ W, p i = 0) : hom (facePoint U p) ∈ FR G := by
  refine ⟨?_, ?_⟩
  · intro i
    simp only [hom, Option.elim_some, facePoint]
    split_ifs
    · norm_num
    · exact hp0 i
  · intro i j hij
    simp only [hom, Option.elim_some, Option.elim_none, facePoint]
    by_cases hi : i ∈ U <;> by_cases hj : j ∈ U
    · exact False.elim (hU hi hj hij.ne hij)
    · have hjW : j ∉ W := fun h => hUW i hi j h hij
      simp [hi, hj, hps j hjW]
    · have hiW : i ∉ W := fun h => hUW j hj i h hij.symm
      simp [hi, hj, hps i hiW]
    · simp only [if_neg hi, if_neg hj]
      linarith [hp1 i, hp1 j]

lemma faceCube_Niter (G : SimpleGraph V) (U W : Finset V)
    (hdis : Disjoint U W) (hU : G.IsIndepSet (U : Set V))
    (hUW : ∀ i ∈ U, ∀ j ∈ W, ¬G.Adj i j) (t : ℕ)
    (p : V → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1 / (t + 2 : ℝ))
    (hps : ∀ i ∉ W, p i = 0) : hom (facePoint U p) ∈ Niter t (FR G) := by
  induction t generalizing p with
  | zero => exact facePoint_FR G U W hU hUW p hp0 (by simpa using hp1) hps
  | succ t ih =>
    have hpU : ∀ i ∈ U, p i = 0 := fun i hi => hps i (fun hw => Finset.disjoint_left.mp hdis hi hw)
    have hbound : ∀ i, p i ≤ 1 / (t + 3 : ℝ) := by simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using hp1
    have hden : 0 < (t : ℝ) + 2 := by positivity
    have hpold : ∀ i, p i ≤ 1 / (t + 2 : ℝ) := fun i =>
      le_trans (hbound i) (one_div_le_one_div_of_le hden (by linarith))
    have hx := ih p hp0 hpold hps
    have hplt : ∀ i, p i < 1 := by
      intro i
      have h : 1 / (t + 3 : ℝ) < 1 := (div_lt_one (by positivity)).mpr (by have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith)
      exact lt_of_le_of_lt (hbound i) h
    refine ⟨faceMatrix U p, ?_, faceMatrix_first U p hpU⟩
    apply mem_M_of_columns _ _ (faceMatrix_symm U p) (faceMatrix_diag U p hpU)
    · rwa [faceMatrix_first U p hpU]
    · intro j
      by_cases hj : j ∈ U
      · rwa [faceMatrix_column_in U p hpU hj]
      · rw [faceMatrix_column_out U p hj]
        by_cases hjW : j ∈ W
        · apply Niter_smul G t (p j) (hp0 j)
          apply stable_hom_Niter
          intro i hi k hk hik
          simp only [Finset.mem_coe, Finset.mem_insert] at hi hk
          rcases hi with hi | hi
          · subst i
            rcases hk with hk | hk
            · exact (hik hk.symm).elim
            · exact fun h => hUW k hk j hjW h.symm
          · rcases hk with hk | hk
            · subst k; exact hUW i hi j hjW
            · exact hU hi hk hik
        · simpa [hps j hjW] using Niter_zero G t
    · intro j
      rw [mulVec_sub, faceMatrix_first U p hpU]
      by_cases hj : j ∈ U
      · rw [faceMatrix_column_in U p hpU hj, sub_self]
        exact Niter_zero G t
      · rw [faceMatrix_column_out U p hj]
        have hd : 0 < 1 - p j := sub_pos.mpr (hplt j)
        rw [facePoint_difference U p hj (ne_of_gt hd)]
        apply Niter_smul G t (1 - p j) hd.le
        apply ih
        · intro i
          split_ifs <;> first | exact le_rfl | exact div_nonneg (hp0 i) hd.le
        · intro i
          split_ifs
          · positivity
          · apply (div_le_iff₀ hd).mpr
            rw [one_div_mul_eq_div]
            apply (le_div_iff₀ hden).mpr
            have hbi := (le_div_iff₀ (by positivity : (0 : ℝ) < t + 3)).mp (hbound i)
            have hbj := (le_div_iff₀ (by positivity : (0 : ℝ) < t + 3)).mp (hbound j)
            nlinarith [hp0 i, hp0 j]
        · intro i hi
          split_ifs <;> simp [hps i hi]

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.ThresholdScalar

open MeasureTheory Set

namespace LovaszSchrijver.Defect.LSFresh

noncomputable def halfRound (t y : ℝ) : ℝ :=
  if 1 - t < y then 1 else if t ≤ y then 1 / 2 else 0

theorem halfRound_values (t y : ℝ) :
    halfRound t y = 0 ∨ halfRound t y = 1 / 2 ∨ halfRound t y = 1 := by
  unfold halfRound
  split_ifs <;> simp

theorem halfRound_nonneg (t y : ℝ) : 0 ≤ halfRound t y := by
  rcases halfRound_values t y with h | h | h <;> rw [h] <;> norm_num

theorem halfRound_edge {t x y : ℝ} (ht : t ≤ 1 / 2) (hxy : x + y ≤ 1) :
    halfRound t x + halfRound t y ≤ 1 := by
  unfold halfRound
  split_ifs <;> norm_num at * <;> linarith

theorem halfRound_indicator {y : ℝ} (_hy0 : 0 ≤ y) (_hy1 : y ≤ 1) :
    (Ioc (0 : ℝ) (1 / 2)).indicator (fun t => halfRound t y) =
      (Ioc (0 : ℝ) (min y (1 / 2))).indicator (fun _ => (1 / 2 : ℝ)) +
      (Ioc (max (1 - y) 0) (1 / 2)).indicator (fun _ => (1 / 2 : ℝ)) := by
  funext t
  simp only [Pi.add_apply, Set.indicator_apply, Set.mem_Ioc, le_min_iff, max_lt_iff,
    halfRound]
  split_ifs <;> norm_num at * <;> grind

theorem integrable_interval_half (a b : ℝ) :
    Integrable ((Ioc a b).indicator (fun _ : ℝ => (1 / 2 : ℝ))) volume := by
  exact (integrableOn_const (measure_Ioc_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ)) (Ioc a b) volume).integrable_indicator
      measurableSet_Ioc

theorem integrable_halfRound {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    IntegrableOn (fun t => halfRound t y) (Ioc (0 : ℝ) (1 / 2)) volume := by
  rw [← integrable_indicator_iff measurableSet_Ioc, halfRound_indicator hy0 hy1]
  exact (integrable_interval_half 0 (min y (1 / 2))).add
    (integrable_interval_half (max (1 - y) 0) (1 / 2))

theorem integral_halfRound {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (∫ t in Ioc (0 : ℝ) (1 / 2), halfRound t y) = y / 2 := by
  rw [← integral_indicator measurableSet_Ioc, halfRound_indicator hy0 hy1]
  simp only [Pi.add_apply]
  rw [integral_add (integrable_interval_half 0 (min y (1 / 2)))
      (integrable_interval_half (max (1 - y) 0) (1 / 2)),
    integral_indicator_const _ measurableSet_Ioc,
    integral_indicator_const _ measurableSet_Ioc]
  simp only [Real.volume_real_Ioc, smul_eq_mul, sub_zero]
  by_cases h : y ≤ 1 / 2
  · rw [min_eq_left h, max_eq_left hy0, max_eq_left (by linarith : 0 ≤ 1 - y),
      max_eq_right (by linarith : 1 / 2 - (1 - y) ≤ 0)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2),
      max_eq_left (by linarith : 0 ≤ 1 - y),
      max_eq_left (by linarith : 0 ≤ 1 / 2 - (1 - y))]
    ring

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.FractionalBasics

open Set Matrix

namespace LovaszSchrijver.Defect.LSFresh

variable {V : Type} [Fintype V]

omit [Fintype V] in
theorem frac_zero (G : SimpleGraph V) : (0 : V → ℝ) ∈ FRAC G := by
  constructor
  · intro i
    norm_num
  · intro i j hij
    norm_num

omit [Fintype V] in
theorem frac_coord_bounds (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    {x : V → ℝ} (hx : x ∈ FRAC G) (i : V) : 0 ≤ x i ∧ x i ≤ 1 := by
  obtain ⟨j, hij⟩ := hG i
  exact ⟨hx.1 i, le_trans (le_add_of_nonneg_right (hx.1 j)) (hx.2 i j hij)⟩

omit [Fintype V] in
theorem frac_closed (G : SimpleGraph V) : IsClosed (FRAC G) := by
  simp only [FRAC, Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le ((continuous_apply i).add (continuous_apply j)) continuous_const)

omit [Fintype V] in
theorem frac_compact (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) :
    IsCompact (FRAC G) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : V → ℝ) 1)).of_isClosed_subset
    (frac_closed G)
  intro x hx
  exact ⟨fun i => (frac_coord_bounds G hG hx i).1,
    fun i => (frac_coord_bounds G hG hx i).2⟩

omit [Fintype V] in
theorem frac_convex (G : SimpleGraph V) : Convex ℝ (FRAC G) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · intro i j hij
    change a * x i + b * y i + (a * x j + b * y j) ≤ 1
    nlinarith [mul_nonneg ha (sub_nonneg.mpr (hx.2 i j hij)),
      mul_nonneg hb (sub_nonneg.mpr (hy.2 i j hij))]

theorem objective_continuous (a : V → ℝ) : Continuous (fun x => a ⬝ᵥ x) := by
  unfold dotProduct
  fun_prop

theorem exists_frac_maximizer (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) : ∃ x, IsFRACMaximizer G a x := by
  obtain ⟨x, hx, hm⟩ := (frac_compact G hG).exists_isMaxOn ⟨0, frac_zero G⟩
    (objective_continuous a).continuousOn
  exact ⟨x, hx, fun y hy => hm hy⟩

theorem defect_of_maximizer (G : SimpleGraph V) (a : V → ℝ) (b : ℝ)
    {x : V → ℝ} (hx : IsFRACMaximizer G a x) :
    IsDefect G a b (2 * (a ⬝ᵥ x - b)) := by
  refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
  rintro s ⟨y, hy, rfl⟩
  linarith [hx.2 y hy]

theorem defect_eq_of_maximizer (G : SimpleGraph V) (a : V → ℝ) (b r : ℝ)
    (hr : IsDefect G a b r) {x : V → ℝ} (hx : IsFRACMaximizer G a x) :
    r = 2 * (a ⬝ᵥ x - b) :=
  hr.unique (defect_of_maximizer G a b hx)

variable [DecidableEq V]

omit [Fintype V] in
theorem chi_mem_stab (G : SimpleGraph V) (A : Finset V)
    (hA : G.IsIndepSet (A : Set V)) : chi A ∈ STAB G :=
  subset_convexHull ℝ _ ⟨A, hA, rfl⟩

theorem valid_singleton_bound (G : SimpleGraph V) (a : V → ℝ) (b : ℝ)
    (h : Valid (STAB G) a b) (i : V) : a i ≤ b := by
  have hi := h (chi {i}) (chi_mem_stab G {i} (by simp))
  simpa [chi, dotProduct] using hi

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.HalfIntegralOptimum

open Set MeasureTheory Matrix

namespace LovaszSchrijver.Defect.LSFresh

variable {V : Type} [Fintype V]

def IsHalfIntegral (x : V → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1 / 2 ∨ x i = 1

theorem halfIntegral_finite : {x : V → ℝ | IsHalfIntegral x}.Finite := by
  have h : ∀ _ : V, ({0, 1 / 2, 1} : Set ℝ).Finite := fun _ => by simp
  simpa [IsHalfIntegral] using Set.Finite.pi' h

omit [Fintype V] in
theorem halfRound_frac (G : SimpleGraph V) {y : V → ℝ} (hy : y ∈ FRAC G)
    {t : ℝ} (ht : t ≤ 1 / 2) : (fun i => halfRound t (y i)) ∈ FRAC G := by
  exact ⟨fun i => halfRound_nonneg t (y i),
    fun i j hij => halfRound_edge ht (hy.2 i j hij)⟩

theorem integral_rounded_objective (G : SimpleGraph V)
    (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) {y : V → ℝ} (hy : y ∈ FRAC G) :
    (∫ t in Ioc (0 : ℝ) (1 / 2), a ⬝ᵥ (fun i => halfRound t (y i))) =
      (a ⬝ᵥ y) / 2 := by
  simp only [dotProduct]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    have he (i : V) := integral_halfRound (frac_coord_bounds G hG hy i).1
      (frac_coord_bounds G hG hy i).2
    simp_rw [he]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  · intro i hi
    exact (integrable_halfRound (frac_coord_bounds G hG hy i).1
      (frac_coord_bounds G hG hy i).2).const_mul (a i)

theorem exists_halfIntegral_maximizer (G : SimpleGraph V)
    (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) :
    ∃ x, IsFRACMaximizer G a x ∧ IsHalfIntegral x := by
  have hf : {x : V → ℝ | x ∈ FRAC G ∧ IsHalfIntegral x}.Finite :=
    halfIntegral_finite.subset fun _ hx => hx.2
  have hn : {x : V → ℝ | x ∈ FRAC G ∧ IsHalfIntegral x}.Nonempty :=
    ⟨0, frac_zero G, fun _ => Or.inl rfl⟩
  obtain ⟨x, hx, hm⟩ := hf.isCompact.exists_isMaxOn hn
    (objective_continuous a).continuousOn
  refine ⟨x, ⟨hx.1, ?_⟩, hx.2⟩
  intro y hy
  have hi : IntegrableOn (fun t => a ⬝ᵥ (fun i => halfRound t (y i)))
      (Ioc (0 : ℝ) (1 / 2)) volume := by
    unfold dotProduct
    exact integrable_finsetSum _ fun i _ =>
      (integrable_halfRound (frac_coord_bounds G hG hy i).1
        (frac_coord_bounds G hG hy i).2).const_mul (a i)
  have hh := setIntegral_mono_on hi (integrableOn_const measure_Ioc_lt_top.ne)
    measurableSet_Ioc (fun t (ht : t ∈ Ioc (0 : ℝ) (1 / 2)) =>
      hm ⟨halfRound_frac G hy ht.2, fun i => halfRound_values t (y i)⟩)
  rw [integral_rounded_objective G hG a hy, setIntegral_const] at hh
  norm_num [Real.volume_real_Ioc, smul_eq_mul] at hh
  linarith

theorem defect_is_integer (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℕ) (b : ℕ) (r : ℝ) (hr : IsDefect G (fun i => (a i : ℝ)) b r) :
    ∃ z : ℤ, r = z := by
  obtain ⟨x, hx, hh⟩ := exists_halfIntegral_maximizer G hG (fun i => (a i : ℝ))
  have hz : ∀ i, ∃ z : ℤ, 2 * x i = z := by
    intro i
    rcases hh i with h | h | h
    · exact ⟨0, by rw [h]; norm_num⟩
    · exact ⟨1, by rw [h]; norm_num⟩
    · exact ⟨2, by rw [h]; norm_num⟩
  choose z hz using hz
  refine ⟨(∑ i, (a i : ℤ) * z i) - 2 * b, ?_⟩
  rw [defect_eq_of_maximizer G (fun i => (a i : ℝ)) b r hr hx]
  push_cast
  simp only [dotProduct, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hz i]
  ring

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.DefectLowerBound

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V]

lemma defect_le_index_mul (G : SimpleGraph V) (hG : ∀ i, ∃ j, G.Adj i j)
    (a : V → ℕ) (b : ℕ) (r : ℝ) (hr : IsDefect G (fun i => (a i : ℝ)) b r)
    (k : ℕ) (hk : Valid (NG k G) (fun i => (a i : ℝ)) b) : r ≤ k * b := by
  classical
  obtain ⟨y, hy, hh⟩ := exists_halfIntegral_maximizer G hG (fun i => (a i : ℝ))
  let U := Finset.univ.filter (fun i => y i = 1)
  let W := Finset.univ.filter (fun i => y i = 1 / 2)
  have hUmem (i : V) : i ∈ U ↔ y i = 1 := by simp [U]
  have hWmem (i : V) : i ∈ W ↔ y i = 1 / 2 := by simp [W]
  have hdis : Disjoint U W := Finset.disjoint_left.mpr (by
    intro i hi hw
    have h1 := (hUmem i).mp hi
    have h2 := (hWmem i).mp hw
    linarith)
  have hU : G.IsIndepSet (U : Set V) := by
    intro i hi j hj hij hadj
    have he := hy.1.2 i j hadj
    rw [(hUmem i).mp hi, (hUmem j).mp hj] at he
    norm_num at he
  have hUW : ∀ i ∈ U, ∀ j ∈ W, ¬G.Adj i j := by
    intro i hi j hj hadj
    have he := hy.1.2 i j hadj
    rw [(hUmem i).mp hi, (hWmem j).mp hj] at he
    norm_num at he
  let p : V → ℝ := fun i => if i ∈ W then 1 / (k + 2 : ℝ) else 0
  have hden : 0 < (k : ℝ) + 2 := by positivity
  have hx : facePoint U p ∈ NG k G := faceCube_Niter G U W hdis hU hUW k p
    (by intro i; dsimp [p]; split_ifs <;> positivity)
    (by intro i; dsimp [p]; split_ifs <;> first | exact le_rfl | positivity)
    (by intro i hi; simp [p, hi])
  have hpw : ∀ i, 2 * y i ≤ (k + 2 : ℝ) * facePoint U p i := by
    intro i
    rcases hh i with hi | hi | hi
    · simp [facePoint, p, U, W, hi]
    · simp [facePoint, p, U, W, hi, ne_of_gt hden]
    · simp [facePoint, p, U, hi]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hpw i) (Nat.cast_nonneg (a i)))
  have hs' : 2 * ((fun i => (a i : ℝ)) ⬝ᵥ y) ≤
      (k + 2 : ℝ) * ((fun i => (a i : ℝ)) ⬝ᵥ facePoint U p) := by
    simpa only [dotProduct, Finset.mul_sum, mul_left_comm] using hs
  have hv := hk _ hx
  have he := defect_eq_of_maximizer G (fun i => (a i : ℝ)) b r hr hy
  nlinarith

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.ValidityPersistence

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

lemma valid_homogeneous (G : SimpleGraph V) (hG : ∀ i, ∃ j, G.Adj i j)
    (t : ℕ) (a : V → ℝ) (b : ℝ) (hv : Valid (NG t G) a b) :
    linForm a b ∈ dualCone (Niter t (FR G)) := by
  intro x hx
  obtain ⟨hn, _, hb⟩ := Niter_FR_bounds G hG t hx
  have h0 : 0 ≤ x none := le_trans (hn (Classical.choice inferInstance)) (hb _)
  by_cases hz : x none = 0
  · have he : x = 0 := by
      funext o
      cases o with
      | none => exact hz
      | some i => exact le_antisymm (by simpa [hz] using hb i) (hn i)
    simp [he]
  · have hp : 0 < x none := lt_of_le_of_ne h0 (Ne.symm hz)
    let y : V → ℝ := fun i => x (some i) / x none
    have hy : y ∈ NG t G := by
      have hs := Niter_smul G t (x none)⁻¹ (inv_nonneg.mpr h0) hx
      have he : (x none)⁻¹ • x = hom y := by
        funext o
        cases o <;> simp [hom, y, smul_eq_mul, hz, div_eq_mul_inv, mul_comm]
      rwa [he] at hs
    have hvy := hv y hy
    have hd : a ⬝ᵥ y = (a ⬝ᵥ fun i => x (some i)) / x none := by
      simp [dotProduct, y, mul_div_assoc, Finset.sum_div]
    rw [hd, div_le_iff₀ hp] at hvy
    rw [linForm_dot]
    linarith

lemma valid_NG_succ (G : SimpleGraph V) (hG : ∀ i, ∃ j, G.Adj i j)
    (t : ℕ) (a : V → ℝ) (b : ℝ) (hv : Valid (NG t G) a b) :
    Valid (NG (t + 1) G) a b := by
  intro x hx
  have h := dual_N1 _ (valid_homogeneous G hG t a b hv) (hom x) hx
  rw [linForm_dot] at h
  simpa [hom] using (sub_nonneg.mp h)

lemma valid_NG_mono (G : SimpleGraph V) (hG : ∀ i, ∃ j, G.Adj i j)
    {t s : ℕ} (hts : t ≤ s) (a : V → ℝ) (b : ℝ) (hv : Valid (NG t G) a b) :
    Valid (NG s G) a b := by
  induction s, hts using Nat.le_induction with
  | base => exact hv
  | succ s hs ih => exact valid_NG_succ G hG s a b ih

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.MatrixEdges

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V]

lemma M_entry_nonneg (G : SimpleGraph V) (t : ℕ)
    {Y : Matrix (Option V) (Option V) ℝ} (hY : Y ∈ M (Niter t (FR G)) Q) (i j : V) :
    0 ≤ Y (some i) (some j) := by
  have h := hY.2.2 _ (dual_Niter _ (FR_coordinate_dual G i) t) _ (ei_dual_Q j)
  simpa [mulVec_single_one, Matrix.col, Matrix.transpose] using h

lemma M_edge_zero (G : SimpleGraph V) (t : ℕ)
    {Y : Matrix (Option V) (Option V) ℝ} (hY : Y ∈ M (Niter t (FR G)) Q)
    {i j : V} (hij : G.Adj i j) : Y (some j) (some i) = 0 := by
  have h := hY.2.2 _ (dual_Niter _ (FR_edge_dual G hij) t) _ (ei_dual_Q i)
  simp only [sub_dotProduct, single_dotProduct, one_mul, mulVec_single_one] at h
  change 0 ≤ Y none (some i) - Y (some i) (some i) - Y (some j) (some i) at h
  rw [hY.2.1] at h
  linarith [M_entry_nonneg G t hY j i]

lemma deletion_dot (a x : V → ℝ) (i : V) :
    deletion a i ⬝ᵥ x = a ⬝ᵥ x - a i * x i := by
  classical
  have he : deletion a i = a - Pi.single i (a i) := by
    funext j
    by_cases h : j = i <;> simp [deletion, h]
  rw [he, sub_dotProduct, single_dotProduct]

lemma contraction_column_dot (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℝ) (i : V) (z : V → ℝ) (hz : ∀ j, G.Adj i j → z j = 0) :
    contraction G a i ⬝ᵥ z = deletion a i ⬝ᵥ z := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : j = i
  · simp [contraction, deletion, he]
  · by_cases ha : G.Adj i j
    · simp [contraction, deletion, he, ha, hz j ha]
    · simp [contraction, deletion, he, ha]

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.OneRound

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

lemma valid_one_round (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ i, ∃ j, G.Adj i j) (a : V → ℝ) (b : ℝ) (i : V) (t : ℕ)
    (hd : Valid (NG t G) (deletion a i) b)
    (hc : Valid (NG t G) (contraction G a i) (b - a i)) :
    Valid (NG (t + 1) G) a b := by
  intro x hx
  obtain ⟨Y, hY, hcol⟩ := hx
  have hdc := valid_homogeneous G hG t _ _ hd
  have hcc := valid_homogeneous G hG t _ _ hc
  have h1 := hY.2.2 _ hdc _ (fi_dual_Q i)
  have h2 := hY.2.2 _ hcc _ (ei_dual_Q i)
  rw [mulVec_sub, dotProduct_sub, hcol] at h1
  rw [linForm_dot, linForm_dot] at h1
  rw [linForm_dot] at h2
  have hz : ∀ j, G.Adj i j → (Y *ᵥ Pi.single (some i) 1) (some j) = 0 := by
    intro j hij
    simpa [mulVec_single_one, Matrix.col, Matrix.transpose] using M_edge_zero G t hY hij
  rw [contraction_column_dot G a i _ hz] at h2
  have he : (Y *ᵥ Pi.single (some i) 1) none = x i := by
    have h := congrFun hcol (some i)
    simp only [mulVec_single_one] at h ⊢
    change Y none (some i) = x i
    change Y (some i) none = x i at h
    rw [← h]
    exact congrFun (congrFun hY.1 (some i)) none
  simp only [hom, Option.elim_none, Option.elim_some, mul_one] at h1
  rw [he] at h1 h2
  rw [deletion_dot] at h1
  nlinarith

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.ModifiedPoints

open Set Matrix

namespace LovaszSchrijver.Defect.LSFresh

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem update_zero_frac (G : SimpleGraph V) {x : V → ℝ} (hx : x ∈ FRAC G)
    (i : V) : Function.update x i 0 ∈ FRAC G := by
  constructor
  · intro j
    by_cases hj : j = i
    · subst j
      simp
    · simpa [Function.update_of_ne hj] using hx.1 j
  · intro j l hjl
    by_cases hj : j = i <;> by_cases hl : l = i
    · subst j
      subst l
      exact (G.loopless.irrefl i hjl).elim
    · subst j
      simp only [Function.update_self, Function.update_of_ne hl, zero_add]
      linarith [hx.2 i l hjl, hx.1 i]
    · subst l
      simp only [Function.update_self, Function.update_of_ne hj, add_zero]
      linarith [hx.2 j i hjl, hx.1 i]
    · simpa [Function.update_of_ne hj, Function.update_of_ne hl] using hx.2 j l hjl

theorem deletion_objective (a x : V → ℝ) (i : V) :
    a ⬝ᵥ Function.update x i 0 = deletion a i ⬝ᵥ x := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : j = i
  · subst j
    simp [deletion]
  · simp [deletion, Function.update_of_ne he]

noncomputable def contractPoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (i : V) : V → ℝ :=
  fun j => if j = i then 1 else if G.Adj i j then 0 else x j

omit [Fintype V] in
theorem contractPoint_at (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (i : V) : contractPoint G x i i = 1 := by simp [contractPoint]

omit [Fintype V] in
theorem contractPoint_frac (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ v, ∃ w, G.Adj v w) {x : V → ℝ} (hx : x ∈ FRAC G) (i : V) :
    contractPoint G x i ∈ FRAC G := by
  constructor
  · intro j
    dsimp [contractPoint]
    split_ifs <;> first | positivity | exact hx.1 j
  · intro j l hjl
    by_cases hj : j = i
    · subst j
      have hl : l ≠ i := by intro h; subst l; exact G.loopless.irrefl i hjl
      simp [contractPoint, hl, hjl]
    · by_cases hl : l = i
      · subst l
        simp [contractPoint, hj, hjl.symm]
      · simp only [contractPoint, if_neg hj, if_neg hl]
        split_ifs
        · norm_num
        · simpa using (frac_coord_bounds G hG hx l).2
        · simpa using (frac_coord_bounds G hG hx j).2
        · exact hx.2 j l hjl

theorem contraction_objective (G : SimpleGraph V) [DecidableRel G.Adj]
    (a x : V → ℝ) (i : V) :
    a ⬝ᵥ contractPoint G x i = a i + contraction G a i ⬝ᵥ x := by
  have he (j : V) : a j * contractPoint G x i j =
      (if j = i then a i else 0) + contraction G a i j * x j := by
    by_cases hj : j = i
    · subst j
      simp [contractPoint, contraction]
    · by_cases hij : G.Adj i j <;> simp [contractPoint, contraction, hj, hij]
  simp only [dotProduct, he, Finset.sum_add_distrib]
  simp

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.StrictDefects

open Set Matrix

namespace LovaszSchrijver.Defect.LSFresh

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem maximizer_of_defect_value (G : SimpleGraph V) (a : V → ℝ) (b r : ℝ)
    (hr : IsDefect G a b r) {x : V → ℝ} (hx : x ∈ FRAC G)
    (he : 2 * (a ⬝ᵥ x - b) = r) : IsFRACMaximizer G a x := by
  refine ⟨hx, ?_⟩
  intro y hy
  have hh := hr.2 ⟨y, hy, rfl⟩
  linarith

theorem strict_modified_defects (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) (b r : ℝ)
    (hr : IsDefect G a b r) (i : V)
    (hi : ∀ y, IsFRACMaximizer G a y → y i = 1 / 2) :
    (∃ r₁, IsDefect G (deletion a i) b r₁ ∧ r₁ < r) ∧
    (∃ r₂, IsDefect G (contraction G a i) (b - a i) r₂ ∧ r₂ < r) := by
  constructor
  · obtain ⟨x, hx⟩ := exists_frac_maximizer G hG (deletion a i)
    refine ⟨2 * (deletion a i ⬝ᵥ x - b), defect_of_maximizer G _ b hx, ?_⟩
    have hmap := update_zero_frac G hx.1 i
    have he := deletion_objective a x i
    have hle := hr.2 ⟨Function.update x i 0, hmap, rfl⟩
    by_contra hn
    have heq : 2 * (a ⬝ᵥ Function.update x i 0 - b) = r := by
      push Not at hn
      linarith
    have hh := hi _ (maximizer_of_defect_value G a b r hr hmap heq)
    norm_num at hh
  · obtain ⟨x, hx⟩ := exists_frac_maximizer G hG (contraction G a i)
    refine ⟨2 * (contraction G a i ⬝ᵥ x - (b - a i)),
      defect_of_maximizer G _ (b - a i) hx, ?_⟩
    have hmap := contractPoint_frac G hG hx.1 i
    have he := contraction_objective G a x i
    have hle := hr.2 ⟨contractPoint G x i, hmap, rfl⟩
    by_contra hn
    have heq : 2 * (a ⬝ᵥ contractPoint G x i - b) = r := by
      push Not at hn
      linarith
    have hh := hi _ (maximizer_of_defect_value G a b r hr hmap heq)
    rw [contractPoint_at] at hh
    norm_num at hh

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.ModifiedValidity

open Set Matrix

namespace LovaszSchrijver.Defect.LSFresh

variable {V : Type} [Fintype V] [DecidableEq V]

theorem valid_of_chi (G : SimpleGraph V) (a : V → ℝ) (b : ℝ)
    (h : ∀ A : Finset V, G.IsIndepSet (A : Set V) → a ⬝ᵥ chi A ≤ b) :
    Valid (STAB G) a b := by
  apply convexHull_min
  · rintro x ⟨A, hA, rfl⟩
    exact h A hA
  · intro x hx y hy s t hs ht hst
    change a ⬝ᵥ (s • x + t • y) ≤ b
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    calc
      s * (a ⬝ᵥ x) + t * (a ⬝ᵥ y) ≤ s * b + t * b :=
        add_le_add (mul_le_mul_of_nonneg_left hx hs) (mul_le_mul_of_nonneg_left hy ht)
      _ = b := by rw [← add_mul, hst, one_mul]

theorem valid_deletion (G : SimpleGraph V) (a : V → ℝ) (b : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hvalid : Valid (STAB G) a b) (i : V) :
    Valid (STAB G) (deletion a i) b := by
  apply valid_of_chi
  intro A hA
  apply le_trans _ (hvalid _ (chi_mem_stab G A hA))
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [deletion, Function.update_self, zero_mul]
    apply mul_nonneg (ha i)
    simp only [chi]
    split_ifs <;> norm_num
  · simp [deletion, Function.update_of_ne hji]

theorem valid_contraction (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℝ) (b : ℝ) (hvalid : Valid (STAB G) a b) (i : V) :
    Valid (STAB G) (contraction G a i) (b - a i) := by
  classical
  apply valid_of_chi
  intro A hA
  let B : Finset V := insert i (A.filter fun j => j ≠ i ∧ ¬ G.Adj i j)
  have hB : G.IsIndepSet (B : Set V) := by
    rw [SimpleGraph.isIndepSet_iff] at hA ⊢
    intro j hj l hl hne hadj
    by_cases hji : j = i
    · subst j
      have hli : l ≠ i := Ne.symm hne
      have hh : l ∈ A.filter (fun j => j ≠ i ∧ ¬ G.Adj i j) := by
        simpa [B, hli] using hl
      exact (Finset.mem_filter.mp hh).2.2 hadj
    · by_cases hli : l = i
      · subst l
        have hh : j ∈ A.filter (fun j => j ≠ i ∧ ¬ G.Adj i j) := by
          simpa [B, hji] using hj
        exact (Finset.mem_filter.mp hh).2.2 hadj.symm
      · have hjA : j ∈ A := (show j ∈ A ∧ ¬ G.Adj i j by simpa [B, hji] using hj).1
        have hlA : l ∈ A := (show l ∈ A ∧ ¬ G.Adj i l by simpa [B, hli] using hl).1
        exact hA hjA hlA hne hadj
  have he : contractPoint G (chi A) i = chi B := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [contractPoint, chi, B]
    · by_cases hij : G.Adj i j <;> simp [contractPoint, chi, B, hji, hij]
  have hv := hvalid _ (chi_mem_stab G B hB)
  rw [← he, contraction_objective] at hv
  linarith

theorem nat_coefficient_le_rhs (G : SimpleGraph V) (a : V → ℕ) (b : ℕ)
    (hvalid : Valid (STAB G) (fun j => (a j : ℝ)) b) (i : V) : a i ≤ b := by
  exact_mod_cast valid_singleton_bound G (fun j => (a j : ℝ)) b hvalid i

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.FiniteAvoidance

open Set Filter
open scoped Topology

namespace LovaszSchrijver.Defect.LSFresh

variable {V : Type} [Fintype V]

theorem convex_avoid_coordinates (F : Set (V → ℝ)) (hF : Convex ℝ F)
    (hne : F.Nonempty) (c : V → ℝ) (hw : ∀ i, ∃ x ∈ F, x i ≠ c i) :
    ∃ x ∈ F, ∀ i, x i ≠ c i := by
  classical
  have aux (s : Finset V) : ∃ x ∈ F, ∀ i ∈ s, x i ≠ c i := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, by simp⟩
    | @insert i s his ih =>
      obtain ⟨z, hz, hzs⟩ := ih
      by_cases hzi : z i = c i
      · obtain ⟨w, hwF, hwi⟩ := hw i
        have hav : ∀ᶠ t : ℝ in 𝓝 0,
            ∀ j ∈ s, (1 - t) * z j + t * w j ≠ c j := by
          apply (Filter.eventually_all_finset s).2
          intro j hj
          have hc : Continuous (fun t : ℝ => (1 - t) * z j + t * w j) := by
            fun_prop
          have he := hc.tendsto 0
          simp only [sub_zero, one_mul, zero_mul, add_zero] at he
          exact he.eventually (eventually_ne_nhds (hzs j hj))
        obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hav
        let t : ℝ := min δ 1 / 2
        have ht0 : 0 < t := by dsimp [t]; positivity
        have htδ : t < δ := by
          have hm := min_le_left δ 1
          dsimp [t]
          linarith
        have ht1 : t ≤ 1 := by
          have hm := min_le_right δ 1
          dsimp [t]
          linarith
        refine ⟨(1 - t) • z + t • w,
          hF hz hwF (sub_nonneg.mpr ht1) ht0.le (by ring), ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          change (1 - t) * z i + t * w i ≠ c i
          rw [hzi]
          intro he
          have hh : t * (w i - c i) = 0 := by nlinarith
          exact hwi (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left ht0.ne'))
        · exact hball (by simpa [Real.dist_eq, abs_of_pos ht0] using htδ) j hj
      · exact ⟨z, hz, fun j hj => by
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hzi
          · exact hzs j hj⟩
  obtain ⟨x, hx, hh⟩ := aux Finset.univ
  exact ⟨x, hx, fun i => hh i (Finset.mem_univ i)⟩

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.ReverseSlack

open Set Filter
open scoped Topology

namespace LovaszSchrijver.Defect.LSFresh

variable {V : Type} [Fintype V]

theorem exists_reverse_frac (G : SimpleGraph V) {z : V → ℝ} (hz : z ∈ FRAC G)
    (u : V → ℝ) (hzero : ∀ i, z i = 0 → u i = 0)
    (hedge : ∀ i j, G.Adj i j → z i + z j = 1 → u i + u j = 1) :
    ∃ ε : ℝ, 0 < ε ∧ z + ε • (z - u) ∈ FRAC G := by
  have hc (i : V) : Continuous (fun t : ℝ => z i + t * (z i - u i)) := by fun_prop
  have hcoord (i : V) : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ z i + t * (z i - u i) := by
    by_cases hi : z i = 0
    · filter_upwards [] with t
      simp [hi, hzero i hi]
    · have hp : 0 < z i := lt_of_le_of_ne (hz.1 i) (Ne.symm hi)
      have ht := (hc i).tendsto 0
      simp only [zero_mul, add_zero] at ht
      exact (ht.eventually (eventually_gt_nhds hp)).mono fun _ h => h.le
  have hpair (i j : V) : ∀ᶠ t : ℝ in 𝓝 0,
      G.Adj i j → (z i + t * (z i - u i)) + (z j + t * (z j - u j)) ≤ 1 := by
    by_cases hij : G.Adj i j
    · by_cases he : z i + z j = 1
      · filter_upwards [] with t
        intro h
        have hu := hedge i j h he
        calc
          _ = (z i + z j) + t * ((z i + z j) - (u i + u j)) := by ring
          _ ≤ 1 := by rw [he, hu]; norm_num
      · have hp : z i + z j < 1 := lt_of_le_of_ne (hz.2 i j hij) he
        have ht := ((hc i).add (hc j)).tendsto 0
        simp only [Pi.add_apply, zero_mul, add_zero] at ht
        exact (ht.eventually (eventually_lt_nhds hp)).mono fun _ h _ => h.le
    · exact Filter.Eventually.of_forall fun _ h => (hij h).elim
  have hall : ∀ᶠ t : ℝ in 𝓝 0, z + t • (z - u) ∈ FRAC G := by
    have h1 := Filter.eventually_all.mpr hcoord
    have h2 := Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hpair i)
    filter_upwards [h1, h2] with t ht1 ht2
    exact ⟨ht1, ht2⟩
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨δ / 2, by positivity, hd ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ / 2)]
  linarith

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.FixedHalf

open Set Matrix

namespace LovaszSchrijver.Defect.LSFresh

variable {V : Type} [Fintype V]

theorem maximizer_face_convex (G : SimpleGraph V) (a : V → ℝ) :
    Convex ℝ {x | IsFRACMaximizer G a x} := by
  intro x hx y hy s t hs ht hst
  refine ⟨frac_convex G hx.1 hy.1 hs ht hst, ?_⟩
  intro w hw
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
  simp only [smul_eq_mul]
  calc
    a ⬝ᵥ w = s * (a ⬝ᵥ w) + t * (a ⬝ᵥ w) := by rw [← add_mul, hst, one_mul]
    _ ≤ s * (a ⬝ᵥ x) + t * (a ⬝ᵥ y) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 w hw) hs)
        (mul_le_mul_of_nonneg_left (hy.2 w hw) ht)

variable [DecidableEq V]

theorem exists_fixed_half (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (b : ℝ) (hvalid : Valid (STAB G) a b)
    (hgap : ∃ y ∈ FRAC G, b < a ⬝ᵥ y) :
    ∃ i : V, ∀ y, IsFRACMaximizer G a y → y i = 1 / 2 := by
  classical
  by_contra hn
  push Not at hn
  have hf : {x | IsFRACMaximizer G a x}.Nonempty := exists_frac_maximizer G hG a
  obtain ⟨z, hz, hzh⟩ := convex_avoid_coordinates _ (maximizer_face_convex G a) hf
    (fun _ => (1 / 2 : ℝ)) hn
  let A : Finset V := Finset.univ.filter fun i => 1 / 2 < z i
  have hA : G.IsIndepSet (A : Set V) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro i hi j hj hij hadj
    have hi' : 1 / 2 < z i := (Finset.mem_filter.mp hi).2
    have hj' : 1 / 2 < z j := (Finset.mem_filter.mp hj).2
    linarith [hz.1.2 i j hadj]
  have hchi (i : V) : chi A i = if 1 / 2 < z i then 1 else 0 := by
    simp [chi, A]
  have hzero (i : V) (hi : z i = 0) : chi A i = 0 := by
    rw [hchi, hi]
    norm_num
  have hedge (i j : V) (_hij : G.Adj i j) (he : z i + z j = 1) :
      chi A i + chi A j = 1 := by
    rw [hchi, hchi]
    have hi := hzh i
    have hj := hzh j
    split_ifs <;> norm_num <;> grind
  obtain ⟨ε, hε, hrev⟩ := exists_reverse_frac G hz.1 (chi A) hzero hedge
  have hmax := hz.2 _ hrev
  simp only [dotProduct_add, dotProduct_smul, dotProduct_sub, smul_eq_mul] at hmax
  have hv := hvalid (chi A) (chi_mem_stab G A hA)
  obtain ⟨y, hy, hby⟩ := hgap
  have hzy := hz.2 y hy
  nlinarith

theorem exists_fixed_half_of_defect (G : SimpleGraph V)
    (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) (b r : ℝ)
    (hvalid : Valid (STAB G) a b) (hr : IsDefect G a b r) (hr0 : 0 < r) :
    ∃ i : V, ∀ y, IsFRACMaximizer G a y → y i = 1 / 2 := by
  apply exists_fixed_half G hG a b hvalid
  obtain ⟨y, hy, he⟩ := hr.1
  exact ⟨y, hy, by linarith⟩

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.DefectInduction

namespace LovaszSchrijver.Defect.LSFresh
open Matrix
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]

lemma valid_NG_of_nonpositive_defect (G : SimpleGraph V) (hG : ∀ i, ∃ j, G.Adj i j)
    (a : V → ℝ) (b r : ℝ) (hr : IsDefect G a b r) (hr0 : r ≤ 0) (t : ℕ) :
    Valid (NG t G) a b := by
  apply valid_NG_mono G hG (Nat.zero_le t) a b
  intro x hx
  have h := hr.2 ⟨x, hx, rfl⟩
  linarith

omit [Fintype V] [DecidableEq V] [Nonempty V] in
lemma integer_le_of_lt_succ (r : ℝ) (R : ℕ) (hi : ∃ z : ℤ, r = z)
    (hr : r < (R : ℝ) + 1) : r ≤ R := by
  obtain ⟨z, rfl⟩ := hi
  have hz : z < (R : ℤ) + 1 := by exact_mod_cast hr
  have hz' : z ≤ (R : ℤ) := by omega
  exact_mod_cast hz'

lemma valid_NG_of_defect_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ i, ∃ j, G.Adj i j) (R : ℕ) (a : V → ℕ) (b : ℕ) (r : ℝ)
    (hv : Valid (STAB G) (fun i => (a i : ℝ)) b)
    (hr : IsDefect G (fun i => (a i : ℝ)) b r) (hR : r ≤ R) :
    Valid (NG R G) (fun i => (a i : ℝ)) b := by
  induction R generalizing a b r with
  | zero => exact valid_NG_of_nonpositive_defect G hG _ _ r hr (by simpa using hR) 0
  | succ R ih =>
    by_cases hr0 : r ≤ 0
    · exact valid_NG_of_nonpositive_defect G hG _ _ r hr hr0 (R + 1)
    have hrp : 0 < r := lt_of_not_ge hr0
    obtain ⟨i, hi⟩ := exists_fixed_half_of_defect G hG (fun j => (a j : ℝ)) b r hv hr hrp
    obtain ⟨⟨rd, hrd, hdr⟩, ⟨rc, hrc, hcr⟩⟩ :=
      strict_modified_defects G hG (fun j => (a j : ℝ)) b r hr i hi
    let ad : V → ℕ := Function.update a i 0
    let ac : V → ℕ := fun j => if j = i ∨ G.Adj i j then 0 else a j
    have hed : (fun j => (ad j : ℝ)) = deletion (fun j => (a j : ℝ)) i := by
      funext j
      by_cases h : j = i <;> simp [ad, deletion, h]
    have hec : (fun j => (ac j : ℝ)) = contraction G (fun j => (a j : ℝ)) i := by
      funext j
      simp [ac, contraction]
    have hai : a i ≤ b := nat_coefficient_le_rhs G a b hv i
    have heb : ((b - a i : ℕ) : ℝ) = (b : ℝ) - a i := Nat.cast_sub hai
    have hddef : IsDefect G (fun j => (ad j : ℝ)) b rd := by rwa [hed]
    have hcdef : IsDefect G (fun j => (ac j : ℝ)) (b - a i : ℕ) rc := by rwa [hec, heb]
    have hdR : rd ≤ R := integer_le_of_lt_succ rd R (defect_is_integer G hG ad b rd hddef)
      (by push_cast at hR; linarith)
    have hcR : rc ≤ R := integer_le_of_lt_succ rc R (defect_is_integer G hG ac (b - a i) rc hcdef)
      (by push_cast at hR; linarith)
    have hdv : Valid (STAB G) (fun j => (ad j : ℝ)) b := by
      rw [hed]
      exact valid_deletion G _ _ (fun j => Nat.cast_nonneg (a j)) hv i
    have hcv : Valid (STAB G) (fun j => (ac j : ℝ)) (b - a i : ℕ) := by
      rw [hec, heb]
      exact valid_contraction G _ _ hv i
    have hd := ih ad b rd hdv hddef hdR
    have hc := ih ac (b - a i) rc hcv hcdef hcR
    rw [hed] at hd
    rw [hec, heb] at hc
    exact valid_one_round G hG _ _ i R hd hc

end LovaszSchrijver.Defect.LSFresh

-- Complete module: LSDProof.FinalRoot

namespace LovaszSchrijver.Defect

theorem defect_div_le_NIndex_le_defect {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℕ) (b : ℕ) (hvalid : Valid (STAB G) (fun i => (a i : ℝ)) b)
    (r : ℝ) (hr : IsDefect G (fun i => (a i : ℝ)) b r) (hr0 : 0 ≤ r)
    (k : ℕ) (hk : IsNIndex G (fun i => (a i : ℝ)) b k) :
    r ≤ k * b ∧ (k : ℝ) ≤ r := by
  constructor
  · exact LSFresh.defect_le_index_mul G hG a b r hr k hk.1
  · cases isEmpty_or_nonempty V with
    | inl hE =>
      let : IsEmpty V := hE
      have hv0 : Valid (NG 0 G) (fun i => (a i : ℝ)) b := by
        intro x hx
        simp [dotProduct]
      have hk0 : k ≤ 0 := hk.2 hv0
      have he : k = 0 := Nat.eq_zero_of_le_zero hk0
      simpa [he] using hr0
    | inr hE =>
      let : Nonempty V := hE
      obtain ⟨z, hz⟩ := LSFresh.defect_is_integer G hG a b r hr
      have hz0 : (0 : ℤ) ≤ z := by exact_mod_cast (show (0 : ℝ) ≤ z by simpa [← hz] using hr0)
      have hcast : (z.toNat : ℝ) = r := by
        rw [hz]
        exact_mod_cast Int.toNat_of_nonneg hz0
      have hv := LSFresh.valid_NG_of_defect_le G hG z.toNat a b r hvalid hr (by rw [hcast])
      have hkR : k ≤ z.toNat := hk.2 hv
      have hh : (k : ℝ) ≤ (z.toNat : ℝ) := by exact_mod_cast hkR
      rwa [hcast] at hh

end LovaszSchrijver.Defect


open LovaszSchrijver.Defect

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℕ) (b : ℕ) (hvalid : Valid (STAB G) (fun i => (a i : ℝ)) b)
    (r : ℝ) (hr : IsDefect G (fun i => (a i : ℝ)) b r) (hr0 : 0 ≤ r)
    (k : ℕ) (hk : IsNIndex G (fun i => (a i : ℝ)) b k) :
    r ≤ k * b ∧ (k : ℝ) ≤ r := by
  exact defect_div_le_NIndex_le_defect G hG a b hvalid r hr hr0 k hk
