-- Prove2me | solution 1 for MagicSquares.real_cone_face_support_order_iso
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-22T15:34:45.975892+00:00
-- url     : https://prove2.me/submissions/fe97f4d1-8496-443b-9f74-ead04788dc58

import Mathlib
import Definitions.Def_MagicSquaresRealCone
import Definitions.Def_MagicSquaresMatchingBoundary

set_option autoImplicit false


/-! From OrthantFace.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- A sufficiently small positive multiple preserves coordinatewise domination. -/
theorem exists_pos_smul_le_of_zero_imp {ι : Type*} [Fintype ι]
    (x y : ι → 𝕜) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hzero : ∀ i, x i = 0 → y i = 0) :
    ∃ a : 𝕜, 0 < a ∧ ∀ i, a * y i ≤ x i := by
  classical
  have hfinite (s : Finset ι) : ∃ a : 𝕜, 0 < a ∧ ∀ i ∈ s, a * y i ≤ x i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a, ha, hbound⟩ := ih
      by_cases hxi : x i = 0
      · refine ⟨a, ha, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          simp [hzero i hxi, hxi]
        · exact hbound j hj
      · obtain ⟨b, hb, hbi⟩ := exists_pos_mul_lt (lt_of_le_of_ne (hx i) (Ne.symm hxi)) (y i)
        refine ⟨min a b, lt_min ha hb, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          calc
            min a b * y i ≤ b * y i := mul_le_mul_of_nonneg_right (min_le_right _ _) (hy i)
            _ ≤ x i := by nlinarith
        · exact (mul_le_mul_of_nonneg_right (min_le_left a b) (hy j)).trans (hbound j hj)
  obtain ⟨a, ha, hab⟩ := hfinite Finset.univ
  exact ⟨a, ha, fun i => hab i (Finset.mem_univ i)⟩

/-- The nonnegative vectors in a linear subspace form a pointed cone. -/
def orthantSection {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) :
    PointedCone 𝕜 (ι → 𝕜) :=
  PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)

theorem mem_orthantSection {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (x : ι → 𝕜) :
    x ∈ orthantSection L ↔ x ∈ L ∧ ∀ i, 0 ≤ x i := Iff.rfl

/-- Every face of an orthant section is closed downward under coordinate support.
This is the substantive domination step in its face/support correspondence. -/
theorem face_mem_of_zero_imp {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) {x y : ι → 𝕜}
    (hx : x ∈ F) (hy : y ∈ orthantSection L)
    (hzero : ∀ i, x i = 0 → y i = 0) : y ∈ F := by
  have hxC := (mem_orthantSection L x).mp (hF.le hx)
  have hyC := (mem_orthantSection L y).mp hy
  obtain ⟨a, ha, hab⟩ := exists_pos_smul_le_of_zero_imp x y hxC.2 hyC.2 hzero
  have hz : x - a • y ∈ orthantSection L := by
    apply (mem_orthantSection L _).mpr
    refine ⟨L.sub_mem hxC.1 (L.smul_mem a hyC.1), ?_⟩
    intro i
    change 0 ≤ x i - a * y i
    exact sub_nonneg.mpr (hab i)
  apply hF.mem_of_smul_add_mem hy hz ha
  simpa using hx

end MagicSquaresGeometry

/-! From OrthantFaceSupport.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Every face has a point that uses every coordinate used anywhere in the face. -/
theorem exists_max_support_point {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) :
    ∃ x : ι → 𝕜, x ∈ F ∧
      ∀ y : ι → 𝕜, y ∈ F → ∀ i, x i = 0 → y i = 0 := by
  classical
  have hchoice (i : ι) : ∃ v : ι → 𝕜, v ∈ F ∧
      (∀ y : ι → 𝕜, y ∈ F → y i ≠ 0 → v i ≠ 0) := by
    by_cases h : ∃ y : ι → 𝕜, y ∈ F ∧ y i ≠ 0
    · obtain ⟨y, hy, hyi⟩ := h
      exact ⟨y, hy, fun _ _ _ => hyi⟩
    · refine ⟨0, F.zero_mem, ?_⟩
      intro y hy hyi
      exact False.elim (h ⟨y, hy, hyi⟩)
  choose v hvF hvcover using hchoice
  let x : ι → 𝕜 := ∑ i : ι, v i
  have hx : x ∈ F := F.sum_mem (fun i _ => hvF i)
  refine ⟨x, hx, ?_⟩
  intro y hy i hxi
  by_contra hyi
  have hvi : v i i ≠ 0 := hvcover i y hy hyi
  have hnonneg (j : ι) : 0 ≤ v j i :=
    ((mem_orthantSection L (v j)).mp (hF.le (hvF j))).2 i
  have hle : v i i ≤ x i := by
    change v i i ≤ (∑ j : ι, v j) i
    rw [Finset.sum_apply]
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hzero : v i i = 0 := le_antisymm (hxi ▸ hle) (hnonneg i)
  exact hvi hzero

/-- Faces of an orthant section are exactly its members with fixed zero coordinates. -/
theorem exists_face_zero_characterization {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) :
    ∃ x : ι → 𝕜, x ∈ F ∧ ∀ y : ι → 𝕜,
      (y ∈ F ↔ y ∈ orthantSection L ∧ ∀ i, x i = 0 → y i = 0) := by
  obtain ⟨x, hx, hmax⟩ := exists_max_support_point L F hF
  refine ⟨x, hx, fun y => ?_⟩
  constructor
  · intro hy
    exact ⟨hF.le hy, hmax y hy⟩
  · rintro ⟨hy, hzero⟩
    exact face_mem_of_zero_imp L F hF hx hy hzero

end MagicSquaresGeometry

/-! From OrthantCoordinateFace.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Impose additional coordinate zeros on an orthant section. -/
def coordinateFace {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (B : Set ι) :
    PointedCone 𝕜 (ι → 𝕜) where
  carrier := {x | x ∈ orthantSection L ∧ ∀ i, i ∉ B → x i = 0}
  zero_mem' := ⟨(orthantSection L).zero_mem, by simp⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨(orthantSection L).add_mem hx.1 hy.1, ?_⟩
    intro i hi
    change x i + y i = 0
    rw [hx.2 i hi, hy.2 i hi, add_zero]
  smul_mem' := by
    intro a x hx
    refine ⟨(orthantSection L).smul_mem a.property hx.1, ?_⟩
    intro i hi
    change (a : 𝕜) * x i = 0
    rw [hx.2 i hi, mul_zero]

theorem mem_coordinateFace {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (B : Set ι)
    (x : ι → 𝕜) :
    x ∈ coordinateFace L B ↔ x ∈ orthantSection L ∧ ∀ i, i ∉ B → x i = 0 := Iff.rfl

/-- Nonnegativity makes every additional zero-coordinate constraint a face. -/
theorem coordinateFace_isFaceOf {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (B : Set ι) :
    (coordinateFace L B).IsFaceOf (orthantSection L) := by
  constructor
  · exact fun _ hx => hx.1
  · intro x y a hx hy ha hsum
    refine ⟨hx, ?_⟩
    intro i hi
    have hxi := ((mem_orthantSection L x).mp hx).2 i
    have hyi := ((mem_orthantSection L y).mp hy).2 i
    have heq := hsum.2 i hi
    change a * x i + y i = 0 at heq
    nlinarith

theorem isFaceOf_iff_coordinateFace {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜)) :
    F.IsFaceOf (orthantSection L) ↔ ∃ B : Set ι, F = coordinateFace L B := by
  constructor
  · intro hF
    obtain ⟨x, hx, hchar⟩ := exists_face_zero_characterization L F hF
    refine ⟨{i | x i ≠ 0}, ?_⟩
    ext y
    rw [mem_coordinateFace, hchar y]
    simp
  · rintro ⟨B, rfl⟩
    exact coordinateFace_isFaceOf L B

end MagicSquaresGeometry

/-! From OrthantFaceOrder.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype ι]

/-- Coordinates used by at least one point of a cone. -/
noncomputable def faceSupport (F : PointedCone 𝕜 (ι → 𝕜)) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∃ x ∈ F, x i ≠ 0

theorem mem_faceSupport (F : PointedCone 𝕜 (ι → 𝕜)) (i : ι) :
    i ∈ faceSupport F ↔ ∃ x ∈ F, x i ≠ 0 := by
  classical
  simp [faceSupport]

theorem exists_faceSupport_witness (L : Submodule 𝕜 (ι → 𝕜))
    (F : PointedCone 𝕜 (ι → 𝕜)) (hF : F.IsFaceOf (orthantSection L)) :
    ∃ x ∈ F, ∀ i, i ∈ faceSupport F ↔ x i ≠ 0 := by
  obtain ⟨x, hx, hmax⟩ := exists_max_support_point L F hF
  refine ⟨x, hx, fun i => ?_⟩
  rw [mem_faceSupport]
  constructor
  · rintro ⟨y, hy, hiy⟩ hix
    exact hiy (hmax y hy i hix)
  · exact fun hix => ⟨x, hx, hix⟩

theorem face_eq_coordinateFace_support (L : Submodule 𝕜 (ι → 𝕜))
    (F : PointedCone 𝕜 (ι → 𝕜)) (hF : F.IsFaceOf (orthantSection L)) :
    F = coordinateFace L (↑(faceSupport F) : Set ι) := by
  obtain ⟨x, hx, hchar⟩ := exists_face_zero_characterization L F hF
  ext y
  rw [mem_coordinateFace, hchar y]
  constructor
  · rintro ⟨hy, hzero⟩
    refine ⟨hy, fun i hi => ?_⟩
    apply hzero i
    by_contra hxi
    exact hi ((mem_faceSupport F i).mpr ⟨x, hx, hxi⟩)
  · rintro ⟨hy, hzero⟩
    refine ⟨hy, fun i hxi => ?_⟩
    apply hzero i
    intro hi
    obtain ⟨z, hz, hzi⟩ := (mem_faceSupport F i).mp hi
    exact hzi (((hchar z).mp hz).2 i hxi)

theorem face_le_iff_support_subset (L : Submodule 𝕜 (ι → 𝕜))
    (F G : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) (hG : G.IsFaceOf (orthantSection L)) :
    F ≤ G ↔ faceSupport F ⊆ faceSupport G := by
  constructor
  · intro h i hi
    obtain ⟨x, hx, hxi⟩ := (mem_faceSupport F i).mp hi
    exact (mem_faceSupport G i).mpr ⟨x, h hx, hxi⟩
  · intro h x hx
    rw [face_eq_coordinateFace_support L G hG, mem_coordinateFace]
    refine ⟨hF.le hx, fun i hi => ?_⟩
    by_contra hxi
    exact hi (h ((mem_faceSupport F i).mpr ⟨x, hx, hxi⟩))

/-- The entire face order embeds into the Boolean order on coordinates. -/
noncomputable def faceSupportOrderEmbedding (L : Submodule 𝕜 (ι → 𝕜)) :
    {F : PointedCone 𝕜 (ι → 𝕜) // F.IsFaceOf (orthantSection L)} ↪o Finset ι where
  toFun F := faceSupport F.val
  inj' := by
    intro F G h
    change faceSupport F.val = faceSupport G.val at h
    apply Subtype.ext
    apply le_antisymm
    · exact (face_le_iff_support_subset L F.val G.val F.property G.property).mpr
        (by rw [h])
    · exact (face_le_iff_support_subset L G.val F.val G.property F.property).mpr
        (by rw [h])
  map_rel_iff' := by
    intro F G
    exact (face_le_iff_support_subset L F.val G.val F.property G.property).symm

theorem finite_faces_orthantSection (L : Submodule 𝕜 (ι → 𝕜)) :
    Finite {F : PointedCone 𝕜 (ι → 𝕜) // F.IsFaceOf (orthantSection L)} :=
  Finite.of_injective (faceSupportOrderEmbedding L) (faceSupportOrderEmbedding L).injective

/-- The coordinate supports actually realized by points of the orthant section. -/
def RealizedSupport (L : Submodule 𝕜 (ι → 𝕜)) (B : Finset ι) : Prop :=
  ∃ x ∈ orthantSection L, ∀ i, i ∈ B ↔ x i ≠ 0

theorem faceSupport_coordinateFace (L : Submodule 𝕜 (ι → 𝕜))
    (B : Finset ι) (hB : RealizedSupport L B) :
    faceSupport (coordinateFace L (↑B : Set ι)) = B := by
  classical
  obtain ⟨x, hx, hs⟩ := hB
  have hxF : x ∈ coordinateFace L (↑B : Set ι) := by
    refine ⟨hx, fun i hi => ?_⟩
    by_contra hxi
    exact hi ((hs i).mpr hxi)
  ext i
  rw [mem_faceSupport]
  constructor
  · rintro ⟨y, hy, hyi⟩
    by_contra hi
    exact hyi (hy.2 i hi)
  · exact fun hi => ⟨x, hxF, (hs i).mp hi⟩

/-- The face lattice and the order of realized coordinate supports agree exactly. -/
noncomputable def faceSupportOrderIso (L : Submodule 𝕜 (ι → 𝕜)) :
    {F : PointedCone 𝕜 (ι → 𝕜) // F.IsFaceOf (orthantSection L)} ≃o
      {B : Finset ι // RealizedSupport L B} where
  toFun F := ⟨faceSupport F.val, by
    obtain ⟨x, hx, hs⟩ := exists_faceSupport_witness L F.val F.property
    exact ⟨x, F.property.le hx, hs⟩⟩
  invFun B := ⟨coordinateFace L (↑B.val : Set ι), coordinateFace_isFaceOf L _⟩
  left_inv F := by
    apply Subtype.ext
    exact (face_eq_coordinateFace_support L F.val F.property).symm
  right_inv B := by
    apply Subtype.ext
    exact faceSupport_coordinateFace L B.val B.property
  map_rel_iff' := by
    intro F G
    exact (face_le_iff_support_subset L F.val G.val F.property G.property).symm

end MagicSquaresGeometry

/-! From BirkhoffSupport.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

/-- Every positive entry of a doubly stochastic matrix lies in the positive
support of one entire permutation. -/
theorem exists_positive_permutation_through_entry (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin n))
    (i j : Fin n) (hij : 0 < M i j) :
    ∃ σ : Equiv.Perm (Fin n), σ i = j ∧ ∀ k, 0 < M k (σ k) := by
  classical
  obtain ⟨w, hw, -, hsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hperm (σ : Equiv.Perm (Fin n)) (k l : Fin n) :
      σ.permMatrix ℝ k l = if σ k = l then 1 else 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      eq_comm]
  have hentry (k l : Fin n) :
      M k l = ∑ σ : Equiv.Perm (Fin n), w σ * σ.permMatrix ℝ k l := by
    rw [← hsum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hterm_nonneg (σ : Equiv.Perm (Fin n)) (k l : Fin n) :
      0 ≤ w σ * σ.permMatrix ℝ k l := by
    rw [hperm]
    split_ifs <;> nlinarith [hw σ]
  have hsumpos :
      0 < ∑ σ : Equiv.Perm (Fin n), w σ * σ.permMatrix ℝ i j := by
    rw [← hentry]
    exact hij
  obtain ⟨σ, -, hσpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun σ _ => hterm_nonneg σ i j)).mp hsumpos
  have hσij : σ i = j := by
    by_contra hne
    rw [hperm, if_neg hne, mul_zero] at hσpos
    exact (lt_irrefl (0 : ℝ)) hσpos
  have hwσ : 0 < w σ := by
    simpa [hperm, hσij] using hσpos
  refine ⟨σ, hσij, ?_⟩
  intro k
  have hle :
      w σ * σ.permMatrix ℝ k (σ k) ≤
        ∑ τ : Equiv.Perm (Fin n), w τ * τ.permMatrix ℝ k (σ k) :=
    Finset.single_le_sum (fun τ _ => hterm_nonneg τ k (σ k)) (Finset.mem_univ σ)
  rw [hperm, if_pos rfl, mul_one, ← hentry] at hle
  exact lt_of_lt_of_le hwσ hle

end MagicSquaresGeometry

/-! From DoublyStochasticSupport.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset MagicSquaresBoundary
attribute [local instance] Classical.propDecidable

/-- The positive support of a real doubly stochastic matrix is matching-covered. -/
theorem matchingCovered_positive_support (n : ℕ) (hn : 1 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    MatchingCoveredBoard n
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e => 0 < M e.1 e.2)) := by
  classical
  let B : Finset (Fin n × Fin n) :=
    (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => 0 < M e.1 e.2)
  have hnonneg (j : Fin n) : 0 ≤ M ⟨0, hn⟩ j :=
    nonneg_of_mem_doublyStochastic hM
  have hrow : 0 < ∑ j : Fin n, M ⟨0, hn⟩ j := by
    rw [sum_row_of_mem_doublyStochastic hM]
    norm_num
  obtain ⟨j, _, hj⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun j _ => hnonneg j)).mp hrow
  change MatchingCoveredBoard n B
  constructor
  · exact ⟨(⟨0, hn⟩, j), by simp [B, hj]⟩
  · intro e he
    obtain ⟨i, j⟩ := e
    have hij : 0 < M i j := by simpa [B] using he
    obtain ⟨σ, hσij, hσpos⟩ := exists_positive_permutation_through_entry n M hM i j hij
    refine ⟨σ, ?_, ?_⟩
    · simp [permSupport, ← hσij]
    · intro p hp
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
      simp [B, hσpos k]

/-- Every matching-covered board is exactly the positive support of a real
doubly stochastic matrix. -/
theorem exists_doublyStochastic_with_positive_support (n : ℕ)
    (B : Finset (Fin n × Fin n)) (hB : MatchingCoveredBoard n B) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ,
      M ∈ doublyStochastic ℝ (Fin n) ∧
        ∀ i j : Fin n, 0 < M i j ↔ (i, j) ∈ B := by
  classical
  let P : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun σ => permSupport σ ⊆ B)
  obtain ⟨e, he⟩ := hB.1
  obtain ⟨τ, _, hτB⟩ := hB.2 e he
  have hτP : τ ∈ P := by simp [P, hτB]
  have hP : P.Nonempty := ⟨τ, hτP⟩
  let w : ℝ := (P.card : ℝ)⁻¹
  have hw : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr hP)
  have hwsum : ∑ σ ∈ P, w = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [w]
    exact mul_inv_cancel₀ (by exact_mod_cast Finset.card_ne_zero_of_mem hτP)
  let M : Matrix (Fin n) (Fin n) ℝ :=
    ∑ σ ∈ P, w • σ.permMatrix ℝ
  have hM : M ∈ doublyStochastic ℝ (Fin n) := by
    apply convex_doublyStochastic.sum_mem
    · exact fun _ _ => hw.le
    · exact hwsum
    · exact fun _ _ => permMatrix_mem_doublyStochastic
  have hperm (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
      σ.permMatrix ℝ i j = if σ i = j then 1 else 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      eq_comm]
  have hentry (i j : Fin n) :
      M i j = ∑ σ ∈ P, w * σ.permMatrix ℝ i j := by
    simp only [M, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hterm_nonneg (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
      0 ≤ w * σ.permMatrix ℝ i j := by
    rw [hperm]
    split_ifs <;> nlinarith [hw.le]
  refine ⟨M, hM, ?_⟩
  intro i j
  constructor
  · intro hij
    have hsumpos : 0 < ∑ σ ∈ P, w * σ.permMatrix ℝ i j := by
      rw [← hentry]
      exact hij
    obtain ⟨σ, hσP, hσpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun σ _ => hterm_nonneg σ i j)).mp hsumpos
    have hσij : σ i = j := by
      by_contra hne
      rw [hperm, if_neg hne, mul_zero] at hσpos
      exact (lt_irrefl (0 : ℝ)) hσpos
    have hσB : permSupport σ ⊆ B := by simpa [P] using hσP
    apply hσB
    simp [permSupport, hσij]
  · intro hij
    obtain ⟨σ, hcell, hσB⟩ := hB.2 (i, j) hij
    have hσP : σ ∈ P := by simp [P, hσB]
    have hσij : σ i = j := by
      simpa [permSupport] using hcell
    have hle : w * σ.permMatrix ℝ i j ≤
        ∑ ρ ∈ P, w * ρ.permMatrix ℝ i j :=
      Finset.single_le_sum (fun ρ _ => hterm_nonneg ρ i j) hσP
    rw [hperm, if_pos hσij, mul_one, ← hentry] at hle
    exact lt_of_lt_of_le hw hle

end MagicSquaresGeometry

/-! From SemiMagicCone.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset

/-- Real matrices whose rows and columns have one common line sum. -/
def semiMagicSubspace (n : ℕ) : Submodule ℝ ((Fin n × Fin n) → ℝ) where
  carrier := {x | ∃ s : ℝ,
    (∀ i, ∑ j, x (i, j) = s) ∧ (∀ j, ∑ i, x (i, j) = s)}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩ <;> intro i <;> simp
  add_mem' := by
    rintro x y ⟨sx, hxr, hxc⟩ ⟨sy, hyr, hyc⟩
    refine ⟨sx + sy, ?_, ?_⟩
    · intro i
      simp only [Pi.add_apply, sum_add_distrib, hxr i, hyr i]
    · intro j
      simp only [Pi.add_apply, sum_add_distrib, hxc j, hyc j]
  smul_mem' := by
    rintro a x ⟨s, hxr, hxc⟩
    refine ⟨a * s, ?_, ?_⟩
    · intro i
      change ∑ j, a * x (i, j) = a * s
      rw [← Finset.mul_sum, hxr i]
    · intro j
      change ∑ i, a * x (i, j) = a * s
      rw [← Finset.mul_sum, hxc j]

theorem exists_pos_common_line_sum_of_nonneg_ne_zero {n : ℕ}
    {x : (Fin n × Fin n) → ℝ} (hx : x ∈ semiMagicSubspace n)
    (hnonneg : ∀ e, 0 ≤ x e) (hne : x ≠ 0) :
    ∃ s : ℝ, 0 < s ∧
      (∀ i, ∑ j, x (i, j) = s) ∧ (∀ j, ∑ i, x (i, j) = s) := by
  obtain ⟨s, hrow, hcol⟩ := hx
  have hentry : ∃ i j, x (i, j) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    funext e
    rcases e with ⟨i, j⟩
    exact h i j
  obtain ⟨i, j, hij⟩ := hentry
  have hpos : 0 < x (i, j) := lt_of_le_of_ne (hnonneg (i, j)) (Ne.symm hij)
  have hle : x (i, j) ≤ ∑ k, x (i, k) :=
    Finset.single_le_sum (fun k _ => hnonneg (i, k)) (Finset.mem_univ j)
  refine ⟨s, hpos.trans_le (by simpa [hrow i] using hle), hrow, hcol⟩

/-- Divide a nonzero nonnegative semi-magic matrix by its common line sum. -/
noncomputable def normalizedSemiMagic {n : ℕ} (x : (Fin n × Fin n) → ℝ) (s : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => x (i, j) / s

theorem normalizedSemiMagic_mem_doublyStochastic {n : ℕ}
    {x : (Fin n × Fin n) → ℝ} {s : ℝ} (hs : 0 < s)
    (hnonneg : ∀ e, 0 ≤ x e) (hrow : ∀ i, ∑ j, x (i, j) = s)
    (hcol : ∀ j, ∑ i, x (i, j) = s) :
    normalizedSemiMagic x s ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact div_nonneg (hnonneg (i, j)) hs.le
  · intro i
    change (∑ j, x (i, j) / s) = 1
    rw [← Finset.sum_div, hrow i, div_self hs.ne']
  · intro j
    change (∑ i, x (i, j) / s) = 1
    rw [← Finset.sum_div, hcol j, div_self hs.ne']

theorem normalizedSemiMagic_pos_iff {n : ℕ} {x : (Fin n × Fin n) → ℝ} {s : ℝ}
    (hs : 0 < s) (i j : Fin n) :
    0 < normalizedSemiMagic x s i j ↔ 0 < x (i, j) := by
  simp only [normalizedSemiMagic]
  exact div_pos_iff_of_pos_right hs

end MagicSquaresGeometry

/-! From SemiMagicFaceSupport.lean -/
set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset MagicSquaresBoundary
attribute [local instance] Classical.propDecidable

/-- Nonzero supports of the semi-magic cone are precisely matching-covered boards. -/
theorem realizedSupport_semiMagic_iff (n : ℕ) (hn : 1 ≤ n)
    (B : Finset (Fin n × Fin n)) :
    RealizedSupport (semiMagicSubspace n) B ↔ B = ∅ ∨ MatchingCoveredBoard n B := by
  classical
  constructor
  · rintro ⟨x, hx, hB⟩
    obtain ⟨hxL, hxpos⟩ := (mem_orthantSection _ _).mp hx
    by_cases hx0 : x = 0
    · left
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      have hne := (hB e).mp he
      simpa [hx0] using hne
    · right
      obtain ⟨s, hs, hrow, hcol⟩ :=
        exists_pos_common_line_sum_of_nonneg_ne_zero hxL hxpos hx0
      have hM := normalizedSemiMagic_mem_doublyStochastic hs hxpos hrow hcol
      have hc := matchingCovered_positive_support n hn (normalizedSemiMagic x s) hM
      have heq : (Finset.univ.filter
          (fun e : Fin n × Fin n => 0 < normalizedSemiMagic x s e.1 e.2)) = B := by
        ext e
        simp only [mem_filter, mem_univ, true_and]
        rw [normalizedSemiMagic_pos_iff hs]
        exact (show 0 < x e ↔ x e ≠ 0 from
          ⟨ne_of_gt, fun he => lt_of_le_of_ne (hxpos e) (Ne.symm he)⟩).trans (hB e).symm
      rwa [heq] at hc
  · rintro (rfl | hB)
    · exact ⟨0, (orthantSection (semiMagicSubspace n)).zero_mem, by simp⟩
    · obtain ⟨M, hM, hMB⟩ := exists_doublyStochastic_with_positive_support n B hB
      refine ⟨fun e => M e.1 e.2, ?_, ?_⟩
      · apply (mem_orthantSection _ _).mpr
        exact ⟨⟨1, sum_row_of_mem_doublyStochastic hM,
          sum_col_of_mem_doublyStochastic hM⟩, fun e => nonneg_of_mem_doublyStochastic hM⟩
      · intro e
        exact (hMB e.1 e.2).symm.trans
          ⟨ne_of_gt, fun he => lt_of_le_of_ne (nonneg_of_mem_doublyStochastic hM) (Ne.symm he)⟩

/-- The face order of the nonnegative semi-magic cone is the matching-board order,
with the empty board as its bottom element. -/
noncomputable def semiMagicFaceSupportOrderIso (n : ℕ) (hn : 1 ≤ n) :
    {F : PointedCone ℝ ((Fin n × Fin n) → ℝ) //
      F.IsFaceOf (orthantSection (semiMagicSubspace n))} ≃o
    {B : Finset (Fin n × Fin n) // B = ∅ ∨ MatchingCoveredBoard n B} :=
  (faceSupportOrderIso (semiMagicSubspace n)).trans
    { toFun := fun B => ⟨B.val, (realizedSupport_semiMagic_iff n hn B.val).mp B.property⟩
      invFun := fun B => ⟨B.val, (realizedSupport_semiMagic_iff n hn B.val).mpr B.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

end MagicSquaresGeometry


/-! Platform-facing face/support theorem. -/

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ e :
      {F : PointedCone ℝ ((Fin n × Fin n) → ℝ) //
        F.IsFaceOf (MagicSquaresRealCone.cone n)} ≃o
      {B : Finset (Fin n × Fin n) //
        B = ∅ ∨ MagicSquaresBoundary.MatchingCoveredBoard n B},
      ∀ F i, i ∈ (e F).val ↔ ∃ x ∈ F.val, x i ≠ 0 := by
  change ∃ e :
      {F : PointedCone ℝ ((Fin n × Fin n) → ℝ) //
        F.IsFaceOf (MagicSquaresGeometry.orthantSection
          (MagicSquaresGeometry.semiMagicSubspace n))} ≃o
      {B : Finset (Fin n × Fin n) //
        B = ∅ ∨ MagicSquaresBoundary.MatchingCoveredBoard n B},
      ∀ F i, i ∈ (e F).val ↔ ∃ x ∈ F.val, x i ≠ 0
  refine ⟨MagicSquaresGeometry.semiMagicFaceSupportOrderIso n hn, ?_⟩
  intro F i
  exact MagicSquaresGeometry.mem_faceSupport F.val i
