-- Prove2me | solution 1 for Grunbaum2003.centrally_symmetric_neighborly_families
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T19:34:51.137103+00:00
-- url     : https://prove2.me/submissions/46d7cc76-639d-4113-8074-da2250506c6b

import Definitions.Def_Grunbaum2003_IsDPolytope
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

namespace Grunbaum2003

namespace CentrallySymmetricNeighborly

variable {d : ℕ}

def idx0 (hd : 3 ≤ d) : Fin d := ⟨0, by omega⟩
def idx1 (hd : 3 ≤ d) : Fin d := ⟨1, by omega⟩
def idx2 (hd : 3 ≤ d) : Fin d := ⟨2, by omega⟩

lemma idx0_ne_idx1 (hd : 3 ≤ d) : idx0 hd ≠ idx1 hd := by
  intro h
  have := congrArg Fin.val h
  simp [idx0, idx1] at this

lemma idx0_ne_idx2 (hd : 3 ≤ d) : idx0 hd ≠ idx2 hd := by
  intro h
  have := congrArg Fin.val h
  simp [idx0, idx2] at this

lemma idx1_ne_idx2 (hd : 3 ≤ d) : idx1 hd ≠ idx2 hd := by
  intro h
  have := congrArg Fin.val h
  simp [idx1, idx2] at this

/-- Standard basis vector in `Fin d → ℝ`. -/
def stdBasis (a : Fin d) (b : Fin d) : ℝ :=
  if b = a then 1 else 0

@[simp]
lemma stdBasis_apply (a b : Fin d) :
    stdBasis a b = if b = a then 1 else 0 := rfl

/-- Linear part of the separating functional between indices with real parameters `r, s`. -/
noncomputable def LMap (hd : 3 ≤ d) (r s : ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := (r - s) * x (idx0 hd) + (r ^ 2 - s ^ 2) * x (idx1 hd) + (r ^ 3 - s ^ 3) * x (idx2 hd)
  map_add' x y := by simp; ring
  map_smul' c x := by simp; ring

@[simp]
lemma LMap_apply (hd : 3 ≤ d) (r s : ℝ) (x : Fin d → ℝ) :
    LMap hd r s x =
      (r - s) * x (idx0 hd) + (r ^ 2 - s ^ 2) * x (idx1 hd) + (r ^ 3 - s ^ 3) * x (idx2 hd) := rfl

lemma LMap_swap (hd : 3 ≤ d) (r s : ℝ) (x : Fin d → ℝ) :
    LMap hd s r x = - LMap hd r s x := by
  simp [LMap_apply]
  ring

/-- Affine separating functional `ℓ(r, s)(x) = L(r, s)(x) + (r^4 - s^4)`. -/
noncomputable def ell (hd : 3 ≤ d) (r s : ℝ) (x : Fin d → ℝ) : ℝ :=
  LMap hd r s x + (r ^ 4 - s ^ 4)

lemma ell_swap (hd : 3 ≤ d) (r s : ℝ) (x : Fin d → ℝ) :
    ell hd s r x = - ell hd r s x := by
  unfold ell
  rw [LMap_swap]
  ring

/-- Contact basepoint `m(r, s)` for parameters `r, s`. Symmetric in `(r, s)`. -/
def contactBase (hd : 3 ≤ d) (r s : ℝ) (b : Fin d) : ℝ :=
  if b = idx0 hd then -2 * r * s * (r + s)
  else if b = idx1 hd then (r + s) ^ 2 + 2 * r * s
  else if b = idx2 hd then -2 * (r + s)
  else 0

lemma contactBase_comm (hd : 3 ≤ d) (r s : ℝ) :
    contactBase hd r s = contactBase hd s r := by
  ext b
  unfold contactBase
  split_ifs <;> ring

lemma contactBase_idx0 (hd : 3 ≤ d) (r s : ℝ) :
    contactBase hd r s (idx0 hd) = -2 * r * s * (r + s) := by
  unfold contactBase
  simp

lemma contactBase_idx1 (hd : 3 ≤ d) (r s : ℝ) :
    contactBase hd r s (idx1 hd) = (r + s) ^ 2 + 2 * r * s := by
  unfold contactBase
  simp [Ne.symm (idx0_ne_idx1 hd)]

lemma contactBase_idx2 (hd : 3 ≤ d) (r s : ℝ) :
    contactBase hd r s (idx2 hd) = -2 * (r + s) := by
  unfold contactBase
  simp [Ne.symm (idx0_ne_idx2 hd), Ne.symm (idx1_ne_idx2 hd)]

/-- Key degree-4 moment cancellation identity:
`ell(i, j)(contactBase(r, s)) = (i - r)^2 (i - s)^2 - (j - r)^2 (j - s)^2`. -/
lemma ell_contactBase (hd : 3 ≤ d) (i j r s : ℝ) :
    ell hd i j (contactBase hd r s) =
      (i - r) ^ 2 * (i - s) ^ 2 - (j - r) ^ 2 * (j - s) ^ 2 := by
  unfold ell
  rw [LMap_apply, contactBase_idx0, contactBase_idx1, contactBase_idx2]
  ring

/-- Coefficient at `idx0` for the tangent vector `w(r, s, a)`. -/
def coeff0 (hd : 3 ≤ d) (r s : ℝ) (a : Fin d) : ℝ :=
  if a = idx1 hd then -(r + s)
  else if a = idx2 hd then -(r ^ 2 + r * s + s ^ 2)
  else 0

lemma coeff0_comm (hd : 3 ≤ d) (r s : ℝ) (a : Fin d) :
    coeff0 hd r s a = coeff0 hd s r a := by
  unfold coeff0
  split_ifs <;> ring

/-- Unscaled tangent direction `w(r, s, a)` in `ker (LMap hd r s)`.
At `a = idx0 hd`, we set `w(r, s, idx0 hd) = 0`. -/
def tangentVec (hd : 3 ≤ d) (r s : ℝ) (a : Fin d) (b : Fin d) : ℝ :=
  if a = idx0 hd then 0
  else if b = idx0 hd then coeff0 hd r s a
  else if b = a then 1
  else 0

lemma tangentVec_comm (hd : 3 ≤ d) (r s : ℝ) (a : Fin d) :
    tangentVec hd r s a = tangentVec hd s r a := by
  ext b
  unfold tangentVec
  rw [coeff0_comm]

@[simp]
lemma tangentVec_idx0 (hd : 3 ≤ d) (r s : ℝ) :
    tangentVec hd r s (idx0 hd) = 0 := by
  ext b
  simp [tangentVec]

lemma LMap_tangentVec (hd : 3 ≤ d) (r s : ℝ) (a : Fin d) :
    LMap hd r s (tangentVec hd r s a) = 0 := by
  by_cases ha0 : a = idx0 hd
  · subst ha0
    simp [LMap_apply]
  · by_cases ha1 : a = idx1 hd
    · subst ha1
      rw [LMap_apply]
      unfold tangentVec coeff0
      simp [Ne.symm (idx0_ne_idx1 hd), Ne.symm (idx0_ne_idx2 hd), Ne.symm (idx1_ne_idx2 hd)]
      ring
    · by_cases ha2 : a = idx2 hd
      · subst ha2
        rw [LMap_apply]
        unfold tangentVec coeff0
        simp [Ne.symm (idx0_ne_idx1 hd), Ne.symm (idx0_ne_idx2 hd),
          idx1_ne_idx2 hd, Ne.symm (idx1_ne_idx2 hd)]
        ring
      · rw [LMap_apply]
        unfold tangentVec coeff0
        simp [ha0, ha1, ha2, Ne.symm ha1, Ne.symm ha2,
          Ne.symm (idx0_ne_idx1 hd), Ne.symm (idx0_ne_idx2 hd)]

lemma tangentVec_apply_of_ne_idx0 (hd : 3 ≤ d) (r s : ℝ) {a b : Fin d}
    (ha0 : a ≠ idx0 hd) (hb0 : b ≠ idx0 hd) :
    tangentVec hd r s a b = stdBasis a b := by
  unfold tangentVec stdBasis
  simp [ha0, hb0]

/-- Positive self-normalizing scale factor ensuring `|L(i, j)(scale • u)| ≤ 1/4`
for all `0 ≤ i, j ≤ B` and all `u : Fin d → ℝ`. -/
noncomputable def safeScale (hd : 3 ≤ d) (B : ℝ) (u : Fin d → ℝ) : ℝ :=
  (2 * (B ^ 2 + B ^ 4 + B ^ 6 +
    u (idx0 hd) ^ 2 + u (idx1 hd) ^ 2 + u (idx2 hd) ^ 2 + 1))⁻¹

lemma safeScale_pos (hd : 3 ≤ d) (B : ℝ) (u : Fin d → ℝ) :
    0 < safeScale hd B u := by
  unfold safeScale
  positivity

lemma safeScale_ne_zero (hd : 3 ≤ d) (B : ℝ) (u : Fin d → ℝ) :
    safeScale hd B u ≠ 0 :=
  ne_of_gt (safeScale_pos hd B u)

noncomputable def scaledVec (hd : 3 ≤ d) (B : ℝ) (u : Fin d → ℝ) : Fin d → ℝ :=
  safeScale hd B u • u

@[simp]
lemma scaledVec_zero (hd : 3 ≤ d) (B : ℝ) :
    scaledVec hd B (0 : Fin d → ℝ) = 0 := by
  simp [scaledVec]

lemma sq_sub_le_of_nonneg_le {x y B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B) (hy0 : 0 ≤ y) (hyB : y ≤ B) :
    (x - y) ^ 2 ≤ B ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hy0)]

lemma pow_le_pow_of_nonneg_le {x B : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B) (n : ℕ) :
    0 ≤ x ^ n ∧ x ^ n ≤ B ^ n := by
  refine ⟨pow_nonneg hx0 n, ?_⟩
  exact pow_le_pow_left₀ hx0 hxB n

lemma LMap_scaledVec_bounds (hd : 3 ≤ d) {B r s : ℝ}
    (hr0 : 0 ≤ r) (hrB : r ≤ B) (hs0 : 0 ≤ s) (hsB : s ≤ B) (u : Fin d → ℝ) :
    -(1 / 4 : ℝ) ≤ LMap hd r s (scaledVec hd B u) ∧
      LMap hd r s (scaledVec hd B u) ≤ (1 / 4 : ℝ) := by
  have h1 : (r - s) ^ 2 ≤ B ^ 2 := sq_sub_le_of_nonneg_le hr0 hrB hs0 hsB
  have hr2 := pow_le_pow_of_nonneg_le hr0 hrB 2
  have hs2 := pow_le_pow_of_nonneg_le hs0 hsB 2
  have h2 : (r ^ 2 - s ^ 2) ^ 2 ≤ B ^ 4 := by
    calc (r ^ 2 - s ^ 2) ^ 2 ≤ (B ^ 2) ^ 2 := sq_sub_le_of_nonneg_le hr2.1 hr2.2 hs2.1 hs2.2
    _ = B ^ 4 := by ring
  have hr3 := pow_le_pow_of_nonneg_le hr0 hrB 3
  have hs3 := pow_le_pow_of_nonneg_le hs0 hsB 3
  have h3 : (r ^ 3 - s ^ 3) ^ 2 ≤ B ^ 6 := by
    calc (r ^ 3 - s ^ 3) ^ 2 ≤ (B ^ 3) ^ 2 := sq_sub_le_of_nonneg_le hr3.1 hr3.2 hs3.1 hs3.2
    _ = B ^ 6 := by ring
  set D : ℝ := B ^ 2 + B ^ 4 + B ^ 6 +
    u (idx0 hd) ^ 2 + u (idx1 hd) ^ 2 + u (idx2 hd) ^ 2 + 1
  have hD_pos : 0 < 2 * D := by positivity
  have hL_upper : 2 * LMap hd r s u ≤ D := by
    rw [LMap_apply]
    nlinarith [sq_nonneg ((r - s) - u (idx0 hd)),
      sq_nonneg ((r ^ 2 - s ^ 2) - u (idx1 hd)),
      sq_nonneg ((r ^ 3 - s ^ 3) - u (idx2 hd))]
  have hL_lower : -D ≤ 2 * LMap hd r s u := by
    rw [LMap_apply]
    nlinarith [sq_nonneg ((r - s) + u (idx0 hd)),
      sq_nonneg ((r ^ 2 - s ^ 2) + u (idx1 hd)),
      sq_nonneg ((r ^ 3 - s ^ 3) + u (idx2 hd))]
  have h_scale : LMap hd r s (scaledVec hd B u) = LMap hd r s u / (2 * D) := by
    simp [scaledVec, safeScale, D, div_eq_inv_mul, mul_comm]
  rw [h_scale]
  constructor
  · rw [le_div_iff₀ hD_pos]
    linarith
  · rw [div_le_iff₀ hD_pos]
    linarith

/-- Symmetry center `c(r)` for parameter `r` and separation constant `M`. -/
def centerPt (hd : 3 ≤ d) (M r : ℝ) (b : Fin d) : ℝ :=
  if b = idx0 hd then -2 * M * r
  else if b = idx1 hd then M
  else 0

lemma centerPt_idx0 (hd : 3 ≤ d) (M r : ℝ) :
    centerPt hd M r (idx0 hd) = -2 * M * r := by
  unfold centerPt
  simp

lemma centerPt_idx1 (hd : 3 ≤ d) (M r : ℝ) :
    centerPt hd M r (idx1 hd) = M := by
  unfold centerPt
  simp [Ne.symm (idx0_ne_idx1 hd)]

lemma centerPt_idx2 (hd : 3 ≤ d) (M r : ℝ) :
    centerPt hd M r (idx2 hd) = 0 := by
  unfold centerPt
  simp [Ne.symm (idx0_ne_idx2 hd), Ne.symm (idx1_ne_idx2 hd)]

lemma LMap_centerPt (hd : 3 ≤ d) (M r s : ℝ) :
    LMap hd r s (centerPt hd M r) = -M * (r - s) ^ 2 := by
  rw [LMap_apply, centerPt_idx0, centerPt_idx1, centerPt_idx2]
  ring

lemma ell_centerPt (hd : 3 ≤ d) (M r s : ℝ) :
    ell hd r s (centerPt hd M r) = -M * (r - s) ^ 2 + (r ^ 4 - s ^ 4) := by
  unfold ell
  rw [LMap_centerPt]

lemma ell_centerPt_le (hd : 3 ≤ d) {B r s : ℝ}
    (hr0 : 0 ≤ r) (hrB : r ≤ B) (_hs0 : 0 ≤ s) (hrs : 1 ≤ (r - s) ^ 2) :
    ell hd r s (centerPt hd (2 * B ^ 4 + 10) r) ≤ -10 := by
  rw [ell_centerPt]
  have hr4 := (pow_le_pow_of_nonneg_le hr0 hrB 4).2
  have hs4 : 0 ≤ s ^ 4 := by positivity
  have hB4 : 0 ≤ B ^ 4 := by positivity
  nlinarith

lemma ell_reflect_contactBase_le (hd : 3 ≤ d) {B r s t : ℝ}
    (hr0 : 0 ≤ r) (hrB : r ≤ B) (hs0 : 0 ≤ s) (hsB : s ≤ B)
    (ht0 : 0 ≤ t) (htB : t ≤ B) (hrs : 1 ≤ (r - s) ^ 2) :
    2 * ell hd r s (centerPt hd (2 * B ^ 4 + 10) r) -
      ell hd r s (contactBase hd r t) ≤ -20 := by
  rw [ell_contactBase]
  have h_sr : (s - r) ^ 2 ≤ B ^ 2 := sq_sub_le_of_nonneg_le hs0 hsB hr0 hrB
  have h_st : (s - t) ^ 2 ≤ B ^ 2 := sq_sub_le_of_nonneg_le hs0 hsB ht0 htB
  have h_prod : (s - r) ^ 2 * (s - t) ^ 2 ≤ B ^ 4 := by
    calc (s - r) ^ 2 * (s - t) ^ 2 ≤ B ^ 2 * B ^ 2 :=
      mul_le_mul h_sr h_st (sq_nonneg _) (sq_nonneg _)
    _ = B ^ 4 := by ring
  have h_cent2 : ell hd r s (centerPt hd (2 * B ^ 4 + 10) r) ≤ -B ^ 4 - 10 := by
    rw [ell_centerPt]
    have hr4 := (pow_le_pow_of_nonneg_le hr0 hrB 4).2
    have hs4 : 0 ≤ s ^ 4 := by positivity
    have hB4 : 0 ≤ B ^ 4 := by positivity
    nlinarith
  nlinarith [sq_nonneg (r - r), sq_nonneg (r - t)]

/-- Real coordinate of index `i : Fin N`. -/
def param {N : ℕ} (i : Fin N) : ℝ := (i.val : ℝ)

lemma param_nonneg {N : ℕ} (i : Fin N) : 0 ≤ param i :=
  Nat.cast_nonneg i.val

lemma param_le {N : ℕ} (i : Fin N) : param i ≤ (N : ℝ) := by
  unfold param
  exact_mod_cast le_of_lt i.isLt

lemma sq_param_sub_ge_one {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    1 ≤ (param i - param j) ^ 2 := by
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : (i.val + 1 : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    have h2 : 1 ≤ param j - param i := by unfold param; linarith
    nlinarith
  · have h1 : (j.val + 1 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
    have h2 : 1 ≤ param i - param j := by unfold param; linarith
    nlinarith

lemma param_ne_of_ne {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    param i ≠ param j := by
  intro h
  have := sq_param_sub_ge_one hij
  rw [h, sub_self] at this
  norm_num at this

/-- Separation constant `M_N = 2 N^4 + 10`. -/
def sepConst (N : ℕ) : ℝ := 2 * (N : ℝ) ^ 4 + 10

/-- Half-generator set `U_i` before point reflection across `centerPt(i)`. -/
noncomputable def halfGenSet (hd : 3 ≤ d) {N : ℕ} (i : Fin N) : Set (Fin d → ℝ) :=
  let B : ℝ := (N : ℝ)
  let c := centerPt hd (sepConst N) (param i)
  {c} ∪ Set.range (fun a : Fin d => c + scaledVec hd B (stdBasis a)) ∪
    ⋃ k ∈ (Finset.univ.erase i : Finset (Fin N)),
      Set.range (fun a : Fin d =>
        contactBase hd (param i) (param k) +
          scaledVec hd B (tangentVec hd (param i) (param k) a))

/-- Full symmetric vertex set `V_i = U_i ∪ reflect(c_i)(U_i)`. -/
noncomputable def vertexSet (hd : 3 ≤ d) {N : ℕ} (i : Fin N) : Set (Fin d → ℝ) :=
  let c := centerPt hd (sepConst N) (param i)
  halfGenSet hd i ∪ (AffineEquiv.pointReflection ℝ c) '' halfGenSet hd i

/-- Polytope `P_i = convexHull ℝ (vertexSet i)`. -/
noncomputable def poly (hd : 3 ≤ d) {N : ℕ} (i : Fin N) : Set (Fin d → ℝ) :=
  convexHull ℝ (vertexSet hd i)

lemma halfGenSet_finite (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    (halfGenSet hd i).Finite := by
  unfold halfGenSet
  refine ((Set.finite_singleton _).union (Set.finite_range _)).union ?_
  refine Set.Finite.biUnion (Finset.finite_toSet _) (fun k _ => Set.finite_range _)

lemma vertexSet_finite (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    (vertexSet hd i).Finite := by
  unfold vertexSet
  exact (halfGenSet_finite hd i).union ((halfGenSet_finite hd i).image _)

lemma center_mem_halfGenSet (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    centerPt hd (sepConst N) (param i) ∈ halfGenSet hd i :=
  Or.inl (Or.inl rfl)

lemma center_mem_vertexSet (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    centerPt hd (sepConst N) (param i) ∈ vertexSet hd i :=
  Or.inl (center_mem_halfGenSet hd i)

lemma center_mem_poly (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    centerPt hd (sepConst N) (param i) ∈ poly hd i :=
  subset_convexHull ℝ (vertexSet hd i) (center_mem_vertexSet hd i)

lemma axial_mem_vertexSet (hd : 3 ≤ d) {N : ℕ} (i : Fin N) (a : Fin d) :
    centerPt hd (sepConst N) (param i) + scaledVec hd (N : ℝ) (stdBasis a) ∈
      vertexSet hd i :=
  Or.inl (Or.inl (Or.inr ⟨a, rfl⟩))

lemma contact_mem_vertexSet (hd : 3 ≤ d) {N : ℕ} {i k : Fin N} (hik : k ≠ i) (a : Fin d) :
    contactBase hd (param i) (param k) +
      scaledVec hd (N : ℝ) (tangentVec hd (param i) (param k) a) ∈ vertexSet hd i := by
  refine Or.inl (Or.inr ?_)
  refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_erase.mpr ⟨hik, Finset.mem_univ k⟩, ⟨a, rfl⟩⟩

lemma pointReflection_vertexSet (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    (AffineEquiv.pointReflection ℝ (centerPt hd (sepConst N) (param i))) '' vertexSet hd i =
      vertexSet hd i := by
  set f := AffineEquiv.pointReflection ℝ (centerPt hd (sepConst N) (param i))
  unfold vertexSet
  rw [Set.image_union, ← Set.image_comp]
  have hf2 : (f ∘ f) = id := by
    ext x b
    exact AffineEquiv.pointReflection_involutive ℝ (centerPt hd (sepConst N) (param i)) x |> congrFun <| b
  rw [hf2, Set.image_id, Set.union_comm]

lemma pointReflection_poly (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    (AffineEquiv.pointReflection ℝ (centerPt hd (sepConst N) (param i))) '' poly hd i =
      poly hd i := by
  set f := AffineEquiv.pointReflection ℝ (centerPt hd (sepConst N) (param i))
  unfold poly
  rw [← AffineEquiv.coe_toAffineMap, f.toAffineMap.image_convexHull, AffineEquiv.coe_toAffineMap,
    pointReflection_vertexSet]

lemma poly_isDPolytope (hd : 3 ≤ d) {N : ℕ} (i : Fin N) :
    IsDPolytope (poly hd i) := by
  refine ⟨⟨vertexSet hd i, vertexSet_finite hd i, ⟨_, center_mem_vertexSet hd i⟩, rfl⟩, ?_⟩
  unfold poly
  rw [affineSpan_convexHull]
  rw [eq_top_iff]
  intro x _
  set c := centerPt hd (sepConst N) (param i)
  have hc_mem : c ∈ affineSpan ℝ (vertexSet hd i) :=
    subset_affineSpan ℝ (vertexSet hd i) (center_mem_vertexSet hd i)
  have h_dir : ∀ a : Fin d, stdBasis a ∈ (affineSpan ℝ (vertexSet hd i)).direction := by
    intro a
    have ha_mem : c + scaledVec hd (N : ℝ) (stdBasis a) ∈ affineSpan ℝ (vertexSet hd i) :=
      subset_affineSpan ℝ (vertexSet hd i) (axial_mem_vertexSet hd i a)
    have h_vsub : (c + scaledVec hd (N : ℝ) (stdBasis a)) -ᵥ c ∈
        (affineSpan ℝ (vertexSet hd i)).direction :=
      AffineSubspace.vsub_mem_direction ha_mem hc_mem
    simp only [vsub_eq_sub, add_sub_cancel_left] at h_vsub
    have h_smul := (affineSpan ℝ (vertexSet hd i)).direction.smul_mem
      (safeScale hd (N : ℝ) (stdBasis a))⁻¹ h_vsub
    unfold scaledVec at h_smul
    rwa [inv_smul_smul₀ (safeScale_ne_zero hd (N : ℝ) _)] at h_smul
  have hx_sub : x -ᵥ c ∈ (affineSpan ℝ (vertexSet hd i)).direction := by
    have hx_eq : x -ᵥ c = ∑ a : Fin d, (x -ᵥ c) a • stdBasis a := by
      ext b
      simp [Finset.sum_apply, stdBasis_apply]
    rw [hx_eq]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (h_dir a))
  simpa using AffineSubspace.vadd_mem_of_mem_direction hx_sub hc_mem

lemma ell_pointReflection (hd : 3 ≤ d) (r s : ℝ) (c u : Fin d → ℝ) :
    ell hd r s (AffineEquiv.pointReflection ℝ c u) =
      2 * ell hd r s c - ell hd r s u := by
  have h_apply : AffineEquiv.pointReflection ℝ c u = (2 : ℝ) • c - u := by
    ext b
    simp [Equiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add]
    ring
  rw [h_apply]
  unfold ell
  rw [map_sub, map_smul, smul_eq_mul]
  ring

lemma ell_le_zero_on_halfGenSet (hd : 3 ≤ d) {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    {u : Fin d → ℝ} (hu : u ∈ halfGenSet hd i) :
    ell hd (param i) (param j) u ≤ 0 ∧
      ell hd (param i) (param j)
        (AffineEquiv.pointReflection ℝ (centerPt hd (sepConst N) (param i)) u) ≤ 0 := by
  set B : ℝ := (N : ℝ)
  set c := centerPt hd (sepConst N) (param i)
  have hi0 := param_nonneg i
  have hiB := param_le i
  have hj0 := param_nonneg j
  have hjB := param_le j
  have hij_sq := sq_param_sub_ge_one hij
  have hc_le : ell hd (param i) (param j) c ≤ -10 :=
    ell_centerPt_le hd hi0 hiB hj0 hij_sq
  rcases hu with (rfl | ⟨a, rfl⟩) | hu_contact
  · constructor
    · linarith
    · rw [ell_pointReflection]; linarith
  · have h_bd := LMap_scaledVec_bounds hd hi0 hiB hj0 hjB (stdBasis a)
    have h_ell_add : ell hd (param i) (param j) (c + scaledVec hd B (stdBasis a)) =
        ell hd (param i) (param j) c + LMap hd (param i) (param j) (scaledVec hd B (stdBasis a)) := by
      unfold ell; rw [map_add]; ring
    constructor
    · rw [h_ell_add]; linarith
    · rw [ell_pointReflection, h_ell_add]; linarith
  · rcases Set.mem_iUnion₂.mp hu_contact with ⟨k, hk_mem, a, rfl⟩
    have hk0 := param_nonneg k
    have hkB := param_le k
    set w := tangentVec hd (param i) (param k) a
    have h_bd := LMap_scaledVec_bounds hd hi0 hiB hj0 hjB w
    have h_ell_add :
        ell hd (param i) (param j) (contactBase hd (param i) (param k) + scaledVec hd B w) =
          ell hd (param i) (param j) (contactBase hd (param i) (param k)) +
            LMap hd (param i) (param j) (scaledVec hd B w) := by
      unfold ell; rw [map_add]; ring
    constructor
    · rw [h_ell_add]
      by_cases hkj : k = j
      · subst hkj
        have h_base : ell hd (param i) (param k) (contactBase hd (param i) (param k)) = 0 := by
          rw [ell_contactBase]; ring
        have h_w0 : LMap hd (param i) (param k) (scaledVec hd B w) = 0 := by
          unfold scaledVec w
          rw [map_smul, LMap_tangentVec, smul_zero]
        linarith
      · have hjk_sq : 1 ≤ (param j - param k) ^ 2 := sq_param_sub_ge_one (Ne.symm hkj)
        have hji_sq : 1 ≤ (param j - param i) ^ 2 := sq_param_sub_ge_one (Ne.symm hij)
        have h_prod : 1 ≤ (param j - param i) ^ 2 * (param j - param k) ^ 2 := by
          nlinarith
        have h_base : ell hd (param i) (param j) (contactBase hd (param i) (param k)) ≤ -1 := by
          rw [ell_contactBase]
          have h_zero : (param i - param i) ^ 2 * (param i - param k) ^ 2 = 0 := by ring
          linarith
        linarith
    · rw [ell_pointReflection, h_ell_add]
      have h_ref : 2 * ell hd (param i) (param j) c -
          ell hd (param i) (param j) (contactBase hd (param i) (param k)) ≤ -20 :=
        ell_reflect_contactBase_le hd hi0 hiB hj0 hjB hk0 hkB hij_sq
      linarith

lemma ell_le_zero_on_vertexSet (hd : 3 ≤ d) {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    {v : Fin d → ℝ} (hv : v ∈ vertexSet hd i) :
    ell hd (param i) (param j) v ≤ 0 := by
  rcases hv with hu | ⟨u, hu, rfl⟩
  · exact (ell_le_zero_on_halfGenSet hd hij hu).1
  · exact (ell_le_zero_on_halfGenSet hd hij hu).2

lemma ell_le_zero_on_poly (hd : 3 ≤ d) {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    {x : Fin d → ℝ} (hx : x ∈ poly hd i) :
    ell hd (param i) (param j) x ≤ 0 := by
  have h_conv : Convex ℝ {y : Fin d → ℝ | ell hd (param i) (param j) y ≤ 0} := by
    intro x hx y hy a b ha hb hab
    change ell hd (param i) (param j) x ≤ 0 at hx
    change ell hd (param i) (param j) y ≤ 0 at hy
    change ell hd (param i) (param j) (a • x + b • y) ≤ 0
    have h_aff : ell hd (param i) (param j) (a • x + b • y) =
        a * ell hd (param i) (param j) x + b * ell hd (param i) (param j) y := by
      unfold ell
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have hb_eq : b = 1 - a := by linarith
      subst hb_eq
      ring
    rw [h_aff]
    nlinarith
  exact convexHull_min (fun v hv => ell_le_zero_on_vertexSet hd hij hv) h_conv hx

lemma poly_injective (hd : 3 ≤ d) {N : ℕ} :
    Function.Injective (poly hd (N := N)) := by
  intro i j hP
  by_contra hij
  have hc_i : centerPt hd (sepConst N) (param i) ∈ poly hd j := by
    rw [← hP]
    exact center_mem_poly hd i
  have h_ji : ell hd (param j) (param i) (centerPt hd (sepConst N) (param i)) ≤ 0 :=
    ell_le_zero_on_poly hd (Ne.symm hij) hc_i
  rw [ell_swap] at h_ji
  have h_ij : ell hd (param i) (param j) (centerPt hd (sepConst N) (param i)) ≤ -10 :=
    ell_centerPt_le hd (param_nonneg i) (param_le i) (param_nonneg j) (sq_param_sub_ge_one hij)
  linarith

lemma contact_mem_inter (hd : 3 ≤ d) {N : ℕ} {i j : Fin N} (hij : i ≠ j) (a : Fin d) :
    contactBase hd (param i) (param j) +
      scaledVec hd (N : ℝ) (tangentVec hd (param i) (param j) a) ∈
        poly hd i ∩ poly hd j := by
  constructor
  · exact subset_convexHull ℝ (vertexSet hd i) (contact_mem_vertexSet hd (Ne.symm hij) a)
  · rw [contactBase_comm hd (param i) (param j), tangentVec_comm hd (param i) (param j) a]
    exact subset_convexHull ℝ (vertexSet hd j) (contact_mem_vertexSet hd hij a)

lemma contactBase_mem_inter (hd : 3 ≤ d) {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    contactBase hd (param i) (param j) ∈ poly hd i ∩ poly hd j := by
  have h := contact_mem_inter hd hij (idx0 hd)
  simpa [tangentVec_idx0, scaledVec_zero] using h

lemma direction_inter_eq_ker (hd : 3 ≤ d) {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    (affineSpan ℝ (poly hd i ∩ poly hd j)).direction =
      LinearMap.ker (LMap hd (param i) (param j)) := by
  apply le_antisymm
  · rw [direction_affineSpan, vectorSpan_def ℝ, Submodule.span_le]
    rintro v ⟨x, hx, y, hy, rfl⟩
    simp only [Set.mem_inter_iff] at hx hy
    have hx_le := ell_le_zero_on_poly hd hij hx.1
    have hx_ge : 0 ≤ ell hd (param i) (param j) x := by
      have := ell_le_zero_on_poly hd (Ne.symm hij) hx.2
      rw [ell_swap] at this; linarith
    have hx_eq : ell hd (param i) (param j) x = 0 := le_antisymm hx_le hx_ge
    have hy_le := ell_le_zero_on_poly hd hij hy.1
    have hy_ge : 0 ≤ ell hd (param i) (param j) y := by
      have := ell_le_zero_on_poly hd (Ne.symm hij) hy.2
      rw [ell_swap] at this; linarith
    have hy_eq : ell hd (param i) (param j) y = 0 := le_antisymm hy_le hy_ge
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    dsimp only
    rw [vsub_eq_sub, map_sub]
    unfold ell at hx_eq hy_eq
    linarith
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    set W := (affineSpan ℝ (poly hd i ∩ poly hd j)).direction
    have hw_mem : ∀ a : Fin d, tangentVec hd (param i) (param j) a ∈ W := by
      intro a
      have hm_mem : contactBase hd (param i) (param j) ∈ affineSpan ℝ (poly hd i ∩ poly hd j) :=
        subset_affineSpan ℝ _ (contactBase_mem_inter hd hij)
      have ha_mem :
          contactBase hd (param i) (param j) +
            scaledVec hd (N : ℝ) (tangentVec hd (param i) (param j) a) ∈
              affineSpan ℝ (poly hd i ∩ poly hd j) :=
        subset_affineSpan ℝ _ (contact_mem_inter hd hij a)
      have h_vsub := AffineSubspace.vsub_mem_direction ha_mem hm_mem
      simp only [vsub_eq_sub, add_sub_cancel_left] at h_vsub
      have h_smul := W.smul_mem
        (safeScale hd (N : ℝ) (tangentVec hd (param i) (param j) a))⁻¹ h_vsub
      unfold scaledVec at h_smul
      rwa [inv_smul_smul₀ (safeScale_ne_zero hd (N : ℝ) _)] at h_smul
    set u : Fin d → ℝ :=
      ∑ a ∈ (Finset.univ.erase (idx0 hd) : Finset (Fin d)),
        v a • tangentVec hd (param i) (param j) a
    have hu_W : u ∈ W :=
      Submodule.sum_mem W (fun a _ => Submodule.smul_mem W (v a) (hw_mem a))
    have hu_ker : LMap hd (param i) (param j) u = 0 := by
      unfold u
      rw [map_sum]
      refine Finset.sum_eq_zero (fun a _ => ?_)
      rw [map_smul, LMap_tangentVec, smul_zero]
    have hu_eq_ne0 : ∀ b : Fin d, b ≠ idx0 hd → u b = v b := by
      intro b hb0
      unfold u
      rw [Finset.sum_apply]
      have hb_mem : b ∈ (Finset.univ.erase (idx0 hd) : Finset (Fin d)) :=
        Finset.mem_erase.mpr ⟨hb0, Finset.mem_univ b⟩
      rw [Finset.sum_eq_single b]
      · simp [tangentVec_apply_of_ne_idx0 hd (param i) (param j) hb0 hb0, stdBasis_apply]
      · intro a ha hab
        have ha0 : a ≠ idx0 hd := (Finset.mem_erase.mp ha).1
        rw [Pi.smul_apply, tangentVec_apply_of_ne_idx0 hd (param i) (param j) ha0 hb0]
        simp [stdBasis_apply, Ne.symm hab]
      · intro hb_not
        exact False.elim (hb_not hb_mem)
    have hu_idx1 : u (idx1 hd) = v (idx1 hd) :=
      hu_eq_ne0 (idx1 hd) (Ne.symm (idx0_ne_idx1 hd))
    have hu_idx2 : u (idx2 hd) = v (idx2 hd) :=
      hu_eq_ne0 (idx2 hd) (Ne.symm (idx0_ne_idx2 hd))
    have hu_idx0 : u (idx0 hd) = v (idx0 hd) := by
      rw [LMap_apply, hu_idx1, hu_idx2] at hu_ker
      rw [LMap_apply] at hv
      have h_ne : param i - param j ≠ 0 := sub_ne_zero.mpr (param_ne_of_ne hij)
      have h_mul : (param i - param j) * (u (idx0 hd) - v (idx0 hd)) = 0 := by
        linarith
      rcases mul_eq_zero.mp h_mul with h_abs | h_sub
      · exact False.elim (h_ne h_abs)
      · linarith
    have huv : u = v := by
      ext b
      by_cases hb0 : b = idx0 hd
      · subst hb0; exact hu_idx0
      · exact hu_eq_ne0 b hb0
    rwa [← huv]

lemma finrank_direction_inter (hd : 3 ≤ d) {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Module.finrank ℝ (affineSpan ℝ (poly hd i ∩ poly hd j)).direction + 1 = d := by
  rw [direction_inter_eq_ker hd hij]
  have h_rn := LinearMap.finrank_range_add_finrank_ker (LMap hd (param i) (param j))
  have h_range : LinearMap.range (LMap hd (param i) (param j)) = ⊤ := by
    rw [eq_top_iff]
    intro t _
    rw [LinearMap.mem_range]
    have h_ne : param i - param j ≠ 0 := sub_ne_zero.mpr (param_ne_of_ne hij)
    refine ⟨(t / (param i - param j)) • stdBasis (idx0 hd), ?_⟩
    rw [map_smul, smul_eq_mul, LMap_apply]
    simp [stdBasis_apply, Ne.symm (idx0_ne_idx1 hd), Ne.symm (idx0_ne_idx2 hd),
      div_mul_cancel₀ t h_ne]
  rw [h_range, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h_rn
  omega

end CentrallySymmetricNeighborly

open CentrallySymmetricNeighborly in
theorem centrally_symmetric_neighborly_families (d : ℕ) (hd : 3 ≤ d) (N : ℕ) :
    ∃ S : Finset (Set (Fin d → ℝ)),
      N ≤ S.card ∧
      (∀ P ∈ S, IsDPolytope P ∧
        ∃ c : Fin d → ℝ, (AffineEquiv.pointReflection ℝ c) '' P = P) ∧
      (∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
        (P ∩ Q).Nonempty ∧
        Module.finrank ℝ (affineSpan ℝ (P ∩ Q)).direction + 1 = d) := by
  classical
  refine ⟨Finset.univ.image (poly hd (N := N)), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (poly_injective hd), Finset.card_univ, Fintype.card_fin]
  · intro P hP
    rcases Finset.mem_image.mp hP with ⟨i, _, rfl⟩
    exact ⟨poly_isDPolytope hd i, centerPt hd (sepConst N) (param i), pointReflection_poly hd i⟩
  · intro P hP Q hQ hPQ
    rcases Finset.mem_image.mp hP with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hQ with ⟨j, _, rfl⟩
    have hij : i ≠ j := fun h => hPQ (congrArg (poly hd) h)
    exact ⟨⟨contactBase hd (param i) (param j), contactBase_mem_inter hd hij⟩,
      finrank_direction_inter hd hij⟩

end Grunbaum2003

theorem solution :
    ∀ (d : ℕ) (_hd : 3 ≤ d) (N : ℕ),
    ∃ S : Finset (Set (Fin d → ℝ)),
      N ≤ S.card ∧
      (∀ P ∈ S, Grunbaum2003.IsDPolytope P ∧
        ∃ c : Fin d → ℝ, (AffineEquiv.pointReflection ℝ c) '' P = P) ∧
      (∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
        (P ∩ Q).Nonempty ∧
        Module.finrank ℝ (affineSpan ℝ (P ∩ Q)).direction + 1 = d) :=
  Grunbaum2003.centrally_symmetric_neighborly_families
