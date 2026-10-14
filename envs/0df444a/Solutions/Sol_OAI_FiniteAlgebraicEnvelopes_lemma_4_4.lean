-- Prove2me | solution 1 for OAI.FiniteAlgebraicEnvelopes.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-14T08:22:41.169305+00:00
-- url     : https://prove2.me/submissions/9372348a-d124-4159-8e1d-1cf6f6df8a1f

import Mathlib
import Definitions.Def_BooneHigman_Steinberg
import Definitions.Def_BooneHigman_cornerSub
import Definitions.Def_OAI_FiniteAlgebraicEnvelopes_steinCoeffMap
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_4_2
import Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_lemma_4_3

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable {n : ℕ} {R : Type u} [Ring R]

theorem steinberg_x_zero (i j : Fin n) (hij : i ≠ j) :
    SteinbergGroup.x i j hij (0 : R) = 1 := by
  have h := steinberg_x_add i j hij (0 : R) (0 : R)
  rw [add_zero] at h
  calc SteinbergGroup.x i j hij (0 : R)
      = (SteinbergGroup.x i j hij (0 : R))⁻¹ *
        (SteinbergGroup.x i j hij (0 : R) * SteinbergGroup.x i j hij (0 : R)) := by group
    _ = (SteinbergGroup.x i j hij (0 : R))⁻¹ * SteinbergGroup.x i j hij (0 : R) := by rw [h]
    _ = 1 := by group

theorem steinberg_x_inv (i j : Fin n) (hij : i ≠ j) (a : R) :
    (SteinbergGroup.x i j hij a)⁻¹ = SteinbergGroup.x i j hij (-a) := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, steinberg_x_add, neg_add_cancel, steinberg_x_zero]

theorem lam_zero (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b) :
    lam (0 : R) = 0 := by
  have h := hadd 0 0
  rw [add_zero] at h
  have h2 : lam (0 : R) + lam (0 : R) = lam (0 : R) + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem lam_sum (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    {ι : Type*} (s : Finset ι) (f : ι → R) :
    lam (∑ i ∈ s, f i) = ∑ i ∈ s, lam (f i) := by
  classical
  refine s.induction ?_ ?_
  · simp [lam_zero lam hadd]
  · intro a t hat ih
    rw [Finset.sum_insert hat, hadd, ih, Finset.sum_insert hat]

/-- `lam` applied entrywise to a matrix. -/
noncomputable def matLam (lam : R → R) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => lam (A i j)

theorem matLam_apply (lam : R → R) (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    matLam lam A i j = lam (A i j) := rfl

theorem matLam_add (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (A B : Matrix (Fin n) (Fin n) R) :
    matLam lam (A + B) = matLam lam A + matLam lam B := by
  funext i j
  show lam ((A + B) i j) = lam (A i j) + lam (B i j)
  rw [Matrix.add_apply, hadd]

theorem matLam_zero (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b) :
    matLam lam (0 : Matrix (Fin n) (Fin n) R) = 0 := by
  funext i j
  show lam ((0 : Matrix (Fin n) (Fin n) R) i j) = (0 : Matrix (Fin n) (Fin n) R) i j
  simp [lam_zero lam hadd]

theorem matLam_mul (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (hmul : ∀ a b : R, lam (a * b) = lam a * lam b) (A B : Matrix (Fin n) (Fin n) R) :
    matLam lam (A * B) = matLam lam A * matLam lam B := by
  funext i j
  show lam ((A * B) i j) = (matLam lam A * matLam lam B) i j
  rw [Matrix.mul_apply, Matrix.mul_apply, lam_sum lam hadd]
  exact Finset.sum_congr rfl (fun k _ => hmul (A i k) (B k j))

theorem matLam_single (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (i j : Fin n) (a : R) :
    matLam lam (Matrix.single i j a) = Matrix.single i j (lam a) := by
  funext i' j'
  show lam (Matrix.single i j a i' j') = Matrix.single i j (lam a) i' j'
  simp only [Matrix.single_apply]
  by_cases h : i = i' ∧ j = j'
  · simp [h]
  · simp [h, lam_zero lam hadd]

/-- `g ↦ 1 + lam⁽ⁿ⁾(g - 1)`, equation (15)'s matrix-level map, for a UNIT `g`. -/
noncomputable def mCoeff (lam : R → R) (g : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  1 + matLam lam (g - 1)

theorem mCoeff_mul (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (hmul : ∀ a b : R, lam (a * b) = lam a * lam b) (g h : Matrix (Fin n) (Fin n) R) :
    mCoeff lam g * mCoeff lam h = mCoeff lam (g * h) := by
  unfold mCoeff
  have hgh : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
  rw [hgh, matLam_add lam hadd, matLam_add lam hadd, matLam_mul lam hadd hmul]
  noncomm_ring

theorem mCoeff_one (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b) :
    mCoeff lam (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold mCoeff
  rw [sub_self, matLam_zero lam hadd, add_zero]

/-- The group homomorphism `g ↦ 1 + lam⁽ⁿ⁾(g - 1)` on units, equation (15) in bundled form. -/
noncomputable def matCoeffMap (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (hmul : ∀ a b : R, lam (a * b) = lam a * lam b) :
    (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin n) (Fin n) R)ˣ where
  toFun g := ⟨mCoeff lam g.val, mCoeff lam (g⁻¹).val,
    by rw [mCoeff_mul lam hadd hmul, Units.mul_inv, mCoeff_one lam hadd],
    by rw [mCoeff_mul lam hadd hmul, Units.inv_mul, mCoeff_one lam hadd]⟩
  map_one' := by
    apply Units.ext
    show mCoeff lam (1 : Matrix (Fin n) (Fin n) R) = 1
    exact mCoeff_one lam hadd
  map_mul' g h := by
    apply Units.ext
    show mCoeff lam (g.val * h.val) = mCoeff lam g.val * mCoeff lam h.val
    rw [mCoeff_mul lam hadd hmul]

theorem matCoeffMap_val (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (hmul : ∀ a b : R, lam (a * b) = lam a * lam b) (g : (Matrix (Fin n) (Fin n) R)ˣ) :
    (matCoeffMap lam hadd hmul g : Matrix (Fin n) (Fin n) R) = mCoeff lam g.val := rfl

/-- Equation (15): the coefficient endomorphism `θ` and the matrix representation `π`
commute via `matCoeffMap`, for EVERY `w : St_n(R)` (not just root words reached by a specific
induction): `π(θ(w)) = 1 + lam⁽ⁿ⁾(π(w) - 1)`. -/
theorem steinPi_coeffMap (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (hmul : ∀ a b : R, lam (a * b) = lam a * lam b) (w : SteinbergGroup n R) :
    steinPi (steinCoeffMap lam hadd hmul w) = matCoeffMap lam hadd hmul (steinPi w) := by
  have heq : steinPi.comp (steinCoeffMap lam hadd hmul) =
      (matCoeffMap lam hadd hmul).comp steinPi :=
    PresentedGroup.ext (rels := steinRelations n R) (fun g => by
      show steinPi (steinCoeffMap lam hadd hmul (SteinbergGroup.x g.i g.j g.hij g.a)) =
        matCoeffMap lam hadd hmul (steinPi (SteinbergGroup.x g.i g.j g.hij g.a))
      rw [steinCoeffMap_x, steinPi_x, steinPi_x]
      apply Units.ext
      show (elemUnit g.i g.j g.hij (lam g.a) : Matrix (Fin n) (Fin n) R) =
        mCoeff lam (elemUnit g.i g.j g.hij g.a : Matrix (Fin n) (Fin n) R)
      show (1 : Matrix (Fin n) (Fin n) R) + Matrix.single g.i g.j (lam g.a) =
        1 + matLam lam ((1 + Matrix.single g.i g.j g.a) - 1)
      rw [add_sub_cancel_left, matLam_single lam hadd])
  exact congrFun (congrArg (fun f => f.toFun) heq) w

/-- Equation (15)'s special case: `θ` sends `ker π` into `ker π`, for any additive
multiplicative `lam`. -/
theorem steinCoeffMap_mem_ker (lam : R → R) (hadd : ∀ a b : R, lam (a + b) = lam a + lam b)
    (hmul : ∀ a b : R, lam (a * b) = lam a * lam b) (w : SteinbergGroup n R)
    (hw : steinPi w = 1) :
    steinPi (steinCoeffMap lam hadd hmul w) = 1 := by
  rw [steinPi_coeffMap lam hadd hmul w, hw, map_one]


theorem columnElem_congr (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (c1 c2 : Fin n → R) (h : ∀ i ∈ J, c1 i = c2 i) :
    columnElem J k hk c1 = columnElem J k hk c2 := by
  unfold columnElem
  refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
  simp only [dif_pos (hk i hi), h i hi]

theorem rowElem_congr (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (r1 r2 : Fin n → R) (h : ∀ i ∈ J, r1 i = r2 i) :
    rowElem J k hk r1 = rowElem J k hk r2 := by
  unfold rowElem
  refine Finset.noncommProd_congr rfl (fun i hi => ?_) _
  simp only [dif_pos (hk i hi), h i hi]

theorem columnElem_single (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (i : Fin n) (hi : i ∈ J) (a : R) :
    columnElem J k hk (Function.update (0 : Fin n → R) i a) =
      SteinbergGroup.x i k (hk i hi) a := by
  classical
  set f : Fin n → SteinbergGroup n R := fun i' => if h : i' ≠ k then SteinbergGroup.x i' k h
      ((Function.update (0 : Fin n → R) i a) i') else 1 with hf_def
  have comm : (↑J : Set (Fin n)).Pairwise (Function.onFun Commute f) := by
    intro i' hi' j' hj' hij'
    simp only [Function.onFun, hf_def, dif_pos (hk i' hi'), dif_pos (hk j' hj')]
    exact steinberg_col_commute k (hk i' hi') (hk j' hj') hij' _ _
  show J.noncommProd f comm = SteinbergGroup.x i k (hk i hi) a
  rw [← Finset.mul_noncommProd_erase J hi f comm]
  have hrest : (J.erase i).noncommProd f
      (fun _ hx _ hy hxy => comm (J.mem_of_mem_erase hx) (J.mem_of_mem_erase hy) hxy) = 1 := by
    refine (Finset.noncommProd_eq_pow_card _ _ _ 1 (fun x hx => ?_)).trans (one_pow _)
    have hxne : x ≠ i := (Finset.mem_erase.mp hx).1
    have hx0 : (Function.update (0 : Fin n → R) i a) x = 0 := by
      rw [Function.update_of_ne hxne]; rfl
    show (if h : x ≠ k then SteinbergGroup.x x k h
      ((Function.update (0 : Fin n → R) i a) x) else 1) = 1
    rw [hx0]
    by_cases h : x ≠ k
    · rw [dif_pos h, steinberg_x_zero]
    · rw [dif_neg h]
  rw [hrest, mul_one]
  show (if h : i ≠ k then SteinbergGroup.x i k h ((Function.update (0 : Fin n → R) i a) i)
    else 1) = SteinbergGroup.x i k (hk i hi) a
  rw [dif_pos (hk i hi), Function.update_self]

theorem rowElem_single (J : Finset (Fin n)) (k : Fin n) (hk : ∀ i ∈ J, i ≠ k)
    (i : Fin n) (hi : i ∈ J) (a : R) :
    rowElem J k hk (Function.update (0 : Fin n → R) i a) =
      SteinbergGroup.x k i (hk i hi).symm a := by
  classical
  set f : Fin n → SteinbergGroup n R := fun i' => if h : i' ≠ k then SteinbergGroup.x k i' h.symm
      ((Function.update (0 : Fin n → R) i a) i') else 1 with hf_def
  have comm : (↑J : Set (Fin n)).Pairwise (Function.onFun Commute f) := by
    intro i' hi' j' hj' hij'
    simp only [Function.onFun, hf_def, dif_pos (hk i' hi'), dif_pos (hk j' hj')]
    exact steinberg_row_commute k (hk i' hi') (hk j' hj') hij' _ _
  show J.noncommProd f comm = SteinbergGroup.x k i (hk i hi).symm a
  rw [← Finset.mul_noncommProd_erase J hi f comm]
  have hrest : (J.erase i).noncommProd f
      (fun _ hx _ hy hxy => comm (J.mem_of_mem_erase hx) (J.mem_of_mem_erase hy) hxy) = 1 := by
    refine (Finset.noncommProd_eq_pow_card _ _ _ 1 (fun x hx => ?_)).trans (one_pow _)
    have hxne : x ≠ i := (Finset.mem_erase.mp hx).1
    have hx0 : (Function.update (0 : Fin n → R) i a) x = 0 := by
      rw [Function.update_of_ne hxne]; rfl
    show (if h : x ≠ k then SteinbergGroup.x k x h.symm
      ((Function.update (0 : Fin n → R) i a) x) else 1) = 1
    rw [hx0]
    by_cases h : x ≠ k
    · rw [dif_pos h, steinberg_x_zero]
    · rw [dif_neg h]
  rw [hrest, mul_one]
  show (if h : i ≠ k then SteinbergGroup.x k i h.symm ((Function.update (0 : Fin n → R) i a) i)
    else 1) = SteinbergGroup.x k i (hk i hi).symm a
  rw [dif_pos (hk i hi), Function.update_self]

/-- The coefficient transform a single `h_pq(a)`-conjugation applies to a generator
`x_ij(y)`, as a function of how `i,j` relate to `{p,q}`. Matches the seven-case
formula of `hElem_conj_single`. -/
noncomputable def hStep (p q : Fin n) (a : Rˣ) (i j : Fin n) (y : R) : R :=
  if i = p then (if j = q then (a : R) * y * (a : R) else (a : R) * y)
  else if i = q then (if j = p then (a : R) * y * (a : R) else (a : R) * y)
  else if j = p then y * (a : R)
  else if j = q then y * (a : R)
  else y

section Section42

variable {p q : Fin n} (hpq : p ≠ q)

/-- `w_ij(a) = x_ij(a) x_ji(-a⁻¹) x_ij(a)` for a unit `a`, from §4.2 of the preprint. -/
noncomputable def wElem (a : Rˣ) : SteinbergGroup n R :=
  SteinbergGroup.x p q hpq (a : R) * SteinbergGroup.x q p hpq.symm (-(a⁻¹ : Rˣ) : R) *
    SteinbergGroup.x p q hpq (a : R)

/-- `h_ij(a) = w_ij(a) w_ij(-1)`, from §4.2 of the preprint. -/
noncomputable def hElem (a : Rˣ) : SteinbergGroup n R :=
  wElem hpq a * wElem hpq (-1 : Rˣ)

/-- The matrix of `w_ij(a)`, equation (20). -/
theorem wElem_matrix (a : Rˣ) :
    (steinPi (wElem hpq a) : Matrix (Fin n) (Fin n) R) =
      1 - Matrix.single p p (1 : R) - Matrix.single q q (1 : R) +
        Matrix.single p q (a : R) - Matrix.single q p ((a⁻¹ : Rˣ) : R) := by
  unfold wElem
  rw [map_mul, map_mul, steinPi_x, steinPi_x, Units.val_mul, Units.val_mul]
  show (1 + Matrix.single p q (a : R)) * (1 + Matrix.single q p (-(a⁻¹ : Rˣ) : R)) *
      (1 + Matrix.single p q (a : R)) =
    1 - Matrix.single p p (1 : R) - Matrix.single q q (1 : R) +
      Matrix.single p q (a : R) - Matrix.single q p ((a⁻¹ : Rˣ) : R)
  have hqp_sub : Matrix.single q p (-(a⁻¹ : Rˣ) : R) = -Matrix.single q p ((a⁻¹ : Rˣ) : R) := by
    have h0 : Matrix.single q p ((a⁻¹ : Rˣ) : R) + Matrix.single q p (-(a⁻¹ : Rˣ) : R) = 0 := by
      rw [← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
    exact eq_neg_of_add_eq_zero_right h0
  rw [hqp_sub]
  have haainv : (a : R) * (a⁻¹ : Rˣ) = 1 := Units.mul_inv a
  have hainva : (a⁻¹ : Rˣ) * (a : R) = 1 := Units.inv_mul a
  have step1 : (1 + Matrix.single p q (a : R)) * (1 + (-Matrix.single q p ((a⁻¹ : Rˣ) : R))) =
      1 + (-Matrix.single q p ((a⁻¹ : Rˣ) : R)) + Matrix.single p q (a : R) - Matrix.single p p (1 : R) := by
    rw [mul_add, mul_one, mul_neg, add_mul, one_mul, Matrix.single_mul_single_same, haainv]
    abel
  rw [step1]
  have hcross : (1 + (-Matrix.single q p ((a⁻¹ : Rˣ) : R)) + Matrix.single p q (a : R) -
      Matrix.single p p (1 : R)) * Matrix.single p q (a : R) = -Matrix.single q q (1 : R) := by
    rw [sub_mul, add_mul, add_mul, one_mul, neg_mul,
      Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne (h := hpq.symm),
      Matrix.single_mul_single_same, hainva, one_mul]
    abel
  calc (1 + (-Matrix.single q p ((a⁻¹ : Rˣ) : R)) + Matrix.single p q (a : R) - Matrix.single p p (1 : R)) *
      (1 + Matrix.single p q (a : R))
      = (1 + (-Matrix.single q p ((a⁻¹ : Rˣ) : R)) + Matrix.single p q (a : R) - Matrix.single p p (1 : R)) +
        (1 + (-Matrix.single q p ((a⁻¹ : Rˣ) : R)) + Matrix.single p q (a : R) - Matrix.single p p (1 : R)) *
          Matrix.single p q (a : R) := by rw [mul_add, mul_one]
    _ = (1 + (-Matrix.single q p ((a⁻¹ : Rˣ) : R)) + Matrix.single p q (a : R) - Matrix.single p p (1 : R)) +
        (- Matrix.single q q (1 : R)) := by rw [hcross]
    _ = 1 - Matrix.single p p (1 : R) - Matrix.single q q (1 : R) +
        Matrix.single p q (a : R) - Matrix.single q p ((a⁻¹ : Rˣ) : R) := by abel

/-- The matrix of `h_ij(a)`, equation (20). -/
theorem hElem_matrix (a : Rˣ) :
    (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) =
      1 - Matrix.single p p (1 : R) - Matrix.single q q (1 : R) +
        Matrix.single p p (a : R) + Matrix.single q q ((a⁻¹ : Rˣ) : R) := by
  have hmA := wElem_matrix hpq a
  have hmB := wElem_matrix hpq (-1 : Rˣ)
  have hBneg : ((-1 : Rˣ) : R) = -1 := by push_cast; rfl
  have hBinv : (((-1 : Rˣ)⁻¹ : Rˣ) : R) = -1 := by
    have h1 : (-1 : Rˣ)⁻¹ = (-1 : Rˣ) := by
      apply inv_eq_of_mul_eq_one_right
      apply Units.ext
      show ((-1 : Rˣ) : R) * ((-1 : Rˣ) : R) = 1
      push_cast; rw [neg_mul_neg, one_mul]
    rw [h1, hBneg]
  rw [hBneg, hBinv] at hmB
  have hpq_neg : Matrix.single p q (-1 : R) = -Matrix.single p q (1 : R) := by
    have h0 : Matrix.single p q (1 : R) + Matrix.single p q (-1 : R) = 0 := by
      rw [← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
    exact eq_neg_of_add_eq_zero_right h0
  have hqp_neg : Matrix.single q p (-1 : R) = -Matrix.single q p (1 : R) := by
    have h0 : Matrix.single q p (1 : R) + Matrix.single q p (-1 : R) = 0 := by
      rw [← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
    exact eq_neg_of_add_eq_zero_right h0
  rw [hpq_neg, hqp_neg] at hmB
  have hmB' : (steinPi (wElem hpq (-1 : Rˣ)) : Matrix (Fin n) (Fin n) R) =
      1 - Matrix.single p p (1 : R) - Matrix.single q q (1 : R) -
        Matrix.single p q (1 : R) + Matrix.single q p (1 : R) := by
    rw [hmB]; abel
  unfold hElem
  rw [map_mul, Units.val_mul, hmA, hmB']
  have haainv : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := Units.mul_inv a
  have hainva : ((a⁻¹ : Rˣ) : R) * (a : R) = 1 := Units.inv_mul a
  have epp_pp : Matrix.single p p (1 : R) * Matrix.single p p (1 : R) =
      Matrix.single p p (1 : R) := by rw [Matrix.single_mul_single_same, one_mul]
  have epp_qq : Matrix.single p p (1 : R) * Matrix.single q q (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (1:R) p p q hpq (1:R)
  have epp_pq : Matrix.single p p (1 : R) * Matrix.single p q (1 : R) =
      Matrix.single p q (1 : R) := by rw [Matrix.single_mul_single_same, one_mul]
  have epp_qp : Matrix.single p p (1 : R) * Matrix.single q p (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (1:R) p p q hpq (1:R)
  have eqq_pp : Matrix.single q q (1 : R) * Matrix.single p p (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (1:R) q q p hpq.symm (1:R)
  have eqq_qq : Matrix.single q q (1 : R) * Matrix.single q q (1 : R) =
      Matrix.single q q (1 : R) := by rw [Matrix.single_mul_single_same, one_mul]
  have eqq_pq : Matrix.single q q (1 : R) * Matrix.single p q (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (1:R) q q p hpq.symm (1:R)
  have eqq_qp : Matrix.single q q (1 : R) * Matrix.single q p (1 : R) =
      Matrix.single q p (1 : R) := by rw [Matrix.single_mul_single_same, one_mul]
  have epqa_pp : Matrix.single p q (a : R) * Matrix.single p p (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (a:R) p q p hpq.symm (1:R)
  have epqa_qq : Matrix.single p q (a : R) * Matrix.single q q (1 : R) =
      Matrix.single p q (a : R) := by rw [Matrix.single_mul_single_same, mul_one]
  have epqa_pq : Matrix.single p q (a : R) * Matrix.single p q (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (a:R) p q p hpq.symm (1:R)
  have epqa_qp : Matrix.single p q (a : R) * Matrix.single q p (1 : R) =
      Matrix.single p p (a : R) := by rw [Matrix.single_mul_single_same, mul_one]
  have eqpa_pp : Matrix.single q p ((a⁻¹ : Rˣ) : R) * Matrix.single p p (1 : R) =
      Matrix.single q p ((a⁻¹ : Rˣ) : R) := by rw [Matrix.single_mul_single_same, mul_one]
  have eqpa_qq : Matrix.single q p ((a⁻¹ : Rˣ) : R) * Matrix.single q q (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne ((a⁻¹ : Rˣ):R) q p q hpq (1:R)
  have eqpa_pq : Matrix.single q p ((a⁻¹ : Rˣ) : R) * Matrix.single p q (1 : R) =
      Matrix.single q q ((a⁻¹ : Rˣ) : R) := by rw [Matrix.single_mul_single_same, mul_one]
  have eqpa_qp : Matrix.single q p ((a⁻¹ : Rˣ) : R) * Matrix.single q p (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne ((a⁻¹ : Rˣ):R) q p q hpq (1:R)
  simp only [sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one,
    epp_pp, epp_qq, epp_pq, epp_qp, eqq_pp, eqq_qq, eqq_pq, eqq_qp,
    epqa_pp, epqa_qq, epqa_pq, epqa_qp, eqpa_pp, eqpa_qq, eqpa_pq, eqpa_qp]
  abel

theorem hElem_mem_steinSub (a : Rˣ) : hElem hpq a ∈ steinSub ({p, q} : Finset (Fin n)) := by
  unfold hElem wElem
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hmem1 : SteinbergGroup.x p q hpq (a : R) ∈ steinSub ({p, q} : Finset (Fin n)) :=
    Subgroup.subset_closure ⟨p, q, hpq, (a : R), hp, hq, rfl⟩
  have hmem2 : SteinbergGroup.x q p hpq.symm (-(a⁻¹ : Rˣ) : R) ∈
      steinSub ({p, q} : Finset (Fin n)) :=
    Subgroup.subset_closure ⟨q, p, hpq.symm, (-(a⁻¹ : Rˣ) : R), hq, hp, rfl⟩
  have hmem1' : SteinbergGroup.x p q hpq ((-1 : Rˣ) : R) ∈ steinSub ({p, q} : Finset (Fin n)) :=
    Subgroup.subset_closure ⟨p, q, hpq, ((-1 : Rˣ) : R), hp, hq, rfl⟩
  have hmem2' : SteinbergGroup.x q p hpq.symm (-((-1 : Rˣ)⁻¹ : Rˣ) : R) ∈
      steinSub ({p, q} : Finset (Fin n)) :=
    Subgroup.subset_closure ⟨q, p, hpq.symm, (-((-1 : Rˣ)⁻¹ : Rˣ) : R), hq, hp, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hmem1 hmem2) hmem1)
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ hmem1' hmem2') hmem1')

/-- The matrix of `h_pq(a)` when `a` is its own inverse. -/
theorem hElem_matrix_symm (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) :
    (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) =
      1 - Matrix.single p p (1 : R) - Matrix.single q q (1 : R) +
        Matrix.single p p (a : R) + Matrix.single q q (a : R) := by
  rw [hElem_matrix hpq a, hb]

theorem hElem_col_entry (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (i' : Fin n) :
    (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) i' p = if i' = p then (a : R) else 0 := by
  have hmat := hElem_matrix_symm hpq a hb
  have hent := congrFun (congrFun hmat i') p
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : i' = p
  · subst h1; simp [hpq.symm, hpq]
  · by_cases h2 : i' = q
    · subst h2; simp [hpq, h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem hElem_row_entry (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (j' : Fin n) :
    (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) p j' = if j' = p then (a : R) else 0 := by
  have hmat := hElem_matrix_symm hpq a hb
  have hent := congrFun (congrFun hmat p) j'
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : j' = p
  · subst h1; simp [hpq.symm, hpq]
  · by_cases h2 : j' = q
    · subst h2; simp [hpq, h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem hElem_col_entry_q (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (i' : Fin n) :
    (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) i' q = if i' = q then (a : R) else 0 := by
  have hmat := hElem_matrix_symm hpq a hb
  have hent := congrFun (congrFun hmat i') q
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : i' = p
  · subst h1; simp [hpq, hpq.symm]
  · by_cases h2 : i' = q
    · subst h2; simp [hpq]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem hElem_row_entry_q (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (j' : Fin n) :
    (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) q j' = if j' = q then (a : R) else 0 := by
  have hmat := hElem_matrix_symm hpq a hb
  have hent := congrFun (congrFun hmat q) j'
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : j' = p
  · subst h1; simp [hpq, hpq.symm]
  · by_cases h2 : j' = q
    · subst h2; simp [hpq]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

include hpq in
theorem hElem_conj_col_p (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (k : Fin n) (hkp : k ≠ p) (hkq : k ≠ q)
    (y : R) :
    hElem hpq a * SteinbergGroup.x p k hkp.symm y * (hElem hpq a)⁻¹ =
      SteinbergGroup.x p k hkp.symm ((a : R) * y) := by
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hJmem : ∀ i ∈ ({p, q} : Finset (Fin n)), i ≠ k := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hkp.symm
    · exact hkq.symm
  set c : Fin n → R := Function.update (0 : Fin n → R) p y with hc_def
  have heq := (lemma_4_2 ({p, q} : Finset (Fin n)) k hJmem (hElem hpq a)
    (hElem_mem_steinSub hpq a) c (0 : Fin n → R)).1
  rw [columnElem_single _ k _ p hp y] at heq
  have hcp : c p = y := by simp [hc_def]
  have hcq : c q = 0 := by simp [hc_def, Function.update_of_ne hpq.symm]
  have heq2 : (fun i' => ∑ j ∈ ({p, q} : Finset (Fin n)),
      (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) i' j * c j) =
      Function.update (0 : Fin n → R) p ((a : R) * y) := by
    funext i'
    rw [Finset.sum_pair hpq, hcp, hcq, mul_zero, add_zero, hElem_col_entry hpq a hb i']
    rcases eq_or_ne i' p with rfl | hip
    · rw [if_pos rfl]; simp [Function.update_self]
    · rw [if_neg hip, zero_mul]
      simp [Function.update_of_ne hip]
  rw [heq2, columnElem_single _ k _ p hp ((a : R) * y)] at heq
  exact heq

include hpq in
theorem hElem_sq_eq_one (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) :
    (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) *
      (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) = 1 := by
  have haa : (a : R) * (a : R) = 1 := by
    have := Units.mul_inv a
    rwa [hb] at this
  rw [hElem_matrix_symm hpq a hb]
  have epp_pp : Matrix.single p p (1 : R) * Matrix.single p p (1 : R) =
      Matrix.single p p (1 : R) := by rw [Matrix.single_mul_single_same, one_mul]
  have eqq_qq : Matrix.single q q (1 : R) * Matrix.single q q (1 : R) =
      Matrix.single q q (1 : R) := by rw [Matrix.single_mul_single_same, one_mul]
  have epp_qq : Matrix.single p p (1 : R) * Matrix.single q q (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (1 : R) p p q hpq (1 : R)
  have eqq_pp : Matrix.single q q (1 : R) * Matrix.single p p (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (1 : R) q q p hpq.symm (1 : R)
  have epp_a_pp : Matrix.single p p (1 : R) * Matrix.single p p (a : R) =
      Matrix.single p p (a : R) := by rw [Matrix.single_mul_single_same, one_mul]
  have epp_a_qq : Matrix.single p p (a : R) * Matrix.single q q (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (a : R) p p q hpq (1 : R)
  have epp_app : Matrix.single p p (a : R) * Matrix.single p p (1 : R) =
      Matrix.single p p (a : R) := by rw [Matrix.single_mul_single_same, mul_one]
  have epp_qq_a : Matrix.single q q (1 : R) * Matrix.single p p (a : R) = 0 :=
    Matrix.single_mul_single_of_ne (1 : R) q q p hpq.symm (a : R)
  have eqq_app : Matrix.single q q (a : R) * Matrix.single p p (1 : R) = 0 :=
    Matrix.single_mul_single_of_ne (a : R) q q p hpq.symm (1 : R)
  have epp_qqa : Matrix.single p p (1 : R) * Matrix.single q q (a : R) = 0 :=
    Matrix.single_mul_single_of_ne (1 : R) p p q hpq (a : R)
  have eqq_aqq : Matrix.single q q (a : R) * Matrix.single q q (1 : R) =
      Matrix.single q q (a : R) := by rw [Matrix.single_mul_single_same, mul_one]
  have eqq_qqa : Matrix.single q q (1 : R) * Matrix.single q q (a : R) =
      Matrix.single q q (a : R) := by rw [Matrix.single_mul_single_same, one_mul]
  have eppa_appa : Matrix.single p p (a : R) * Matrix.single p p (a : R) =
      Matrix.single p p (1 : R) := by rw [Matrix.single_mul_single_same, haa]
  have eppa_qqa : Matrix.single p p (a : R) * Matrix.single q q (a : R) = 0 :=
    Matrix.single_mul_single_of_ne (a : R) p p q hpq (a : R)
  have eqqa_ppa : Matrix.single q q (a : R) * Matrix.single p p (a : R) = 0 :=
    Matrix.single_mul_single_of_ne (a : R) q q p hpq.symm (a : R)
  have eqqa_qqa : Matrix.single q q (a : R) * Matrix.single q q (a : R) =
      Matrix.single q q (1 : R) := by rw [Matrix.single_mul_single_same, haa]
  simp only [sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one,
    epp_pp, eqq_qq, epp_qq, eqq_pp, epp_a_pp, epp_a_qq, epp_app, epp_qq_a,
    eqq_app, epp_qqa, eqq_aqq, eqq_qqa, eppa_appa, eppa_qqa, eqqa_ppa, eqqa_qqa]
  abel

include hpq in
/-- The matrix of `h_pq(a)⁻¹` when `a` is its own inverse: the same uniform diagonal. -/
theorem hElem_inv_matrix_symm (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) :
    (steinPi (hElem hpq a)⁻¹ : Matrix (Fin n) (Fin n) R) =
      1 - Matrix.single p p (1 : R) - Matrix.single q q (1 : R) +
        Matrix.single p p (a : R) + Matrix.single q q (a : R) := by
  have hU : steinPi (hElem hpq a) * steinPi (hElem hpq a) = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    exact hElem_sq_eq_one hpq a hb
  rw [map_inv, inv_eq_of_mul_eq_one_right hU, hElem_matrix_symm hpq a hb]

theorem hElem_inv_row_entry (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (j' : Fin n) :
    (steinPi (hElem hpq a)⁻¹ : Matrix (Fin n) (Fin n) R) p j' = if j' = p then (a : R) else 0 := by
  have hmat := hElem_inv_matrix_symm hpq a hb
  have hent := congrFun (congrFun hmat p) j'
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : j' = p
  · subst h1; simp [hpq.symm, hpq]
  · by_cases h2 : j' = q
    · subst h2; simp [hpq, h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem hElem_inv_row_entry_q (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (j' : Fin n) :
    (steinPi (hElem hpq a)⁻¹ : Matrix (Fin n) (Fin n) R) q j' = if j' = q then (a : R) else 0 := by
  have hmat := hElem_inv_matrix_symm hpq a hb
  have hent := congrFun (congrFun hmat q) j'
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply] at hent
  rw [hent]
  by_cases h1 : j' = p
  · subst h1; simp [hpq, hpq.symm]
  · by_cases h2 : j' = q
    · subst h2; simp [hpq]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

include hpq in
theorem hElem_conj_col_q (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (k : Fin n) (hkp : k ≠ p) (hkq : k ≠ q)
    (y : R) :
    hElem hpq a * SteinbergGroup.x q k hkq.symm y * (hElem hpq a)⁻¹ =
      SteinbergGroup.x q k hkq.symm ((a : R) * y) := by
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hJmem : ∀ i ∈ ({p, q} : Finset (Fin n)), i ≠ k := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hkp.symm
    · exact hkq.symm
  set c : Fin n → R := Function.update (0 : Fin n → R) q y with hc_def
  have heq := (lemma_4_2 ({p, q} : Finset (Fin n)) k hJmem (hElem hpq a)
    (hElem_mem_steinSub hpq a) c (0 : Fin n → R)).1
  rw [columnElem_single _ k _ q hq y] at heq
  have hcp : c p = 0 := by simp [hc_def, Function.update_of_ne hpq]
  have hcq : c q = y := by simp [hc_def]
  have heq2 : (fun i' => ∑ j ∈ ({p, q} : Finset (Fin n)),
      (steinPi (hElem hpq a) : Matrix (Fin n) (Fin n) R) i' j * c j) =
      Function.update (0 : Fin n → R) q ((a : R) * y) := by
    funext i'
    rw [Finset.sum_pair hpq, hcp, hcq, mul_zero, zero_add, hElem_col_entry_q hpq a hb i']
    rcases eq_or_ne i' q with rfl | hiq
    · rw [if_pos rfl]; simp [Function.update_self]
    · rw [if_neg hiq, zero_mul]
      simp [Function.update_of_ne hiq]
  rw [heq2, columnElem_single _ k _ q hq ((a : R) * y)] at heq
  exact heq

include hpq in
theorem hElem_conj_row_p (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (k : Fin n) (hkp : k ≠ p) (hkq : k ≠ q)
    (y : R) :
    hElem hpq a * SteinbergGroup.x k p hkp y * (hElem hpq a)⁻¹ =
      SteinbergGroup.x k p hkp (y * (a : R)) := by
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hJmem : ∀ i ∈ ({p, q} : Finset (Fin n)), i ≠ k := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hkp.symm
    · exact hkq.symm
  set r : Fin n → R := Function.update (0 : Fin n → R) p y with hr_def
  have heq := (lemma_4_2 ({p, q} : Finset (Fin n)) k hJmem (hElem hpq a)
    (hElem_mem_steinSub hpq a) (0 : Fin n → R) r).2
  rw [rowElem_single _ k _ p hp y] at heq
  have hrp : r p = y := by simp [hr_def]
  have hrq : r q = 0 := by simp [hr_def, Function.update_of_ne hpq.symm]
  have heq2 : (fun j => ∑ i' ∈ ({p, q} : Finset (Fin n)),
      r i' * (steinPi (hElem hpq a)⁻¹ : Matrix (Fin n) (Fin n) R) i' j) =
      Function.update (0 : Fin n → R) p (y * (a : R)) := by
    funext j
    rw [Finset.sum_pair hpq, hrp, hrq, zero_mul, add_zero, hElem_inv_row_entry hpq a hb j]
    rcases eq_or_ne j p with rfl | hjp
    · rw [if_pos rfl]; simp [Function.update_self]
    · rw [if_neg hjp, mul_zero]
      simp [Function.update_of_ne hjp]
  rw [heq2, rowElem_single _ k _ p hp (y * (a : R))] at heq
  exact heq

include hpq in
theorem hElem_conj_row_q (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (k : Fin n) (hkp : k ≠ p) (hkq : k ≠ q)
    (y : R) :
    hElem hpq a * SteinbergGroup.x k q hkq y * (hElem hpq a)⁻¹ =
      SteinbergGroup.x k q hkq (y * (a : R)) := by
  have hp : p ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_self p {q}
  have hq : q ∈ ({p, q} : Finset (Fin n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  have hJmem : ∀ i ∈ ({p, q} : Finset (Fin n)), i ≠ k := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hkp.symm
    · exact hkq.symm
  set r : Fin n → R := Function.update (0 : Fin n → R) q y with hr_def
  have heq := (lemma_4_2 ({p, q} : Finset (Fin n)) k hJmem (hElem hpq a)
    (hElem_mem_steinSub hpq a) (0 : Fin n → R) r).2
  rw [rowElem_single _ k _ q hq y] at heq
  have hrp : r p = 0 := by simp [hr_def, Function.update_of_ne hpq]
  have hrq : r q = y := by simp [hr_def]
  have heq2 : (fun j => ∑ i' ∈ ({p, q} : Finset (Fin n)),
      r i' * (steinPi (hElem hpq a)⁻¹ : Matrix (Fin n) (Fin n) R) i' j) =
      Function.update (0 : Fin n → R) q (y * (a : R)) := by
    funext j
    rw [Finset.sum_pair hpq, hrp, hrq, zero_mul, zero_add, hElem_inv_row_entry_q hpq a hb j]
    rcases eq_or_ne j q with rfl | hjq
    · rw [if_pos rfl]; simp [Function.update_self]
    · rw [if_neg hjq, mul_zero]
      simp [Function.update_of_ne hjq]
  rw [heq2, rowElem_single _ k _ q hq (y * (a : R))] at heq
  exact heq

include hpq in
theorem hElem_conj_pq (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (k0 : Fin n) (hk0p : k0 ≠ p) (hk0q : k0 ≠ q)
    (y : R) :
    hElem hpq a * SteinbergGroup.x p q hpq y * (hElem hpq a)⁻¹ =
      SteinbergGroup.x p q hpq ((a : R) * y * (a : R)) := by
  have hchain : SteinbergGroup.x p k0 hk0p.symm y * SteinbergGroup.x k0 q hk0q (1 : R) *
      (SteinbergGroup.x p k0 hk0p.symm y)⁻¹ * (SteinbergGroup.x k0 q hk0q (1 : R))⁻¹ =
      SteinbergGroup.x p q hpq y := by
    have hc := steinberg_x_chain p k0 q hk0p.symm hk0q hpq y (1 : R)
    rwa [mul_one] at hc
  rw [← hchain]
  have hc1 := hElem_conj_col_p hpq a hb k0 hk0p hk0q y
  have hc2 := hElem_conj_row_q hpq a hb k0 hk0p hk0q (1 : R)
  rw [one_mul] at hc2
  have hfinal : (hElem hpq a) *
      (SteinbergGroup.x p k0 hk0p.symm y * SteinbergGroup.x k0 q hk0q (1 : R) *
        (SteinbergGroup.x p k0 hk0p.symm y)⁻¹ * (SteinbergGroup.x k0 q hk0q (1 : R))⁻¹) *
      (hElem hpq a)⁻¹ =
      SteinbergGroup.x p k0 hk0p.symm ((a : R) * y) * SteinbergGroup.x k0 q hk0q (a : R) *
        (SteinbergGroup.x p k0 hk0p.symm ((a : R) * y))⁻¹ *
        (SteinbergGroup.x k0 q hk0q (a : R))⁻¹ := by
    calc (hElem hpq a) *
        (SteinbergGroup.x p k0 hk0p.symm y * SteinbergGroup.x k0 q hk0q (1 : R) *
          (SteinbergGroup.x p k0 hk0p.symm y)⁻¹ * (SteinbergGroup.x k0 q hk0q (1 : R))⁻¹) *
        (hElem hpq a)⁻¹
        = (hElem hpq a) * SteinbergGroup.x p k0 hk0p.symm y * (hElem hpq a)⁻¹ *
          ((hElem hpq a) * SteinbergGroup.x k0 q hk0q (1 : R) * (hElem hpq a)⁻¹) *
          ((hElem hpq a) * SteinbergGroup.x p k0 hk0p.symm y * (hElem hpq a)⁻¹)⁻¹ *
          ((hElem hpq a) * SteinbergGroup.x k0 q hk0q (1 : R) * (hElem hpq a)⁻¹)⁻¹ := by group
      _ = SteinbergGroup.x p k0 hk0p.symm ((a : R) * y) * SteinbergGroup.x k0 q hk0q (a : R) *
          (SteinbergGroup.x p k0 hk0p.symm ((a : R) * y))⁻¹ *
          (SteinbergGroup.x k0 q hk0q (a : R))⁻¹ := by rw [hc1, hc2]
  rw [hfinal, steinberg_x_chain p k0 q hk0p.symm hk0q hpq ((a : R) * y) (a : R)]

include hpq in
theorem hElem_conj_qp (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (k0 : Fin n) (hk0p : k0 ≠ p) (hk0q : k0 ≠ q)
    (y : R) :
    hElem hpq a * SteinbergGroup.x q p hpq.symm y * (hElem hpq a)⁻¹ =
      SteinbergGroup.x q p hpq.symm ((a : R) * y * (a : R)) := by
  have hchain : SteinbergGroup.x q k0 hk0q.symm y * SteinbergGroup.x k0 p hk0p (1 : R) *
      (SteinbergGroup.x q k0 hk0q.symm y)⁻¹ * (SteinbergGroup.x k0 p hk0p (1 : R))⁻¹ =
      SteinbergGroup.x q p hpq.symm y := by
    have hc := steinberg_x_chain q k0 p hk0q.symm hk0p hpq.symm y (1 : R)
    rwa [mul_one] at hc
  rw [← hchain]
  have hc1 := hElem_conj_col_q hpq a hb k0 hk0p hk0q y
  have hc2 := hElem_conj_row_p hpq a hb k0 hk0p hk0q (1 : R)
  rw [one_mul] at hc2
  have hfinal : (hElem hpq a) *
      (SteinbergGroup.x q k0 hk0q.symm y * SteinbergGroup.x k0 p hk0p (1 : R) *
        (SteinbergGroup.x q k0 hk0q.symm y)⁻¹ * (SteinbergGroup.x k0 p hk0p (1 : R))⁻¹) *
      (hElem hpq a)⁻¹ =
      SteinbergGroup.x q k0 hk0q.symm ((a : R) * y) * SteinbergGroup.x k0 p hk0p (a : R) *
        (SteinbergGroup.x q k0 hk0q.symm ((a : R) * y))⁻¹ *
        (SteinbergGroup.x k0 p hk0p (a : R))⁻¹ := by
    calc (hElem hpq a) *
        (SteinbergGroup.x q k0 hk0q.symm y * SteinbergGroup.x k0 p hk0p (1 : R) *
          (SteinbergGroup.x q k0 hk0q.symm y)⁻¹ * (SteinbergGroup.x k0 p hk0p (1 : R))⁻¹) *
        (hElem hpq a)⁻¹
        = (hElem hpq a) * SteinbergGroup.x q k0 hk0q.symm y * (hElem hpq a)⁻¹ *
          ((hElem hpq a) * SteinbergGroup.x k0 p hk0p (1 : R) * (hElem hpq a)⁻¹) *
          ((hElem hpq a) * SteinbergGroup.x q k0 hk0q.symm y * (hElem hpq a)⁻¹)⁻¹ *
          ((hElem hpq a) * SteinbergGroup.x k0 p hk0p (1 : R) * (hElem hpq a)⁻¹)⁻¹ := by group
      _ = SteinbergGroup.x q k0 hk0q.symm ((a : R) * y) * SteinbergGroup.x k0 p hk0p (a : R) *
          (SteinbergGroup.x q k0 hk0q.symm ((a : R) * y))⁻¹ *
          (SteinbergGroup.x k0 p hk0p (a : R))⁻¹ := by rw [hc1, hc2]
  rw [hfinal, steinberg_x_chain q k0 p hk0q.symm hk0p hpq.symm ((a : R) * y) (a : R)]

theorem wElem_commute_disjoint (c : Rˣ) (i j : Fin n) (hij : i ≠ j) (hip : i ≠ p) (hiq : i ≠ q)
    (hjp : j ≠ p) (hjq : j ≠ q) (y : R) :
    Commute (wElem hpq c) (SteinbergGroup.x i j hij y) := by
  unfold wElem
  have h1 : Commute (SteinbergGroup.x p q hpq (c : R)) (SteinbergGroup.x i j hij y) :=
    steinberg_x_commute p q i j hpq hij hjp.symm hiq.symm (c : R) y
  have h2 : Commute (SteinbergGroup.x q p hpq.symm (-(c⁻¹ : Rˣ) : R))
      (SteinbergGroup.x i j hij y) :=
    steinberg_x_commute q p i j hpq.symm hij hjq.symm hip.symm (-(c⁻¹ : Rˣ) : R) y
  exact (h1.mul_left h2).mul_left h1

include hpq in
theorem hElem_commute_disjoint (a : Rˣ) (i j : Fin n) (hij : i ≠ j) (hip : i ≠ p) (hiq : i ≠ q)
    (hjp : j ≠ p) (hjq : j ≠ q) (y : R) :
    Commute (hElem hpq a) (SteinbergGroup.x i j hij y) := by
  unfold hElem
  exact (wElem_commute_disjoint hpq a i j hij hip hiq hjp hjq y).mul_left
    (wElem_commute_disjoint hpq (-1 : Rˣ) i j hij hip hiq hjp hjq y)

include hpq in
/-- The full single-`hElem` conjugation formula for an arbitrary generator `x_ij(y)`,
covering all seven ways `{i,j}` can meet `{p,q}`. Needs an auxiliary index `k0` outside
`{p,q}` for the two same-pair cases (unused in the other five). -/
theorem hElem_conj_single (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (k0 : Fin n) (hk0p : k0 ≠ p)
    (hk0q : k0 ≠ q) (i j : Fin n) (hij : i ≠ j) (y : R) :
    hElem hpq a * SteinbergGroup.x i j hij y * (hElem hpq a)⁻¹ =
      SteinbergGroup.x i j hij
        (if i = p then (if j = q then (a : R) * y * (a : R) else (a : R) * y)
         else if i = q then (if j = p then (a : R) * y * (a : R) else (a : R) * y)
         else if j = p then y * (a : R)
         else if j = q then y * (a : R)
         else y) := by
  by_cases h1 : i = p
  · subst h1
    by_cases h2 : j = q
    · subst h2
      simp only [if_true]
      exact hElem_conj_pq hpq a hb k0 hk0p hk0q y
    · simp only [if_neg h2]
      exact hElem_conj_col_p hpq a hb j (Ne.symm hij) h2 y
  · by_cases h1' : i = q
    · subst h1'
      by_cases h2 : j = p
      · subst h2
        simp only [if_neg h1]
        exact hElem_conj_qp hpq a hb k0 hk0p hk0q y
      · simp only [if_neg h1, if_neg h2]
        exact hElem_conj_col_q hpq a hb j h2 (Ne.symm hij) y
    · by_cases h2 : j = p
      · subst h2
        simp only [if_neg h1, if_neg h1']
        exact hElem_conj_row_p hpq a hb i h1 h1' y
      · by_cases h2' : j = q
        · subst h2'
          simp only [if_neg h1, if_neg h1', if_neg h2]
          exact hElem_conj_row_q hpq a hb i h1 h1' y
        · simp only [if_neg h1, if_neg h1', if_neg h2, if_neg h2']
          rw [(hElem_commute_disjoint hpq a i j hij h1 h1' h2 h2' y).eq,
            mul_inv_cancel_right]

include hpq in
/-- `hElem_conj_single` restated with the `hStep` coefficient function, for composing
several `hElem` conjugations in a row. -/
theorem hElem_conj_single' (a : Rˣ) (hb : (a⁻¹ : Rˣ) = a) (k0 : Fin n) (hk0p : k0 ≠ p)
    (hk0q : k0 ≠ q) (i j : Fin n) (hij : i ≠ j) (y : R) :
    hElem hpq a * SteinbergGroup.x i j hij y * (hElem hpq a)⁻¹ =
      SteinbergGroup.x i j hij (hStep p q a i j y) :=
  hElem_conj_single hpq a hb k0 hk0p hk0q i j hij y

end Section42

section Equation21

variable {p1 q1 p2 q2 p3 q3 : Fin n} (h1 : p1 ≠ q1) (h2 : p2 ≠ q2) (h3 : p3 ≠ q3)
  (hp1p2 : p1 ≠ p2) (hq1p2 : q1 ≠ p2) (hp1q2 : p1 ≠ q2) (hq1q2 : q1 ≠ q2)
  (hp1p3 : p1 ≠ p3) (hq1p3 : q1 ≠ p3) (hp1q3 : p1 ≠ q3) (hq1q3 : q1 ≠ q3)
  (hp2p3 : p2 ≠ p3) (hq2p3 : q2 ≠ p3) (hp2q3 : p2 ≠ q3) (hq2q3 : q2 ≠ q3)

include h1 h2 h3 in
/-- Equation (21): conjugating an arbitrary generator `x_ij(y)` by the product of three
`h`-elements over three (not necessarily disjoint) pairs, expressed via three nested
applications of the single-pair transform `hStep`. Each pair needs a witness index
outside it (`k0k`) for its own same-pair case; no relation between the three pairs
themselves is required for this composition to hold. -/
theorem hElem_triple_conj (b : Rˣ) (hb : (b⁻¹ : Rˣ) = b)
    (k01 : Fin n) (hk01p : k01 ≠ p1) (hk01q : k01 ≠ q1)
    (k02 : Fin n) (hk02p : k02 ≠ p2) (hk02q : k02 ≠ q2)
    (k03 : Fin n) (hk03p : k03 ≠ p3) (hk03q : k03 ≠ q3)
    (i j : Fin n) (hij : i ≠ j) (y : R) :
    (hElem h1 b * hElem h2 b * hElem h3 b) * SteinbergGroup.x i j hij y *
        (hElem h1 b * hElem h2 b * hElem h3 b)⁻¹ =
      SteinbergGroup.x i j hij
        (hStep p1 q1 b i j (hStep p2 q2 b i j (hStep p3 q3 b i j y))) := by
  calc (hElem h1 b * hElem h2 b * hElem h3 b) * SteinbergGroup.x i j hij y *
      (hElem h1 b * hElem h2 b * hElem h3 b)⁻¹
      = hElem h1 b * (hElem h2 b * (hElem h3 b * SteinbergGroup.x i j hij y *
          (hElem h3 b)⁻¹) * (hElem h2 b)⁻¹) * (hElem h1 b)⁻¹ := by group
    _ = hElem h1 b * (hElem h2 b * (SteinbergGroup.x i j hij (hStep p3 q3 b i j y)) *
          (hElem h2 b)⁻¹) * (hElem h1 b)⁻¹ := by
        rw [hElem_conj_single' h3 b hb k03 hk03p hk03q i j hij y]
    _ = hElem h1 b * (SteinbergGroup.x i j hij
          (hStep p2 q2 b i j (hStep p3 q3 b i j y))) * (hElem h1 b)⁻¹ := by
        rw [hElem_conj_single' h2 b hb k02 hk02p hk02q i j hij (hStep p3 q3 b i j y)]
    _ = SteinbergGroup.x i j hij
          (hStep p1 q1 b i j (hStep p2 q2 b i j (hStep p3 q3 b i j y))) := by
        rw [hElem_conj_single' h1 b hb k01 hk01p hk01q i j hij
          (hStep p2 q2 b i j (hStep p3 q3 b i j y))]

include h1 h2 h3 hp1p2 hq1p2 hp1q2 hq1q2 hp1p3 hq1p3 hp1q3 hq1q3 hp2p3 hq2p3 hp2q3 hq2q3 in
/-- When the three pairs are mutually disjoint, conjugating the FIRST pair's own
generator `x_{p1,q1}(y)` by `D = h_{p1q1}(b) h_{p2q2}(b) h_{p3q3}(b)` gives `byb` (the
`a = a⁻¹` case of equation (21)): the second and third factors act trivially since
`p1,q1` lie outside both of their pairs. -/
theorem hElem_triple_conj_same_pair1 (b : Rˣ) (hb : (b⁻¹ : Rˣ) = b) (y : R) :
    (hElem h1 b * hElem h2 b * hElem h3 b) * SteinbergGroup.x p1 q1 h1 y *
        (hElem h1 b * hElem h2 b * hElem h3 b)⁻¹ =
      SteinbergGroup.x p1 q1 h1 ((b : R) * y * (b : R)) := by
  have := hElem_triple_conj h1 h2 h3 b hb p2 hp1p2.symm hq1p2.symm p1 hp1p2 hp1q2
    p1 hp1p3 hp1q3 p1 q1 h1 y
  rw [this]
  congr 1
  unfold hStep
  simp [hp1p2, hq1p2, hp1q2, hq1q2, hp1p3, hq1p3, hp1q3, hq1q3]

include h1 h2 h3 hp1p2 hq1p2 hp1q2 hq1q2 hp1p3 hq1p3 hp1q3 hq1q3 hp2p3 hq2p3 hp2q3 hq2q3 in
/-- The mirror of `hElem_triple_conj_same_pair1` for the SECOND pair's own generator. -/
theorem hElem_triple_conj_same_pair2 (b : Rˣ) (hb : (b⁻¹ : Rˣ) = b) (y : R) :
    (hElem h1 b * hElem h2 b * hElem h3 b) * SteinbergGroup.x p2 q2 h2 y *
        (hElem h1 b * hElem h2 b * hElem h3 b)⁻¹ =
      SteinbergGroup.x p2 q2 h2 ((b : R) * y * (b : R)) := by
  have := hElem_triple_conj h1 h2 h3 b hb p2 hp1p2.symm hq1p2.symm p1 hp1p2 hp1q2
    p1 hp1p3 hp1q3 p2 q2 h2 y
  rw [this]
  congr 1
  unfold hStep
  simp [hp1p2.symm, hq1p2.symm, hp1q2.symm, hq1q2.symm, hp2p3, hq2p3, hp2q3, hq2q3]

include h1 h2 h3 hp1p2 hq1p2 hp1q2 hq1q2 hp1p3 hq1p3 hp1q3 hq1q3 hp2p3 hq2p3 hp2q3 hq2q3 in
/-- The mirror of `hElem_triple_conj_same_pair1` for the THIRD pair's own generator. -/
theorem hElem_triple_conj_same_pair3 (b : Rˣ) (hb : (b⁻¹ : Rˣ) = b) (y : R) :
    (hElem h1 b * hElem h2 b * hElem h3 b) * SteinbergGroup.x p3 q3 h3 y *
        (hElem h1 b * hElem h2 b * hElem h3 b)⁻¹ =
      SteinbergGroup.x p3 q3 h3 ((b : R) * y * (b : R)) := by
  have := hElem_triple_conj h1 h2 h3 b hb p3 hp1p3.symm hq1p3.symm p3 hp2p3.symm hq2p3.symm
    p1 hp1p3 hp1q3 p3 q3 h3 y
  rw [this]
  congr 1
  unfold hStep
  simp [hp1p3.symm, hq1p3.symm, hp1q3.symm, hq1q3.symm, hp2p3.symm, hq2p3.symm, hp2q3.symm,
    hq2q3.symm]

include h1 h2 h3 hp1p2 hq1p2 hp1q2 hq1q2 hp1p3 hq1p3 hp1q3 hq1q3 hp2p3 hq2p3 hp2q3 hq2q3 in
/-- A cross-pair instance: conjugating `x_{p1,p2}(y)` (one index from pair 1, one from
pair 2) by `D` gives `byb`, since `p1`'s pair contributes a left multiplication by `b`
and `p2`'s pair a right multiplication, while the third pair acts trivially. -/
theorem hElem_triple_conj_cross_12 (b : Rˣ) (hb : (b⁻¹ : Rˣ) = b) (y : R) :
    (hElem h1 b * hElem h2 b * hElem h3 b) *
        SteinbergGroup.x p1 p2 hp1p2 y *
        (hElem h1 b * hElem h2 b * hElem h3 b)⁻¹ =
      SteinbergGroup.x p1 p2 hp1p2 ((b : R) * y * (b : R)) := by
  have := hElem_triple_conj h1 h2 h3 b hb p2 hp1p2.symm hq1p2.symm p1 hp1p2 hp1q2
    p1 hp1p3 hp1q3 p1 p2 hp1p2 y
  rw [this]
  congr 1
  unfold hStep
  simp [hp1p2, hq1p2.symm, hp1q2, hq1q2, hp1p3, hq1p3, hp1q3, hq1q3, hp2p3, hq2p3, hp2q3, hq2q3,
    mul_assoc]

end Equation21

/-- The preprint's actual equation (21): specialized to `n = 6` with the fixed pairs
`(0,1), (2,3), (4,5)` partitioning all of `Fin 6`, `D x_ij(y) D⁻¹ = x_ij(byb)` holds for
EVERY generator, not just the five shapes checked individually above — there is no
"outside all three pairs" case left once the three pairs exhaust the index set. Proved by
exhaustive case-splitting on `i, j : Fin 6` rather than one named corollary per shape. -/
theorem hElem_triple_conj_fin6 {R : Type u} [Ring R] (b : Rˣ) (hb : (b⁻¹ : Rˣ) = b)
    (i j : Fin 6) (hij : i ≠ j) (y : R) :
    (hElem (show (0 : Fin 6) ≠ 1 by decide) b * hElem (show (2 : Fin 6) ≠ 3 by decide) b *
        hElem (show (4 : Fin 6) ≠ 5 by decide) b) * SteinbergGroup.x i j hij y *
      (hElem (show (0 : Fin 6) ≠ 1 by decide) b * hElem (show (2 : Fin 6) ≠ 3 by decide) b *
        hElem (show (4 : Fin 6) ≠ 5 by decide) b)⁻¹ =
      SteinbergGroup.x i j hij ((b : R) * y * (b : R)) := by
  have := hElem_triple_conj (show (0 : Fin 6) ≠ 1 by decide) (show (2 : Fin 6) ≠ 3 by decide)
    (show (4 : Fin 6) ≠ 5 by decide) b hb
    2 (by decide) (by decide) 0 (by decide) (by decide) 0 (by decide) (by decide) i j hij y
  rw [this]
  congr 1
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (simp_all [hStep]; try noncomm_ring)

/-! ### Lemma 4.4: interchanging and splitting corners.

`cornerSub` and `lemma_4_3` are restated here (unproved locally) exactly as already PROVED
and ACCEPTED on prove2.me (`Sol_lemma43.lean`, commits `ebe0901`/`b93d338`) — restating them
avoids duplicating that file's ~600 lines of matrix algebra into this one; the real
submission will `import` the accepted theorem instead of this local stub. -/

/-- Every generator of `St_n(R)` maps, under the coefficient endomorphism `λ ↦ ψ(a)E`, into a
generator of `cornerSub E`, PROVIDED `E` is idempotent and commutes with `ψ(R)`. -/
theorem steinCoeffMap_corner_gen (psi : R → R) (E : R) (hE : E * E = E)
    (hcomm : ∀ a : R, E * psi a = psi a * E) (i j : Fin n) (hij : i ≠ j) (a : R) :
    SteinbergGroup.x i j hij (psi a * E) ∈ cornerSub E := by
  have heq : psi a * E = E * (psi a) * E := by rw [hcomm a, mul_assoc, hE]
  rw [heq]
  exact Subgroup.subset_closure ⟨i, j, hij, psi a, rfl⟩

/-- `steinCoeffMap` for `λ(a) = ψ(a)E` sends EVERY element of `St_n(R)` into `cornerSub E`
(not just the generators), provided `E` is idempotent and commutes with `ψ(R)`. -/
theorem steinCoeffMap_mem_cornerSub (psi : R → R) (E : R) (hE : E * E = E)
    (hcomm : ∀ a : R, E * psi a = psi a * E)
    (hadd : ∀ a b : R, psi (a + b) * E = psi a * E + psi b * E)
    (hmul : ∀ a b : R, psi (a * b) * E = (psi a * E) * (psi b * E))
    (z : SteinbergGroup n R) :
    steinCoeffMap (fun a => psi a * E) hadd hmul z ∈ cornerSub E := by
  have hmem : z ∈ Subgroup.comap (steinCoeffMap (fun a => psi a * E) hadd hmul) (cornerSub E) := by
    apply PresentedGroup.generated_by (steinRelations n R)
    intro w
    show steinCoeffMap (fun a => psi a * E) hadd hmul
      (SteinbergGroup.x w.i w.j w.hij w.a) ∈ cornerSub E
    rw [steinCoeffMap_x]
    exact steinCoeffMap_corner_gen psi E hE hcomm w.i w.j w.hij w.a
  exact Subgroup.mem_comap.mp hmem

/-! ### Lemma 4.4 itself: the ring algebra for `b = d + d* + 1 - E - F`. -/

section BElem

variable {E F d dstar : R} (hEE : E * E = E) (hFF : F * F = F) (hEF : E * F = 0)
  (hFE : F * E = 0) (hd : d = F * d * E) (hdstar : dstar = E * dstar * F)
  (hdstard : dstar * d = E) (hddstar : d * dstar = F)

include hFF hd in
theorem bElem_Fd : F * d = d := by
  nth_rewrite 1 [hd]
  rw [show F * (F * d * E) = F * F * d * E from by noncomm_ring, hFF]
  exact hd.symm

include hEE hd in
theorem bElem_dE : d * E = d := by
  nth_rewrite 1 [hd]
  rw [show F * d * E * E = F * d * (E * E) from by noncomm_ring, hEE]
  exact hd.symm

include hEF hd in
theorem bElem_dF : d * F = 0 := by
  nth_rewrite 1 [hd]
  rw [show F * d * E * F = F * d * (E * F) from by noncomm_ring, hEF, mul_zero]

include hEF hd in
theorem bElem_Ed : E * d = 0 := by
  nth_rewrite 1 [hd]
  rw [show E * (F * d * E) = (E * F) * d * E from by noncomm_ring, hEF, zero_mul, zero_mul]

include hEE hdstar in
theorem bElem_Edstar : E * dstar = dstar := by
  nth_rewrite 1 [hdstar]
  rw [show E * (E * dstar * F) = E * E * dstar * F from by noncomm_ring, hEE]
  exact hdstar.symm

include hFF hdstar in
theorem bElem_dstarF : dstar * F = dstar := by
  nth_rewrite 1 [hdstar]
  rw [show E * dstar * F * F = E * dstar * (F * F) from by noncomm_ring, hFF]
  exact hdstar.symm

include hFE hdstar in
theorem bElem_dstarE : dstar * E = 0 := by
  nth_rewrite 1 [hdstar]
  rw [show E * dstar * F * E = E * dstar * (F * E) from by noncomm_ring, hFE, mul_zero]

include hFE hdstar in
theorem bElem_Fdstar : F * dstar = 0 := by
  nth_rewrite 1 [hdstar]
  rw [show F * (E * dstar * F) = (F * E) * dstar * F from by noncomm_ring, hFE, zero_mul,
    zero_mul]

include hEF hd in
theorem bElem_dd : d * d = 0 := by
  calc d * d = d * (F * d * E) := by nth_rewrite 2 [hd]; rfl
    _ = (d * F) * (d * E) := by noncomm_ring
    _ = 0 * (d * E) := by rw [bElem_dF hEF hd]
    _ = 0 := by rw [zero_mul]

include hFE hdstar in
theorem bElem_dstardstar : dstar * dstar = 0 := by
  calc dstar * dstar = dstar * (E * dstar * F) := by nth_rewrite 2 [hdstar]; rfl
    _ = (dstar * E) * (dstar * F) := by noncomm_ring
    _ = 0 * (dstar * F) := by rw [bElem_dstarE hFE hdstar]
    _ = 0 := by rw [zero_mul]

include hEF hFF hd in
/-- `(1-E-F)` annihilates `d` on both sides. -/
theorem bElem_oneEF_mul_d : (1 - E - F) * d = 0 := by
  rw [sub_mul, sub_mul, one_mul, bElem_Ed hEF hd, bElem_Fd hFF hd, sub_zero, sub_self]

include hEE hEF hd in
theorem bElem_d_mul_oneEF : d * (1 - E - F) = 0 := by
  rw [mul_sub, mul_sub, mul_one, bElem_dE hEE hd, bElem_dF hEF hd, sub_self, sub_zero]

include hFE hEE hdstar in
/-- The mirror facts for `d*` (annihilation by `(1-E-F)`), needed symmetrically. -/
theorem bElem_oneEF_mul_dstar : (1 - E - F) * dstar = 0 := by
  rw [sub_mul, sub_mul, one_mul, bElem_Edstar hEE hdstar, bElem_Fdstar hFE hdstar, sub_zero,
    sub_self]

include hFF hFE hdstar in
theorem bElem_dstar_mul_oneEF : dstar * (1 - E - F) = 0 := by
  rw [mul_sub, mul_sub, mul_one, bElem_dstarE hFE hdstar, bElem_dstarF hFF hdstar, sub_zero,
    sub_self]

include hEE hFF hEF hFE in
theorem bElem_oneEF_sq : (1 - E - F) * (1 - E - F) = 1 - E - F := by
  have expand : (1 - E - F) * (1 - E - F) =
      1 - E - F - E + E * E + E * F - F + F * E + F * F := by noncomm_ring
  rw [expand, hEE, hEF, hFE, hFF]
  noncomm_ring

include hEE hFF hEF hFE hd hdstar hdstard hddstar in
/-- `b² = 1` from the paper's proof of Lemma 4.4 (p. 13), for `b = d + d* + 1 - E - F`. -/
theorem bElem_sq_eq_one : (d + dstar + 1 - E - F) * (d + dstar + 1 - E - F) = 1 := by
  have expand : (d + dstar + 1 - E - F) * (d + dstar + 1 - E - F) =
      d * d + d * dstar + d * (1 - E - F) + dstar * d + dstar * dstar +
        dstar * (1 - E - F) + (1 - E - F) * d + (1 - E - F) * dstar +
        (1 - E - F) * (1 - E - F) := by noncomm_ring
  rw [expand, bElem_dd hEF hd, hddstar, bElem_d_mul_oneEF hEE hEF hd, hdstard,
    bElem_dstardstar hFE hdstar, bElem_dstar_mul_oneEF hFF hFE hdstar,
    bElem_oneEF_mul_d hFF hEF hd, bElem_oneEF_mul_dstar hEE hFE hdstar,
    bElem_oneEF_sq hEE hFF hEF hFE]
  noncomm_ring

include hEE hFE hd hdstar hEF hddstar in
/-- `bEb = F` from the paper's proof of Lemma 4.4 (p. 13). -/
theorem bElem_bEb_eq_F : (d + dstar + 1 - E - F) * E * (d + dstar + 1 - E - F) = F := by
  have step1 : (d + dstar + 1 - E - F) * E = d := by
    have expand : (d + dstar + 1 - E - F) * E = d * E + dstar * E + E - E * E - F * E := by
      noncomm_ring
    rw [expand, bElem_dE hEE hd, bElem_dstarE hFE hdstar, hEE, hFE]
    noncomm_ring
  rw [step1]
  have expand2 : d * (d + dstar + 1 - E - F) = d * d + d * dstar + d * (1 - E - F) := by
    noncomm_ring
  rw [expand2, bElem_dd hEF hd, hddstar, bElem_d_mul_oneEF hEE hEF hd]
  abel

end BElem
variable {E F d dstar : R} (hEE : E * E = E) (hFF : F * F = F) (hEF : E * F = 0)
  (hFE : F * E = 0) (hd : d = F * d * E) (hdstar : dstar = E * dstar * F)
  (hdstard : dstar * d = E) (hddstar : d * dstar = F)
  (psi : R → R) (hpsi_add : ∀ a b : R, psi (a + b) = psi a + psi b)
  (hpsi_mul : ∀ a b : R, psi (a * b) = psi a * psi b)
  (hEpsi : ∀ a : R, E * psi a = psi a * E) (hFpsi : ∀ a : R, F * psi a = psi a * F)
  (hdpsi : ∀ a : R, d * psi a = psi a * d) (hdstarpsi : ∀ a : R, dstar * psi a = psi a * dstar)

include hEE hFF hEF hFE hd hdstar hdstard hddstar hEpsi hFpsi hdpsi hdstarpsi in
theorem bElem_psi (a : R) :
    (d + dstar + 1 - E - F) * psi a = psi a * (d + dstar + 1 - E - F) := by
  have h1 : d * psi a = psi a * d := hdpsi a
  have h2 : dstar * psi a = psi a * dstar := hdstarpsi a
  have h3 : E * psi a = psi a * E := hEpsi a
  have h4 : F * psi a = psi a * F := hFpsi a
  calc (d + dstar + 1 - E - F) * psi a
      = d * psi a + dstar * psi a + psi a - E * psi a - F * psi a := by noncomm_ring
    _ = psi a * d + psi a * dstar + psi a - psi a * E - psi a * F := by rw [h1, h2, h3, h4]
    _ = psi a * (d + dstar + 1 - E - F) := by noncomm_ring

include hEE hFF hEF hFE hd hdstar hdstard hddstar hpsi_add hpsi_mul hEpsi hFpsi hdpsi hdstarpsi in
/-- **Lemma 4.4** (interchanging and splitting corners): for `z ∈ ker π`, its images under
the coefficient maps `a ↦ ψ(a)E` and `a ↦ ψ(a)F` agree. -/
theorem lemma_4_4 (haddE : ∀ a b : R, psi (a + b) * E = psi a * E + psi b * E)
    (hmulE : ∀ a b : R, psi (a * b) * E = (psi a * E) * (psi b * E))
    (haddF : ∀ a b : R, psi (a + b) * F = psi a * F + psi b * F)
    (hmulF : ∀ a b : R, psi (a * b) * F = (psi a * F) * (psi b * F))
    (z : SteinbergGroup 6 R) (hz : steinPi z = 1) :
    steinCoeffMap (fun a => psi a * E) haddE hmulE z =
      steinCoeffMap (fun a => psi a * F) haddF hmulF z := by
  have hbb : (d + dstar + 1 - E - F) * (d + dstar + 1 - E - F) = 1 :=
    bElem_sq_eq_one hEE hFF hEF hFE hd hdstar hdstard hddstar
  set b : R := d + dstar + 1 - E - F with hb_def
  set bU : Rˣ := ⟨b, b, hbb, hbb⟩ with hbU_def
  have hbUinv : bU⁻¹ = bU := by apply Units.ext; rfl
  set D : SteinbergGroup 6 R :=
    hElem (show (0 : Fin 6) ≠ 1 by decide) bU * hElem (show (2 : Fin 6) ≠ 3 by decide) bU *
      hElem (show (4 : Fin 6) ≠ 5 by decide) bU with hD_def
  have hbEb : (bU : R) * E * (bU : R) = F :=
    bElem_bEb_eq_F hEE hEF hFE hd hdstar hddstar
  have hbcomm : ∀ a : R, (bU : R) * psi a = psi a * (bU : R) :=
    bElem_psi hEE hFF hEF hFE hd hdstar hdstard hddstar psi hEpsi hFpsi hdpsi hdstarpsi
  have hagree : (MulAut.conj D).toMonoidHom.comp (steinCoeffMap (fun a => psi a * E) haddE hmulE)
      = steinCoeffMap (fun a => psi a * F) haddF hmulF :=
    PresentedGroup.ext (rels := steinRelations 6 R) (fun w => by
      show D * steinCoeffMap (fun a => psi a * E) haddE hmulE
          (SteinbergGroup.x w.i w.j w.hij w.a) * D⁻¹ =
        steinCoeffMap (fun a => psi a * F) haddF hmulF (SteinbergGroup.x w.i w.j w.hij w.a)
      rw [steinCoeffMap_x, steinCoeffMap_x, hD_def,
        hElem_triple_conj_fin6 bU hbUinv w.i w.j w.hij (psi w.a * E)]
      congr 1
      calc (bU : R) * (psi w.a * E) * (bU : R)
          = (bU : R) * psi w.a * E * (bU : R) := by noncomm_ring
        _ = psi w.a * (bU : R) * E * (bU : R) := by rw [hbcomm w.a]
        _ = psi w.a * ((bU : R) * E * (bU : R)) := by noncomm_ring
        _ = psi w.a * F := by rw [hbEb])
  have hDzE : D * steinCoeffMap (fun a => psi a * E) haddE hmulE z * D⁻¹ =
      steinCoeffMap (fun a => psi a * F) haddF hmulF z :=
    congrFun (congrArg (fun f => f.toFun) hagree) z
  have hzE_mem : steinCoeffMap (fun a => psi a * E) haddE hmulE z ∈ cornerSub E :=
    steinCoeffMap_mem_cornerSub psi E hEE hEpsi haddE hmulE z
  have hzE_ker : steinPi (steinCoeffMap (fun a => psi a * E) haddE hmulE z) = 1 :=
    steinCoeffMap_mem_ker (fun a => psi a * E) haddE hmulE z hz
  have hzE_central := lemma_4_3 (E := E) (F := F) (d := d) (dstar := dstar)
    (hpq := show (0 : Fin 6) ≠ 1 by decide) (hex := ⟨2, by decide, by decide⟩)
    (hE := hEE) (hEF := hEF) (hFE := hFE) (hF := hFF) (hd := hd) (hdstar := hdstar)
    (hdstard := hdstard) (hddstar := hddstar)
    (w0 := steinCoeffMap (fun a => psi a * E) haddE hmulE z) (hw0 := hzE_mem) (hid := hzE_ker)
    (v := D)
  have hfix : D * steinCoeffMap (fun a => psi a * E) haddE hmulE z * D⁻¹ =
      steinCoeffMap (fun a => psi a * E) haddE hmulE z := by
    rw [← hzE_central]; group
  rw [hfix] at hDzE
  exact hDzE

end FiniteAlgebraicEnvelopes
end OAI

open OAI.FiniteAlgebraicEnvelopes

universe u

theorem solution {R : Type u} [Ring R] {E F d dstar : R}
    (hEE : E * E = E) (hFF : F * F = F) (hEF : E * F = 0)
    (hFE : F * E = 0) (hd : d = F * d * E) (hdstar : dstar = E * dstar * F)
    (hdstard : dstar * d = E) (hddstar : d * dstar = F)
    (psi : R → R) (hpsi_add : ∀ a b : R, psi (a + b) = psi a + psi b)
    (hpsi_mul : ∀ a b : R, psi (a * b) = psi a * psi b)
    (hEpsi : ∀ a : R, E * psi a = psi a * E) (hFpsi : ∀ a : R, F * psi a = psi a * F)
    (hdpsi : ∀ a : R, d * psi a = psi a * d) (hdstarpsi : ∀ a : R, dstar * psi a = psi a * dstar)
    (haddE : ∀ a b : R, psi (a + b) * E = psi a * E + psi b * E)
    (hmulE : ∀ a b : R, psi (a * b) * E = (psi a * E) * (psi b * E))
    (haddF : ∀ a b : R, psi (a + b) * F = psi a * F + psi b * F)
    (hmulF : ∀ a b : R, psi (a * b) * F = (psi a * F) * (psi b * F))
    (z : SteinbergGroup 6 R) (hz : steinPi z = 1) :
    steinCoeffMap (fun a => psi a * E) haddE hmulE z =
      steinCoeffMap (fun a => psi a * F) haddF hmulF z :=
  lemma_4_4 hEE hFF hEF hFE hd hdstar hdstard hddstar psi hpsi_add hpsi_mul hEpsi hFpsi hdpsi
    hdstarpsi haddE hmulE haddF hmulF z hz
