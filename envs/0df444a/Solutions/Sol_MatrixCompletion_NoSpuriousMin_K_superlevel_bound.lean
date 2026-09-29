-- Prove2me | solution 1 for MatrixCompletion.NoSpuriousMin.K_superlevel_bound
-- status  : ACCEPTED   (disprove)
-- author  : @LukeBernese
-- created : 2026-08-14T02:41:45.706802+00:00
-- url     : https://prove2.me/submissions/775d9f6d-5baf-48e2-83fd-c38356b7f44f

/-
A counterexample to `MatrixCompletion.NoSpuriousMin.perturbation_terms_bound`
(Chen–Li 2019, Lemma 4.8, as instantiated by this mission).

The configuration is completely explicit and deterministic:

  d = 10¹²,  r = 1,  Z = U = 10⁻⁶ · 𝟙  (a d × 1 column),  Ω = everything,
  p = 1 − 5·10⁻⁵,  α = 2·10⁻⁴ = 200‖Z‖_{2→∞},  λ = 100‖Ω − pJ‖ = 5·10⁹,
  X = U except in the first row, where X₀ = 3.2 α = 6.4·10⁻⁴.

Taking Ω to be the full square collapses the model layer to closed forms:
`projSet Ω A = A`, so `sampDev Ω p A B = (1−p)⟨A,B⟩`, and the sampling matrix minus
`p J` is the constant matrix `(1−p) J`, whose largest singular value is `(1−p) d`.

Every hypothesis of the milestone then holds — including `spec_bound` and
`tangent_conc`, the latter for *all* symmetric matrices by Cauchy–Schwarz — while the
conclusion fails by a factor of about 9.5·10⁵.  The culprit is `SampleCondition`'s
constant `10¹⁰`, which is far too small for the mission's own windows
`α ≤ 200‖Z‖_{2→∞}` and `λ ≤ 200‖Ω − pJ‖`.
-/
import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix Finset MatrixCompletion.NoSpuriousMin WithLp

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option maxHeartbeats 400000

namespace MS6CE

/-! ### `vecNorm` basics -/

lemma vecNorm_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ vecNorm x := Real.sqrt_nonneg _

lemma vecNorm_sq {n : ℕ} (x : Fin n → ℝ) : vecNorm x ^ 2 = ∑ i, x i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma vecNorm_eq_norm {n : ℕ} (x : Fin n → ℝ) :
    vecNorm x = ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq, vecNorm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp [sq_abs]

/-- Cauchy–Schwarz for a plain finite sum. -/
lemma abs_sum_mul_le {n : ℕ} (x y : Fin n → ℝ) :
    |∑ j, x j * y j| ≤ vecNorm x * vecNorm y := by
  have h := abs_real_inner_le_norm (toLp 2 x : EuclideanSpace ℝ (Fin n)) (toLp 2 y)
  rw [EuclideanSpace.inner_toLp_toLp] at h
  simpa [vecNorm_eq_norm, dotProduct, mul_comm] using h

/-- Cauchy–Schwarz for the matrix (Frobenius) pairing. -/
lemma abs_innerM_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) :
    |innerM A B| ≤ frobNorm A * frobNorm B := by
  classical
  have hsq : innerM A B ^ 2 ≤ frobSq A * frobSq B := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
      (fun q => A q.1 q.2) (fun q => B q.1 q.2)
    simpa [innerM, frobSq, Fintype.sum_prod_type] using h
  have h1 : (0 : ℝ) ≤ frobSq A :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : (0 : ℝ) ≤ frobSq B :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [frobNorm, frobNorm, ← Real.sqrt_mul h1,
    show |innerM A B| = Real.sqrt (innerM A B ^ 2) from (Real.sqrt_sq_eq_abs _).symm]
  exact Real.sqrt_le_sqrt hsq

/-- The Frobenius bound on `sigmaMax`, and hence its boundedness. -/
lemma vecNorm_mulVec_le_frob {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {v : Fin n → ℝ}
    (hv : vecNorm v = 1) : vecNorm (A *ᵥ v) ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
  have hv2 : ∑ j, v j ^ 2 = 1 := by rw [← vecNorm_sq, hv]; norm_num
  rw [vecNorm]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, (A *ᵥ v) i ^ 2
      ≤ ∑ i, (∑ j, A i j ^ 2) * ∑ j, v j ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        simpa [Matrix.mulVec, dotProduct] using
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => A i j) v
    _ = ∑ i, ∑ j, A i j ^ 2 := by simp [hv2]

lemma bddAbove_sigma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    BddAbove (Set.range fun v : {v : Fin n → ℝ // vecNorm v = 1} => vecNorm (A.mulVec v.1)) := by
  refine ⟨Real.sqrt (∑ i, ∑ j, A i j ^ 2), ?_⟩
  rintro _ ⟨v, rfl⟩
  exact vecNorm_mulVec_le_frob A v.2

/-! ### The configuration -/

/-- The dimension `d = 10¹²`. -/
abbrev D : ℕ := 10 ^ 12

/-- The first row index. -/
def i0 : Fin D := ⟨0, by norm_num⟩

noncomputable def zz : ℝ := 1 / 10 ^ 6          -- every entry of `Z`
noncomputable def x0 : ℝ := 64 / 10 ^ 5         -- the outlying row of `X`
noncomputable def dl : ℝ := 639 / 10 ^ 6        -- `x0 - zz`
noncomputable def al : ℝ := 2 / 10 ^ 4          -- the regularization radius `α`
noncomputable def pp : ℝ := 1 - 5 / 10 ^ 5      -- the sampling rate `p`
noncomputable def lm : ℝ := 5 * 10 ^ 9          -- the regularization weight `λ`

noncomputable def ZM : Matrix (Fin D) (Fin 1) ℝ := Matrix.of fun _ _ => zz
noncomputable def XM : Matrix (Fin D) (Fin 1) ℝ := Matrix.of fun i _ => if i = i0 then x0 else zz

lemma zz_pos : 0 < zz := by norm_num [zz]
lemma x0_pos : 0 < x0 := by norm_num [x0]
lemma dl_pos : 0 < dl := by norm_num [dl]
lemma dl_eq : dl = x0 - zz := by norm_num [dl, x0, zz]

/-- Sums of a constant over `Fin D`. -/
lemma sum_const_D (c : ℝ) : (∑ _i : Fin D, c) = 10 ^ 12 * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

lemma vecNorm_fin_one {c : ℝ} (hc : 0 ≤ c) : vecNorm (fun _ : Fin 1 => c) = c := by
  rw [vecNorm, Fin.sum_univ_one, Real.sqrt_sq hc]

/-! ### Row norms -/

lemma rowNorm_ZM (i : Fin D) : rowNorm ZM i = zz := vecNorm_fin_one zz_pos.le

lemma rowNorm_XM_i0 : rowNorm XM i0 = x0 := by
  rw [rowNorm, show XM i0 = fun _ : Fin 1 => x0 from by funext j; simp [XM]]
  exact vecNorm_fin_one x0_pos.le

lemma rowNorm_XM_ne {i : Fin D} (hi : i ≠ i0) : rowNorm XM i = zz := by
  rw [rowNorm, show XM i = fun _ : Fin 1 => zz from by funext j; simp [XM, hi]]
  exact vecNorm_fin_one zz_pos.le

lemma subM_apply (i : Fin D) (j : Fin 1) :
    (XM - ZM) i j = if i = i0 then dl else 0 := by
  simp only [Matrix.sub_apply, XM, ZM, Matrix.of_apply]
  split <;> simp [dl_eq]

lemma rowNorm_sub_i0 : rowNorm (XM - ZM) i0 = dl := by
  rw [rowNorm, show (XM - ZM) i0 = fun _ : Fin 1 => dl from by
    funext j; rw [subM_apply, if_pos rfl]]
  exact vecNorm_fin_one dl_pos.le

lemma rowNorm_sub_ne {i : Fin D} (hi : i ≠ i0) : rowNorm (XM - ZM) i = 0 := by
  rw [rowNorm, show (XM - ZM) i = fun _ : Fin 1 => (0 : ℝ) from by
    funext j; rw [subM_apply, if_neg hi]]
  exact vecNorm_fin_one le_rfl

/-! ### `Z`'s scalar invariants -/

lemma frobSq_ZM : frobSq ZM = 1 := by
  rw [frobSq]
  simp only [ZM, Matrix.of_apply, Fin.sum_univ_one]
  rw [sum_const_D]
  norm_num [zz]

lemma frobNorm_ZM : frobNorm ZM = 1 := by rw [frobNorm, frobSq_ZM, Real.sqrt_one]

lemma twoInftyNorm_ZM : twoInftyNorm ZM = zz := by
  rw [twoInftyNorm, show (fun i => rowNorm ZM i) = fun _ : Fin D => zz from
    funext rowNorm_ZM]
  exact ciSup_const

lemma vecNorm_fin_one_eq {v : Fin 1 → ℝ} : vecNorm v = |v 0| := by
  rw [vecNorm, Fin.sum_univ_one, Real.sqrt_sq_eq_abs]

lemma sphere_nonempty : Nonempty {v : Fin 1 → ℝ // vecNorm v = 1} :=
  ⟨⟨fun _ => 1, by rw [vecNorm_fin_one_eq]; norm_num⟩⟩

lemma vecNorm_mulVec_ZM (v : {v : Fin 1 → ℝ // vecNorm v = 1}) :
    vecNorm (ZM *ᵥ v.1) = 1 := by
  have hv : |v.1 0| = 1 := by rw [← vecNorm_fin_one_eq]; exact v.2
  have hrow : (ZM *ᵥ v.1) = fun _ : Fin D => zz * v.1 0 := by
    funext i; simp [Matrix.mulVec, dotProduct, ZM]
  rw [hrow, vecNorm, sum_const_D]
  rw [show (10 : ℝ) ^ 12 * (zz * v.1 0) ^ 2 = (v.1 0) ^ 2 from by rw [zz]; ring]
  rw [Real.sqrt_sq_eq_abs, hv]

lemma sigmaMax_ZM : sigmaMax ZM = 1 := by
  have := sphere_nonempty
  rw [sigmaMax, show (fun v : {v : Fin 1 → ℝ // vecNorm v = 1} => vecNorm (ZM *ᵥ v.1))
    = fun _ => (1 : ℝ) from funext vecNorm_mulVec_ZM]
  exact ciSup_const

lemma sigmaMin_ZM : sigmaMin ZM = 1 := by
  have := sphere_nonempty
  rw [sigmaMin, show (fun v : {v : Fin 1 → ℝ // vecNorm v = 1} => vecNorm (ZM *ᵥ v.1))
    = fun _ => (1 : ℝ) from funext vecNorm_mulVec_ZM]
  exact ciInf_const

/-! ### The sample: `Ω` is the full square -/

def OM : Finset (Fin D × Fin D) := Finset.univ

lemma projSet_univ (A : Matrix (Fin D) (Fin D) ℝ) : projSet OM A = A := by
  funext i j; simp [projSet, OM]

lemma sampDev_univ (A B : Matrix (Fin D) (Fin D) ℝ) :
    sampDev OM pp A B = (1 - pp) * innerM A B := by
  rw [sampDev, projSet_univ, projSet_univ]; ring

/-- The centered sampling matrix is the constant matrix `(1 − p) J`. -/
noncomputable def CM : Matrix (Fin D) (Fin D) ℝ := Matrix.of fun _ _ => 1 - pp

lemma centered_eq : sampMatrix OM - pp • (Matrix.of fun _ _ : Fin D => (1 : ℝ)) = CM := by
  funext i j
  simp [sampMatrix, OM, CM, Matrix.sub_apply]

lemma unit_vec_D : vecNorm (fun _ : Fin D => zz) = 1 := by
  rw [vecNorm, sum_const_D, show (10 : ℝ) ^ 12 * zz ^ 2 = 1 from by rw [zz]; norm_num]
  exact Real.sqrt_one

lemma sphere_D_nonempty : Nonempty {v : Fin D → ℝ // vecNorm v = 1} :=
  ⟨⟨fun _ => zz, unit_vec_D⟩⟩

lemma vecNorm_ones : vecNorm (fun _ : Fin D => (1 : ℝ)) = 10 ^ 6 := by
  rw [vecNorm, sum_const_D,
    show (10 : ℝ) ^ 12 * (1 : ℝ) ^ 2 = (10 ^ 6) ^ 2 from by ring]
  exact Real.sqrt_sq (by norm_num)

lemma mulVec_CM (v : Fin D → ℝ) : CM *ᵥ v = fun _ => (1 - pp) * ∑ j, v j := by
  funext i
  simp [Matrix.mulVec, dotProduct, CM, Finset.mul_sum]

lemma one_sub_pp : (1 : ℝ) - pp = 5 / 10 ^ 5 := by rw [pp]; ring

lemma vecNorm_mulVec_CM (v : Fin D → ℝ) :
    vecNorm (CM *ᵥ v) = 10 ^ 6 * (1 - pp) * |∑ j, v j| := by
  have hq : (0 : ℝ) ≤ 1 - pp := by rw [one_sub_pp]; norm_num
  have key : (10 : ℝ) ^ 12 * ((1 - pp) * ∑ j, v j) ^ 2
      = (10 ^ 6 * (1 - pp) * |∑ j, v j|) ^ 2 := by
    have habs : |∑ j, v j| ^ 2 = (∑ j, v j) ^ 2 := sq_abs _
    calc (10 : ℝ) ^ 12 * ((1 - pp) * ∑ j, v j) ^ 2
        = (10 ^ 6 * (1 - pp)) ^ 2 * (∑ j, v j) ^ 2 := by ring
      _ = (10 ^ 6 * (1 - pp)) ^ 2 * |∑ j, v j| ^ 2 := by rw [habs]
      _ = (10 ^ 6 * (1 - pp) * |∑ j, v j|) ^ 2 := by ring
  rw [mulVec_CM, vecNorm, sum_const_D, key]
  exact Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) hq) (abs_nonneg _))

lemma sigmaMax_CM : sigmaMax CM = 5 * 10 ^ 7 := by
  haveI := sphere_D_nonempty
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun v => ?_
    have hcs : |∑ j, v.1 j| ≤ 10 ^ 6 := by
      have h := abs_sum_mul_le (fun _ : Fin D => (1 : ℝ)) v.1
      simp only [one_mul] at h
      rw [vecNorm_ones, v.2, mul_one] at h
      exact h
    rw [vecNorm_mulVec_CM, one_sub_pp]
    nlinarith [abs_nonneg (∑ j, v.1 j)]
  · have h := le_ciSup (bddAbove_sigma CM)
      (⟨fun _ : Fin D => zz, unit_vec_D⟩ : {v : Fin D → ℝ // vecNorm v = 1})
    rw [vecNorm_mulVec_CM, sum_const_D,
      show |(10 : ℝ) ^ 12 * zz| = 10 ^ 6 from by rw [zz]; norm_num,
      one_sub_pp] at h
    calc (5 : ℝ) * 10 ^ 7 = 10 ^ 6 * (5 / 10 ^ 5) * 10 ^ 6 := by norm_num
      _ ≤ sigmaMax CM := h

lemma sampDevNorm_val : sampDevNorm OM pp = 5 * 10 ^ 7 := by
  rw [sampDevNorm, centered_eq, sigmaMax_CM]

lemma filter_card_le (i : Fin D) : ((OM.filter fun e => e.1 = i)).card ≤ D := by
  classical
  have h : (OM.filter fun e : Fin D × Fin D => e.1 = i).card
      ≤ (Finset.univ : Finset (Fin D)).card := by
    refine Finset.card_le_card_of_injOn (fun e => e.2) (fun _ _ => Finset.mem_univ _) ?_
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
    exact Prod.ext_iff.mpr ⟨ha.2.trans hb.2.symm, hab⟩
  simpa using h

/-! ### Splitting a sum over `Fin D` at the outlying row -/

lemma sum_split_D (f : Fin D → ℝ) (c : ℝ) (hf : ∀ i, i ≠ i0 → f i = c) :
    ∑ i, f i = f i0 + (10 ^ 12 - 1) * c := by
  classical
  have h1 : ∑ i ∈ (Finset.univ : Finset (Fin D)).erase i0, f i = (10 ^ 12 - 1) * c := by
    rw [Finset.sum_congr rfl (fun i hi => hf i (Finset.ne_of_mem_erase hi)),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i0),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by norm_num : 1 ≤ 10 ^ 12)]
    push_cast
    ring
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ i0), h1]

lemma sum_ite_D (a c : ℝ) : (∑ j : Fin D, if j = i0 then a else c)
    = a + (10 ^ 12 - 1) * c := by
  rw [sum_split_D (fun j => if j = i0 then a else c) c (fun j hj => by simp [hj])]
  simp

/-! ### Matrix entries -/

lemma XM_apply (i : Fin D) (j : Fin 1) : XM i j = if i = i0 then x0 else zz := rfl
lemma ZM_apply (i : Fin D) (j : Fin 1) : ZM i j = zz := rfl

lemma mulT_apply (A B : Matrix (Fin D) (Fin 1) ℝ) (i j : Fin D) :
    (A * Bᵀ) i j = A i 0 * B j 0 := by
  simp [Matrix.mul_apply]

lemma W_apply (i j : Fin D) :
    (XM * XMᵀ - ZM * ZMᵀ) i j
      = (if i = i0 then x0 else zz) * (if j = i0 then x0 else zz) - zz * zz := by
  rw [Matrix.sub_apply, mulT_apply, mulT_apply, ZM_apply, ZM_apply, XM_apply, XM_apply]

lemma UDt_apply (i j : Fin D) : (ZM * (XM - ZM)ᵀ) i j = zz * (if j = i0 then dl else 0) := by
  rw [mulT_apply, ZM_apply, subM_apply]

lemma innerM_self {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : innerM A A = frobSq A := by
  rw [innerM, frobSq]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (sq (A i j)).symm

lemma frobSq_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### The Frobenius quantities -/

/-- One row's contribution to `‖XXᵀ − ZZᵀ‖_F²`, as a function of that row's entry. -/
noncomputable def gW (u : ℝ) : ℝ :=
  (u * x0 - zz * zz) ^ 2 + (10 ^ 12 - 1) * (u * zz - zz * zz) ^ 2

lemma inner_W (u : ℝ) :
    (∑ j : Fin D, (u * (if j = i0 then x0 else zz) - zz * zz) ^ 2) = gW u := by
  rw [Finset.sum_congr rfl (fun j _ =>
    (by by_cases hj : j = i0 <;> simp [hj] :
      (u * (if j = i0 then x0 else zz) - zz * zz) ^ 2
        = if j = i0 then (u * x0 - zz * zz) ^ 2 else (u * zz - zz * zz) ^ 2)), sum_ite_D, gW]

lemma frobSq_W_le : frobSq (XM * XMᵀ - ZM * ZMᵀ) ≤ 9 / 10 ^ 7 := by
  classical
  have h : frobSq (XM * XMᵀ - ZM * ZMᵀ) = gW x0 + (10 ^ 12 - 1) * gW zz := by
    rw [frobSq]
    simp only [W_apply]
    rw [Finset.sum_congr rfl (fun i _ => inner_W (if i = i0 then x0 else zz)),
      Finset.sum_congr rfl (fun i _ =>
        (by by_cases hi : i = i0 <;> simp [hi] :
          gW (if i = i0 then x0 else zz) = if i = i0 then gW x0 else gW zz)),
      sum_ite_D]
  rw [h]
  simp only [gW, zz, x0]
  norm_num

lemma DtD_entry : ((XM - ZM)ᵀ * (XM - ZM)) 0 0 = dl ^ 2 := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun i _ =>
    (by rw [Matrix.transpose_apply, subM_apply]
        by_cases hi : i = i0 <;> simp [hi] :
      (XM - ZM)ᵀ 0 i * (XM - ZM) i 0 = if i = i0 then dl * dl else 0)), sum_ite_D]
  ring

lemma frobSq_DtD_le : frobSq ((XM - ZM)ᵀ * (XM - ZM)) ≤ 2 / 10 ^ 13 := by
  rw [frobSq, Fin.sum_univ_one, Fin.sum_univ_one, DtD_entry, dl]
  norm_num

lemma frobSq_UDt_le : frobSq (ZM * (XM - ZM)ᵀ) ≤ 41 / 10 ^ 8 := by
  classical
  have inner : (∑ j : Fin D, (zz * (if j = i0 then dl else 0)) ^ 2) = (zz * dl) ^ 2 := by
    rw [Finset.sum_congr rfl (fun j _ =>
      (by by_cases hj : j = i0 <;> simp [hj] :
        (zz * (if j = i0 then dl else 0)) ^ 2 = if j = i0 then (zz * dl) ^ 2 else 0)),
      sum_ite_D]
    ring
  rw [frobSq]
  simp only [UDt_apply]
  rw [Finset.sum_congr rfl (fun i _ => inner), sum_const_D, zz, dl]
  norm_num

/-! ### The regularizer's contribution -/

lemma max_zz_al : max (zz - al) 0 = 0 := max_eq_right (by norm_num [zz, al])
lemma max_x0_al : max (x0 - al) 0 = x0 - al := max_eq_left (by norm_num [x0, al])
lemma x0_ne : x0 ≠ 0 := ne_of_gt x0_pos

lemma inner_row_i0 : (∑ j : Fin 1, XM i0 j * (XM - ZM) i0 j) = x0 * dl := by
  rw [Fin.sum_univ_one, XM_apply, subM_apply]; simp

lemma vecNorm_sub_i0 : vecNorm ((XM - ZM) i0) = dl := rowNorm_sub_i0

lemma regHess_val : regHessQF al XM (XM - ZM) = 12 * (x0 - al) ^ 2 * dl ^ 2 := by
  classical
  have hdiv : x0 * dl / x0 = dl := mul_div_cancel_left₀ dl x0_ne
  rw [regHessQF, sum_split_D _ 0 (by
    intro i hi
    simp only [rowNorm_XM_ne hi, max_zz_al]
    norm_num)]
  simp only [rowNorm_XM_i0, inner_row_i0, vecNorm_sub_i0, max_x0_al, hdiv]
  ring

lemma regGrad_inner : innerM (regGrad al XM) (XM - ZM) = 4 * (x0 - al) ^ 3 * dl := by
  classical
  rw [innerM, sum_split_D _ 0 (by
    intro i hi
    simp only [Fin.sum_univ_one, regGrad, Matrix.of_apply, rowNorm_XM_ne hi, max_zz_al]
    norm_num)]
  have h1 : XM i0 0 = x0 := by rw [XM_apply]; simp
  have h2 : (XM - ZM) i0 0 = dl := by rw [subM_apply]; simp
  have hx0 : x0 ≠ 0 := x0_ne
  simp only [Fin.sum_univ_one, regGrad, Matrix.of_apply, rowNorm_XM_i0, max_x0_al, h1, h2]
  field_simp
  ring

lemma reg_term : regHessQF al XM (XM - ZM) - 4 * innerM (regGrad al XM) (XM - ZM)
    = 12 * (x0 - al) ^ 2 * dl ^ 2 - 16 * (x0 - al) ^ 3 * dl := by
  rw [regHess_val, regGrad_inner]; ring

/-! ### Every hypothesis of the milestone -/

lemma cast_D : ((D : ℕ) : ℝ) = 10 ^ 12 := by push_cast; ring

lemma sqrt_cast_D : Real.sqrt ((D : ℕ) : ℝ) = 10 ^ 6 := by
  rw [show ((D : ℕ) : ℝ) = ((10 : ℝ) ^ 6) ^ 2 from by rw [cast_D]; ring]
  exact Real.sqrt_sq (by norm_num)

lemma hcond : sigmaMax ZM ≤ 1 * sigmaMin ZM := by
  rw [sigmaMax_ZM, sigmaMin_ZM]; norm_num

lemma hsig : 0 < sigmaMin ZM := by rw [sigmaMin_ZM]; norm_num

lemma hinc : Incoherent 1 ZM := by
  intro i
  rw [rowNorm_ZM, frobNorm_ZM, sqrt_cast_D]
  norm_num [zz]

lemma hfrob : frobSq ZM = ((1 : ℕ) : ℝ) := by rw [frobSq_ZM]; norm_num

lemma hal1 : 100 * twoInftyNorm ZM ≤ al := by rw [twoInftyNorm_ZM]; norm_num [zz, al]
lemma hal2 : al ≤ 200 * twoInftyNorm ZM := by rw [twoInftyNorm_ZM]; norm_num [zz, al]

lemma hlam1 : 100 * sampDevNorm OM pp ≤ lm := by rw [sampDevNorm_val]; norm_num [lm]
lemma hlam2 : lm ≤ 200 * sampDevNorm OM pp := by rw [sampDevNorm_val]; norm_num [lm]

lemma log_D_le : Real.log ((D : ℕ) : ℝ) ≤ 40 := by
  rw [cast_D]
  have h1 : Real.log ((10 : ℝ) ^ 12) ≤ Real.log ((2 : ℝ) ^ 40) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log ((2 : ℝ) ^ 40) = 40 * Real.log 2 := by
    rw [Real.log_pow]; push_cast; ring
  have h3 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  linarith

lemma hsample : SampleCondition D 1 pp 1 1 := by
  constructor
  · have h := log_D_le
    have hlog0 : (0:ℝ) ≤ Real.log ((D : ℕ) : ℝ) := Real.log_nonneg (by rw [cast_D]; norm_num)
    rw [cast_D] at h hlog0 ⊢
    rw [pp]
    set L := Real.log ((10 : ℝ) ^ 12) with hL
    push_cast
    linarith
  · rw [pp]; norm_num

lemma good : GoodSample ZM OM pp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j; simp [OM]
  · intro i
    have h : ((OM.filter fun e => e.1 = i).card : ℝ) ≤ ((D : ℕ) : ℝ) := by
      exact_mod_cast filter_card_le i
    rw [cast_D] at h ⊢
    rw [pp]
    linarith
  · rw [sampDevNorm_val, cast_D]
    have h1 : (7 : ℝ) * 10 ^ 5 ≤ Real.sqrt ((10 : ℝ) ^ 12 * pp) := by
      rw [show (7 : ℝ) * 10 ^ 5 = Real.sqrt (((7 : ℝ) * 10 ^ 5) ^ 2) from
        (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by rw [pp]; norm_num)
    have h2 : (0 : ℝ) ≤ Real.sqrt (Real.log ((10 : ℝ) ^ 12)) := Real.sqrt_nonneg _
    linarith
  · intro W W' _ _ _ _
    rw [sampDev_univ, one_sub_pp, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5 / 10 ^ 5)]
    have hcs := abs_innerM_le W W'
    have hW : (0 : ℝ) ≤ frobNorm W := Real.sqrt_nonneg _
    have hW' : (0 : ℝ) ≤ frobNorm W' := Real.sqrt_nonneg _
    have hprod : (0 : ℝ) ≤ frobNorm W * frobNorm W' := mul_nonneg hW hW'
    rw [pp]
    nlinarith [hcs, hprod]

lemma XtU_entry : (XMᵀ * ZM) 0 0 = x0 * zz + (10 ^ 12 - 1) * (zz * zz) := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun i _ =>
    (by rw [Matrix.transpose_apply, XM_apply, ZM_apply]
        by_cases hi : i = i0 <;> simp [hi] :
      XMᵀ 0 i * ZM i 0 = if i = i0 then x0 * zz else zz * zz)), sum_ite_D]

lemma hpsd : Matrix.PosSemidef (XMᵀ * ZM) := by
  have hent : (0 : ℝ) ≤ (XMᵀ * ZM) 0 0 := by rw [XtU_entry, x0, zz]; norm_num
  refine ⟨?_, ?_⟩
  · ext i j
    rw [Matrix.conjTranspose_apply, star_trivial, Subsingleton.elim i j]
  · intro v
    rw [Finsupp.sum]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Finsupp.sum]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1), star_trivial]
    nlinarith [hent, sq_nonneg (v 0)]


/-! ### Extra machinery for `K_superlevel_bound` -/

lemma innerM_add_left {m n : ℕ} (A B C : Matrix (Fin m) (Fin n) ℝ) :
    innerM (A + B) C = innerM A C + innerM B C := by
  rw [innerM, innerM, innerM, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.add_apply]; ring

lemma innerM_smul_left {m n : ℕ} (c : ℝ) (A B : Matrix (Fin m) (Fin n) ℝ) :
    innerM (c • A) B = c * innerM A B := by
  rw [innerM, innerM, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply]; simp [mul_assoc]

lemma DD_apply (i j : Fin D) : ((XM - ZM) * (XM - ZM)ᵀ) i j
    = (if i = i0 then dl else 0) * (if j = i0 then dl else 0) := by
  rw [mulT_apply, subM_apply, subM_apply]

/-! Entry values at and away from the outlying row, stated without `if`s. -/

lemma XM_i0_apply (j : Fin 1) : XM i0 j = x0 := by rw [XM_apply, if_pos rfl]
lemma sub_i0_apply (j : Fin 1) : (XM - ZM) i0 j = dl := by rw [subM_apply, if_pos rfl]
lemma sub_ne_apply {i : Fin D} (hi : i ≠ i0) (j : Fin 1) : (XM - ZM) i j = 0 := by
  rw [subM_apply, if_neg hi]
lemma W_i0_i0 : (XM * XMᵀ - ZM * ZMᵀ) i0 i0 = x0 * x0 - zz * zz := by
  rw [W_apply, if_pos rfl]
lemma W_i0_ne {k : Fin D} (hk : k ≠ i0) :
    (XM * XMᵀ - ZM * ZMᵀ) i0 k = x0 * zz - zz * zz := by
  rw [W_apply, if_pos rfl, if_neg hk]
lemma negW_i0_i0 : (ZM * ZMᵀ - XM * XMᵀ) i0 i0 = zz * zz - x0 * x0 := by
  rw [Matrix.sub_apply, mulT_apply, mulT_apply, ZM_apply, XM_i0_apply]
lemma DD_i0_i0 : ((XM - ZM) * (XM - ZM)ᵀ) i0 i0 = dl * dl := by
  rw [DD_apply, if_pos rfl]
lemma DD_i0_ne {j : Fin D} (hj : j ≠ i0) : ((XM - ZM) * (XM - ZM)ᵀ) i0 j = 0 := by
  rw [DD_apply, if_neg hj]; ring
lemma DD_ne_left {i : Fin D} (hi : i ≠ i0) (j : Fin D) :
    ((XM - ZM) * (XM - ZM)ᵀ) i j = 0 := by
  rw [DD_apply, if_neg hi]; ring

/-- Pairing anything against `ΔΔᵀ` only sees the outlying entry. -/
lemma innerM_DD (A : Matrix (Fin D) (Fin D) ℝ) :
    innerM A ((XM - ZM) * (XM - ZM)ᵀ) = A i0 i0 * dl ^ 2 := by
  classical
  have hne : ∀ i : Fin D, i ≠ i0 →
      (∑ j, A i j * ((XM - ZM) * (XM - ZM)ᵀ) i j) = 0 := fun i hi =>
    Finset.sum_eq_zero fun j _ => by rw [DD_ne_left hi]; ring
  have hne' : ∀ j : Fin D, j ≠ i0 → A i0 j * ((XM - ZM) * (XM - ZM)ᵀ) i0 j = 0 := by
    intro j hj; rw [DD_i0_ne hj]; ring
  have hi0 : (∑ j, A i0 j * ((XM - ZM) * (XM - ZM)ᵀ) i0 j) = A i0 i0 * dl ^ 2 := by
    rw [sum_split_D (fun j => A i0 j * ((XM - ZM) * (XM - ZM)ᵀ) i0 j) 0 hne']
    show A i0 i0 * ((XM - ZM) * (XM - ZM)ᵀ) i0 i0 + (10 ^ 12 - 1) * 0 = A i0 i0 * dl ^ 2
    rw [DD_i0_i0]; ring
  rw [innerM, sum_split_D _ 0 hne]
  show (∑ j, A i0 j * ((XM - ZM) * (XM - ZM)ᵀ) i0 j) + (10 ^ 12 - 1) * 0 = A i0 i0 * dl ^ 2
  rw [hi0]; ring

lemma innerM_curv_le : innerM (ZM * ZMᵀ - XM * XMᵀ) ((XM - ZM) * (XM - ZM)ᵀ) ≤ 0 := by
  rw [innerM_DD, negW_i0_i0]
  have h1 : zz * zz - x0 * x0 ≤ 0 := by rw [zz, x0]; norm_num
  nlinarith [sq_nonneg dl]

/-- The `∇f`-side pairing, bounded above. -/
lemma innerM_grad_le :
    innerM ((XM * XMᵀ - ZM * ZMᵀ) * XM) (XM - ZM) ≤ 41 / 10 ^ 8 := by
  classical
  have hk : ∀ k : Fin D, k ≠ i0 →
      (XM * XMᵀ - ZM * ZMᵀ) i0 k * XM k 0 = (x0 * zz - zz * zz) * zz := by
    intro k hk; rw [W_i0_ne hk, XM_apply, if_neg hk]
  have hrow : ((XM * XMᵀ - ZM * ZMᵀ) * XM) i0 0
      = (x0 * x0 - zz * zz) * x0 + (10 ^ 12 - 1) * ((x0 * zz - zz * zz) * zz) := by
    rw [Matrix.mul_apply,
      sum_split_D (fun k => (XM * XMᵀ - ZM * ZMᵀ) i0 k * XM k 0)
        ((x0 * zz - zz * zz) * zz) hk]
    show (XM * XMᵀ - ZM * ZMᵀ) i0 i0 * XM i0 0
        + (10 ^ 12 - 1) * ((x0 * zz - zz * zz) * zz) = _
    rw [W_i0_i0, XM_i0_apply]
  have hrne : ∀ i : Fin D, i ≠ i0 →
      (∑ j, ((XM * XMᵀ - ZM * ZMᵀ) * XM) i j * (XM - ZM) i j) = 0 := fun i hi =>
    Finset.sum_eq_zero fun j _ => by rw [sub_ne_apply hi]; ring
  have hval : innerM ((XM * XMᵀ - ZM * ZMᵀ) * XM) (XM - ZM)
      = ((XM * XMᵀ - ZM * ZMᵀ) * XM) i0 0 * dl := by
    rw [innerM, sum_split_D _ 0 hrne]
    show (∑ j, ((XM * XMᵀ - ZM * ZMᵀ) * XM) i0 j * (XM - ZM) i0 j) + (10 ^ 12 - 1) * 0 = _
    rw [Fin.sum_univ_one, sub_i0_apply]; ring
  rw [hval, hrow, x0, zz, dl]
  norm_num

/-! ### The right-hand side of `K_superlevel_bound` -/

lemma frobSq_DtU : frobSq ((XM - ZM)ᵀ * ZM) = (dl * zz) ^ 2 := by
  classical
  have hne : ∀ i : Fin D, i ≠ i0 → (XM - ZM)ᵀ 0 i * ZM i 0 = 0 := by
    intro i hi; rw [Matrix.transpose_apply, sub_ne_apply hi]; ring
  have ent : ((XM - ZM)ᵀ * ZM) 0 0 = dl * zz := by
    rw [Matrix.mul_apply, sum_split_D (fun i => (XM - ZM)ᵀ 0 i * ZM i 0) 0 hne]
    show (XM - ZM)ᵀ 0 i0 * ZM i0 0 + (10 ^ 12 - 1) * 0 = dl * zz
    rw [Matrix.transpose_apply, sub_i0_apply, ZM_apply]; ring
  rw [frobSq, Fin.sum_univ_one, Fin.sum_univ_one, ent]

lemma frobNorm_DtD_le : frobNorm ((XM - ZM)ᵀ * (XM - ZM)) ≤ 5 / 10 ^ 7 := by
  rw [frobNorm]
  calc Real.sqrt (frobSq ((XM - ZM)ᵀ * (XM - ZM)))
      ≤ Real.sqrt (2 / 10 ^ 13) := Real.sqrt_le_sqrt frobSq_DtD_le
    _ ≤ 5 / 10 ^ 7 := by
        rw [show (5 : ℝ) / 10 ^ 7 = Real.sqrt (((5 : ℝ) / 10 ^ 7) ^ 2) from
          (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num)

lemma frobNorm_DtU_le : frobNorm ((XM - ZM)ᵀ * ZM) ≤ 7 / 10 ^ 10 := by
  rw [frobNorm, frobSq_DtU,
    show (7 : ℝ) / 10 ^ 10 = Real.sqrt (((7 : ℝ) / 10 ^ 10) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [dl, zz]; norm_num

lemma frobNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ frobNorm A :=
  Real.sqrt_nonneg _

end MS6CE

open MS6CE in
/-- **`K_superlevel_bound` is false.**  The same configuration that disproves
`perturbation_terms_bound` disproves this one too, by a factor of about `10⁹`. -/
theorem solution : ¬ (∀ {d r : ℕ}, 2 ≤ d → 1 ≤ r →
    ∀ (Z X U : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
      (p μ κ lam α : ℝ),
      1 ≤ μ → 1 ≤ κ → sigmaMax Z ≤ κ * sigmaMin Z → 0 < sigmaMin Z →
      Incoherent μ Z → frobSq Z = (r : ℝ) →
      100 * twoInftyNorm Z ≤ α → α ≤ 200 * twoInftyNorm Z →
      100 * sampDevNorm Ω p ≤ lam → lam ≤ 200 * sampDevNorm Ω p →
      SampleCondition d r p μ κ → GoodSample Z Ω p →
      U * Uᵀ = Z * Zᵀ → (Xᵀ * U).PosSemidef →
      Kfun Z Ω lam α X U ≤
        p * (-(1999 / 1000) * frobSq ((X - U)ᵀ * (X - U))
          + (6001 / 1000) * frobNorm ((X - U)ᵀ * (X - U)) * frobNorm ((X - U)ᵀ * U)
          - 6 * frobSq ((X - U)ᵀ * U))) := by
  intro h
  have H := @h D 1 (by norm_num) le_rfl ZM XM ZM OM pp 1 1 lm al
    le_rfl le_rfl hcond hsig hinc hfrob hal1 hal2 hlam1 hlam2 hsample good rfl hpsd
  rw [Kfun, hessQF, objGrad, projSet_univ, projSet_univ, projSet_univ,
    innerM_add_left, innerM_smul_left, innerM_smul_left, regGrad_inner, regHess_val] at H
  have hF : (0 : ℝ) ≤ frobSq ((XM - ZM) * XMᵀ + XM * (XM - ZM)ᵀ) := frobSq_nonneg _
  have hI := innerM_curv_le
  have hG := innerM_grad_le
  have hReg : (38 : ℝ) / 10 ^ 5
      ≤ lm * (12 * (x0 - al) ^ 2 * dl ^ 2) - 4 * (lm * (4 * (x0 - al) ^ 3 * dl)) := by
    rw [lm, x0, al, dl]; norm_num
  have hR : pp * (-(1999 / 1000) * frobSq ((XM - ZM)ᵀ * (XM - ZM))
      + (6001 / 1000) * frobNorm ((XM - ZM)ᵀ * (XM - ZM)) * frobNorm ((XM - ZM)ᵀ * ZM)
      - 6 * frobSq ((XM - ZM)ᵀ * ZM)) ≤ 1 / 10 ^ 6 := by
    have hA : (0 : ℝ) ≤ frobSq ((XM - ZM)ᵀ * (XM - ZM)) := frobSq_nonneg _
    have hE : (0 : ℝ) ≤ frobSq ((XM - ZM)ᵀ * ZM) := frobSq_nonneg _
    have hC0 : (0 : ℝ) ≤ frobNorm ((XM - ZM)ᵀ * ZM) := frobNorm_nonneg _
    have hprod : frobNorm ((XM - ZM)ᵀ * (XM - ZM)) * frobNorm ((XM - ZM)ᵀ * ZM)
        ≤ (5 / 10 ^ 7) * (7 / 10 ^ 10) :=
      mul_le_mul frobNorm_DtD_le frobNorm_DtU_le hC0 (by norm_num)
    have hp0 : (0 : ℝ) < pp := by rw [pp]; norm_num
    have hp1 : pp ≤ 1 := by rw [pp]; norm_num
    nlinarith [hA, hE, hprod, hp0, hp1]
  linarith
