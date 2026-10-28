-- Prove2me | solution 1 for OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:28:54.997065+00:00
-- url     : https://prove2.me/submissions/6c6090ca-9ebc-44e6-9ccd-7c699494959e

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section
-- module Solutions.OAIQ3_Hot.HotSpots_Reciprocal
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section SingularLayer



namespace ReciprocalKernel

open Matrix Filter Topology
open scoped BigOperators

variable {ι : Type*} [Fintype ι]


lemma pairing_symm {A : Matrix ι ι ℝ} (hA : A.IsSymm) (x y : ι → ℝ) :
    pairing A x y = pairing A y x := by
  simpa only [pairing, hA.eq] using Matrix.dotProduct_transpose_mulVec A x y

lemma pairing_sub_smul (A : Matrix ι ι ℝ) (x y : ι → ℝ) (t : ℝ) :
    pairing A (y - t • x) (y - t • x) =
      pairing A y y - t * pairing A y x - t * pairing A x y + t ^ 2 * pairing A x x := by
  simp only [pairing, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma pairing_sub_smul_right (A : Matrix ι ι ℝ) (x y z : ι → ℝ) (t : ℝ) :
    pairing A x (y - t • z) = pairing A x y - t * pairing A x z := by
  simp only [pairing, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]

lemma pairing_tendsto {A : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) (x y : ι → ℝ) :
    Tendsto (fun n => pairing (A n) x y) atTop (𝓝 (pairing B x y)) := by
  unfold pairing dotProduct Matrix.mulVec
  exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
    (tendsto_finsetSum _ fun j _ => (hlim i j).mul tendsto_const_nhds))



lemma onePositiveSquare_reverse_cauchy {A : Matrix ι ι ℝ} (hA : OnePositiveSquare A)
    (x y : ι → ℝ) (hx : 0 < pairing A x x) :
    pairing A x x * pairing A y y ≤ (pairing A x y) ^ 2 := by
  have hz : pairing A x (y - (pairing A x y / pairing A x x) • x) = 0 := by
    rw [pairing_sub_smul_right]
    field_simp
    ring
  have hn := hA.2 x _ hx hz
  rw [pairing_sub_smul, pairing_symm hA.1 y x] at hn
  have he : pairing A y y - (pairing A x y / pairing A x x) * pairing A x y -
      (pairing A x y / pairing A x x) * pairing A x y +
      (pairing A x y / pairing A x x) ^ 2 * pairing A x x =
      pairing A y y - (pairing A x y) ^ 2 / pairing A x x := by
    field_simp
    ring
  rw [he] at hn
  have := (le_div_iff₀ hx).mp (sub_nonpos.mp hn)
  nlinarith

lemma onePositiveSquare_of_entrywise_tendsto {A : ℕ → Matrix ι ι ℝ}
    {B : Matrix ι ι ℝ} (hA : ∀ n, OnePositiveSquare (A n))
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) :
    OnePositiveSquare B := by
  refine ⟨?_, ?_⟩
  · ext i j
    exact tendsto_nhds_unique (hlim j i)
      ((hlim i j).congr fun n => (hA n).1.apply i j |>.symm)
  · intro x y hx hxy
    have hxx := pairing_tendsto hlim x x
    have hyy := pairing_tendsto hlim y y
    have hxy' := pairing_tendsto hlim x y
    have hp : ∀ᶠ n in atTop, 0 < pairing (A n) x x :=
      hxx.eventually_const_lt hx
    have hn : pairing B x x * pairing B y y - (pairing B x y) ^ 2 ≤ 0 := by
      apply le_of_tendsto ((hxx.mul hyy).sub (hxy'.pow 2))
      filter_upwards [hp] with n hn
      exact sub_nonpos.mpr (onePositiveSquare_reverse_cauchy (hA n) x y hn)
    rw [hxy] at hn
    nlinarith



lemma onePositiveSquare_of_nonpos_on_kernel {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) (l : ι → ℝ)
    (h : ∀ x : ι → ℝ, l ⬝ᵥ x = 0 → pairing A x x ≤ 0) :
    OnePositiveSquare A := by
  refine ⟨hA, ?_⟩
  intro x y hx hxy
  have hlx : l ⬝ᵥ x ≠ 0 := by
    intro he
    exact (not_le_of_gt hx) (h x he)
  have hyx : pairing A y x = 0 := (pairing_symm hA y x).trans hxy
  have hz : l ⬝ᵥ (y - ((l ⬝ᵥ y) / (l ⬝ᵥ x)) • x) = 0 := by
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp
    ring
  have hh := h _ hz
  rw [pairing_sub_smul, hxy, hyx] at hh
  nlinarith [sq_nonneg ((l ⬝ᵥ y) / (l ⬝ᵥ x))]

lemma onePositiveSquare_rankOne_sub_psd (l : ι → ℝ) {U : Matrix ι ι ℝ}
    (hU : U.PosSemidef) :
    OnePositiveSquare (Matrix.vecMulVec l l - U) := by
  apply onePositiveSquare_of_nonpos_on_kernel (l := l)
  · apply Matrix.isHermitian_iff_isSymm.mp
    exact (Matrix.posSemidef_vecMulVec_self_star l |>.isHermitian).sub hU.isHermitian
  · intro x hx
    have hnon := hU.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hnon
    simp [pairing, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, hx, hnon]

lemma pairing_const (a : ℝ) (x y : ι → ℝ) :
    pairing (Matrix.of (fun _ _ => a)) x y = a * (∑ i, x i) * (∑ j, y j) := by
  simp only [pairing, Matrix.mulVec, dotProduct, Matrix.of_apply]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma pairing_scale (A : Matrix ι ι ℝ) (l x y : ι → ℝ) :
    pairing (Matrix.of (fun i j => l i * A i j * l j)) x y =
      pairing A (l * x) (l * y) := by
  simp only [pairing, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.mul_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma onePositiveSquare_scale {A : Matrix ι ι ℝ} (hA : OnePositiveSquare A)
    (l : ι → ℝ) :
    OnePositiveSquare (Matrix.of (fun i j => l i * A i j * l j)) := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [hA.1.apply]
    ring
  · intro x y hx hxy
    rw [pairing_scale] at hx hxy ⊢
    exact hA.2 _ _ hx hxy

lemma onePositiveSquare_const_sub_psd (a : ℝ) {U : Matrix ι ι ℝ}
    (hU : U.PosSemidef) :
    OnePositiveSquare (Matrix.of (fun _ _ => a) - U) := by
  apply onePositiveSquare_of_nonpos_on_kernel (l := fun _ => 1)
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.of_apply]
    have hij : U j i = U i j := by simpa using hU.isHermitian.apply i j
    rw [hij]
  · intro x hx
    have hsum : ∑ i, x i = 0 := by simpa [dotProduct] using hx
    have hn := hU.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hn
    change pairing (Matrix.of (fun _ _ => a) - U) x x ≤ 0
    change x ⬝ᵥ (Matrix.of (fun _ _ => a) - U) *ᵥ x ≤ 0
    rw [Matrix.sub_mulVec, dotProduct_sub]
    change pairing (Matrix.of (fun _ _ => a)) x x - pairing U x x ≤ 0
    rw [pairing_const, hsum]
    simpa only [pairing, mul_zero, zero_sub, neg_nonpos] using hn



lemma normalized_complement_posSemidef {H : Matrix ι ι ℝ}
    (hH : OnePositiveSquare H) (z : ι) {a : ℝ} (ha : 0 < a)
    (hrow : ∀ j, H z j = a) :
    (Matrix.of (fun _ _ => a) - H).PosSemidef := by
  classical
  have hpair (v : ι → ℝ) : pairing H (Pi.single z 1) v = a * ∑ i, v i := by
    unfold pairing
    rw [single_dotProduct, one_mul]
    change (∑ j, H z j * v j) = a * ∑ i, v i
    simp only [hrow, Finset.mul_sum]
  have he : pairing H (Pi.single z 1) (Pi.single z 1) = a := by
    simp [hpair]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.ext
    intro i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.of_apply]
    rw [hH.1.apply]
  · intro v
    have hz : pairing H (Pi.single z 1) (v - (∑ i, v i) • Pi.single z 1) = 0 := by
      rw [hpair]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      simp
    have hyn := hH.2 (Pi.single z 1) _ (he ▸ ha) hz
    rw [pairing_sub_smul, he, hpair, pairing_symm hH.1 v (Pi.single z 1), hpair] at hyn
    have heval : star v ⬝ᵥ (Matrix.of (fun _ _ => a) - H) *ᵥ v =
        a * (∑ i, v i) ^ 2 - pairing H v v := by
      simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
      change pairing (Matrix.of (fun _ _ => a)) v v - pairing H v v = _
      rw [pairing_const]
      ring
    rw [heval]
    nlinarith

omit [Fintype ι] in

lemma posSemidef_entry_sq_le {U : Matrix ι ι ℝ} (hU : U.PosSemidef) (i j : ι) :
    (U i j) ^ 2 ≤ U i i * U j j := by
  have h := (hU.submatrix ![i, j]).det_nonneg
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  have hij : U j i = U i j := by simpa using hU.isHermitian.apply i j
  rw [hij] at h
  nlinarith

omit [Fintype ι] in
lemma posSemidef_abs_entry_lt {U : Matrix ι ι ℝ} (hU : U.PosSemidef)
    {a : ℝ} (ha : 0 < a) (hdiag : ∀ i, U i i < a) (i j : ι) : |U i j| < a := by
  have hp : U i i * U j j < a * a := calc
    U i i * U j j ≤ U i i * a :=
      mul_le_mul_of_nonneg_left (hdiag j).le hU.diag_nonneg
    _ < a * a := mul_lt_mul_of_pos_right (hdiag i) ha
  have hs := posSemidef_entry_sq_le hU i j
  nlinarith [sq_abs (U i j), abs_nonneg (U i j)]


lemma posSemidef_entry_pow {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (n : ℕ) :
    (Matrix.of (fun i j => A i j ^ n)).PosSemidef := by
  induction n with
  | zero =>
    simpa [Matrix.vecMulVec] using
      (Matrix.posSemidef_vecMulVec_self_star (fun _ : ι => (1 : ℝ)))
  | succ n ih =>
    have he : Matrix.of (fun i j => A i j ^ (n + 1)) =
        Matrix.of (fun i j => A i j ^ n) ⊙ A := by
      ext i j
      simp [pow_succ]
    rw [he]
    exact ih.hadamard hA


lemma posSemidef_of_entrywise_tendsto {A : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (hA : ∀ n, (A n).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact tendsto_nhds_unique (hlim j i)
      ((hlim i j).congr fun n => by simpa using (hA n).isHermitian.apply j i)
  · intro x
    have hlimq : Tendsto (fun n => star x ⬝ᵥ A n *ᵥ x) atTop
        (𝓝 (star x ⬝ᵥ B *ᵥ x)) := by
      unfold dotProduct Matrix.mulVec
      exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hlim i j).mul tendsto_const_nhds))
    exact ge_of_tendsto hlimq (Filter.Eventually.of_forall fun n =>
      (hA n).dotProduct_mulVec_nonneg x)


lemma posSemidef_entry_resolvent {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hsmall : ∀ i j, |A i j| < 1) :
    (Matrix.of (fun i j => A i j / (1 - A i j))).PosSemidef := by
  apply posSemidef_of_entrywise_tendsto
    (A := fun n => ∑ k ∈ Finset.range n, Matrix.of (fun i j => A i j ^ (k + 1)))
  · intro n
    exact Matrix.posSemidef_sum _ (fun k _ => posSemidef_entry_pow hA (k + 1))
  · intro i j
    have hs := (hasSum_geometric_of_norm_lt_one (show ‖A i j‖ < 1 by
      simpa only [Real.norm_eq_abs] using hsmall i j)).mul_left (A i j)
    simpa only [Matrix.sum_apply, Matrix.of_apply, div_eq_mul_inv, pow_succ, mul_comm]
      using hs.tendsto_sum_nat


lemma onePositiveSquare_normalized_update {H : Matrix ι ι ℝ}
    (hH : OnePositiveSquare H) (hpos : ∀ i j, 0 < H i j)
    (z : ι) {a : ℝ} (hrow : ∀ j, H z j = a) {c : ℝ} (hc : 0 ≤ c) :
    OnePositiveSquare (Matrix.of (fun i j => H i j / (1 + c * H i j))) := by
  rcases hc.eq_or_lt with hc | hc
  · subst c
    have he : Matrix.of (fun i j => H i j / (1 + 0 * H i j)) = H := by
      ext i j
      simp
    rwa [he]
  have ha : 0 < a := hrow z ▸ hpos z z
  let U := Matrix.of (fun _ _ => a) - H
  have hU : U.PosSemidef := normalized_complement_posSemidef hH z ha hrow
  have hdiag : ∀ i, U i i < a := by
    intro i
    change a - H i i < a
    exact sub_lt_self _ (hpos i i)
  have hUa : ∀ i j, |U i j| < a := posSemidef_abs_entry_lt hU ha hdiag
  have hd : 0 < 1 + c * a := by positivity
  let r := c / (1 + c * a)
  have hr : 0 < r := div_pos hc hd
  let V := r • U
  have hV : V.PosSemidef := hU.smul hr.le
  have hra : r * a < 1 := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    linarith
  have hsmall : ∀ i j, |V i j| < 1 := by
    intro i j
    change |r * U i j| < 1
    rw [abs_mul, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left (hUa i j) hr).trans hra
  have hW := (posSemidef_entry_resolvent hV hsmall).smul
    (show 0 ≤ (1 / (c * (1 + c * a)) : ℝ) by positivity)
  have hP := onePositiveSquare_const_sub_psd (a / (1 + c * a)) hW
  have he : Matrix.of (fun i j => H i j / (1 + c * H i j)) =
      Matrix.of (fun _ _ => a / (1 + c * a)) -
        (1 / (c * (1 + c * a))) • Matrix.of (fun i j => V i j / (1 - V i j)) := by
    ext i j
    have hij := hpos i j
    have hden : 0 < 1 + c * H i j := by positivity
    have hone : 1 - V i j ≠ 0 := ne_of_gt (sub_pos.mpr (abs_lt.mp (hsmall i j)).2)
    simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    dsimp [V, U, r] at hone ⊢
    field_simp [ne_of_gt hden, ne_of_gt hd, ne_of_gt hc]
    ring_nf
    field_simp [show 1 + H i j * c ≠ 0 by nlinarith [hden]]
    ring
  rw [he]
  exact hP



theorem reciprocal_rankOne_update {M : Matrix ι ι ℝ} (hM : M.IsSymm)
    (hpos : ∀ i j, 0 < M i j)
    (hrec : OnePositiveSquare (Matrix.of (fun i j => (M i j)⁻¹)))
    (z : ι) {c : ℝ} (hc : 0 ≤ c) :
    OnePositiveSquare (Matrix.of (fun i j => (M i j + c * M i z * M z j)⁻¹)) := by
  let H := Matrix.of (fun i j => M i z * (M i j)⁻¹ * M j z)
  have hH : OnePositiveSquare H := onePositiveSquare_scale hrec (fun i => M i z)
  have hHp : ∀ i j, 0 < H i j := by
    intro i j
    change 0 < M i z * (M i j)⁻¹ * M j z
    exact mul_pos (mul_pos (hpos i z) (inv_pos.mpr (hpos i j))) (hpos j z)
  have hrow : ∀ j, H z j = M z z := by
    intro j
    change M z z * (M z j)⁻¹ * M j z = M z z
    rw [hM.apply j z]
    field_simp [ne_of_gt (hpos j z)]
  have hnew := onePositiveSquare_normalized_update hH hHp z hrow hc
  have hscaled := onePositiveSquare_scale hnew (fun i => (M i z)⁻¹)
  have he : Matrix.of (fun i j => (M i j + c * M i z * M z j)⁻¹) =
      Matrix.of (fun i j => (M i z)⁻¹ * (H i j / (1 + c * H i j)) * (M j z)⁻¹) := by
    ext i j
    have hij := hpos i j
    have hiz := hpos i z
    have hjz := hpos j z
    have hn : 0 < M i j + c * M i z * M j z := by positivity
    simp only [Matrix.of_apply]
    dsimp [H]
    rw [hM.apply z j]
    have hzj := hpos z j
    have hn' : 0 < M i j + c * M i z * M z j := by positivity
    field_simp [ne_of_gt hzj, ne_of_gt hn']
  rw [he]
  exact hscaled


end ReciprocalKernel

namespace ReciprocalKernel
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] [DecidableEq ι] in
lemma eliminate_denominator_pos {M : Matrix ι ι ℝ} {w f : ι → ℝ}
    (hM : ∀ i j, 0 < M i j) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 < f i)
    {S : Finset ι} {z : ι} (hz : z ∈ S)
    (hb : ∀ i, ∑ j ∈ S, M i j * w j * f j < f i) :
    0 < 1 - w z * M z z := by
  have hs : M z z * w z * f z ≤ ∑ j ∈ S, M z j * w j * f j :=
    Finset.single_le_sum (f := fun j => M z j * w j * f j)
      (fun i hi => mul_nonneg (mul_nonneg (hM z i).le (hw i)) (hf i).le) hz
  have hh := lt_of_le_of_lt hs (hb z)
  nlinarith [hf z]

omit [Fintype ι] [DecidableEq ι] in
lemma eliminate_symm {M : Matrix ι ι ℝ} (hM : M.IsSymm) (w : ι → ℝ) (z : ι) :
    (eliminate M w z).IsSymm := by
  ext i j
  simp only [eliminate, Matrix.transpose_apply, Matrix.of_apply]
  rw [hM.apply j i, hM.apply j z, hM.apply z i]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma eliminate_pos {M : Matrix ι ι ℝ} {w : ι → ℝ} {z : ι}
    (hM : ∀ i j, 0 < M i j) (hw : 0 ≤ w z) (hz : 0 < 1 - w z * M z z) :
    ∀ i j, 0 < eliminate M w z i j := by
  intro i j
  dsimp [eliminate]
  exact add_pos_of_pos_of_nonneg (hM i j)
    (mul_nonneg (mul_nonneg (div_nonneg hw hz.le) (hM i z).le) (hM z j).le)

omit [Fintype ι] in
lemma eliminate_bound {M : Matrix ι ι ℝ} {w f : ι → ℝ}
    (hM : ∀ i j, 0 < M i j) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 < f i)
    {S : Finset ι} {z : ι} (hz : z ∉ S)
    (hb : ∀ i, ∑ j ∈ insert z S, M i j * w j * f j < f i) :
    ∀ i, ∑ j ∈ S, eliminate M w z i j * w j * f j < f i := by
  have hd := eliminate_denominator_pos hM hw hf (Finset.mem_insert_self z S) hb
  have hc : 0 ≤ w z / (1 - w z * M z z) := div_nonneg (hw z) hd.le
  have hb' : ∀ i, M i z * w z * f z + ∑ j ∈ S, M i j * w j * f j < f i := by
    simpa only [Finset.sum_insert hz] using hb
  intro i
  have he : (∑ j ∈ S, eliminate M w z i j * w j * f j) =
      (∑ j ∈ S, M i j * w j * f j) +
        (w z / (1 - w z * M z z)) * M i z * (∑ j ∈ S, M z j * w j * f j) := by
    simp only [eliminate, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  have hz' : ∑ j ∈ S, M z j * w j * f j ≤ (1 - w z * M z z) * f z := by
    linarith [hb' z]
  have hmul := mul_le_mul_of_nonneg_left hz' (mul_nonneg hc (hM i z).le)
  have he' : w z / (1 - w z * M z z) * M i z * ((1 - w z * M z z) * f z) =
      M i z * w z * f z := by field_simp
  rw [he'] at hmul
  linarith [hb' i]

omit [DecidableEq ι] in
lemma eliminate_reciprocal {M : Matrix ι ι ℝ} {w : ι → ℝ} {z : ι}
    (hM : M.IsSymm) (hp : ∀ i j, 0 < M i j)
    (hP : OnePositiveSquare (Matrix.of fun i j => (M i j)⁻¹))
    (hw : 0 ≤ w z) (hd : 0 < 1 - w z * M z z) :
    OnePositiveSquare (Matrix.of fun i j => (eliminate M w z i j)⁻¹) :=
  reciprocal_rankOne_update hM hp hP z (div_nonneg hw hd.le)




theorem finite_resolvent_of_superharmonic {M : Matrix ι ι ℝ} {w f : ι → ℝ}
    (hM : M.IsSymm) (hp : ∀ i j, 0 < M i j)
    (hP : OnePositiveSquare (Matrix.of fun i j => (M i j)⁻¹))
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 < f i)
    (S : Finset ι) (hb : ∀ i, ∑ j ∈ S, M i j * w j * f j < f i) :
    ∃ R : Matrix ι ι ℝ, R.IsSymm ∧ (∀ i j, 0 < R i j) ∧
      OnePositiveSquare (Matrix.of fun i j => (R i j)⁻¹) ∧
      ∀ i j, R i j = M i j + ∑ k ∈ S, M i k * w k * R k j := by
  induction S using Finset.induction_on generalizing M with
  | empty => exact ⟨M, hM, hp, hP, by simp⟩
  | @insert z S hz ih =>
    have hd := eliminate_denominator_pos hp hw hf (Finset.mem_insert_self z S) hb
    obtain ⟨R, hRs, hRp, hRP, hReq⟩ := ih (eliminate_symm hM w z)
      (eliminate_pos hp (hw z) hd) (eliminate_reciprocal hM hp hP (hw z) hd)
      (eliminate_bound hp hw hf hz hb)
    refine ⟨R, hRs, hRp, hRP, ?_⟩
    have heq (i j) : R i j = M i j + (∑ k ∈ S, M i k * w k * R k j) +
        (w z / (1 - w z * M z z)) * M i z *
          (M z j + ∑ k ∈ S, M z k * w k * R k j) := by
      rw [hReq i j]
      simp only [eliminate, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_add]
      ring_nf
    have hez (j) : (1 - w z * M z z) * R z j =
        M z j + ∑ k ∈ S, M z k * w k * R k j := by
      have hh := heq z j
      field_simp at hh
      nlinarith
    intro i j
    rw [Finset.sum_insert hz, heq i j, ← hez j]
    field_simp
    ring


open scoped Matrix.Norms.L2Operator

end ReciprocalKernel






open Filter
open scoped Topology
namespace StrictHotSpots.BanachResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma resolvent_left (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    (1 - A) * resolvent A = 1 := mul_neg_geom_series A hA

lemma resolvent_right (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    resolvent A * (1 - A) = 1 := geom_series_mul_neg A hA

omit [CompleteSpace E] in
lemma resolvent_norm_le (A : E →L[ℝ] E) {d : ℝ} (hA : ‖A‖ ≤ d) (hd : d < 1) :
    ‖resolvent A‖ ≤ (1 - d)⁻¹ := by
  have h := tsum_geometric_le_of_norm_lt_one A (hA.trans_lt hd)
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hi : (1 - ‖A‖)⁻¹ ≤ (1 - d)⁻¹ := by
    apply inv_anti₀ (sub_pos.mpr hd)
    linarith
  dsimp only [resolvent]
  linarith

lemma resolvent_identity (A B : E →L[ℝ] E) (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    resolvent B - resolvent A = resolvent B * (B - A) * resolvent A := by
  have ht : B - A = (1 - A) - (1 - B) := by abel
  rw [ht, mul_sub, sub_mul, mul_assoc, resolvent_left A hA,
    resolvent_right B hB, mul_one, one_mul]

lemma resolvent_strong_tendsto (A : E →L[ℝ] E) (Q : ℕ → E →L[ℝ] E)
    {d : ℝ} (hd : d < 1) (hA : ‖A‖ < 1)
    (hQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ d)
    (hs : ∀ v, Tendsto (fun n => Q n v) atTop (𝓝 (A v))) (v : E) :
    Tendsto (fun n => resolvent (Q n) v) atTop (𝓝 (resolvent A v)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hz : Tendsto (fun n => (1 - d)⁻¹ * ‖(Q n - A) (resolvent A v)‖) atTop (𝓝 0) := by
    have ht := ((hs (resolvent A v)).sub (tendsto_const_nhds (x := A (resolvent A v)))).norm.const_mul (1 - d)⁻¹
    simpa using ht
  apply squeeze_zero_norm' _ hz
  filter_upwards [hQ] with n hn
  have he := congrArg (fun T : E →L[ℝ] E => T v)
    (resolvent_identity A (Q n) hA (hn.trans_lt hd))
  simp only [sub_apply, mul_apply_eq_comp] at he
  rw [he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (resolvent_norm_le (Q n) hn hd) (norm_nonneg _))

lemma resolvent_solution (A : E →L[ℝ] E) (hA : ‖A‖ < 1) {u f : E}
    (hu : u - A u = f) : u = resolvent A f := by
  have h := congrArg (fun T : E →L[ℝ] E => T u) (resolvent_right A hA)
  simpa only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self, hu] using h.symm

lemma resolvent_nonneg [PartialOrder E] [IsOrderedAddMonoid E] [OrderClosedTopology E]
    (A : E →L[ℝ] E) (hA : ‖A‖ < 1)
    (hpos : ∀ v, 0 ≤ v → 0 ≤ A v) {f : E} (hf : 0 ≤ f) :
    0 ≤ resolvent A f := by
  have ht : ∀ n : ℕ, 0 ≤ (A^n) f := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using hpos _ ih
  have hs0 : HasSum (fun n : ℕ => A^n) (resolvent A) :=
    (summable_geometric_of_norm_lt_one hA).hasSum
  have hs := (ContinuousLinearMap.apply ℝ E f).hasSum hs0
  change HasSum (fun n : ℕ => (A^n) f) (resolvent A f) at hs
  rw [← hs.tsum_eq]
  exact tsum_nonneg ht

end StrictHotSpots.BanachResolvent







open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal
namespace StrictHotSpots.CompactKernel

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma kernelOp_apply (C : C(X × X, ℝ)) (f : C(X, ℝ)) (x : X) :
    kernelOp ν C f x = ∫ z, C (z,x) * f z ∂ν := by
  change (∫ z, f z • C.curry z ∂ν) x = _
  rw [ContinuousMap.integral_apply (kernel_integrable ν C f)]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.curry_apply, mul_comm]



lemma kernelOp_norm_le (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {d : ℝ} (hd : 0 ≤ d) (hrow : ∀ x, ∫ z, C (z,x) ∂ν ≤ d) :
    ‖kernelOp ν C‖ ≤ d := by
  apply ContinuousLinearMap.opNorm_le_bound _ hd
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hd (norm_nonneg f))).mpr
  intro x
  rw [kernelOp_apply]
  calc
    ‖∫ z, C (z,x) * f z ∂ν‖ ≤ ∫ z, ‖C (z,x) * f z‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ z, C (z,x) * ‖f‖ ∂ν := by
      apply integral_mono
      · exact ((C.continuous.comp (continuous_id.prodMk continuous_const)).mul f.continuous).norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact ((C.continuous.comp (continuous_id.prodMk continuous_const)).mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · intro z
        dsimp only
        rw [norm_mul, Real.norm_of_nonneg (hC z x)]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm z) (hC z x)
    _ = (∫ z, C (z,x) ∂ν) * ‖f‖ := integral_mul_const _ _
    _ ≤ d * ‖f‖ := mul_le_mul_of_nonneg_right (hrow x) (norm_nonneg f)


omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
lemma integral_comp_simpleFunc {Y : Type*} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (π : SimpleFunc X Y) (F : Y → E) :
    ∫ x, F (π x) ∂ν = ∑ y ∈ π.range, ν.real (π ⁻¹' {y}) • F y := by
  classical
  have he : (fun x => F (π x)) = fun x =>
      ∑ y ∈ π.range, (π ⁻¹' {y}).indicator (fun _ => F y) x := by
    funext x
    simp [Set.indicator_apply, eq_comm]
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y hy
    exact integral_indicator_const _ (π.measurableSet_fiber y)
  · intro y hy
    exact (integrable_const (F y)).indicator (π.measurableSet_fiber y)


omit [BorelSpace X] in
lemma sampleOp_eq_integral (π : SimpleFunc X X) (C : C(X × X, ℝ)) (f : C(X, ℝ)) :
    sampleOp ν π C f = ∫ z, f (π z) • C.curry (π z) ∂ν := by
  rw [integral_comp_simpleFunc ν π (fun z => f z • C.curry z)]
  simp [sampleOp, sum_apply]

omit [BorelSpace X] [IsFiniteMeasure ν] in
lemma sampleOp_apply (π : SimpleFunc X X) (C : C(X × X, ℝ)) (f : C(X, ℝ)) (x : X) :
    sampleOp ν π C f x = ∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * C (z,x) * f z := by
  simp only [sampleOp, sum_apply, smul_apply,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousMap.evalCLM_apply, ContinuousMap.curry_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z hz
  ring

omit [BorelSpace X] [IsFiniteMeasure ν] in
lemma sampleOp_norm_le (π : SimpleFunc X X) (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {d : ℝ} (hd : 0 ≤ d) (hrow : ∀ x, sampleOp ν π C 1 x ≤ d) :
    ‖sampleOp ν π C‖ ≤ d := by
  apply ContinuousLinearMap.opNorm_le_bound _ hd
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hd (norm_nonneg f))).mpr
  intro x
  rw [sampleOp_apply]
  calc
    ‖∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * C (z,x) * f z‖ ≤
      ∑ z ∈ π.range, ‖ν.real (π ⁻¹' {z}) * C (z,x) * f z‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * C (z,x) * ‖f‖ := by
      apply Finset.sum_le_sum
      intro z hz
      rw [norm_mul, Real.norm_of_nonneg (mul_nonneg measureReal_nonneg (hC z x))]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm z)
        (mul_nonneg measureReal_nonneg (hC z x))
    _ = sampleOp ν π C 1 x * ‖f‖ := by simp [sampleOp_apply, Finset.sum_mul]
    _ ≤ d * ‖f‖ := mul_le_mul_of_nonneg_right (hrow x) (norm_nonneg f)

variable [Nonempty X]



lemma quantize_tendsto (x : X) : Tendsto (fun n => quantize (X := X) n x) atTop (𝓝 x) :=
  SimpleFunc.tendsto_nearestPt (by rw [(denseRange_denseSeq X).closure_range]; trivial)

lemma integral_quantize_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : C(X, E)) :
    Tendsto (fun n => ∫ z, F (quantize n z) ∂ν) atTop (𝓝 (∫ z, F z ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact ((quantize n).map F).stronglyMeasurable.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall fun z => F.norm_coe_le_norm (quantize n z)
  · exact Filter.Eventually.of_forall fun z => F.continuous.continuousAt.tendsto.comp
      (quantize_tendsto z)

lemma sampleOp_strong_tendsto (C : C(X × X, ℝ)) (f : C(X, ℝ)) :
    Tendsto (fun n => sampleOp ν (quantize n) C f) atTop (𝓝 (kernelOp ν C f)) := by
  simp only [sampleOp_eq_integral]
  exact integral_quantize_tendsto ν ⟨_, f.continuous.smul C.curry.continuous⟩



lemma sampleOp_eventually_norm_le (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 ≤ C (z,x)) {d d' : ℝ} (hd : 0 ≤ d)
    (hdd' : d < d') (hrow : ∀ x, ∫ z, C (z,x) ∂ν ≤ d) :
    ∀ᶠ n in atTop, ‖sampleOp ν (quantize n) C‖ ≤ d' := by
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (sampleOp_strong_tendsto ν C 1)
    (d' - d) (sub_pos.mpr hdd')
  filter_upwards [eventually_ge_atTop N] with n hn
  apply sampleOp_norm_le ν _ C hC (hd.trans hdd'.le)
  intro x
  have hh := (sampleOp ν (quantize n) C 1 - kernelOp ν C 1).norm_coe_le_norm x
  have hk : kernelOp ν C 1 x ≤ d := by simpa [kernelOp_apply] using hrow x
  have hc : sampleOp ν (quantize n) C 1 x - kernelOp ν C 1 x ≤
      ‖sampleOp ν (quantize n) C 1 - kernelOp ν C 1‖ :=
    (le_abs_self _).trans hh
  have he := hN n hn
  rw [dist_eq_norm] at he
  linarith

end StrictHotSpots.CompactKernel

namespace ReciprocalKernel
open Matrix
lemma onePositiveSquare_submatrix_sum_inl {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hA : OnePositiveSquare A) :
    OnePositiveSquare (A.submatrix Sum.inl Sum.inl) := by
  have he (u v : ι → ℝ) : pairing (A.submatrix Sum.inl Sum.inl) u v =
      pairing A (Sum.elim u (fun _ => 0)) (Sum.elim v (fun _ => 0)) := by
    simp [pairing, dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  refine ⟨?_, ?_⟩
  · ext i j
    exact hA.1.apply _ _
  · intro u v hu huv
    rw [he] at hu huv ⊢
    exact hA.2 _ _ hu huv
end ReciprocalKernel


namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma l2SectionOp_apply (C : C(X × X, ℝ)) (f : Lp ℝ 2 ν) (x : X) :
    l2SectionOp ν C f x = ∫ z, C (z,x) * f z ∂ν := by
  change (∫ z, f z • C.curry z ∂ν) x = _
  rw [ContinuousMap.integral_apply (l2kernel_integrable ν C f)]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.curry_apply, mul_comm]

lemma l2SectionOp_toLp (C : C(X × X, ℝ)) (f : C(X, ℝ)) :
    l2SectionOp ν C (ContinuousMap.toLp 2 ν ℝ f) = kernelOp ν C f := by
  ext x
  rw [kernelOp_apply, l2SectionOp_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν f] with z hz
  rw [hz]

lemma l2SectionOp_nonneg (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {f : Lp ℝ 2 ν} (hf : 0 ≤ f) : 0 ≤ l2SectionOp ν C f := by
  intro x
  change 0 ≤ l2SectionOp ν C f x
  rw [l2SectionOp_apply]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with z hz
  exact mul_nonneg (hC z x) hz

lemma l2Op_nonneg (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {f : Lp ℝ 2 ν} (hf : 0 ≤ f) : 0 ≤ l2Op ν C f := by
  apply (Lp.coeFn_nonneg _).mp
  have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (l2SectionOp ν C f)
  filter_upwards [he] with x hx
  exact (l2SectionOp_nonneg ν C hC hf x).trans_eq hx.symm



theorem exists_superharmonic (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    (hn : ‖l2Op ν C‖ < 1) :
    ∃ f : C(X, ℝ), (∀ x, 1 ≤ f x) ∧ kernelOp ν C f = f - 1 := by
  let a := ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))
  let g := resolvent (l2Op ν C) a
  let f : C(X, ℝ) := 1 + l2SectionOp ν C g
  have ha : 0 ≤ a := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (1 : C(X, ℝ))] with x hx
    change 0 ≤ (ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))) x
    rw [hx]
    exact zero_le_one
  have hg : 0 ≤ g := resolvent_nonneg _ hn (fun v hv => l2Op_nonneg ν C hC hv) ha
  have hf : ContinuousMap.toLp 2 ν ℝ f = g := by
    have he := congrArg (fun T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => T a)
      (resolvent_left (l2Op ν C) hn)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at he
    change g - l2Op ν C g = a at he
    dsimp only [f]
    rw [map_add]
    change a + l2Op ν C g = g
    exact (sub_eq_iff_eq_add.mp he).symm
  refine ⟨f, ?_, ?_⟩
  · intro x
    have hp := l2SectionOp_nonneg ν C hC hg x
    change 0 ≤ l2SectionOp ν C g x at hp
    change 1 ≤ 1 + l2SectionOp ν C g x
    linarith
  · rw [← l2SectionOp_toLp, hf]
    dsimp only [f]
    abel

end StrictHotSpots.CompactKernel


namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma scaledKernel_pos (C : C(X × X, ℝ)) (hC : ∀ z x, 0 < C (z,x))
    (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) (z x : X) :
    0 < scaledKernel C f hf (z,x) := div_pos (mul_pos (hC z x) (hf z)) (hf x)

lemma kernelOp_scaled (C : C(X × X, ℝ)) (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    (u : C(X, ℝ)) :
    kernelOp ν (scaledKernel C f hf) u = invMap f hf * kernelOp ν C (f*u) := by
  ext x
  simp only [kernelOp_apply, ContinuousMap.mul_apply]
  change (∫ z, (C (z,x) * f z / f x) * u z ∂ν) =
    (f x)⁻¹ * ∫ z, C (z,x) * (f z * u z) ∂ν
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by ring

omit [BorelSpace X] [IsFiniteMeasure ν] in
lemma sampleOp_scaled (π : SimpleFunc X X) (C : C(X × X, ℝ))
    (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) (u : C(X, ℝ)) :
    sampleOp ν π (scaledKernel C f hf) u = invMap f hf * sampleOp ν π C (f*u) := by
  ext x
  simp only [sampleOp_apply, ContinuousMap.mul_apply]
  change (∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * (C (z,x) * f z / f x) * u z) =
    (f x)⁻¹ * ∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * C (z,x) * (f z * u z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma mul_invMap (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) : f * invMap f hf = 1 := by
  ext x
  exact mul_inv_cancel₀ (hf x).ne'

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma invMap_mul_cancel (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) (u : C(X, ℝ)) :
    f * (invMap f hf * u) = u := by rw [← mul_assoc, mul_invMap, one_mul]



lemma scaled_row_bound [Nonempty X] (C : C(X × X, ℝ))
    (f : C(X, ℝ)) (hf : ∀ x, 1 ≤ f x) (he : kernelOp ν C f = f - 1) :
    0 ≤ 1 - ‖f‖⁻¹ ∧ 1 - ‖f‖⁻¹ < 1 ∧
      ∀ x, ∫ z, scaledKernel C f (fun x => (hf x).trans_lt' zero_lt_one) (z,x) ∂ν
        ≤ 1 - ‖f‖⁻¹ := by
  have hfn : 1 ≤ ‖f‖ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (hf x).trans ((le_abs_self _).trans (f.norm_coe_le_norm x))
  have hfnpos : 0 < ‖f‖ := lt_of_lt_of_le zero_lt_one hfn
  refine ⟨sub_nonneg.mpr (inv_le_one_of_one_le₀ hfn), by linarith [inv_pos.mpr hfnpos], ?_⟩
  intro x
  have hx : 0 < f x := lt_of_lt_of_le zero_lt_one (hf x)
  have hfx : f x ≤ ‖f‖ := (le_abs_self _).trans (f.norm_coe_le_norm x)
  have hxf := inv_anti₀ hx hfx
  have hr := congrArg (fun u : C(X, ℝ) => u x)
    (kernelOp_scaled ν C f (fun x => lt_of_lt_of_le zero_lt_one (hf x)) 1)
  simp only [mul_one, he, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, kernelOp_apply] at hr
  change (∫ z, scaledKernel C f _ (z,x) ∂ν) = (f x)⁻¹ * (f x - 1) at hr
  rw [hr, mul_sub, inv_mul_cancel₀ hx.ne', mul_one]
  linarith

end StrictHotSpots.CompactKernel

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]


omit [MeasurableSpace X] [BorelSpace X] in
lemma scaled_solution (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    (A B : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hB : ‖B‖ < 1)
    (hscale : ∀ u, B u = invMap f hf * A (f * u))
    {u v : C(X, ℝ)} (heq : u - A u = v) :
    u = f * resolvent B (invMap f hf * v) := by
  have h : invMap f hf * u - B (invMap f hf * u) = invMap f hf * v := by
    rw [hscale, invMap_mul_cancel, ← mul_sub, heq]
  have hr := congrArg (fun z : C(X, ℝ) => f * z) (resolvent_solution B hB h)
  rwa [invMap_mul_cancel] at hr

lemma rescaledKernel_eq_l2ResolvedKernel (C : C(X × X, ℝ))
    (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    (hL : ‖l2Op ν C‖ < 1) (hC : ‖kernelOp ν (scaledKernel C f hf)‖ < 1)
    (x y : X) :
    rescaledKernel C f hf (kernelOp ν (scaledKernel C f hf)) x y =
      l2ResolvedKernel ν C x y := by
  let g := resolvent (l2Op ν C) (ContinuousMap.toLp 2 ν ℝ (C.curry y))
  let u : C(X, ℝ) := C.curry y + l2SectionOp ν C g
  have hg : ContinuousMap.toLp 2 ν ℝ u = g := by
    have he := congrArg (fun T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν =>
      T (ContinuousMap.toLp 2 ν ℝ (C.curry y))) (resolvent_left (l2Op ν C) hL)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at he
    change g - l2Op ν C g = ContinuousMap.toLp 2 ν ℝ (C.curry y) at he
    change ContinuousMap.toLp 2 ν ℝ (C.curry y + l2SectionOp ν C g) = g
    rw [map_add]
    exact (sub_eq_iff_eq_add.mp he).symm
  have hu : u - kernelOp ν C u = C.curry y := by
    rw [← l2SectionOp_toLp, hg]
    dsimp only [u]
    abel
  have hu' := scaled_solution f hf (kernelOp ν C)
    (kernelOp ν (scaledKernel C f hf)) hC (kernelOp_scaled ν C f hf) hu
  have h := congrArg (fun v : C(X, ℝ) => v x) hu'
  exact h.symm

lemma l2ResolvedKernel_ge (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    (hn : ‖l2Op ν C‖ < 1) (x y : X) :
    C (y,x) ≤ l2ResolvedKernel ν C x y := by
  have hy : 0 ≤ ContinuousMap.toLp 2 ν ℝ (C.curry y) := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (C.curry y)] with z hz
    rw [hz]
    exact hC y z
  have hp := l2SectionOp_nonneg ν C hC
    (resolvent_nonneg (l2Op ν C) hn (fun v hv => l2Op_nonneg ν C hC hv) hy) x
  exact le_add_of_nonneg_right hp

omit [BorelSpace X] [IsFiniteMeasure ν] in


lemma sampled_rescaled_reciprocal (π : SimpleFunc X X) (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 < C (z,x)) (hsym : ∀ x y, C (x,y) = C (y,x))
    (hP : ∀ (ι : Type) [Fintype ι] (s : ι → X),
      OnePositiveSquare (Matrix.of fun i j => (C (s i,s j))⁻¹))
    (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hrow : ∀ x, sampleOp ν π (scaledKernel C f hf) 1 x ≤ d)
    {ι : Type} [Fintype ι] (s : ι → X) :
    (∀ i j, 0 < rescaledKernel C f hf (sampleOp ν π (scaledKernel C f hf)) (s i) (s j)) ∧
      OnePositiveSquare (Matrix.of fun i j =>
        (rescaledKernel C f hf (sampleOp ν π (scaledKernel C f hf)) (s i) (s j))⁻¹) := by
  classical
  let t : ι ⊕ π.range → X := Sum.elim s Subtype.val
  let w : ι ⊕ π.range → ℝ := Sum.elim (fun _ => 0) (fun z => ν.real (π ⁻¹' {z.val}))
  let M : Matrix (ι ⊕ π.range) (ι ⊕ π.range) ℝ := Matrix.of fun i j => C (t j,t i)
  have hM : M.IsSymm := by ext i j; exact hsym _ _
  have hp : ∀ i j, 0 < M i j := fun i j => hC _ _
  have hrec : OnePositiveSquare (Matrix.of fun i j => (M i j)⁻¹) := by
    have he : (Matrix.of fun i j => (M i j)⁻¹) =
        (Matrix.of fun i j => (C (t i,t j))⁻¹) := by ext i j; simp [M, hsym]
    rw [he]
    exact hP _ t
  have hw : ∀ i, 0 ≤ w i := by intro i; cases i <;> simp [w, measureReal_nonneg]
  have hsum (i : ι ⊕ π.range) (v : C(X, ℝ)) :
      ∑ j, M i j * w j * v (t j) = sampleOp ν π C v (t i) := by
    simp only [Fintype.sum_sum_type, M, w, t, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
      sampleOp_apply]
    rw [Finset.sum_subtype π.range (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hb : ∀ i, ∑ j ∈ Finset.univ, M i j * w j * f (t j) < f (t i) := by
    intro i
    rw [hsum]
    have he := congrArg (fun v : C(X, ℝ) => f * v) (sampleOp_scaled ν π C f hf 1)
    rw [mul_one, invMap_mul_cancel] at he
    have hx := congrArg (fun v : C(X, ℝ) => v (t i)) he
    change f (t i) * sampleOp ν π (scaledKernel C f hf) 1 (t i) = sampleOp ν π C f (t i) at hx
    rw [← hx]
    exact (mul_le_mul_of_nonneg_left (hrow (t i)) (hf _).le).trans_lt
      (by simpa using (mul_lt_mul_of_pos_left hd1 (hf (t i))))
  obtain ⟨R,hRs,hRp,hRrec,hReq⟩ := finite_resolvent_of_superharmonic
    hM hp hrec hw (fun i => hf (t i)) Finset.univ hb
  have hn : ‖sampleOp ν π (scaledKernel C f hf)‖ < 1 :=
    (sampleOp_norm_le ν π _ (fun z x => (scaledKernel_pos C hC f hf z x).le) hd hrow).trans_lt hd1
  have hmatch (j : ι ⊕ π.range) : ∀ i,
      R i j = rescaledKernel C f hf (sampleOp ν π (scaledKernel C f hf)) (t i) (t j) := by
    let u : C(X, ℝ) := C.curry (t j) +
      ∑ z : π.range, (ν.real (π ⁻¹' {z.val}) * R (Sum.inr z) j) • C.curry z.val
    have hu (i : ι ⊕ π.range) : u (t i) = R i j := by
      rw [hReq i j]
      simp only [u, ContinuousMap.add_apply, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, ContinuousMap.curry_apply, smul_eq_mul,
        Fintype.sum_sum_type, M, w, t, Sum.elim_inl, Sum.elim_inr,
        Matrix.of_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      ring
    have he : u - sampleOp ν π C u = C.curry (t j) := by
      ext x
      simp only [ContinuousMap.sub_apply, sampleOp_apply]
      rw [Finset.sum_subtype π.range (fun _ => Iff.rfl)]
      have hz (z : π.range) : u z.val = R (Sum.inr z) j := hu (Sum.inr z)
      simp only [hz, u, ContinuousMap.add_apply, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, ContinuousMap.curry_apply, smul_eq_mul]
      have hsum' : (∑ z : π.range, (ν.real (π ⁻¹' {↑z}) * R (Sum.inr z) j) * C (↑z,x)) =
          ∑ z : π.range, ν.real (π ⁻¹' {↑z}) * C (↑z,x) * R (Sum.inr z) j := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      rw [hsum']
      abel
    have he' := scaled_solution f hf (sampleOp ν π C)
      (sampleOp ν π (scaledKernel C f hf)) hn (sampleOp_scaled ν π C f hf) he
    intro i
    rw [← hu i, he']
    rfl
  refine ⟨fun i j => ?_, ?_⟩
  · simpa only [t, Sum.elim_inl, hmatch] using hRp (Sum.inl i) (Sum.inl j)
  · have hsub := onePositiveSquare_submatrix_sum_inl hRrec
    convert hsub using 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hmatch, t, Sum.elim_inl]

lemma rescaledKernel_tendsto [Nonempty X] (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 ≤ C (z,x)) (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hrow : ∀ x, ∫ z, scaledKernel C f hf (z,x) ∂ν ≤ d) (x y : X) :
    Tendsto (fun n => rescaledKernel C f hf (sampleOp ν (quantize n) (scaledKernel C f hf)) x y) atTop
      (𝓝 (rescaledKernel C f hf (kernelOp ν (scaledKernel C f hf)) x y)) := by
  have hp (z x : X) : 0 ≤ scaledKernel C f hf (z,x) :=
    div_nonneg (mul_nonneg (hC z x) (hf z).le) (hf x).le
  have hn := kernelOp_norm_le ν (scaledKernel C f hf) hp hd hrow
  have hh := BanachResolvent.resolvent_strong_tendsto (kernelOp ν (scaledKernel C f hf))
    (fun n => sampleOp ν (quantize n) (scaledKernel C f hf))
    (d := (1+d)/2) (by linarith) (hn.trans_lt hd1)
    (sampleOp_eventually_norm_le ν (scaledKernel C f hf) hp hd (by linarith) hrow)
    (sampleOp_strong_tendsto ν (scaledKernel C f hf)) (invMap f hf * C.curry y)
  exact (((ContinuousMap.evalCLM ℝ x).continuous.tendsto _).comp hh).const_mul (f x)

end StrictHotSpots.CompactKernel

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]




theorem compact_reciprocal_of_l2_norm_lt_one [Nonempty X] (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 < C (z,x)) (hsym : ∀ x y, C (x,y) = C (y,x))
    (hP : ∀ (ι : Type) [Fintype ι] (s : ι → X),
      OnePositiveSquare (Matrix.of fun i j => (C (s i,s j))⁻¹))
    (hL : ‖l2Op ν C‖ < 1)
    {ι : Type} [Fintype ι] (s : ι → X) :
    (∀ i j, 0 < l2ResolvedKernel ν C (s i) (s j)) ∧
      OnePositiveSquare (Matrix.of fun i j => (l2ResolvedKernel ν C (s i) (s j))⁻¹) := by
  obtain ⟨f,hf,heq⟩ := exists_superharmonic ν C (fun z x => (hC z x).le) hL
  let hf' : ∀ x, 0 < f x := fun x => lt_of_lt_of_le zero_lt_one (hf x)
  let C' := scaledKernel C f hf'
  let d : ℝ := 1 - ‖f‖⁻¹
  obtain ⟨hd,hd1,hrow⟩ := scaled_row_bound ν C f hf heq
  have hp' (z x : X) : 0 ≤ C' (z,x) := (scaledKernel_pos C hC f hf' z x).le
  have hn : ‖kernelOp ν C'‖ < 1 :=
    (kernelOp_norm_le ν C' hp' hd hrow).trans_lt hd1
  have hkernel (x y : X) : rescaledKernel C f hf' (kernelOp ν C') x y =
      l2ResolvedKernel ν C x y := rescaledKernel_eq_l2ResolvedKernel ν C f hf' hL hn x y
  have hp (x y : X) : 0 < l2ResolvedKernel ν C x y :=
    (hC y x).trans_le (l2ResolvedKernel_ge ν C (fun z x => (hC z x).le) hL x y)
  refine ⟨fun i j => hp _ _, ?_⟩
  have hev := sampleOp_eventually_norm_le ν C' hp' hd
    (show d < (1+d)/2 by dsimp [d]; linarith) hrow
  have hr : ∀ᶠ n in atTop, ∀ x, sampleOp ν (quantize n) C' 1 x ≤ (1+d)/2 := by
    filter_upwards [hev] with n hnn x
    calc
      sampleOp ν (quantize n) C' 1 x ≤ ‖sampleOp ν (quantize n) C' 1 x‖ := le_abs_self _
      _ ≤ ‖sampleOp ν (quantize n) C' 1‖ := ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖sampleOp ν (quantize n) C'‖ * ‖(1 : C(X, ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1+d)/2 := by simpa using hnn
  obtain ⟨N,hN⟩ := eventually_atTop.mp hr
  apply onePositiveSquare_of_entrywise_tendsto
    (A := fun n => Matrix.of fun i j =>
      (rescaledKernel C f hf' (sampleOp ν (quantize (n+N)) C') (s i) (s j))⁻¹)
  · intro n
    exact (sampled_rescaled_reciprocal ν (quantize (n+N)) C hC hsym hP f hf'
      (show 0 ≤ (1+d)/2 by dsimp [d]; linarith)
      (show (1+d)/2 < 1 by dsimp [d]; linarith)
      (hN _ (Nat.le_add_left _ _)) s).2
  · intro i j
    have ht := rescaledKernel_tendsto ν C (fun z x => (hC z x).le) f hf' hd hd1 hrow (s i) (s j)
    rw [hkernel] at ht
    exact (ht.inv₀ (hp _ _).ne').comp (tendsto_add_atTop_nat N)

lemma l2ResolvedKernel_eq_inner (C : C(X × X, ℝ))
    (hsym : ∀ x y, C (x,y) = C (y,x)) (x y : X) :
    l2ResolvedKernel ν C x y = C (x,y) +
      inner ℝ (ContinuousMap.toLp 2 ν ℝ (C.curry x))
        (resolvent (l2Op ν C) (ContinuousMap.toLp 2 ν ℝ (C.curry y))) := by
  unfold l2ResolvedKernel
  rw [hsym y x, l2SectionOp_apply, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (C.curry x)] with z hz
  rw [hz]
  change C (z,x) * _ = _ * C (x,z)
  rw [hsym z x, mul_comm]

end StrictHotSpots.CompactKernel




open MeasureTheory Filter
open scoped Topology ENNReal
namespace StrictHotSpots.L2Limits
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma tendsto_L2_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → Lp ℝ 2 ν) (g b : Lp ℝ 2 ν)
    (hdom : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    Tendsto f l (𝓝 g) := by
  have ht := tendsto_toLp_of_dominated (fun n => Lp.memLp (f n)) (Lp.memLp g)
    (Lp.memLp b) hdom hlim
  simpa only [Lp.toLp_coeFn] using ht

end StrictHotSpots.L2Limits

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma l2Op_ae_integral (C : C(X × X, ℝ)) (f : Lp ℝ 2 ν) :
    ∀ᵐ x ∂ν, l2Op ν C f x = ∫ z, C (z,x) * f z ∂ν := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (l2SectionOp ν C f)]
    with x hx
  exact hx.trans (l2SectionOp_apply ν C f x)

lemma l2Op_abs_domination (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ x, ∀ᵐ z ∂ν, C (z,x) ≤ G z x)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (f : Lp ℝ 2 ν) : |l2Op ν C f| ≤ T |f| := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [l2Op_ae_integral ν C f, hT |f|, Lp.coeFn_abs (l2Op ν C f)]
    with x hx htx hax
  rw [hax, hx, htx]
  calc
    |∫ z, C (z,x) * f z ∂ν| ≤ ∫ z, ‖C (z,x) * f z‖ ∂ν :=
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => C (z,x) * f z)
    _ ≤ ∫ z, G z x * (|f|) z ∂ν := by
      apply integral_mono_ae
      · exact (ContinuousMap.memLp (p := (2 : ℝ≥0∞)) ν ℝ
          (⟨fun z => C (z,x), C.continuous.comp (continuous_id.prodMk continuous_const)⟩ : C(X,ℝ))).integrable_mul (Lp.memLp f) |>.norm
      · exact (hG x).integrable_mul (Lp.memLp |f|)
      · filter_upwards [hdom x, Lp.coeFn_abs f] with z hz hfz
        rw [hfz, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hC z x), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)

lemma norm_l2Op_le_of_domination (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ x, ∀ᵐ z ∂ν, C (z,x) ≤ G z x)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν) :
    ‖l2Op ν C‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  calc
    ‖l2Op ν C f‖ ≤ ‖T |f|‖ :=
      norm_le_norm_of_abs_le_abs ((l2Op_abs_domination ν C hC G hG hdom T hT f).trans
        (le_abs_self _))
    _ ≤ ‖T‖ * ‖f‖ := by simpa only [norm_abs_eq_norm] using T.le_opNorm |f|

lemma l2Op_strong_tendsto_of_dominated
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 ≤ C n (z,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (f : Lp ℝ 2 ν) :
    Tendsto (fun n => l2Op ν (C n) f) atTop (𝓝 (T f)) := by
  apply L2Limits.tendsto_L2_of_dominated _ _ (T |f|)
  · apply Eventually.of_forall
    intro n
    have hd := (Lp.coeFn_le _ _).mpr (l2Op_abs_domination ν (C n) (hC n) G hG
      (hdom n) T hT f)
    filter_upwards [hd, Lp.coeFn_abs (l2Op ν (C n) f)] with x hx hax
    simpa only [hax, Real.norm_eq_abs] using hx
  · have he : ∀ᵐ x ∂ν, ∀ n, l2Op ν (C n) f x = ∫ z, C n (z,x) * f z ∂ν :=
      ae_all_iff.mpr fun n => l2Op_ae_integral ν (C n) f
    filter_upwards [he, hT f] with x hx htx
    simp only [hx, htx]
    apply tendsto_integral_of_dominated_convergence (fun z => G z x * ‖f z‖)
    · intro n
      exact ((C n).continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f)
    · exact (hG x).integrable_mul (Lp.memLp f).norm
    · intro n
      filter_upwards [hdom n x] with z hz
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hC n z x)]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    · filter_upwards [hlim x] with z hz
      exact hz.mul_const (f z)

end StrictHotSpots.CompactKernel

namespace StrictHotSpots.BanachResolvent
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma resolvent_strong_tendsto_moving (A : E →L[ℝ] E) (Q : ℕ → E →L[ℝ] E)
    {d : ℝ} (hd : d < 1) (hA : ‖A‖ < 1)
    (hQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ d)
    (hs : ∀ v, Tendsto (fun n => Q n v) atTop (𝓝 (A v)))
    {v : ℕ → E} {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => resolvent (Q n) (v n)) atTop (𝓝 (resolvent A w)) := by
  have hz : Tendsto (fun n => resolvent (Q n) (v n-w)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => (1-d)⁻¹ * ‖v n-w‖) atTop (𝓝 0) := by
      simpa using (hv.sub_const w).norm.const_mul (1-d)⁻¹
    apply squeeze_zero_norm' _ hb
    filter_upwards [hQ] with n hn
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (resolvent_norm_le (Q n) hn hd) (norm_nonneg _))
  have ht := hz.add (resolvent_strong_tendsto A Q hd hA hQ hs w)
  simpa only [map_sub, sub_add_cancel, zero_add] using ht

end StrictHotSpots.BanachResolvent

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma l2Sections_tendsto_of_dominated
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 ≤ C n (z,x))
    (hsym : ∀ n x y, C n (x,y) = C n (y,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (x : X) :
    Tendsto (fun n => ContinuousMap.toLp 2 ν ℝ ((C n).curry x)) atTop
      (𝓝 ((hG x).toLp (fun z => G z x))) := by
  apply L2Limits.tendsto_L2_of_dominated _ _ ((hG x).toLp (fun z => G z x))
  · apply Eventually.of_forall
    intro n
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν ((C n).curry x),
      (hG x).coeFn_toLp, hdom n x] with z hz hgz hdz
    rw [hz, hgz]
    change ‖C n (x,z)‖ ≤ G z x
    rw [hsym n x z, Real.norm_eq_abs, abs_of_nonneg (hC n z x)]
    exact hdz
  · have he : ∀ᵐ z ∂ν, ∀ n,
        ContinuousMap.toLp 2 ν ℝ ((C n).curry x) z = C n (x,z) :=
      ae_all_iff.mpr fun n => ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν ((C n).curry x)
    filter_upwards [he, (hG x).coeFn_toLp, hlim x] with z hz hgz hlz
    simpa only [hz, hgz, hsym] using hlz



lemma l2ResolvedKernel_tendsto_of_dominated
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 ≤ C n (z,x))
    (hsym : ∀ n x y, C n (x,y) = C n (y,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (hsub : ‖T‖ < 1) (x y : X)
    (hxy : Tendsto (fun n => C n (x,y)) atTop (𝓝 (G x y))) :
    Tendsto (fun n => l2ResolvedKernel ν (C n) x y) atTop
      (𝓝 (singularResolvedKernel ν G hG T x y)) := by
  have hs := l2Sections_tendsto_of_dominated ν C hC hsym G hG hdom hlim
  have hop := l2Op_strong_tendsto_of_dominated ν C hC G hG hdom hlim T hT
  have hb : ∀ᶠ n in atTop, ‖l2Op ν (C n)‖ ≤ ‖T‖ :=
    Eventually.of_forall fun n => norm_l2Op_le_of_domination ν (C n) (hC n) G hG
      (hdom n) T hT
  have hr := resolvent_strong_tendsto_moving T (fun n => l2Op ν (C n))
    hsub hsub hb hop (hs y)
  have ht := hxy.add ((hs x).inner hr)
  simpa only [singularResolvedKernel, l2ResolvedKernel_eq_inner ν _ (hsym _)] using ht

lemma singularResolvedKernel_ge
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 ≤ C n (z,x))
    (hsym : ∀ n x y, C n (x,y) = C n (y,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (hsub : ‖T‖ < 1) (x y : X)
    (hxy : Tendsto (fun n => C n (x,y)) atTop (𝓝 (G x y))) :
    G x y ≤ singularResolvedKernel ν G hG T x y := by
  apply le_of_tendsto_of_tendsto hxy
    (l2ResolvedKernel_tendsto_of_dominated ν C hC hsym G hG hdom hlim T hT hsub x y hxy)
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [hsym n x y]
    exact l2ResolvedKernel_ge ν (C n) (hC n)
      ((norm_l2Op_le_of_domination ν (C n) (hC n) G hG (hdom n) T hT).trans_lt hsub) x y





theorem singular_reciprocal_of_regularization [Nonempty X] [DecidableEq X]
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 < C n (z,x))
    (hsym : ∀ n x y, C n (x,y) = C n (y,x))
    (hP : ∀ n (ι : Type) [Fintype ι] (s : ι → X),
      OnePositiveSquare (Matrix.of fun i j => (C n (s i,s j))⁻¹))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hpos : ∀ x y, x ≠ y → 0 < G x y)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (hoff : ∀ x y, x ≠ y → Tendsto (fun n => C n (x,y)) atTop (𝓝 (G x y)))
    (hdiag : ∀ x, Tendsto (fun n => C n (x,x)) atTop atTop)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (hsub : ‖T‖ < 1) {ι : Type} [Fintype ι] (s : ι → X) :
    OnePositiveSquare (Matrix.of fun i j =>
      if s i = s j then 0 else (singularResolvedKernel ν G hG T (s i) (s j))⁻¹) := by
  classical
  have hCn : ∀ n z x, 0 ≤ C n (z,x) := fun n z x => (hC n z x).le
  have hb (n : ℕ) : ‖l2Op ν (C n)‖ < 1 :=
    (norm_l2Op_le_of_domination ν (C n) (hCn n) G hG (hdom n) T hT).trans_lt hsub
  apply onePositiveSquare_of_entrywise_tendsto
    (A := fun n => Matrix.of fun i j => (l2ResolvedKernel ν (C n) (s i) (s j))⁻¹)
  · intro n
    exact (compact_reciprocal_of_l2_norm_lt_one ν (C n) (hC n) (hsym n) (hP n) (hb n) s).2
  · intro i j
    dsimp only [Matrix.of_apply]
    split_ifs with hij
    · have ht : Tendsto (fun n => l2ResolvedKernel ν (C n) (s i) (s j)) atTop atTop := by
        apply tendsto_atTop_mono _ (hdiag (s i))

        intro n
        simpa only [← hij] using l2ResolvedKernel_ge ν (C n) (hCn n) (hb n) (s i) (s i)
      exact tendsto_inv_atTop_zero.comp ht
    · have hp := (hpos (s i) (s j) hij).trans_le
        (singularResolvedKernel_ge ν C hCn hsym G hG hdom hlim T hT hsub
          (s i) (s j) (hoff (s i) (s j) hij))
      exact (l2ResolvedKernel_tendsto_of_dominated ν C hCn hsym G hG hdom hlim T hT hsub
        (s i) (s j) (hoff (s i) (s j) hij)).inv₀ hp.ne'

end StrictHotSpots.CompactKernel

end SingularLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_DiskKernel
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section DiskFiniteLayer

open Filter Matrix
open scoped Topology
namespace StrictHotSpots.ScalarKernel

lemma choose_recurrence (a : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.choose a (n + 1) = (a - n) * Ring.choose a n := by
  have hh := Ring.descPochhammer_eq_factorial_smul_choose a (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast,
    Ring.descPochhammer_eq_factorial_smul_choose] at hh
  simp only [nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one] at hh
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hn
  nlinarith [hh]

lemma coeff_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) : 0 ≤ coeff a n := by
  induction n with
  | zero =>
    have hh := choose_recurrence a 1
    simp only [Nat.cast_one, Ring.choose_one_right] at hh
    simp only [coeff, zero_add, even_two, Even.neg_pow, one_pow, mul_one]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr ha1)]
  | succ n ih =>
    have hh := choose_recurrence a (n + 2)
    have hrec : ((n : ℝ) + 3) * coeff a (n + 1) = ((n : ℝ) + 2 - a) * coeff a n := by
      simp only [coeff, Nat.cast_add, Nat.cast_ofNat] at *
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
      nlinarith [congrArg (fun t : ℝ => t * (-1) ^ (n + 2)) hh]
    have hn : 0 < (n : ℝ) + 3 := by positivity
    have hmul : 0 ≤ ((n : ℝ) + 2 - a) * coeff a n :=
      mul_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) ih
    nlinarith

lemma binomial_hasSum {a k : ℝ} (hk : |k| < 1) :
    HasSum (fun n : ℕ => Ring.choose a n * (-k) ^ n) ((1 - k) ^ a) := by
  have hh := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)).hasSum
    (y := -k) (by simpa [Metric.mem_eball, edist_dist, Real.norm_eq_abs] using hk)
  simpa [binomialSeries, FormalMultilinearSeries.coeff_ofScalars,
    sub_eq_add_neg, mul_comm] using hh


lemma defect_hasSum {a k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    HasSum (fun n : ℕ => coeff a n * k ^ (n + 1))
      ((1 - (1 - k) ^ a) / k - a) := by
  have hh := binomial_hasSum (a := a) (abs_lt.mpr ⟨by linarith, hk1⟩)
  have ht := (hasSum_nat_add_iff' 2).mpr hh
  have hs := ht.mul_left (-k⁻¹)
  have he : (fun n : ℕ => -k⁻¹ * (Ring.choose a (n + 2) * (-k) ^ (n + 2))) =
      (fun n : ℕ => coeff a n * k ^ (n + 1)) := by
    funext n
    rw [neg_pow k (n + 2)]
    simp only [coeff, pow_add]
    field_simp
  rw [he] at hs
  have hv : -k⁻¹ * ((1 - k) ^ a - ∑ i ∈ Finset.range 2, Ring.choose a i * (-k) ^ i) =
      (1 - (1 - k) ^ a) / k - a := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      Ring.choose_zero_right, Ring.choose_one_right, pow_zero, pow_one]
    field_simp
    ring
  rwa [hv] at hs

section Matrix
variable {ι : Type*} [Fintype ι]


lemma posSemidef_entry_pow {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (n : ℕ) :
    (Matrix.of (fun i j => A i j ^ n)).PosSemidef := by
  induction n with
  | zero =>
    simpa [Matrix.vecMulVec] using
      (Matrix.posSemidef_vecMulVec_self_star (fun _ : ι => (1 : ℝ)))
  | succ n ih =>
    have he : Matrix.of (fun i j => A i j ^ (n + 1)) =
        Matrix.of (fun i j => A i j ^ n) ⊙ A := by
      ext i j
      simp [pow_succ]
    rw [he]
    exact ih.hadamard hA


lemma posSemidef_of_entrywise_tendsto {A : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (hA : ∀ n, (A n).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact tendsto_nhds_unique (hlim j i)
      ((hlim i j).congr fun n => by simpa using (hA n).isHermitian.apply j i)
  · intro x
    have hlimq : Tendsto (fun n => star x ⬝ᵥ A n *ᵥ x) atTop
        (𝓝 (star x ⬝ᵥ B *ᵥ x)) := by
      unfold dotProduct Matrix.mulVec
      exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hlim i j).mul tendsto_const_nhds))
    exact ge_of_tendsto hlimq (Filter.Eventually.of_forall fun n =>
      (hA n).dotProduct_mulVec_nonneg x)


lemma defect_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hpos : ∀ i j, 0 < A i j) (hlt : ∀ i j, A i j < 1)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (Matrix.of (fun i j => (1 - (1 - A i j) ^ a) / A i j - a)).PosSemidef := by
  apply posSemidef_of_entrywise_tendsto
    (A := fun n => ∑ m ∈ Finset.range n,
      coeff a m • Matrix.of (fun i j => A i j ^ (m + 1)))
  · intro n
    exact Matrix.posSemidef_sum _ (fun m _ =>
      (posSemidef_entry_pow hA _).smul (coeff_nonneg ha ha1 m))
  · intro i j
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      using (defect_hasSum (a := a) (hpos i j) (hlt i j)).tendsto_sum_nat

lemma integral_posSemidef {F : ℝ → Matrix ι ι ℝ}
    (hF : ∀ a ∈ Set.Icc (0 : ℝ) 1, (F a).PosSemidef)
    (hi : ∀ i j, IntervalIntegrable (fun a => F a i j) MeasureTheory.volume 0 1) :
    (Matrix.of (fun i j => ∫ a in (0 : ℝ)..1, F a i j)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    apply intervalIntegral.integral_congr
    intro a ha
    have ha' : a ∈ Set.Icc (0 : ℝ) 1 := by simpa using ha
    simpa using (hF a ha').isHermitian.apply i j
  · intro v
    have he : (star v ⬝ᵥ (Matrix.of (fun i j => ∫ a in (0 : ℝ)..1, F a i j)) *ᵥ v) =
        ∫ a in (0 : ℝ)..1, star v ⬝ᵥ F a *ᵥ v := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, Matrix.of_apply]
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
        · simp only [intervalIntegral.integral_mul_const]
        · intro j _
          exact (hi i j).mul_const _
      · intro i _
        simpa only [Finset.sum_apply] using
          (IntervalIntegrable.sum Finset.univ fun j _ => (hi i j).mul_const (v j)).const_mul (v i)
    rw [he]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro a ha
    exact (hF a ha).dotProduct_mulVec_nonneg v

end Matrix


lemma integral_rpow_parameter {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (∫ a in (0 : ℝ)..1, x ^ a) = (x - 1) / Real.log x := by
  have hl : Real.log x ≠ 0 := ne_of_lt (Real.log_neg hx hx1)
  have hh := intervalIntegral.mul_integral_comp_mul_left
    (f := Real.exp) (a := 0) (b := 1) (Real.log x)
  simp only [mul_zero, mul_one, integral_exp, Real.exp_zero, Real.exp_log hx] at hh
  rw [eq_div_iff hl]
  convert hh using 1
  · simp only [Real.rpow_def_of_pos hx, mul_comm]

lemma integral_defect {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    (∫ a in (0 : ℝ)..1, ((1 - (1 - k) ^ a) / k - a)) =
      k⁻¹ - 1 / 2 + (Real.log (1 - k))⁻¹ := by
  have hb : 0 < 1 - k := sub_pos.mpr hk1
  have hcont : Continuous (fun a : ℝ => (1 - k) ^ a) :=
    Real.continuous_const_rpow hb.ne'
  have hi := hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have hi1 : IntervalIntegrable (fun a : ℝ => (1 - (1 - k) ^ a) / k)
      MeasureTheory.volume 0 1 :=
    ((continuous_const.sub hcont).div_const k).intervalIntegrable 0 1
  have hiid : IntervalIntegrable (fun a : ℝ => a) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hi1 hiid]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable 0 1) hi]
  rw [integral_rpow_parameter hb (by linarith)]
  norm_num [intervalIntegral.integral_const, integral_id]
  field_simp
  ring

section Matrix
variable {ι : Type*} [Fintype ι]

lemma logDefect_posSemidef {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hpos : ∀ i j, 0 < A i j) (hlt : ∀ i j, A i j < 1) :
    (Matrix.of (fun i j => (A i j)⁻¹ - 1 / 2 + (Real.log (1 - A i j))⁻¹)).PosSemidef := by
  have hh := integral_posSemidef
    (F := fun a => Matrix.of (fun i j => (1 - (1 - A i j) ^ a) / A i j - a))
    (fun a ha => defect_posSemidef hA hpos hlt ha.1 ha.2)
    (fun i j => (((continuous_const.sub
      (Real.continuous_const_rpow (sub_pos.mpr (hlt i j)).ne')).div_const
        (A i j)).sub continuous_id).intervalIntegrable 0 1)
  simpa only [Matrix.of_apply, integral_defect (hpos _ _) (hlt _ _)] using hh

end Matrix


lemma dilation_pos (n : ℕ) : 0 < dilation n := by
  have hn : 1 < (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hn)

lemma dilation_lt_one (n : ℕ) : dilation n < 1 := by
  have hn : 0 < ((n : ℝ) + 2)⁻¹ := by positivity
  dsimp [dilation]
  linarith

lemma dilation_tendsto : Tendsto dilation atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  unfold dilation
  simpa only [sub_zero] using (tendsto_const_nhds.sub ht.inv_tendsto_atTop :
    Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 (1 - 0)))

lemma logDefect_tendsto {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun n => (dilation n * a)⁻¹ - 1 / 2 +
        (Real.log (1 - dilation n * a))⁻¹) atTop
      (𝓝 (a⁻¹ - 1 / 2 + (Real.log (1 - a))⁻¹)) := by
  have ht : Tendsto (fun n => dilation n * a) atTop (𝓝 a) :=
    by simpa using dilation_tendsto.mul_const a
  apply (ht.inv₀ ha.ne').sub_const (1 / 2) |>.add
  have ht' : Tendsto (fun n => 1 - dilation n * a) atTop (𝓝 (1 - a)) :=
    tendsto_const_nhds.sub ht
  by_cases he : a = 1
  · subst a
    simpa only [Function.comp_def, mul_one, sub_self, Real.log_zero, _root_.inv_zero] using
      invLog_continuousAt_zero.tendsto.comp (by simpa using ht')
  · have hb : 0 < 1 - a := sub_pos.mpr (lt_of_le_of_ne ha1 he)
    have hl : Real.log (1 - a) ≠ 0 := ne_of_lt (Real.log_neg hb (by linarith))
    exact (Real.continuousAt_log hb.ne').tendsto.comp ht' |>.inv₀ hl

lemma logDefect_posSemidef_le {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hpos : ∀ i j, 0 < A i j) (hle : ∀ i j, A i j ≤ 1) :
    (Matrix.of (fun i j => (A i j)⁻¹ - 1 / 2 + (Real.log (1 - A i j))⁻¹)).PosSemidef := by
  apply posSemidef_of_entrywise_tendsto
    (A := fun n => Matrix.of (fun i j => (dilation n * A i j)⁻¹ - 1 / 2 +
      (Real.log (1 - dilation n * A i j))⁻¹))
  · intro n
    exact logDefect_posSemidef (hA.smul (dilation_pos n).le)
      (fun i j => mul_pos (dilation_pos n) (hpos i j))
      (fun i j => lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (hle i j) (dilation_pos n).le)
      (by simpa using dilation_lt_one n))
  · intro i j
    exact logDefect_tendsto (hpos i j) (hle i j)

end StrictHotSpots.ScalarKernel





open Matrix Filter _root_.Complex
open scoped Topology ComplexOrder ENNReal
namespace StrictHotSpots.DiskKernel

lemma h_pos {x y : Disk} (hxy : x ≠ y) : 0 < h x y := by
  apply div_pos _ (mul_pos (disk_weight_pos x) (disk_weight_pos y))
  exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Subtype.coe_ne_coe.mpr hxy)))

lemma complex_posSemidef_of_entrywise_tendsto {ι : Type*} [Fintype ι]
    {A : ℕ → Matrix ι ι ℂ} {B : Matrix ι ι ℂ}
    (hA : ∀ n, (A n).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have hl := (hlim j i).star
    exact tendsto_nhds_unique (hl.congr fun n => (hA n).isHermitian.apply i j) (hlim i j)
  · intro v
    have hq : Tendsto (fun n => star v ⬝ᵥ A n *ᵥ v) atTop (𝓝 (star v ⬝ᵥ B *ᵥ v)) := by
      unfold dotProduct Matrix.mulVec
      exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hlim i j).mul tendsto_const_nhds))
    exact ge_of_tendsto hq (Filter.Eventually.of_forall fun n =>
      (hA n).dotProduct_mulVec_nonneg v)


lemma szego_posSemidef {ι : Type*} [Fintype ι] (x : ι → Disk) :
    (Matrix.of (fun i j => (1 - (x i : ℂ) * star (x j : ℂ))⁻¹)).PosSemidef := by
  let A (n : ℕ) : Matrix ι ι ℂ :=
    Matrix.vecMulVec (fun i => (x i : ℂ) ^ n) (star (fun j => (x j : ℂ) ^ n))
  apply complex_posSemidef_of_entrywise_tendsto
    (A := fun n => ∑ m ∈ Finset.range n, A m)
  · intro n
    exact Matrix.posSemidef_sum _ (fun m _ => Matrix.posSemidef_vecMulVec_self_star _)
  · intro i j
    have hn : ‖(x i : ℂ) * star (x j : ℂ)‖ < 1 := by
      rw [norm_mul, norm_star]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (x j).property.le (norm_nonneg _))
        (by simpa using (x i).property)
    have hs := (hasSum_geometric_of_norm_lt_one hn).tendsto_sum_nat
    simpa [A, Matrix.sum_apply, Matrix.vecMulVec, mul_pow] using hs

lemma realPart_posSemidef {ι : Type*} [Fintype ι] {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) : (Matrix.of (fun i j => (A i j).re)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    have hh := congrArg Complex.re (hA.isHermitian.apply i j)
    simpa using hh
  · intro v
    have hh := (Complex.nonneg_iff.mp
      (hA.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)))).1
    simpa [dotProduct, Matrix.mulVec, map_sum, Complex.mul_re] using hh

lemma disk_cross_identity (x y : ℂ) :
    ‖1 - x * star y‖ ^ 2 = (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) + ‖x - y‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma normSzego_posSemidef {ι : Type*} [Fintype ι] (x : ι → Disk) :
    (Matrix.of (fun i j => (‖1 - (x i : ℂ) * star (x j : ℂ)‖ ^ 2)⁻¹)).PosSemidef := by
  have hh := realPart_posSemidef ((szego_posSemidef x).hadamard
    (szego_posSemidef x).transpose)
  convert hh using 1
  ext i j
  change _ = (((1 - (x i : ℂ) * star (x j : ℂ))⁻¹) *
    (1 - (x j : ℂ) * star (x i : ℂ))⁻¹).re
  rw [show 1 - (x j : ℂ) * star (x i : ℂ) =
    star (1 - (x i : ℂ) * star (x j : ℂ)) by simp [mul_comm]]
  rw [← star_inv₀, Complex.star_def, Complex.mul_conj]
  simp only [Matrix.of_apply, Complex.ofReal_re, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]

lemma k_identity (x y : Disk) :
    (1 + h x y)⁻¹ = (1 - ‖(x : ℂ)‖ ^ 2) *
      (‖1 - (x : ℂ) * star (y : ℂ)‖ ^ 2)⁻¹ * (1 - ‖(y : ℂ)‖ ^ 2) := by
  rw [disk_cross_identity]
  unfold h
  have hx := disk_weight_pos x
  have hy := disk_weight_pos y
  have hn := sq_nonneg ‖(x : ℂ) - y‖
  field_simp

lemma k_posSemidef {ι : Type*} [Fintype ι] (x : ι → Disk) :
    (Matrix.of (fun i j => (1 + h (x i) (x j))⁻¹)).PosSemidef := by
  classical
  have hh := (normSzego_posSemidef x).mul_mul_conjTranspose_same
    (Matrix.diagonal (fun i => (1 - ‖(x i : ℂ)‖ ^ 2)))
  convert hh using 1
  ext i j
  simp [k_identity]

end StrictHotSpots.DiskKernel

namespace StrictHotSpots.DiskKernel

lemma f_eq_logDefect {t : ℝ} (ht : 0 ≤ t) :
    f t = ((1 + t)⁻¹)⁻¹ - 1 / 2 + (Real.log (1 - (1 + t)⁻¹))⁻¹ := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t
    norm_num [f, logMean]
  · have hh : 1 - (1 + t)⁻¹ = (1 + 1 / t)⁻¹ := by
      have : 1 + t ≠ 0 := by positivity
      field_simp
      ring
    rw [hh, Real.log_inv, inv_neg, inv_inv]
    simp only [f, logMean]
    ring

lemma f_posSemidef {ι : Type*} [Fintype ι] (x : ι → Disk) :
    (Matrix.of (fun i j => f (h (x i) (x j)))).PosSemidef := by
  have hh := ScalarKernel.logDefect_posSemidef_le (k_posSemidef x)
    (fun i j => inv_pos.mpr (by have := h_nonneg (x i) (x j); linarith))
    (fun i j => inv_le_one_of_one_le₀ (by have := h_nonneg (x i) (x j); linarith))
  simpa only [Matrix.of_apply, ← f_eq_logDefect (h_nonneg _ _)] using hh

lemma logMean_pos {t : ℝ} (ht : 0 < t) : 0 < logMean t := by
  apply inv_pos.mpr
  exact Real.log_pos (by have := one_div_pos.mpr ht; linarith)

lemma f_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  rcases eq_or_lt_of_le ht with he | hp
  · subst t; rw [f_zero]; norm_num
  · have hlo := Real.le_log_one_add_of_nonneg (one_div_nonneg.mpr ht)
    have hi : 2 * (1 / t) / (1 / t + 2) = (t + 1 / 2)⁻¹ := by
      have : 1 / t + 2 ≠ 0 := by positivity
      have : t + 1 / 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [hi] at hlo
    have hbound := (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0 < (t + 1 / 2)⁻¹) hlo)
      (by positivity : 0 < (t + 1 / 2)⁻¹)).mpr hlo
    simpa only [inv_inv, f, logMean, sub_nonneg] using hbound

end StrictHotSpots.DiskKernel

namespace StrictHotSpots.DiskKernel

lemma regularized_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x y : Disk) :
    0 < regularized ε x y := by
  apply inv_pos.mpr
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (lt_of_lt_of_le (by positivity : 0 < ε / 2) (regularized_denominator hε hε1 x y))

lemma regularized_self (ε : ℝ) (x : Disk) :
    regularized ε x x = (2 * Real.pi * ε)⁻¹ := by
  rw [regularized, h_self, f_zero]
  congr 1
  ring

lemma regularized_tendsto_offDiagonal {x y : Disk} (hxy : x ≠ y) :
    Tendsto (fun ε : ℝ => regularized ε x y) (𝓝 0) (𝓝 (green x y)) := by
  have hl := logMean_pos (h_pos hxy)
  have hh : ContinuousAt (fun ε : ℝ => regularized ε x y) 0 := by
    apply (continuousAt_const.mul (continuousAt_const.sub
      ((continuousAt_const.sub continuousAt_id).mul continuousAt_const))).inv₀
    have he : h x y + 1 / 2 - (1 - (0 : ℝ)) * f (h x y) = logMean (h x y) := by
      dsimp [f]; ring
    change 4 * Real.pi * (h x y + 1 / 2 - (1 - (0 : ℝ)) * f (h x y)) ≠ 0
    rw [he]
    positivity
  convert hh.tendsto using 1
  congr 1
  dsimp [regularized, f, logMean, green]
  rw [show h x y + 1 / 2 - (1 - (0 : ℝ)) *
      (h x y + 1 / 2 - (Real.log (1 + 1 / h x y))⁻¹) =
        (Real.log (1 + 1 / h x y))⁻¹ by ring]
  simp only [_root_.mul_inv_rev, inv_inv]
  ring

end StrictHotSpots.DiskKernel




namespace ReciprocalKernel
open Matrix
variable {ι : Type*} [Fintype ι]

lemma onePositiveSquare_smul {A : Matrix ι ι ℝ} (hA : OnePositiveSquare A)
    {a : ℝ} (ha : 0 < a) : OnePositiveSquare (a • A) := by
  have he (x y : ι → ℝ) : pairing (a • A) x y = a * pairing A x y := by
    simp [pairing, Matrix.smul_mulVec, dotProduct_smul]
  refine ⟨?_, ?_⟩
  · ext i j
    simpa only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] using
      congrArg (a * ·) (hA.1.apply i j)
  · intro x y hx hxy
    rw [he] at hx hxy ⊢
    exact mul_nonpos_of_nonneg_of_nonpos ha.le
      (hA.2 x y ((mul_pos_iff_of_pos_left ha).mp hx)
        ((mul_eq_zero.mp hxy).resolve_left ha.ne'))

end ReciprocalKernel

namespace StrictHotSpots.DiskKernel
open ReciprocalKernel

lemma lorentz_identity (x y : Disk) :
    (1 - ‖(x : ℂ)‖ ^ 2) * (h x y + 1 / 2) * (1 - ‖(y : ℂ)‖ ^ 2) =
      (1 / 2) * (1 + ‖(x : ℂ)‖ ^ 2) * (1 + ‖(y : ℂ)‖ ^ 2) -
        2 * ((x : ℂ) * star (y : ℂ)).re := by
  have hx := (disk_weight_pos x).ne'
  have hy := (disk_weight_pos y).ne'
  dsimp [h]
  field_simp
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma regularized_reciprocal_onePositiveSquare {ι : Type*} [Fintype ι]
    (x : ι → Disk) {ε : ℝ} (hε1 : ε ≤ 1) :
    OnePositiveSquare (Matrix.of (fun i j => (regularized ε (x i) (x j))⁻¹)) := by
  classical
  let w : ι → ℝ := fun i => 1 - ‖(x i : ℂ)‖ ^ 2
  let v : ι → ℝ := fun i => Real.sqrt (1 / 2) * (1 + ‖(x i : ℂ)‖ ^ 2)
  let G : Matrix ι ι ℝ := Matrix.of fun i j => ((x i : ℂ) * star (x j : ℂ)).re
  let F : Matrix ι ι ℝ := Matrix.of fun i j => f (h (x i) (x j))
  have hG : G.PosSemidef := realPart_posSemidef
    (Matrix.posSemidef_vecMulVec_self_star (fun i => (x i : ℂ)))
  have hF : (Matrix.diagonal w * F * (Matrix.diagonal w).conjTranspose).PosSemidef :=
    (f_posSemidef x).mul_mul_conjTranspose_same _
  have hU := (hG.smul (by norm_num : 0 ≤ (2 : ℝ))).add (hF.smul (sub_nonneg.mpr hε1))
  have hP := onePositiveSquare_rankOne_sub_psd v hU
  have hsqrt : Real.sqrt (1 / 2) * Real.sqrt (1 / 2) = (1 / 2 : ℝ) :=
    Real.mul_self_sqrt (by norm_num)
  have hn : Matrix.vecMulVec v v - ((2 : ℝ) • G + (1 - ε) •
      (Matrix.diagonal w * F * (Matrix.diagonal w).conjTranspose)) =
      Matrix.of (fun i j => w i *
        (h (x i) (x j) + 1 / 2 - (1 - ε) * f (h (x i) (x j))) * w j) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_conjTranspose,
      star_trivial, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    dsimp [v, G, F]
    have hv : Real.sqrt (1 / 2) * (1 + ‖(x i : ℂ)‖ ^ 2) *
        (Real.sqrt (1 / 2) * (1 + ‖(x j : ℂ)‖ ^ 2)) =
        (1 / 2) * (1 + ‖(x i : ℂ)‖ ^ 2) * (1 + ‖(x j : ℂ)‖ ^ 2) := by
      calc
        _ = (Real.sqrt (1 / 2) * Real.sqrt (1 / 2)) *
            (1 + ‖(x i : ℂ)‖ ^ 2) * (1 + ‖(x j : ℂ)‖ ^ 2) := by ring
        _ = _ := by rw [hsqrt]
    rw [hv]
    have hh := lorentz_identity (x i) (x j)
    dsimp [w]
    simp only [starRingEnd_apply]
    rw [sub_add_eq_sub_sub, ← hh]
    ring
  rw [hn] at hP
  have hres := onePositiveSquare_smul (onePositiveSquare_scale hP (fun i => (w i)⁻¹))
    (mul_pos (by norm_num : 0 < (4 : ℝ)) Real.pi_pos)
  convert hres using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, regularized, inv_inv]
  have hi := (disk_weight_pos (x i)).ne'
  have hj := (disk_weight_pos (x j)).ne'
  dsimp [w]
  field_simp

end StrictHotSpots.DiskKernel

namespace StrictHotSpots.DiskKernel

lemma regularized_zero (x y : Disk) : regularized 0 x y = green x y := by
  dsimp [regularized, green, f, logMean]
  rw [show h x y + 1 / 2 - (1 - (0 : ℝ)) *
      (h x y + 1 / 2 - (Real.log (1 + 1 / h x y))⁻¹) =
        (Real.log (1 + 1 / h x y))⁻¹ by ring]
  simp only [_root_.mul_inv_rev, inv_inv]
  ring

lemma regularized_le_green {ε : ℝ} (hε : 0 ≤ ε) {x y : Disk} (hxy : x ≠ y) :
    regularized ε x y ≤ green x y := by
  rw [← regularized_zero]
  apply inv_anti₀
  · have hh := logMean_pos (h_pos hxy)
    have he : h x y + 1 / 2 - (1 - (0 : ℝ)) * f (h x y) = logMean (h x y) := by
      dsimp [f]; ring
    rw [he]
    positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4 * Real.pi)
    nlinarith [mul_nonneg hε (f_nonneg (h_nonneg x y))]

lemma regularized_tendsto_diagonal (x : Disk) :
    Tendsto (fun ε : ℝ => regularized ε x x) (𝓝[>] 0) atTop := by
  simp only [regularized_self]
  have hh := tendsto_inv_nhdsGT_zero.const_mul_atTop
    (by positivity : 0 < (2 * Real.pi)⁻¹)
  simpa only [_root_.mul_inv_rev, mul_comm] using hh


end StrictHotSpots.DiskKernel
end DiskFiniteLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Sobolev
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace _root_.OAI.StrictHotSpots.PlaneGreen.diskFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer



open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots


lemma existsUnique_of_coercive {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, B u v = ℓ v := by
  let e := hB.continuousLinearEquivOfBilin
  let y := (InnerProductSpace.toDual ℝ V).symm ℓ
  refine ⟨e.symm y, ?_, ?_⟩
  · intro v
    calc
      B (e.symm y) v = inner ℝ (e (e.symm y)) v :=
        (hB.continuousLinearEquivOfBilin_apply _ _).symm
      _ = ℓ v := by simp [y, InnerProductSpace.toDual_symm_apply]
  · intro u hu
    apply e.injective
    rw [e.apply_symm_apply]
    apply ext_inner_right ℝ
    intro v
    calc
      inner ℝ (e u) v = B u v := hB.continuousLinearEquivOfBilin_apply _ _
      _ = ℓ v := hu v
      _ = inner ℝ y v := InnerProductSpace.toDual_symm_apply.symm




namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)



lemma existsUnique_energy_solution (hb : Bornology.IsBounded Ω)
    (ℓ : H10 hΩ →L[ℝ] ℝ) :
    ∃! u : H10 hΩ, ∀ v : H10 hΩ, energy hΩ u v = ℓ v := by
  exact @existsUnique_of_coercive (H10 hΩ) (H10.normedAddCommGroup hΩ)
    (H10.innerProductSpace hΩ) (H10.completeSpace hΩ)
    (energy hΩ) (energy_coercive hΩ hb) ℓ


end H10
end StrictHotSpots




open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
namespace StrictHotSpots.DiskCutoff

lemma transition_deriv_zero {t : ℝ} (ht : t < 0 ∨ 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht with ht | ht
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds ht] with x hx
      exact Real.smoothTransition.zero_of_nonpos hx.le
    simpa using h.deriv_eq
  · have h : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_nhds ht] with x hx
      exact Real.smoothTransition.one_of_one_le hx.le
    simpa using h.deriv_eq

lemma transition_deriv_bound : ∃ L : ℝ, 0 ≤ L ∧
    ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn (deriv Real.smoothTransition) (Icc (0 : ℝ) 1) from
      (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp) |>.continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hC t ht).trans (le_max_left _ _)
  · have h : t < 0 ∨ 1 < t := by simpa only [mem_Icc, not_and_or, not_le] using ht
    rw [transition_deriv_zero h, norm_zero]
    exact le_max_right _ _

variable {E : Type*} [NormedAddCommGroup E]

lemma cutoff_nonneg (κ : ℝ) (x : E) : 0 ≤ cutoff κ x :=
  Real.smoothTransition.nonneg _

lemma cutoff_le_one (κ : ℝ) (x : E) : cutoff κ x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma cutoff_zero {κ : ℝ} {x : E} (hκ : 0 < κ) (hx : 1 - κ⁻¹ ≤ ‖x‖ ^ 2) :
    cutoff κ x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
  nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hx)]

lemma cutoff_one {κ : ℝ} {x : E} (hx : 2 ≤ κ * (1 - ‖x‖ ^ 2)) :
    cutoff κ x = 1 := Real.smoothTransition.one_of_one_le (by linarith)

lemma cutoff_tsupport {κ : ℝ} (hκ : 0 < κ) :
    tsupport (cutoff (E := E) κ) ⊆ {x | ‖x‖ ^ 2 ≤ 1 - κ⁻¹} := by
  apply closure_minimal _ (isClosed_le (continuous_norm.pow 2) continuous_const)
  intro x hx
  change ‖x‖ ^ 2 ≤ 1 - κ⁻¹
  by_contra hh
  exact hx (cutoff_zero hκ (le_of_lt (lt_of_not_ge hh)))

lemma cutoff_tsupport_disk {κ : ℝ} (hκ : 0 < κ) :
    tsupport (cutoff (E := E) κ) ⊆ Metric.ball 0 1 := by
  intro x hx
  have h := cutoff_tsupport hκ hx
  change ‖x‖ ^ 2 ≤ 1 - κ⁻¹ at h
  simp only [Metric.mem_ball, dist_zero_right]
  have hi : 0 < κ⁻¹ := inv_pos.mpr hκ
  have hn := norm_nonneg x
  nlinarith

lemma cutoff_hasCompactSupport [ProperSpace E] {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (cutoff (E := E) κ) :=
  isCompact_closedBall 0 1 |>.of_isClosed_subset (isClosed_tsupport _)
    ((cutoff_tsupport_disk hκ).trans Metric.ball_subset_closedBall)

variable [InnerProductSpace ℝ E]

lemma cutoff_contDiff (κ : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) κ) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_const.sub (contDiff_id.norm_sq (𝕜 := ℝ)))).sub contDiff_const)

lemma cutoff_fderiv (κ : ℝ) (x : E) :
    fderiv ℝ (cutoff κ) x =
      (-2 * κ * deriv Real.smoothTransition (κ * (1 - ‖x‖ ^ 2) - 1)) • innerSL ℝ x := by
  have hnorm := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have ha := ((hnorm.const_sub 1).const_mul κ).sub_const 1
  have hb := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) (κ * (1 - ‖x‖ ^ 2) - 1)).hasDerivAt
  have hc := hb.comp_hasFDerivAt x ha
  change fderiv ℝ (Real.smoothTransition ∘ fun x : E => κ * (1 - ‖x‖ ^ 2) - 1) x = _
  rw [hc.fderiv]
  ext y
  simp
  ring

lemma cutoff_fderiv_zero {κ : ℝ} {x : E}
    (hx : 2 < κ * (1 - ‖x‖ ^ 2)) : fderiv ℝ (cutoff κ) x = 0 := by
  rw [cutoff_fderiv, transition_deriv_zero (Or.inr (by linarith))]
  simp

lemma cutoff_eventually_one (x : E) (hx : ‖x‖ < 1) :
    ∀ᶠ n : ℕ in atTop, cutoff ((n : ℝ) + 2) x = 1 ∧
      fderiv ℝ (cutoff ((n : ℝ) + 2)) x = 0 := by
  have hp : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 2) * (1 - ‖x‖ ^ 2)) atTop atTop :=
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop).atTop_mul_const hp
  filter_upwards [ht.eventually (eventually_gt_atTop (2 : ℝ))] with n hn
  exact ⟨cutoff_one hn.le, cutoff_fderiv_zero hn⟩

lemma boundary_vanishing_estimate [Nontrivial E] {f : E → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf : ∀ x ∈ Metric.closedBall (0 : E) 1, DifferentiableAt ℝ f x)
    (hd : ∀ x ∈ Metric.closedBall (0 : E) 1, ‖fderiv ℝ f x‖ ≤ C)
    (hz : ∀ x : E, ‖x‖ = 1 → f x = 0) {x : E} (hx : ‖x‖ ≤ 1) :
    ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2) := by
  have hpoint : ∃ y : E, ‖y‖ = 1 ∧ ‖y-x‖ = 1-‖x‖ := by
    by_cases h : x = 0
    · obtain ⟨y,hy⟩ := exists_ne (0 : E)
      exact ⟨normalize y, norm_normalize hy, by simp [h, norm_normalize hy]⟩
    · refine ⟨normalize x, norm_normalize h, ?_⟩
      calc
        ‖normalize x - x‖ = ‖(1-‖x‖) • normalize x‖ := by rw [sub_smul, one_smul, norm_smul_normalize]
        _ = 1-‖x‖ := by rw [norm_smul, norm_normalize h, mul_one, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx)]
  obtain ⟨y,hy,hdist⟩ := hpoint
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hf hd
    (convex_closedBall (0 : E) (1 : ℝ))
    (show x ∈ Metric.closedBall (0 : E) 1 by simpa using hx)
    (show y ∈ Metric.closedBall (0 : E) 1 by simp [hy])
  rw [hz y hy, zero_sub, norm_neg, hdist] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith [norm_nonneg x]

lemma cutoff_mul_contDiff {f : E → ℝ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R)) :
    ContDiff ℝ ∞ (fun x => cutoff κ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (cutoff (E := E) κ)
  · have hxd := cutoff_tsupport_disk hκ hx
    have hxR : x ∈ Metric.ball (0 : E) R := Metric.ball_subset_ball hR.le hxd
    exact (cutoff_contDiff κ).contDiffAt.mul
      ((hf x hxR).contDiffAt (Metric.isOpen_ball.mem_nhds hxR))
  · have he := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

omit [InnerProductSpace ℝ E] in
lemma cutoff_mul_hasCompactSupport [ProperSpace E] {f : E → ℝ} {κ : ℝ}
    (hκ : 0 < κ) : HasCompactSupport (fun x => cutoff κ x * f x) :=
  (cutoff_hasCompactSupport hκ).mul_right

omit [InnerProductSpace ℝ E] in
lemma cutoff_mul_norm_le {f : E → ℝ} {κ C : ℝ} {x : E} (hf : ‖f x‖ ≤ C) :
    ‖cutoff κ x * f x‖ ≤ C := by
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans hf

lemma cutoff_mul_fderiv_bound {f : E → ℝ} {κ C L : ℝ} {x : E}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hx : ‖x‖ ≤ 1)
    (hf : DifferentiableAt ℝ f x) (hd : ‖fderiv ℝ f x‖ ≤ C)
    (hz : ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2))
    (ht : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ L) :
    ‖fderiv ℝ (fun x => cutoff κ x * f x) x‖ ≤ C + 4 * C * L := by
  rw [fderiv_fun_mul ((cutoff_contDiff κ).differentiable (by simp) x) hf]
  apply (norm_add_le _ _).trans
  have h1 : ‖cutoff κ x • fderiv ℝ f x‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg _ _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _ _)).trans hd
  have h2 : ‖f x • fderiv ℝ (cutoff κ) x‖ ≤ 4 * C * L := by
    by_cases hh : 2 < κ * (1 - ‖x‖ ^ 2)
    · rw [cutoff_fderiv_zero hh, smul_zero, norm_zero]
      positivity
    · have hh' : κ * (1 - ‖x‖ ^ 2) ≤ 2 := le_of_not_gt hh
      rw [norm_smul, cutoff_fderiv, norm_smul]
      simp only [norm_mul, norm_neg, Real.norm_of_nonneg hκ.le,
        innerSL_apply_norm]
      rw [show ‖(2 : ℝ)‖ = 2 by norm_num]
      have hn : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      calc
        _ ≤ (C * (1 - ‖x‖ ^ 2)) * (2 * κ * L * 1) := by
          apply mul_le_mul hz _ (by positivity) (mul_nonneg hC hn)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (ht _) (by positivity)) hx
            (norm_nonneg _) (by positivity)
        _ = 2 * C * L * (κ * (1 - ‖x‖ ^ 2)) := by ring
        _ ≤ 4 * C * L := by nlinarith [mul_le_mul_of_nonneg_left hh' (show 0 ≤ 2 * C * L by positivity)]
  exact add_le_add h1 h2

end StrictHotSpots.DiskCutoff

namespace StrictHotSpots

namespace DiskH10
open DiskCutoff

lemma norm_gradient_eq (f : Plane → ℝ) (x : Plane) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

lemma smooth_zero_boundary_bounds {f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (hz : ∀ x : Plane, ‖x‖ = 1 → f x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x ∈ disk, ‖f x‖ ≤ C) ∧
      (∀ x ∈ disk, ‖fderiv ℝ f x‖ ≤ C) ∧
      (∀ x ∈ disk, ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2)) := by
  have hs : Metric.closedBall (0 : Plane) 1 ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hR
  have hdc := hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Plane) 1).exists_bound_of_continuousOn
    (hdc.mono hs)
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hd : ∀ x ∈ Metric.closedBall (0 : Plane) 1, ‖fderiv ℝ f x‖ ≤ C :=
    fun x hx => (hB x hx).trans (le_max_left _ _)
  have hdiff : ∀ x ∈ Metric.closedBall (0 : Plane) 1, DifferentiableAt ℝ f x :=
    fun x hx => ((hf x (hs hx)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hx))).differentiableAt (by simp)
  have hv : ∀ x ∈ disk, ‖f x‖ ≤ C * (1 - ‖x‖ ^ 2) := by
    intro x hx
    exact boundary_vanishing_estimate hC hdiff hd hz (by simpa [disk] using (Metric.ball_subset_closedBall hx))
  refine ⟨C,hC,?_,fun x hx => hd x (Metric.ball_subset_closedBall hx),hv⟩
  intro x hx
  exact (hv x hx).trans (by nlinarith [sq_nonneg ‖x‖, mul_nonneg hC (sq_nonneg ‖x‖)])



lemma smooth_zero_boundary_memH10 {f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (hz : ∀ x : Plane, ‖x‖ = 1 → f x = 0) :
    (smooth_memH1 hR hf).toH1 ∈ h10Submodule (Ω := disk) Metric.isOpen_ball := by
  let hΩ : IsOpen disk := Metric.isOpen_ball
  let h := smooth_memH1 hR hf
  let : IsFiniteMeasure (volume.restrict disk) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  obtain ⟨C,hC,hv,hd,hzC⟩ := smooth_zero_boundary_bounds hR hf hz
  obtain ⟨L,hL,ht⟩ := transition_deriv_bound
  let ψ : ℕ → Plane → ℝ := fun n x => cutoff ((n : ℝ) + 2) x * f x
  have hκ (n : ℕ) : 0 < (n : ℝ) + 2 := by positivity
  have hψ (n : ℕ) : ContDiff ℝ ∞ (ψ n) := cutoff_mul_contDiff (hκ n) hR hf
  have hc (n : ℕ) : HasCompactSupport (ψ n) := cutoff_mul_hasCompactSupport (hκ n)
  have hs (n : ℕ) : tsupport (ψ n) ⊆ disk :=
    tsupport_mul_subset_left.trans (cutoff_tsupport_disk (hκ n))
  let test : ℕ → smoothTestSpace disk := fun n => ⟨ψ n, hψ n, hc n, hs n⟩
  have hdiff (x : Plane) (hx : x ∈ disk) : DifferentiableAt ℝ f x := by
    have hxR : x ∈ Metric.ball (0 : Plane) R := Metric.ball_subset_ball hR.le hx
    exact ((hf x hxR).contDiffAt (Metric.isOpen_ball.mem_nhds hxR)).differentiableAt (by simp)
  have hval : Tendsto (fun n => H1.value (smoothTestToH1 hΩ (test n))) atTop
      (𝓝 (H1.value h.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => test_memLp (hψ n) (hc n)) h.1 (memLp_const C)
    · apply Eventually.of_forall
      intro n
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      exact cutoff_mul_norm_le (hv x hx)
    · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      have he : ∀ᶠ n : ℕ in atTop, ψ n x = f x := by
        filter_upwards [cutoff_eventually_one x (by simpa [disk] using hx)] with n hn
        simp only [ψ, hn.1, one_mul]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
  have hgrad : Tendsto (fun n => H1.grad (smoothTestToH1 hΩ (test n))) atTop
      (𝓝 (H1.grad h.toH1)) := by
    apply L2VectorLimits.tendsto_toLp_of_dominated
      (fun n => test_gradient_memLp (hψ n) (hc n)) h.2.1 (memLp_const (C + 4 * C * L))
    · apply Eventually.of_forall
      intro n
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      rw [norm_gradient_eq]
      exact cutoff_mul_fderiv_bound (hκ n) hC hL
        (by simpa [disk] using (Metric.ball_subset_closedBall hx))
        (hdiff x hx) (hd x hx) (hzC x hx) ht
    · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      have he : ∀ᶠ n : ℕ in atTop, gradient (ψ n) x = gradient f x := by
        filter_upwards [cutoff_eventually_one x (by simpa [disk] using hx)] with n hn
        unfold gradient ψ
        rw [fderiv_fun_mul ((cutoff_contDiff _).differentiable (by simp) x) (hdiff x hx)]
        simp only [hn.1, hn.2, one_smul, smul_zero, add_zero]
      exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)
  change h.toH1 ∈ closure ((smoothTestToH1 hΩ).range : Set (H1 disk))
  exact mem_closure_of_tendsto (H1.tendsto_of_value_grad hval hgrad)
    (Eventually.of_forall fun n => ⟨test n, rfl⟩)

end DiskH10
end StrictHotSpots

open scoped Laplacian
namespace StrictHotSpots

lemma integral_inner_gradient_test {Ω : Set Plane} {f φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, inner ℝ (gradient f x) (gradient φ x)) =
      -(∫ x in Ω, Δ f x * φ x) := by
  let b := stdOrthonormalBasis ℝ Plane
  have hd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (b i)) Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hdd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i)) Ω :=
    ((hd i).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have he (x : Plane) : inner ℝ (gradient f x) (gradient φ x) =
      ∑ i, fderiv ℝ f x (b i) * fderiv ℝ φ x (b i) := by
    rw [← b.sum_inner_mul_inner (gradient f x) (gradient φ x)]
    simp only [inner_gradient_left, inner_gradient_right, starRingEnd_apply, star_trivial]
  have hl (x : Plane) (hx : x ∈ Ω) : Δ f x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    apply Finset.sum_congr rfl
    intro i _
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
    rw [fderiv_clm_apply
      ((((hf x hx).contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
      (differentiableAt_const _)]
    simp
  have hi (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ f x (b i) * fderiv ℝ φ x (b i)) (volume.restrict Ω) := by
    apply Integrable.restrict
    exact integrable_mul_test hΩ (hd i).continuousOn
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (b i)) ((tsupport_fderiv_apply_subset ℝ (b i)).trans hs)
  have hj (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) * φ x)
      (volume.restrict Ω) :=
    (integrable_mul_test hΩ (hdd i).continuousOn hφ.continuous hc hs).restrict
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_mul_test_fderiv hΩ (hd _) hφ hc hs]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum _ (fun i _ => hj i)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [hl x hx, Finset.sum_mul]

lemma inner_toLp_toLp {X F : Type*} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f g : X → F}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

lemma smoothTest_value {Ω : Set Plane} (hΩ : IsOpen Ω) (φ : smoothTestSpace Ω) :
    H1.value (smoothTestToH1 hΩ φ) =
      (test_memLp (Ω := Ω) φ.property.1 φ.property.2.1).toLp (φ : Plane → ℝ) := by
  rw [show smoothTestToH1 hΩ φ =
    (HasH1Gradient.test hΩ φ.property.1 φ.property.2.1).toH1 from rfl, H1.value_toH1]

lemma smoothTest_grad {Ω : Set Plane} (hΩ : IsOpen Ω) (φ : smoothTestSpace Ω) :
    H1.grad (smoothTestToH1 hΩ φ) =
      (test_gradient_memLp (Ω := Ω) φ.property.1 φ.property.2.1).toLp (gradient (φ : Plane → ℝ)) := by
  rw [show smoothTestToH1 hΩ φ =
    (HasH1Gradient.test hΩ φ.property.1 φ.property.2.1).toH1 from rfl, H1.grad_toH1]

lemma smooth_weak_poisson {Ω : Set Plane} {u f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (huH1 : HasH1Gradient Ω u (gradient u))
    (hf : MemLp f 2 (volume.restrict Ω))
    (hp : ∀ x ∈ Ω, Δ u x = -f x) (v : H10 hΩ) :
    inner ℝ (H1.grad huH1.toH1) (H10.grad hΩ v) =
      inner ℝ (hf.toLp f) (H10.value hΩ v) := by
  let S : Set (H1 Ω) := {w | inner ℝ (H1.grad huH1.toH1) (H1.grad w) =
    inner ℝ (hf.toLp f) (H1.value w)}
  have hS : IsClosed S := isClosed_eq (continuous_const.inner H1.grad.continuous)
    (continuous_const.inner H1.value.continuous)
  have hi : ((smoothTestToH1 hΩ).range : Set (H1 Ω)) ⊆ S := by
    rintro w ⟨φ,rfl⟩
    change inner ℝ (H1.grad huH1.toH1) (H1.grad (smoothTestToH1 hΩ φ)) =
      inner ℝ (hf.toLp f) (H1.value (smoothTestToH1 hΩ φ))
    rw [H1.grad_toH1, smoothTest_grad, smoothTest_value, inner_toLp_toLp, inner_toLp_toLp,
      integral_inner_gradient_test hΩ hu φ.property.1 φ.property.2.1 φ.property.2.2]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [hp x hx]
    ring
  exact (closure_minimal hi hS) v.property

end StrictHotSpots







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Green
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace _root_.OAI.StrictHotSpots.PlaneGreen.diskFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian

open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace

namespace StrictHotSpots.GreenFundamental

lemma denominator_pos {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    0 < ‖z‖ ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hε)

lemma logRegularized_contDiff {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ∞ (logRegularized ε) := by
  exact ((contDiff_id.norm_sq (𝕜 := ℂ)).add contDiff_const).log
    (fun z => (denominator_pos hε z).ne')

lemma logRegularized_fderiv {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    fderiv ℝ (logRegularized ε) z =
      (‖z‖ ^ 2 + ε ^ 2)⁻¹ • (2 • innerSL ℝ z) := by
  exact (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).log
    (denominator_pos hε z).ne').fderiv

lemma logRegularized_second {ε : ℝ} (hε : ε ≠ 0) (z a b : ℂ) :
    fderiv ℝ (fderiv ℝ (logRegularized ε)) z a b =
      2 * (‖z‖ ^ 2 + ε ^ 2)⁻¹ * ⟪a, b⟫_ℝ -
        4 * (‖z‖ ^ 2 + ε ^ 2)⁻¹ ^ 2 * ⟪z, a⟫_ℝ * ⟪z, b⟫_ℝ := by
  have hf : fderiv ℝ (logRegularized ε) = fun z : ℂ =>
      (‖z‖ ^ 2 + ε ^ 2)⁻¹ • (2 • innerSL ℝ z) :=
    funext (logRegularized_fderiv hε)
  rw [hf]
  have hd := (hasDerivAt_inv (denominator_pos hε z).ne').comp_hasFDerivAt z
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2))
  have hi : HasFDerivAt (fun z : ℂ => 2 • innerSL ℝ z) (2 • innerSL ℝ (E := ℂ)) z := by
    exact (2 • innerSL ℝ (E := ℂ)).hasFDerivAt
  calc
    _ = _ := congrArg (fun L : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) => L a b) (hd.smul hi).fderiv
    _ = _ := by
      simp only [add_apply, smul_apply, two_smul, ContinuousLinearMap.smulRight_apply,
        Function.comp_def, neg_mul, smul_eq_mul, innerSL_apply_apply]
      erw [innerSL_apply_apply]
      simp only [← inv_pow]
      ring

lemma logRegularized_laplacian {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    Δ (logRegularized ε) z = 4 * ε ^ 2 / (‖z‖ ^ 2 + ε ^ 2) ^ 2 := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, logRegularized_second hε]
  have hz : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq z
  simp only [Complex.inner]
  simp at *
  field_simp
  nlinarith

lemma radial_primitive_hasDerivAt (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(2 * Real.pi)⁻¹ * (1 + r ^ 2)⁻¹)
      (r / (Real.pi * (1 + r ^ 2)^2)) r := by
  have hd := ((hasDerivAt_id r).pow 2).const_add 1
  have h := (hasDerivAt_inv (show 1 + r ^ 2 ≠ 0 by positivity)).comp r hd
  have hh := h.const_mul (-(2 * Real.pi)⁻¹)
  simp only [Function.comp_def, id_eq, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, mul_one] at hh
  convert! hh using 1
  field_simp

lemma radial_primitive_tendsto :
    Tendsto (fun r : ℝ => -(2 * Real.pi)⁻¹ * (1 + r ^ 2)⁻¹) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_left atTop (1 : ℝ) (tendsto_pow_atTop two_ne_zero))).const_mul
      (-(2 * Real.pi)⁻¹)

lemma integral_radial :
    ∫ r in Ioi (0 : ℝ), r / (Real.pi * (1 + r ^ 2)^2) = (2 * Real.pi)⁻¹ := by
  simpa using integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (fun r _ => radial_primitive_hasDerivAt r)
    (fun r hr => div_nonneg hr.le (by positivity)) radial_primitive_tendsto

lemma integral_peak : ∫ z : ℂ, peak z = 1 := by
  rw [← Complex.integral_comp_polarCoord_symm]
  have heq : (fun p : ℝ × ℝ => p.1 • peak (Complex.polarCoord.symm p)) =
      (fun p : ℝ × ℝ => (p.1 / (Real.pi * (1 + p.1 ^ 2)^2)) * (1 : ℝ)) := by
    funext p
    simp [peak, sq_abs, div_eq_mul_inv]
  rw [heq]
  change (∫ p in (Ioi (0 : ℝ)) ×ˢ Ioo (-Real.pi) Real.pi,
    (p.1 / (Real.pi * (1 + p.1 ^ 2)^2)) * (1 : ℝ)) = 1
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setIntegral_prod_mul (fun r : ℝ => r / (Real.pi * (1 + r ^ 2)^2))
      (fun _ : ℝ => (1 : ℝ)), integral_radial]
  simp [Real.pi_pos.le]
  field_simp
  ring

lemma peak_nonneg (z : ℂ) : 0 ≤ peak z := by
  unfold peak
  positivity

lemma peak_decay : Tendsto (fun z : ℂ => ‖z‖ ^ Module.finrank ℝ ℂ * peak z)
    (cobounded ℂ) (𝓝 0) := by
  have h : Tendsto (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹) (cobounded ℂ) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ (1 : ℝ)
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop))
  have hh := (h.sub (h.pow 2)).const_mul Real.pi⁻¹
  simp only [zero_pow two_ne_zero, sub_zero, mul_zero] at hh
  convert! hh using 1
  funext z
  simp only [Complex.finrank_real_complex, peak]
  field_simp
  ring

lemma tendsto_peak_mul {φ : ℂ → ℝ} (hφ : Integrable φ) (hc : ContinuousAt φ 0) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, (c ^ 2 * peak (c • z)) * φ z)
      atTop (𝓝 (φ 0)) := by
  simpa only [Complex.finrank_real_complex, smul_eq_mul] using
    tendsto_integral_comp_smul_smul_of_integrable peak_nonneg integral_peak peak_decay hφ hc

lemma logRegularized_laplacian_scale {c : ℝ} (hc : c ≠ 0) (z : ℂ) :
    Δ (logRegularized c⁻¹) z = (4 * Real.pi) * (c ^ 2 * peak (c • z)) := by
  rw [logRegularized_laplacian (inv_ne_zero hc)]
  simp only [peak, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hd : ‖z‖ ^ 2 + c⁻¹ ^ 2 ≠ 0 := (denominator_pos (inv_ne_zero hc) z).ne'
  have hd' : 1 + c ^ 2 * ‖z‖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

lemma tendsto_logRegularized_laplacian_mul {φ : ℂ → ℝ}
    (hφ : Integrable φ) (hc : ContinuousAt φ 0) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, Δ (logRegularized c⁻¹) z * φ z)
      atTop (𝓝 ((4 * Real.pi) * φ 0)) := by
  apply ((tendsto_peak_mul hφ hc).const_mul (4 * Real.pi)).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  simp_rw [logRegularized_laplacian_scale hc.ne', mul_assoc]
  simpa only [mul_assoc] using (integral_const_mul (μ := (volume : Measure ℂ)) (4 * Real.pi)
    (fun z : ℂ => c ^ 2 * (peak (c • z) * φ z))).symm

lemma direction_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (e : ℂ) :
    ContDiff ℝ ∞ (direction f e) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma direction_compact {φ : ℂ → ℝ} (hc : HasCompactSupport φ) (e : ℂ) :
    HasCompactSupport (direction φ e) := hc.fderiv_apply ℝ e

lemma second_direction {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (e x : ℂ) :
    direction (direction f e) e x = fderiv ℝ (fderiv ℝ f) x e e := by
  unfold direction
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const _)]
  simp

lemma laplacian_direction {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    Δ f = fun x => direction (direction f 1) 1 x +
      direction (direction f Complex.I) Complex.I x := by
  funext x
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, second_direction hf]

lemma integral_direction_by_parts {f φ : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : ℂ) :
    ∫ x, f x * direction φ e x = -(∫ x, direction f e x * φ x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((direction_smooth hf e).continuous.mul hφ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  · exact (hf.continuous.mul (direction_smooth hφ e).continuous).integrable_of_hasCompactSupport
      (direction_compact hc e).mul_left
  · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · intro x _
    exact hf.differentiable (by simp) x
  · intro x _
    exact hφ.differentiable (by simp) x

lemma integral_second_direction {f φ : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : ℂ) :
    ∫ x, f x * direction (direction φ e) e x =
      ∫ x, direction (direction f e) e x * φ x := by
  rw [integral_direction_by_parts hf (direction_smooth hφ e) (direction_compact hc e),
    integral_direction_by_parts (direction_smooth hf e) hφ hc, neg_neg]

lemma integral_laplacian_by_parts {f φ : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ x, f x * Δ φ x = ∫ x, Δ f x * φ x := by
  have hi (e : ℂ) : Integrable (fun x => f x * direction (direction φ e) e x) :=
    (hf.continuous.mul (direction_smooth (direction_smooth hφ e) e).continuous).integrable_of_hasCompactSupport (direction_compact (direction_compact hc e) e).mul_left
  have hi' (e : ℂ) : Integrable (fun x => direction (direction f e) e x * φ x) :=
    ((direction_smooth (direction_smooth hf e) e).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  simp_rw [laplacian_direction hf, laplacian_direction hφ, mul_add, add_mul]
  rw [integral_add (hi 1) (hi Complex.I), integral_add (hi' 1) (hi' Complex.I),
    integral_second_direction hf hφ hc, integral_second_direction hf hφ hc]

lemma tendsto_logRegularized_test {φ : ℂ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, logRegularized c⁻¹ z * Δ φ z)
      atTop (𝓝 ((4 * Real.pi) * φ 0)) := by
  apply (tendsto_logRegularized_laplacian_mul
    (hφ.continuous.integrable_of_hasCompactSupport hc) hφ.continuous.continuousAt).congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc'
  exact (integral_laplacian_by_parts (logRegularized_contDiff (inv_ne_zero hc'.ne')) hφ hc).symm

lemma abs_log_bound {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + t⁻¹ := by
  have hu := Real.log_le_sub_one_of_pos ht
  have hl := Real.one_sub_inv_le_log_of_pos ht
  exact abs_le.mpr ⟨by linarith, by have := inv_pos.mpr ht; linarith⟩

lemma log_norm_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := R ^ 2 + 1) (α := 1)
    (by norm_num : 1 ≤ Module.finrank ℝ ℂ) (by norm_num : (1 : ℝ) < Module.finrank ℝ ℂ)
  · filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
    rw [Real.norm_eq_abs, Real.rpow_neg_one]
    by_cases he : z = 0
    · simp [he]
    · have hp : 0 < ‖z‖ := norm_pos_iff.mpr he
      have hr : ‖z‖ < R := by simpa using hz
      calc
        _ ≤ ‖z‖ + ‖z‖⁻¹ := abs_log_bound hp
        _ ≤ (R ^ 2 + 1) * ‖z‖⁻¹ := by
          rw [← div_eq_mul_inv]
          apply (le_div_iff₀ hp).mpr
          have he : (‖z‖ + ‖z‖⁻¹) * ‖z‖ = ‖z‖ ^ 2 + 1 := by field_simp
          rw [he]
          nlinarith
  · exact (Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable

lemma logRegularized_abs_le {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1)
    {z : ℂ} (hz : z ≠ 0) :
    |logRegularized ε z| ≤ 2 * |Real.log ‖z‖| + ‖z‖ ^ 2 + 1 := by
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hl := Real.log_le_log (sq_pos_of_pos hp) (le_add_of_nonneg_right (sq_nonneg ε))
  have hu := Real.log_le_self (show 0 ≤ ‖z‖ ^ 2 + ε ^ 2 by positivity)
  rw [Real.log_pow] at hl
  norm_num at hl
  have ha := neg_abs_le (Real.log ‖z‖)
  have hb := abs_nonneg (Real.log ‖z‖)
  unfold logRegularized
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg ‖z‖], by nlinarith⟩

lemma tendsto_logRegularized {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun c : ℝ => logRegularized c⁻¹ z) atTop (𝓝 (2 * Real.log ‖z‖)) := by
  have hp : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have ht : Tendsto (fun c : ℝ => ‖z‖ ^ 2 + (c⁻¹) ^ 2) atTop (𝓝 (‖z‖ ^ 2)) := by
    simpa using (tendsto_const_nhds (x := ‖z‖ ^ 2)).add (tendsto_inv_atTop_zero.pow 2)
  simpa [logRegularized, Real.log_pow, Function.comp_def] using (Real.continuousAt_log hp).tendsto.comp ht

lemma tendsto_integral_logRegularized {ψ : ℂ → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun c : ℝ => ∫ z : ℂ, logRegularized c⁻¹ z * ψ z)
      atTop (𝓝 (∫ z : ℂ, (2 * Real.log ‖z‖) * ψ z)) := by
  obtain ⟨R, hR, hsub⟩ := hc.isBounded.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hψ
  have hB0 : 0 ≤ B := (norm_nonneg (ψ 0)).trans (hB 0)
  let bound : ℂ → ℝ := (Metric.ball (0 : ℂ) R).indicator
    (fun z => (2 * |Real.log ‖z‖| + R ^ 2 + 1) * B)
  have hi : Integrable bound := by
    apply (integrable_indicator_iff measurableSet_ball).mpr
    exact ((((log_norm_integrableOn_ball R).abs.const_mul 2).add
      (integrableOn_const (measure_ball_lt_top.ne))).add
      (integrableOn_const (measure_ball_lt_top.ne))).mul_const B
  refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hi ?_
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc'
    exact ((logRegularized_contDiff (inv_ne_zero hc'.ne')).continuous.mul hψ).aestronglyMeasurable
  · filter_upwards [Ici_mem_atTop (1 : ℝ)] with c hc'
    change 1 ≤ c at hc'
    filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    by_cases hzr : z ∈ Metric.ball (0 : ℂ) R
    · rw [norm_mul, Real.norm_eq_abs, show bound z =
        (2 * |Real.log ‖z‖| + R ^ 2 + 1) * B from Set.indicator_of_mem hzr _]
      have hr : ‖z‖ < R := by simpa using hzr
      have hli : |logRegularized c⁻¹ z| ≤ 2 * |Real.log ‖z‖| + R ^ 2 + 1 := by
        apply (logRegularized_abs_le (inv_nonneg.mpr (by linarith))
          (inv_le_one₀ (by linarith) |>.mpr hc') hz).trans
        nlinarith [norm_nonneg z]
      exact mul_le_mul hli (hB z) (norm_nonneg _) (by positivity)
    · have hzψ : ψ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun hz' => hzr (hsub hz'))
      simp [hzψ, bound, hzr]
  · filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
    exact (tendsto_logRegularized hz).mul_const (ψ z)

lemma laplacian_smooth {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (Δ φ) := by
  rw [laplacian_direction hφ]
  exact (direction_smooth (direction_smooth hφ 1) 1).add
    (direction_smooth (direction_smooth hφ Complex.I) Complex.I)

lemma laplacian_compact {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : HasCompactSupport (Δ φ) := by
  rw [laplacian_direction hφ]
  exact (direction_compact (direction_compact hc 1) 1).add
    (direction_compact (direction_compact hc Complex.I) Complex.I)



lemma integral_log_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∫ z : ℂ, Real.log ‖z‖ * Δ φ z = (2 * Real.pi) * φ 0 := by
  have he := tendsto_nhds_unique (tendsto_logRegularized_test hφ hc)
    (tendsto_integral_logRegularized (laplacian_smooth hφ).continuous
      (laplacian_compact hφ hc))
  simp_rw [mul_assoc] at he
  rw [integral_const_mul] at he
  linarith

lemma log_norm_locallyIntegrable : LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) := by
  intro z
  refine ⟨Metric.ball (0 : ℂ) (‖z‖ + 1), Metric.isOpen_ball.mem_nhds ?_,
    log_norm_integrableOn_ball _⟩
  simp

lemma laplacian_comp_add_right (φ : ℂ → ℝ) (a : ℂ) :
    Δ (fun z => φ (z+a)) = fun z => Δ φ (z+a) := by
  funext z
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_comp_add_right]

lemma log_sub_mul_integrable {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (a : ℂ) :
    Integrable (fun z : ℂ => Real.log ‖z-a‖ * ψ z) := by
  have hi := log_norm_locallyIntegrable.integrable_smul_right_of_hasCompactSupport
    (hψ.comp (continuous_id.add continuous_const))
    (hc.comp_homeomorph (Homeomorph.addRight a))
  simpa [Function.comp_def, sub_eq_add_neg, smul_eq_mul] using
    (measurePreserving_add_right volume (-a)).integrable_comp_of_integrable hi

end StrictHotSpots.GreenFundamental

namespace StrictHotSpots.DiskFormula
open StrictHotSpots.GreenFundamental



lemma disk_cross_identity (x y : ℂ) :
    ‖1 - x * star y‖ ^ 2 = (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) + ‖x-y‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma green_eq_log {x y : ℂ} (hxy : x ≠ y) (hnum : 1 - x * star y ≠ 0) :
    green x y = (Real.log ‖1-x*star y‖ - Real.log ‖x-y‖) / (2 * Real.pi) := by
  have hd := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  have hn := pow_ne_zero 2 (norm_ne_zero_iff.mpr hnum)
  have he : 1 + (1 - ‖x‖ ^ 2) * (1 - ‖y‖ ^ 2) / ‖x-y‖ ^ 2 =
      ‖1-x*star y‖ ^ 2 / ‖x-y‖ ^ 2 := by
    rw [disk_cross_identity, add_div, div_self hd]
    ring
  rw [green, he, Real.log_div hn hd, Real.log_pow, Real.log_pow]
  ring

end StrictHotSpots.DiskFormula

open scoped Convolution
namespace StrictHotSpots.GreenPotential
open StrictHotSpots.GreenFundamental

lemma direction_convolution {f g : ℂ → ℝ}
    (hf : LocallyIntegrable f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (e : ℂ) : direction (f ⋆ g) e = f ⋆ (direction g e) := by
  funext x
  rw [direction, (hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (hg.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ)
    hf (hc.fderiv ℝ) (hg.continuous_fderiv (by simp)) x e

lemma laplacian_convolution {f g : ℂ → ℝ}
    (hf : LocallyIntegrable f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    Δ (f ⋆ g) = f ⋆ (Δ g) := by
  rw [laplacian_direction (hc.contDiff_convolution_right _ hf hg), laplacian_direction hg]
  rw [direction_convolution hf hg hc, direction_convolution hf hg hc,
    direction_convolution hf (direction_smooth hg _) (direction_compact hc _),
    direction_convolution hf (direction_smooth hg _) (direction_compact hc _)]
  funext x
  symm
  apply ConvolutionExistsAt.distrib_add
  · exact (direction_compact (direction_compact hc _) _).convolutionExists_right _ hf
      (direction_smooth (direction_smooth hg _) _).continuous x
  · exact (direction_compact (direction_compact hc _) _).convolutionExists_right _ hf
      (direction_smooth (direction_smooth hg _) _).continuous x



lemma log_potential_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ ((fun z : ℂ => Real.log ‖z‖) ⋆ f) :=
  hc.contDiff_convolution_right _ log_norm_locallyIntegrable hf

lemma laplacian_comp_neg {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    Δ (fun x : ℂ => f (-x)) z = Δ f (-z) := by
  have hh := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := 2) (-1 : ℝ)
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hh' : iteratedFDeriv ℝ 2 (fun x : ℂ => f (-x)) z =
      iteratedFDeriv ℝ 2 f (-z) := by
    simpa using congrFun hh z
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, hh']

lemma laplacian_comp_const_sub {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (a z : ℂ) :
    Δ (fun x : ℂ => f (a-x)) z = Δ f (a-z) := by
  have he : (fun x : ℂ => f (a-x)) = fun x => (fun y => f (y+a)) (-x) := by
    funext x; congr 1; abel
  have hshift : ContDiff ℝ ∞ (fun y : ℂ => f (y+a)) :=
    hf.comp (contDiff_id.add contDiff_const)
  calc
    _ = Δ (fun y : ℂ => f (y+a)) (-z) := by
      rw [he]
      exact laplacian_comp_neg hshift z
    _ = Δ f (-z+a) := congrFun (laplacian_comp_add_right f a) (-z)
    _ = Δ f (a-z) := by rw [sub_eq_add_neg, add_comm a]



lemma log_potential_laplacian {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) :
    Δ ((fun x : ℂ => Real.log ‖x‖) ⋆ f) z = (2 * Real.pi) * f z := by
  rw [laplacian_convolution log_norm_locallyIntegrable hf hc]
  let φ : ℂ → ℝ := fun x => f (z-x)
  have hφ : ContDiff ℝ ∞ φ := hf.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := by
    simpa [φ, Function.comp_def, sub_eq_add_neg, add_comm] using
      hc.comp_homeomorph ((Homeomorph.neg ℂ).trans (Homeomorph.addRight z))
  have h := integral_log_laplacian hφ hφc
  simp only [φ, laplacian_comp_const_sub hf, sub_zero] at h
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using h

lemma correctionIntegrand_contDiffOn {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    {s : Set ℂ} (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) :
    ContDiffOn ℝ ∞ (correctionIntegrand f) (s ×ˢ univ) := by
  intro p hp
  by_cases hy : p.2 ∈ tsupport f
  · have hg : ContDiff ℝ ∞ (fun p : ℂ × ℂ => 1-p.1*star p.2) := by
      exact contDiff_const.sub (contDiff_fst.mul
        (Complex.conjCLE.contDiff.comp contDiff_snd))
    exact ((hf.comp contDiff_snd).contDiffAt.mul
      ((hg.contDiffAt.norm (𝕜 := ℂ) (hn p.1 hp.1 p.2 hy)).log
        (norm_ne_zero_iff.mpr (hn p.1 hp.1 p.2 hy)))).contDiffWithinAt
  · have he : (fun q : ℂ × ℂ => f q.2) =ᶠ[𝓝 p] (fun _ => (0 : ℝ)) :=
      (notMem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto continuousAt_snd
    have hz : ContDiffAt ℝ ∞ (correctionIntegrand f) p := by
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [he] with q hq
      simp [correctionIntegrand, hq]
    exact hz.contDiffWithinAt

lemma correction_potential_smooth {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) :
    ContDiffOn ℝ ∞ (fun z : ℂ => ∫ y : ℂ, f y * Real.log ‖1-z*star y‖) s := by
  have hh := contDiffOn_convolution_left_with_param_comp
    (ContinuousLinearMap.lsmul ℝ ℝ) (v := fun _ : ℂ => (0 : ℂ))
    contDiffOn_const (f := fun _ : ℂ => (1 : ℝ))
    (g := fun z y => correctionIntegrand f (z,y)) hs hc.isCompact
    (fun z y _ hy => by simp [correctionIntegrand, image_eq_zero_of_notMem_tsupport hy])
    (locallyIntegrable_const (μ := (volume : Measure ℂ)) (1 : ℝ))
    (correctionIntegrand_contDiffOn hf hn)
  simpa only [convolution_def, correctionIntegrand, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_one] using hh

end StrictHotSpots.GreenPotential



open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
namespace StrictHotSpots.CompactParameter

variable {s k : Set ℂ} {F : ℂ × ℂ → ℝ}

lemma fderiv_eq_zero_outside (hs : IsOpen s) (hk : IsClosed k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0) {p : ℂ × ℂ}
    (hp : p.1 ∈ s) (hy : p.2 ∉ k) : fderiv ℝ F p = 0 := by
  have hd : HasFDerivAt F (0 : (ℂ × ℂ) →L[ℝ] ℝ) p := by
    apply (hasFDerivAt_const (0 : ℝ) p).congr_of_eventuallyEq
    filter_upwards [(hs.prod hk.isOpen_compl).mem_nhds (show p ∈ s ×ˢ kᶜ from ⟨hp,hy⟩)] with q hq
    exact hz q.1 hq.1 q.2 hq.2
  exact hd.fderiv

lemma fderiv_section_compact (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0) {z : ℂ} (hzz : z ∈ s) :
    HasCompactSupport (fun y : ℂ => fderiv ℝ F (z,y)) := by
  apply HasCompactSupport.intro hk
  intro y hy
  exact fderiv_eq_zero_outside hs hk.isClosed hz hzz hy

lemma fderiv_section_continuous (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hz : z ∈ s) :
    Continuous (fun y : ℂ => fderiv ℝ F (z,y)) := by
  exact (hf.continuousOn_fderiv_of_isOpen (hs.prod isOpen_univ) (by simp)).comp_continuous
    (continuous_const.prodMk continuous_id) (fun y => ⟨hz, mem_univ y⟩)

lemma hasFDerivAt_integral (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) :
    HasFDerivAt (fun z : ℂ => ∫ y : ℂ, F (z,y))
      ((∫ y : ℂ, fderiv ℝ F (z,y)).comp (ContinuousLinearMap.inl ℝ ℂ ℂ)) z := by
  have h := hasFDerivAt_convolution_right_with_param
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure ℂ))
    (f := fun _ : ℂ => (1 : ℝ)) (g := fun z y => F (z,y))
    hs hk (fun z y hzz hy => hz z hzz y hy)
    (locallyIntegrable_const (1 : ℝ)) (hf.of_le (by simp)) (z,0) hzz
  have h' := h.comp z (ContinuousLinearMap.inl ℝ ℂ ℂ).hasFDerivAt
  have hfun : (fun z : ℂ => (fun q : ℂ × ℂ =>
      ((fun _ : ℂ => (1 : ℝ)) ⋆ (fun y => F (q.1,y))) q.2)
      ((ContinuousLinearMap.inl ℝ ℂ ℂ) z)) =
      (fun z : ℂ => ∫ y : ℂ, F (z,y)) := by
    funext z
    simp only [ContinuousLinearMap.inl_apply, convolution_def,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul, one_mul, zero_sub]
    exact integral_neg_eq_self (fun y : ℂ => F (z,y)) volume
  simp only [Function.comp_def] at h'
  rw [hfun] at h'
  convert! h' using 1
  congr 1
  change (∫ y : ℂ, fderiv ℝ F (z,y)) =
    ∫ y : ℂ, (ContinuousLinearMap.lsmul ℝ ℝ).precompR (ℂ × ℂ) 1
      (fderiv ℝ F (z,0-y))
  have hid : (ContinuousLinearMap.lsmul ℝ ℝ).precompR (ℂ × ℂ) 1 =
      ContinuousLinearMap.id ℝ ((ℂ × ℂ) →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro D
    apply ContinuousLinearMap.ext
    intro p
    simp [ContinuousLinearMap.precompR_apply]
  rw [hid]
  simpa only [zero_sub, ContinuousLinearMap.id_apply] using
    (integral_neg_eq_self (fun y : ℂ => fderiv ℝ F (z,y)) volume).symm

lemma partial_contDiffOn (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) (e : ℂ) :
    ContDiffOn ℝ ∞ (paramDeriv F e) (s ×ˢ univ) :=
  (hf.fderiv_of_isOpen (hs.prod isOpen_univ) (by simp)).clm_apply contDiffOn_const

lemma partial_zero_outside (hs : IsOpen s) (hk : IsClosed k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0) (e : ℂ) :
    ∀ z ∈ s, ∀ y ∉ k, paramDeriv F e (z,y) = 0 := by
  intro z hzz y hy
  simp [paramDeriv, fderiv_eq_zero_outside hs hk hz (p := (z,y)) hzz hy]

lemma integral_contDiffOn (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : ℂ => ∫ y : ℂ, F (z,y)) s := by
  have hh := contDiffOn_convolution_left_with_param_comp
    (ContinuousLinearMap.lsmul ℝ ℝ) (v := fun _ : ℂ => (0 : ℂ))
    contDiffOn_const (f := fun _ : ℂ => (1 : ℝ))
    (g := fun z y => F (z,y)) hs hk
    (fun z y hzz hy => hz z hzz y hy)
    (locallyIntegrable_const (μ := (volume : Measure ℂ)) (1 : ℝ)) hf
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_one] using hh

lemma fderiv_integral_apply (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) (e : ℂ) :
    fderiv ℝ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z e =
      ∫ y : ℂ, paramDeriv F e (z,y) := by
  rw [(hasFDerivAt_integral hs hk hz hf hzz).fderiv]
  change (∫ y : ℂ, fderiv ℝ F (z,y)) (e,0) = _
  exact ContinuousLinearMap.integral_apply
    ((fderiv_section_continuous hs hf hzz).integrable_of_hasCompactSupport
      (fderiv_section_compact hs hk hz hzz)) _

lemma fderiv_section_apply (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hz : z ∈ s) (y e : ℂ) :
    fderiv ℝ (fun z : ℂ => F (z,y)) z e = paramDeriv F e (z,y) := by
  have hd := ((hf (z,y) ⟨hz, mem_univ y⟩).contDiffAt
    ((hs.prod isOpen_univ).mem_nhds ⟨hz, mem_univ y⟩)).differentiableAt (by simp)
  have hpair : HasFDerivAt (fun x : ℂ => (x,y)) (ContinuousLinearMap.inl ℝ ℂ ℂ) z := by
    exact (hasFDerivAt_id z).prodMk (hasFDerivAt_const y z)
  have hc := hd.hasFDerivAt.comp z hpair
  exact congrArg (fun L : ℂ →L[ℝ] ℝ => L e) hc.fderiv

lemma second_integral_apply (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) (e : ℂ) :
    fderiv ℝ (fun z : ℂ => fderiv ℝ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z e) z e =
      ∫ y : ℂ, paramDeriv (paramDeriv F e) e (z,y) := by
  have he : (fun z : ℂ => fderiv ℝ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z e) =ᶠ[𝓝 z]
      (fun z : ℂ => ∫ y : ℂ, paramDeriv F e (z,y)) := by
    filter_upwards [hs.mem_nhds hzz] with x hx
    exact fderiv_integral_apply hs hk hz hf hx e
  rw [he.fderiv_eq]
  exact fderiv_integral_apply hs hk (partial_zero_outside hs hk.isClosed hz e)
    (partial_contDiffOn hs hf e) hzz e

lemma second_section_apply (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hz : z ∈ s) (y e : ℂ) :
    fderiv ℝ (fun z : ℂ => fderiv ℝ (fun z : ℂ => F (z,y)) z e) z e =
      paramDeriv (paramDeriv F e) e (z,y) := by
  have he : (fun z : ℂ => fderiv ℝ (fun z : ℂ => F (z,y)) z e) =ᶠ[𝓝 z]
      (fun z : ℂ => paramDeriv F e (z,y)) := by
    filter_upwards [hs.mem_nhds hz] with x hx
    exact fderiv_section_apply hs hf hx y e
  rw [he.fderiv_eq]
  exact fderiv_section_apply hs (partial_contDiffOn hs hf e) hz y e

lemma integrable_section (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) :
    Integrable (fun y : ℂ => F (z,y)) := by
  have hc : HasCompactSupport (fun y : ℂ => F (z,y)) :=
    HasCompactSupport.intro hk (hz z hzz)
  exact (hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    (fun y => ⟨hzz, mem_univ y⟩)).integrable_of_hasCompactSupport hc

lemma laplacian_directions_at {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    Δ f z =
      fderiv ℝ (fun x : ℂ => fderiv ℝ f x 1) z 1 +
      fderiv ℝ (fun x : ℂ => fderiv ℝ f x Complex.I) z Complex.I := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const _),
    fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
    (differentiableAt_const _)]
  simp

lemma laplacian_integral (hs : IsOpen s) (hk : IsCompact k)
    (hz : ∀ z ∈ s, ∀ y ∉ k, F (z,y) = 0)
    (hf : ContDiffOn ℝ ∞ F (s ×ˢ univ)) {z : ℂ} (hzz : z ∈ s) :
    Δ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z =
      ∫ y : ℂ, Δ (fun z : ℂ => F (z,y)) z := by
  have hfi : ContDiffAt ℝ ∞ (fun z : ℂ => ∫ y : ℂ, F (z,y)) z :=
    ((integral_contDiffOn hs hk hz hf) z hzz).contDiffAt (hs.mem_nhds hzz)
  have hfs (y : ℂ) : ContDiffAt ℝ ∞ (fun z : ℂ => F (z,y)) z :=
    ((hf (z,y) ⟨hzz, mem_univ y⟩).contDiffAt
      ((hs.prod isOpen_univ).mem_nhds ⟨hzz, mem_univ y⟩)).comp z
      (contDiffAt_id.prodMk contDiffAt_const)
  have hi (e : ℂ) : Integrable (fun y : ℂ => paramDeriv (paramDeriv F e) e (z,y)) :=
    integrable_section hk
      (partial_zero_outside hs hk.isClosed (partial_zero_outside hs hk.isClosed hz e) e)
      (partial_contDiffOn hs (partial_contDiffOn hs hf e) e) hzz
  rw [laplacian_directions_at hfi, second_integral_apply hs hk hz hf hzz,
    second_integral_apply hs hk hz hf hzz, ← integral_add (hi 1) (hi Complex.I)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [laplacian_directions_at (hfs y), second_section_apply hs hf hzz,
    second_section_apply hs hf hzz]

end StrictHotSpots.CompactParameter


namespace StrictHotSpots.GreenPotential
open StrictHotSpots.GreenFundamental StrictHotSpots.DiskFormula

lemma correction_potential_laplacian {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) {z : ℂ} (hz : z ∈ s) :
    Δ (fun z : ℂ => ∫ y : ℂ, f y * Real.log ‖1-z*star y‖) z = 0 := by
  change Δ (fun z : ℂ => ∫ y : ℂ, correctionIntegrand f (z,y)) z = 0
  rw [CompactParameter.laplacian_integral hs hc.isCompact
    (F := correctionIntegrand f)
    (fun z _ y hy => by simp [correctionIntegrand, image_eq_zero_of_notMem_tsupport hy])
    (correctionIntegrand_contDiffOn hf hn) hz]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : f y = 0
  · simp [correctionIntegrand, hy]
  · have hyt : y ∈ tsupport f := subset_tsupport _ hy
    have ha : AnalyticAt ℂ (fun z : ℂ => 1-z*star y) z :=
      analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
    have hh := (ha.harmonicAt_log_norm (hn z hz y hyt)).const_smul (c := f y)
    exact hh.2.self_of_nhds

lemma log_potential_eq (f : ℂ → ℝ) (z : ℂ) :
    ((fun x : ℂ => Real.log ‖x‖) ⋆ f) z = ∫ y : ℂ, f y * Real.log ‖z-y‖ := by
  rw [← convolution_flip]
  simp only [convolution_def, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring


lemma potential_contDiffOn {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) :
    ContDiffOn ℝ ∞ (potential f) s :=
  ((correction_potential_smooth hf hc hs hn).div_const _).sub
    ((log_potential_smooth hf hc).contDiffOn.div_const _)

lemma potential_laplacian {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) {z : ℂ} (hz : z ∈ s) :
    Δ (potential f) z = -f z := by
  have ha := ((correction_potential_smooth hf hc hs hn) z hz).contDiffAt (hs.mem_nhds hz)
  have hb := (log_potential_smooth hf hc).contDiffAt (x := z)
  have he : potential f = (2 * Real.pi)⁻¹ •
      (fun z : ℂ => ∫ y : ℂ, f y * Real.log ‖1-z*star y‖) -
      (2 * Real.pi)⁻¹ • ((fun x : ℂ => Real.log ‖x‖) ⋆ f) := by
    funext x
    simp only [potential, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have ha2 : ContDiffAt ℝ 2 ((2 * Real.pi)⁻¹ •
      (fun z : ℂ => ∫ y : ℂ, f y * Real.log ‖1-z*star y‖)) z :=
    (ha.const_smul ((2 * Real.pi)⁻¹)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hb2 : ContDiffAt ℝ 2 ((2 * Real.pi)⁻¹ •
      ((fun x : ℂ => Real.log ‖x‖) ⋆ f)) z :=
    (hb.const_smul ((2 * Real.pi)⁻¹)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [he, ha2.laplacian_sub hb2,
    laplacian_smul _ (ha.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    laplacian_smul _ (hb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    correction_potential_laplacian hf hc hs hn hz, log_potential_laplacian hf hc]
  simp only [smul_eq_mul, mul_zero, zero_sub, neg_inj]
  field_simp

lemma potential_eq_zero_on_circle (f : ℂ → ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    potential f z = 0 := by
  have he (y : ℂ) : ‖1-z*star y‖ = ‖z-y‖ := by
    have hh := disk_cross_identity z y
    rw [hz] at hh
    nlinarith [norm_nonneg (1-z*star y), norm_nonneg (z-y)]
  simp only [potential, he, log_potential_eq, sub_self]

lemma potential_eq_integral {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {s : Set ℂ} (_hs : IsOpen s)
    (hn : ∀ z ∈ s, ∀ y ∈ tsupport f, 1-z*star y ≠ 0) {z : ℂ} (hz : z ∈ s) :
    potential f z = ∫ y : ℂ, green z y * f y := by
  have hi : Integrable (fun y : ℂ => f y * Real.log ‖1-z*star y‖) :=
    CompactParameter.integrable_section hc.isCompact
      (F := correctionIntegrand f)
      (fun z _ y hy => by simp [correctionIntegrand, image_eq_zero_of_notMem_tsupport hy])
      (correctionIntegrand_contDiffOn hf hn) hz
  have hj : Integrable (fun y : ℂ => f y * Real.log ‖z-y‖) := by
    simpa only [norm_sub_rev z, mul_comm] using log_sub_mul_integrable hf.continuous hc z
  rw [potential, log_potential_eq, ← integral_div, ← integral_div,
    ← integral_sub (hi.div_const _) (hj.div_const _)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne z] with y hy
  by_cases hfy : f y = 0
  · simp [hfy]
  · rw [green_eq_log (Ne.symm hy) (hn z hz y (subset_tsupport _ hfy))]
    ring

lemma exists_regular_neighborhood {f : ℂ → ℝ} (hc : HasCompactSupport f)
    (hd : tsupport f ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ R : ℝ, 1 < R ∧ ∀ z ∈ Metric.ball (0 : ℂ) R,
      ∀ y ∈ tsupport f, 1-z*star y ≠ 0 := by
  obtain ⟨a, ha, hsub⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ) < 1)
    hc.isCompact.isClosed hd
  refine ⟨a⁻¹, (one_lt_inv₀ ha.1).mpr ha.2, ?_⟩
  intro z hz y hy
  have hz' : ‖z‖ < a⁻¹ := by simpa using hz
  have hy' : ‖y‖ < a := by simpa using hsub hy
  have hp : ‖z*star y‖ < 1 := by
    rw [norm_mul, norm_star]
    calc
      _ ≤ ‖z‖ * a := mul_le_mul_of_nonneg_left hy'.le (norm_nonneg _)
      _ < a⁻¹ * a := mul_lt_mul_of_pos_right hz' ha.1
      _ = 1 := inv_mul_cancel₀ ha.1.ne'
  intro he
  have hm : z*star y = 1 := (sub_eq_zero.mp he).symm
  rw [hm, norm_one] at hp
  exact lt_irrefl _ hp

lemma potential_smooth_near_closed_disk {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hd : tsupport f ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ R : ℝ, 1 < R ∧ ContDiffOn ℝ ∞ (potential f) (Metric.ball 0 R) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) R, Δ (potential f) z = -f z) := by
  obtain ⟨R,hR,hn⟩ := exists_regular_neighborhood hc hd
  exact ⟨R,hR,potential_contDiffOn hf hc Metric.isOpen_ball hn,
    fun z hz => potential_laplacian hf hc Metric.isOpen_ball hn hz⟩

end StrictHotSpots.GreenPotential




open InnerProductSpace
open scoped Laplacian ContDiff
namespace StrictHotSpots

lemma laplacian_comp_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (g : E ≃ₗᵢ[ℝ] F) (f : F → ℝ) (x : E) :
    Δ (f ∘ g) x = Δ f (g x) := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis _ (b.map g)]
  have he : iteratedFDeriv ℝ 2 (f ∘ g) x =
      (iteratedFDeriv ℝ 2 f (g x)).compContinuousLinearMap (fun _ => g.toContinuousLinearEquiv.toContinuousLinearMap) := by
    simpa [iteratedFDerivWithin_univ] using g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
      uniqueDiffOn_univ (Set.mem_univ (g x)) 2
  simp only [he, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  fin_cases j <;> simp

end StrictHotSpots


namespace StrictHotSpots.PlaneGreen
open GreenPotential DiskH10

lemma source_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (source f) :=
  hf.comp complexIso.toContinuousLinearEquiv.contDiff

lemma source_compact {f : Plane → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (source f) :=
  hc.comp_homeomorph complexIso.toHomeomorph

lemma source_support {f : Plane → ℝ} (hs : tsupport f ⊆ disk) :
    tsupport (source f) ⊆ Metric.ball (0 : ℂ) 1 := by
  intro z hz
  have he := Set.ext_iff.mp (tsupport_comp_eq_preimage f complexIso.toHomeomorph) z
  have hm : complexIso z ∈ disk := hs (he.mp hz)
  simpa [disk] using hm

lemma smooth_near_closed_disk {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ disk) :
    ∃ R : ℝ, 1 < R ∧ ContDiffOn ℝ ∞ (potential f) (Metric.ball 0 R) ∧
      (∀ x ∈ Metric.ball (0 : Plane) R, Δ (potential f) x = -f x) := by
  obtain ⟨R,hR,hu,hp⟩ := GreenPotential.potential_smooth_near_closed_disk
    (source_contDiff hf) (source_compact hc) (source_support hs)
  refine ⟨R,hR,?_,?_⟩
  · exact hu.comp complexIso.symm.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun x hx => by simpa using hx)
  · intro x hx
    change Δ (GreenPotential.potential (source f) ∘ complexIso.symm) x = -f x
    rw [laplacian_comp_linearIsometryEquiv]
    have hh := hp (complexIso.symm x) (by simpa using hx)
    simpa [source] using hh

lemma zero_on_circle (f : Plane → ℝ) {x : Plane} (hx : ‖x‖ = 1) :
    potential f x = 0 :=
  GreenPotential.potential_eq_zero_on_circle (source f) (by simpa using hx)

lemma value_mk (w : H1 disk) (hw : w ∈ h10Submodule diskOpen) :
    H10.value diskOpen ⟨w,hw⟩ = H1.value w := rfl

lemma energy_mk (w : H1 disk) (hw : w ∈ h10Submodule diskOpen) (v : H10 diskOpen) :
    H10.energy diskOpen ⟨w,hw⟩ v = inner ℝ (H1.grad w) (H10.grad diskOpen v) := rfl

lemma exists_smooth_weak_solution {u f : Plane → ℝ} {R : ℝ}
    (hR : 1 < R) (hu : ContDiffOn ℝ ∞ u (Metric.ball 0 R))
    (hz : ∀ x : Plane, ‖x‖ = 1 → u x = 0)
    (hf : MemLp f 2 (volume.restrict disk))
    (hp : ∀ x ∈ disk, Δ u x = -f x) :
    ∃ w : H10 (Ω := disk) diskOpen,
      (H10.value diskOpen w =ᵐ[volume.restrict disk] u) ∧
      ∀ v : H10 (Ω := disk) diskOpen,
        H10.energy diskOpen w v = inner ℝ (hf.toLp f) (H10.value diskOpen v) := by
  let h : HasH1Gradient disk u (gradient u) := smooth_memH1 hR hu
  have hm : h.toH1 ∈ h10Submodule diskOpen := smooth_zero_boundary_memH10 hR hu hz
  refine ⟨⟨h.toH1,hm⟩,?_,?_⟩
  · rw [value_mk, H1.value_toH1]
    exact h.1.coeFn_toLp
  · intro v
    rw [energy_mk]
    exact smooth_weak_poisson diskOpen (hu.mono (Metric.ball_subset_ball hR.le)) h hf hp v



lemma exists_dirichlet_representative {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ disk) :
    ∃ u : H10 (Ω := disk) diskOpen,
      (H10.value diskOpen u =ᵐ[volume.restrict disk] potential f) ∧
      ∀ v : H10 (Ω := disk) diskOpen,
        H10.energy diskOpen u v =
          inner ℝ ((test_memLp (Ω := disk) hf hc).toLp f) (H10.value diskOpen v) := by
  have hex : ∃ R : ℝ, 1 < R ∧ ContDiffOn ℝ ∞ (potential f) (Metric.ball 0 R) ∧
      (∀ x ∈ Metric.ball (0 : Plane) R, Δ (potential f) x = -f x) :=
    smooth_near_closed_disk (f := f) hf hc hs
  rcases hex with ⟨R,hR,hu,hp⟩
  refine exists_smooth_weak_solution (u := potential f) (f := f) (R := R) hR hu
    ?_ (test_memLp (Ω := disk) hf hc) ?_
  · intro x hx
    exact zero_on_circle f hx
  · intro x hx
    exact hp x (Metric.ball_subset_ball hR.le hx)

end StrictHotSpots.PlaneGreen







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology




open MeasureTheory Filter
open scoped Topology ENNReal





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.MeasurableL2Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (K : X × Y → ℝ) (hK : AEStronglyMeasurable K (μ.prod ν))
  (hrow : ∀ᵐ x ∂μ, MemLp (fun y => K (x,y)) 2 ν)
  {B : ℝ} (hB : 0 ≤ B)
  (hbound : ∀ᵐ x ∂μ, (eLpNorm (fun y => K (x,y)) 2 ν).toReal ≤ B)

lemma operator_apply_ae (f : Lp ℝ 2 ν) :
    operator K hK hrow hB hbound f =ᵐ[μ] fun x => ∫ y, K (x,y) * f y ∂ν :=
  (apply_memLp K hK hrow hbound f).coeFn_toLp

end StrictHotSpots.MeasurableL2Kernel



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology
namespace StrictHotSpots

lemma eq_zero_of_inner_smoothTest_eq_zero {Ω : Set Plane} (hΩ : IsOpen Ω)
    (u : Lp ℝ 2 (volume.restrict Ω))
    (h : ∀ φ : smoothTestSpace Ω, inner ℝ (H1.value (smoothTestToH1 hΩ φ)) u = 0) :
    u = 0 := by
  have hl := (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hh := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict Ω) (hl.locallyIntegrableOn Ω)
    (fun φ hp hc hs => show (∫ x in Ω, φ x • u x) = 0 from by
      have ht := h ⟨φ,hp,hc,hs⟩
      have hv : H1.value (smoothTestToH1 hΩ ⟨φ,hp,hc,hs⟩) =
          (test_memLp (Ω := Ω) hp hc).toLp φ := rfl
      rw [hv, L2.inner_def] at ht
      convert ht using 1
      apply integral_congr_ae
      filter_upwards [(test_memLp (Ω := Ω) hp hc).coeFn_toLp] with x hx
      simp only [hx, smul_eq_mul, RCLike.inner_apply, conj_trivial]
      ring)
  apply Lp.ext
  filter_upwards [hh, ae_restrict_mem hΩ.measurableSet, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)]
    with x hx hΩx hz
  rw [hz]
  exact hx hΩx

lemma smoothTest_dense_L2 {Ω : Set Plane} (hΩ : IsOpen Ω) :
    DenseRange (fun φ : smoothTestSpace Ω => H1.value (smoothTestToH1 hΩ φ)) := by
  let T : smoothTestSpace Ω →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
    H1.value.toLinearMap.comp (smoothTestToH1 hΩ)
  have hz : T.rangeᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    change u = 0
    apply eq_zero_of_inner_smoothTest_eq_zero hΩ u
    intro φ
    exact (Submodule.mem_orthogonal _ _).mp hu (T φ) ⟨φ,rfl⟩
  have ht : T.range.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hz, Submodule.bot_orthogonal_eq_top]
  have hd : closure (Set.range T) = Set.univ := by
    change closure (T.range : Set (Lp ℝ 2 (volume.restrict Ω))) = Set.univ
    rw [← Submodule.topologicalClosure_coe, ht, Submodule.top_coe]
  exact dense_iff_closure_eq.mpr hd

end StrictHotSpots







open scoped InnerProductSpace
namespace StrictHotSpots.DirichletOperator

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


lemma solution_spec (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H)
    (f : H) (v : V) : B (solution B hB J f) v = ⟪f, J v⟫_ℝ := by
  rw [← hB.continuousLinearEquivOfBilin_apply]
  simp only [solution, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]



lemma green_norm_le (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : V →L[ℝ] H) {d : ℝ} (hd : 0 ≤ d)
    (hsub : ∀ v : V, ‖J v‖ ^ 2 ≤ d * B v v) : ‖green B hB J‖ ≤ d := by
  apply ContinuousLinearMap.opNorm_le_bound _ hd
  intro f
  let u := solution B hB J f
  have h0 := hsub u
  have hs : B u u = ⟪f, J u⟫_ℝ := solution_spec B hB J f u
  rw [hs] at h0
  have hi : ⟪f, J u⟫_ℝ ≤ ‖f‖ * ‖J u‖ := real_inner_le_norm _ _
  have ht : ‖J u‖ ^ 2 ≤ d * (‖f‖ * ‖J u‖) :=
    h0.trans (mul_le_mul_of_nonneg_left hi hd)
  change ‖J u‖ ≤ d * ‖f‖
  by_cases hz : ‖J u‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖J u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

end StrictHotSpots.DirichletOperator


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma integralOperator_ae (f : Lp ℝ 2 (volume.restrict disk)) :
    integralOperator f =ᵐ[volume.restrict disk] fun x => ∫ y in disk, kernel x y * f y :=
  MeasurableL2Kernel.operator_apply_ae _ _ _ _ _ f

lemma potential_eq_integral {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ disk) {x : Plane} (hx : x ∈ disk) :
    potential f x = ∫ y in disk, kernel x y * f y := by
  obtain ⟨R,hR,hn⟩ := GreenPotential.exists_regular_neighborhood (source_compact hc)
    (source_support hs)
  have hx' : complexIso.symm x ∈ Metric.ball (0 : ℂ) R := by
    have : ‖x‖ < 1 := by simpa [disk] using hx
    simpa using this.trans hR
  have hh := GreenPotential.potential_eq_integral (source_contDiff hf) (source_compact hc)
    Metric.isOpen_ball hn hx'
  change GreenPotential.potential (source f) (complexIso.symm x) = _
  rw [hh]
  have he := complexIso.symm.measurePreserving.integral_comp
    complexIso.symm.toMeasurableEquiv.measurableEmbedding
    (fun z => DiskFormula.green (complexIso.symm x) z * source f z)
  simp only [source, complexIso.apply_symm_apply] at he
  simp only [source]
  rw [← he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
  simp [hfy, kernel]

lemma variationalOperator_test (f : smoothTestSpace disk) :
    variationalOperator (H1.value (smoothTestToH1 diskOpen f)) =ᵐ[volume.restrict disk]
      potential f := by
  obtain ⟨u,hu,he⟩ := exists_dirichlet_representative f.property.1 f.property.2.1 f.property.2.2
  let w := DirichletOperator.solution (H10.energy diskOpen)
    (H10.energy_coercive diskOpen diskBounded) (H10.value diskOpen)
    (H1.value (smoothTestToH1 diskOpen f))
  have hw : ∀ v, H10.energy diskOpen w v = inner ℝ
      (H1.value (smoothTestToH1 diskOpen f)) (H10.value diskOpen v) :=
    DirichletOperator.solution_spec _ _ _ _
  have he' : ∀ v, H10.energy diskOpen u v = inner ℝ
      (H1.value (smoothTestToH1 diskOpen f)) (H10.value diskOpen v) := he
  obtain ⟨_,_,hun⟩ := H10.existsUnique_energy_solution diskOpen diskBounded
    ((innerSL ℝ (H1.value (smoothTestToH1 diskOpen f))).comp (H10.value diskOpen))
  have heq : w = u := (hun w hw).trans (hun u he').symm
  change H10.value diskOpen w =ᵐ[volume.restrict disk] potential f
  rw [heq]
  exact hu



lemma integralOperator_eq_variationalOperator : integralOperator = variationalOperator := by
  apply DFunLike.coe_injective
  apply (smoothTest_dense_L2 diskOpen).equalizer integralOperator.continuous
    variationalOperator.continuous
  funext f
  simp only [Function.comp_apply]
  apply Lp.ext
  filter_upwards [integralOperator_ae (H1.value (smoothTestToH1 diskOpen f)),
    variationalOperator_test f, ae_restrict_mem diskOpen.measurableSet] with x hx hu hxd
  rw [hx,hu,potential_eq_integral f.property.1 f.property.2.1 f.property.2.2 hxd]
  apply integral_congr_ae
  have hf : H1.value (smoothTestToH1 diskOpen f) =ᵐ[volume.restrict disk] f :=
    (test_memLp (Ω := disk) f.property.1 f.property.2.1).coeFn_toLp
  filter_upwards [hf] with y hy
  rw [hy]

end StrictHotSpots.PlaneGreen


open MeasureTheory
open scoped InnerProductSpace ENNReal
namespace StrictHotSpots.H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict Ω)


lemma greenOperator_norm_le {d : ℝ} (hd : 0 ≤ d)
    (hsub : ∀ u : H10 hΩ, ‖weightedValue hΩ hC hν u‖ ^ 2 ≤
      d * ‖grad hΩ u‖ ^ 2) : ‖greenOperator hΩ hb hC hν‖ ≤ d := by
  apply DirichletOperator.green_norm_le (energy hΩ) (energy_coercive hΩ hb)
    (weightedValue hΩ hC hν) hd
  intro u
  simpa only [energy_apply, real_inner_self_eq_norm_sq] using hsub u

end StrictHotSpots.H10


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.DirichletOperator

lemma green_comp {V H K : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B) (J : V →L[ℝ] H) (S : H →L[ℝ] K) :
    green B hB (S.comp J) = (S.comp (green B hB J)).comp S.adjoint := by
  simp only [green, solution, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]

end StrictHotSpots.DirichletOperator
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

lemma inclusion_ae (f : Lp ℝ 2 (volume.restrict disk)) : inclusion hC hν f =ᵐ[ν] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hC hν f

lemma inclusion_row (x : Plane) (hx : x ∈ disk) :
    inclusion hC hν ((kernel_memLp x hx).toLp (kernel x)) =
      (kernel_memLp_weighted hC hν x hx).toLp (kernel x) := by
  apply Lp.ext
  exact (inclusion_ae hC hν _).trans
    (((Measure.absolutelyContinuous_of_le_smul hν).ae_eq (kernel_memLp x hx).coeFn_toLp).trans
      (kernel_memLp_weighted hC hν x hx).coeFn_toLp.symm)

lemma integral_adjoint_row (f : Lp ℝ 2 ν) (x : Plane) (hx : x ∈ disk) :
    (∫ y in disk, kernel x y * (inclusion hC hν).adjoint f y) =
      ∫ y, kernel x y * f y ∂ν := by
  rw [MeasurableL2Kernel.integral_mul_eq_inner (kernel_memLp x hx)
    (Lp.memLp ((inclusion hC hν).adjoint f)), Lp.toLp_coeFn,
    ContinuousLinearMap.adjoint_inner_right, inclusion_row hC hν x hx]
  rw [MeasurableL2Kernel.integral_mul_eq_inner (kernel_memLp_weighted hC hν x hx)
    (Lp.memLp f), Lp.toLp_coeFn]



lemma weightedIntegralOperator_ae (f : Lp ℝ 2 ν) :
    weightedIntegralOperator hC hν f =ᵐ[ν] fun x => ∫ y, kernel x y * f y ∂ν := by
  have ha := (Measure.absolutelyContinuous_of_le_smul hν)
  filter_upwards [inclusion_ae hC hν (integralOperator ((inclusion hC hν).adjoint f)),
    ha.ae_eq (integralOperator_ae ((inclusion hC hν).adjoint f)),
    (ae_restrict_mem diskOpen.measurableSet).filter_mono ha.ae_le] with x hx hi hxd
  change inclusion hC hν (integralOperator ((inclusion hC hν).adjoint f)) x = _
  rw [hx,hi,integral_adjoint_row hC hν f x hxd]

lemma weightedIntegralOperator_eq_greenOperator : weightedIntegralOperator hC hν =
    H10.greenOperator diskOpen diskBounded hC hν := by
  unfold weightedIntegralOperator H10.greenOperator H10.weightedValue

  rw [DirichletOperator.green_comp, integralOperator_eq_variationalOperator]
  rfl



lemma weightedIntegralOperator_norm_le {d : ℝ} (hd : 0 ≤ d)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) : ‖weightedIntegralOperator hC hν‖ ≤ d := by
  rw [weightedIntegralOperator_eq_greenOperator]
  exact H10.greenOperator_norm_le diskOpen diskBounded hC hν hd hsub

end StrictHotSpots.PlaneGreen

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryKernel
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section TransferLayer



open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.MeasureKernelTransfer

lemma integral_mul_eq_inner {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    (∫ x, f x * g x ∂ν) = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx,hy, RCLike.inner_apply, conj_trivial]
  ring

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure X} {μ : Measure Y} (e : X → Y) (he : MeasurePreserving e ν μ)

lemma observe_ae (f : Lp ℝ 2 μ) : observe e he f =ᵐ[ν] f ∘ e :=
  Lp.coeFn_compMeasurePreserving f he

lemma observe_row {g : Y → ℝ} (hg : MemLp g 2 μ) :
    observe e he (hg.toLp g) = (hg.comp_measurePreserving he).toLp (g ∘ e) := rfl

lemma integral_adjoint_row {g : Y → ℝ} (hg : MemLp g 2 μ) (f : Lp ℝ 2 ν) :
    (∫ y, g y * (observe e he).adjoint f y ∂μ) = ∫ x, g (e x) * f x ∂ν := by
  rw [integral_mul_eq_inner hg (Lp.memLp _), Lp.toLp_coeFn,
    ContinuousLinearMap.adjoint_inner_right, observe_row e he hg]
  symm
  simpa only [Function.comp_apply, Lp.toLp_coeFn] using
    integral_mul_eq_inner (hg.comp_measurePreserving he) (Lp.memLp f)

lemma operator_ae (G : Y → Y → ℝ) (hrow : ∀ x, MemLp (G (e x)) 2 μ)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f : Lp ℝ 2 μ, T f =ᵐ[μ] fun y => ∫ z, G y z * f z ∂μ)
    (f : Lp ℝ 2 ν) :
    operator e he T f =ᵐ[ν] fun x => ∫ z, G (e x) (e z) * f z ∂ν := by
  filter_upwards [observe_ae e he (T ((observe e he).adjoint f)),
    he.quasiMeasurePreserving.ae_eq_comp (hT ((observe e he).adjoint f))] with x hx ht
  change observe e he (T ((observe e he).adjoint f)) x = _
  rw [hx]
  change T ((observe e he).adjoint f) (e x) = _
  rw [show T ((observe e he).adjoint f) (e x) =
    ∫ y, G (e x) y * (observe e he).adjoint f y ∂μ from ht]
  exact integral_adjoint_row e he (hrow x) f

lemma observe_norm_le : ‖observe e he‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖Lp.compMeasurePreserving e he f‖ ≤ 1 * ‖f‖
  simp

lemma operator_norm_le (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : ‖operator e he T‖ ≤ ‖T‖ := by
  calc
    ‖operator e he T‖ ≤ ‖(observe e he).comp T‖ * ‖(observe e he).adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖observe e he‖ * ‖T‖) * ‖observe e he‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖T‖) * 1 := by
      gcongr <;> exact observe_norm_le e he
    _ = ‖T‖ := by ring

end StrictHotSpots.MeasureKernelTransfer

end TransferLayer


namespace StrictHotSpots.MeasureKernelTransfer
open MeasureTheory
open scoped ENNReal InnerProductSpace
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure X} {μ : Measure Y} (e : X → Y) (he : MeasurePreserving e ν μ)

lemma observe_inner (f g : Lp ℝ 2 μ) :
    inner ℝ (observe e he f) (observe e he g) = inner ℝ f g :=
  (Lp.compMeasurePreservingₗᵢ ℝ e he).inner_map_map f g

lemma adjoint_observe (f : Lp ℝ 2 μ) :
    (observe e he).adjoint (observe e he f) = f := by
  have h := congrArg (fun T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => T f)
    (Lp.compMeasurePreservingₗᵢ ℝ e he).adjoint_comp_self
  exact h

lemma operator_observe (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℝ 2 μ) :
    operator e he T (observe e he f) = observe e he (T f) := by
  change observe e he (T ((observe e he).adjoint (observe e he f))) = _
  rw [adjoint_observe]

lemma resolvent_observe (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hT : ‖T‖ < 1)
    (f : Lp ℝ 2 μ) :
    BanachResolvent.resolvent (operator e he T) (observe e he f) =
      observe e he (BanachResolvent.resolvent T f) := by
  symm
  apply BanachResolvent.resolvent_solution _ ((operator_norm_le e he T).trans_lt hT)
  rw [operator_observe, ← map_sub]
  congr 1
  exact congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f)
    (BanachResolvent.resolvent_left T hT)

lemma resolvent_inner (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hT : ‖T‖ < 1)
    (f g : Lp ℝ 2 μ) :
    inner ℝ (observe e he f) (BanachResolvent.resolvent (operator e he T) (observe e he g)) =
      inner ℝ f (BanachResolvent.resolvent T g) := by
  rw [resolvent_observe e he T hT, observe_inner]

end StrictHotSpots.MeasureKernelTransfer

section DiskCompactLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.DiskKernel
lemma green_eq_formula (x y : Disk) :
    green x y = DiskFormula.green x y := by
  unfold green h DiskFormula.green
  rw [one_div_div]
  ring

lemma regularized_symm (ε : ℝ) (x y : Disk) : regularized ε x y = regularized ε y x := by
  have hh : h x y = h y x := by simp only [h, norm_sub_rev, mul_comm]
  simp only [regularized, hh]
end StrictHotSpots.DiskKernel

namespace StrictHotSpots.DiskCompact
open PlaneGreen DiskH10
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (ν : Measure X) [IsFiniteMeasure ν]
  (e : X → Plane) (he : Continuous e) (hd : ∀ x, e x ∈ disk)

omit [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma coordinates_injective (hinj : Function.Injective e) : Function.Injective (coordinates e hd) := by
  intro x y h
  apply hinj
  exact complexIso.symm.injective (congrArg Subtype.val h)

lemma parameter_tendsto : Tendsto regularizationParameter atTop (𝓝 (0 : ℝ)) := by
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
lemma parameter_tendsto_gt : Tendsto regularizationParameter atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨parameter_tendsto, Eventually.of_forall parameter_pos⟩

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_pos (n : ℕ) (x y : X) : 0 < regularized e he hd n (x,y) :=
  DiskKernel.regularized_pos (parameter_pos n) (parameter_le_one n) _ _
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_symm (n : ℕ) (x y : X) : regularized e he hd n (x,y) = regularized e he hd n (y,x) :=
  DiskKernel.regularized_symm _ _ _
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_onePositiveSquare {ι : Type} [Fintype ι] (n : ℕ) (s : ι → X) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => (regularized e he hd n (s i,s j))⁻¹) :=
  DiskKernel.regularized_reciprocal_onePositiveSquare (fun i => coordinates e hd (s i))
    (parameter_le_one n)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_tendsto_off (hinj : Function.Injective e) (x y : X) (hxy : x ≠ y) :
    Tendsto (fun n => regularized e he hd n (x,y)) atTop (𝓝 (kernel (e x) (e y))) := by
  have h := (DiskKernel.regularized_tendsto_offDiagonal
    (fun h => hxy (coordinates_injective e hd hinj h))).comp parameter_tendsto
  simpa only [DiskKernel.green_eq_formula, regularized, ContinuousMap.coe_mk,
    coordinates, kernel, Function.comp_def] using h
omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_tendsto_diagonal (x : X) :
    Tendsto (fun n => regularized e he hd n (x,x)) atTop atTop :=
  (DiskKernel.regularized_tendsto_diagonal (coordinates e hd x)).comp parameter_tendsto_gt

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma regularized_le (hinj : Function.Injective e) (n : ℕ) (x y : X) (hxy : x ≠ y) :
    regularized e he hd n (x,y) ≤ kernel (e x) (e y) := by
  simpa only [DiskKernel.green_eq_formula, regularized, ContinuousMap.coe_mk,
    coordinates, kernel] using DiskKernel.regularized_le_green (parameter_pos n).le
      (fun h => hxy (coordinates_injective e hd hinj h))

variable {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : Measure.map e ν ≤ C • volume.restrict disk)

omit [CompactSpace X] [IsFiniteMeasure ν] in
include he hν in
lemma ae_ne (x : X) : ∀ᵐ z ∂ν, z ≠ x := by
  have h := (Measure.absolutelyContinuous_of_le_smul hν).ae_le
  have hp : ∀ᵐ y ∂Measure.map e ν, y ≠ e x :=
    (Measure.ae_ne (volume.restrict disk) (e x)).filter_mono h
  filter_upwards [(preserving ν e he).quasiMeasurePreserving.ae hp] with z hz hx
  exact hz (congrArg e hx)

omit [CompactSpace X] [IsFiniteMeasure ν] in
include hd in
lemma operator_ae (f : Lp ℝ 2 ν) :
    operator ν e he hC hν f =ᵐ[ν] fun x => ∫ z, kernel (e z) (e x) * f z ∂ν := by
  simpa only [operator, kernel_symm] using MeasureKernelTransfer.operator_ae e (preserving ν e he)
    kernel (fun x => kernel_memLp_weighted hC hν (e x) (hd x))
    (weightedIntegralOperator hC hν) (weightedIntegralOperator_ae hC hν) f

omit [CompactSpace X] [IsFiniteMeasure ν] in
lemma operator_norm_le {d : ℝ} (hd0 : 0 ≤ d)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) : ‖operator ν e he hC hν‖ ≤ d :=
  (MeasureKernelTransfer.operator_norm_le e (preserving ν e he) _).trans
    (weightedIntegralOperator_norm_le hC hν hd0 hsub)




theorem reciprocal [Nonempty X] [DecidableEq X] (hinj : Function.Injective e)
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → X) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
      (CompactKernel.singularResolvedKernel ν (fun x y => kernel (e x) (e y))
        (kernel_memLp ν e he hd hC hν) (operator ν e he hC hν) (s i) (s j))⁻¹) := by
  apply CompactKernel.singular_reciprocal_of_regularization ν (regularized e he hd)
    (regularized_pos e he hd) (regularized_symm e he hd)
  · intro n ι _ s
    exact regularized_onePositiveSquare e he hd n s
  · intro x y hxy
    exact DiskFormula.green_pos (coordinates e hd x).property (coordinates e hd y).property
      (fun h => hxy (hinj (complexIso.symm.injective h)))
  · intro n x
    filter_upwards [ae_ne ν e he hν x] with z hz
    exact regularized_le e he hd hinj n z x hz
  · intro x
    filter_upwards [ae_ne ν e he hν x] with z hz
    exact regularized_tendsto_off e he hd hinj z x hz
  · exact regularized_tendsto_off e he hd hinj
  · exact regularized_tendsto_diagonal e he hd
  · exact operator_ae ν e he hd hC hν
  · exact (operator_norm_le ν e he hC hν hd0 hsub).trans_lt hd1

end StrictHotSpots.DiskCompact
end
end DiskCompactLayer

section PlaneResolvedLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.DiskCompact
open PlaneGreen DiskH10
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (ν : Measure X) [IsFiniteMeasure ν]
  (e : X → Plane) (he : Continuous e) (hd : ∀ x, e x ∈ disk)
  {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : Measure.map e ν ≤ C • volume.restrict disk)

omit [CompactSpace X] [IsFiniteMeasure ν] in
lemma observe_row (x : X) :
    MeasureKernelTransfer.observe e (preserving ν e he) (row hC hν ⟨e x,hd x⟩) =
      (kernel_memLp ν e he hd hC hν x).toLp (fun z => kernel (e z) (e x)) := rfl

omit [CompactSpace X] [IsFiniteMeasure ν] in
lemma resolved_eq {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) (x y : X) :
    CompactKernel.singularResolvedKernel ν (fun x y => kernel (e x) (e y))
      (kernel_memLp ν e he hd hC hν) (operator ν e he hC hν) x y =
      resolved hC hν ⟨e x,hd x⟩ ⟨e y,hd y⟩ := by
  unfold CompactKernel.singularResolvedKernel resolved
  rw [← observe_row ν e he hd hC hν x, ← observe_row ν e he hd hC hν y]
  exact congrArg (fun r : ℝ => kernel (e x) (e y) + r)
    (MeasureKernelTransfer.resolvent_inner e (preserving ν e he) _
      ((weightedIntegralOperator_norm_le hC hν hd0 hsub).trans_lt hd1) _ _)

include he in


theorem reciprocal_ambient [Nonempty X] [DecidableEq X] (hinj : Function.Injective e)
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → X) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
      (resolved hC hν ⟨e (s i),hd (s i)⟩ ⟨e (s j),hd (s j)⟩)⁻¹) := by
  have h := reciprocal ν e he hd hC hν hinj hd0 hd1 hsub s
  simpa only [resolved_eq ν e he hd hC hν hd0 hd1 hsub] using h

include he in
lemma reciprocal_ambient_of_map [Nonempty X] [DecidableEq X] (hinj : Function.Injective e)
    (μ : Measure Plane) (hmap : Measure.map e ν = μ) (hμ : μ ≤ C • volume.restrict disk)
    {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hμ u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → X) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
      (resolved hC hμ ⟨e (s i),hd (s i)⟩ ⟨e (s j),hd (s j)⟩)⁻¹) := by
  subst μ
  exact reciprocal_ambient ν e he hd hC hμ hinj hd0 hd1 hsub s

end StrictHotSpots.DiskCompact
end
end PlaneResolvedLayer

section PlaneCompactSupportLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable (ν : Measure Plane) [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)



theorem reciprocal_compact_support_oai (K : Set Plane) (hK : IsCompact K) (hKd : K ⊆ disk)
    (hsupp : ν Kᶜ = 0) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → disk) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
      (resolved hC hν (s i) (s j))⁻¹) := by
  classical
  let L : Set Plane := insert 0 (K ∪ Set.range (fun i => (s i : Plane)))
  have hc : IsCompact L := (hK.union (Set.finite_range _).isCompact).insert 0
  have hLd : L ⊆ disk := by
    intro x hx
    rcases hx with hx | hx | hx
    · rw [hx]; simp [disk]
    · exact hKd hx
    · rcases hx with ⟨i,rfl⟩; exact (s i).property
  have hKL : K ⊆ L := fun x hx => Or.inr (Or.inl hx)
  have hm : ∀ᵐ x ∂ν, x ∈ L := by
    rw [ae_iff]
    exact measure_mono_null (compl_subset_compl.mpr hKL) hsupp
  let : CompactSpace L := isCompact_iff_compactSpace.mp hc
  let : Nonempty L := ⟨⟨0,Or.inl rfl⟩⟩
  let νL : Measure L := ν.comap Subtype.val
  have hmap : Measure.map (Subtype.val : L → Plane) νL = ν := by
    rw [map_comap_subtype_coe hc.measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem hm
  let t : ι → L := fun i => ⟨s i,Or.inr (Or.inr ⟨i,rfl⟩)⟩
  have hp := DiskCompact.reciprocal_ambient_of_map νL Subtype.val continuous_subtype_val
    (fun x => hLd x.property) hC Subtype.val_injective ν hmap hν hd0 hd1 hsub t
  simpa only [t, Subtype.mk.injEq, Subtype.coe_eta, Subtype.ext_iff] using hp

end StrictHotSpots.PlaneGreen
end
end PlaneCompactSupportLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support_oai := @OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support_oai
