-- Prove2me | solution 1 for LatticePrepro.exists_latticeReduction
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:30:41.168602+00:00
-- url     : https://prove2.me/submissions/cab133b2-5e17-450d-bfbc-4f4d16a2a86e

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Theorems.Thm_LatticePrepro_LinearSystemFamily_code_no
import Theorems.Thm_LatticePrepro_LinearSystemFamily_code_yes
import Theorems.Thm_LatticePrepro_blockHad_lift_bound
import Theorems.Thm_LatticePrepro_radius_bound_gt_two

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

/-- The Hamming weight of a difference is the Hamming distance. -/
lemma hammingNorm_sub_eq_hammingDist {M : Type*} [Fintype M] {R : Type*} [AddGroup R] [DecidableEq R]
    (a b : M → R) :
    hammingNorm (a - b) = hammingDist a b := by
  simp [hammingNorm, hammingDist, sub_eq_zero]

end LatticePrepro

namespace LatticePrepro

open Finset

variable {M : Type*} [Fintype M]

/-- Sums of nonnegative real powers of absolute values are nonnegative. -/
lemma sum_abs_rpow_nonneg (q : ℝ) (v : M → ℝ) : 0 ≤ ∑ i, |v i| ^ q :=
  sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

/-- For an integer vector, the number of nonzero coordinates is at most `∑ |v i| ^ q`
(`q ≥ 0`). -/
lemma card_ne_zero_le_sum_abs_rpow {q : ℝ} (hq : 0 ≤ q) (v : M → ℤ) :
    (((univ.filter fun i => v i ≠ 0).card : ℕ) : ℝ) ≤ ∑ i, |(v i : ℝ)| ^ q := by
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_le_sum fun i _ => ?_
  split_ifs with h
  · have h1 : (1 : ℝ) ≤ |(v i : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h
    exact_mod_cast Real.one_le_rpow h1 hq
  · exact Real.rpow_nonneg (abs_nonneg _) _

/-- For an integer vector, the number of nonzero coordinates is at most `∑ (v i)^2`. -/
lemma card_ne_zero_le_sum_sq (v : M → ℤ) :
    (((univ.filter fun i => v i ≠ 0).card : ℕ) : ℝ) ≤ ∑ i, ((v i : ℝ)) ^ 2 := by
  have := card_ne_zero_le_sum_abs_rpow (q := 2) (by norm_num) v
  simpa [Real.rpow_two, sq_abs] using this

/-- For a vector with entries of absolute value at most `1`, `∑ |v i| ^ q` is at most the
number of nonzero coordinates (`q > 0`). -/
lemma sum_abs_rpow_le_card_ne_zero {q : ℝ} (hq : 0 < q) {v : M → ℝ} (hv : ∀ i, |v i| ≤ 1) :
    ∑ i, |v i| ^ q ≤ (((univ.filter fun i => v i ≠ 0).card : ℕ) : ℝ) := by
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_le_sum fun i _ => ?_
  split_ifs with h
  · exact_mod_cast Real.rpow_le_one (abs_nonneg _) (hv i) hq.le
  · have h0 : v i = 0 := by simpa using h
    rw [h0, abs_zero, Real.zero_rpow hq.ne']

/-- Power-mean inequality: for `q ≥ 2`,
`∑ v_i² ≤ N ^ (1 - 2/q) · (∑ |v_i|^q) ^ (2/q)` where `N = |M|`. -/
lemma sum_sq_le_card_rpow_mul {q : ℝ} (hq : 2 ≤ q) (v : M → ℝ) :
    ∑ i, (v i) ^ 2 ≤ (Fintype.card M : ℝ) ^ (1 - 2 / q) * (∑ i, |v i| ^ q) ^ (2 / q) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [univ_eq_empty, sum_empty, Fintype.card_eq_zero, Nat.cast_zero]
    positivity
  have hq0 : 0 < q := by linarith
  set N : ℝ := (Fintype.card M : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  -- power mean with weights `1/N` and exponent `q/2 ≥ 1`
  have hpm := Real.rpow_arith_mean_le_arith_mean_rpow (s := univ) (fun _ => 1 / N)
    (fun i => (v i) ^ 2) (fun _ _ => by positivity)
    (by simp [hN, Finset.sum_const, Finset.card_univ])
    (fun i _ => sq_nonneg _) (p := q / 2) (by linarith)
  have hz : ∀ i, ((v i) ^ 2) ^ (q / 2) = |v i| ^ q := by
    intro i
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    push_cast
    ring
  simp only [hz] at hpm
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hpm
  -- raise to the power `2/q`
  have h2q : 0 ≤ 2 / q := by positivity
  have hA : 0 ≤ ∑ i, (v i) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, |v i| ^ q := sum_abs_rpow_nonneg q v
  have hmono := Real.rpow_le_rpow (by positivity) hpm h2q
  rw [← Real.rpow_mul (by positivity), show q / 2 * (2 / q) = 1 by field_simp, Real.rpow_one,
    Real.mul_rpow (by positivity) hB] at hmono
  -- `hmono : 1/N * A ≤ (1/N)^(2/q) * B^(2/q)`
  have hN' : N ^ (1 - 2 / q) = N * (1 / N) ^ (2 / q) := by
    rw [Real.rpow_sub hNpos, Real.rpow_one, one_div, Real.inv_rpow hNpos.le, div_eq_mul_inv]
  rw [hN']
  calc ∑ i, (v i) ^ 2 = N * (1 / N * ∑ i, (v i) ^ 2) := by field_simp
    _ ≤ N * ((1 / N) ^ (2 / q) * (∑ i, |v i| ^ q) ^ (2 / q)) :=
        mul_le_mul_of_nonneg_left hmono hNpos.le
    _ = N * (1 / N) ^ (2 / q) * (∑ i, |v i| ^ q) ^ (2 / q) := by ring

end LatticePrepro

namespace LatticePrepro

namespace LinearSystemFamily

variable {F : Type} [Field F] {X : Type}

variable (L : LinearSystemFamily F X)

/-- Number of columns `n = D · b`. -/
lemma card_ι : Fintype.card L.ι = L.numBlocks * L.blockSize := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := L.blk) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp [L.card_fiber, Finset.sum_const, numBlocks]

end LinearSystemFamily

end LatticePrepro

namespace LatticePrepro

section OfSystem

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

lemma LinearSystemFamily.card_codeBlk_fiber (s : L.β ⊕ L.β) :
    (Finset.univ.filter fun i => L.codeBlk i = s).card = L.blockSize := by
  rcases s with t | t
  · rw [← L.card_fiber t, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.inl.injEq, reduceCtorEq,
      ite_false, Finset.sum_const_zero, add_zero]
  · rw [← L.card_fiber t, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
    simp only [LinearSystemFamily.codeBlk, Sum.map_inl, Sum.map_inr, Sum.inr.injEq, reduceCtorEq,
      ite_false, Finset.sum_const_zero, zero_add]

end OfSystem

end LatticePrepro

namespace LatticePrepro

open Finset

variable {p : ℕ} [Fact p.Prime] {M : Type*}

/-- Coordinatewise reduction modulo `p` as a `ℤ`-linear map. -/
def redMod (p : ℕ) (M : Type*) : (M → ℤ) →ₗ[ℤ] (M → ZMod p) :=
  LinearMap.pi fun i => (Int.castAddHom (ZMod p)).toIntLinearMap ∘ₗ LinearMap.proj i

@[simp] lemma redMod_apply (v : M → ℤ) (i : M) : redMod p M v i = (v i : ZMod p) := rfl

/-- The Construction A lattice `Λ_𝒞 = {v : v mod p ∈ 𝒞}`. -/
def constructionA (C : Submodule (ZMod p) (M → ZMod p)) : Submodule ℤ (M → ℤ) :=
  (C.restrictScalars ℤ).comap (redMod p M)

lemma mem_constructionA {C : Submodule (ZMod p) (M → ZMod p)} {v : M → ℤ} :
    v ∈ constructionA C ↔ redMod p M v ∈ C := Iff.rfl

/-- `p · ℤ^M ⊆ Λ_𝒞`. -/
lemma natCast_smul_mem_constructionA (C : Submodule (ZMod p) (M → ZMod p)) (v : M → ℤ) :
    (p : ℤ) • v ∈ constructionA C := by
  rw [mem_constructionA]
  convert C.zero_mem
  funext i
  simp

@[simp] lemma redMod_liftZMod (y : M → ZMod p) : redMod p M (liftZMod y) = y := by
  funext i
  simp [liftZMod]

lemma liftZMod_eq_zero_iff (y : M → ZMod p) (i : M) : liftZMod y i = 0 ↔ y i = 0 := by
  unfold liftZMod
  rw [Int.natCast_eq_zero, ZMod.val_eq_zero]

/-- The lift of a binary word is a `{0, 1}`-vector. -/
lemma liftZMod_binary {e : M → ZMod p} (he : IsBinary e) (i : M) :
    liftZMod e i = 0 ∨ liftZMod e i = 1 := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  rcases he i with h | h
  · left; unfold liftZMod; rw [h, ZMod.val_zero]; simp
  · right; unfold liftZMod; rw [h, ZMod.val_one]; simp

lemma abs_liftZMod_le_one {e : M → ZMod p} (he : IsBinary e) (i : M) : |liftZMod e i| ≤ 1 := by
  rcases liftZMod_binary he i with h | h <;> simp [h]

/-- The weight of a reduction is at most the number of nonzero coordinates. -/
lemma hammingNorm_redMod_le [Fintype M] (w : M → ℤ) :
    hammingNorm (redMod p M w) ≤ (univ.filter fun i => w i ≠ 0).card := by
  unfold hammingNorm
  refine Finset.card_le_card fun i hi => ?_
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, fun h0 => hi.2 ?_⟩
  simp [h0]

/-- The residual `t - v` of a lattice vector `v ∈ Λ_𝒞` against the lift `t` of `y` reduces to
`y - (v mod p)`, a word at Hamming distance `hammingDist y (v mod p)` from `y`, with
`v mod p ∈ 𝒞`. -/
lemma redMod_lift_sub [Fintype M] (C : Submodule (ZMod p) (M → ZMod p)) (y : M → ZMod p)
    {v : M → ℤ} (hv : v ∈ constructionA C) :
    redMod p M v ∈ C ∧ hammingNorm (redMod p M (liftZMod y - v)) = hammingDist y (redMod p M v) := by
  refine ⟨hv, ?_⟩
  rw [map_sub, redMod_liftZMod, hammingNorm_sub_eq_hammingDist]

/-- YES direction of Construction A: `t - ẽ ∈ Λ_𝒞` when `y - e ∈ 𝒞`. -/
lemma lift_sub_lift_mem_constructionA (C : Submodule (ZMod p) (M → ZMod p)) {y e : M → ZMod p}
    (h : y - e ∈ C) : liftZMod y - liftZMod e ∈ constructionA C := by
  rw [mem_constructionA, map_sub, redMod_liftZMod, redMod_liftZMod]
  exact h

end LatticePrepro

namespace LatticePrepro

namespace Hadamard

lemma sgn_one : sgn 1 = -1 := by decide

lemma sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  revert a b; decide

lemma zmod2_eq_one_of_ne_zero : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

lemma zmod2_add_eq_zero_iff : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide

variable (k : ℕ)

lemma card_Idx : Fintype.card (Idx k) = 2 ^ k := by
  simp [ZMod.card]

lemma ip_comm (u w : Idx k) : ip k u w = ip k w u := by
  simp [ip, mul_comm]

lemma ip_add_right (u w w' : Idx k) : ip k u (w + w') = ip k u w + ip k u w' := by
  simp [ip, mul_add, Finset.sum_add_distrib]

lemma ip_zero_right (u : Idx k) : ip k u 0 = 0 := by simp [ip]

lemma ip_add_single (u d : Idx k) (i : Fin k) :
    ip k (u + Pi.single i 1) d = ip k u d + d i := by
  simp [ip, add_mul, Finset.sum_add_distrib, Pi.single_apply]

lemma wh_comm (u w : Idx k) : wh k u w = wh k w u := by
  rw [wh, wh, ip_comm]

lemma wh_mul_wh (u w w' : Idx k) : wh k u w * wh k u w' = wh k u (w + w') := by
  rw [wh, wh, wh, ip_add_right, sgn_add]

lemma idx_add_eq_zero_iff (w w' : Idx k) : w + w' = 0 ↔ w = w' := by
  constructor
  · intro h; funext i; exact (zmod2_add_eq_zero_iff _ _).mp (congrFun h i)
  · rintro rfl; funext i; exact (zmod2_add_eq_zero_iff _ _).mpr rfl

/-- The character sum `∑_u (-1)^{⟨u, d⟩}` is `2^k` for `d = 0` and `0` otherwise. -/
lemma sum_sgn_ip (d : Idx k) : ∑ u, sgn (ip k u d) = if d = 0 then (2 ^ k : ℤ) else 0 := by
  split_ifs with hd
  · subst hd
    simp [ip_zero_right, Finset.card_univ]
  · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hd (funext h)
    have hdi : d i = 1 := zmod2_eq_one_of_ne_zero _ hi
    have key : ∀ u, sgn (ip k (u + Pi.single i 1) d) = - sgn (ip k u d) := by
      intro u
      rw [ip_add_single, hdi, sgn_add, sgn_one]
      ring
    have h := Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod 2)))
      (fun u => sgn (ip k u d))
    simp only [Equiv.coe_addRight, key, Finset.sum_neg_distrib] at h
    linarith

/-- Orthogonality of the Walsh–Hadamard matrix. -/
lemma sum_wh_mul_wh (w w' : Idx k) :
    ∑ u, wh k u w * wh k u w' = if w = w' then (2 ^ k : ℤ) else 0 := by
  simp_rw [wh_mul_wh]
  unfold wh
  rw [sum_sgn_ip]
  simp only [idx_add_eq_zero_iff]

lemma whMat_transpose : (whMat k).transpose = whMat k := by
  ext u w; simp [whMat, wh_comm]

lemma whMat_mul_whMat : whMat k * whMat k = (2 ^ k : ℤ) • (1 : Matrix (Idx k) (Idx k) ℤ) := by
  ext w w'
  simp only [Matrix.mul_apply, whMat, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl fun u _ => by rw [wh_comm k w u]]
  exact sum_wh_mul_wh k w w'

/-- `‖H x‖₂² = 2^k ‖x‖₂²`. -/
lemma dotProduct_mulVec_self (x : Idx k → ℤ) :
    ((whMat k).mulVec x) ⬝ᵥ ((whMat k).mulVec x) = (2 ^ k : ℤ) * (x ⬝ᵥ x) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, whMat_transpose,
    Matrix.mulVec_mulVec, whMat_mul_whMat, Matrix.smul_mulVec, Matrix.one_mulVec,
    smul_dotProduct, smul_eq_mul]

section Block

variable {β : Type*}

lemma blockHad_apply (v : β × Idx k → ℤ) (su : β × Idx k) :
    blockHad k v su = ∑ w, wh k su.2 w * v (su.1, w) := by
  simp [blockHad, Matrix.mulVec, dotProduct, whMat]

lemma blockHad_add (v w : β × Idx k → ℤ) : blockHad k (v + w) = blockHad k v + blockHad k w := by
  funext su; simp [blockHad_apply, mul_add, Finset.sum_add_distrib]

lemma blockHad_sub (v w : β × Idx k → ℤ) : blockHad k (v - w) = blockHad k v - blockHad k w := by
  funext su; simp [blockHad_apply, mul_sub, Finset.sum_sub_distrib]

lemma blockHad_smul (c : ℤ) (v : β × Idx k → ℤ) : blockHad k (c • v) = c • blockHad k v := by
  funext su; simp [blockHad_apply, Finset.mul_sum, mul_left_comm]

/-- The block Hadamard map as a `ℤ`-linear map. -/
def blockHadₗ : (β × Idx k → ℤ) →ₗ[ℤ] (β × Idx k → ℤ) where
  toFun := blockHad k
  map_add' := blockHad_add k
  map_smul' := blockHad_smul k

@[simp] lemma blockHadₗ_apply (v : β × Idx k → ℤ) : blockHadₗ k v = blockHad k v := rfl

/-- `H` applied twice is multiplication by `2^k`. -/
lemma blockHad_blockHad (v : β × Idx k → ℤ) : blockHad k (blockHad k v) = (2 ^ k : ℤ) • v := by
  funext su
  simp only [blockHad]
  rw [show (fun w => (whMat k).mulVec (fun w' => v (su.1, w')) w) =
      (whMat k).mulVec (fun w' => v (su.1, w')) from rfl]
  rw [Matrix.mulVec_mulVec, whMat_mul_whMat, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

/-- The inverse `2^{-k} H` of the block Hadamard map, on its image: `blockInv k (blockHad k u) = u`
(integer division is exact there). -/
def blockInv (v : β × Idx k → ℤ) : β × Idx k → ℤ := fun su => blockHad k v su / 2 ^ k

lemma blockInv_blockHad (u : β × Idx k → ℤ) : blockInv k (blockHad k u) = u := by
  funext su
  simp only [blockInv, blockHad_blockHad, Pi.smul_apply, smul_eq_mul]
  exact Int.mul_ediv_cancel_left (u su) (by positivity)

/-- Parseval's identity for the block Hadamard map. -/
lemma sum_sq_blockHad [Fintype β] (v : β × Idx k → ℤ) :
    ∑ su, (blockHad k v su) ^ 2 = 2 ^ k * ∑ su, (v su) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have := dotProduct_mulVec_self k (fun w => v (s, w))
  simp only [dotProduct, ← sq] at this
  exact this

end Block

end Hadamard

end LatticePrepro

namespace LatticePrepro

open Finset

variable {M : Type*} [Fintype M]

/-- The `ℓ_q` norm `(∑ i, |v i| ^ q) ^ (1 / q)` of a real vector. -/
noncomputable def lpNorm (q : ℝ) (v : M → ℝ) : ℝ := (∑ i, |v i| ^ q) ^ (1 / q)

/-- The sup norm `⨆ i, |v i|` of a real vector. -/
noncomputable def supNorm (v : M → ℝ) : ℝ := ⨆ i, |v i|

lemma lpNorm_nonneg (q : ℝ) (v : M → ℝ) : 0 ≤ lpNorm q v :=
  Real.rpow_nonneg (sum_abs_rpow_nonneg q v) _

lemma lpNorm_rpow {q : ℝ} (hq : 0 < q) (v : M → ℝ) : lpNorm q v ^ q = ∑ i, |v i| ^ q := by
  unfold lpNorm
  rw [one_div, Real.rpow_inv_rpow (sum_abs_rpow_nonneg q v) hq.ne']

lemma lpNorm_le_rpow_of_sum_le {q : ℝ} (hq : 0 < q) {v : M → ℝ} {c : ℝ}
    (h : ∑ i, |v i| ^ q ≤ c) : lpNorm q v ≤ c ^ (1 / q) :=
  Real.rpow_le_rpow (sum_abs_rpow_nonneg q v) h (by positivity)

lemma abs_le_supNorm (v : M → ℝ) (i : M) : |v i| ≤ supNorm v := by
  unfold supNorm
  exact le_ciSup (Set.finite_range fun j => |v j|).bddAbove i

omit [Fintype M] in
lemma supNorm_le {v : M → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |v i| ≤ c) : supNorm v ≤ c :=
  Real.iSup_le h hc

/-- `∑ v_i² ≤ N · (sup |v_i|)²`. -/
lemma sum_sq_le_card_mul_supNorm_sq (v : M → ℝ) :
    ∑ i, (v i) ^ 2 ≤ (Fintype.card M : ℝ) * supNorm v ^ 2 := by
  calc ∑ i, (v i) ^ 2 ≤ ∑ _i : M, supNorm v ^ 2 := by
        refine sum_le_sum fun i _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_supNorm v i) 2
    _ = (Fintype.card M : ℝ) * supNorm v ^ 2 := by
        rw [sum_const, card_univ, nsmul_eq_mul]

end LatticePrepro

namespace LatticePrepro

open Finset

variable {F : Type*} [Semiring F] {ι M : Type*}

open Classical in
/-- Extension by zero along an embedding, as a linear map. -/
noncomputable def padMap (f : ι ↪ M) : (ι → F) →ₗ[F] (M → F) :=
  LinearMap.pi fun m => if h : ∃ i, f i = m then LinearMap.proj h.choose else 0

open Classical in
lemma padMap_apply (f : ι ↪ M) (v : ι → F) (m : M) :
    padMap f v m = if h : ∃ i, f i = m then v h.choose else 0 := by
  unfold padMap
  rw [LinearMap.pi_apply]
  split_ifs <;> rfl

lemma padMap_apply_emb (f : ι ↪ M) (v : ι → F) (i : ι) : padMap f v (f i) = v i := by
  rw [padMap_apply]
  split_ifs with h
  · congr 1
    exact f.injective (Classical.choose_spec h)
  · exact absurd ⟨i, rfl⟩ h

lemma padMap_apply_of_not (f : ι ↪ M) (v : ι → F) {m : M} (hm : ¬ ∃ i, f i = m) :
    padMap f v m = 0 := by
  rw [padMap_apply]
  simp [hm]

lemma isBinary_padMap (f : ι ↪ M) {v : ι → F} (hv : IsBinary v) : IsBinary (padMap f v) := by
  intro m
  by_cases hm : ∃ i, f i = m
  · obtain ⟨i, rfl⟩ := hm
    rw [padMap_apply_emb]
    exact hv i
  · left
    exact padMap_apply_of_not f v hm

variable [Fintype ι] [Fintype M] [DecidableEq F]

lemma filter_padMap_ne (f : ι ↪ M) (v w : ι → F) :
    (univ.filter fun m => padMap f v m ≠ padMap f w m) =
      (univ.filter fun i => v i ≠ w i).map f := by
  ext m
  simp only [mem_filter, mem_univ, true_and, mem_map]
  constructor
  · intro h
    by_cases hm : ∃ i, f i = m
    · obtain ⟨i, rfl⟩ := hm
      rw [padMap_apply_emb, padMap_apply_emb] at h
      exact ⟨i, h, rfl⟩
    · exact absurd (by rw [padMap_apply_of_not f v hm, padMap_apply_of_not f w hm]) h
  · rintro ⟨i, hi, rfl⟩
    rwa [padMap_apply_emb, padMap_apply_emb]

lemma hammingDist_padMap (f : ι ↪ M) (v w : ι → F) :
    hammingDist (padMap f v) (padMap f w) = hammingDist v w := by
  unfold hammingDist
  rw [filter_padMap_ne, card_map]

lemma hammingNorm_padMap (f : ι ↪ M) (v : ι → F) : hammingNorm (padMap f v) = hammingNorm v := by
  rw [← hammingDist_zero_right, ← hammingDist_zero_right, ← map_zero (padMap (F := F) f),
    hammingDist_padMap]

lemma blockSupport_padMap {β : Type*} [DecidableEq β] (f : ι ↪ M) (blk : ι → β) (blk' : M → β)
    (hf : ∀ i, blk' (f i) = blk i) (v : ι → F) (s : β) :
    blockSupport blk' (padMap f v) s = (blockSupport blk v s).map f := by
  ext m
  simp only [blockSupport, mem_filter, mem_univ, true_and, mem_map]
  constructor
  · rintro ⟨hs, h⟩
    by_cases hm : ∃ i, f i = m
    · obtain ⟨i, rfl⟩ := hm
      rw [hf] at hs
      rw [padMap_apply_emb] at h
      exact ⟨i, ⟨hs, h⟩, rfl⟩
    · exact absurd (padMap_apply_of_not f v hm) h
  · rintro ⟨i, ⟨hs, h⟩, rfl⟩
    rw [hf, padMap_apply_emb]
    exact ⟨hs, h⟩

lemma atMostOnePerBlock_padMap {β : Type*} [DecidableEq β] (f : ι ↪ M) (blk : ι → β)
    (blk' : M → β) (hf : ∀ i, blk' (f i) = blk i) {v : ι → F} (hv : AtMostOnePerBlock blk v) :
    AtMostOnePerBlock blk' (padMap f v) := by
  intro s
  rw [blockSupport_padMap f blk blk' hf, card_map]
  exact hv s

end LatticePrepro

namespace LatticePrepro

section Padded

open Finset

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

namespace LinearSystemFamily

/-- `k` with `b ≤ 2^k < 2b`, where `b` is the block size. -/
noncomputable def padK : ℕ := Nat.clog 2 L.blockSize

lemma blockSize_le_two_pow_padK : L.blockSize ≤ 2 ^ L.padK := Nat.le_pow_clog one_lt_two _

lemma two_pow_padK_lt (hb : 1 ≤ L.blockSize) : 2 ^ L.padK < 2 * L.blockSize := by
  rcases Nat.lt_or_ge 1 L.blockSize with h | h
  · have h1 := Nat.pow_pred_clog_lt_self one_lt_two h
    have hk : 0 < L.padK := Nat.clog_pos one_lt_two h
    unfold padK at *
    rw [Nat.pred_eq_sub_one] at h1
    calc 2 ^ Nat.clog 2 L.blockSize = 2 * 2 ^ (Nat.clog 2 L.blockSize - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hk]
      _ < 2 * L.blockSize := by omega
  · have : L.blockSize = 1 := by omega
    simp [padK, this]

/-- Index set of a padded block. -/
abbrev PadIdx : Type := Hadamard.Idx L.padK

/-- Coordinates of the padded code: a block of the code and a position in `Fin k → ZMod 2`. -/
abbrev PadM : Type := (L.β ⊕ L.β) × L.PadIdx

lemma card_padM : Fintype.card L.PadM = 2 * L.numBlocks * 2 ^ L.padK := by
  simp only [Fintype.card_prod, Fintype.card_sum, Hadamard.card_Idx, numBlocks]
  ring

/-- An enumeration of the code coordinates. -/
noncomputable def codeEnum : (L.ι ⊕ L.ι) ≃ Fin (Fintype.card (L.ι ⊕ L.ι)) := Fintype.equivFin _

/-- The position of a coordinate inside its block. -/
noncomputable def codeRank (i : L.ι ⊕ L.ι) : ℕ :=
  (univ.filter fun j => L.codeBlk j = L.codeBlk i ∧ L.codeEnum j < L.codeEnum i).card

lemma codeRank_lt_blockSize (i : L.ι ⊕ L.ι) : L.codeRank i < L.blockSize := by
  calc L.codeRank i ≤ ((univ.filter fun j => L.codeBlk j = L.codeBlk i).erase i).card := by
        apply Finset.card_le_card
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
        refine ⟨fun hji => ?_, hj.1⟩
        subst hji
        exact lt_irrefl _ hj.2
    _ < (univ.filter fun j => L.codeBlk j = L.codeBlk i).card :=
        Finset.card_erase_lt_of_mem (by simp)
    _ = L.blockSize := L.card_codeBlk_fiber _

lemma codeRank_lt_of_lt {i j : L.ι ⊕ L.ι} (hs : L.codeBlk i = L.codeBlk j)
    (hij : L.codeEnum i < L.codeEnum j) : L.codeRank i < L.codeRank j := by
  unfold codeRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simp [hs, hij], by simp⟩
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact ⟨hl.1.trans hs, hl.2.trans hij⟩

lemma codeRank_inj {i j : L.ι ⊕ L.ι} (hs : L.codeBlk i = L.codeBlk j)
    (hr : L.codeRank i = L.codeRank j) : i = j := by
  by_contra hne
  have hne' : L.codeEnum i ≠ L.codeEnum j := fun h => hne (L.codeEnum.injective h)
  rcases lt_or_gt_of_ne hne' with h | h
  · exact absurd hr (L.codeRank_lt_of_lt hs h).ne
  · exact absurd hr (L.codeRank_lt_of_lt hs.symm h).ne'

/-- Positions `Fin (2^k)` as elements of `Fin k → ZMod 2`. -/
noncomputable def padIdxEquiv : Fin (2 ^ L.padK) ≃ L.PadIdx :=
  (Fintype.equivFinOfCardEq (Hadamard.card_Idx L.padK)).symm

/-- The block-respecting embedding of the code coordinates into the padded coordinates. -/
noncomputable def padEmbFn (i : L.ι ⊕ L.ι) : L.PadM :=
  (L.codeBlk i, L.padIdxEquiv ⟨L.codeRank i,
    lt_of_lt_of_le (L.codeRank_lt_blockSize i) L.blockSize_le_two_pow_padK⟩)

lemma padEmbFn_injective : Function.Injective L.padEmbFn := by
  intro i j h
  simp only [padEmbFn, Prod.mk.injEq] at h
  obtain ⟨hs, he⟩ := h
  have := L.padIdxEquiv.injective he
  exact L.codeRank_inj hs (Fin.mk.inj_iff.mp this)

/-- The padding embedding. -/
noncomputable def padEmb : L.ι ⊕ L.ι ↪ L.PadM := ⟨L.padEmbFn, L.padEmbFn_injective⟩

lemma padEmb_fst (i : L.ι ⊕ L.ι) : (L.padEmb i).1 = L.codeBlk i := rfl

/-- The padded code. -/
noncomputable def padCode : Submodule (ZMod p) (L.PadM → ZMod p) :=
  Submodule.map (padMap L.padEmb) L.code

/-- The padded target. -/
noncomputable def padTarget (x : X) : L.PadM → ZMod p := padMap L.padEmb (L.codeTarget x)

/-- (38) for the padded code, YES instances. -/
theorem pad_yes {x : X} (hx : L.IsYes x) :
    ∃ e : L.PadM → ZMod p, IsBinary e ∧ AtMostOnePerBlock Prod.fst e ∧
      hammingNorm e ≤ L.numBlocks ∧ L.padTarget x - e ∈ L.padCode := by
  obtain ⟨e, hb, h1, hw, hmem⟩ := L.code_yes hx
  refine ⟨padMap L.padEmb e, isBinary_padMap _ hb,
    atMostOnePerBlock_padMap L.padEmb L.codeBlk Prod.fst L.padEmb_fst h1,
    by rw [hammingNorm_padMap]; exact hw, ?_⟩
  rw [padTarget, ← map_sub]
  exact Submodule.mem_map_of_mem hmem

/-- (38) for the padded code, NO instances. -/
theorem pad_no {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hx : L.IsNo g x) :
    ∀ c ∈ L.padCode, g * L.numBlocks < hammingDist (L.padTarget x) c := by
  intro c hc
  obtain ⟨c₀, hc₀, rfl⟩ := Submodule.mem_map.mp hc
  rw [padTarget, hammingDist_padMap]
  exact L.code_no hg hD hx c₀ hc₀

end LinearSystemFamily

end Padded

section RealBounds

/-- Case `1 ≤ q ≤ 2`: with `R = ⌈D^{1/q}⌉`, `r^q ≤ 16 D (r / R)^q`. -/
lemma radius_bound_le_two {q D r : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hD : 1 ≤ D) (hr : 0 ≤ r) :
    r ^ q ≤ 16 * D * (r / (⌈D ^ (1 / q)⌉₊ : ℝ)) ^ q := by
  have hq0 : 0 < q := by linarith
  set R₀ : ℝ := D ^ (1 / q) with hR₀
  have hR₀1 : 1 ≤ R₀ := Real.one_le_rpow hD (by positivity)
  have hRpos : (0 : ℝ) < ⌈R₀⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (by linarith)
  have hRle : (⌈R₀⌉₊ : ℝ) ≤ 2 * R₀ := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ R₀)
    linarith
  have hRq : (⌈R₀⌉₊ : ℝ) ^ q ≤ 4 * D := by
    calc (⌈R₀⌉₊ : ℝ) ^ q ≤ (2 * R₀) ^ q := Real.rpow_le_rpow hRpos.le hRle hq0.le
      _ = 2 ^ q * R₀ ^ q := Real.mul_rpow (by norm_num) (by linarith)
      _ = 2 ^ q * D := by
          rw [hR₀, ← Real.rpow_mul (by linarith), one_div_mul_cancel hq0.ne', Real.rpow_one]
      _ ≤ 4 * D := by
          have h2 : (2 : ℝ) ^ q ≤ 2 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hq2
          rw [Real.rpow_two] at h2
          nlinarith
  rw [Real.div_rpow hr hRpos.le]
  have hRqpos : 0 < (⌈R₀⌉₊ : ℝ) ^ q := Real.rpow_pos_of_pos hRpos q
  have hrq : 0 ≤ r ^ q := Real.rpow_nonneg hr q
  rw [show 16 * D * (r ^ q / (⌈R₀⌉₊ : ℝ) ^ q) = r ^ q * (16 * D / (⌈R₀⌉₊ : ℝ) ^ q) by ring]
  have : 1 ≤ 16 * D / (⌈R₀⌉₊ : ℝ) ^ q := by
    rw [le_div_iff₀ hRqpos]
    linarith
  nlinarith

/-- Case `p = ∞`: with `R = 1`, `w ≤ A / t` and `A ≤ 2 t D m^2`, we get `w ≤ 16 D (m / 1)^2`. -/
lemma radius_bound_inf {t D A m w : ℝ} (ht : 0 < t) (hD : 0 ≤ D) (hw : w ≤ A / t)
    (hA : A ≤ 2 * (t * D) * m ^ 2) : w ≤ 16 * D * (m / ((1 : ℕ) : ℝ)) ^ (2 : ℝ) := by
  rw [Nat.cast_one, div_one, Real.rpow_two]
  have : A / t ≤ 2 * D * m ^ 2 := by
    rw [div_le_iff₀ ht]
    nlinarith
  nlinarith [sq_nonneg m]

end RealBounds

section Cases

open Finset

variable {p : ℕ} [Fact p.Prime] {X : Type} (L : LinearSystemFamily (ZMod p) X)

namespace LinearSystemFamily

/-- The Construction A lattice family on the padded code (for `p ≤ 2`). -/
noncomputable abbrev latticeA : LatticeFamily X where
  M := L.PadM
  lattice := constructionA L.padCode
  target := fun x => liftZMod (L.padTarget x)

/-- The residual weight for Construction A: `wt((t_x - v) mod p)`. -/
noncomputable def weightA (x : X) (v : L.PadM → ℤ) : ℕ :=
  hammingNorm (redMod p L.PadM (liftZMod (L.padTarget x) - v))

/-- The Hadamard-transformed lattice family (for `p > 2`). -/
noncomputable abbrev latticeH : LatticeFamily X where
  M := L.PadM
  lattice := Submodule.map (Hadamard.blockHadₗ L.padK) (constructionA L.padCode)
  target := fun x => Hadamard.blockHad L.padK (liftZMod (L.padTarget x))

/-- The residual weight for the Hadamard lattice: `wt((t_x - H⁻¹ v) mod p)`, where
`H⁻¹ v = 2^{-k} H v`. -/
noncomputable def weightH (x : X) (v : L.PadM → ℤ) : ℕ :=
  hammingNorm (redMod p L.PadM (liftZMod (L.padTarget x) - Hadamard.blockInv L.padK v))

lemma two_mul_card_le_card_padM : 2 * Fintype.card L.ι ≤ Fintype.card L.PadM := by
  rw [L.card_padM, L.card_ι, mul_assoc]
  exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ L.blockSize_le_two_pow_padK)

lemma card_padM_lt {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) :
    Fintype.card L.PadM < 4 * Fintype.card L.ι := by
  rw [L.card_padM, L.card_ι]
  have hk := L.two_pow_padK_lt (by omega)
  calc 2 * L.numBlocks * 2 ^ L.padK < 2 * L.numBlocks * (2 * L.blockSize) :=
        Nat.mul_lt_mul_of_pos_left hk (by omega)
    _ = 4 * (L.numBlocks * L.blockSize) := by ring

/-- NO instances for Construction A: the residual weight exceeds `g · D`. -/
lemma lt_weightA {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hno : L.IsNo g x) {v : L.PadM → ℤ} (hv : v ∈ L.latticeA.lattice) :
    g * L.numBlocks < L.weightA x v := by
  obtain ⟨hvC, hwt⟩ := redMod_lift_sub L.padCode (L.padTarget x) hv
  unfold weightA
  rw [hwt]
  exact L.pad_no hg hD hno _ hvC

/-- Case `1 ≤ q ≤ 2`. -/
noncomputable def reduction_le_two {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2) : LatticeReduction L g (PNorm.fin q hq) := by
  have hq0 : 0 < q := by linarith
  have hD1 : (1 : ℝ) ≤ L.numBlocks := by exact_mod_cast hD
  set R₀ : ℝ := (L.numBlocks : ℝ) ^ (1 / q) with hR₀
  have hR₀1 : 1 ≤ R₀ := Real.one_le_rpow hD1 (by positivity)
  refine ⟨L.latticeA, ⌈R₀⌉₊, ?_, ?_, L.two_mul_card_le_card_padM, L.card_padM_lt hg hD,
    p, (Fact.out : p.Prime).pos, fun v => natCast_smul_mem_constructionA _ v, L.weightA, ?_, ?_,
    fun x hno v hv => L.lt_weightA hg hD hno hv⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  · rw [Nat.ceil_le]
    calc R₀ ≤ (L.numBlocks : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hD1 (by rw [div_le_one hq0]; exact hq)
      _ = (L.numBlocks : ℝ) := Real.rpow_one _
      _ ≤ (Fintype.card L.PadM : ℝ) := by
          rw [L.card_padM]
          have : 1 ≤ 2 ^ L.padK := Nat.one_le_two_pow
          exact_mod_cast (by nlinarith : L.numBlocks ≤ 2 * L.numBlocks * 2 ^ L.padK)
  · -- YES
    intro x hx
    obtain ⟨e, hb, h1, hw, hmem⟩ := L.pad_yes hx
    refine ⟨liftZMod (L.padTarget x) - liftZMod e,
      lift_sub_lift_mem_constructionA _ hmem, ?_⟩
    change lpNorm q (LatticeFamily.toReal
      (liftZMod (L.padTarget x) - (liftZMod (L.padTarget x) - liftZMod e))) ≤ (⌈R₀⌉₊ : ℝ)
    rw [sub_sub_cancel]
    refine le_trans (lpNorm_le_rpow_of_sum_le hq0 ?_) (Nat.le_ceil _)
    calc ∑ i, |LatticeFamily.toReal (liftZMod e) i| ^ q
        ≤ ((univ.filter fun i => LatticeFamily.toReal (liftZMod e) i ≠ 0).card : ℝ) := by
          refine sum_abs_rpow_le_card_ne_zero hq0 fun i => ?_
          simp only [LatticeFamily.toReal]
          rw [← Int.cast_abs]
          exact_mod_cast abs_liftZMod_le_one hb i
      _ = (hammingNorm e : ℝ) := by
          unfold hammingNorm
          congr 2
          ext i
          simp [LatticeFamily.toReal, liftZMod_eq_zero_iff]
      _ ≤ (L.numBlocks : ℝ) := by exact_mod_cast hw
  · -- the weight bound
    intro x v _
    have hs : (PNorm.fin q hq).s = q := min_eq_left hq2
    rw [hs]
    set d := liftZMod (L.padTarget x) - v with hd
    change (hammingNorm (redMod p L.PadM d) : ℝ) ≤
      16 * L.numBlocks * (lpNorm q (LatticeFamily.toReal d) / (⌈R₀⌉₊ : ℝ)) ^ q
    have hwd : (hammingNorm (redMod p L.PadM d) : ℝ) ≤ lpNorm q (LatticeFamily.toReal d) ^ q := by
      rw [lpNorm_rpow hq0]
      calc (hammingNorm (redMod p L.PadM d) : ℝ)
          ≤ ((univ.filter fun i => d i ≠ 0).card : ℝ) := by exact_mod_cast hammingNorm_redMod_le d
        _ ≤ ∑ i, |LatticeFamily.toReal d i| ^ q := card_ne_zero_le_sum_abs_rpow hq0.le d
    exact hwd.trans (radius_bound_le_two hq hq2 hD1 (lpNorm_nonneg _ _))

/-- The common data of the Hadamard cases: full rank, the YES bound and the NO bound. -/
lemma latticeH_smul_mem (v : L.PadM → ℤ) :
    ((p * 2 ^ L.padK : ℕ) : ℤ) • v ∈ L.latticeH.lattice := by
  refine Submodule.mem_map.mpr ⟨(p : ℤ) • Hadamard.blockHad L.padK v,
    natCast_smul_mem_constructionA _ _, ?_⟩
  rw [Hadamard.blockHadₗ_apply, Hadamard.blockHad_smul, Hadamard.blockHad_blockHad, smul_smul]
  push_cast
  rfl

/-- YES instances in the Hadamard cases: the residual `H ẽ` has entries of absolute value at
most `1` on at most `D · 2^k` coordinates. -/
lemma latticeH_yes {x : X} (hx : L.IsYes x) :
    ∃ v ∈ L.latticeH.lattice, (∀ su, |(L.latticeH.target x - v) su| ≤ 1) ∧
      (univ.filter fun su => (L.latticeH.target x - v) su ≠ 0).card ≤
        L.numBlocks * 2 ^ L.padK := by
  obtain ⟨e, hb, h1, hw, hmem⟩ := L.pad_yes hx
  refine ⟨Hadamard.blockHad L.padK (liftZMod (L.padTarget x) - liftZMod e),
    Submodule.mem_map_of_mem (lift_sub_lift_mem_constructionA _ hmem), ?_⟩
  have hres : L.latticeH.target x - Hadamard.blockHad L.padK (liftZMod (L.padTarget x) - liftZMod e)
      = Hadamard.blockHad L.padK (liftZMod e) := by
    show Hadamard.blockHad L.padK (liftZMod (L.padTarget x)) - _ = _
    rw [← Hadamard.blockHad_sub, sub_sub_cancel]
  rw [hres]
  obtain ⟨habs, hcard⟩ := blockHad_lift_bound hb h1
  exact ⟨habs, hcard.trans (Nat.mul_le_mul_right _ hw)⟩

/-- The residual weight of `v = H u` in the Hadamard lattice is `wt((t - u) mod p)`. -/
lemma weightH_blockHad (x : X) (u : L.PadM → ℤ) :
    L.weightH x (Hadamard.blockHad L.padK u) =
      hammingNorm (redMod p L.PadM (liftZMod (L.padTarget x) - u)) := by
  rw [weightH, Hadamard.blockInv_blockHad]

/-- The residual weight in the Hadamard cases satisfies `w ≤ ‖t_H - v‖₂² / 2^k`. -/
lemma weightH_le (x : X) {v : L.PadM → ℤ} (hv : v ∈ L.latticeH.lattice) :
    (L.weightH x v : ℝ) ≤ (∑ su, ((L.latticeH.target x - v) su : ℝ) ^ 2) / (2 ^ L.padK : ℝ) := by
  obtain ⟨u, -, rfl⟩ := Submodule.mem_map.mp hv
  rw [Hadamard.blockHadₗ_apply, weightH_blockHad]
  set d := liftZMod (L.padTarget x) - u with hd
  have hres : L.latticeH.target x - Hadamard.blockHad L.padK u = Hadamard.blockHad L.padK d := by
    show Hadamard.blockHad L.padK (liftZMod (L.padTarget x)) - _ = _
    rw [← Hadamard.blockHad_sub]
  rw [hres]
  have hpars : ∑ su, ((Hadamard.blockHad L.padK d su : ℤ) : ℝ) ^ 2 =
      (2 ^ L.padK : ℝ) * ∑ su, ((d su : ℤ) : ℝ) ^ 2 := by
    have := Hadamard.sum_sq_blockHad L.padK d
    exact_mod_cast this
  rw [hpars, mul_div_cancel_left₀ _ (by positivity)]
  calc (hammingNorm (redMod p L.PadM d) : ℝ)
      ≤ ((univ.filter fun i => d i ≠ 0).card : ℝ) := by exact_mod_cast hammingNorm_redMod_le d
    _ ≤ ∑ su, ((d su : ℤ) : ℝ) ^ 2 := card_ne_zero_le_sum_sq d

/-- NO instances in the Hadamard cases: the residual weight exceeds `g · D`. -/
lemma lt_weightH {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) {x : X}
    (hno : L.IsNo g x) {v : L.PadM → ℤ} (hv : v ∈ L.latticeH.lattice) :
    g * L.numBlocks < L.weightH x v := by
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
  rw [Hadamard.blockHadₗ_apply, weightH_blockHad]
  obtain ⟨huC, hwt⟩ := redMod_lift_sub L.padCode (L.padTarget x) hu
  rw [hwt]
  exact L.pad_no hg hD hno _ huC

/-- Case `q > 2`. -/
noncomputable def reduction_gt_two {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    {q : ℝ} (hq : 1 ≤ q) (hq2 : 2 < q) : LatticeReduction L g (PNorm.fin q hq) := by
  have hq0 : 0 < q := by linarith
  have hD1 : (1 : ℝ) ≤ L.numBlocks := by exact_mod_cast hD
  have ht1 : (1 : ℝ) ≤ (2 ^ L.padK : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  set a : ℝ := (2 ^ L.padK : ℝ) * L.numBlocks with ha
  have ha1 : 1 ≤ a := by nlinarith
  set R₀ : ℝ := a ^ (1 / q) with hR₀
  have hR₀1 : 1 ≤ R₀ := Real.one_le_rpow ha1 (by positivity)
  have hcardR : (Fintype.card L.PadM : ℝ) = 2 * a := by
    rw [L.card_padM, ha]; push_cast; ring
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨L.latticeH, ⌈R₀⌉₊, ?_, ?_, L.two_mul_card_le_card_padM, L.card_padM_lt hg hD,
    p * 2 ^ L.padK, by positivity, L.latticeH_smul_mem, L.weightH, ?_, ?_,
    fun x hno v hv => L.lt_weightH hg hD hno hv⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  · change ⌈R₀⌉₊ ≤ Fintype.card L.PadM
    rw [Nat.ceil_le, hcardR]
    calc R₀ ≤ a ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ha1 (by rw [div_le_one hq0]; exact hq)
      _ = a := Real.rpow_one _
      _ ≤ 2 * a := by linarith
  · -- YES
    intro x hx
    obtain ⟨v, hv, habs, hcard⟩ := L.latticeH_yes hx
    refine ⟨v, hv, ?_⟩
    change lpNorm q (LatticeFamily.toReal (L.latticeH.target x - v)) ≤ (⌈R₀⌉₊ : ℝ)
    refine le_trans (lpNorm_le_rpow_of_sum_le hq0 ?_) (Nat.le_ceil _)
    calc ∑ i, |LatticeFamily.toReal (L.latticeH.target x - v) i| ^ q
        ≤ ((univ.filter fun i =>
            LatticeFamily.toReal (L.latticeH.target x - v) i ≠ 0).card : ℝ) := by
          refine sum_abs_rpow_le_card_ne_zero hq0 fun i => ?_
          simp only [LatticeFamily.toReal]
          rw [← Int.cast_abs]
          exact_mod_cast habs i
      _ = ((univ.filter fun su => (L.latticeH.target x - v) su ≠ 0).card : ℝ) := by
          congr 2
          ext i
          simp only [mem_filter, mem_univ, true_and, LatticeFamily.toReal, ne_eq, Int.cast_eq_zero]
      _ ≤ ((L.numBlocks * 2 ^ L.padK : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = a := by rw [ha]; push_cast; ring
  · -- the weight bound
    intro x v hv
    have hw := L.weightH_le x hv
    have hs : (PNorm.fin q hq).s = 2 := min_eq_right hq2.le
    rw [hs]
    change (L.weightH x v : ℝ) ≤ 16 * L.numBlocks *
      (lpNorm q (LatticeFamily.toReal (L.latticeH.target x - v)) / (⌈R₀⌉₊ : ℝ)) ^ (2 : ℝ)
    have hpm := sum_sq_le_card_rpow_mul hq2.le (LatticeFamily.toReal (L.latticeH.target x - v))
    rw [hcardR] at hpm
    simp only [LatticeFamily.toReal] at hpm hw ⊢
    exact radius_bound_gt_two hq2 ht1 hD1 (sum_abs_rpow_nonneg _ _) hw hpm

/-- Case `p = ∞`. -/
noncomputable def reduction_inf {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks) :
    LatticeReduction L g PNorm.inf := by
  have hD1 : (1 : ℝ) ≤ L.numBlocks := by exact_mod_cast hD
  have ht1 : (1 : ℝ) ≤ (2 ^ L.padK : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  have hcardR : (Fintype.card L.PadM : ℝ) = 2 * ((2 ^ L.padK : ℝ) * L.numBlocks) := by
    rw [L.card_padM]; push_cast; ring
  have hne : Nonempty L.PadM := by
    obtain ⟨b⟩ := Fintype.card_pos_iff.mp hD
    exact ⟨(Sum.inl b, 0)⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨L.latticeH, 1, le_rfl, Fintype.card_pos, L.two_mul_card_le_card_padM,
    L.card_padM_lt hg hD, p * 2 ^ L.padK, by positivity, L.latticeH_smul_mem, L.weightH, ?_, ?_,
    fun x hno v hv => L.lt_weightH hg hD hno hv⟩
  · -- YES
    intro x hx
    obtain ⟨v, hv, habs, -⟩ := L.latticeH_yes hx
    refine ⟨v, hv, ?_⟩
    change supNorm (LatticeFamily.toReal (L.latticeH.target x - v)) ≤ ((1 : ℕ) : ℝ)
    rw [Nat.cast_one]
    refine supNorm_le zero_le_one fun i => ?_
    simp only [LatticeFamily.toReal]
    rw [← Int.cast_abs]
    exact_mod_cast habs i
  · -- the weight bound
    intro x v hv
    have hw := L.weightH_le x hv
    change (L.weightH x v : ℝ) ≤ 16 * L.numBlocks *
      (supNorm (LatticeFamily.toReal (L.latticeH.target x - v)) / ((1 : ℕ) : ℝ)) ^ (2 : ℝ)
    have hsup := sum_sq_le_card_mul_supNorm_sq (LatticeFamily.toReal (L.latticeH.target x - v))
    rw [hcardR] at hsup
    simp only [LatticeFamily.toReal] at hsup hw ⊢
    exact radius_bound_inf (by positivity) (by linarith) hw hsup

end LinearSystemFamily

end Cases

/-- **Lemma 3.12** (the lattice reduction). Given a linear system family over `𝔽_p` with gap
`g < b` and at least one block, there is a `LatticeReduction`: a fixed full-rank lattice
`Λ ⊆ ℤ^M` with `2 n ≤ M < 4 n` (`n = |ι|`), an integer radius `1 ≤ R ≤ M`, targets, and a
residual weight such that

* YES instances have a lattice vector within `ℓ_p`-distance `R` of the target;
* every lattice vector `v` has residual weight `w ≤ 16 · D · (dist / R)^s`, and `w > g · D` on NO
  instances. -/
private theorem exists_latticeReduction {p : ℕ} [Fact p.Prime] {X : Type}
    (L : LinearSystemFamily (ZMod p) X) {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    (pn : PNorm) : Nonempty (LatticeReduction L g pn) := by
  rcases pn with ⟨q, hq⟩ | _
  · rcases le_or_gt q 2 with hq2 | hq2
    · exact ⟨L.reduction_le_two hg hD hq hq2⟩
    · exact ⟨L.reduction_gt_two hg hD hq hq2⟩
  · exact ⟨L.reduction_inf hg hD⟩

end LatticePrepro

open LatticePrepro
theorem solution {p : ℕ} [Fact p.Prime] {X : Type}
    (L : LinearSystemFamily (ZMod p) X) {g : ℕ} (hg : g < L.blockSize) (hD : 0 < L.numBlocks)
    (pn : PNorm) : Nonempty (LatticeReduction L g pn) :=
  @LatticePrepro.exists_latticeReduction p _ X L g hg hD pn
