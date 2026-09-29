-- Prove2me | solution 1 for Matrix.exists_bifiltered_unimodular_of_forall_block_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/bb09acd9-d23e-5987-892a-f93ece519603

import Mathlib
import Theorems.Thm_FiniteField_exists_forall_affineMap_apply_ne_zero_of_forall_lt
import Theorems.Thm_Matrix_isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_bifiltered_unimodular_of_forall_block_avoidance

set_option autoImplicit false

namespace BIF

open Matrix

theorem linearIndependent_of_forall_notMem_span_lt {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [LinearOrder ι] (v : ι → V) (h : ∀ i, v i ∉ Submodule.span K (v '' {j | j < i})) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s c hs
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁s, hi₁⟩ := hne

  let t : Finset ι := s.filter fun i => c i ≠ 0
  have ht : t.Nonempty := ⟨i₁, Finset.mem_filter.mpr ⟨hi₁s, hi₁⟩⟩
  let i₀ := t.max' ht
  have hi₀t : i₀ ∈ t := Finset.max'_mem t ht
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.mp hi₀t).1
  have hc₀ : c i₀ ≠ 0 := (Finset.mem_filter.mp hi₀t).2
  apply h i₀

  have hsum : c i₀ • v i₀ + ∑ j ∈ s.erase i₀, c j • v j = 0 := by
    rw [← Finset.add_sum_erase s _ hi₀s] at hs; exact hs
  have hmem : ∑ j ∈ s.erase i₀, c j • v j ∈ Submodule.span K (v '' {j | j < i₀}) := by
    refine Submodule.sum_mem _ fun j hj => ?_
    by_cases hcj : c j = 0
    · simp [hcj]
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_, rfl⟩)
      have hjt : j ∈ t := Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hj).2, hcj⟩
      exact lt_of_le_of_ne (Finset.le_max' t j hjt) (Finset.mem_erase.mp hj).1
  have : v i₀ = -((c i₀)⁻¹ • ∑ j ∈ s.erase i₀, c j • v j) := by
    rw [eq_neg_iff_add_eq_zero, ← smul_right_injective V hc₀ |>.eq_iff]
    simp only [smul_add, smul_inv_smul₀ hc₀, smul_zero]
    exact hsum
  rw [this]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem)

section Avatars

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (n : Fin r → ℕ) (d : Fin r → Fin r → ZMod p)

def Uz : Matrix (Fin r) (Fin r) ℤ := fun i j => (p : ℤ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * ((d i j).val : ℤ)

def Lz : Matrix (Fin r) (Fin r) ℤ := fun i j => (p : ℤ) ^ (max 0 ((n j : ℤ) - (n i : ℤ))).toNat * ((d i j).val : ℤ)

theorem Uz_map_cast : (Uz p n d).map (Int.cast : ℤ → ZMod p) = fun i j => if n i ≤ n j then d i j else 0 := by
  ext i j
  simp only [Uz, Matrix.map_apply, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ZMod.natCast_val,
    ZMod.cast_id', id_eq]
  by_cases h : n i ≤ n j
  · have : (max 0 ((n i : ℤ) - (n j : ℤ))).toNat = 0 := by
      rw [max_eq_left (by omega), Int.toNat_zero]
    simp [h, this]
  · have : 0 < (max 0 ((n i : ℤ) - (n j : ℤ))).toNat := by
      rw [max_eq_right (by omega)]; omega
    rw [if_neg h, ZMod.natCast_self, zero_pow this.ne', zero_mul]

theorem Lz_map_cast : (Lz p n d).map (Int.cast : ℤ → ZMod p) = fun i j => if n j ≤ n i then d i j else 0 := by
  ext i j
  simp only [Lz, Matrix.map_apply, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ZMod.natCast_val,
    ZMod.cast_id', id_eq]
  by_cases h : n j ≤ n i
  · have : (max 0 ((n j : ℤ) - (n i : ℤ))).toNat = 0 := by
      rw [max_eq_left (by omega), Int.toNat_zero]
    simp [h, this]
  · have : 0 < (max 0 ((n j : ℤ) - (n i : ℤ))).toNat := by
      rw [max_eq_right (by omega)]; omega
    rw [if_neg h, ZMod.natCast_self, zero_pow this.ne', zero_mul]

def D (c : ℕ) : Matrix {a : Fin r // n a = c} {a : Fin r // n a = c} (ZMod p) := fun i j => d i.1 j.1

theorem blockTriangular_U : Matrix.BlockTriangular ((Uz p n d).map (Int.cast : ℤ → ZMod p)) n := by
  intro i j hij
  rw [Uz_map_cast]
  simp [not_le.mpr hij]

theorem blockTriangular_L :
    Matrix.BlockTriangular ((Lz p n d).map (Int.cast : ℤ → ZMod p)) (fun i => OrderDual.toDual (n i)) := by
  intro i j hij
  rw [Lz_map_cast]
  have : n i < n j := hij
  simp [not_le.mpr this]

theorem det_U_map_cast [DecidableEq ℕ] :
    ((Uz p n d).map (Int.cast : ℤ → ZMod p)).det = ∏ c ∈ Finset.univ.image n, (D p n d c).det := by
  rw [(blockTriangular_U p n d).det]
  refine Finset.prod_congr rfl fun c _ => ?_
  congr 1
  ext i j
  simp only [Matrix.toSquareBlock_def, Uz_map_cast, D, Matrix.of_apply]
  rw [if_pos (by rw [i.2, j.2])]

theorem det_L_map_cast_ne_zero (hD : ∀ c, (D p n d c).det ≠ 0) :
    ((Lz p n d).map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
  classical
  rw [(blockTriangular_L p n d).det, Finset.prod_ne_zero_iff]
  intro c _

  have : ((Lz p n d).map (Int.cast : ℤ → ZMod p)).toSquareBlock (fun i => OrderDual.toDual (n i)) c
      = D p n d (OrderDual.ofDual c) := by
    ext i j
    simp only [Matrix.toSquareBlock_def, Lz_map_cast, D, Matrix.of_apply]
    have hi : n i.1 = OrderDual.ofDual c := i.2
    have hj : n j.1 = OrderDual.ofDual c := j.2
    rw [if_pos (by rw [hi, hj])]
  rw [this]
  exact hD _

theorem det_U_map_cast_ne_zero (hD : ∀ c, (D p n d c).det ≠ 0) :
    ((Uz p n d).map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
  classical
  rw [det_U_map_cast, Finset.prod_ne_zero_iff]
  exact fun c _ => hD c

theorem not_dvd_det_Uz (hD : ∀ c, (D p n d c).det ≠ 0) : ¬ (p : ℤ) ∣ (Uz p n d).det := by
  intro h
  apply det_U_map_cast_ne_zero p n d hD
  have h1 : ((Uz p n d).map (Int.cast : ℤ → ZMod p)).det = ((Uz p n d).det : ZMod p) := by
    rw [show (Uz p n d).map (Int.cast : ℤ → ZMod p) = (Int.castRingHom (ZMod p)).mapMatrix (Uz p n d) from rfl,
      ← RingHom.map_det]
    rfl
  rw [h1, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h]

theorem not_dvd_det_Lz (hD : ∀ c, (D p n d c).det ≠ 0) : ¬ (p : ℤ) ∣ (Lz p n d).det := by
  intro h
  apply det_L_map_cast_ne_zero p n d hD
  have h1 : ((Lz p n d).map (Int.cast : ℤ → ZMod p)).det = ((Lz p n d).det : ZMod p) := by
    rw [show (Lz p n d).map (Int.cast : ℤ → ZMod p) = (Int.castRingHom (ZMod p)).mapMatrix (Lz p n d) from rfl,
      ← RingHom.map_det]
    rfl
  rw [h1, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h]

end Avatars

section Rat

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (n : Fin r → ℕ) (d : Fin r → Fin r → ZMod p)

abbrev U : Matrix (Fin r) (Fin r) ℚ := (Uz p n d).map (Int.cast : ℤ → ℚ)

abbrev L : Matrix (Fin r) (Fin r) ℚ := (Lz p n d).map (Int.cast : ℤ → ℚ)

def N : Matrix (Fin r) (Fin r) ℚ := Matrix.diagonal fun i => (p : ℚ) ^ (n i)
def N' : Matrix (Fin r) (Fin r) ℚ := Matrix.diagonal fun i => ((p : ℚ) ^ (n i))⁻¹

theorem hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem N_mul_N' : N p n * N' p n = 1 := by
  rw [N, N', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  exact mul_inv_cancel₀ (pow_ne_zero _ (hp0 p))

theorem N'_mul_N : N' p n * N p n = 1 := by
  rw [N, N', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i
  exact inv_mul_cancel₀ (pow_ne_zero _ (hp0 p))

theorem U_apply (i j : Fin r) :
    U p n d i j = (p : ℚ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * ((d i j).val : ℚ) := by
  simp [Uz, Matrix.map_apply]

theorem L_apply (i j : Fin r) :
    L p n d i j = (p : ℚ) ^ (max 0 ((n j : ℤ) - (n i : ℤ))).toNat * ((d i j).val : ℚ) := by
  simp [Lz, Matrix.map_apply]

theorem zpow_conj (a b : ℕ) :
    ((p : ℚ) ^ a)⁻¹ * (p : ℚ) ^ (max 0 ((a : ℤ) - (b : ℤ))).toNat * (p : ℚ) ^ b
      = (p : ℚ) ^ (max 0 ((b : ℤ) - (a : ℤ))).toNat := by
  have hp := hp0 p
  rcases le_total a b with h | h
  · have e1 : (max 0 ((a : ℤ) - b)).toNat = 0 := by rw [max_eq_left (by omega)]; rfl
    have e2 : (max 0 ((b : ℤ) - a)).toNat = b - a := by rw [max_eq_right (by omega)]; omega
    rw [e1, e2, pow_zero, mul_one, pow_sub₀ _ hp h, mul_comm]
  · have e1 : (max 0 ((a : ℤ) - b)).toNat = a - b := by rw [max_eq_right (by omega)]; omega
    have e2 : (max 0 ((b : ℤ) - a)).toNat = 0 := by rw [max_eq_left (by omega)]; rfl
    rw [e1, e2, pow_zero, mul_assoc, pow_sub_mul_pow _ h, inv_mul_cancel₀ (pow_ne_zero _ hp)]

theorem L_eq_conj : L p n d = N' p n * U p n d * N p n := by
  ext i j
  rw [N', N, Matrix.mul_diagonal, Matrix.diagonal_mul, U_apply, L_apply]
  rw [show ((p : ℚ) ^ n i)⁻¹ * ((p : ℚ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * ((d i j).val : ℚ)) * (p : ℚ) ^ n j
      = (((p : ℚ) ^ n i)⁻¹ * (p : ℚ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * (p : ℚ) ^ n j) * ((d i j).val : ℚ) by ring,
    zpow_conj]

theorem U_eq_conj : U p n d = N p n * L p n d * N' p n := by
  rw [L_eq_conj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, N_mul_N', Matrix.one_mul, Matrix.mul_assoc, N_mul_N',
    Matrix.mul_one]

theorem U_inv_eq (hL : IsUnit (L p n d)) : (U p n d)⁻¹ = N p n * (L p n d)⁻¹ * N' p n := by
  apply Matrix.inv_eq_right_inv
  have hLdet : IsUnit (L p n d).det := (Matrix.isUnit_iff_isUnit_det _).mp hL
  rw [U_eq_conj]
  calc N p n * L p n d * N' p n * (N p n * (L p n d)⁻¹ * N' p n)
      = N p n * (L p n d * ((N' p n * N p n) * (L p n d)⁻¹)) * N' p n := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [N'_mul_N, Matrix.one_mul, Matrix.mul_nonsing_inv _ hLdet, Matrix.mul_one, N_mul_N']

theorem U_inv_apply (hL : IsUnit (L p n d)) (i j : Fin r) :
    (U p n d)⁻¹ i j = (p : ℚ) ^ (n i) * (L p n d)⁻¹ i j * ((p : ℚ) ^ (n j))⁻¹ := by
  rw [U_inv_eq p n d hL, N, N', Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem filt_U (i j : Fin r) :
    max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U p n d i j) ∨ U p n d i j = 0 := by
  rw [U_apply]
  by_cases h0 : (d i j).val = 0
  · right; simp [h0]
  · left
    have hvpos : 0 < (d i j).val := Nat.pos_of_ne_zero h0
    have hvlt : (d i j).val < p := ZMod.val_lt _
    have hv : padicValRat p ((d i j).val : ℚ) = 0 := by
      rw [padicValRat.of_nat, Nat.cast_eq_zero]
      exact padicValNat.eq_zero_of_not_dvd fun h => Nat.not_lt.mpr (Nat.le_of_dvd hvpos h) hvlt
    have hne : ((d i j).val : ℚ) ≠ 0 := by exact_mod_cast h0
    rw [padicValRat.mul (pow_ne_zero _ (hp0 p)) hne, padicValRat.pow _, padicValRat.self
      (Fact.out : p.Prime).one_lt, hv, mul_one, add_zero]
    exact le_of_eq (Int.toNat_of_nonneg (le_max_left _ _)).symm

theorem filt_U_inv (hL : IsUnit (L p n d)) (hUint : ∀ i j, 0 ≤ padicValRat p ((U p n d)⁻¹ i j))
    (hLint : ∀ i j, 0 ≤ padicValRat p ((L p n d)⁻¹ i j)) (i j : Fin r) :
    max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p ((U p n d)⁻¹ i j) ∨ (U p n d)⁻¹ i j = 0 := by
  by_cases h0 : (U p n d)⁻¹ i j = 0
  · exact Or.inr h0
  · left
    refine max_le (hUint i j) ?_
    have hLne : (L p n d)⁻¹ i j ≠ 0 := by
      intro h; apply h0; rw [U_inv_apply p n d hL, h]; simp
    rw [U_inv_apply p n d hL, padicValRat.mul (mul_ne_zero (pow_ne_zero _ (hp0 p)) hLne)
      (inv_ne_zero (pow_ne_zero _ (hp0 p))), padicValRat.mul (pow_ne_zero _ (hp0 p)) hLne,
      padicValRat.inv, padicValRat.pow _, padicValRat.pow _, padicValRat.self (Fact.out : p.Prime).one_lt]
    have := hLint i j
    push_cast
    linarith

end Rat

section Digits

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (n : Fin r → ℕ)

def e₀ : Fin r → ZMod p := fun j => if (j : ℕ) = 0 then 1 else 0
def fix0 (x : Fin r → Fin r → ZMod p) : Fin r → Fin r → ZMod p := fun i => if (i : ℕ) = 0 then e₀ p else x i

def projc (c : ℕ) : (Fin r → ZMod p) →ₗ[ZMod p] ({a : Fin r // n a = c} → ZMod p) :=
  LinearMap.funLeft (ZMod p) (ZMod p) Subtype.val

theorem projc_apply (c : ℕ) (v : Fin r → ZMod p) (a : {a : Fin r // n a = c}) : projc p n c v a = v a.1 := rfl

theorem projc_surjective (c : ℕ) : Function.Surjective (projc p n c) :=
  LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective

def Wc (c : ℕ) (i : Fin r) (x : Fin r → Fin r → ZMod p) : Submodule (ZMod p) ({a : Fin r // n a = c} → ZMod p) :=
  Submodule.span (ZMod p) ((fun i' => projc p n c (fix0 p x i')) '' {i' | i' < i ∧ n i' = c})

theorem Wc_lt_top (i : Fin r) (x : Fin r → Fin r → ZMod p) : Wc p n (n i) i x < ⊤ := by
  classical
  apply Submodule.lt_top_of_finrank_lt_finrank
  have himg : (fun i' => projc p n (n i) (fix0 p x i')) '' {i' | i' < i ∧ n i' = n i}
      = Set.range (fun i' : {i' : Fin r // i' < i ∧ n i' = n i} => projc p n (n i) (fix0 p x i'.1)) := by
    ext v; simp
  unfold Wc
  rw [himg]
  calc Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range fun i' : {i' : Fin r // i' < i ∧ n i' = n i} =>
          projc p n (n i) (fix0 p x i'.1)))
      ≤ Fintype.card {i' : Fin r // i' < i ∧ n i' = n i} := finrank_range_le_card _
    _ < Fintype.card {a : Fin r // n a = n i} := by

        refine Fintype.card_lt_of_injective_of_notMem (fun i' => (⟨i'.1, i'.2.2⟩ : {a : Fin r // n a = n i}))
          (fun a b h => ?_) (b := ⟨i, rfl⟩) ?_
        · simp only [Subtype.mk.injEq] at h
          exact Subtype.ext h
        · rintro ⟨i', hi'⟩
          simp only [Subtype.mk.injEq] at hi'
          have hlt := i'.2.1
          rw [hi'] at hlt
          exact lt_irrefl i hlt
    _ = Module.finrank (ZMod p) ({a : Fin r // n a = n i} → ZMod p) := by simp

noncomputable def fcOf {M : Type*} [AddCommGroup M] [Module (ZMod p) M] (W : Submodule (ZMod p) M) :
    Module.Dual (ZMod p) M :=
  haveI := Classical.dec (W < ⊤)
  if h : W < ⊤ then Classical.choose (W.exists_le_ker_of_lt_top h) else 0

theorem fcOf_spec {M : Type*} [AddCommGroup M] [Module (ZMod p) M] (W : Submodule (ZMod p) M) (h : W < ⊤) :
    fcOf p W ≠ 0 ∧ W ≤ LinearMap.ker (fcOf p W) := by
  unfold fcOf
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec (W.exists_le_ker_of_lt_top h)

noncomputable def fc (c : ℕ) (i : Fin r) (x : Fin r → Fin r → ZMod p) :
    Module.Dual (ZMod p) ({a : Fin r // n a = c} → ZMod p) :=
  fcOf p (Wc p n c i x)

theorem fc_spec (i : Fin r) (x : Fin r → Fin r → ZMod p) :
    fc p n (n i) i x ≠ 0 ∧ Wc p n (n i) i x ≤ LinearMap.ker (fc p n (n i) i x) :=
  fcOf_spec p _ (Wc_lt_top p n i x)

theorem fix0_fix0 (x : Fin r → Fin r → ZMod p) : fix0 p (fix0 p x) = fix0 p x := by
  funext i; unfold fix0; split_ifs <;> rfl

theorem Wc_fix0 (c : ℕ) (i : Fin r) (x : Fin r → Fin r → ZMod p) : Wc p n c i (fix0 p x) = Wc p n c i x := by
  unfold Wc; rw [fix0_fix0]

theorem fc_fix0 (c : ℕ) (i : Fin r) (x : Fin r → Fin r → ZMod p) : fc p n c i (fix0 p x) = fc p n c i x :=
  congrArg (fcOf p) (Wc_fix0 p n c i x)

theorem Wc_congr (c : ℕ) (i : Fin r) (x x' : Fin r → Fin r → ZMod p) (h : ∀ i', i' < i → x i' = x' i') :
    Wc p n c i x = Wc p n c i x' := by
  unfold Wc
  congr 1
  ext v
  constructor
  · rintro ⟨i', hi', rfl⟩; exact ⟨i', hi', by simp only [fix0, h i' hi'.1]⟩
  · rintro ⟨i', hi', rfl⟩; exact ⟨i', hi', by simp only [fix0, h i' hi'.1]⟩

theorem fc_congr (c : ℕ) (i : Fin r) (x x' : Fin r → Fin r → ZMod p) (h : ∀ i', i' < i → x i' = x' i') :
    fc p n c i x = fc p n c i x' :=
  congrArg (fcOf p) (Wc_congr p n c i x x' h)

end Digits

section Main

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (n : Fin r → ℕ)

theorem exists_digits (hn0 : ∀ i : Fin r, (i : ℕ) = 0 → n i = 0)
    {ι : Fin r → Type*} [∀ i, Fintype (ι i)]
    {V : ∀ i, ι i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module (ZMod p) (V i j)]
    (φ : ∀ i j, (Fin r → ZMod p) →ᵃ[ZMod p] V i j)
    (hφ : ∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, ∃ x, φ i j x ≠ 0)
    (hm : ∀ i, Fintype.card (ι i) + 1 < p) :
    ∃ dg : Fin r → Fin r → ZMod p,
      (∀ i : Fin r, (i : ℕ) = 0 → dg i = e₀ p) ∧
      (∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, φ i j (dg i) ≠ 0) ∧
      (∀ i : Fin r, (i : ℕ) ≠ 0 → fc p n (n i) i dg (projc p n (n i) (dg i)) ≠ 0) ∧
      (∀ i, fix0 p dg i = dg i) := by
  classical

  have hlam : ∀ (i : Fin r) j, ∃ l : Module.Dual (ZMod p) (V i j), (i : ℕ) ≠ 0 → ∃ x, l (φ i j x) ≠ 0 := fun i j => by
    by_cases hi : (i : ℕ) = 0
    · exact ⟨0, fun h => absurd hi h⟩
    · obtain ⟨x, hx⟩ := hφ i hi j
      obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero (ZMod p) hx
      exact ⟨l, fun _ => ⟨x, hl⟩⟩
  choose lam hlam' using hlam

  let one : (Fin r → ZMod p) →ᵃ[ZMod p] ZMod p := AffineMap.const (ZMod p) (Fin r → ZMod p) (1 : ZMod p)
  let ψ : ∀ i : Fin r, (Fin r → Fin r → ZMod p) → (ι i ⊕ Unit) → ((Fin r → ZMod p) →ᵃ[ZMod p] ZMod p) :=
    fun i x => if (i : ℕ) = 0 then fun _ => one else
      Sum.elim (fun j => (lam i j).toAffineMap.comp (φ i j))
        (fun _ => (fc p n (n i) i x).toAffineMap.comp (projc p n (n i)).toAffineMap)
  have hdep : ∀ i (x x' : Fin r → Fin r → ZMod p), (∀ i', i' < i → x i' = x' i') → ψ i x = ψ i x' := by
    intro i x x' hxx'
    by_cases hi : (i : ℕ) = 0
    · simp only [ψ, hi, ↓reduceIte]
    · simp only [ψ, hi, ↓reduceIte, fc_congr p n (n i) i x x' hxx']
  have hψ : ∀ i x o, ∃ y, ψ i x o y ≠ 0 := by
    intro i x o
    by_cases hi : (i : ℕ) = 0
    · exact ⟨0, by simp [ψ, hi, one]⟩
    · cases o with
      | inl j =>
        obtain ⟨y, hy⟩ := hlam' i j hi
        exact ⟨y, by simpa [ψ, hi] using hy⟩
      | inr u =>
        have hne := (fc_spec p n i x).1
        obtain ⟨w, hw⟩ : ∃ w, fc p n (n i) i x w ≠ 0 := by
          by_contra h; push Not at h; exact hne (LinearMap.ext h)
        obtain ⟨y, rfl⟩ := projc_surjective p n (n i) w
        exact ⟨y, by simpa [ψ, hi] using hw⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hm' : ∀ i : Fin r, Fintype.card (ι i ⊕ Unit) < Fintype.card (ZMod p) := fun i => by
    simpa [ZMod.card] using hm i
  obtain ⟨x, hx⟩ := FiniteField.exists_forall_affineMap_apply_ne_zero_of_forall_lt (s := r) (n := fun _ => r)
    (V := fun i (_ : ι i ⊕ Unit) => ZMod p) ψ hdep hψ hm'
  refine ⟨fix0 p x, fun i hi => by simp [fix0, hi], fun i hi j => ?_, fun i hi => ?_, fun i => ?_⟩
  · have := hx i (Sum.inl j)
    simp only [ψ, hi, ↓reduceIte, Sum.elim_inl, AffineMap.coe_comp, Function.comp_apply,
      LinearMap.coe_toAffineMap] at this
    intro h
    apply this
    have : fix0 p x i = x i := by simp [fix0, hi]
    rw [this] at h
    rw [h, map_zero]
  · have := hx i (Sum.inr ())
    simp only [ψ, hi, ↓reduceIte, Sum.elim_inr, AffineMap.coe_comp, Function.comp_apply,
      LinearMap.coe_toAffineMap] at this
    have hxi : fix0 p x i = x i := by simp [fix0, hi]
    rw [fc_fix0, hxi]
    exact this
  · rw [fix0_fix0]

end Main

section Assembly

variable (p : ℕ) [Fact p.Prime] {r : ℕ} (n : Fin r → ℕ)

theorem rows_linearIndependent (hn0 : ∀ i : Fin r, (i : ℕ) = 0 → n i = 0) (dg : Fin r → Fin r → ZMod p)
    (h0 : ∀ i : Fin r, (i : ℕ) = 0 → dg i = e₀ p)
    (hblk : ∀ i : Fin r, (i : ℕ) ≠ 0 → fc p n (n i) i dg (projc p n (n i) (dg i)) ≠ 0)
    (hfix : ∀ i, fix0 p dg i = dg i) (c : ℕ) :
    LinearIndependent (ZMod p) (fun a : {a : Fin r // n a = c} => projc p n c (dg a.1)) := by
  classical
  apply linearIndependent_of_forall_notMem_span_lt
  rintro ⟨a, ha⟩ hmem
  subst ha
  by_cases ha0 : (a : ℕ) = 0
  ·
    have hempty : (fun b : {b : Fin r // n b = n a} => projc p n (n a) (dg b.1)) '' {j | j < ⟨a, rfl⟩} = ∅ := by
      rw [Set.image_eq_empty]
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      change a ≤ j.1
      rw [Fin.le_def, ha0]
      exact Nat.zero_le _
    rw [hempty, Submodule.span_empty, Submodule.mem_bot] at hmem
    have := congrFun hmem ⟨a, rfl⟩
    rw [projc_apply, h0 a ha0] at this
    simp [e₀, ha0] at this
  · have hW : projc p n (n a) (dg a) ∉ Wc p n (n a) a dg := fun hin =>
      hblk a ha0 ((fc_spec p n a dg).2 hin)
    apply hW
    unfold Wc
    refine Submodule.span_mono ?_ hmem
    rintro _ ⟨⟨j, hj⟩, hjlt, rfl⟩
    exact ⟨j, ⟨hjlt, hj⟩, by simp [hfix]⟩

theorem isUnit_det_D (hn0 : ∀ i : Fin r, (i : ℕ) = 0 → n i = 0) (dg : Fin r → Fin r → ZMod p)
    (h0 : ∀ i : Fin r, (i : ℕ) = 0 → dg i = e₀ p)
    (hblk : ∀ i : Fin r, (i : ℕ) ≠ 0 → fc p n (n i) i dg (projc p n (n i) (dg i)) ≠ 0)
    (hfix : ∀ i, fix0 p dg i = dg i) (c : ℕ) :
    IsUnit (D p n dg c).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
  exact rows_linearIndependent p n hn0 dg h0 hblk hfix c

end Assembly

end BIF

theorem solution
    (p : ℕ) [Fact p.Prime] {r : ℕ} (n : Fin r → ℕ) (hn0 : ∀ i : Fin r, (i : ℕ) = 0 → n i = 0)
    {ι : Fin r → Type*} [∀ i, Fintype (ι i)]
    {V : ∀ i, ι i → Type*} [∀ i j, AddCommGroup (V i j)] [∀ i j, Module (ZMod p) (V i j)]
    (φ : ∀ i j, (Fin r → ZMod p) →ᵃ[ZMod p] V i j)
    (hφ : ∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, ∃ x, φ i j x ≠ 0)
    (hm : ∀ i, Fintype.card (ι i) + 1 < p) :
    ∃ (U : Matrix (Fin r) (Fin r) ℚ) (d : Fin r → Fin r → ZMod p),
      IsUnit U ∧
      (∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U i j) ∨ U i j = 0) ∧
      (∀ i j, max 0 ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U⁻¹ i j) ∨ U⁻¹ i j = 0) ∧
      (∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0) ∧
      (∀ i j, U i j = (p : ℚ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * ((d i j).val : ℚ)) ∧
      (∀ c : ℕ, IsUnit (Matrix.det (Matrix.of fun (i j : {a : Fin r // n a = c}) => d i.1 j.1))) ∧
      (∀ i : Fin r, (i : ℕ) ≠ 0 → ∀ j, φ i j (d i) ≠ 0) := by
  classical
  obtain ⟨dg, h0, havoid, hblk, hfix⟩ := BIF.exists_digits p n hn0 φ hφ hm
  have hD : ∀ c, IsUnit (BIF.D p n dg c).det := BIF.isUnit_det_D p n hn0 dg h0 hblk hfix
  have hD' : ∀ c, (BIF.D p n dg c).det ≠ 0 := fun c => (hD c).ne_zero
  obtain ⟨hU, hUint⟩ := Matrix.isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det p (BIF.Uz p n dg)
    (BIF.not_dvd_det_Uz p n dg hD')
  obtain ⟨hL, hLint⟩ := Matrix.isUnit_and_padicValRat_inv_nonneg_of_not_dvd_det p (BIF.Lz p n dg)
    (BIF.not_dvd_det_Lz p n dg hD')
  refine ⟨BIF.U p n dg, dg, hU, BIF.filt_U p n dg, BIF.filt_U_inv p n dg hL hUint hLint, fun i j hi => ?_,
    BIF.U_apply p n dg, fun c => ?_, havoid⟩
  ·
    rw [BIF.U_apply, h0 i hi, hn0 i hi]
    simp only [BIF.e₀, Nat.cast_zero, zero_sub]
    rw [max_eq_left (by omega), Int.toNat_zero, pow_zero, one_mul]
    split_ifs with hj <;> simp [ZMod.val_one]
  · exact hD c

end S_Matrix_exists_bifiltered_unimodular_of_forall_block_avoidance
end P2MW
export P2MW.S_Matrix_exists_bifiltered_unimodular_of_forall_block_avoidance (solution)
