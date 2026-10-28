-- Prove2me | solution 2 for KAdaptability.Bilinear.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T06:14:00.979422+00:00
-- url     : https://prove2.me/submissions/7a6f1591-8584-4741-8381-be58f33fbed4

import Mathlib
import Definitions.Def_KAdaptability_Bilinear_Program7
import Theorems.Thm_LP_exists_dual_of_isBounded
import Theorems.Thm_LP_farkas
import Theorems.Thm_LP_strong_duality_matrix

-- carved verbatim out of submission 26c152cf-78b5-4775-a67c-8090f7f24a33, lines 1152-1175

section
open Matrix
open KAdaptability.Bilinear KAdaptability.Bilinear.Problem
variable {N M L nQ R K : ℕ} (P : Problem N M L nQ R)

theorem Hrow_zero (ℓ : Fin K → Fin (L + 1)) (k : Fin K) (h : ℓ k = 0) : P.Hrow ℓ k = 0 := by
  simp [Hrow, h]

abbrev Row (K L R : ℕ) := Fin K ⊕ (Fin R ⊕ ((Fin K × Fin L) ⊕ Fin K))

def g (ℓ : Fin K → Fin (L + 1)) (k : Fin K) : ℝ := if ℓ k = 0 then 1 else 0

def Mb (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) :
    Matrix (Row K L R) (Option (Fin nQ)) ℝ := Matrix.of fun i o =>
  match i, o with
  | Sum.inl k, none => g ℓ k
  | Sum.inl k, some q => -(g ℓ k * (P.Q *ᵥ y k) q)
  | Sum.inr (Sum.inl _), none => 0
  | Sum.inr (Sum.inl r), some q => P.A r q
  | Sum.inr (Sum.inr (Sum.inl _)), none => 0
  | Sum.inr (Sum.inr (Sum.inl p)), some q => -(g ℓ p.1 * P.H p.2 q)
  | Sum.inr (Sum.inr (Sum.inr _)), none => 0
  | Sum.inr (Sum.inr (Sum.inr k)), some q => P.Hrow ℓ k q

def wlam (ℓ : Fin K → Fin (L + 1)) (w : Row K L R → ℝ) : Fin K → ℝ := fun k => g ℓ k * w (Sum.inl k)

theorem I1 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (w : Row K L R → ℝ) :
    ((Mb P y ℓ)ᵀ *ᵥ w) none = ∑ k, wlam ℓ w k := by
  simp [Mb, mulVec, dotProduct, Fintype.sum_sum_type, wlam]

def wα (w : Row K L R → ℝ) : Fin R → ℝ := fun r => w (Sum.inr (Sum.inl r))

def wβ (w : Row K L R → ℝ) : Fin K → Fin L → ℝ := fun k i => w (Sum.inr (Sum.inr (Sum.inl (k, i))))

def wγ (w : Row K L R → ℝ) : Fin K → ℝ := fun k => w (Sum.inr (Sum.inr (Sum.inr k)))

theorem I2 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (w : Row K L R → ℝ) (q : Fin nQ) :
    ((Mb P y ℓ)ᵀ *ᵥ w) (some q) = P.dualLhsBdry ℓ (wα w) (wβ w) (wγ w) q
      - (∑ k, wlam ℓ w k • (P.Q *ᵥ y k)) q := by
  simp only [Mb, mulVec, dotProduct, Fintype.sum_sum_type, transpose_apply, of_apply,
    dualLhsBdry, Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_filter, Fintype.sum_prod_type, wα, wγ, wlam]
  have h1 : ∑ x, -(g ℓ x * ∑ x_1, P.Q q x_1 * y x x_1) * w (Sum.inl x) =
      -∑ x, g ℓ x * w (Sum.inl x) * ∑ x_1, P.Q q x_1 * y x x_1 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ x, ∑ x_1, -(g ℓ x * P.H x_1 q) * w (Sum.inr (Sum.inr (Sum.inl (x, x_1)))) =
      -∑ c, (if ℓ c = 0 then P.Hᵀ *ᵥ wβ w c else 0) q := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ℓ c = 0
    · simp only [hc, if_true, g, mulVec, dotProduct, transpose_apply, wβ, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    · simp [hc, g]
  have h3 : ∑ x, P.Hrow ℓ x q * w (Sum.inr (Sum.inr (Sum.inr x))) =
      ∑ c, (if ℓ c ≠ 0 then w (Sum.inr (Sum.inr (Sum.inr c))) • P.Hrow ℓ c else 0) q := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ℓ c = 0
    · simp [hc, Hrow_zero P ℓ c hc]
    · simp [hc, mul_comm]
  rw [h1, h2, h3]
  ring

def bb (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) :
    Row K L R → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl r) => P.b r
  | Sum.inr (Sum.inr (Sum.inl p)) => -(g ℓ p.1 * P.lhs x (y p.1) p.2)
  | Sum.inr (Sum.inr (Sum.inr k)) => (1 - g ℓ k) * (P.lhsRow x y ℓ k - ε)

theorem I3 (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (w : Row K L R → ℝ) :
    bb P ε x y ℓ ⬝ᵥ w = P.dualObjBdry ε x y ℓ (wα w) (wβ w) (wγ w) := by
  simp only [bb, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, dualObjBdry,
    Finset.sum_filter, wα, wβ, wγ, zero_mul, Finset.sum_const_zero, zero_add]
  have h2 : ∑ x_1, ∑ x_2, -(g ℓ x_1 * P.lhs x (y x_1) x_2) * w (Sum.inr (Sum.inr (Sum.inl (x_1, x_2))))
      = -∑ c, if ℓ c = 0 then P.lhs x (y c) ⬝ᵥ (fun i => w (Sum.inr (Sum.inr (Sum.inl (c, i))))) else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ℓ c = 0
    · simp only [hc, if_true, g, dotProduct, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    · simp [hc, g]
  have h3 : ∑ x_1, (1 - g ℓ x_1) * (P.lhsRow x y ℓ x_1 - ε) * w (Sum.inr (Sum.inr (Sum.inr x_1)))
      = ∑ c, if ℓ c ≠ 0 then (P.lhsRow x y ℓ c - ε) * w (Sum.inr (Sum.inr (Sum.inr c))) else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : ℓ c = 0
    · simp [hc, g]
    · simp [hc, g]
  rw [h2, h3]
  simp only [dotProduct]
  ring

theorem Mb_row1 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (v : Option (Fin nQ) → ℝ)
    (k : Fin K) :
    (Mb (R := R) P y ℓ *ᵥ v) (Sum.inl k) =
      g ℓ k * (v none - P.secondCost (fun q => v (some q)) (y k)) := by
  simp only [Mb, mulVec, dotProduct, Fintype.sum_option, of_apply, secondCost]
  rw [mul_sub, Finset.mul_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]
  have : ∀ i, g ℓ k * (∑ x, P.Q i x * y k x) * v (some i) = g ℓ k * (v (some i) * ∑ x, P.Q i x * y k x) :=
    fun i => by ring
  simp only [this]
  ring

theorem Mb_row2 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (v : Option (Fin nQ) → ℝ)
    (r : Fin R) :
    (Mb P y ℓ *ᵥ v) (Sum.inr (Sum.inl r)) = (P.A *ᵥ fun q => v (some q)) r := by
  simp [Mb, mulVec, dotProduct, Fintype.sum_option]

theorem Mb_row3 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (v : Option (Fin nQ) → ℝ)
    (k : Fin K) (i : Fin L) :
    (Mb (R := R) P y ℓ *ᵥ v) (Sum.inr (Sum.inr (Sum.inl (k, i)))) =
      -(g ℓ k * P.rhs (fun q => v (some q)) i) := by
  simp only [Mb, mulVec, dotProduct, Fintype.sum_option, of_apply, rhs, zero_mul, zero_add,
    neg_mul, Finset.sum_neg_distrib, Finset.mul_sum, mul_assoc]

theorem Mb_row4 (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) (v : Option (Fin nQ) → ℝ)
    (k : Fin K) :
    (Mb (R := R) P y ℓ *ᵥ v) (Sum.inr (Sum.inr (Sum.inr k))) =
      P.Hrow ℓ k ⬝ᵥ (fun q => v (some q)) := by
  simp [Mb, mulVec, dotProduct, Fintype.sum_option]

def Mp (ℓ : Fin K → Fin (L + 1)) : Matrix (Fin R ⊕ Fin K) (Fin nQ) ℝ := Matrix.of fun i q =>
  match i with
  | Sum.inl r => P.A r q
  | Sum.inr k => P.Hrow ℓ k q

theorem MpT (ℓ : Fin K → Fin (L + 1)) (w : Fin R ⊕ Fin K → ℝ) :
    (Mp P ℓ)ᵀ *ᵥ w = P.Aᵀ *ᵥ (fun r => w (Sum.inl r)) + ∑ k, w (Sum.inr k) • P.Hrow ℓ k := by
  funext q
  simp [Mp, mulVec, dotProduct, Fintype.sum_sum_type, Finset.sum_apply, mul_comm]

theorem hrow_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (k : Fin K) (h : ℓ k ≠ 0) (ξ : Fin nQ → ℝ) :
    (∀ i : Fin L, ℓ k = i.succ → P.rhs ξ i + ε ≤ P.lhs x (y k) i) ↔
      P.Hrow ℓ k ⬝ᵥ ξ + ε ≤ P.lhsRow x y ℓ k := by
  simp only [Hrow, lhsRow, h, dite_false]
  constructor
  · intro hh
    exact hh _ (Fin.succ_pred _ h).symm
  · intro hh i hi
    have hp : (ℓ k).pred h = i := by simp [hi]
    rw [hp] at hh
    exact hh

theorem XiEps_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (ξ : Fin nQ → ℝ) :
    ξ ∈ P.XiEps ε x y ℓ ↔ (∀ r, (P.A *ᵥ ξ) r ≤ P.b r) ∧
      (∀ k i, ℓ k = 0 → P.lhs x (y k) i ≤ P.rhs ξ i) ∧
      ∀ k, ℓ k ≠ 0 → P.Hrow ℓ k ⬝ᵥ ξ + ε ≤ P.lhsRow x y ℓ k := by
  simp only [XiEps, Xi, Set.mem_ofPred_eq, Pi.le_def]
  refine and_congr Iff.rfl (and_congr ⟨fun h k i hk => h k hk i, fun h k hk i => h k i hk⟩ ?_)
  refine forall_congr' fun k => ?_
  by_cases hk : ℓ k = 0
  · simp only [hk, ne_eq, not_true_eq_false, IsEmpty.forall_iff, iff_true]
    intro i hi
    exact absurd hi.symm (Fin.succ_ne_zero i)
  · rw [hrow_iff P ε x y ℓ k hk ξ]
    exact ⟨fun h _ => h, fun h => h hk⟩

def bp (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1)) :
    Fin R ⊕ Fin K → ℝ
  | Sum.inl r => P.b r
  | Sum.inr k => P.lhsRow x y ℓ k - ε

theorem Mp_feas (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hℓ : ∀ k, ℓ k ≠ 0) (ξ : Fin nQ → ℝ) :
    Mp P ℓ *ᵥ ξ ≤ bp P ε x y ℓ ↔ ξ ∈ P.XiEps ε x y ℓ := by
  rw [XiEps_iff, Pi.le_def, Sum.forall]
  simp only [Mp, bp, hℓ, false_imp_iff, implies_true, true_and, ne_eq, not_false_eq_true,
    true_imp_iff]
  refine and_congr Iff.rfl (forall_congr' fun k => ?_)
  simp only [mulVec, of_apply]
  constructor <;> intro h <;> linarith

theorem bracket_eq (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hZ : (Finset.univ.filter fun k => ℓ k = 0).Nonempty) (ξ : Fin nQ → ℝ) :
    P.bracket x y ℓ ξ = ((P.firstCost ξ x +
      (Finset.univ.filter fun k => ℓ k = 0).inf' hZ (fun k => P.secondCost ξ (y k)) : ℝ) : EReal) := by
  rw [bracket, EReal.coe_add]
  congr 1
  apply le_antisymm
  · obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' hZ (fun k => P.secondCost ξ (y k))
    rw [hkeq]
    exact iInf₂_le k (by simpa using hk)
  · refine le_iInf₂ fun k hk => EReal.coe_le_coe_iff.2 (Finset.inf'_le _ ?_)
    simpa using hk

def cb (x : Fin N → ℝ) : Option (Fin nQ) → ℝ
  | none => 1
  | some q => (P.C *ᵥ x) q

theorem cb_dot (x : Fin N → ℝ) (v : Option (Fin nQ) → ℝ) :
    cb P x ⬝ᵥ v = v none + P.firstCost (fun q => v (some q)) x := by
  simp [cb, dotProduct, Fintype.sum_option, firstCost, mul_comm]

theorem dual_iff (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (w : Row K L R → ℝ) :
    (Mb P y ℓ)ᵀ *ᵥ w = cb P x ↔ ∑ k, wlam ℓ w k = 1 ∧
      P.dualLhsBdry ℓ (wα w) (wβ w) (wγ w) = P.costVec x y (wlam ℓ w) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congr_fun h none
      rwa [I1] at this
    · funext q
      have := congr_fun h (some q)
      rw [I2] at this
      simp only [cb] at this
      simp only [costVec, Pi.add_apply]
      linarith
  · rintro ⟨h1, h2⟩
    funext o
    cases o with
    | none => rw [I1, h1]; rfl
    | some q =>
      rw [I2, h2]
      simp [costVec, cb]

end

section
open Matrix

def dl {n : Type*} [Fintype n] (u : n → ℝ) : Module.Dual ℝ (n → ℝ) where
  toFun ξ := u ⬝ᵥ ξ
  map_add' a b := dotProduct_add u a b
  map_smul' c a := by simp [dotProduct_smul]

theorem dl_apply {n : Type*} [Fintype n] (u ξ : n → ℝ) : dl u ξ = u ⬝ᵥ ξ := rfl

theorem farkas_mat {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (b : m → ℝ) (h : ¬ ∃ x, M *ᵥ x ≤ b) :
    ∃ y, 0 ≤ y ∧ Mᵀ *ᵥ y = 0 ∧ b ⬝ᵥ y < 0 := by
  have h' : ¬ ∃ x : n → ℝ, (∀ i, dl (M i) x ≤ b i) ∧
      ∀ j : Empty, (0 : Module.Dual ℝ (n → ℝ)) x = (0 : Empty → ℝ) j := by
    rintro ⟨x, hx, -⟩
    exact h ⟨x, fun i => by simpa [dl_apply, mulVec] using hx i⟩
  obtain ⟨y, z, hy, hsum, hneg⟩ := (LP.farkas (fun i => dl (M i)) b
    (fun _ : Empty => (0 : Module.Dual ℝ (n → ℝ))) (fun _ => 0)).1 h'
  refine ⟨y, hy, ?_, ?_⟩
  · funext j
    have := LinearMap.congr_fun hsum (Pi.single j 1)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, LinearMap.sum_apply,
      LinearMap.smul_apply, dl_apply, LinearMap.zero_apply] at this
    simp only [mulVec, dotProduct, transpose_apply, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [dotProduct_single, mul_comm]
  · simpa [dotProduct_comm] using hneg

theorem dual_le_of_bound {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) (τ : ℝ)
    (hD : ∃ y, 0 ≤ y ∧ Mᵀ *ᵥ y = c) (H : ∀ x, M *ᵥ x ≤ b → c ⬝ᵥ x ≤ τ) :
    ∃ y, 0 ≤ y ∧ Mᵀ *ᵥ y = c ∧ b ⬝ᵥ y ≤ τ := by
  by_cases hP : ∃ x, M *ᵥ x ≤ b
  · obtain ⟨x, y, hx, hy, hc, heq, -⟩ := LP.strong_duality_matrix M b c hP hD
    exact ⟨y, hy, hc, heq ▸ H x hx⟩
  · obtain ⟨y0, hy0, hc0⟩ := hD
    obtain ⟨z, hz, hMz, hbz⟩ := farkas_mat M b hP
    set s : ℝ := max 0 ((b ⬝ᵥ y0 - τ) / (-(b ⬝ᵥ z))) with hs
    have hs0 : 0 ≤ s := le_max_left _ _
    refine ⟨y0 + s • z, add_nonneg hy0 (smul_nonneg hs0 hz), ?_, ?_⟩
    · rw [mulVec_add, mulVec_smul, hMz, smul_zero, add_zero, hc0]
    · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have h1 : (b ⬝ᵥ y0 - τ) / (-(b ⬝ᵥ z)) ≤ s := le_max_right _ _
      have hpos : 0 < -(b ⬝ᵥ z) := by linarith
      rw [div_le_iff₀ hpos] at h1
      nlinarith

end

section
open Matrix
open KAdaptability.Bilinear KAdaptability.Bilinear.Problem
variable {N M L nQ R K : ℕ} (P : Problem N M L nQ R)

theorem feas_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (v : Option (Fin nQ) → ℝ) :
    Mb (R := R) P y ℓ *ᵥ v ≤ bb P ε x y ℓ ↔
      (∀ k, ℓ k = 0 → v none ≤ P.secondCost (fun q => v (some q)) (y k)) ∧
        (fun q => v (some q)) ∈ P.XiEps ε x y ℓ := by
  rw [XiEps_iff, Pi.le_def]
  simp only [Sum.forall, Prod.forall, Mb_row1, Mb_row2, Mb_row3, Mb_row4, bb]
  refine and_congr (forall_congr' fun k => ?_) (and_congr Iff.rfl
    (and_congr (forall_congr' fun k => forall_congr' fun i => ?_) (forall_congr' fun k => ?_)))
  · by_cases hk : ℓ k = 0
    · simp only [g, hk, if_true, one_mul, true_imp_iff]; constructor <;> intro h <;> linarith
    · simp [g, hk]
  · by_cases hk : ℓ k = 0
    · simp only [g, hk, if_true, one_mul, true_imp_iff, neg_le_neg_iff]
    · simp [g, hk]
  · by_cases hk : ℓ k = 0
    · simp [g, hk, Hrow_zero P ℓ k hk]
    · simp only [g, hk, if_false, sub_zero, one_mul, ne_eq, not_false_eq_true, true_imp_iff]
      constructor <;> intro h <;> linarith

end

section
open Matrix

theorem weak_mat {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (b : m → ℝ) (c x : n → ℝ) (y : m → ℝ) (hx : M *ᵥ x ≤ b)
    (hy : 0 ≤ y) (hc : Mᵀ *ᵥ y = c) : c ⬝ᵥ x ≤ b ⬝ᵥ y := by
  rw [← hc, mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm b]
  exact dotProduct_le_dotProduct_of_nonneg_left hx hy

end

section
open Matrix
open KAdaptability.Bilinear KAdaptability.Bilinear.Problem
variable {N M L nQ R K : ℕ} (P : Problem N M L nQ R)

theorem bdry_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hℓ : ∃ k, ℓ k = 0) (τ : ℝ) :
    (∃ (lam : Fin K → ℝ) (α : Fin R → ℝ) (β : Fin K → Fin L → ℝ) (γ : Fin K → ℝ),
      lam ∈ DeltaK ℓ ∧ P.DualBdry ε x y ℓ lam τ α β γ) ↔
      ∀ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ ≤ (τ : EReal) := by
  classical
  obtain ⟨k0, hk0⟩ := hℓ
  have hZ : (Finset.univ.filter fun k => ℓ k = 0).Nonempty := ⟨k0, by simp [hk0]⟩
  constructor
  · rintro ⟨lam, α, β, γ, hΔ, hD⟩ ξ hξ
    let w : Row K L R → ℝ := Sum.elim lam (Sum.elim α (Sum.elim (fun p => β p.1 p.2) γ))
    have hwl : wlam ℓ w = lam := by
      funext k
      by_cases hk : ℓ k = 0
      · simp [wlam, g, hk, w]
      · simp [wlam, g, hk, hΔ.2.2 k hk]
    have hw : 0 ≤ w := by
      intro i
      rcases i with k | r | p | k
      · exact hΔ.1 k
      · exact hD.1 r
      · exact hD.2.1 p.1 p.2
      · exact hD.2.2.1 k
    have hc : (Mb P y ℓ)ᵀ *ᵥ w = cb P x :=
      (dual_iff P x y ℓ w).2 ⟨by rw [hwl]; exact hΔ.2.1, by rw [hwl]; exact hD.2.2.2.2⟩
    have hb : bb P ε x y ℓ ⬝ᵥ w ≤ τ := by rw [I3]; exact hD.2.2.2.1
    let t : ℝ := (Finset.univ.filter fun k => ℓ k = 0).inf' hZ (fun k => P.secondCost ξ (y k))
    let v : Option (Fin nQ) → ℝ := fun o => o.elim t ξ
    have hv : Mb P y ℓ *ᵥ v ≤ bb P ε x y ℓ := by
      refine (feas_iff P ε x y ℓ v).2 ⟨fun k hk => ?_, hξ⟩
      exact Finset.inf'_le _ (by simp [hk])
    have hwk := weak_mat _ _ _ _ _ hv hw hc
    rw [cb_dot] at hwk
    rw [bracket_eq P x y ℓ hZ, EReal.coe_le_coe_iff]
    change t + P.firstCost ξ x ≤ bb P ε x y ℓ ⬝ᵥ w at hwk
    linarith
  · intro H
    have H' : ∀ v, Mb (R := R) P y ℓ *ᵥ v ≤ bb P ε x y ℓ → cb P x ⬝ᵥ v ≤ τ := by
      intro v hv
      obtain ⟨hk, hξ⟩ := (feas_iff P ε x y ℓ v).1 hv
      have h1 := H _ hξ
      rw [bracket_eq P x y ℓ hZ, EReal.coe_le_coe_iff] at h1
      have h2 : v none ≤ (Finset.univ.filter fun k => ℓ k = 0).inf' hZ
          (fun k => P.secondCost (fun q => v (some q)) (y k)) :=
        Finset.le_inf' _ _ fun k hk' => hk k (by simpa using hk')
      rw [cb_dot]
      linarith
    have hD : ∃ w, 0 ≤ w ∧ (Mb (R := R) P y ℓ)ᵀ *ᵥ w = cb P x := by
      obtain ⟨α0, hα0, hAα0⟩ := LP.exists_dual_of_isBounded P.A P.b P.Xi_nonempty
        P.Xi_bounded (P.C *ᵥ x + P.Q *ᵥ y k0)
      let w0 : Row K L R → ℝ :=
        Sum.elim (fun k => if k = k0 then 1 else 0) (Sum.elim α0 0)
      have hwl : wlam ℓ w0 = fun k => if k = k0 then 1 else 0 := by
        funext k
        by_cases hk : k = k0
        · subst hk; simp [wlam, g, hk0, w0]
        · simp [wlam, hk, w0]
      refine ⟨w0, ?_, (dual_iff P x y ℓ w0).2 ⟨?_, ?_⟩⟩
      · intro i
        rcases i with k | r | p | k
        · by_cases hk : k = k0 <;> simp [w0, hk]
        · exact hα0 r
        · exact le_refl 0
        · exact le_refl 0
      · rw [hwl]; simp
      · rw [hwl]
        have hβ : wβ w0 = 0 := rfl
        have hγ : wγ w0 = 0 := rfl
        have hα : wα w0 = α0 := rfl
        rw [hβ, hγ, hα]
        simp [dualLhsBdry, costVec, hAα0, ite_smul]
    obtain ⟨w, hw, hc, hb⟩ := dual_le_of_bound _ _ _ τ hD H'
    obtain ⟨hsum, heq⟩ := (dual_iff P x y ℓ w).1 hc
    refine ⟨wlam ℓ w, wα w, wβ w, wγ w, ⟨?_, hsum, ?_⟩, ?_, ?_, ?_, ?_, heq⟩
    · intro k
      exact mul_nonneg (by unfold g; split_ifs <;> norm_num) (hw _)
    · intro k hk
      simp [wlam, g, hk]
    · exact fun r => hw _
    · exact fun k i => hw _
    · exact fun k => hw _
    · rw [← I3]; exact hb

theorem bp_dot (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (w : Fin R ⊕ Fin K → ℝ) :
    bp P ε x y ℓ ⬝ᵥ w = P.b ⬝ᵥ (fun r => w (Sum.inl r)) +
      ∑ k, (P.lhsRow x y ℓ k - ε) * w (Sum.inr k) := by
  simp [bp, dotProduct, Fintype.sum_sum_type]

theorem bracket_top (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hℓ : ∀ k, ℓ k ≠ 0) (ξ : Fin nQ → ℝ) : P.bracket x y ℓ ξ = ⊤ := by
  simp [bracket, hℓ]

theorem plus_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (hℓ : ∀ k, ℓ k ≠ 0) :
    (∃ (α : Fin R → ℝ) (γ : Fin K → ℝ), P.PlusBlock ε x y ℓ α γ) ↔
      P.XiEps ε x y ℓ = ∅ := by
  constructor
  · rintro ⟨α, γ, hα, hγ, hobj, heq⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro ξ hξ
    have hw : (0 : Fin R ⊕ Fin K → ℝ) ≤ Sum.elim α γ := by
      intro i; rcases i with r | k
      · exact hα r
      · exact hγ k
    have hc : (Mp P ℓ)ᵀ *ᵥ Sum.elim α γ = 0 := by
      rw [MpT]; exact heq
    have := weak_mat _ _ _ _ _ ((Mp_feas P ε x y ℓ hℓ ξ).2 hξ) hw hc
    rw [bp_dot, zero_dotProduct] at this
    simp only [Sum.elim_inl, Sum.elim_inr] at this
    change 0 ≤ P.b ⬝ᵥ α + ∑ k, (P.lhsRow x y ℓ k - ε) * γ k at this
    linarith
  · intro h
    have hP : ¬ ∃ ξ, Mp P ℓ *ᵥ ξ ≤ bp P ε x y ℓ := by
      rintro ⟨ξ, hξ⟩
      have := (Mp_feas P ε x y ℓ hℓ ξ).1 hξ
      rw [h] at this
      exact this
    obtain ⟨z, hz, hMz, hbz⟩ := farkas_mat _ _ hP
    set s : ℝ := -1 / (bp P ε x y ℓ ⬝ᵥ z) with hs
    have hs0 : 0 ≤ s := by
      rw [hs]; exact div_nonneg_of_nonpos (by norm_num) hbz.le
    have hsb : s * (bp P ε x y ℓ ⬝ᵥ z) = -1 := by
      rw [hs]; field_simp [hbz.ne]
    have hw : 0 ≤ s • z := smul_nonneg hs0 hz
    have hc : (Mp P ℓ)ᵀ *ᵥ (s • z) = 0 := by rw [mulVec_smul, hMz, smul_zero]
    have hb : bp P ε x y ℓ ⬝ᵥ (s • z) = -1 := by rw [dotProduct_smul, smul_eq_mul, hsb]
    rw [MpT] at hc
    rw [bp_dot] at hb
    refine ⟨fun r => (s • z) (Sum.inl r), fun k => (s • z) (Sum.inr k), fun r => hw _,
      fun k => hw _, le_of_eq hb, hc⟩

theorem loc_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (τ : ℝ) :
    (∃ t : (Fin K → ℝ) × (Fin R → ℝ) × (Fin K → Fin L → ℝ) × (Fin K → ℝ),
      (ℓ ∈ LBdry K L → t.1 ∈ DeltaK ℓ ∧ P.DualBdry ε x y ℓ t.1 τ t.2.1 t.2.2.1 t.2.2.2) ∧
      (ℓ ∈ LPlus K L → P.PlusBlock ε x y ℓ t.2.1 t.2.2.2)) ↔
      ∀ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ ≤ (τ : EReal) := by
  by_cases hB : ∃ k, ℓ k = 0
  · have hnP : ℓ ∉ LPlus K L := by
      obtain ⟨k, hk⟩ := hB
      exact fun h => h k hk
    rw [← bdry_iff P ε x y ℓ hB τ]
    constructor
    · rintro ⟨t, h1, -⟩
      exact ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, h1 hB⟩
    · rintro ⟨lam, α, β, γ, h⟩
      exact ⟨(lam, α, β, γ), fun _ => h, fun h' => absurd h' hnP⟩
  · simp only [not_exists] at hB
    have hnB : ℓ ∉ LBdry K L := by
      rintro ⟨k, hk⟩; exact hB k hk
    have hR : (∀ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ ≤ (τ : EReal)) ↔
        P.XiEps ε x y ℓ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      refine forall_congr' fun ξ => ?_
      rw [bracket_top P x y ℓ hB]
      simp
    rw [hR, ← plus_iff P ε x y ℓ hB]
    constructor
    · rintro ⟨t, -, h2⟩
      exact ⟨t.2.1, t.2.2.2, h2 hB⟩
    · rintro ⟨α, γ, h⟩
      exact ⟨(0, α, 0, γ), fun h' => absurd h' hnB, fun _ => h⟩

theorem feas7_iff (ε : ℝ) (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (τ : ℝ) :
    P.Feasible7 ε x y τ ↔ P.obj6Eps ε x y ≤ (τ : EReal) := by
  simp only [obj6Eps, iSup_le_iff]
  rw [show (∀ ℓ, ∀ ξ ∈ P.XiEps ε x y ℓ, P.bracket x y ℓ ξ ≤ (τ : EReal)) ↔ _ from
    forall_congr' fun ℓ => (loc_iff P ε x y ℓ τ).symm]
  constructor
  · rintro ⟨lam, α, β, γ, h1, h2⟩ ℓ
    exact ⟨(lam ℓ, α ℓ, β ℓ, γ ℓ), h1 ℓ, h2 ℓ⟩
  · intro h
    choose f hf using h
    exact ⟨fun ℓ => (f ℓ).1, fun ℓ => (f ℓ).2.1, fun ℓ => (f ℓ).2.2.1, fun ℓ => (f ℓ).2.2.2,
      fun ℓ => (hf ℓ).1, fun ℓ => (hf ℓ).2⟩

theorem sInf_upper (φ : EReal) :
    sInf ((fun τ : ℝ => (τ : EReal)) '' {τ | φ ≤ (τ : EReal)}) = φ := by
  apply le_antisymm
  · induction φ using EReal.rec with
    | bot =>
      refine le_of_eq ((EReal.eq_bot_iff_forall_lt _).2 fun r => ?_)
      exact lt_of_le_of_lt (sInf_le ⟨r - 1, show (⊥ : EReal) ≤ ((r - 1 : ℝ) : EReal) from bot_le, rfl⟩)
        (EReal.coe_lt_coe_iff.2 (by linarith))
    | top => exact le_top
    | coe r => exact sInf_le ⟨r, show ((r : ℝ) : EReal) ≤ r from le_refl _, rfl⟩
  · refine le_sInf ?_
    rintro _ ⟨τ, hτ, rfl⟩
    exact hτ

end

section
open Matrix

open KAdaptability.Bilinear KAdaptability.Bilinear.Problem in
theorem solution {N M L nQ R K : ℕ} (P : Problem N M L nQ R) (ε : ℝ) (hε : 0 < ε) :
    (∀ (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ), P.IsDecision x y →
      P.obj6Eps ε x y = P.val7 ε x y ∧
      ∀ τ : ℝ, P.Feasible7 ε x y τ ↔ P.obj6Eps ε x y ≤ (τ : EReal)) ∧
    P.opt6Eps ε K = P.opt7 ε K := by
  have hval : ∀ (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ), P.val7 ε x y = P.obj6Eps ε x y := by
    intro x y
    rw [val7]
    simp_rw [feas7_iff P ε x y]
    exact sInf_upper _
  refine ⟨fun x y _ => ⟨(hval x y).symm, feas7_iff P ε x y⟩, ?_⟩
  apply le_antisymm
  · refine le_sInf ?_
    rintro _ ⟨τ, ⟨x, y, hd, hf⟩, rfl⟩
    refine iInf_le_of_le x (iInf_le_of_le y (iInf_le_of_le hd ?_))
    exact (feas7_iff P ε x y τ).1 hf
  · refine le_iInf fun x => le_iInf fun y => le_iInf fun hd => ?_
    rw [← hval x y, val7]
    refine sInf_le_sInf (Set.image_mono ?_)
    intro τ hτ
    exact ⟨x, y, hd, hτ⟩

end
