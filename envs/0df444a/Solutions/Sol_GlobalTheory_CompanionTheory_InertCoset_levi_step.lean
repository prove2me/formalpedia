-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertCoset.levi_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:04:13.632676+00:00
-- url     : https://prove2.me/submissions/e0c44c2b-7ed3-4a10-a641-39142e68d604

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryBlockTriangularLeviPartUnitary
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetSurjectiveOfLevi
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_single_left
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_hf_col
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_isLeviElt_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_InertCoset_isLeviElt_unique
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_idx_cases
import Theorems.Thm_GlobalTheory_InertZeta_last_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_injective
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_last
import Theorems.Thm_GlobalTheory_InertZeta_mid_ne_zero
import Theorems.Thm_GlobalTheory_InertZeta_mid_rev
import Theorems.Thm_GlobalTheory_InertZeta_sum_idx
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
import Theorems.Thm_GlobalTheory_SatakeWeyl_leviPart
import Theorems.Thm_GlobalTheory_SatakeWeyl_leviRad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


section
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
private theorem single_one_rev_eq_antiJ_apply (i j : Fin n) : (Pi.single j (1 : L) : Fin n → L) i.rev = antiJ L n i j := by
  by_cases h : i.rev = j
  · subst h
    have hv : (i : ℕ) + (i.rev : ℕ) + 1 = n := by rw [Fin.val_rev]; omega
    show (Pi.single i.rev (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (i.rev : ℕ) + 1 = n then 1 else 0)
    rw [if_pos hv, Pi.single_eq_same]
  · have hv : ¬ ((i : ℕ) + (j : ℕ) + 1 = n) := by
      intro h'
      apply h
      ext
      rw [Fin.val_rev]
      omega
    show (Pi.single j (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (j : ℕ) + 1 = n then 1 else 0)
    rw [if_neg hv, Pi.single_eq_of_ne h]
private theorem cT_mul_antiJ_mul_apply_eq_hf_col (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ A * antiJ L n * A) i j = hf σ (fun k => A k i) (fun k => A k j) := by
  have key : ∀ l, (cT σ A * antiJ L n) i l = σ (A l.rev i) := by
    intro l
    simp only [Matrix.mul_apply, antiJ, cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [Finset.sum_eq_single l.rev]
    · have hl : (l.rev : ℕ) + l + 1 = n := by rw [Fin.val_rev]; omega
      rw [if_pos hl, mul_one]
    · intro b _ hb
      have hbl : ¬ ((b : ℕ) + l + 1 = n) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      rw [if_neg hbl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply]
  simp only [key]
  rfl
private theorem mem_KU_of_mat_and_inv_mem_intL {m : ℕ} (A : GU σ m) (h1 : ∀ i j, mat A i j ∈ intL L)
    (h2 : ∀ i j, (((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j ∈ intL L) :
    A ∈ KU σ m := by
  let X : Matrix (Fin m) (Fin m) (intL L) := Matrix.of fun i j => ⟨mat A i j, h1 i j⟩
  let Y : Matrix (Fin m) (Fin m) (intL L) :=
    Matrix.of fun i j => ⟨(((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j, h2 i j⟩
  have hX : (intL L).subtype.mapMatrix X = mat A := by
    ext i j
    rfl
  have hY : (intL L).subtype.mapMatrix Y = (((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) := by
    ext i j
    rfl
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin m) (Fin m) (intL L) → Matrix (Fin m) (Fin m) L) :=
    Matrix.map_injective Subtype.val_injective
  have hXY : X * Y = 1 := hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).mul_inv)
  have hYX : Y * X = 1 := hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).inv_mul)
  rw [KU, Subgroup.mem_subgroupOf]
  show (A : GL (Fin m) L) ∈ GU σ m ⊓ (bc (intL L).subtype).range
  refine Subgroup.mem_inf.2 ⟨A.2, MonoidHom.mem_range.2 ⟨⟨X, Y, hXY, hYX⟩, ?_⟩⟩
  apply Units.ext
  ext i j
  rfl
section Levi
variable {N : ℕ} {ϖ : L} {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)}
end Levi
private theorem mat_apply_mem_intL_of_mem_KU {m : ℕ} {A : GU σ m} (hA : A ∈ KU σ m) (i j : Fin m) : mat A i j ∈ intL L := by
  rw [KU, Subgroup.mem_subgroupOf, intPts] at hA
  obtain ⟨-, hr⟩ := Subgroup.mem_inf.1 hA
  obtain ⟨g', hg'⟩ := MonoidHom.mem_range.1 hr
  show ((A : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j ∈ intL L
  rw [← hg']
  exact ((g' : Matrix (Fin m) (Fin m) (intL L)) i j).2
private theorem mat_apply_mem_intL_of_isLeviElt_of_mem_KU {N : ℕ} {ϖ : L} {h : GU σ N} {e : GU σ (N + 2)} (he : IsLeviElt ϖ 0 h e)
    (hh : h ∈ KU σ N) (i j : Fin (N + 2)) : mat e i j ∈ intL L := by
  obtain ⟨heL, he0, hel, hem⟩ := he
  have hez : ∀ i j, blk N i ≠ blk N j → mat e i j = 0 := heL
  by_cases hij : blk N i = blk N j
  · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl
    all_goals first
      | (rw [he0, zpow_zero]; exact (intL L).one_mem)
      | (rw [hem]; exact mat_apply_mem_intL_of_mem_KU hh _ _)
      | (rw [hel, neg_zero, zpow_zero]; exact (intL L).one_mem)
      | (simp [blk_zero, blk_mid, blk_last] at hij)
  · rw [hez i j hij]
    exact (intL L).zero_mem
end GlobalTheory.CompanionTheory.InertCoset
end
end

set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCoset
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace GlobalTheory.CompanionTheory.InertCoset
theorem _root_.solution (hLE : LeviExists) {ϖ : L} {q N : ℕ} (hU : IsUnramInv ϖ σ q) {s : ℤ} (p : GU σ (N + 2))
    (hp : ∀ i, mat p i 0 = ϖ ^ s * (Pi.single 0 1 : Fin (N + 2) → L) i) :
    ∃ y : GU σ N ⧸ KU σ N, ∀ m, IsLeviElt ϖ s y.out m →
      ∃ u ∈ radQ σ N, ∃ k ∈ KU σ (N + 2), p = m * u * k := by
  have hU' := hU
  obtain ⟨hσσ, hσ, hσϖ, hϖ, -⟩ := hU'
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hcol0 : (fun k => mat p k 0) = ϖ ^ s • Pi.single 0 1 := by
    funext k
    rw [hp k]
    rfl
  have hσs : σ (ϖ ^ s) = ϖ ^ s := by rw [map_zpow₀, hσϖ]
  have hrow : ∀ b, ϖ ^ s * mat p (Fin.last (N + 1)) b = (Pi.single b (1 : L) : Fin (N + 2) → L) (Fin.last (N + 1)) := by
    intro b
    have h := hf_col p 0 b
    rw [hcol0, ← single_one_rev_eq_antiJ_apply, Fin.rev_zero] at h
    have h2 := hf_smul (σ := σ) (ϖ ^ s) 1 (Pi.single 0 1) (fun k => mat p k b)
    rw [one_smul, mul_one, hf_single_left, Fin.rev_zero, hσs] at h2
    rw [← h, h2]
  have hlast0 : ∀ b, b ≠ Fin.last (N + 1) → mat p (Fin.last (N + 1)) b = 0 := by
    intro b hb
    have h := hrow b
    rw [Pi.single_eq_of_ne (Ne.symm hb)] at h
    exact (mul_eq_zero.1 h).resolve_left (zpow_ne_zero _ hϖ0)
  have hlastlast : mat p (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-s) := by
    have h := hrow (Fin.last (N + 1))
    rw [Pi.single_eq_same] at h
    rw [_root_.zpow_neg]
    exact eq_inv_of_mul_eq_one_right h
  have hp0 : ∀ i, i ≠ 0 → mat p i 0 = 0 := fun i hi => by rw [hp i, Pi.single_eq_of_ne hi, mul_zero]
  have htri : (mat p).BlockTriangular (blk N) := by
    intro i j hij
    rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl
    all_goals simp only [blk_zero, blk_mid, blk_last] at hij
    all_goals first
      | omega
      | exact hp0 _ (mid_ne_zero _)
      | exact hp0 _ last_ne_zero
      | exact hlast0 _ (mid_ne_last _)
  have hrevblk : ∀ a : Fin (N + 2), blk N a.rev = 2 - blk N a := by
    intro a
    rcases idx_cases a with rfl | ⟨i', rfl⟩ | rfl
    · rw [Fin.rev_zero, blk_last, blk_zero]
    · rw [← mid_rev, blk_mid, blk_mid]
    · rw [Fin.rev_last, blk_zero, blk_last]
  have hsym : ∀ a b : Fin (N + 2), blk N a = blk N b → blk N a.rev = blk N b.rev := by
    intro a b hab
    rw [hrevblk, hrevblk, hab]
  obtain ⟨m0, hm0L, hm0eq, hm0r⟩ := leviPart L σ (N + 2) (blk N) hsym p htri
  have hm0z : ∀ i j, blk N i ≠ blk N j → mat m0 i j = 0 := hm0L
  have hm0iL : m0⁻¹ ∈ leviU σ (blk N) := Subgroup.inv_mem _ hm0L
  have hm0iz : ∀ i j, blk N i ≠ blk N j → mat m0⁻¹ i j = 0 := hm0iL
  have hmidprod : ∀ (a b : GU σ (N + 2)), (∀ i j, blk N i ≠ blk N j → mat a i j = 0) → ∀ i j,
      mat (a * b) (mid i) (mid j) = ∑ k, mat a (mid i) (mid k) * mat b (mid k) (mid j) := by
    intro a b ha i j
    show (mat a * mat b) (mid i) (mid j) = _
    rw [Matrix.mul_apply, sum_idx, ha (mid i) 0 (by rw [blk_mid, blk_zero]; decide),
      ha (mid i) (Fin.last (N + 1)) (by rw [blk_mid, blk_last]; decide), zero_mul, zero_mul, zero_add, add_zero]
  have hone : ∀ i j : Fin N, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) (mid j) =
      (1 : Matrix (Fin N) (Fin N) L) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun h' => h (mid_injective h'))]
  let G : Matrix (Fin N) (Fin N) L := fun i j => mat m0 (mid i) (mid j)
  let G' : Matrix (Fin N) (Fin N) L := fun i j => mat m0⁻¹ (mid i) (mid j)
  have hGG' : G * G' = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    show ∑ k, mat m0 (mid i) (mid k) * mat m0⁻¹ (mid k) (mid j) = _
    rw [← hmidprod m0 m0⁻¹ hm0z, mul_inv_cancel]
    exact hone i j
  have hG'G : G' * G = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    show ∑ k, mat m0⁻¹ (mid i) (mid k) * mat m0 (mid k) (mid j) = _
    rw [← hmidprod m0⁻¹ m0 hm0iz, inv_mul_cancel]
    exact hone i j
  have hGU : cT σ G * antiJ L N * G = antiJ L N := by
    ext i j
    rw [cT_mul_antiJ_mul_apply_eq_hf_col]
    have h := hf_col m0 (mid i) (mid j)
    have hJ : antiJ L (N + 2) (mid i) (mid j) = antiJ L N i j := by
      show (if ((mid i : Fin (N + 2)) : ℕ) + ((mid j : Fin (N + 2)) : ℕ) + 1 = N + 2 then (1 : L) else 0) =
        (if (i : ℕ) + (j : ℕ) + 1 = N then 1 else 0)
      rw [val_mid, val_mid]
      by_cases hc : (i : ℕ) + (j : ℕ) + 1 = N
      · rw [if_pos (by omega), if_pos hc]
      · rw [if_neg (by omega), if_neg hc]
    rw [hJ] at h
    rw [← h]
    show ∑ k, σ (G k.rev i) * G k j = ∑ l, σ (mat m0 l.rev (mid i)) * mat m0 l (mid j)
    rw [sum_idx, hm0z 0 (mid j) (by rw [blk_zero, blk_mid]; decide),
      hm0z (Fin.last (N + 1)) (mid j) (by rw [blk_last, blk_mid]; decide), mul_zero, mul_zero, zero_add, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← mid_rev]
  let g0 : GU σ N := ⟨⟨G, G', hGG', hG'G⟩, hGU⟩
  refine ⟨QuotientGroup.mk g0, fun m hm => ?_⟩
  obtain ⟨k0, hk0⟩ := QuotientGroup.mk_out_eq_mul (KU σ N) g0
  obtain ⟨e, he⟩ := hLE L ϖ σ q N hU 0 (k0 : GU σ N)
  obtain ⟨e', he'⟩ := hLE L ϖ σ q N hU 0 ((k0 : GU σ N)⁻¹)
  have hm0lev : IsLeviElt ϖ s g0 m0 := by
    refine ⟨hm0L, ?_, ?_, fun i j => rfl⟩
    · rw [hm0eq 0 0 rfl, hp 0, Pi.single_eq_same, mul_one]
    · rw [hm0eq _ _ rfl, hlastlast]
  have hprod := isLeviElt_mul hϖ0 hm0lev he
  rw [add_zero, ← hk0] at hprod
  have hmeq : m = m0 * e := isLeviElt_unique hm hprod
  have hee' : e * e' = 1 := by
    have h1 := isLeviElt_mul hϖ0 he he'
    rw [add_zero, mul_inv_cancel] at h1
    have h2 : IsLeviElt ϖ 0 (1 : GU σ N) (1 : GU σ (N + 2)) := by
      refine ⟨Subgroup.one_mem _, ?_, ?_, ?_⟩
      · show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 0 = ϖ ^ (0 : ℤ)
        simp
      · show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-(0 : ℤ))
        simp
      · intro i j
        exact hone i j
    exact isLeviElt_unique h1 h2
  have he'eq : e' = e⁻¹ := eq_inv_of_mul_eq_one_right hee'
  have heK : e ∈ KU σ (N + 2) := by
    refine mem_KU_of_mat_and_inv_mem_intL e (mat_apply_mem_intL_of_isLeviElt_of_mem_KU he k0.2) ?_
    intro i j
    have h := mat_apply_mem_intL_of_isLeviElt_of_mem_KU he' (Subgroup.inv_mem _ k0.2) i j
    rw [he'eq] at h
    exact h
  have heL' := he
  obtain ⟨heL, -⟩ := heL'
  refine ⟨e⁻¹ * (m0⁻¹ * p) * e, ?_, e⁻¹, Subgroup.inv_mem _ heK, ?_⟩
  · have h := (leviRad L σ (N + 2) (blk N) hσ e⁻¹ (Subgroup.inv_mem _ heL) (m0⁻¹ * p) hm0r).1
    rw [inv_inv] at h
    exact h
  · rw [hmeq]
    group
end GlobalTheory.CompanionTheory.InertCoset
