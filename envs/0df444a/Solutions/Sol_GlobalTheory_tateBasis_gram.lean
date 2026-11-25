-- Prove2me | solution 1 for GlobalTheory.tateBasis_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:43:14.30501+00:00
-- url     : https://prove2.me/submissions/845cc8b6-3086-4bbe-8621-30e19969ddab

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TateBasisGram
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isPairingValue_add_left
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_exists
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_mul
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_pow
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_sw
import Theorems.Thm_ReciprocityTheory_PGsh_BX_pairing_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
section SlopeTestRemainingChoices
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}
private lemma gram_zero (N : ℕ) (y : B.G R) (hy : N • y = 0) : B.IsPairing N 0 y 1 := by
  obtain ⟨z, hz⟩ := B.pairing_exists N 0 y (smul_zero N) hy
  have h := B.isPairingValue_add_left N 0 0 y z z hz hz
  rw [add_zero] at h
  have e : z * z = z := B.pairing_unique N 0 y _ _ h hz
  have e1 : z = 1 := by simpa using e
  rwa [e1] at hz
private lemma gram_nsmul (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (m : ℕ) : B.IsPairing N (m • x) y (z ^ m) := by
  induction m with
  | zero =>
    rw [zero_smul, pow_zero]
    exact gram_zero B N y h.2.1
  | succ m ih =>
    rw [succ_nsmul, pow_succ]
    exact B.isPairingValue_add_left N _ _ y _ _ ih h
private lemma gram_sum {κ : Type} (s : Finset κ) (N : ℕ) (x : κ → B.G R) (y : B.G R)
    (z : κ → (R : Type)ˣ) (hy : N • y = 0) (h : ∀ i, B.IsPairing N (x i) y (z i)) :
    B.IsPairing N (∑ i ∈ s, x i) y (∏ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    exact gram_zero B N y hy
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact B.isPairingValue_add_left N _ _ y _ _ (h a) ih
end SlopeTestRemainingChoices
private lemma gram_limit {p : ℕ} [Fact p.Prime] (k : ℕ → ℕ)
    (hk : ∀ n, k n ≡ k (n + 1) [MOD p ^ (n + 1)]) :
    ∃ a : ℤ_[p], ∀ n, PadicInt.toZModPow (n + 1) a = (k n : ZMod (p ^ (n + 1))) := by
  have hi : ∀ i : ℕ, (p : ℤ) ^ i ∣ (fun i : ℕ => (k (i - 1) : ℤ)) (i + 1) -
      (fun i : ℕ => (k (i - 1) : ℤ)) i := by
    intro i
    cases i with
    | zero => simp
    | succ n =>
      have h := (Nat.modEq_iff_dvd.1 (hk n))
      simpa using h
  have key := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun i : ℕ => (k (i - 1) : ℤ)) p hi
  refine ⟨_, fun n => (key (n + 1)).trans ?_⟩
  simp only [Nat.add_sub_cancel, Int.cast_natCast]
private lemma gram_ext {p : ℕ} [Fact p.Prime] (a b : ℤ_[p])
    (h : ∀ n, PadicInt.toZModPow (n + 1) a = PadicInt.toZModPow (n + 1) b) : a = b := by
  refine PadicInt.ext_of_toZModPow.1 fun n => ?_
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, h,
    PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) b]
private lemma gram_toZMod {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) (k : ℕ)
    (h : PadicInt.toZModPow (0 + 1) a = (k : ZMod (p ^ (0 + 1)))) :
    PadicInt.toZMod a = (k : ZMod p) := by
  have h1 : a - (k : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) (0 + 1)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, h, sub_self]
  rw [PadicInt.ker_toZModPow, zero_add, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h1
  exact h1
end GlobalTheory
end

set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) [IsDomain (Tw.O : Type)] [Algebra ℤ_[p] (Tw.O : Type)],
    (∀ n, RingHom.ker (Tw.q n).1 = Ideal.span {((p : ℕ) : (Tw.O : Type)) ^ (n + 1)}) →
    (∀ n, IsPrimitiveRoot (Tw.ζ n) (p ^ (n + 1))) → (∀ n, Tw.ζ (n + 1) ^ p = Tw.ζ n) →
    ∀ τ : Ix g → ℕ → B.G Tw.O, (∀ i n, (p ^ (n + 1)) • τ i n = 0) → (∀ i n, τ i n = p • τ i (n + 1)) →
    (∀ x : B.G Tw.O, p • x = 0 → ∃! t : Ix g → ZMod p, x = ptOf B τ t) →
    (∀ x : B.G Tw.O, p • x = 0 → (∀ y : B.G Tw.O, p • y = 0 → B.IsPairing p x y 1) → x = 0) →
    ∃ E : Matrix (Ix g) (Ix g) ℤ_[p], (Eᵀ = -E ∧ ∀ i, E i i = 0) ∧ IsUnit E.det ∧
      ∀ i j n, B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ (PadicInt.toZModPow (n + 1) (E i j)).val)) := by
  intro R₀ _ p hp g B Tw _ _ _ hζ hζp τ htors hcomp hbasis hnd
  have hex : ∀ i j n, ∃ k : ℕ, k < p ^ (n + 1) ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k) := by
    intro i j n
    obtain ⟨z, hz⟩ := B.pairing_exists _ _ _ (htors i n) (htors j n)
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    obtain ⟨k, hk, e⟩ := (hζ n).eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity _ z).2 (B.pairing_pow _ _ _ _ hz))
    exact ⟨k, hk, e ▸ hz⟩
  choose k hklt hk using hex
  have hcompat : ∀ i j n, k i j n ≡ k i j (n + 1) [MOD p ^ (n + 1)] := by
    intro i j n
    have h1 := gram_nsmul B _ _ _ _ (hk i j (n + 1)) p
    rw [← hcomp, pow_succ p (n + 1)] at h1
    have h2 := B.pairing_mul _ p _ _ _ (htors i n)
      (by rw [← pow_succ]; exact htors j (n + 1)) h1
    rw [← hcomp, ← pow_mul, mul_comm, pow_mul, hζp] at h2
    have h3 := B.pairing_unique _ _ _ _ _ (hk i j n) h2
    rwa [pow_eq_pow_iff_modEq, ← (hζ n).eq_orderOf] at h3
  choose E hE using fun i j => gram_limit (k i j) (hcompat i j)
  have hanti : ∀ i j, E j i = -E i j := by
    intro i j
    refine gram_ext _ _ fun n => ?_
    have h1 := B.pairing_unique _ _ _ _ _ (hk j i n) (B.pairing_sw _ _ _ _ (hk i j n))
    rw [eq_inv_iff_mul_eq_one, ← pow_add, (hζ n).pow_eq_one_iff_dvd,
      ← ZMod.natCast_eq_zero_iff, Nat.cast_add] at h1
    rw [map_neg, hE, hE]
    exact eq_neg_of_add_eq_zero_left h1
  refine ⟨Matrix.of E, ⟨?_, fun i => ?_⟩, ?_, fun i j n => ?_⟩
  · ext i j
    exact hanti i j
  · exact self_eq_neg.1 (hanti i i)
  · by_contra hu
    have hd : (Matrix.of E).det ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
      rw [PadicInt.ker_toZMod]
      exact hu
    rw [RingHom.mem_ker, RingHom.map_det] at hd
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    have ht0 : ∀ i, p • τ i 0 = 0 := fun i => by simpa using htors i 0
    have hpt : ∀ t : Ix g → ZMod p, p • ptOf B τ t = 0 := fun t => by
      simp only [ptOf, Finset.smul_sum, smul_comm p]
      exact Finset.sum_eq_zero fun j _ => by rw [ht0, smul_zero]
    have hrow : ∀ j, B.IsPairing p (ptOf B τ s) (τ j 0) 1 := by
      intro j
      have h1 := gram_sum B Finset.univ (p ^ (0 + 1)) (fun i => (s i).val • τ i 0) (τ j 0)
        (fun i => (Tw.ζ 0 ^ k i j 0) ^ (s i).val) (htors j 0)
        (fun i => gram_nsmul B _ _ _ _ (hk i j 0) _)
      have h2 : ∏ i, (Tw.ζ 0 ^ k i j 0) ^ (s i).val = 1 := by
        simp only [← pow_mul]
        rw [Finset.prod_pow_eq_pow_sum, (hζ 0).pow_eq_one_iff_dvd, zero_add, pow_one,
          ← ZMod.natCast_eq_zero_iff, Nat.cast_sum]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (congrFun hs j)
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm, ← gram_toZMod _ _ (hE i j 0)]
        rfl
      rw [h2, zero_add, pow_one] at h1
      exact h1
    have hx : ptOf B τ s = 0 := by
      refine hnd _ (hpt s) fun y hy => ?_
      obtain ⟨t, rfl, -⟩ := hbasis y hy
      have h1 := gram_sum B Finset.univ p (fun j => (t j).val • τ j 0) (ptOf B τ s)
        (fun j => (1⁻¹) ^ (t j).val) (hpt s)
        (fun j => gram_nsmul B _ _ _ _ (B.pairing_sw _ _ _ _ (hrow j)) _)
      have h2 := B.pairing_sw _ _ _ _ h1
      simp only [inv_one, one_pow, Finset.prod_const_one] at h2
      exact h2
    have h0 : (0 : B.G Tw.O) = ptOf B τ (0 : Ix g → ZMod p) := by simp [ptOf]
    exact hs0 ((hbasis 0 (smul_zero p)).unique hx.symm h0)
  · rw [Matrix.of_apply, hE, ZMod.val_cast_of_lt (hklt i j n)]
    exact hk i j n
end GlobalTheory
