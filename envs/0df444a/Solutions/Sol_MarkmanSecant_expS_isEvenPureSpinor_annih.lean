-- Prove2me | solution 1 for MarkmanSecant.expS_isEvenPureSpinor_annih
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:10:41.013081+00:00
-- url     : https://prove2.me/submissions/383570f0-6dc2-4b73-8abc-4cf26ee6b4fd

import Mathlib
import Definitions.Def_MarkmanSecant

set_option autoImplicit false

open MarkmanSecant
open scoped ExteriorAlgebra

namespace E77Helpers

open MarkmanSecant

lemma wedge_eq_zero {n m : ℕ} (hm : 2 * n < m) (x : Spinor n)
    (hx : x ∈ ⋀[ℂ]^m (H1 n)) : x = 0 := by
  have h : Module.finrank ℂ (⋀[ℂ]^m (H1 n)) = 0 := by
    rw [exteriorPower.finrank_eq, Module.finrank_fin_fun]
    exact Nat.choose_eq_zero_of_lt hm
  have hs : Subsingleton (⋀[ℂ]^m (H1 n)) := Module.finrank_zero_iff.mp h
  exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : ⋀[ℂ]^m (H1 n)) 0)

lemma pow_mem_wedge {n : ℕ} (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (k : ℕ) :
    Θ ^ k ∈ ⋀[ℂ]^(2 * k) (H1 n) := by
  have := Submodule.pow_mem_pow _ hΘ k
  simpa [ExteriorAlgebra.exteriorPower, pow_mul] using this

lemma mem_mul_of_wedge2 {n : ℕ} (x : Spinor n) (hx : x ∈ ⋀[ℂ]^2 (H1 n)) :
    x ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : H1 n →ₗ[ℂ] Spinor n) *
      LinearMap.range (ExteriorAlgebra.ι ℂ : H1 n →ₗ[ℂ] Spinor n) := by
  have h : x ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : H1 n →ₗ[ℂ] Spinor n) ^ 2 := hx
  rwa [pow_two] at h

lemma triv_wedge2 {n : ℕ} (x : Spinor n) (hx : x ∈ ⋀[ℂ]^2 (H1 n)) :
    ExteriorAlgebra.toTrivSqZeroExt x = 0 := by
  refine Submodule.mul_induction_on (mem_mul_of_wedge2 x hx) ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp [TrivSqZeroExt.inr_mul_inr]
  · intro x y hx hy
    simp [hx, hy]

abbrev D {n : ℕ} (d : Module.Dual ℂ (H1 n)) : Spinor n →ₗ[ℂ] Spinor n :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) d

lemma wedge2_props {n : ℕ} (d : Module.Dual ℂ (H1 n)) (x : Spinor n)
    (hx : x ∈ ⋀[ℂ]^2 (H1 n)) :
    D d x ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : H1 n →ₗ[ℂ] Spinor n) ∧
      (∀ y : Spinor n, D d (x * y) = D d x * y + x * D d y) ∧
      (∀ z : H1 n, ExteriorAlgebra.ι ℂ z * x = x * ExteriorAlgebra.ι ℂ z) := by
  refine Submodule.mul_induction_on (mem_mul_of_wedge2 x hx) ?_ ?_
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hab : D d (ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b) =
        d a • ExteriorAlgebra.ι ℂ b - d b • ExteriorAlgebra.ι ℂ a := by
      simp only [D]
      rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι,
        ← Algebra.commutes, ← Algebra.smul_def]
    refine ⟨?_, ?_, ?_⟩
    · rw [hab]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _))
        (Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _))
    · intro y
      rw [hab]
      simp only [D]
      rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul]
      simp only [Algebra.smul_def, sub_mul, mul_sub, mul_assoc]
      rw [← mul_assoc (ExteriorAlgebra.ι ℂ a) (algebraMap ℂ _ (d b)), ← Algebra.commutes,
        mul_assoc]
      abel
    · intro z
      have h1 : ExteriorAlgebra.ι ℂ z * ExteriorAlgebra.ι ℂ a =
          -(ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ z) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap z a)
      have h2 : ExteriorAlgebra.ι ℂ z * ExteriorAlgebra.ι ℂ b =
          -(ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ z) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap z b)
      rw [← mul_assoc, h1, neg_mul, mul_assoc, h2, mul_neg, neg_neg, mul_assoc]
  · rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [map_add]; exact Submodule.add_mem _ hx1 hy1
    · intro w
      rw [add_mul, map_add, map_add, hx2, hy2, add_mul, add_mul]
      abel
    · intro z
      rw [mul_add, add_mul, hx3, hy3]

lemma deriv_pow {n : ℕ} (d : Module.Dual ℂ (H1 n)) (Φ : Spinor n)
    (hΦ : Φ ∈ ⋀[ℂ]^2 (H1 n)) (u : H1 n) (hu : D d Φ = ExteriorAlgebra.ι ℂ u) (k : ℕ) :
    D d (Φ ^ (k + 1)) = ((k : ℂ) + 1) • (ExteriorAlgebra.ι ℂ u * Φ ^ k) := by
  obtain ⟨-, hder, hcomm⟩ := wedge2_props d Φ hΦ
  induction k with
  | zero => simp [hu]
  | succ k ih =>
    rw [pow_succ' Φ (k + 1), hder, hu, ih, mul_smul_comm, ← mul_assoc, ← hcomm, mul_assoc,
      ← pow_succ']
    push_cast
    module

lemma deriv_expS {n : ℕ} (d : Module.Dual ℂ (H1 n)) (Φ : Spinor n)
    (hΦ : Φ ∈ ⋀[ℂ]^2 (H1 n)) (u : H1 n) (hu : D d Φ = ExteriorAlgebra.ι ℂ u) :
    D d (expS Φ) = ExteriorAlgebra.ι ℂ u * expS Φ := by
  have htop : ExteriorAlgebra.ι ℂ u * Φ ^ (2 * n) = 0 := by
    apply wedge_eq_zero (m := 1 + 2 * (2 * n)) (by omega)
    show _ ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : H1 n →ₗ[ℂ] Spinor n) ^ (1 + 2 * (2 * n))
    rw [pow_add, pow_one]
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (pow_mem_wedge Φ hΦ (2 * n))
  unfold expS
  rw [map_sum, Finset.mul_sum, Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [map_smul, pow_zero, D, CliffordAlgebra.contractLeft_one, smul_zero, add_zero,
    mul_smul_comm, htop]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := deriv_pow d Φ hΦ u hu k
  simp only [D] at this
  rw [this, smul_smul, Nat.factorial_succ]
  congr 1
  push_cast
  have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

lemma triv_expS {n : ℕ} (Φ : Spinor n) (hΦ : Φ ∈ ⋀[ℂ]^2 (H1 n)) :
    ExteriorAlgebra.toTrivSqZeroExt (expS Φ) = 1 := by
  unfold expS
  rw [map_sum, Finset.sum_range_succ']
  simp [triv_wedge2 Φ hΦ]

lemma iota_mul_expS_eq_zero {n : ℕ} (Φ : Spinor n) (hΦ : Φ ∈ ⋀[ℂ]^2 (H1 n)) (x : H1 n) :
    ExteriorAlgebra.ι ℂ x * expS Φ = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := congrArg (fun s => (ExteriorAlgebra.toTrivSqZeroExt s).snd) h
    simpa [triv_expS Φ hΦ] using this
  · rintro rfl
    simp

def thetaL {n : ℕ} (Θ : Spinor n) : H1 n →ₗ[ℂ] H1 n :=
  ExteriorAlgebra.ιInv ∘ₗ
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n)))).flip Θ ∘ₗ dualLin

lemma thetaL_apply {n : ℕ} (Θ : Spinor n) (y : H1 n) : thetaL Θ y = theta Θ y := rfl

lemma cliffAt_apply {n : ℕ} (s : Spinor n) (v : VC n) :
    cliffAt s v = ExteriorAlgebra.ι ℂ (wPart v) * s + D (dualOf (tPart v)) s := rfl

lemma iota_theta {n : ℕ} (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (y : H1 n) :
    ExteriorAlgebra.ι ℂ (theta Θ y) = D (dualOf y) Θ := by
  obtain ⟨u, hu⟩ := (wedge2_props (dualOf y) Θ hΘ).1
  unfold theta
  simp only [D] at hu
  rw [← hu, ExteriorAlgebra.ι_leftInverse]

lemma mem_annih_iff {n : ℕ} (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (c : ℂ) (v : VC n) :
    v ∈ annih (expS (c • Θ)) ↔ wPart v = -(c • theta Θ (tPart v)) := by
  have hΦ : c • Θ ∈ ⋀[ℂ]^2 (H1 n) := Submodule.smul_mem _ c hΘ
  have hu : D (dualOf (tPart v)) (c • Θ) = ExteriorAlgebra.ι ℂ (c • theta Θ (tPart v)) := by
    rw [map_smul, map_smul, iota_theta Θ hΘ]
  unfold annih
  rw [LinearMap.mem_ker, cliffAt_apply, deriv_expS _ _ hΦ _ hu, ← add_mul, ← map_add,
    iota_mul_expS_eq_zero _ hΦ, add_eq_zero_iff_eq_neg]

end E77Helpers

open MarkmanSecant in
theorem solution (n : ℕ) (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (c : ℂ) :
    IsEvenPureSpinor (expS (c • Θ)) ∧
      ∀ v : VC n, v ∈ annih (expS (c • Θ)) ↔ wPart v = -(c • theta Θ (tPart v)) := by
  have hΦ : c • Θ ∈ ⋀[ℂ]^2 (H1 n) := Submodule.smul_mem _ c hΘ
  refine ⟨⟨?_, ?_, ?_⟩, E77Helpers.mem_annih_iff Θ hΘ c⟩
  · unfold expS evenSpinors
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    exact Submodule.mem_iSup_of_mem k (E77Helpers.pow_mem_wedge _ hΦ k)
  · intro h
    have := E77Helpers.triv_expS _ hΦ
    rw [h, map_zero] at this
    have h2 := congrArg TrivSqZeroExt.fst this
    simp at h2
  · let L : VC n →ₗ[ℂ] H1 n := wPartLin + c • (E77Helpers.thetaL Θ ∘ₗ tPartLin)
    have hL : annih (expS (c • Θ)) = LinearMap.ker L := by
      ext v
      rw [E77Helpers.mem_annih_iff Θ hΘ c, LinearMap.mem_ker, eq_neg_iff_add_eq_zero]
      rfl
    have hsurj : Function.Surjective L := by
      intro y
      refine ⟨Sum.elim y 0, ?_⟩
      show y + c • E77Helpers.thetaL Θ 0 = y
      simp
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← hL] at h
    simp only [Module.finrank_pi, Fintype.card_sum,
      Fintype.card_fin] at h
    omega
