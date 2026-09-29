-- Prove2me | solution 1 for M4aLocalCFT.unitsDecomp_exists_cohTrivial_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/689565ec-7c25-5ebb-bfb6-8bc4f85ff9dd

import Definitions.Def_M4aLocalCFT_VocabDefs
import Theorems.Thm_M4aLocalCFT_decompositionSubgroup_exists_integralNormalBasis
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.SModEq.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsLocalRing

namespace M4aLocalCFT
p2m_export "M4aLocalCFT" "unitsAct unitsNorm unitsDerive decompositionSubgroup_exists_integralNormalBasis"
p2m_open "M4aLocalCFT"

namespace CohTrivFI

section Approx

variable {U : Type*} [CommGroup U]

theorem approx (V W : ℕ → Subgroup U) (φ ψ : U →* U)
    (hV0 : ∀ k, V k ≤ V 0) (hVW : ∀ k, V k ≤ W k)
    (hφW : ∀ k, ∀ x ∈ W k, φ x ∈ W k)
    (hlim : ∀ w : ℕ → U, (∀ k, w (k + 1) * (w k)⁻¹ ∈ V k) → ∃ x, ∀ k, x * (w k)⁻¹ ∈ W k)
    (hsep : ∀ x, (∀ k, x ∈ W k) → x = 1)
    (hW0 : ∃ k₀, W k₀ ≤ V 0)
    (hψφ : ∀ x, ψ (φ x) = 1)
    (hstep : ∀ k, ∀ u ∈ V k, ψ u = 1 → ∃ z ∈ V k, u * (φ z)⁻¹ ∈ V (k + 1))
    (v : U) (hv : v ∈ V 0) (hψ : ψ v = 1) : ∃ w ∈ V 0, φ w = v := by
  have key : ∀ k, ∀ w : U, w ∈ V 0 → v * (φ w)⁻¹ ∈ V k →
      ∃ w' : U, w' ∈ V 0 ∧ v * (φ w')⁻¹ ∈ V (k + 1) ∧ w' * w⁻¹ ∈ V k := by
    intro k w hw hk
    have hψu : ψ (v * (φ w)⁻¹) = 1 := by
      rw [map_mul, map_inv, hψ, hψφ, inv_one, mul_one]
    obtain ⟨z, hz, hz'⟩ := hstep k _ hk hψu
    refine ⟨w * z, mul_mem hw (hV0 k hz), ?_, ?_⟩
    · rw [map_mul, mul_inv_rev, ← mul_assoc, mul_right_comm]
      exact hz'
    · rw [mul_comm w z, mul_inv_cancel_right]
      exact hz
  choose! F hF0 hF1 hF2 using key
  let w : ℕ → U := fun k => Nat.rec 1 (fun k wk => F k wk) k
  have hw0 : w 0 = 1 := rfl
  have hwsucc : ∀ k, w (k + 1) = F k (w k) := fun k => rfl
  have hwV : ∀ k, w k ∈ V 0 ∧ v * (φ (w k))⁻¹ ∈ V k := by
    intro k
    induction k with
    | zero =>
      refine ⟨by rw [hw0]; exact one_mem _, ?_⟩
      rw [hw0, map_one, inv_one, mul_one]; exact hv
    | succ k ih =>
      exact ⟨hwsucc k ▸ hF0 k _ ih.1 ih.2, hwsucc k ▸ hF1 k _ ih.1 ih.2⟩
  have hwdiff : ∀ k, w (k + 1) * (w k)⁻¹ ∈ V k := fun k =>
    hwsucc k ▸ hF2 k _ (hwV k).1 (hwV k).2
  obtain ⟨x, hx⟩ := hlim w hwdiff
  obtain ⟨k₀, hk₀⟩ := hW0
  refine ⟨x, ?_, ?_⟩
  · have : x = (x * (w k₀)⁻¹) * w k₀ := by rw [inv_mul_cancel_right]
    rw [this]
    exact mul_mem (hk₀ (hx k₀)) (hwV k₀).1
  · have hmem : ∀ k, v * (φ x)⁻¹ ∈ W k := by
      intro k
      have h1 : v * (φ (w k))⁻¹ ∈ W k := hVW k (hwV k).2
      have h2 : φ (x * (w k)⁻¹) ∈ W k := hφW k _ (hx k)
      have : v * (φ x)⁻¹ = (v * (φ (w k))⁻¹) * (φ (x * (w k)⁻¹))⁻¹ := by
        rw [map_mul, map_inv, mul_inv_rev, inv_inv, ← mul_assoc, inv_mul_cancel_right]
      rw [this]
      exact mul_mem h1 (inv_mem h2)
    have := hsep _ hmem
    rw [mul_inv_eq_one] at this
    exact this.symm

end Approx

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L)
variable [Finite (A.decompositionSubgroup K)]

attribute [local instance] Fintype.ofFinite

local notation "G" => (ValuationSubring.decompositionSubgroup K A)
local notation "F" => (FixedPoints.subfield (ValuationSubring.decompositionSubgroup K A) L)

scoped instance instFaithfulSMul : FaithfulSMul (A.decompositionSubgroup K) L where
  eq_of_smul_eq_smul {s t} h := by
    apply Subtype.ext
    ext x
    exact h x

variable (K) in
theorem sigma_mem {x : L} (s : G) (hx : x ∈ A) : s • x ∈ A :=
  (A.subMulAction K).smul_mem s hx

variable (K) in
theorem smul_coe_fixed (s : G) (r : F) : s • (r : L) = r := r.2 s

variable (K) in
@[scoped simp] theorem coe_smul_A (s : G) (a : A) : ((s • a : A) : L) = s • (a : L) := rfl

variable (K) in
theorem coe_unitsAct (s : G) (u : Aˣ) :
    (((unitsAct A s u : Aˣ) : A) : L) = s • ((u : A) : L) := rfl

variable (K) in
theorem unitsNorm_apply (u : Aˣ) : unitsNorm (K := K) A u = ∏ s : G, unitsAct A s u := by
  simp only [unitsNorm, MonoidHom.finsetProd_apply]

variable (K) in
theorem coe_unitsNorm (u : Aˣ) :
    (((unitsNorm (K := K) A u : Aˣ) : A) : L) = ∏ s : G, s • ((u : A) : L) := by
  rw [unitsNorm_apply]; push_cast; rfl

variable (K) in
theorem unitsAct_mul (s t : G) (u : Aˣ) : unitsAct A (s * t) u = unitsAct A s (unitsAct A t u) := by
  ext
  simp only [coe_unitsAct]
  exact mul_smul s t _

variable (K) in
theorem unitsDerive_apply (g : G) (u : Aˣ) : unitsDerive A g u = unitsAct A g u / u := by
  simp [unitsDerive, MonoidHom.div_apply]

variable (K) in
theorem unitsAct_norm (g : G) (u : Aˣ) :
    unitsAct A g (unitsNorm (K := K) A u) = unitsNorm (K := K) A u := by
  rw [unitsNorm_apply, map_prod]
  simp_rw [← unitsAct_mul]
  exact Fintype.prod_bijective _ (Group.mulLeft_bijective g) _ _ fun _ => rfl

variable (K) in
theorem norm_unitsAct (g : G) (u : Aˣ) :
    unitsNorm (K := K) A (unitsAct A g u) = unitsNorm (K := K) A u := by
  rw [unitsNorm_apply, unitsNorm_apply]
  simp_rw [← unitsAct_mul]
  exact Fintype.prod_bijective _ (Group.mulRight_bijective g) _ _ fun _ => rfl

variable (K) in
theorem derive_norm (g : G) (u : Aˣ) :
    unitsDerive A g (unitsNorm (K := K) A u) = 1 := by
  rw [unitsDerive_apply, unitsAct_norm, div_self']

variable (K) in
theorem norm_derive (g : G) (u : Aˣ) :
    unitsNorm (K := K) A (unitsDerive A g u) = 1 := by
  rw [unitsDerive_apply, map_div, norm_unitsAct, div_self']

structure NBData (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite (A.decompositionSubgroup K)] where

  α : L

  τ : A

  d : L
  αA : α ∈ A
  li : LinearIndependent (FixedPoints.subfield (A.decompositionSubgroup K) L)
    (fun s : A.decompositionSubgroup K => s • α)
  τ0 : τ ≠ 0
  τfix : ∀ s : A.decompositionSubgroup K, s • τ = τ
  τnu : ¬IsUnit τ
  dA : d ∈ A
  d0 : d ≠ 0
  dfix : ∀ s : A.decompositionSubgroup K, s • d = d
  hd : ∀ a : L, a ∈ A → ∃ c : A.decompositionSubgroup K → L,
    (∀ s, c s ∈ A) ∧ (∀ s t : A.decompositionSubgroup K, t • c s = c s) ∧
    d * a = ∑ s, c s * s • α

variable (K) in
theorem exists_tau [IsDiscreteValuationRing A] :
    ∃ τ : A, τ ≠ 0 ∧ (∀ s : G, s • τ = τ) ∧ ¬IsUnit τ := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine ⟨∏ s : G, s • ϖ, ?_, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro s _ h
    exact hϖ.ne_zero ((smul_eq_zero_iff_eq s).1 h)
  · intro t
    rw [Finset.smul_prod']
    simp_rw [← mul_smul]
    exact Fintype.prod_bijective _ (Group.mulLeft_bijective t) _ _ fun _ => rfl
  · intro hu
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : G)), one_smul] at hu
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left hu)

variable (K) in
theorem nonempty_NBData [IsDiscreteValuationRing A] : Nonempty (NBData K A) := by
  obtain ⟨α, hαA, hα, d, hdA, hd0, hdfix, hd⟩ :=
    M4aLocalCFT.decompositionSubgroup_exists_integralNormalBasis (K := K) A
  obtain ⟨τ, hτ0, hτfix, hτnu⟩ := exists_tau K A
  exact ⟨⟨α, τ, d, hαA, hα, hτ0, hτfix, hτnu, hdA, hd0, hdfix, hd⟩⟩

namespace NBData

variable {A}
variable (X : NBData K A)

noncomputable def nb : Module.Basis G F L :=
  basisOfLinearIndependentOfCardEqFinrank X.li (FixedPoints.finrank_eq_card G L).symm

@[scoped simp] theorem nb_apply (s : G) : X.nb s = s • X.α := by
  simp [nb]

noncomputable def coef (x : L) (s : G) : L := (X.nb.repr x s : L)

theorem coef_fixed (x : L) (s t : G) : t • X.coef x s = X.coef x s :=
  (X.nb.repr x s).2 t

theorem coef_add (x y : L) (s : G) : X.coef (x + y) s = X.coef x s + X.coef y s := by
  simp [coef]

theorem coef_sub (x y : L) (s : G) : X.coef (x - y) s = X.coef x s - X.coef y s := by
  simp [coef]

theorem coef_neg (x : L) (s : G) : X.coef (-x) s = -X.coef x s := by
  simp [coef]

theorem coef_zero (s : G) : X.coef 0 s = 0 := by
  simp [coef]

theorem sum_coef (x : L) : ∑ s, X.coef x s * s • X.α = x := by
  conv_rhs => rw [← X.nb.sum_repr x]
  simp only [coef, nb_apply]
  rfl

theorem coef_sum_mul (f : G → F) (s : G) :
    X.coef (∑ t, (f t : L) * t • X.α) s = f s := by
  have := X.nb.repr_sum_self f
  have h : (∑ t, f t • X.nb t) = ∑ t, (f t : L) * t • X.α := by
    simp only [nb_apply]; rfl
  rw [h] at this
  simp only [coef, this]

theorem coef_smul (t : G) (x : L) (s : G) : X.coef (t • x) s = X.coef x (t⁻¹ * s) := by

  have hx : t • x = ∑ s, ((X.nb.repr x (t⁻¹ * s) : F) : L) * s • X.α := by
    conv_lhs => rw [← X.sum_coef x]
    rw [Finset.smul_sum]
    simp only [coef, smul_mul', smul_coe_fixed, ← mul_smul]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective t) _ _ fun u => by
      simp [inv_mul_cancel_left]
  rw [hx, coef_sum_mul]
  rfl

theorem coef_single [DecidableEq (A.decompositionSubgroup K)] (z : L) (hz : ∀ t : G, t • z = z)
    (u s : G) : X.coef (z * u • X.α) s = if s = u then z else 0 := by
  have h : z * u • X.α = ∑ t, (((if t = u then (⟨z, hz⟩ : F) else 0) : F) : L) * t • X.α := by
    rw [Finset.sum_eq_single u]
    · simp
    · intro t _ ht; simp [ht]
    · intro h; exact absurd (Finset.mem_univ u) h
  rw [h, coef_sum_mul]
  split_ifs <;> rfl

noncomputable def e (k : ℕ) : L := ((X.τ : A) : L) ^ (k + 1) * X.d

theorem τL_ne : ((X.τ : A) : L) ≠ 0 := fun h => X.τ0 (Subtype.ext h)

theorem τL_fix (s : G) : s • ((X.τ : A) : L) = ((X.τ : A) : L) := by
  rw [← coe_smul_A, X.τfix]

theorem e_ne (k : ℕ) : X.e k ≠ 0 := mul_ne_zero (pow_ne_zero _ X.τL_ne) X.d0

theorem e_mem (k : ℕ) : X.e k ∈ A := mul_mem (pow_mem (X.τ).2 _) X.dA

theorem e_fix (s : G) (k : ℕ) : s • X.e k = X.e k := by
  simp only [e, smul_mul', smul_pow', τL_fix, X.dfix]

theorem e_succ (k : ℕ) : X.e (k + 1) = ((X.τ : A) : L) * X.e k := by
  simp only [e]; ring

theorem e_add (j k : ℕ) : X.e j * X.e k = X.e (j + k + 1) * X.d := by
  simp only [e]; ring

noncomputable def latt (k : ℕ) : AddSubgroup L where
  carrier := {x | ∀ s : G, (X.e k)⁻¹ * X.coef x s ∈ A}
  zero_mem' s := by simp [coef_zero]
  add_mem' {x y} hx hy s := by
    rw [coef_add, mul_add]; exact add_mem (hx s) (hy s)
  neg_mem' {x} hx s := by
    rw [coef_neg, mul_neg]; exact neg_mem (hx s)

theorem mem_latt {k : ℕ} {x : L} : x ∈ X.latt k ↔ ∀ s : G, (X.e k)⁻¹ * X.coef x s ∈ A :=
  Iff.rfl

theorem latt_succ_le (k : ℕ) : X.latt (k + 1) ≤ X.latt k := by
  intro x hx s
  have : (X.e k)⁻¹ * X.coef x s = ((X.τ : A) : L) * ((X.e (k + 1))⁻¹ * X.coef x s) := by
    rw [e_succ, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ X.τL_ne, one_mul]
  rw [this]
  exact mul_mem (X.τ).2 (hx s)

theorem latt_le {j k : ℕ} (h : j ≤ k) : X.latt k ≤ X.latt j :=
  (antitone_nat_of_succ_le X.latt_succ_le) h

theorem smul_mem_latt {k : ℕ} {x : L} (t : G) (hx : x ∈ X.latt k) : t • x ∈ X.latt k := by
  intro s
  rw [coef_smul]
  exact hx _

theorem single_mem_latt {k : ℕ} (z : L) (hz : ∀ t : G, t • z = z)
    (hzA : (X.e k)⁻¹ * z ∈ A) (u : G) : z * u • X.α ∈ X.latt k := by
  classical
  intro s
  rw [coef_single _ _ hz]
  split_ifs
  · exact hzA
  · rw [mul_zero]; exact zero_mem _

theorem exists_eq_of_mem_latt {k : ℕ} {x : L} (hx : x ∈ X.latt k) :
    ∃ Y : L, Y ∈ A ∧ x = X.e k * Y := by
  refine ⟨∑ s, ((X.e k)⁻¹ * X.coef x s) * s • X.α,
    sum_mem fun s _ => mul_mem (hx s) (sigma_mem K A s X.αA), ?_⟩
  rw [Finset.mul_sum]
  conv_lhs => rw [← X.sum_coef x]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (X.e_ne k), one_mul]

theorem latt_subset {k : ℕ} {x : L} (hx : x ∈ X.latt k) : x ∈ A := by
  obtain ⟨Y, hY, rfl⟩ := X.exists_eq_of_mem_latt hx
  exact mul_mem (X.e_mem k) hY

theorem latt_mem_pow {k : ℕ} {x : L} (hx : x ∈ X.latt k) :
    (⟨x, X.latt_subset hx⟩ : A) ∈ (maximalIdeal A) ^ (k + 1) := by
  obtain ⟨Y, hY, hxY⟩ := X.exists_eq_of_mem_latt hx
  have : (⟨x, X.latt_subset hx⟩ : A) = X.τ ^ (k + 1) * (⟨X.d, X.dA⟩ * ⟨Y, hY⟩) := by
    apply Subtype.ext
    simp only [hxY, e]
    push_cast
    ring
  rw [this]
  refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
  exact (IsLocalRing.mem_maximalIdeal _).2 X.τnu

theorem base_mem_latt (k : ℕ) {a : L} (ha : a ∈ A) : X.e k * (X.d * a) ∈ X.latt k := by
  obtain ⟨c, hcA, hcfix, hda⟩ := X.hd a ha
  rw [hda, Finset.mul_sum]
  refine sum_mem fun s _ => ?_
  rw [← mul_assoc]
  refine X.single_mem_latt _ (fun t => ?_) ?_ s
  · rw [smul_mul', e_fix, hcfix]
  · rw [← mul_assoc, inv_mul_cancel₀ (X.e_ne k), one_mul]; exact hcA s

theorem mul_mem_latt {j k : ℕ} {x y c : L} (hx : x ∈ X.latt j) (hy : y ∈ X.latt k)
    (hc : c ∈ A) : x * y * c ∈ X.latt (j + k + 1) := by
  obtain ⟨X', hX', rfl⟩ := X.exists_eq_of_mem_latt hx
  obtain ⟨Y', hY', rfl⟩ := X.exists_eq_of_mem_latt hy
  have : X.e j * X' * (X.e k * Y') * c = X.e (j + k + 1) * (X.d * (X' * Y' * c)) := by
    simp only [e]; ring
  rw [this]
  exact X.base_mem_latt _ (mul_mem (mul_mem hX' hY') hc)

theorem mul_mem_latt_left {j k : ℕ} {x y c : L} (hx : x ∈ X.latt j) (hy : y ∈ X.latt k)
    (hc : c ∈ A) : x * y * c ∈ X.latt j :=
  X.latt_le (by omega) (X.mul_mem_latt hx hy hc)

theorem mul_mem_latt_succ {k : ℕ} {x y : L} (hx : x ∈ X.latt k) (hy : y ∈ X.latt k) :
    x * y ∈ X.latt (k + 1) := by
  have := X.mul_mem_latt hx hy (one_mem A)
  rw [mul_one] at this
  exact X.latt_le (by omega) this

theorem graded_H0 (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) {k : ℕ} {x : L}
    (hx : x ∈ X.latt k) (hgx : g • x - x ∈ X.latt (k + 1)) :
    ∃ y ∈ X.latt k, x - ∑ s : G, s • y ∈ X.latt (k + 1) := by

  have hP : ∀ s : G, (X.e (k + 1))⁻¹ * (X.coef x (g⁻¹ * s) - X.coef x s) ∈ A := by
    intro s
    have := hgx s
    rwa [coef_sub, coef_smul] at this
  have hQ : ∀ s : G, (X.e (k + 1))⁻¹ * (X.coef x s - X.coef x 1) ∈ A := by
    intro s
    obtain ⟨i, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hg s))
    induction i with
    | zero => simp
    | succ i ih =>
      have h1 : g⁻¹ * g ^ (i + 1) = g ^ i := by rw [pow_succ', inv_mul_cancel_left]
      have := hP (g ^ (i + 1))
      rw [h1] at this
      have e1 : (X.e (k + 1))⁻¹ * (X.coef x (g ^ (i + 1)) - X.coef x 1) =
          -((X.e (k + 1))⁻¹ * (X.coef x (g ^ i) - X.coef x (g ^ (i + 1)))) +
            (X.e (k + 1))⁻¹ * (X.coef x (g ^ i) - X.coef x 1) := by ring
      rw [e1]
      exact add_mem (neg_mem this) ih
  refine ⟨X.coef x 1 * X.α, ?_, ?_⟩
  · have := X.single_mem_latt (X.coef x 1) (X.coef_fixed x 1) (hx 1) 1
    rwa [one_smul] at this
  · have hy : ∀ s : G, s • (X.coef x 1 * X.α) = X.coef x 1 * s • X.α := by
      intro s; rw [smul_mul', coef_fixed]
    simp_rw [hy]
    have : x - ∑ s : G, X.coef x 1 * s • X.α = ∑ s : G, (X.coef x s - X.coef x 1) * s • X.α := by
      simp only [sub_mul, Finset.sum_sub_distrib, X.sum_coef]
    rw [this]
    refine sum_mem fun s _ => X.single_mem_latt _ (fun t => ?_) (hQ s) s
    rw [smul_sub, coef_fixed, coef_fixed]

theorem smul_partial_sub (g : G) (m : ℕ) :
    g • (∑ j ∈ Finset.range m, (g ^ j) • X.α) - ∑ j ∈ Finset.range m, (g ^ j) • X.α =
      (g ^ m) • X.α - X.α := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, smul_add, ← mul_smul, ← pow_succ']
    have := ih
    linear_combination this

theorem graded_H1 (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) {k : ℕ} {x : L}
    (hx : x ∈ X.latt k) (hNx : ∑ t : G, t • x ∈ X.latt (k + 1)) :
    ∃ y ∈ X.latt k, x - (g • y - y) ∈ X.latt (k + 1) := by
  have hn : ∀ s : G, ∃ n : ℕ, g ^ n = s := fun s => mem_powers_iff_mem_zpowers.2 (hg s)
  choose n hn using hn
  let T : G → L := fun s => ∑ j ∈ Finset.range (n s), (g ^ j) • X.α
  have hT : ∀ s, g • T s - T s = s • X.α - X.α := by
    intro s
    simp only [T]
    rw [smul_partial_sub, hn]
  refine ⟨∑ s, X.coef x s * T s, ?_, ?_⟩
  · refine sum_mem fun s _ => ?_
    simp only [T, Finset.mul_sum]
    exact sum_mem fun j _ => X.single_mem_latt _ (X.coef_fixed x s) (hx s) _
  ·
    have h1 : g • (∑ s, X.coef x s * T s) - ∑ s, X.coef x s * T s =
        x - (∑ s, X.coef x s) * X.α := by
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      have : ∀ s, g • (X.coef x s * T s) - X.coef x s * T s = X.coef x s * (s • X.α - X.α) := by
        intro s
        rw [smul_mul', coef_fixed, ← mul_sub, hT]
      simp_rw [this, mul_sub, Finset.sum_sub_distrib, sum_coef, Finset.sum_mul]
    rw [h1, sub_sub_cancel]

    have hS : X.coef (∑ t : G, t • x) 1 = ∑ s, X.coef x s := by
      have : X.coef (∑ t : G, t • x) 1 = ∑ t : G, X.coef (t • x) 1 := by
        simp only [coef, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
        push_cast; rfl
      rw [this]
      simp_rw [coef_smul, mul_one]
      exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl
    have hfix : ∀ t : G, t • (∑ s, X.coef x s) = ∑ s, X.coef x s := by
      intro t; rw [Finset.smul_sum]; simp_rw [coef_fixed]
    have := X.single_mem_latt (∑ s, X.coef x s) hfix (by rw [← hS]; exact hNx 1) 1
    rwa [one_smul] at this

theorem prod_one_add_sub_mem (k : ℕ) (y : G → L) (hy : ∀ s, y s ∈ X.latt k) (S : Finset G) :
    ∏ s ∈ S, (1 + y s) - 1 - ∑ s ∈ S, y s ∈ X.latt (k + 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hsum : ∑ s ∈ S, y s ∈ X.latt k := sum_mem fun s _ => hy s
    set r := ∏ s ∈ S, (1 + y s) - 1 - ∑ s ∈ S, y s with hr
    have : (1 + y a) * ∏ s ∈ S, (1 + y s) - 1 - (y a + ∑ s ∈ S, y s) =
        r + y a * (∑ s ∈ S, y s) + y a * r := by
      rw [hr]; ring
    rw [this]
    refine add_mem (add_mem ih (X.mul_mem_latt_succ (hy a) hsum)) ?_
    have := X.mul_mem_latt (hy a) ih (one_mem A)
    rw [mul_one] at this
    exact X.latt_le (by omega) this

theorem prod_one_add_sub_mem' (k : ℕ) (y : G → L) (hy : ∀ s, y s ∈ X.latt k) :
    ∏ s, (1 + y s) - 1 - ∑ s, y s ∈ X.latt (k + 1) :=
  X.prod_one_add_sub_mem k y hy Finset.univ

theorem coe_units_inv_mul (u : Aˣ) : (((u⁻¹ : Aˣ) : A) : L) * ((u : A) : L) = 1 := by
  have := congrArg (fun a : A => (a : L)) u.inv_mul
  push_cast at this
  exact this

noncomputable def V (k : ℕ) : Subgroup Aˣ where
  carrier := {u | ((u : A) : L) - 1 ∈ X.latt k}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    have : (((u * v : Aˣ) : A) : L) - 1 =
        (((u : A) : L) - 1) + (((v : A) : L) - 1) + (((u : A) : L) - 1) * (((v : A) : L) - 1) := by
      push_cast; ring
    show (((u * v : Aˣ) : A) : L) - 1 ∈ X.latt k
    rw [this]
    exact add_mem (add_mem hu hv) (X.latt_le (by omega) (X.mul_mem_latt_succ hu hv))
  inv_mem' {u} hu := by
    have h := coe_units_inv_mul u
    have : (((u⁻¹ : Aˣ) : A) : L) - 1 =
        -(((u : A) : L) - 1) + (((u : A) : L) - 1) * (((u : A) : L) - 1) * (((u⁻¹ : Aˣ) : A) : L) := by
      linear_combination (2 - ((u : A) : L)) * h
    show (((u⁻¹ : Aˣ) : A) : L) - 1 ∈ X.latt k
    rw [this]
    exact add_mem (neg_mem hu) (X.mul_mem_latt_left hu hu (u⁻¹ : Aˣ).1.2)

theorem mem_V {k : ℕ} {u : Aˣ} : u ∈ X.V k ↔ ((u : A) : L) - 1 ∈ X.latt k := Iff.rfl

theorem V_le {j k : ℕ} (h : j ≤ k) : X.V k ≤ X.V j := fun _ hu => X.latt_le h hu

theorem unitsAct_mem_V {k : ℕ} (s : G) {u : Aˣ} (hu : u ∈ X.V k) : unitsAct A s u ∈ X.V k := by
  rw [mem_V, coe_unitsAct]
  have : s • ((u : A) : L) - 1 = s • (((u : A) : L) - 1) := by rw [smul_sub, smul_one]
  rw [this]
  exact X.smul_mem_latt s hu

theorem norm_mem_V {k : ℕ} {u : Aˣ} (hu : u ∈ X.V k) : unitsNorm (K := K) A u ∈ X.V k := by
  rw [unitsNorm_apply]
  exact prod_mem fun s _ => X.unitsAct_mem_V s hu

theorem derive_mem_V (g : G) {k : ℕ} {u : Aˣ} (hu : u ∈ X.V k) : unitsDerive A g u ∈ X.V k := by
  rw [unitsDerive_apply]
  exact div_mem (X.unitsAct_mem_V g hu) hu

theorem mul_inv_mem_V {i j : ℕ} {a b : Aˣ} (hb : b ∈ X.V j)
    (hab : ((a : A) : L) - ((b : A) : L) ∈ X.latt i) : a * b⁻¹ ∈ X.V i := by
  have h := coe_units_inv_mul b
  rw [mem_V]
  have : (((a * b⁻¹ : Aˣ) : A) : L) - 1 =
      (((a : A) : L) - ((b : A) : L)) -
        (((a : A) : L) - ((b : A) : L)) * (((b : A) : L) - 1) * (((b⁻¹ : Aˣ) : A) : L) := by
    push_cast
    linear_combination (((a : A) : L) - ((b : A) : L) + 1) * h
  rw [this]
  exact sub_mem hab (X.mul_mem_latt_left hab hb (b⁻¹ : Aˣ).1.2)

theorem exists_unit_of_mem_latt {k : ℕ} {y : L} (hy : y ∈ X.latt k) :
    ∃ z : Aˣ, z ∈ X.V k ∧ ((z : A) : L) = 1 + y := by
  have hym : (⟨y, X.latt_subset hy⟩ : A) ∈ maximalIdeal A :=
    Ideal.pow_le_self (Nat.succ_ne_zero k) (X.latt_mem_pow hy)
  have hu : IsUnit (1 + (⟨y, X.latt_subset hy⟩ : A)) := by
    rcases isUnit_or_isUnit_one_sub_self (-(⟨y, X.latt_subset hy⟩ : A)) with h | h
    · exact absurd ((IsUnit.neg_iff _).1 h) ((IsLocalRing.mem_maximalIdeal _).1 hym)
    · rwa [sub_neg_eq_add] at h
  refine ⟨hu.unit, ?_, ?_⟩
  · rw [mem_V, hu.unit_spec]; push_cast; simpa using hy
  · rw [hu.unit_spec]; push_cast; rfl

theorem step_H0 (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (k : ℕ) (u : Aˣ) (hu : u ∈ X.V k)
    (hDu : unitsDerive A g u = 1) :
    ∃ z ∈ X.V k, u * (unitsNorm (K := K) A z)⁻¹ ∈ X.V (k + 1) := by
  rw [unitsDerive_apply, div_eq_one] at hDu
  have hgx : g • (((u : A) : L) - 1) - (((u : A) : L) - 1) ∈ X.latt (k + 1) := by
    rw [smul_sub, smul_one, ← coe_unitsAct, hDu, sub_self]; exact zero_mem _
  obtain ⟨y, hy, hxy⟩ := X.graded_H0 g hg hu hgx
  obtain ⟨z, hzV, hz⟩ := X.exists_unit_of_mem_latt hy
  refine ⟨z, hzV, X.mul_inv_mem_V (X.norm_mem_V hzV) ?_⟩
  rw [coe_unitsNorm, hz]
  simp_rw [smul_add, smul_one]
  have hr := X.prod_one_add_sub_mem' k (fun s => s • y) fun s => X.smul_mem_latt s hy
  have : ((u : A) : L) - ∏ s : G, (1 + s • y) =
      (((u : A) : L) - 1 - ∑ s : G, s • y) - (∏ s : G, (1 + s • y) - 1 - ∑ s : G, s • y) := by ring
  rw [this]
  exact sub_mem hxy hr

theorem step_H1 (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (k : ℕ) (u : Aˣ) (hu : u ∈ X.V k)
    (hNu : unitsNorm (K := K) A u = 1) :
    ∃ z ∈ X.V k, u * (unitsDerive A g z)⁻¹ ∈ X.V (k + 1) := by
  have hN : ∏ s : G, s • ((u : A) : L) = 1 := by
    rw [← coe_unitsNorm, hNu]; push_cast; rfl
  have hNx : ∑ t : G, t • (((u : A) : L) - 1) ∈ X.latt (k + 1) := by
    have hr := X.prod_one_add_sub_mem' k (fun s => s • (((u : A) : L) - 1))
      fun s => X.smul_mem_latt s hu
    have h1 : ∏ s : G, (1 + s • (((u : A) : L) - 1)) = 1 := by
      simp_rw [smul_sub, smul_one, add_sub_cancel]; exact hN
    rw [h1, sub_self, zero_sub] at hr
    simpa using neg_mem hr
  obtain ⟨y, hy, hxy⟩ := X.graded_H1 g hg hu hNx
  obtain ⟨z, hzV, hz⟩ := X.exists_unit_of_mem_latt hy
  refine ⟨z, hzV, ?_⟩
  rw [unitsDerive_apply, inv_div, div_eq_mul_inv, ← mul_assoc]
  refine X.mul_inv_mem_V (X.unitsAct_mem_V g hzV) ?_
  rw [coe_unitsAct, hz]
  push_cast
  rw [hz]
  have : ((u : A) : L) * (1 + y) - g • (1 + y) =
      (((u : A) : L) - 1 - (g • y - y)) + (((u : A) : L) - 1) * y := by
    rw [smul_add, smul_one]; ring
  rw [this]
  exact add_mem hxy (X.mul_mem_latt_succ hu hy)

end NBData
p2m_reactivate "P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex.M4aLocalCFT.CohTrivFI.NBData"

section Complete

variable [IsDiscreteValuationRing A]

noncomputable def W (k : ℕ) : Subgroup Aˣ :=
  (Units.map (Ideal.Quotient.mk ((maximalIdeal A) ^ (k + 1))).toMonoidHom).ker

theorem mem_W {k : ℕ} {u : Aˣ} : u ∈ W A k ↔ (u : A) - 1 ∈ (maximalIdeal A) ^ (k + 1) := by
  rw [W, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, ← Ideal.Quotient.eq]
  rfl

theorem smul_mem_maximalIdeal_pow (s : G) {n : ℕ} {x : A} (hx : x ∈ (maximalIdeal A) ^ n) :
    s • x ∈ (maximalIdeal A) ^ n := by
  have hle : Ideal.map (MulSemiringAction.toRingHom G A s) (maximalIdeal A) ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).1 hy
    have := hu.map (MulSemiringAction.toRingHom G A s⁻¹)
    simpa [MulSemiringAction.toRingHom_apply, inv_smul_smul] using this
  have := Ideal.mem_map_of_mem (MulSemiringAction.toRingHom G A s) hx
  rw [Ideal.map_pow, MulSemiringAction.toRingHom_apply] at this
  exact Ideal.pow_right_mono hle n this

theorem unitsAct_mem_W {k : ℕ} (s : G) {u : Aˣ} (hu : u ∈ W A k) : unitsAct A s u ∈ W A k := by
  rw [mem_W] at hu ⊢
  have : ((unitsAct A s u : Aˣ) : A) - 1 = s • ((u : A) - 1) := by
    rw [smul_sub, smul_one]; rfl
  rw [this]
  exact smul_mem_maximalIdeal_pow A s hu

theorem norm_mem_W {k : ℕ} {u : Aˣ} (hu : u ∈ W A k) : unitsNorm (K := K) A u ∈ W A k := by
  rw [unitsNorm_apply]
  exact prod_mem fun s _ => unitsAct_mem_W A s hu

theorem derive_mem_W (g : G) {k : ℕ} {u : Aˣ} (hu : u ∈ W A k) : unitsDerive A g u ∈ W A k := by
  rw [unitsDerive_apply]
  exact div_mem (unitsAct_mem_W A g hu) hu

theorem V_le_W (X : NBData K A) (k : ℕ) : X.V k ≤ W A k := by
  intro u hu
  rw [mem_W]
  have := X.latt_mem_pow hu
  convert this using 2
  rfl

theorem exists_W_le_V (X : NBData K A) : ∃ k₀, W A k₀ ≤ X.V 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  set e' : A := X.τ * (⟨X.d, X.dA⟩ * ⟨X.d, X.dA⟩) with he'
  have he0 : e' ≠ 0 := by
    have hd : (⟨X.d, X.dA⟩ : A) ≠ 0 := fun h => X.d0 (congrArg Subtype.val h)
    exact mul_ne_zero X.τ0 (mul_ne_zero hd hd)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible he0 hϖ
  have hspan : (maximalIdeal A) ^ n = Ideal.span {e'} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
    exact hn.symm
  refine ⟨n, fun u hu => ?_⟩
  rw [mem_W] at hu
  have hu' : (u : A) - 1 ∈ Ideal.span {e'} :=
    hspan ▸ Ideal.pow_le_pow_right (Nat.le_succ n) hu
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hu'
  rw [NBData.mem_V]
  have : ((u : A) : L) - 1 = X.e 0 * (X.d * (a : L)) := by
    have := congrArg (fun z : A => (z : L)) ha
    simp only [he'] at this
    push_cast at this
    rw [← this, NBData.e]; ring
  rw [this]
  exact X.base_mem_latt 0 a.2

variable [Finite (ResidueField A)]

scoped instance finiteIndex_W (k : ℕ) : (W A k).FiniteIndex := by
  haveI : Finite (A ⧸ maximalIdeal A) := ‹Finite (ResidueField A)›
  haveI : Finite (A ⧸ (maximalIdeal A) ^ (k + 1)) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _
  exact Subgroup.finiteIndex_ker _

theorem finiteIndex_V (X : NBData K A) : (X.V 0).FiniteIndex := by
  obtain ⟨k₀, hk₀⟩ := exists_W_le_V A X
  exact Subgroup.finiteIndex_of_le hk₀

variable [IsAdicComplete (maximalIdeal A) A]

theorem exists_limit (w : ℕ → Aˣ) (hw : ∀ k, w (k + 1) * (w k)⁻¹ ∈ W A k) :
    ∃ x : Aˣ, ∀ k, x * (w k)⁻¹ ∈ W A k := by
  let f : ℕ → A := fun k => (w k : A)
  have hstep : ∀ k, f (k + 1) - f k ∈ (maximalIdeal A) ^ (k + 1) := by
    intro k
    have := Ideal.mul_mem_right (w k : A) _ ((mem_W A).1 (hw k))
    rwa [sub_mul, one_mul, ← Units.val_mul, inv_mul_cancel_right] at this
  have hf : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (maximalIdeal A) ^ m • (⊤ : Submodule A A)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have : f m - f (n + 1) = (f m - f n) - (f (n + 1) - f n) := by ring
      rw [this]
      exact sub_mem ih (Ideal.pow_le_pow_right (by omega) (hstep n))
  obtain ⟨ℓ, hℓ⟩ := IsPrecomplete.prec' f hf
  have hℓ' : ∀ k, ℓ - f k ∈ (maximalIdeal A) ^ (k + 1) := by
    intro k
    have h1 := hℓ (k + 1)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    have : ℓ - f k = (f (k + 1) - f k) - (f (k + 1) - ℓ) := by ring
    rw [this]
    exact sub_mem (hstep k) h1
  have hℓu : IsUnit ℓ := by
    by_contra h
    have h0 : ℓ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 h
    have h1 : ℓ - f 0 ∈ maximalIdeal A := by simpa using hℓ' 0
    have : f 0 ∈ maximalIdeal A := by simpa using sub_mem h0 h1
    exact (IsLocalRing.mem_maximalIdeal _).1 this (w 0).isUnit
  refine ⟨hℓu.unit, fun k => ?_⟩
  rw [mem_W]
  have : ((hℓu.unit * (w k)⁻¹ : Aˣ) : A) - 1 = (ℓ - f k) * ((w k)⁻¹ : Aˣ) := by
    rw [Units.val_mul, hℓu.unit_spec, sub_mul, show f k * ((w k)⁻¹ : Aˣ) = 1 from (w k).mul_inv]
  rw [this]
  exact Ideal.mul_mem_right _ _ (hℓ' k)

theorem eq_one_of_forall_mem_W (x : Aˣ) (hx : ∀ k, x ∈ W A k) : x = 1 := by
  have : ∀ n, ((x : A) - 1) ≡ 0 [SMOD (maximalIdeal A) ^ n • (⊤ : Submodule A A)] := by
    intro n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) ((mem_W A).1 (hx n))
  have h := IsHausdorff.haus' _ this
  rw [sub_eq_zero] at h
  exact Units.ext h

theorem main (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ V : Subgroup Aˣ, V.FiniteIndex ∧
      (∀ s : G, ∀ v ∈ V, unitsAct A s v ∈ V) ∧
      (∀ v ∈ V, unitsDerive A g v = 1 → ∃ w ∈ V, unitsNorm (K := K) A w = v) ∧
      (∀ v ∈ V, unitsNorm (K := K) A v = 1 → ∃ w ∈ V, unitsDerive A g w = v) := by
  obtain ⟨X⟩ := nonempty_NBData K A
  refine ⟨X.V 0, finiteIndex_V A X, fun s v hv => X.unitsAct_mem_V s hv, ?_, ?_⟩
  · intro v hv hDv
    exact approx X.V (W A) (unitsNorm (K := K) A) (unitsDerive A g)
      (fun k => X.V_le (Nat.zero_le k)) (V_le_W A X) (fun k x hx => norm_mem_W A hx)
      (fun w hw => exists_limit A w fun k => V_le_W A X k (hw k))
      (eq_one_of_forall_mem_W A) (exists_W_le_V A X) (derive_norm K A g)
      (X.step_H0 g hg) v hv hDv
  · intro v hv hNv
    exact approx X.V (W A) (unitsDerive A g) (unitsNorm (K := K) A)
      (fun k => X.V_le (Nat.zero_le k)) (V_le_W A X) (fun k x hx => derive_mem_W A g hx)
      (fun w hw => exists_limit A w fun k => V_le_W A X k (hw k))
      (eq_one_of_forall_mem_W A) (exists_W_le_V A X) (norm_derive K A g)
      (X.step_H1 g hg) v hv hNv

end Complete
p2m_reactivate "P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex.M4aLocalCFT.CohTrivFI.NBData"

end CohTrivFI
p2m_reactivate "P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex.M4aLocalCFT.CohTrivFI.NBData P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex.M4aLocalCFT.CohTrivFI"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex.M4aLocalCFT.CohTrivFI.NBData P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex.M4aLocalCFT.CohTrivFI P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex.M4aLocalCFT"

theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
    [Finite (IsLocalRing.ResidueField A)]
    [Finite (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ V : Subgroup Aˣ, V.FiniteIndex ∧
      (∀ s : A.decompositionSubgroup K, ∀ v ∈ V, M4aLocalCFT.unitsAct A s v ∈ V) ∧
      (∀ v ∈ V, M4aLocalCFT.unitsDerive A g v = 1 →
        ∃ w ∈ V, M4aLocalCFT.unitsNorm (K := K) A w = v) ∧
      (∀ v ∈ V, M4aLocalCFT.unitsNorm (K := K) A v = 1 →
        ∃ w ∈ V, M4aLocalCFT.unitsDerive A g w = v) :=
  M4aLocalCFT.CohTrivFI.main A g hg

end S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex
end P2MW
export P2MW.S_M4aLocalCFT_unitsDecomp_exists_cohTrivial_finiteIndex (solution)
