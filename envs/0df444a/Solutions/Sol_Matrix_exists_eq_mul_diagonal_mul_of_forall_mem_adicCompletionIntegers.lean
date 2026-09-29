-- Prove2me | solution 1 for Matrix.exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/6ee8ad13-2f14-51e5-ac3f-ed731174fa4a

import Mathlib
import Definitions.Def_LocalLanglands_CartanDecomposition
import Theorems.Thm_LocalGL2_exists_cartanRel_cartanDiag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace HeckeCartan

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

def pr : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ)

theorem pr_prime : (pr v).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v).2

scoped instance factPr : Fact (pr v).Prime := ⟨pr_prime v⟩

theorem pr_ne_zero : pr v ≠ 0 := (pr_prime v).ne_zero

theorem natGenerator_eq_pr : Rat.HeightOneSpectrum.natGenerator v = pr v := rfl

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natCast_mem_asIdeal_iff_pr_dvd (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ pr v ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_eq_pr]

theorem pr_mem_asIdeal : (pr v : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_eq_pr]

theorem pr_notMem_asIdeal_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) :
    (pr v : 𝓞 ℚ) ∉ w.asIdeal := by
  rw [natCast_mem_asIdeal_iff]
  intro h
  have : Rat.HeightOneSpectrum.natGenerator w = pr v :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) (pr_prime v)).mp h
  apply hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext this

theorem asIdeal_eq_span_pr : v.asIdeal = Ideal.span {(pr v : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v
  rw [natGenerator_eq_pr] at h
  have h2 : v.asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) v.asIdeal) := by
    rw [Ideal.map_map]
    have : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ).comp
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) = RingHom.id _ := by
      ext x; simp
    rw [this, Ideal.map_id]
  rw [h2]
  erw [← h]
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp

theorem valuation_pr : v.valuation ℚ (pr v : ℚ) = WithZero.exp (-1) := by
  rw [show (pr v : ℚ) = algebraMap (𝓞 ℚ) ℚ (pr v) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast pr_ne_zero v)
    (asIdeal_eq_span_pr v)

theorem valued_algebraMap (r : ℚ) : Valued.v (algebraMap ℚ 𝕂 r) = v.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r

theorem algebraMap_natCast (n : ℕ) : algebraMap ℚ 𝕂 (n : ℚ) = (n : 𝕂) := map_natCast _ n

theorem valued_pr : Valued.v ((pr v : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_pr]

theorem pr_ne_zero' : ((pr v : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_pr v
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem natCast_mem_integers (n : ℕ) : ((n : ℕ) : 𝕂) ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap,
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one v _

theorem pr_mem_integers : ((pr v : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers v _

theorem valued_natCast_eq_one {n : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (n : w.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem natCast_ne_zero_of_notMem {n : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := valued_natCast_eq_one w hn
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem natCast_inv_mem_integers {n : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one w hn, inv_one]

theorem valued_le_one_of_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hx

theorem mem_integers_of_valued_le_one {x : 𝕂} (hx : Valued.v x ≤ 1) : x ∈ 𝓞v :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hx

theorem pr_inv_mul_mem_integers_iff {x : 𝕂} (hx : x ∈ 𝓞v) :
    ((pr v : ℕ) : 𝕂)⁻¹ * x ∈ 𝓞v ↔ Valued.v x < 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, valued_pr]
  by_cases hx0 : x = 0
  · simp [hx0]
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
      ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx0)).symm⟩
    rw [hm, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp,
      WithZero.exp_lt_exp]
    omega

theorem valued_lt_one_iff_ne_one {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x < 1 ↔ Valued.v x ≠ 1 :=
  ⟨fun h => h.ne, fun h => lt_of_le_of_ne (valued_le_one_of_mem v hx) h⟩

theorem valued_eq_one_of_mul_eq_one {x y : 𝕂} (hx : x ∈ 𝓞v) (hy : y ∈ 𝓞v) (h : x * y = 1) :
    Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, h, map_one]
  have hx1 := valued_le_one_of_mem v hx
  have hy1 := valued_le_one_of_mem v hy
  by_contra hne
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne
  have : Valued.v x * Valued.v y < 1 := by
    calc Valued.v x * Valued.v y ≤ Valued.v x * 1 := mul_le_mul_right hy1 _
      _ = Valued.v x := mul_one _
      _ < 1 := hlt
  rw [h1] at this
  exact lt_irrefl _ this

theorem inv_mem_integers_of_valued_eq_one {x : 𝕂} (h : Valued.v x = 1) : x⁻¹ ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

theorem irreducible_pr : Irreducible (⟨((pr v : ℕ) : 𝕂), pr_mem_integers v⟩ : 𝓞v) := by
  refine ⟨fun hu => ?_, fun x y hxy => ?_⟩
  · obtain ⟨u, hu⟩ := hu
    have h1 : Valued.v ((u : 𝓞v) : 𝕂) = 1 :=
      valued_eq_one_of_mul_eq_one v (u : 𝓞v).2 (↑(u⁻¹) : 𝓞v).2 (by
        rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl)
    rw [hu] at h1
    change Valued.v ((pr v : ℕ) : 𝕂) = 1 at h1
    rw [valued_pr, ← WithZero.exp_zero, WithZero.exp_inj] at h1
    norm_num at h1
  · have hval : Valued.v ((pr v : ℕ) : 𝕂) = Valued.v (x : 𝕂) * Valued.v (y : 𝕂) := by
      rw [← map_mul, ← Subring.coe_mul, ← hxy]
    rw [valued_pr] at hval
    have hx0 : (x : 𝕂) ≠ 0 := by
      intro h; rw [h, map_zero, zero_mul] at hval; exact WithZero.coe_ne_zero hval
    have hy0 : (y : 𝕂) ≠ 0 := by
      intro h; rw [h, map_zero, mul_zero] at hval; exact WithZero.coe_ne_zero hval
    obtain ⟨mx, hmx⟩ : ∃ m : ℤ, Valued.v (x : 𝕂) = WithZero.exp m :=
      ⟨WithZero.log _, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx0)).symm⟩
    obtain ⟨my, hmy⟩ : ∃ m : ℤ, Valued.v (y : 𝕂) = WithZero.exp m :=
      ⟨WithZero.log _, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hy0)).symm⟩
    have hx1 : mx ≤ 0 := by
      have := valued_le_one_of_mem v x.2
      rwa [hmx, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    have hy1 : my ≤ 0 := by
      have := valued_le_one_of_mem v y.2
      rwa [hmy, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    rw [hmx, hmy, ← WithZero.exp_add, WithZero.exp_inj] at hval
    have hunit : ∀ z : 𝓞v, Valued.v (z : 𝕂) = 1 → IsUnit z := fun z hz =>
      ⟨⟨z, ⟨(z : 𝕂)⁻¹, inv_mem_integers_of_valued_eq_one v hz⟩,
        Subtype.ext (mul_inv_cancel₀ (by intro h; rw [h, map_zero] at hz; exact zero_ne_one hz)),
        Subtype.ext (inv_mul_cancel₀ (by intro h; rw [h, map_zero] at hz; exact zero_ne_one hz))⟩, rfl⟩
    rcases (show mx = 0 ∨ my = 0 by omega) with h | h
    · left; apply hunit; rw [hmx, h, WithZero.exp_zero]
    · right; apply hunit; rw [hmy, h, WithZero.exp_zero]

end Places

section LocalMatrix

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def intMat : Subring M₂ where
  carrier := {M | ∀ i j, M i j ∈ 𝓞v}
  mul_mem' {A B} hA hB i j := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => mul_mem (hA i k) (hB k j)
  one_mem' i j := by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  add_mem' {A B} hA hB i j := by rw [Matrix.add_apply]; exact add_mem (hA i j) (hB i j)
  zero_mem' i j := by rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' {A} hA i j := by rw [Matrix.neg_apply]; exact neg_mem (hA i j)

theorem mem_intMat_iff (M : M₂) : M ∈ intMat v ↔ ∀ i j, M i j ∈ 𝓞v := Iff.rfl

theorem smul_mem_intMat {c : 𝕂} (hc : c ∈ 𝓞v) {M : M₂} (hM : M ∈ intMat v) : c • M ∈ intMat v :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

theorem det_mem_integers {M : M₂} (hM : M ∈ intMat v) : M.det ∈ 𝓞v := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

theorem adjugate_mem_intMat {M : M₂} (hM : M ∈ intMat v) : M.adjugate ∈ intMat v := by
  rw [Matrix.adjugate_fin_two]
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using hM 1 1
  · simpa using neg_mem (hM 0 1)
  · simpa using neg_mem (hM 1 0)
  · simpa using hM 0 0

theorem eq_smul_adjugate {M Mi : M₂} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    Mi = M.det⁻¹ • M.adjugate := by
  have hdet : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have key : Mi * (M * M.adjugate) = M.det • Mi := by
    rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one]
  rw [← mul_assoc, h2, one_mul] at key
  rw [key, smul_smul, inv_mul_cancel₀ hdet, one_smul]

theorem det_mul_det_eq_one {M Mi : M₂} (h1 : M * Mi = 1) : M.det * Mi.det = 1 := by
  rw [← Matrix.det_mul, h1, Matrix.det_one]

theorem valued_det_eq_one {M Mi : M₂} (hM : M ∈ intMat v) (hMi : Mi ∈ intMat v) (h1 : M * Mi = 1) :
    Valued.v M.det = 1 :=
  valued_eq_one_of_mul_eq_one v (det_mem_integers v hM) (det_mem_integers v hMi) (det_mul_det_eq_one v h1)

theorem inv_mem_intMat_of_valued_det {M Mi : M₂} (hM : M ∈ intMat v) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hdet : Valued.v M.det = 1) : Mi ∈ intMat v := by
  rw [eq_smul_adjugate v h1 h2]
  exact smul_mem_intMat v (inv_mem_integers_of_valued_eq_one v hdet) (adjugate_mem_intMat v hM)

theorem inv_apply_one_zero {M Mi : M₂} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    Mi 1 0 = -(M.det⁻¹ * M 1 0) := by
  rw [eq_smul_adjugate v h1 h2, Matrix.adjugate_fin_two]
  simp

theorem inv_apply_zero_zero {M Mi : M₂} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    Mi 0 0 = M.det⁻¹ * M 1 1 := by
  rw [eq_smul_adjugate v h1 h2, Matrix.adjugate_fin_two]
  simp

def tM : M₂ := !![1, 0; 0, ϖ]

theorem det_tM : (tM v).det = ϖ := by simp [tM, Matrix.det_fin_two_of]

theorem exists_exp_valued_det {Y : M₂} (hY : Y ∈ intMat v) (hdet : Y.det ≠ 0) :
    ∃ m : ℤ, m ≤ 0 ∧ Valued.v Y.det = WithZero.exp m := by
  have h0 : Valued.v Y.det ≠ 0 := (Valuation.ne_zero_iff _).2 hdet
  have hm : Valued.v Y.det = WithZero.exp (WithZero.log (Valued.v Y.det)) := (WithZero.exp_log h0).symm
  refine ⟨WithZero.log (Valued.v Y.det), ?_, hm⟩
  have := valued_le_one_of_mem v (det_mem_integers v hY)
  rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
  exact this

theorem valued_det_bounds {Y Yi : M₂} (h1 : Y * Yi = 1) (hY : Y ∈ intMat v) (hpYi : ϖ • Yi ∈ intMat v) :
    ∃ m : ℤ, -2 ≤ m ∧ m ≤ 0 ∧ Valued.v Y.det = WithZero.exp m := by
  have hdet0 : Y.det ≠ 0 := fun h => by
    have := det_mul_det_eq_one v h1; rw [h, zero_mul] at this; exact zero_ne_one this
  obtain ⟨m, hm0, hm⟩ := exists_exp_valued_det v hY hdet0
  refine ⟨m, ?_, hm0, hm⟩

  have h2 := valued_le_one_of_mem v (det_mem_integers v hpYi)
  rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, valued_pr] at h2
  have hYi : Valued.v Yi.det = (Valued.v Y.det)⁻¹ := by
    have := det_mul_det_eq_one v h1
    have h' : Valued.v Y.det * Valued.v Yi.det = 1 := by rw [← map_mul, this, map_one]
    exact eq_inv_of_mul_eq_one_right h'
  rw [hYi, hm, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at h2
  omega

variable {v} in

def liftInt (Y : M₂) (hY : Y ∈ intMat v) : Matrix (Fin 2) (Fin 2) 𝓞v := fun i j => ⟨Y i j, hY i j⟩

def coeMat : Matrix (Fin 2) (Fin 2) 𝓞v →+* M₂ :=
  (HeightOneSpectrum.adicCompletionIntegers ℚ v).subtype.mapMatrix

theorem coeMat_apply (Y : Matrix (Fin 2) (Fin 2) 𝓞v) (i j : Fin 2) : coeMat v Y i j = (Y i j : 𝕂) := rfl

theorem coeMat_liftInt (Y : M₂) (hY : Y ∈ intMat v) : coeMat v (liftInt Y hY) = Y := by
  ext i j; rfl

theorem coeMat_mem (Y : Matrix (Fin 2) (Fin 2) 𝓞v) : coeMat v Y ∈ intMat v := fun i j => (Y i j).2

theorem coeMat_det (Y : Matrix (Fin 2) (Fin 2) 𝓞v) : (coeMat v Y).det = (Y.det : 𝕂) :=
  (RingHom.map_det _ Y).symm

theorem exists_eq_mul_tM_mul {Y : M₂} (hY : Y ∈ intMat v) (hdet : Valued.v Y.det = WithZero.exp (-1)) :
    ∃ K1 K1i K2 K2i : M₂, K1 ∈ intMat v ∧ K1i ∈ intMat v ∧ K2 ∈ intMat v ∧ K2i ∈ intMat v ∧
      K1 * K1i = 1 ∧ K1i * K1 = 1 ∧ K2 * K2i = 1 ∧ K2i * K2 = 1 ∧ Y = K1 * tM v * K2 := by
  set Y' := liftInt Y hY with hY'
  have hdet0 : Y.det ≠ 0 := by
    intro h; rw [h, map_zero] at hdet; exact WithZero.zero_ne_coe hdet
  have hdet' : Y'.det ≠ 0 := by
    intro h
    apply hdet0
    rw [← coeMat_liftInt v Y hY, coeMat_det, ← hY', h]; rfl
  obtain ⟨a, b, hab, k₁, k₂, hk⟩ := LocalGL2.exists_cartanRel_cartanDiag (irreducible_pr v) Y' hdet'

  have hu : ∀ k : (Matrix (Fin 2) (Fin 2) 𝓞v)ˣ, Valued.v (coeMat v k.val).det = 1 := fun k =>
    valued_det_eq_one v (coeMat_mem v _) (coeMat_mem v (k⁻¹).val)
      (by rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
  have hsum : a + b = 1 := by
    have h1 : Y = coeMat v k₁.val *
        coeMat v (LocalGL2.cartanDiag (⟨((pr v : ℕ) : 𝕂), pr_mem_integers v⟩ : 𝓞v) a b) *
        coeMat v k₂.val := by
      rw [← map_mul, ← map_mul, ← hk, hY', coeMat_liftInt]
    have h2 := congrArg (fun M : M₂ => Valued.v M.det) h1
    simp only [Matrix.det_mul, map_mul] at h2
    rw [hdet, hu k₁, hu k₂, one_mul, mul_one, coeMat_det, LocalGL2.cartanDiag_det,
      SubmonoidClass.coe_pow] at h2
    change WithZero.exp (-1) = Valued.v (((pr v : ℕ) : 𝕂) ^ (a + b)) at h2
    rw [map_pow, valued_pr, ← WithZero.exp_nsmul, WithZero.exp_inj] at h2
    simp only [smul_eq_mul, nsmul_eq_mul, mul_neg, mul_one] at h2
    omega
  have ha : a = 0 := by omega
  have hb : b = 1 := by omega
  subst ha; subst hb
  have hdiag : coeMat v (LocalGL2.cartanDiag (⟨((pr v : ℕ) : 𝕂), pr_mem_integers v⟩ : 𝓞v) 0 1) = tM v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coeMat_apply, LocalGL2.cartanDiag, tM]
  refine ⟨coeMat v k₁.val, coeMat v (k₁⁻¹).val, coeMat v k₂.val, coeMat v (k₂⁻¹).val,
    coeMat_mem v _, coeMat_mem v _, coeMat_mem v _, coeMat_mem v _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  · rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  · rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  · rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  · rw [← hdiag, ← map_mul, ← map_mul, ← hk, hY', coeMat_liftInt]

theorem valued_det_eq_of_hecke {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1) (hY : Y ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hYi : Yi ∉ intMat v) (hpY : ϖ⁻¹ • Y ∉ intMat v) :
    Valued.v Y.det = WithZero.exp (-1) := by
  obtain ⟨m, hm2, hm0, hm⟩ := valued_det_bounds v h1 hY hpYi
  have hp0 := pr_ne_zero' v
  rcases (show m = 0 ∨ m = -1 ∨ m = -2 by omega) with rfl | rfl | rfl
  · exact absurd (inv_mem_intMat_of_valued_det v hY h1 h2 (by rw [hm, WithZero.exp_zero])) hYi
  · exact hm
  · exfalso
    apply hpY

    have hprod : (ϖ • Yi) * (ϖ⁻¹ • Y) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hp0, one_smul, h2]
    have hprod' : (ϖ⁻¹ • Y) * (ϖ • Yi) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul, h1]
    refine inv_mem_intMat_of_valued_det v hpYi hprod hprod' ?_
    have hYi' : Valued.v Yi.det = (Valued.v Y.det)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by rw [← map_mul, det_mul_det_eq_one v h1, map_one])
    rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, valued_pr, hYi', hm, ← WithZero.exp_nsmul,
      ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1

end LocalMatrix

end HeckeCartan
p2m_reactivate "P2MW.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers.HeckeCartan"

theorem solution
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ)
    (hpY : ¬ ∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) :
    ∃ K₁ K₁i K₂ K₂i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, K₁ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, K₁i i j ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ i j, K₂ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, K₂i i j ∈ v.adicCompletionIntegers ℚ) ∧
      K₁ * K₁i = 1 ∧ K₁i * K₁ = 1 ∧ K₂ * K₂i = 1 ∧ K₂i * K₂ = 1 ∧
      Y = K₁ * !![1, 0; 0, (p : v.adicCompletion ℚ)] * K₂ := by

  have hpr : HeckeCartan.pr v = p := by
    have h := (HeckeCartan.natCast_mem_asIdeal_iff_pr_dvd v p).1 hpv
    exact ((Nat.prime_dvd_prime_iff_eq (HeckeCartan.pr_prime v) hp).1 h)
  have hpYi' : ((HeckeCartan.pr v : ℕ) : v.adicCompletion ℚ) • Yi ∈ HeckeCartan.intMat v := by
    rw [hpr]; exact hpYi
  have hpY' : ((HeckeCartan.pr v : ℕ) : v.adicCompletion ℚ)⁻¹ • Y ∉ HeckeCartan.intMat v := by
    rw [hpr]; exact hpY
  have hdet := HeckeCartan.valued_det_eq_of_hecke v h1 h2 hY hpYi' hYi hpY'
  obtain ⟨K1, K1i, K2, K2i, hK1, hK1i, hK2, hK2i, e1, e2, e3, e4, hYeq⟩ :=
    HeckeCartan.exists_eq_mul_tM_mul v hY hdet
  refine ⟨K1, K1i, K2, K2i, hK1, hK1i, hK2, hK2i, e1, e2, e3, e4, ?_⟩
  rw [hYeq, HeckeCartan.tM, hpr]

end
p2m_reactivate "P2MW.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers.HeckeCartan"

end S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
end P2MW
export P2MW.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers (solution)
