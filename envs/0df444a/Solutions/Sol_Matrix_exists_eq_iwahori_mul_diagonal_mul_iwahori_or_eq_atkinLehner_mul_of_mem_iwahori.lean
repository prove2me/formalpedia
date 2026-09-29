-- Prove2me | solution 1 for Matrix.exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cdaae5a8-6aec-51dc-88a4-58c75be87599

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori

section LevelULocalBlock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LevelULocal

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

def tMi : M₂ := !![1, 0; 0, ϖ⁻¹]

def tbM : M₂ := !![ϖ, 0; 0, 1]

def tbMi : M₂ := !![ϖ⁻¹, 0; 0, 1]

def wM : M₂ := !![0, 1; 1, 0]

theorem tM_mul_tMi : tM v * tMi v = 1 := by
  ext i j : 1; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ (pr_ne_zero' v)]

theorem tMi_mul_tM : tMi v * tM v = 1 := by
  ext i j : 1; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ (pr_ne_zero' v)]

theorem tbM_mul_tM : tbM v * tM v = ϖ • (1 : M₂) := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tM, tbM, Matrix.mul_apply, Fin.sum_univ_two]
theorem tM_mul_tbM : tM v * tbM v = ϖ • (1 : M₂) := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tM, tbM, Matrix.mul_apply, Fin.sum_univ_two]
theorem tMi_mul_tbMi : tMi v * tbMi v = ϖ⁻¹ • (1 : M₂) := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tMi, tbMi, Matrix.mul_apply, Fin.sum_univ_two]
theorem smul_tMi : ϖ • tMi v = tbM v := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tMi, tbM, mul_inv_cancel₀ (pr_ne_zero' v)]
theorem smul_tbMi : ϖ • tbMi v = tM v := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tbMi, tM, mul_inv_cancel₀ (pr_ne_zero' v)]
theorem wM_mul_wM : wM v * wM v = 1 := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [wM, Matrix.mul_apply, Fin.sum_univ_two]
theorem tM_mul_wM : tM v * wM v = wM v * tbM v := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [wM, tM, tbM, Matrix.mul_apply, Fin.sum_univ_two]
theorem wM_mul_tMi : wM v * tMi v = tbMi v * wM v := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [wM, tMi, tbMi, Matrix.mul_apply, Fin.sum_univ_two]
theorem det_tM : (tM v).det = ϖ := by simp [tM, Matrix.det_fin_two_of]

theorem det_tbM : (tbM v).det = ϖ := by simp [tbM, Matrix.det_fin_two_of]

theorem tM_mem : tM v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [tM, one_mem, zero_mem, pr_mem_integers v]

theorem tbM_mem : tbM v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [tbM, one_mem, zero_mem, pr_mem_integers v]

theorem wM_mem : wM v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [wM, one_mem, zero_mem]

theorem wM_apply_one_one (k : M₂) : (k * wM v) 1 1 = k 1 0 := by
  simp [wM, Matrix.mul_apply, Fin.sum_univ_two]

theorem tMi_mul_mul_tM (Y : M₂) : tMi v * Y * tM v = !![Y 0 0, ϖ * Y 0 1; ϖ⁻¹ * Y 1 0, Y 1 1] := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := pr_ne_zero' v
  fin_cases i <;> fin_cases j <;> simp [tM, tMi] <;> field_simp

theorem tMi_mul_mul_tbM (Y : M₂) : tMi v * Y * tbM v = !![ϖ * Y 0 0, Y 0 1; Y 1 0, ϖ⁻¹ * Y 1 1] := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := pr_ne_zero' v
  fin_cases i <;> fin_cases j <;> simp [tbM, tMi] <;> field_simp

theorem tbMi_mul_mul_tM (Y : M₂) : tbMi v * Y * tM v = !![ϖ⁻¹ * Y 0 0, Y 0 1; Y 1 0, ϖ * Y 1 1] := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := pr_ne_zero' v
  fin_cases i <;> fin_cases j <;> simp [tM, tbMi] <;> field_simp

theorem tMi_mul_mul_tM_mem_iff {Y : M₂} (hY : Y ∈ intMat v) :
    tMi v * Y * tM v ∈ intMat v ↔ Valued.v (Y 1 0) < 1 := by
  rw [← pr_inv_mul_mem_integers_iff v (hY 1 0), tMi_mul_mul_tM, mem_intMat_iff]
  constructor
  · intro h; simpa using h 1 0
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using hY 0 0
    · simpa using mul_mem (pr_mem_integers v) (hY 0 1)
    · simpa using h
    · simpa using hY 1 1

theorem tMi_mul_mul_tbM_mem_iff {Y : M₂} (hY : Y ∈ intMat v) :
    tMi v * Y * tbM v ∈ intMat v ↔ Valued.v (Y 1 1) < 1 := by
  rw [← pr_inv_mul_mem_integers_iff v (hY 1 1), tMi_mul_mul_tbM, mem_intMat_iff]
  constructor
  · intro h; simpa using h 1 1
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using mul_mem (pr_mem_integers v) (hY 0 0)
    · simpa using hY 0 1
    · simpa using hY 1 0
    · simpa using h

theorem tbMi_mul_mul_tM_mem_iff {Y : M₂} (hY : Y ∈ intMat v) :
    tbMi v * Y * tM v ∈ intMat v ↔ Valued.v (Y 0 0) < 1 := by
  rw [← pr_inv_mul_mem_integers_iff v (hY 0 0), tbMi_mul_mul_tM, mem_intMat_iff]
  constructor
  · intro h; simpa using h 0 0
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using h
    · simpa using hY 0 1
    · simpa using hY 1 0
    · simpa using mul_mem (pr_mem_integers v) (hY 1 1)

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

end LocalMatrix

section LocalMatrix2

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

theorem tbMi_mul_tMi : tbMi v * tMi v = ϖ⁻¹ • (1 : M₂) := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tMi, tbMi, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_tbMi : (tbMi v).det = ϖ⁻¹ := by simp [tbMi, Matrix.det_fin_two_of]

theorem det_tMi : (tMi v).det = ϖ⁻¹ := by simp [tMi, Matrix.det_fin_two_of]

theorem conj_mem_intMat {P Pi Y : M₂} (hP : P ∈ intMat v) (hPi : Pi ∈ intMat v) (hY : Y ∈ intMat v) :
    Pi * Y * P ∈ intMat v :=
  (intMat v).mul_mem ((intMat v).mul_mem hPi hY) hP

theorem conj_mem_intMat_iff {P Pi Y : M₂} (hP : P ∈ intMat v) (hPi : Pi ∈ intMat v)
    (h1 : P * Pi = 1) (h2 : Pi * P = 1) : Pi * Y * P ∈ intMat v ↔ Y ∈ intMat v := by
  refine ⟨fun h => ?_, conj_mem_intMat v hP hPi⟩
  have := conj_mem_intMat v hPi hP h
  have e : P * (Pi * Y * P) * Pi = (P * Pi) * Y * (P * Pi) := by noncomm_ring
  rwa [e, h1, one_mul, mul_one] at this

theorem valued_det_eq_sq {X Xi : M₂} {c : 𝕂} (hc : c ≠ 0) (h1 : X * Xi = 1)
    (hX : c⁻¹ • X ∈ intMat v) (hXi : c • Xi ∈ intMat v) : Valued.v X.det = Valued.v c ^ 2 := by
  have hprod : (c⁻¹ • X) * (c • Xi) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, h1]
  have := valued_det_eq_one v hX hXi hprod
  rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, map_inv₀] at this
  have hcv : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  calc Valued.v X.det = Valued.v c ^ 2 * ((Valued.v c)⁻¹ ^ 2 * Valued.v X.det) := by field_simp
    _ = Valued.v c ^ 2 := by rw [this, mul_one]

end LocalMatrix2

section Eichler

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def dM (e : ℕ) : M₂ := !![1, 0; 0, ϖ ^ e]

def dMi (e : ℕ) : M₂ := !![1, 0; 0, (ϖ ^ e)⁻¹]

def E00 : M₂ := !![1, 0; 0, 0]

def E01 : M₂ := !![0, 1; 0, 0]

theorem prpow_ne_zero (e : ℕ) : (ϖ ^ e : 𝕂) ≠ 0 := pow_ne_zero _ (pr_ne_zero' v)
theorem prpow_mem_integers (e : ℕ) : (ϖ ^ e : 𝕂) ∈ 𝓞v := pow_mem (pr_mem_integers v) e

theorem dM_mul_dMi (e : ℕ) : dM v e * dMi v e = 1 := by
  ext i j : 1; fin_cases i <;> fin_cases j <;>
    simp [dM, dMi, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ (prpow_ne_zero v e)]
theorem dMi_mul_dM (e : ℕ) : dMi v e * dM v e = 1 := by
  ext i j : 1; fin_cases i <;> fin_cases j <;>
    simp [dM, dMi, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ (prpow_ne_zero v e)]
theorem dM_mem (e : ℕ) : dM v e ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [dM, one_mem, zero_mem, prpow_mem_integers v e]
theorem E00_mem : E00 v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E00, one_mem, zero_mem]
theorem E01_mem : E01 v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E01, one_mem, zero_mem]

theorem mul_E00_apply (Y : M₂) :
    (Y * E00 v) 0 0 = Y 0 0 ∧ (Y * E00 v) 0 1 = 0 ∧ (Y * E00 v) 1 0 = Y 1 0 ∧ (Y * E00 v) 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [E00, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_E00_mem_iff (Y : M₂) : Y * E00 v ∈ intMat v ↔ Y 0 0 ∈ 𝓞v ∧ Y 1 0 ∈ 𝓞v := by
  obtain ⟨h00, h01, h10, h11⟩ := mul_E00_apply v Y
  rw [mem_intMat_iff]
  constructor
  · intro h; exact ⟨h00 ▸ h 0 0, h10 ▸ h 1 0⟩
  · rintro ⟨a0, a1⟩ i j
    fin_cases i <;> fin_cases j
    · simpa [h00] using a0
    · simp [h01, zero_mem]
    · simpa [h10] using a1
    · simp [h11, zero_mem]

theorem E00_mul_mul_eq (X : M₂) : E00 v * X * (1 - E00 v) = (X 0 1) • E01 v := by
  ext i j : 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00, E01]

theorem dMi_mul_mul_dM (e : ℕ) (Y : M₂) :
    dMi v e * Y * dM v e = !![Y 0 0, ϖ ^ e * Y 0 1; (ϖ ^ e)⁻¹ * Y 1 0, Y 1 1] := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := prpow_ne_zero v e
  fin_cases i <;> fin_cases j <;> simp [dM, dMi] <;> field_simp

theorem dMi_mul' (e : ℕ) (Y : M₂) :
    dMi v e * Y = !![Y 0 0, Y 0 1; (ϖ ^ e)⁻¹ * Y 1 0, (ϖ ^ e)⁻¹ * Y 1 1] := by
  ext i j : 1
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [dMi]

theorem dMi_mul_mul_dM_mem_iff (e : ℕ) {Y : M₂} (hY : Y ∈ intMat v) :
    dMi v e * Y * dM v e ∈ intMat v ↔ (ϖ ^ e)⁻¹ * Y 1 0 ∈ 𝓞v := by
  rw [dMi_mul_mul_dM, mem_intMat_iff]
  constructor
  · intro h; simpa using h 1 0
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using hY 0 0
    · simpa using mul_mem (prpow_mem_integers v e) (hY 0 1)
    · simpa using h
    · simpa using hY 1 1

theorem dMi_mul_mem_iff (e : ℕ) (Y : M₂) :
    dMi v e * Y ∈ intMat v ↔
      (Y 0 0 ∈ 𝓞v ∧ Y 0 1 ∈ 𝓞v) ∧ ((ϖ ^ e)⁻¹ * Y 1 0 ∈ 𝓞v ∧ (ϖ ^ e)⁻¹ * Y 1 1 ∈ 𝓞v) := by
  rw [dMi_mul', mem_intMat_iff]
  constructor
  · intro h; exact ⟨⟨by simpa using h 0 0, by simpa using h 0 1⟩, ⟨by simpa using h 1 0, by simpa using h 1 1⟩⟩
  · rintro ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩ i j
    fin_cases i <;> fin_cases j
    · simpa using h00
    · simpa using h01
    · simpa using h10
    · simpa using h11

theorem conj_mem_intMat_of_inv_mul_dM_mem (e : ℕ) {η ηi X : M₂} (h2 : ηi * η = 1)
    (hη : η ∈ intMat v) (hηid : ηi * dM v e ∈ intMat v)
    (hX : X ∈ intMat v) (hXd : dMi v e * X * dM v e ∈ intMat v) :
    ηi * X * η ∈ intMat v := by
  have key : ∀ Z : M₂, dMi v e * Z ∈ intMat v → ηi * Z * η ∈ intMat v := by
    intro Z hZ
    have eq : ηi * Z * η = (ηi * dM v e) * (dMi v e * Z) * η := by
      calc ηi * Z * η = ηi * (dM v e * dMi v e) * Z * η := by rw [dM_mul_dMi, mul_one]
        _ = (ηi * dM v e) * (dMi v e * Z) * η := by noncomm_ring
    rw [eq]; exact (intMat v).mul_mem ((intMat v).mul_mem hηid hZ) hη
  have h10 : (ϖ ^ e)⁻¹ * X 1 0 ∈ 𝓞v := (dMi_mul_mul_dM_mem_iff v e hX).1 hXd
  obtain ⟨s00, s01, s10, s11⟩ := mul_E00_apply v X

  have hdec : X = X * E00 v + (X 0 1) • E01 v + ((X 1 1) • (1 : M₂) - (X 1 1) • E00 v) := by
    ext i j : 1
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [E00, E01, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : ηi * (X * E00 v) * η ∈ intMat v := by
    refine key _ ((dMi_mul_mem_iff v e _).2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩)
    · rw [s00]; exact hX 0 0
    · rw [s01]; exact zero_mem _
    · rw [s10]; exact h10
    · rw [s11, mul_zero]; exact zero_mem _
  have h2' : ηi * ((X 0 1) • E01 v) * η ∈ intMat v := by
    refine key _ ((dMi_mul_mem_iff v e _).2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩) <;>
      simp [E01, Matrix.smul_apply, hX 0 1, zero_mem]
  have h3 : ηi * ((X 1 1) • (1 : M₂) - (X 1 1) • E00 v) * η ∈ intMat v := by
    have eq : ηi * ((X 1 1) • (1 : M₂) - (X 1 1) • E00 v) * η =
        (X 1 1) • (ηi * η) - (X 1 1) • (ηi * E00 v * η) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [eq, h2]
    refine sub_mem (smul_mem_intMat v (hX 1 1) (one_mem _)) (smul_mem_intMat v (hX 1 1) (key _ ?_))
    refine (dMi_mul_mem_iff v e _).2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [E00, one_mem, zero_mem]
  rw [hdec, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  exact add_mem (add_mem h1 h2') h3

theorem valued_mul_lt_one_of_lt {x y : 𝕂} (hx : Valued.v x < 1) (hy : Valued.v y ≤ 1) : Valued.v (x * y) < 1 := by
  rw [map_mul]
  calc Valued.v x * Valued.v y ≤ Valued.v x * 1 := mul_le_mul_right hy _
    _ = Valued.v x := mul_one _
    _ < 1 := hx

theorem valued_eq_one_or {K1 K1i : M₂} (hK1 : K1 ∈ intMat v) (hK1i : K1i ∈ intMat v) (hKK1 : K1 * K1i = 1) :
    Valued.v (K1 0 0) = 1 ∨ Valued.v (K1 1 0) = 1 := by
  by_contra hne
  push Not at hne
  have h00 : Valued.v (K1 0 0) < 1 := lt_of_le_of_ne (valued_le_one_of_mem v (hK1 0 0)) hne.1
  have h10 : Valued.v (K1 1 0) < 1 := lt_of_le_of_ne (valued_le_one_of_mem v (hK1 1 0)) hne.2
  have hdet := valued_det_eq_one v hK1 hK1i hKK1
  rw [Matrix.det_fin_two] at hdet
  have hlt : Valued.v (K1 0 0 * K1 1 1 - K1 0 1 * K1 1 0) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · exact valued_mul_lt_one_of_lt v h00 (valued_le_one_of_mem v (hK1 1 1))
    · rw [mul_comm]; exact valued_mul_lt_one_of_lt v h10 (valued_le_one_of_mem v (hK1 0 1))
  rw [hdet] at hlt
  exact lt_irrefl _ hlt

theorem inv_mul_E00_mem_of_conj_mem {η ηi K1 K1i K2 K2i : M₂}
    (hK1 : K1 ∈ intMat v) (hK1i : K1i ∈ intMat v) (hK2i : K2i ∈ intMat v)
    (hKK1 : K1 * K1i = 1) (hKK2 : K2 * K2i = 1) (hη : η = K1 * tM v * K2)
    (hc00 : ηi * E00 v * η ∈ intMat v) (hc01 : ηi * E01 v * η ∈ intMat v) :
    ηi * E00 v ∈ intMat v := by
  have m00 : E00 v * (K1 * tM v * K2) * K2i * E00 v = (K1 0 0) • E00 v := by
    have : E00 v * (K1 * tM v * K2) * K2i * E00 v = E00 v * K1 * tM v * (K2 * K2i) * E00 v := by noncomm_ring
    rw [this, hKK2, mul_one]
    ext i j : 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [E00, tM]
  have m01 : E01 v * (K1 * tM v * K2) * K2i * E00 v = (K1 1 0) • E00 v := by
    have : E01 v * (K1 * tM v * K2) * K2i * E00 v = E01 v * K1 * tM v * (K2 * K2i) * E00 v := by noncomm_ring
    rw [this, hKK2, mul_one]
    ext i j : 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [E00, E01, tM]
  have hα : (K1 0 0) • (ηi * E00 v) ∈ intMat v := by
    have eq : (K1 0 0) • (ηi * E00 v) = (ηi * E00 v * η) * K2i * E00 v := by
      rw [hη, ← Matrix.mul_smul, ← m00]; noncomm_ring
    rw [eq]; exact (intMat v).mul_mem ((intMat v).mul_mem hc00 hK2i) (E00_mem v)
  have hγ : (K1 1 0) • (ηi * E00 v) ∈ intMat v := by
    have eq : (K1 1 0) • (ηi * E00 v) = (ηi * E01 v * η) * K2i * E00 v := by
      rw [hη, ← Matrix.mul_smul, ← m01]; noncomm_ring
    rw [eq]; exact (intMat v).mul_mem ((intMat v).mul_mem hc01 hK2i) (E00_mem v)
  rcases valued_eq_one_or v hK1 hK1i hKK1 with hu | hu
  · have hne : K1 0 0 ≠ 0 := fun h0 => by rw [h0, map_zero] at hu; exact zero_ne_one hu
    have : ηi * E00 v = (K1 0 0)⁻¹ • ((K1 0 0) • (ηi * E00 v)) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]; exact smul_mem_intMat v (inv_mem_integers_of_valued_eq_one v hu) hα
  · have hne : K1 1 0 ≠ 0 := fun h0 => by rw [h0, map_zero] at hu; exact zero_ne_one hu
    have : ηi * E00 v = (K1 1 0)⁻¹ • ((K1 1 0) • (ηi * E00 v)) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]; exact smul_mem_intMat v (inv_mem_integers_of_valued_eq_one v hu) hγ

theorem inv_mul_dM_mem_of_inv_mul_E00_mem {e : ℕ} (he : 1 ≤ e) {ηi : M₂}
    (hpηi : ϖ • ηi ∈ intMat v) (h00 : ηi * E00 v ∈ intMat v) : ηi * dM v e ∈ intMat v := by
  have hd : dM v e = E00 v + (ϖ ^ (e - 1)) • (ϖ • ((1 : M₂) - E00 v)) := by
    rw [smul_smul, ← pow_succ, Nat.sub_add_cancel he]
    ext i j : 1; fin_cases i <;> fin_cases j <;> simp [dM, E00]
  rw [hd, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one]
  exact add_mem h00 (smul_mem_intMat v (prpow_mem_integers v _) (sub_mem hpηi ((intMat v).mul_mem hpηi (E00_mem v))))

theorem valued_apply_one_one_eq_one {e : ℕ} (he : 1 ≤ e) {η ηi : M₂} (h1 : η * ηi = 1) (h2 : ηi * η = 1)
    (hη : η ∈ intMat v) (hdet : Valued.v η.det = Valued.v ϖ)
    (h10 : (ϖ ^ e)⁻¹ * η 1 0 ∈ 𝓞v) (h00 : ηi * E00 v ∉ intMat v) :
    Valued.v (η 1 1) = 1 := by
  by_contra hne
  have hlt : Valued.v (η 1 1) < 1 := lt_of_le_of_ne (valued_le_one_of_mem v (hη 1 1)) hne
  have hp0 := pr_ne_zero' v
  have hdet0 : η.det ≠ 0 := fun h => by
    have := det_mul_det_eq_one v h1; rw [h, zero_mul] at this; exact zero_ne_one this
  have hu : Valued.v (η.det⁻¹ * ϖ) = 1 := by
    rw [map_mul, map_inv₀, hdet, inv_mul_cancel₀]
    rw [valued_pr]; exact WithZero.coe_ne_zero
  have hdp : η.det⁻¹ * ϖ ∈ 𝓞v := mem_integers_of_valued_le_one v hu.le
  apply h00
  rw [mul_E00_mem_iff]
  constructor
  ·
    have e1 : ηi 0 0 = (η.det⁻¹ * ϖ) * (ϖ⁻¹ * η 1 1) := by
      rw [inv_apply_zero_zero v h1 h2]; field_simp
    rw [e1]; exact mul_mem hdp ((pr_inv_mul_mem_integers_iff v (hη 1 1)).2 hlt)
  ·
    have e1 : ηi 1 0 = -((η.det⁻¹ * ϖ) * (ϖ ^ (e - 1) * ((ϖ ^ e)⁻¹ * η 1 0))) := by
      rw [inv_apply_one_zero v h1 h2,
        show (ϖ ^ e : 𝕂) = ϖ ^ (e - 1) * ϖ by rw [← pow_succ, Nat.sub_add_cancel he]]
      have hpe : (ϖ ^ (e - 1) : 𝕂) ≠ 0 := pow_ne_zero _ hp0
      field_simp
    rw [e1]; exact neg_mem (mul_mem hdp (mul_mem (prpow_mem_integers v _) h10))

theorem dMi_mul_inv_mul_mem {e : ℕ} {η ηi Y : M₂} (h1 : η * ηi = 1)
    (h10 : (ϖ ^ e)⁻¹ * η 1 0 ∈ 𝓞v) (h11 : Valued.v (η 1 1) = 1)
    (hA : ηi * Y ∈ intMat v) (hdY : dMi v e * Y ∈ intMat v) :
    dMi v e * (ηi * Y) ∈ intMat v := by
  set A := ηi * Y with hAdef
  have hYA : Y = η * A := by rw [hAdef, ← mul_assoc, h1, one_mul]
  have hne : η 1 1 ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
  have hinv : (η 1 1)⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v h11
  rw [dMi_mul_mem_iff] at hdY ⊢
  obtain ⟨-, hr10, hr11⟩ := hdY
  have hYj : ∀ j, Y 1 j = η 1 0 * A 0 j + η 1 1 * A 1 j := by
    intro j; rw [hYA, Matrix.mul_apply, Fin.sum_univ_two]
  have key : ∀ j, (ϖ ^ e)⁻¹ * Y 1 j ∈ 𝓞v → (ϖ ^ e)⁻¹ * A 1 j ∈ 𝓞v := by
    intro j hj
    have eq : (ϖ ^ e)⁻¹ * A 1 j = (η 1 1)⁻¹ * ((ϖ ^ e)⁻¹ * Y 1 j - ((ϖ ^ e)⁻¹ * η 1 0) * A 0 j) := by
      rw [hYj]; field_simp; ring
    rw [eq]; exact mul_mem hinv (sub_mem hj (mul_mem h10 (hA 0 j)))
  exact ⟨⟨hA 0 0, hA 0 1⟩, ⟨key 0 hr10, key 1 hr11⟩⟩

end Eichler

section Peirce

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def E10 : M₂ := !![0, 0; 1, 0]

def E11 : M₂ := !![0, 0; 0, 1]

theorem E10_mem : E10 v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E10, one_mem, zero_mem]
theorem E11_mem : E11 v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E11, one_mem, zero_mem]

theorem eq_sum_smul_E (X : M₂) :
    X = (X 0 0) • E00 v + (X 0 1) • E01 v + (X 1 0) • E10 v + (X 1 1) • E11 v := by
  ext i j : 1
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00, E01, E10, E11]

theorem E00_mul_mul_E00 (X : M₂) : E00 v * X * E00 v = (X 0 0) • E00 v := by
  ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00]
theorem E00_mul_mul_E11 (X : M₂) : E00 v * X * E11 v = (X 0 1) • E01 v := by
  ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00, E01, E11]
theorem E11_mul_mul_E00 (X : M₂) : E11 v * X * E00 v = (X 1 0) • E10 v := by
  ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00, E10, E11]
theorem E11_mul_mul_E11 (X : M₂) : E11 v * X * E11 v = (X 1 1) • E11 v := by
  ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E11]
theorem E10_mul_E01 : E10 v * E01 v = E11 v := by
  ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [E01, E10, E11]
theorem E01_mul_E10 : E01 v * E10 v = E00 v := by
  ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [E00, E01, E10]
theorem smul_E_mul_smul_E {x y : 𝕂} (A B C : M₂) (h : A * B = C) : (x • A) * (y • B) = (x * y) • C := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h]

theorem iwahori_generators :
    (E00 v ∈ intMat v ∧ ϖ⁻¹ * (E00 v) 1 0 ∈ 𝓞v) ∧ (E01 v ∈ intMat v ∧ ϖ⁻¹ * (E01 v) 1 0 ∈ 𝓞v) ∧
    (E11 v ∈ intMat v ∧ ϖ⁻¹ * (E11 v) 1 0 ∈ 𝓞v) ∧ (ϖ • E10 v ∈ intMat v ∧ ϖ⁻¹ * (ϖ • E10 v) 1 0 ∈ 𝓞v) := by
  have hp0 := pr_ne_zero' v
  refine ⟨⟨E00_mem v, ?_⟩, ⟨E01_mem v, ?_⟩, ⟨E11_mem v, ?_⟩, ⟨smul_mem_intMat v (pr_mem_integers v) (E10_mem v), ?_⟩⟩ <;>
    simp [E00, E01, E10, E11, Matrix.smul_apply, zero_mem, inv_mul_cancel₀ hp0, one_mem]

theorem mem_integers_of_forall_pow {x : 𝕂} (k : ℕ) (h : ∀ n : ℕ, ϖ ^ k * x ^ n ∈ 𝓞v) : x ∈ 𝓞v := by
  by_contra hx
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hx
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at hx; exact not_lt_zero hx
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
    ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx0)).symm⟩
  have hm1 : 1 ≤ m := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx; omega
  have := valued_le_one_of_mem v (h (k + 1))
  rw [map_mul, map_pow, map_pow, valued_pr, hm, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp] at this
  simp only [smul_eq_mul, nsmul_eq_mul] at this
  push_cast at this
  nlinarith

theorem exists_iwahori_mul_tbM_mul {Y : M₂} (hY : Y ∈ intMat v) (h00 : ϖ⁻¹ * Y 0 0 ∈ 𝓞v) (h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v)
    (h11 : Valued.v (Y 1 1) = 1) (hdet : Valued.v Y.det = Valued.v ϖ) :
    ∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tbM v * ι' := by
  have hp0 := pr_ne_zero' v
  set α := ϖ⁻¹ * Y 0 0 with hα
  set γ := ϖ⁻¹ * Y 1 0 with hγ
  set β := Y 0 1 with hβ
  set δ := Y 1 1 with hδ
  have hδ0 : δ ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
  have hδi : δ⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v h11
  have hY00 : Y 0 0 = ϖ * α := by rw [hα, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  have hY10 : Y 1 0 = ϖ * γ := by rw [hγ, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  set α' := α - β * γ * δ⁻¹ with hα'
  have hα'O : α' ∈ 𝓞v := sub_mem h00 (mul_mem (mul_mem (hY 0 1) h10) hδi)
  have hdet' : Y.det = ϖ * (α' * δ) := by
    rw [Matrix.det_fin_two, hY00, hY10, hα']; field_simp; ring
  have hαδ : Valued.v (α' * δ) = 1 := by
    have := hdet; rw [hdet', map_mul] at this
    have hv0 : Valued.v ϖ ≠ 0 := by rw [valued_pr]; exact WithZero.coe_ne_zero
    calc Valued.v (α' * δ) = (Valued.v ϖ)⁻¹ * (Valued.v ϖ * Valued.v (α' * δ)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hv0, one_mul]
      _ = 1 := by rw [this, inv_mul_cancel₀ hv0]
  have hα'v : Valued.v α' = 1 := by
    rw [map_mul, h11, mul_one] at hαδ; exact hαδ
  have hα'0 : α' ≠ 0 := fun h0 => by rw [h0, map_zero] at hα'v; exact zero_ne_one hα'v
  have hα'i : α'⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v hα'v
  have hβO : β ∈ 𝓞v := hY 0 1
  have hδO : δ ∈ 𝓞v := hY 1 1
  have hx : ϖ * γ * δ⁻¹ ∈ 𝓞v := mul_mem (mul_mem (pr_mem_integers v) h10) hδi
  have hnx : -(ϖ * γ * δ⁻¹) ∈ 𝓞v := neg_mem hx
  have hy : -(β * α'⁻¹ * δ⁻¹) ∈ 𝓞v := neg_mem (mul_mem (mul_mem hβO hα'i) hδi)
  refine ⟨!![α', β; 0, δ], !![α'⁻¹, -(β * α'⁻¹ * δ⁻¹); 0, δ⁻¹], !![1, 0; ϖ * γ * δ⁻¹, 1], !![1, 0; -(ϖ * γ * δ⁻¹), 1],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hα'O, hβO, zero_mem, hδO]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hα'i, hδi, zero_mem, hy]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hx]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hnx]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [zero_mem]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ϖ⁻¹ * (ϖ * γ * δ⁻¹) = γ * δ⁻¹ by field_simp]
    exact mul_mem h10 hδi
  · ext i j : 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [tbM, hY00, hY10, hα'] <;> (try field_simp) <;> ring

theorem exists_iwahori_mul_tM_mul {Y : M₂} (hY : Y ∈ intMat v) (h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v) (h11 : ϖ⁻¹ * Y 1 1 ∈ 𝓞v)
    (h00 : Valued.v (Y 0 0) = 1) (hdet : Valued.v Y.det = Valued.v ϖ) :
    ∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tM v * ι' := by
  have hp0 := pr_ne_zero' v
  set a := Y 0 0 with ha
  set b := Y 0 1 with hb
  set c := ϖ⁻¹ * Y 1 0 with hc
  set d := ϖ⁻¹ * Y 1 1 with hd
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, map_zero] at h00; exact zero_ne_one h00
  have hai : a⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v h00
  have hY10 : Y 1 0 = ϖ * c := by rw [hc, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  have hY11 : Y 1 1 = ϖ * d := by rw [hd, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  set d' := d - c * b * a⁻¹ with hd'
  have hd'O : d' ∈ 𝓞v := sub_mem h11 (mul_mem (mul_mem h10 (hY 0 1)) hai)
  have hdet' : Y.det = ϖ * (a * d') := by
    rw [Matrix.det_fin_two, hY10, hY11, hd']; field_simp; ring
  have had : Valued.v (a * d') = 1 := by
    have := hdet; rw [hdet', map_mul] at this
    have hv0 : Valued.v ϖ ≠ 0 := by rw [valued_pr]; exact WithZero.coe_ne_zero
    calc Valued.v (a * d') = (Valued.v ϖ)⁻¹ * (Valued.v ϖ * Valued.v (a * d')) := by
          rw [← mul_assoc, inv_mul_cancel₀ hv0, one_mul]
      _ = 1 := by rw [this, inv_mul_cancel₀ hv0]
  have hd'v : Valued.v d' = 1 := by rw [map_mul, h00, one_mul] at had; exact had
  have hd'0 : d' ≠ 0 := fun h0 => by rw [h0, map_zero] at hd'v; exact zero_ne_one hd'v
  have hd'i : d'⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v hd'v
  have haO : a ∈ 𝓞v := hY 0 0
  have hbO : b ∈ 𝓞v := hY 0 1
  have hx : ϖ * c * a⁻¹ ∈ 𝓞v := mul_mem (mul_mem (pr_mem_integers v) h10) hai
  have hnx : -(ϖ * c * a⁻¹) ∈ 𝓞v := neg_mem hx
  have hy : -(b * a⁻¹ * d'⁻¹) ∈ 𝓞v := neg_mem (mul_mem (mul_mem hbO hai) hd'i)
  refine ⟨!![1, 0; ϖ * c * a⁻¹, 1], !![1, 0; -(ϖ * c * a⁻¹), 1], !![a, b; 0, d'], !![a⁻¹, -(b * a⁻¹ * d'⁻¹); 0, d'⁻¹],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hx]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hnx]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hd'O, hbO, zero_mem, haO]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hai, hd'i, zero_mem, hy]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ϖ⁻¹ * (ϖ * c * a⁻¹) = c * a⁻¹ by field_simp]
    exact mul_mem h10 hai
  · simp [zero_mem]
  · ext i j : 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [tM, hY10, hY11, hd'] <;> (try field_simp) <;> ring

end Peirce

section IwahoriHecke

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def alM : M₂ := !![0, 1; ϖ, 0]
def alMi : M₂ := !![0, ϖ⁻¹; 1, 0]

theorem alM_mul_alMi : alM v * alMi v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, alM, alMi, mul_inv_cancel₀ hp0]
theorem alMi_mul_alM : alMi v * alM v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, alM, alMi, inv_mul_cancel₀ hp0]

theorem iwahori_iff {X : M₂} (hX : X ∈ intMat v) : tMi v * X * tM v ∈ intMat v ↔ ϖ⁻¹ * X 1 0 ∈ 𝓞v :=
  (tMi_mul_mul_tM_mem_iff v hX).trans (pr_inv_mul_mem_integers_iff v (hX 1 0)).symm

theorem valued_eq_one_or_pr_inv_mul_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x = 1 ∨ ϖ⁻¹ * x ∈ 𝓞v := by
  rcases (valued_le_one_of_mem v hx).lt_or_eq with h | h
  · exact Or.inr ((pr_inv_mul_mem_integers_iff v hx).2 h)
  · exact Or.inl h

theorem valued_diag_mul_lt_one {η : M₂} (hη : η ∈ intMat v) (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v)
    (hdet : Valued.v η.det = Valued.v ϖ) : Valued.v (η 0 0 * η 1 1) < 1 := by
  have hp0 := pr_ne_zero' v
  have e1 : η 0 0 * η 1 1 = η.det + η 0 1 * (ϖ * (ϖ⁻¹ * η 1 0)) := by
    rw [mul_inv_cancel_left₀ hp0, Matrix.det_fin_two]; ring
  rw [e1]
  refine lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt ?_ ?_)
  · rw [hdet, valued_pr, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)
  · rw [map_mul, map_mul, valued_pr]
    calc Valued.v (η 0 1) * (WithZero.exp (-1) * Valued.v (ϖ⁻¹ * η 1 0))
        ≤ 1 * (WithZero.exp (-1) * 1) :=
          mul_le_mul' (valued_le_one_of_mem v (hη 0 1)) (mul_le_mul_right (valued_le_one_of_mem v h10) _)
      _ < 1 := by rw [one_mul, mul_one, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)

theorem pr_inv_mul_apply_zero_zero_mem {η : M₂} (hη : η ∈ intMat v) (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v)
    (hdet : Valued.v η.det = Valued.v ϖ) (h11 : Valued.v (η 1 1) = 1) : ϖ⁻¹ * η 0 0 ∈ 𝓞v := by
  have h := valued_diag_mul_lt_one v hη h10 hdet
  rw [map_mul, h11, mul_one] at h
  exact (pr_inv_mul_mem_integers_iff v (hη 0 0)).2 h

theorem pr_inv_mul_apply_one_one_mem {η : M₂} (hη : η ∈ intMat v) (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v)
    (hdet : Valued.v η.det = Valued.v ϖ) (h00 : Valued.v (η 0 0) = 1) : ϖ⁻¹ * η 1 1 ∈ 𝓞v := by
  have h := valued_diag_mul_lt_one v hη h10 hdet
  rw [map_mul, h00, one_mul] at h
  exact (pr_inv_mul_mem_integers_iff v (hη 1 1)).2 h

theorem iwahori_mul_mul_mem {X Y Z : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v) (hZ : Z ∈ intMat v) (hZ' : tMi v * Z * tM v ∈ intMat v) :
    X * Y * Z ∈ intMat v ∧ tMi v * (X * Y * Z) * tM v ∈ intMat v := by
  refine ⟨(intMat v).mul_mem ((intMat v).mul_mem hX hY) hZ, ?_⟩
  have e : tMi v * (X * Y * Z) * tM v = (tMi v * X * tM v) * (tMi v * Y * tM v) * (tMi v * Z * tM v) := by
    calc tMi v * (X * Y * Z) * tM v = tMi v * X * (tM v * tMi v) * Y * (tM v * tMi v) * Z * tM v := by
          rw [tM_mul_tMi]; simp only [mul_one, Matrix.mul_assoc]
      _ = _ := by noncomm_ring
  rw [e]; exact (intMat v).mul_mem ((intMat v).mul_mem hX' hY') hZ'

theorem iwahori_inv_mem {κ κi : M₂} (h1 : κ * κi = 1) (h2 : κi * κ = 1) (hκ : κ ∈ intMat v)
    (hκ' : tMi v * κ * tM v ∈ intMat v) (hdet : Valued.v κ.det = 1) :
    κi ∈ intMat v ∧ tMi v * κi * tM v ∈ intMat v := by
  have hκiO : κi ∈ intMat v := inv_mem_intMat_of_valued_det v hκ h1 h2 hdet
  refine ⟨hκiO, (iwahori_iff v hκiO).2 ?_⟩
  rw [inv_apply_one_zero v h1 h2, mul_neg, ← mul_assoc, mul_comm ϖ⁻¹, mul_assoc]
  exact neg_mem (mul_mem (inv_mem_integers_of_valued_eq_one v hdet) ((iwahori_iff v hκ).1 hκ'))

theorem alMi_mul_mul_alM (X : M₂) : alMi v * X * alM v = !![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] := by
  have hp0 := pr_ne_zero' v
  ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [alM, alMi] <;> field_simp
theorem alM_mul_mul_alMi (X : M₂) : alM v * X * alMi v = !![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] := by
  have hp0 := pr_ne_zero' v
  ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [alM, alMi] <;> field_simp

theorem swap_mem_iwahori {X : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v) :
    (!![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] : M₂) ∈ intMat v ∧
      tMi v * (!![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] : M₂) * tM v ∈ intMat v := by
  have hp0 := pr_ne_zero' v
  have hX10 := (iwahori_iff v hX).1 hX'
  have hmem : (!![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] : M₂) ∈ intMat v := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [hX 1 1, hX10, hX 0 0, mul_mem (pr_mem_integers v) (hX 0 1)]
  refine ⟨hmem, (iwahori_iff v hmem).2 ?_⟩
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [inv_mul_cancel_left₀ hp0]; exact hX 0 1

theorem conj_mem_iwahori_of_normaliser_type {η ηi : M₂} (h1 : η * ηi = 1) (h2 : ηi * η = 1) (hη : η ∈ intMat v)
    (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v) (hdet : Valued.v η.det = Valued.v ϖ)
    (h00 : ϖ⁻¹ * η 0 0 ∈ 𝓞v) (h11 : ϖ⁻¹ * η 1 1 ∈ 𝓞v) {X : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v) :
    (ηi * X * η ∈ intMat v ∧ tMi v * (ηi * X * η) * tM v ∈ intMat v) ∧
      (η * X * ηi ∈ intMat v ∧ tMi v * (η * X * ηi) * tM v ∈ intMat v) := by
  have hp0 := pr_ne_zero' v
  set κ : M₂ := alMi v * η with hκ
  set κi : M₂ := ηi * alM v with hκi
  have hηκ : η = alM v * κ := by rw [hκ, ← mul_assoc, alM_mul_alMi, one_mul]
  have hηiκ : ηi = κi * alMi v := by rw [hκi, mul_assoc, alM_mul_alMi, mul_one]
  have hκκi : κ * κi = 1 := by
    rw [hκ, hκi, show alMi v * η * (ηi * alM v) = alMi v * (η * ηi) * alM v by noncomm_ring, h1, mul_one, alMi_mul_alM]
  have hκiκ : κi * κ = 1 := by
    rw [hκ, hκi, show ηi * alM v * (alMi v * η) = ηi * (alM v * alMi v) * η by noncomm_ring, alM_mul_alMi, mul_one, h2]
  have eκ : κ = !![ϖ⁻¹ * η 1 0, ϖ⁻¹ * η 1 1; η 0 0, η 0 1] := by
    rw [hκ]; ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [alMi]
  have hκO : κ ∈ intMat v := by
    rw [eκ]; intro i j; fin_cases i <;> fin_cases j <;> simp [h10, h11, hη 0 0, hη 0 1]
  have hκ10 : κ 1 0 = η 0 0 := by rw [eκ]; simp
  have hκ' : tMi v * κ * tM v ∈ intMat v := by rw [iwahori_iff v hκO, hκ10]; exact h00
  have hκdet : Valued.v κ.det = 1 := by
    have : κ.det = -(ϖ⁻¹ * η.det) := by
      rw [eκ, Matrix.det_fin_two, Matrix.det_fin_two]; simp; ring
    rw [this, Valuation.map_neg, map_mul, map_inv₀, hdet, inv_mul_cancel₀]
    rw [valued_pr]; exact WithZero.coe_ne_zero
  obtain ⟨hκiO, hκi'⟩ := iwahori_inv_mem v hκκi hκiκ hκO hκ' hκdet
  constructor
  · rw [hηκ, hηiκ]
    have e : κi * alMi v * X * (alM v * κ) = κi * (alMi v * X * alM v) * κ := by noncomm_ring
    rw [e, alMi_mul_mul_alM]
    obtain ⟨hw, hw'⟩ := swap_mem_iwahori v hX hX'
    exact iwahori_mul_mul_mem v hκiO hκi' hw hw' hκO hκ'
  · rw [hηκ, hηiκ]
    have e : alM v * κ * X * (κi * alMi v) = alM v * (κ * X * κi) * alMi v := by noncomm_ring
    rw [e, alM_mul_mul_alMi]
    obtain ⟨hw, hw'⟩ := iwahori_mul_mul_mem v hκO hκ' hX hX' hκiO hκi'
    exact swap_mem_iwahori v hw hw'

theorem conj_mem_intMat_of_tM_type {ι ιi ι' ι'i : M₂} (hι : ι ∈ intMat v) (hιi : ιi ∈ intMat v)
    (hι' : ι' ∈ intMat v) (hι'i : ι'i ∈ intMat v) (h1 : ι * ιi = 1) (h2 : ιi * ι = 1)
    (hιΓ : tMi v * ι * tM v ∈ intMat v) (hιdet : Valued.v ι.det = 1)
    {X : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v) :
    (ι'i * tMi v * ιi) * X * (ι * tM v * ι') ∈ intMat v := by
  obtain ⟨-, hιiΓ⟩ := iwahori_inv_mem v h1 h2 hι hιΓ hιdet
  have hin : ιi * X * ι ∈ intMat v ∧ tMi v * (ιi * X * ι) * tM v ∈ intMat v :=
    iwahori_mul_mul_mem v hιi hιiΓ hX hX' hι hιΓ
  have e : (ι'i * tMi v * ιi) * X * (ι * tM v * ι') = ι'i * (tMi v * (ιi * X * ι) * tM v) * ι' := by noncomm_ring
  rw [e]; exact (intMat v).mul_mem ((intMat v).mul_mem hι'i hin.2) hι'

theorem conj_mem_intMat_of_tbM_type {ι ιi ι' ι'i : M₂} (hι : ι ∈ intMat v) (hιi : ιi ∈ intMat v)
    (hι' : ι' ∈ intMat v) (hι'i : ι'i ∈ intMat v) (h1 : ι * ιi = 1) (h2 : ιi * ι = 1) (h1' : ι' * ι'i = 1)
    (h2' : ι'i * ι' = 1)
    (hιΓ : tMi v * ι * tM v ∈ intMat v) (hιdet : Valued.v ι.det = 1)
    (hι'Γ : tMi v * ι' * tM v ∈ intMat v) (hι'det : Valued.v ι'.det = 1)
    {X : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v) :
    tMi v * ((ι'i * tbMi v * ιi) * X * (ι * tbM v * ι')) * tM v ∈ intMat v := by
  have hp0 := pr_ne_zero' v
  obtain ⟨-, hιiΓ⟩ := iwahori_inv_mem v h1 h2 hι hιΓ hιdet
  obtain ⟨hι'iO, hι'iΓ⟩ := iwahori_inv_mem v h1' h2' hι' hι'Γ hι'det
  have hin := iwahori_mul_mul_mem v hιi hιiΓ hX hX' hι hιΓ
  have key : tbMi v * (ιi * X * ι) * tbM v = tM v * (ιi * X * ι) * tMi v := by
    rw [show tbM v = ϖ • tMi v from (smul_tMi v).symm]
    have : tbMi v = ϖ⁻¹ • tM v := by
      ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tbMi, tM, inv_mul_cancel₀ hp0]
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  have e : tMi v * ((ι'i * tbMi v * ιi) * X * (ι * tbM v * ι')) * tM v =
      (tMi v * ι'i * tM v) * (tMi v * (tbMi v * (ιi * X * ι) * tbM v) * tM v) * (tMi v * ι' * tM v) := by
    calc tMi v * ((ι'i * tbMi v * ιi) * X * (ι * tbM v * ι')) * tM v
        = tMi v * ι'i * (tM v * tMi v) * (tbMi v * (ιi * X * ι) * tbM v) * (tM v * tMi v) * ι' * tM v := by
          rw [tM_mul_tMi]; simp only [mul_one, Matrix.mul_assoc]
      _ = _ := by noncomm_ring
  rw [e, key, show tMi v * (tM v * (ιi * X * ι) * tMi v) * tM v = (tMi v * tM v) * (ιi * X * ι) * (tMi v * tM v) by
    noncomm_ring, tMi_mul_tM, one_mul, mul_one]
  exact (intMat v).mul_mem ((intMat v).mul_mem hι'iΓ hin.1) hι'Γ

end IwahoriHecke

section ULocal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

theorem tbM_mul_tbMi : tbM v * tbMi v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, tbM, tbMi, mul_inv_cancel₀ hp0]
theorem tbMi_mul_tbM : tbMi v * tbM v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, tbM, tbMi, inv_mul_cancel₀ hp0]

theorem diagonal_eq_tM : Matrix.diagonal ![(1 : 𝕂), ϖ ^ 1] = tM v := by
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [tM, Matrix.diagonal]

theorem one_mem_iwahori : (1 : M₂) ∈ intMat v ∧ tMi v * 1 * tM v ∈ intMat v := by
  refine ⟨(intMat v).one_mem, ?_⟩
  rw [mul_one, tMi_mul_tM]; exact (intMat v).one_mem

theorem iwahori_mul_mem {X Y : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v) :
    X * Y ∈ intMat v ∧ tMi v * (X * Y) * tM v ∈ intMat v := by
  have h := iwahori_mul_mul_mem v hX hX' hY hY' (one_mem_iwahori v).1 (one_mem_iwahori v).2
  simpa only [mul_one] using h

theorem valued_det_eq_valued_pr {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hpYi' : tMi v * (ϖ • Yi) * tM v ∈ intMat v)
    (hYi : ¬ (Yi ∈ intMat v ∧ tMi v * Yi * tM v ∈ intMat v))
    (hpY : ¬ (ϖ⁻¹ • Y ∈ intMat v ∧ tMi v * (ϖ⁻¹ • Y) * tM v ∈ intMat v)) :
    Valued.v Y.det = Valued.v ϖ := by
  have hp0 := pr_ne_zero' v
  obtain ⟨m, hm2, hm0, hm⟩ := valued_det_bounds v h1 hY hpYi
  have hvp : Valued.v ϖ = WithZero.exp (-1) := valued_pr v
  have hYidet : Valued.v Yi.det = (Valued.v Y.det)⁻¹ := by
    have h' : Valued.v Y.det * Valued.v Yi.det = 1 := by rw [← map_mul, det_mul_det_eq_one v h1, map_one]
    exact eq_inv_of_mul_eq_one_right h'
  obtain rfl | rfl | rfl : m = -2 ∨ m = -1 ∨ m = 0 := by omega
  · exfalso
    apply hpY
    have hZ1 : (ϖ • Yi) * (ϖ⁻¹ • Y) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hp0, one_smul, h2]
    have hZ2 : (ϖ⁻¹ • Y) * (ϖ • Yi) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul, h1]
    have hdetZ : Valued.v (ϖ • Yi).det = 1 := by
      rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, hvp, hYidet, hm, ← WithZero.exp_nsmul,
        ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero]
      congr 1
    exact iwahori_inv_mem v hZ1 hZ2 hpYi hpYi' hdetZ
  · rw [hm, hvp]
  · exfalso
    apply hYi
    have hdet1 : Valued.v Y.det = 1 := by rw [hm, WithZero.exp_zero]
    exact iwahori_inv_mem v h1 h2 hY hY' hdet1

theorem exists_tbM_type {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hpYi' : tMi v * (ϖ • Yi) * tM v ∈ intMat v)
    (hYi : ¬ (Yi ∈ intMat v ∧ tMi v * Yi * tM v ∈ intMat v))
    (hpY : ¬ (ϖ⁻¹ • Y ∈ intMat v ∧ tMi v * (ϖ⁻¹ • Y) * tM v ∈ intMat v))
    (hnn : ¬ ∀ X : M₂, X ∈ intMat v → tMi v * X * tM v ∈ intMat v →
        (Yi * X * Y ∈ intMat v ∧ tMi v * (Yi * X * Y) * tM v ∈ intMat v) ∧
        (Y * X * Yi ∈ intMat v ∧ tMi v * (Y * X * Yi) * tM v ∈ intMat v))
    (hnt : ¬ ∀ X : M₂, X ∈ intMat v → tMi v * X * tM v ∈ intMat v → Yi * X * Y ∈ intMat v) :
    ∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tbM v * ι' := by
  have hdet := valued_det_eq_valued_pr v h1 h2 hY hY' hpYi hpYi' hYi hpY
  have h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v := (iwahori_iff v hY).1 hY'
  rcases valued_eq_one_or_pr_inv_mul_mem v (hY 1 1) with h11 | h11
  · exact exists_iwahori_mul_tbM_mul v hY (pr_inv_mul_apply_zero_zero_mem v hY h10 hdet h11) h10 h11 hdet
  · exfalso
    rcases valued_eq_one_or_pr_inv_mul_mem v (hY 0 0) with h00 | h00
    · obtain ⟨ι, ιi, ι', ι'i, hι, hιi, hι', hι'i, e1, e2, e1', e2', hι10, hι'10, hYeq⟩ :=
        exists_iwahori_mul_tM_mul v hY h10 h11 h00 hdet
      apply hnt
      intro X hX hX'
      have hW : Y * (ι'i * tMi v * ιi) = 1 := by
        rw [hYeq]
        calc ι * tM v * ι' * (ι'i * tMi v * ιi) = ι * (tM v * (ι' * ι'i) * tMi v) * ιi := by noncomm_ring
          _ = 1 := by rw [e1', mul_one, tM_mul_tMi, mul_one, e1]
      have hYi_eq : Yi = ι'i * tMi v * ιi := by
        calc Yi = Yi * (Y * (ι'i * tMi v * ιi)) := by rw [hW, mul_one]
          _ = (Yi * Y) * (ι'i * tMi v * ιi) := (mul_assoc _ _ _).symm
          _ = ι'i * tMi v * ιi := by rw [h2, one_mul]
      rw [hYi_eq, hYeq]
      exact conj_mem_intMat_of_tM_type v hι hιi hι' hι'i e1 e2 ((iwahori_iff v hι).2 hι10)
        (valued_det_eq_one v hι hιi e1) hX hX'
    · apply hnn
      intro X hX hX'
      exact conj_mem_iwahori_of_normaliser_type v h1 h2 hY h10 hdet h00 h11 hX hX'

end ULocal

section Lib

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

theorem exists_eq_alM_mul {η ηi : M₂} (h1 : η * ηi = 1) (h2 : ηi * η = 1) (hη : η ∈ intMat v)
    (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v) (hdet : Valued.v η.det = Valued.v ϖ)
    (h00 : ϖ⁻¹ * η 0 0 ∈ 𝓞v) (h11 : ϖ⁻¹ * η 1 1 ∈ 𝓞v) :
    ∃ κ κi : M₂, κ ∈ intMat v ∧ κi ∈ intMat v ∧ κ * κi = 1 ∧ κi * κ = 1 ∧ ϖ⁻¹ * κ 1 0 ∈ 𝓞v ∧ η = alM v * κ := by
  have hp0 := pr_ne_zero' v
  set κ : M₂ := alMi v * η with hκ
  set κi : M₂ := ηi * alM v with hκi
  have hηκ : η = alM v * κ := by rw [hκ, ← mul_assoc, alM_mul_alMi, one_mul]
  have hκκi : κ * κi = 1 := by
    rw [hκ, hκi, show alMi v * η * (ηi * alM v) = alMi v * (η * ηi) * alM v by noncomm_ring, h1, mul_one, alMi_mul_alM]
  have hκiκ : κi * κ = 1 := by
    rw [hκ, hκi, show ηi * alM v * (alMi v * η) = ηi * (alM v * alMi v) * η by noncomm_ring, alM_mul_alMi, mul_one, h2]
  have eκ : κ = !![ϖ⁻¹ * η 1 0, ϖ⁻¹ * η 1 1; η 0 0, η 0 1] := by
    rw [hκ]; ext i j : 1; simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [alMi]
  have hκO : κ ∈ intMat v := by
    rw [eκ]; intro i j; fin_cases i <;> fin_cases j <;> simp [h10, h11, hη 0 0, hη 0 1]
  have hκ10 : κ 1 0 = η 0 0 := by rw [eκ]; simp
  have hκ' : tMi v * κ * tM v ∈ intMat v := by rw [iwahori_iff v hκO, hκ10]; exact h00
  have hκdet : Valued.v κ.det = 1 := by
    have : κ.det = -(ϖ⁻¹ * η.det) := by
      rw [eκ, Matrix.det_fin_two, Matrix.det_fin_two]; simp; ring
    rw [this, Valuation.map_neg, map_mul, map_inv₀, hdet, inv_mul_cancel₀]
    rw [valued_pr]; exact WithZero.coe_ne_zero
  obtain ⟨hκiO, -⟩ := iwahori_inv_mem v hκκi hκiκ hκO hκ' hκdet
  exact ⟨κ, κi, hκO, hκiO, hκκi, hκiκ, by rw [hκ10]; exact h00, hηκ⟩

theorem trichotomy {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hpYi' : tMi v * (ϖ • Yi) * tM v ∈ intMat v)
    (hYi : ¬ (Yi ∈ intMat v ∧ tMi v * Yi * tM v ∈ intMat v))
    (hpY : ¬ (ϖ⁻¹ • Y ∈ intMat v ∧ tMi v * (ϖ⁻¹ • Y) * tM v ∈ intMat v)) :
    Valued.v Y.det = Valued.v ϖ ∧
    ((∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tbM v * ι') ∨
     (∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tM v * ι') ∨
     (∃ κ κi : M₂, κ ∈ intMat v ∧ κi ∈ intMat v ∧ κ * κi = 1 ∧ κi * κ = 1 ∧ ϖ⁻¹ * κ 1 0 ∈ 𝓞v ∧ Y = alM v * κ)) := by
  have hdet := valued_det_eq_valued_pr v h1 h2 hY hY' hpYi hpYi' hYi hpY
  have h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v := (iwahori_iff v hY).1 hY'
  refine ⟨hdet, ?_⟩
  rcases valued_eq_one_or_pr_inv_mul_mem v (hY 1 1) with h11 | h11
  · exact Or.inl (exists_iwahori_mul_tbM_mul v hY (pr_inv_mul_apply_zero_zero_mem v hY h10 hdet h11) h10 h11 hdet)
  · rcases valued_eq_one_or_pr_inv_mul_mem v (hY 0 0) with h00 | h00
    · exact Or.inr (Or.inl (exists_iwahori_mul_tM_mul v hY h10 h11 h00 hdet))
    · exact Or.inr (Or.inr (exists_eq_alM_mul v h1 h2 hY h10 hdet h00 h11))

end Lib

section Card

theorem pr_eq_of_mem (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) : pr v = p :=
  (Nat.prime_dvd_prime_iff_eq (pr_prime v) hp).1 ((natCast_mem_asIdeal_iff_pr_dvd v p).1 hpv)

end Card

end LevelULocal
p2m_reactivate "P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.LevelULocal"

end
p2m_reactivate "P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.LevelULocal"

end LevelULocalBlock
p2m_reactivate "P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.LevelULocal"

open IsDedekindDomain NumberField

theorem solution
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ) (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ)) :
    Valued.v Y.det = Valued.v (p : v.adicCompletion ℚ) ∧
    ((∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![(p : v.adicCompletion ℚ), 0; 0, 1] * ι') ∨
     (∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![1, 0; 0, (p : v.adicCompletion ℚ)] * ι') ∨
     (∃ κ κi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, κ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, κi i j ∈ v.adicCompletionIntegers ℚ) ∧ κ * κi = 1 ∧ κi * κ = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * κ 1 0 ∈ v.adicCompletionIntegers ℚ ∧ Y = !![0, 1; (p : v.adicCompletion ℚ), 0] * κ)) := by
  have hpr := LevelULocal.pr_eq_of_mem p hp v hpv
  subst hpr
  have hYI : Y ∈ LevelULocal.intMat v := hY
  have hpYiI : ((LevelULocal.pr v : ℕ) : v.adicCompletion ℚ) • Yi ∈ LevelULocal.intMat v := hpYi
  have hY' := (LevelULocal.iwahori_iff v hYI).2 hY10
  have hpYi' := (LevelULocal.iwahori_iff v hpYiI).2 hpYi10
  have hYi2 : ¬ (Yi ∈ LevelULocal.intMat v ∧ LevelULocal.tMi v * Yi * LevelULocal.tM v ∈ LevelULocal.intMat v) :=
    fun H => hYi ⟨H.1, (LevelULocal.iwahori_iff v H.1).1 H.2⟩
  have hpY2 : ¬ (((LevelULocal.pr v : ℕ) : v.adicCompletion ℚ)⁻¹ • Y ∈ LevelULocal.intMat v ∧
      LevelULocal.tMi v * (((LevelULocal.pr v : ℕ) : v.adicCompletion ℚ)⁻¹ • Y) * LevelULocal.tM v ∈ LevelULocal.intMat v) :=
    fun H => hpY ⟨H.1, (LevelULocal.iwahori_iff v H.1).1 H.2⟩
  exact LevelULocal.trichotomy v h1 h2 hYI hY' hpYiI hpYi' hYi2 hpY2

end S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori
end P2MW
export P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori (solution)
