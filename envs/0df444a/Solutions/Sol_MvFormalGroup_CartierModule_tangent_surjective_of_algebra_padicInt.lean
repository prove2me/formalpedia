-- Prove2me | solution 1 for MvFormalGroup.CartierModule.tangent_surjective_of_algebra_padicInt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/10c1a0e0-0ec9-5528-b44b-25425dee135c

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse
import Theorems.Thm_MvFormalGroup_ArtinHasse_map_series_eq_map_exp_subst
import Theorems.Thm_MvFormalGroup_BigWittLaw_exists_hom_subst_curveFam_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

universe u

open PowerSeries MvFormalGroup MvFormalGroup.ArtinHasse

namespace CartierExistenceIntSol

variable (p : ℕ) [hp : Fact p.Prime]

def IsPPow (k : ℕ) : Prop := 0 < k ∧ ∀ q ∈ k.factorization.support, q = p

scoped instance (k : ℕ) : Decidable (IsPPow p k) := by unfold IsPPow; infer_instance

theorem isPPow_iff_exists {k : ℕ} : IsPPow p k ↔ ∃ m, k = p ^ m := by
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨k.factorization p, ?_⟩
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hk.ne']
    rw [Finsupp.prod]
    have hsub : k.factorization.support ⊆ {p} := fun q hq => Finset.mem_singleton.mpr (h q hq)
    rcases Finset.subset_singleton_iff.mp hsub with h' | h'
    · rw [h', Finset.prod_empty, Finsupp.notMem_support_iff.mp (h' ▸ Finset.notMem_empty p),
        pow_zero]
    · rw [h', Finset.prod_singleton]
  · rintro ⟨m, rfl⟩
    refine ⟨pow_pos hp.out.pos m, fun q hq => ?_⟩
    have h2 : p.factorization.support = {p} := by
      rw [hp.out.factorization]; simp
    simp only [Nat.factorization_pow] at hq
    have hq' := Finset.mem_of_subset Finsupp.support_smul hq
    rw [h2] at hq'; exact Finset.mem_singleton.mp hq'

theorem constantCoeff_subst_self' {R : Type*} [CommRing R] {g : R⟦X⟧}
    (hg : constantCoeff g = 0) (f : R⟦X⟧) :
    constantCoeff (f.subst g) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply,
    coeff_subst' (HasSubst.of_constantCoeff_zero' hg), finsum_eq_single _ 0]
  · simp
  · intro n hn
    rw [show coeff 0 (g ^ n) = 0 from by
          rw [coeff_zero_eq_constantCoeff, map_pow, hg, zero_pow hn],
      smul_zero]

section Glue

variable {A : Type*} [CommRing A] [Algebra ℚ A]

scoped instance instIsAddTorsionFreeOfAlgebraRat : IsAddTorsionFree A :=
  IsAddTorsionFree.of_module_rat A

theorem constantCoeff_subst_self {g : A⟦X⟧} (hg : constantCoeff g = 0)
    (f : A⟦X⟧) : constantCoeff (f.subst g) = constantCoeff f :=
  constantCoeff_subst_self' hg f

theorem one_add_X_mul_deriv_log : (1 + X : A⟦X⟧) * d⁄dX A (log A) = 1 := by
  rw [deriv_log]
  ext n
  rcases n with _ | n
  · simp [coeff_zero_eq_constantCoeff]
  · rw [add_mul, one_mul, map_add, coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one,
      if_neg (Nat.succ_ne_zero _), ← RingHom.map_add,
      show ((-1 : ℚ) ^ (n + 1) + (-1) ^ n : ℚ) = 0 from by ring]
    exact RingHom.map_zero _

theorem mul_derivative_logOf {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    f * d⁄dX A (logOf f) = d⁄dX A f := by
  have hsub : HasSubst (f - 1 : A⟦X⟧) :=
    HasSubst.of_constantCoeff_zero' (by simp [hf])
  rw [logOf_eq, derivative_subst (R := A) hsub, ← mul_assoc,
    show d⁄dX A (f - 1) = d⁄dX A f from by rw [map_sub]; simp]
  nth_rw 2 [← one_mul (d⁄dX A f)]
  congr 1
  have sub1 : subst (f - 1) (1 : A⟦X⟧) = 1 := by
    rw [← coe_substAlgHom hsub]; exact map_one _
  have step : subst (f - 1) ((1 + X : A⟦X⟧) * d⁄dX A (log A))
      = subst (f - 1) (1 + X : A⟦X⟧) * subst (f - 1) (d⁄dX A (log A)) :=
    subst_mul hsub (1 + X : A⟦X⟧) (d⁄dX A (log A))
  rw [one_add_X_mul_deriv_log, sub1, subst_add hsub, subst_X hsub, sub1,
    show (1 : A⟦X⟧) + (f - 1) = f from by ring] at step
  exact step.symm

theorem logOf_one : logOf (1 : A⟦X⟧) = 0 := by
  refine derivative.ext ?_ (by simp [constantCoeff_logOf (f := (1 : A⟦X⟧)) (by simp)])
  have h := mul_derivative_logOf (A := A) (f := 1) (by simp)
  simpa using h

theorem isUnit_of_constantCoeff_one {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    IsUnit f := by
  rw [PowerSeries.isUnit_iff_constantCoeff, hf]; exact isUnit_one

theorem cancel_unit_left {u a b : A⟦X⟧} (hu : IsUnit u) (h : u * a = u * b) :
    a = b := by
  obtain ⟨v, rfl⟩ := hu
  have := congr_arg (fun x => (↑v⁻¹ : A⟦X⟧) * x) h
  simpa [← mul_assoc] using this

theorem logOf_mul_of_constantCoeff_one {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  have hfg : constantCoeff (f * g) = 1 := by simp [hf, hg]
  refine derivative.ext ?_ ?_
  · refine cancel_unit_left (isUnit_of_constantCoeff_one hfg) ?_
    have leib : d⁄dX A (f * g) = f * d⁄dX A g + g * d⁄dX A f := by
      have := (d⁄dX A).leibniz f g
      simp only [smul_eq_mul] at this; exact this
    rw [mul_derivative_logOf hfg, map_add, mul_add,
      show f * g * d⁄dX A (logOf f) = g * (f * d⁄dX A (logOf f)) from by ring,
      show f * g * d⁄dX A (logOf g) = f * (g * d⁄dX A (logOf g)) from by ring,
      mul_derivative_logOf hf, mul_derivative_logOf hg, leib]
    ring
  · rw [map_add, constantCoeff_logOf hfg, constantCoeff_logOf hf, constantCoeff_logOf hg,
      add_zero]

theorem logOf_prod_of_constantCoeff_one {ι : Type*} (s : Finset ι) (f : ι → A⟦X⟧)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 1) :
    logOf (∏ i ∈ s, f i) = ∑ i ∈ s, logOf (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logOf_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      logOf_mul_of_constantCoeff_one (hf a (Finset.mem_insert_self a s))
        (by rw [map_prod]; exact Finset.prod_eq_one fun i hi =>
              hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem logOf_subst {f g : A⟦X⟧} (hf : constantCoeff f = 1)
    (hg : constantCoeff g = 0) :
    logOf (f.subst g) = (logOf f).subst g := by
  have hgs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have hfg : constantCoeff (f.subst g) = 1 := by
    rw [constantCoeff_subst_self hg, hf]
  refine derivative.ext ?_ ?_
  · refine cancel_unit_left (isUnit_of_constantCoeff_one hfg) ?_
    rw [mul_derivative_logOf hfg, derivative_subst (R := A) hgs, derivative_subst (R := A) hgs,
      ← mul_assoc, ← subst_mul hgs, mul_derivative_logOf hf]
  · rw [constantCoeff_logOf hfg, constantCoeff_subst_self hg, constantCoeff_logOf hf]

theorem logOf_exp_subst {g : A⟦X⟧} (hg : constantCoeff g = 0) :
    logOf ((exp A).subst g) = g := by
  have hgs : HasSubst g := HasSubst.of_constantCoeff_zero' hg
  have heg : constantCoeff ((exp A).subst g) = 1 := by
    rw [constantCoeff_subst_self hg, constantCoeff_exp]
  refine derivative.ext ?_ ?_
  · refine cancel_unit_left (isUnit_of_constantCoeff_one heg) ?_
    rw [mul_derivative_logOf heg, derivative_subst (R := A) hgs, derivative_exp]
  · rw [constantCoeff_logOf heg, hg]

theorem coeff_eq_of_forall_coeff_logOf_eq {f g : A⟦X⟧}
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) (k : ℕ)
    (h : ∀ j ≤ k, coeff j (logOf f) = coeff j (logOf g)) :
    coeff k f = coeff k g := by

  suffices H : ∀ j ≤ k, coeff j f = coeff j g from H k le_rfl
  induction k with
  | zero =>
    intro j hj
    interval_cases j
    simp [coeff_zero_eq_constantCoeff, hf, hg]
  | succ n ih =>
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with hj' | rfl
    · exact ih (fun m hm => h m (hm.trans (Nat.le_succ _))) j (Nat.lt_succ_iff.mp hj')

    have Hf := congr_arg (coeff n) (mul_derivative_logOf hf)
    have Hg := congr_arg (coeff n) (mul_derivative_logOf hg)
    rw [coeff_derivative, coeff_mul] at Hf Hg
    have sums_eq : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, coeff ij.1 f * coeff ij.2 (d⁄dX A (logOf f))
        = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, coeff ij.1 g * coeff ij.2 (d⁄dX A (logOf g)) := by
      refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
      have hij' := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hi : i ≤ n := by omega
      have hj1 : j + 1 ≤ n + 1 := by omega
      rw [ih (fun m hm => h m (hm.trans (Nat.le_succ _))) i hi,
        coeff_derivative, coeff_derivative, h (j + 1) hj1]
    have key : coeff (n + 1) f * (↑n + 1) = coeff (n + 1) g * (↑n + 1) :=
      Hf.symm.trans (sums_eq.trans Hg)
    rw [show ((n : A) + 1) = ((n + 1 : ℕ) : A) from by push_cast; ring,
      mul_comm, mul_comm (coeff (n + 1) g), ← nsmul_eq_mul, ← nsmul_eq_mul] at key
    exact (smul_right_inj (Nat.succ_ne_zero n)).mp key

end Glue

theorem trunc_prod_eq_one {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧)
    (k : ℕ) (hf : ∀ i ∈ s, trunc (k + 1) (f i) = 1) :
    trunc (k + 1) (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← trunc_trunc_mul, hf a (Finset.mem_insert_self _ _),
      Polynomial.coe_one, one_mul, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem ps_map_subst {R S : Type*} [CommRing R] [CommRing S] {a : R⟦X⟧}
    (ha : HasSubst a) (h : R →+* S) (f : R⟦X⟧) :
    PowerSeries.map h (f.subst a) = (PowerSeries.map h f).subst (PowerSeries.map h a) :=
  map_subst ha f

section OverQp

variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A]

theorem hasSubst_C_mul_X_pow (z : A) {q : ℕ} (hq : q ≠ 0) :
    HasSubst (C z * X ^ q : A⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (by simp [hq])

theorem constantCoeff_C_mul_X_pow (z : A) {q : ℕ} (hq : q ≠ 0) :
    constantCoeff (C z * X ^ q : A⟦X⟧) = 0 := by simp [hq]

theorem coeff_C_mul_X_pow_pow (z : A) (q d k : ℕ) :
    coeff k ((C z * X ^ q : A⟦X⟧) ^ d) = if k = q * d then z ^ d else 0 := by
  rw [mul_pow, ← map_pow, ← pow_mul, coeff_C_mul_X_pow]

theorem scaled_eq_subst (z : A) {q : ℕ} (hq : q ≠ 0) :
    scaled p q z = (PowerSeries.map (algebraMap ℤ_[p] A) (series p)).subst (C z * X ^ q) := by
  ext k
  rw [coeff_scaled, coeff_subst' (hasSubst_C_mul_X_pow z hq)]
  simp only [coeff_C_mul_X_pow_pow, coeff_map, smul_eq_mul, mul_ite, mul_zero]
  by_cases hdvd : q ∣ k
  · rw [if_pos hdvd, finsum_eq_single _ (k / q)]
    · rw [if_pos (Nat.mul_div_cancel' hdvd).symm]
    · intro d hd
      rw [if_neg]
      intro hk
      apply hd
      rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hq)]
  · rw [if_neg hdvd, finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro hk
    exact hdvd ⟨d, hk⟩

variable [Algebra ℚ_[p] A] [IsScalarTower ℤ_[p] ℚ_[p] A] [Algebra ℚ A]

def arg (A : Type*) [CommRing A] [Algebra ℚ A] : A⟦X⟧ :=
  PowerSeries.mk fun k => if IsPPow p k then algebraMap ℚ A (k : ℚ)⁻¹ else 0

omit [Algebra ℤ_[p] A] [Algebra ℚ_[p] A] [IsScalarTower ℤ_[p] ℚ_[p] A] in
theorem coeff_arg (k : ℕ) :
    coeff k (arg p A) = if IsPPow p k then algebraMap ℚ A (k : ℚ)⁻¹ else 0 :=
  coeff_mk _ _

omit [Algebra ℤ_[p] A] [Algebra ℚ_[p] A] [IsScalarTower ℤ_[p] ℚ_[p] A] in
theorem constantCoeff_arg : constantCoeff (arg p A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_arg, if_neg]
  rintro ⟨h, -⟩
  exact lt_irrefl 0 h

omit [Algebra ℤ_[p] A] [Algebra ℚ_[p] A] [IsScalarTower ℤ_[p] ℚ_[p] A] in
theorem hasSubst_arg : HasSubst (arg p A) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_arg p)

theorem map_series_eq_exp_subst :
    PowerSeries.map (algebraMap ℤ_[p] A) (series p) = (exp A).subst (arg p A) := by
  classical
  have h1 : PowerSeries.map (algebraMap ℤ_[p] A) (series p) =
      PowerSeries.map (algebraMap ℚ_[p] A) (PowerSeries.map (algebraMap ℤ_[p] ℚ_[p]) (series p)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] A, PowerSeries.map_comp]
    rfl
  have h2 : (PowerSeries.map (algebraMap ℚ_[p] A)).comp (PowerSeries.map (algebraMap ℚ ℚ_[p])) =
      PowerSeries.map (algebraMap ℚ A) := by
    rw [← PowerSeries.map_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [h1, MvFormalGroup.ArtinHasse.map_series_eq_map_exp_subst p]
  change ((PowerSeries.map (algebraMap ℚ_[p] A)).comp (PowerSeries.map (algebraMap ℚ ℚ_[p]))) _ = _
  have harg0 : constantCoeff (PowerSeries.mk fun k : ℕ => if ∃ m : ℕ, k = p ^ m then (k : ℚ)⁻¹ else 0) = 0 := by
    rw [PowerSeries.constantCoeff_mk, if_neg]
    rintro ⟨m, hm⟩
    exact absurd hm.symm (pow_ne_zero m hp.out.ne_zero)
  rw [h2, ps_map_subst (HasSubst.of_constantCoeff_zero' harg0), map_exp]
  congr 1
  ext k
  simp only [coeff_map, coeff_mk, arg, isPPow_iff_exists]
  split_ifs <;> simp

theorem logOf_scaled (z : A) {q : ℕ} (hq : q ≠ 0) :
    logOf (scaled p q z) = (arg p A).subst (C z * X ^ q) := by
  rw [scaled_eq_subst p z hq, map_series_eq_exp_subst p,
    subst_comp_subst_apply (hasSubst_arg p) (hasSubst_C_mul_X_pow z hq)]
  exact logOf_exp_subst (by rw [constantCoeff_subst_self' (constantCoeff_C_mul_X_pow z hq), constantCoeff_arg])

omit [Algebra ℤ_[p] A] [Algebra ℚ_[p] A] [IsScalarTower ℤ_[p] ℚ_[p] A] in

theorem coeff_arg_subst (z : A) {q : ℕ} (hq : q ≠ 0) (j : ℕ) :
    coeff j ((arg p A).subst (C z * X ^ q)) =
      if q ∣ j then coeff (j / q) (arg p A) * z ^ (j / q) else 0 := by
  rw [coeff_subst' (hasSubst_C_mul_X_pow z hq)]
  simp only [coeff_C_mul_X_pow_pow, smul_eq_mul, mul_ite, mul_zero]
  by_cases hdvd : q ∣ j
  · rw [if_pos hdvd, finsum_eq_single _ (j / q)]
    · rw [if_pos (Nat.mul_div_cancel' hdvd).symm]
    · intro d hd
      rw [if_neg]
      intro hk
      apply hd
      rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hq)]
  · rw [if_neg hdvd, finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro hk
    exact hdvd ⟨d, hk⟩

theorem coeff_logOf_prodSeries (z : ℕ → A) (N j : ℕ) :
    coeff j (logOf (prodSeries p z N)) =
      ∑ m ∈ Finset.range N,
        if p ^ m ∣ j then coeff (j / p ^ m) (arg p A) * z m ^ (j / p ^ m) else 0 := by
  rw [prodSeries, logOf_prod_of_constantCoeff_one _ _ (fun m _ => constantCoeff_scaled p _ _), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [logOf_scaled p (z m) (pow_ne_zero m hp.out.ne_zero), coeff_arg_subst p (z m) (pow_ne_zero m hp.out.ne_zero)]

theorem coeff_pow_logOf_prodSeries (z : ℕ → A) {N i : ℕ} (hi : i < N) :
    coeff (p ^ i) (logOf (prodSeries p z N)) =
      algebraMap ℚ A ((p : ℚ) ^ i)⁻¹ * ∑ m ∈ Finset.range (i + 1), (p : A) ^ m * z m ^ p ^ (i - m) := by
  rw [coeff_logOf_prodSeries, Finset.mul_sum]
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hi)]
  have htail : ∑ m ∈ Finset.Ico (i + 1) N,
      (if p ^ m ∣ p ^ i then coeff (p ^ i / p ^ m) (arg p A) * z m ^ (p ^ i / p ^ m) else 0) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' : i < m := (Finset.mem_Ico.mp hm).1
    rw [if_neg]
    intro hdvd
    have := Nat.pow_dvd_pow_iff_le_right hp.out.one_lt |>.mp hdvd
    omega
  rw [htail, add_zero]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hdvd : p ^ m ∣ p ^ i := pow_dvd_pow p hm'
  have hdiv : p ^ i / p ^ m = p ^ (i - m) := Nat.pow_div hm' hp.out.pos
  rw [if_pos hdvd, hdiv, coeff_arg, if_pos ((isPPow_iff_exists p).mpr ⟨i - m, rfl⟩)]
  push_cast
  rw [← mul_assoc]
  congr 1
  rw [show ((p : A) ^ m) = algebraMap ℚ A ((p : ℚ) ^ m) by simp, ← map_mul]
  congr 1
  rw [pow_sub₀ _ (Nat.cast_ne_zero.mpr hp.out.ne_zero) hm']
  field_simp

theorem coeff_logOf_prodSeries_eq_zero (z : ℕ → A) (N : ℕ) {j : ℕ} (hj : ¬ IsPPow p j) :
    coeff j (logOf (prodSeries p z N)) = 0 := by
  rw [coeff_logOf_prodSeries]
  refine Finset.sum_eq_zero fun m _ => ?_
  split_ifs with hdvd
  · rw [coeff_arg, if_neg, zero_mul]
    intro hpp
    apply hj
    obtain ⟨r, hr⟩ := (isPPow_iff_exists p).mp hpp
    refine (isPPow_iff_exists p).mpr ⟨m + r, ?_⟩
    rw [pow_add, ← hr, Nat.mul_div_cancel' hdvd]
  · rfl

end OverQp

section Core

def SQ (m : ℕ) : MvPolynomial (Fin 2 × ℕ) ℚ_[p] :=
  MvPolynomial.aeval (MvPolynomial.X : Fin 2 × ℕ → MvPolynomial (Fin 2 × ℕ) ℚ_[p]) (WittVector.wittAdd p m)

theorem sum_SQ_pow (i : ℕ) :
    ∑ m ∈ Finset.range (i + 1), (p : MvPolynomial (Fin 2 × ℕ) ℚ_[p]) ^ m * SQ p m ^ p ^ (i - m) =
      ∑ m ∈ Finset.range (i + 1), (p : MvPolynomial (Fin 2 × ℕ) ℚ_[p]) ^ m *
          (MvPolynomial.X (0, m) : MvPolynomial (Fin 2 × ℕ) ℚ_[p]) ^ p ^ (i - m) +
        ∑ m ∈ Finset.range (i + 1), (p : MvPolynomial (Fin 2 × ℕ) ℚ_[p]) ^ m *
          (MvPolynomial.X (1, m) : MvPolynomial (Fin 2 × ℕ) ℚ_[p]) ^ p ^ (i - m) := by
  have key := wittStructureInt_prop p (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) i
  rw [map_add, MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_X_right] at key
  have h := congrArg (MvPolynomial.aeval
    (MvPolynomial.X : Fin 2 × ℕ → MvPolynomial (Fin 2 × ℕ) ℚ_[p])) key
  rw [MvPolynomial.aeval_bind₁, map_add, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename,
    aeval_wittPolynomial, aeval_wittPolynomial, aeval_wittPolynomial] at h
  exact h

theorem coeff_prodSeries_SQ_eq (n : ℕ) {k : ℕ} (hk : k < p ^ (n + 1)) :
    coeff k (prodSeries p (SQ p) (n + 1)) =
      coeff k (prodSeries p (fun m => (MvPolynomial.X (0, m) : MvPolynomial (Fin 2 × ℕ) ℚ_[p])) (n + 1) *
        prodSeries p (fun m => (MvPolynomial.X (1, m) : MvPolynomial (Fin 2 × ℕ) ℚ_[p])) (n + 1)) := by
  have h0 := constantCoeff_prodSeries p (fun m => (MvPolynomial.X (0, m) : MvPolynomial (Fin 2 × ℕ) ℚ_[p])) (n + 1)
  have h1 := constantCoeff_prodSeries p (fun m => (MvPolynomial.X (1, m) : MvPolynomial (Fin 2 × ℕ) ℚ_[p])) (n + 1)
  refine coeff_eq_of_forall_coeff_logOf_eq (constantCoeff_prodSeries p _ _) (by rw [map_mul, h0, h1, mul_one]) k
    fun j hj => ?_
  rw [logOf_mul_of_constantCoeff_one h0 h1, map_add]
  by_cases hpp : IsPPow p j
  · obtain ⟨i, rfl⟩ := (isPPow_iff_exists p).mp hpp
    have hi : i < n + 1 := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp (lt_of_le_of_lt hj hk)
    rw [coeff_pow_logOf_prodSeries p _ hi, coeff_pow_logOf_prodSeries p _ hi,
      coeff_pow_logOf_prodSeries p _ hi, sum_SQ_pow, mul_add]
  · rw [coeff_logOf_prodSeries_eq_zero p _ _ hpp, coeff_logOf_prodSeries_eq_zero p _ _ hpp,
      coeff_logOf_prodSeries_eq_zero p _ _ hpp, add_zero]

end Core

section Descent

def SO (m : ℕ) : MvPolynomial (Fin 2 × ℕ) ℤ_[p] :=
  MvPolynomial.map (Int.castRingHom ℤ_[p]) (WittVector.wittAdd p m)

def incl : MvPolynomial (Fin 2 × ℕ) ℤ_[p] →ₐ[ℤ_[p]] MvPolynomial (Fin 2 × ℕ) ℚ_[p] :=
  MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p])

theorem incl_apply (P : MvPolynomial (Fin 2 × ℕ) ℤ_[p]) :
    incl p P = MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) P := by
  rw [incl, MvPolynomial.mapAlgHom_apply]
  rfl

theorem incl_injective : Function.Injective (incl p) := by
  intro P Q h
  rw [incl_apply, incl_apply] at h
  exact MvPolynomial.map_injective _ (IsFractionRing.injective ℤ_[p] ℚ_[p]) h

theorem aeval_X_eq_map {σ : Type*} (S : Type*) [CommRing S] (φ : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S) φ =
      MvPolynomial.map (Int.castRingHom S) φ := by
  refine RingHom.congr_fun (?_ :
    (MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom =
      MvPolynomial.map (Int.castRingHom S)) φ
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · exact RingHom.congr_fun (RingHom.ext_int
      ((MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom.comp
        (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))
      ((MvPolynomial.map (Int.castRingHom S)).comp (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))) r
  · simp

theorem incl_SO (m : ℕ) : incl p (SO p m) = SQ p m := by
  rw [incl_apply, SO, SQ, MvPolynomial.map_map,
    show (algebraMap ℤ_[p] ℚ_[p]).comp (Int.castRingHom ℤ_[p]) = Int.castRingHom ℚ_[p] from
      RingHom.ext_int _ _, aeval_X_eq_map]

theorem incl_X (bm : Fin 2 × ℕ) : incl p (MvPolynomial.X bm) = MvPolynomial.X bm := by
  rw [incl_apply, MvPolynomial.map_X]

theorem coeff_prodSeries_SO_eq (n : ℕ) {k : ℕ} (hk : k < p ^ (n + 1)) :
    coeff k (prodSeries p (SO p) (n + 1)) =
      coeff k (prodSeries p (fun m => (MvPolynomial.X (0, m) : MvPolynomial (Fin 2 × ℕ) ℤ_[p])) (n + 1) *
        prodSeries p (fun m => (MvPolynomial.X (1, m) : MvPolynomial (Fin 2 × ℕ) ℤ_[p])) (n + 1)) := by
  apply incl_injective p
  change ((incl p : MvPolynomial (Fin 2 × ℕ) ℤ_[p] →+* MvPolynomial (Fin 2 × ℕ) ℚ_[p]) (coeff k _)) =
    ((incl p : MvPolynomial (Fin 2 × ℕ) ℤ_[p] →+* MvPolynomial (Fin 2 × ℕ) ℚ_[p]) (coeff k _))
  rw [← coeff_map, ← coeff_map, map_mul, map_prodSeries, map_prodSeries, map_prodSeries]
  simp only [RingHom.coe_coe, incl_SO, incl_X]
  exact coeff_prodSeries_SQ_eq p n hk

theorem trunc_scaled_eq_one {A : Type*} [CommRing A] [Algebra ℤ_[p] A] (z : A) {k m : ℕ}
    (hk : k < p ^ m) : trunc (k + 1) (scaled p (p ^ m) z) = 1 := by
  ext j
  rw [coeff_trunc, Polynomial.coeff_one]
  by_cases hj : j < k + 1
  · rw [if_pos hj, coeff_scaled]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [if_pos (dvd_zero _), Nat.zero_div, coeff_zero_eq_constantCoeff_apply, constantCoeff_series,
        map_one, pow_zero, mul_one, if_pos rfl]
    · rw [if_neg, if_neg hj0.ne']
      intro hdvd
      have := Nat.le_of_dvd hj0 hdvd
      omega
  · rw [if_neg hj, if_neg (by omega)]

theorem coeff_prodSeries_of_le {A : Type*} [CommRing A] [Algebra ℤ_[p] A] (z : ℕ → A) {N N' k : ℕ}
    (hN : N ≤ N') (hk : k < p ^ N) :
    coeff k (prodSeries p z N') = coeff k (prodSeries p z N) := by
  classical
  rw [prodSeries, prodSeries, ← Finset.prod_range_mul_prod_Ico _ hN]
  have htr : trunc (k + 1) (∏ m ∈ Finset.Ico N N', scaled p (p ^ m) (z m)) = 1 :=
    trunc_prod_eq_one _ _ k fun m hm => trunc_scaled_eq_one p (z m)
      (lt_of_lt_of_le hk (Nat.pow_le_pow_right hp.out.pos (Finset.mem_Ico.mp hm).1))
  rw [← coeff_coe_trunc_of_lt (Nat.lt_succ_self k), ← trunc_mul_trunc, htr, Polynomial.coe_one,
    mul_one, coeff_coe_trunc_of_lt (Nat.lt_succ_self k)]

def blkCoord (b : Fin 2) (m : ℕ) : MvPolynomial (Fin 2 × ℕ) ℤ_[p] :=
  MvPolynomial.bind₁ (fun m' => (MvPolynomial.X (b, m') : MvPolynomial (Fin 2 × ℕ) ℤ_[p])) (coord p m)

theorem blkCoord_eq_coeff (b : Fin 2) {m n : ℕ} (hmn : m ≤ n) :
    blkCoord p b m =
      coeff (m + 1) (prodSeries p (fun m' => (MvPolynomial.X (b, m') : MvPolynomial (Fin 2 × ℕ) ℤ_[p])) (n + 1)) := by
  rw [blkCoord, show MvPolynomial.bind₁ (fun m' => (MvPolynomial.X (b, m') : MvPolynomial (Fin 2 × ℕ) ℤ_[p]))
      (coord p m) = MvPolynomial.aeval (fun m' => (MvPolynomial.X (b, m') : MvPolynomial (Fin 2 × ℕ) ℤ_[p]))
      (coord p m) from rfl, aeval_coord]
  exact (coeff_prodSeries_of_le p _ (Nat.succ_le_succ hmn) (Nat.lt_pow_self hp.out.one_lt)).symm

theorem bind₁_SO_coord (n : ℕ) :
    MvPolynomial.bind₁ (SO p) (coord p n) =
      blkCoord p 0 n + blkCoord p 1 n +
        ∑ i ∈ Finset.range n, blkCoord p 0 i * blkCoord p 1 (n - 1 - i) := by
  have hF := constantCoeff_prodSeries p (fun m' => (MvPolynomial.X ((0 : Fin 2), m') : MvPolynomial (Fin 2 × ℕ) ℤ_[p])) (n + 1)
  have hG := constantCoeff_prodSeries p (fun m' => (MvPolynomial.X ((1 : Fin 2), m') : MvPolynomial (Fin 2 × ℕ) ℤ_[p])) (n + 1)
  rw [show MvPolynomial.bind₁ (SO p) (coord p n) = MvPolynomial.aeval (SO p) (coord p n) from rfl,
    aeval_coord, coeff_prodSeries_SO_eq p n (Nat.lt_pow_self hp.out.one_lt),
    BigWittLaw.coeff_succ_mul hF hG, blkCoord_eq_coeff p 0 le_rfl, blkCoord_eq_coeff p 1 le_rfl]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  rw [blkCoord_eq_coeff p 0 (le_of_lt hi'), blkCoord_eq_coeff p 1 (show n - 1 - i ≤ n by omega)]

end Descent

section IntBase

theorem aeval_coe_eq_coe_bind₁ {σ τ : Type*} {S : Type*} [CommRing S] (g : σ → MvPolynomial τ S)
    (P : MvPolynomial σ S) :
    MvPolynomial.aeval (fun i => (g i : MvPowerSeries τ S)) P =
      ((MvPolynomial.bind₁ g P : MvPolynomial τ S) : MvPowerSeries τ S) := by
  let ψ₁ : MvPolynomial σ S →+* MvPowerSeries τ S :=
    (MvPolynomial.aeval fun i => (g i : MvPowerSeries τ S)).toRingHom
  let ψ₂ : MvPolynomial σ S →+* MvPowerSeries τ S :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := S)).comp (MvPolynomial.bind₁ g).toRingHom
  suffices h : ψ₁ = ψ₂ from RingHom.congr_fun h P
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · change MvPolynomial.aeval (fun i => (g i : MvPowerSeries τ S)) (MvPolynomial.C r) =
      ((MvPolynomial.bind₁ g (MvPolynomial.C r) : MvPolynomial τ S) : MvPowerSeries τ S)
    rw [MvPolynomial.aeval_C, MvPolynomial.bind₁_C_right, MvPolynomial.coe_C, MvPowerSeries.algebraMap_apply]
    simp
  · simp [ψ₁, ψ₂]

variable (R : Type u) [CommRing R] [Algebra ℤ_[p] R]

def famInt (n : ℕ) : MvPowerSeries ℕ R :=
  ↑(MvPolynomial.map (algebraMap ℤ_[p] R) (coord p n))

theorem coeff_famInt (n : ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (famInt p R n) = algebraMap ℤ_[p] R (MvPolynomial.coeff e (coord p n)) := by
  rw [famInt, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

theorem weight_eq_of_coeff_famInt_ne_zero {n : ℕ} {e : ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff e (famInt p R n) ≠ 0) :
    Finsupp.weight (fun i : ℕ => p ^ i) e = n + 1 := by
  rw [coeff_famInt] at h
  have h' : MvPolynomial.coeff e (coord p n) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_coord p n h'

theorem constantCoeff_famInt (n : ℕ) : MvPowerSeries.constantCoeff (famInt p R n) = 0 := by
  by_contra h
  have h' : MvPowerSeries.coeff (0 : ℕ →₀ ℕ) (famInt p R n) ≠ 0 := by
    rwa [MvPowerSeries.coeff_zero_eq_constantCoeff]
  have hw := weight_eq_of_coeff_famInt_ne_zero p R h'
  simp at hw

theorem hasSubst_famInt : MvPowerSeries.HasSubst (famInt p R) := by
  refine ⟨fun n => by rw [constantCoeff_famInt]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun i : ℕ => p ^ i) e)).subset ?_
  intro n hn
  have hw := weight_eq_of_coeff_famInt_ne_zero p R hn
  show n < Finsupp.weight (fun i : ℕ => p ^ i) e
  omega

theorem famInt_zero : famInt p R 0 = MvPowerSeries.X 0 := by
  rw [famInt, coord_zero, MvPolynomial.map_X, MvPolynomial.coe_X]

theorem coeff_single_zero_famInt (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 1) (famInt p R n) = if n = 0 then 1 else 0 := by
  classical
  split_ifs with hn
  · subst hn
    rw [famInt_zero, MvPowerSeries.coeff_X, if_pos rfl]
  · by_contra h
    have hw := weight_eq_of_coeff_famInt_ne_zero p R (Ne.symm h ∘ Eq.symm)
    rw [Finsupp.weight_single, pow_zero, smul_eq_mul, mul_one] at hw
    exact hn (by omega)

theorem addFam_eq_coe_map_SO (m : ℕ) :
    WittLaw.addFam p R m =
      ((MvPolynomial.map (algebraMap ℤ_[p] R) (SO p m) : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
  rw [WittLaw.addFam, SO, MvPolynomial.map_map,
    show (algebraMap ℤ_[p] R).comp (Int.castRingHom ℤ_[p]) = Int.castRingHom R from RingHom.ext_int _ _]

theorem pairFam_famInt (b : Fin 2) (m : ℕ) :
    WittLaw.pairFam (famInt p R) (b, m) =
      ((MvPolynomial.map (algebraMap ℤ_[p] R) (blkCoord p b m) : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) := by
  rw [WittLaw.pairFam_apply, famInt, blkCoord, MvPolynomial.map_bind₁]
  simp only [MvPolynomial.map_X]
  have hblk : WittLaw.blk (R := R) b = fun m' =>
      ((MvPolynomial.X (b, m') : MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext m'
    simp [WittLaw.blk, MvPolynomial.coe_X]
  rw [hblk, MvPowerSeries.subst_coe, aeval_coe_eq_coe_bind₁]

theorem subst_addFam_famInt (n : ℕ) :
    MvPowerSeries.subst (WittLaw.addFam p R) (famInt p R n) =
      MvPowerSeries.subst (WittLaw.pairFam (famInt p R)) (BigWittLaw.addFam R n) := by
  have hc : ∀ P : MvPolynomial (Fin 2 × ℕ) R,
      (P : MvPowerSeries (Fin 2 × ℕ) R) = MvPolynomial.coeToMvPowerSeries.ringHom P := fun _ => rfl

  have hS : WittLaw.addFam p R = fun m =>
      ((MvPolynomial.map (algebraMap ℤ_[p] R) (SO p m) : MvPolynomial (Fin 2 × ℕ) R) :
        MvPowerSeries (Fin 2 × ℕ) R) :=
    funext (addFam_eq_coe_map_SO p R)
  have hL : MvPowerSeries.subst (WittLaw.addFam p R) (famInt p R n) =
      ((MvPolynomial.map (algebraMap ℤ_[p] R) (MvPolynomial.bind₁ (SO p) (coord p n)) :
        MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    rw [hS, famInt, MvPowerSeries.subst_coe, aeval_coe_eq_coe_bind₁, MvPolynomial.map_bind₁]

  have hP := WittLaw.hasSubst_pairFam (hasSubst_famInt p R) (constantCoeff_famInt p R)
  rw [hL, bind₁_SO_coord, BigWittLaw.subst_addFam hP]
  simp only [pairFam_famInt, hc, map_add, map_mul, map_sum]

end IntBase

section Compose

open MvPowerSeries MvFormalGroup.WittLaw

variable {p}
variable {R : Type u} [CommRing R] {d : ℕ}

structure IsHomToBigWitt (p : ℕ) [Fact p.Prime] (u : ℕ → MvPowerSeries ℕ R) : Prop where
  hasSubst : HasSubst u
  constantCoeff : ∀ n, (u n).constantCoeff = 0
  subst_addFam : ∀ n, subst (WittLaw.addFam p R) (u n) = subst (WittLaw.pairFam u) (BigWittLaw.addFam R n)

variable {Φ : MvFormalGroup d R}

def compose (G : Fin d → MvPowerSeries ℕ R) (hG0 : ∀ j, (G j).constantCoeff = 0)
    (hG : ∀ j, subst (BigWittLaw.addFam R) (G j) =
      subst (Sum.elim
        (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))
    {u : ℕ → MvPowerSeries ℕ R} (hu : IsHomToBigWitt p u) : CartierModule p Φ where
  toPowerSeries := fun j => subst u (G j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_eq_zero hu.hasSubst hu.constantCoeff (hG0 j)
  subst_eq := by
    intro j
    have hA := hasSubst_addFam p R
    have hP := hasSubst_pairFam hu.hasSubst hu.constantCoeff
    have hB := BigWittLaw.hasSubst_addFam R
    show subst (WittLaw.addFam p R) (subst u (G j)) =
      subst (Sum.elim (CartierModule.inBlk 0 fun l => subst u (G l))
        (CartierModule.inBlk 1 fun l => subst u (G l))) (Φ.toPowerSeries j)
    rw [subst_comp_subst_apply hu.hasSubst hA]
    have hfam : (fun n => subst (WittLaw.addFam p R) (u n)) =
        fun n => subst (WittLaw.pairFam u) (BigWittLaw.addFam R n) := funext hu.subst_addFam
    have hG' : subst (BigWittLaw.addFam R) (G j) =
        subst (Sum.elim (CartierModule.inBlk 0 G) (CartierModule.inBlk 1 G)) (Φ.toPowerSeries j) :=
      hG j
    rw [hfam, ← subst_comp_subst_apply hB hP, hG',
      subst_subst_elim Φ (CartierModule.constantCoeff_inBlk 0 hG0)
        (CartierModule.constantCoeff_inBlk 1 hG0) hP]
    congr 1
    funext s
    rcases s with l | l
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 0 (G l)
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 1 (G l)

@[scoped simp] theorem toPowerSeries_compose (G : Fin d → MvPowerSeries ℕ R)
    (hG0 : ∀ j, (G j).constantCoeff = 0)
    (hG : ∀ j, subst (BigWittLaw.addFam R) (G j) =
      subst (Sum.elim
        (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))
    {u : ℕ → MvPowerSeries ℕ R} (hu : IsHomToBigWitt p u) (j : Fin d) :
    (compose G hG0 hG hu).toPowerSeries j = subst u (G j) := rfl

theorem coeff_single_zero_subst {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0)
    (hu1 : ∀ n, coeff (Finsupp.single 0 1) (u n) = if n = 0 then 1 else 0) (f : MvPowerSeries ℕ R) :
    coeff (Finsupp.single 0 1) (subst u f) = coeff (Finsupp.single 0 1) f := by
  classical
  rw [coeff_subst hu, finsum_eq_single _ (Finsupp.single 0 1)]
  · rw [Finsupp.prod_single_index (h := fun s n => (u s) ^ n) (pow_zero (u 0)), pow_one, hu1 0,
      if_pos rfl, smul_eq_mul, mul_one]
  · intro e he
    suffices hz : coeff (Finsupp.single 0 1) (e.prod fun s n => (u s) ^ n) = 0 by
      rw [hz, smul_zero]
    rcases Nat.lt_trichotomy e.degree 1 with hlt | heq | hgt
    · have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
      subst he0
      rw [Finsupp.prod_zero_index, MvPowerSeries.coeff_one, if_neg (Finsupp.single_ne_zero.mpr one_ne_zero)]
    · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = e := by
        have hmem' : e ∈ {d' : ℕ →₀ ℕ | d'.degree = 1} := heq
        rw [← Finsupp.range_single_one] at hmem'
        exact hmem'
      have ha : a ≠ 0 := fun h => he (by rw [h])
      rw [Finsupp.prod_single_index (h := fun s n => (u s) ^ n) (pow_zero (u a)), pow_one, hu1 a,
        if_neg ha]
    · have horder : (((Finsupp.single (0 : ℕ) 1).degree : ℕ) : ℕ∞) <
          (e.prod fun s n => (u s) ^ n).order := by
        refine lt_of_lt_of_le ?_ (le_order_finsuppProd_pow hu0 e)
        rw [Finsupp.degree_single]
        exact_mod_cast hgt
      exact coeff_of_lt_order horder

theorem coeff_one_subst_curveFam (f : MvPowerSeries ℕ R) :
    PowerSeries.coeff 1 (subst (CartierModule.curveFam R) f) = coeff (Finsupp.single 0 1) f := by
  classical
  have hC := CartierModule.hasSubst_curveFam (R := R)
  show MvPowerSeries.coeff (Finsupp.single () 1) (subst (CartierModule.curveFam R) f) = _
  rw [coeff_subst hC]
  have hterm : ∀ e : ℕ →₀ ℕ, e ≠ Finsupp.single 0 1 →
      coeff e f • coeff (Finsupp.single () 1) (e.prod fun n k => CartierModule.curveFam R n ^ k) = 0 := by
    intro e he
    by_cases hsupp : ∃ n ∈ e.support, n ≠ 0
    · obtain ⟨n, hn, hn0⟩ := hsupp
      have hzero : (e.prod fun n k => CartierModule.curveFam R n ^ k) = 0 := by
        rw [Finsupp.prod]
        refine Finset.prod_eq_zero hn ?_
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        show (0 : PowerSeries R) ^ e (m + 1) = 0
        exact zero_pow (Finsupp.mem_support_iff.mp hn)
      rw [hzero, map_zero, smul_zero]
    · push Not at hsupp
      have he0 : e = Finsupp.single 0 (e 0) := by
        ext n
        by_cases hn : n = 0
        · subst hn; simp
        · rw [Finsupp.single_apply, if_neg (Ne.symm hn)]
          by_contra hne
          exact hn (hsupp n (Finsupp.mem_support_iff.mpr hne))
      have hk : e 0 ≠ 1 := fun h1 => he (by rw [he0, h1])
      rw [he0, Finsupp.prod_single_index (by simp)]
      show coeff _ f • coeff (Finsupp.single () 1) ((PowerSeries.X : PowerSeries R) ^ e 0) = 0
      rw [PowerSeries.X, MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
      intro h
      exact hk ((Finsupp.single_injective ()) h).symm
  rw [finsum_eq_single _ (Finsupp.single 0 1) hterm, Finsupp.prod_single_index (by simp)]
  show coeff _ f • coeff (Finsupp.single () 1) ((PowerSeries.X : PowerSeries R) ^ 1) = _
  rw [pow_one, PowerSeries.X, MvPowerSeries.coeff_X, if_pos rfl, smul_eq_mul, mul_one]

theorem tangent_surjective [Algebra ℤ_[p] R] (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective (CartierModule.tangent : CartierModule p Φ → Fin d → R) := by
  intro v

  obtain ⟨G, hG0, hG, hcurve⟩ := BigWittLaw.exists_hom_subst_curveFam_eq Φ
    (fun j => v j • (PowerSeries.X : PowerSeries R)) (fun j => by simp)

  have hAH : IsHomToBigWitt p (famInt p R) :=
    ⟨hasSubst_famInt p R, constantCoeff_famInt p R, subst_addFam_famInt p R⟩
  refine ⟨compose G hG0 hG hAH, funext fun j => ?_⟩
  rw [CartierModule.tangent_apply, toPowerSeries_compose,
    coeff_single_zero_subst (hasSubst_famInt p R) (constantCoeff_famInt p R)
      (coeff_single_zero_famInt p R) (G j),
    ← coeff_one_subst_curveFam, hcurve j]
  simp

end Compose

end CartierExistenceIntSol
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt.CartierExistenceIntSol"

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [Algebra ℤ_[p] R] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
      (MvFormalGroup.CartierModule.tangent : MvFormalGroup.CartierModule p Φ → Fin d → R) :=
  CartierExistenceIntSol.tangent_surjective Φ

end
p2m_reactivate "P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt.CartierExistenceIntSol"

end S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt (solution)
