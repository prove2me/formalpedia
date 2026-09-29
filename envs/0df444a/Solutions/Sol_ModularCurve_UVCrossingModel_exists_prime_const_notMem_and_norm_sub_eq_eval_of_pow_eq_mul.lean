-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_prime_const_notMem_and_norm_sub_eq_eval_of_pow_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b42f6b83-d321-521d-84dc-46e1b420208a

import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Theorems.Thm_ModularCurve_UVCrossingModel_free_and_finite_quotient_of_ne_bot_of_const_notMem
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Theorems.Thm_MvPowerSeries_exists_algEquiv_apply_X_eq
import Theorems.Thm_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt
import Theorems.Thm_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_prime_const_notMem_and_norm_sub_eq_eval_of_pow_eq_mul
set_option autoImplicit false

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

namespace CrossingValueBranch

section BranchReduction

variable {W : Type*} [CommRing W] {π : W} {E : ℕ}

private def coeffRed (π : W) (E : ℕ) (hE : 1 ≤ E) : W ⧸ Ideal.span {π ^ E} →+* W ⧸ Ideal.span {π} :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self π (Nat.one_le_iff_ne_zero.mp hE)))

private theorem coeffRed_mk (hE : 1 ≤ E) (a : W) :
    coeffRed π E hE (Ideal.Quotient.mk (Ideal.span {π ^ E}) a) = Ideal.Quotient.mk (Ideal.span {π}) a :=
  Ideal.Quotient.factor_mk _ a

private noncomputable def branchRed (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E})) :
    UVCrossingModel W (π ^ E) →+* PowerSeries (W ⧸ Ideal.span {π}) :=
  (PowerSeries.map (coeffRed π E hE)).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {T})))

private theorem branchRed_apply (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (r : UVCrossingModel W (π ^ E)) :
    branchRed hE T e r = PowerSeries.map (coeffRed π E hE) (e (Ideal.Quotient.mk (Ideal.span {T}) r)) :=
  rfl

private theorem branchRed_self (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E})) :
    branchRed hE T e T = 0 := by
  rw [branchRed_apply, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self T), map_zero, map_zero]

private theorem branchRed_const (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heC : ∀ w : W, e (Ideal.Quotient.mk _ (const (π ^ E) w))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) w))
    (w : W) :
    branchRed hE T e (const (π ^ E) w) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by
  rw [branchRed_apply, heC, PowerSeries.map_C, coeffRed_mk]

private theorem branchRed_eq_X (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    {S : UVCrossingModel W (π ^ E)} (heS : e (Ideal.Quotient.mk _ S) = PowerSeries.X) :
    branchRed hE T e S = PowerSeries.X := by
  rw [branchRed_apply, heS, PowerSeries.map_X]

private theorem branchRed_eq_zero_iff (hE : 1 ≤ E) (T : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heC : ∀ w : W, e (Ideal.Quotient.mk _ (const (π ^ E) w))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) w))
    (r : UVCrossingModel W (π ^ E)) :
    branchRed hE T e r = 0 ↔ r ∈ Ideal.span {const (π ^ E) π, T} := by
  constructor
  · intro hr
    rw [branchRed_apply] at hr

    have hcoef : ∀ n, ∃ b : W, PowerSeries.coeff n (e (Ideal.Quotient.mk (Ideal.span {T}) r))
        = Ideal.Quotient.mk (Ideal.span {π ^ E}) (π * b) := by
      intro n
      have hn := congrArg (PowerSeries.coeff n) hr
      rw [PowerSeries.coeff_map, map_zero] at hn
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
        (PowerSeries.coeff n (e (Ideal.Quotient.mk (Ideal.span {T}) r)))
      rw [← ha, coeffRed_mk] at hn
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hn)
      exact ⟨b, by rw [← ha, ← hb, mul_comm]⟩
    choose b hb using hcoef
    have hg : e (Ideal.Quotient.mk (Ideal.span {T}) r)
        = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) π)
          * PowerSeries.mk fun n => Ideal.Quotient.mk (Ideal.span {π ^ E}) (b n) := by
      ext n
      simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← map_mul, hb n]

    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
      ((e.symm) (PowerSeries.mk fun n => Ideal.Quotient.mk (Ideal.span {π ^ E}) (b n)))
    have hr' : Ideal.Quotient.mk (Ideal.span {T}) r = Ideal.Quotient.mk (Ideal.span {T}) (const (π ^ E) π * s) := by
      apply e.injective
      rw [map_mul (Ideal.Quotient.mk (Ideal.span {T})), map_mul e, heC π, hs, RingEquiv.apply_symm_apply, hg]
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hr')
    exact Ideal.mem_span_pair.mpr ⟨s, t, by linear_combination ht⟩
  · intro hr
    obtain ⟨a, c, hac⟩ := Ideal.mem_span_pair.mp hr
    rw [← hac, map_add, map_mul, map_mul, branchRed_self, branchRed_const hE T e heC, mul_zero, add_zero,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self π), map_zero, mul_zero]

private theorem isPrime_span_const_and_not_mem (hp : (Ideal.span {π}).IsPrime) (hE : 1 ≤ E)
    (T S : UVCrossingModel W (π ^ E))
    (e : (UVCrossingModel W (π ^ E) ⧸ Ideal.span {T}) ≃+* PowerSeries (W ⧸ Ideal.span {π ^ E}))
    (heS : e (Ideal.Quotient.mk _ S) = PowerSeries.X)
    (heC : ∀ w : W, e (Ideal.Quotient.mk _ (const (π ^ E) w))
      = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π ^ E}) w)) :
    (Ideal.span {const (π ^ E) π, T}).IsPrime ∧ S ∉ Ideal.span {const (π ^ E) π, T} := by
  haveI := hp
  haveI : IsDomain (W ⧸ Ideal.span {π}) := Ideal.Quotient.isDomain _
  have hker : RingHom.ker (branchRed hE T e) = Ideal.span {const (π ^ E) π, T} := by
    ext r
    rw [RingHom.mem_ker]
    exact branchRed_eq_zero_iff hE T e heC r
  refine ⟨?_, fun hS => ?_⟩
  · rw [← hker]
    exact RingHom.ker_isPrime _
  have h0 := (branchRed_eq_zero_iff hE T e heC S).mpr hS
  rw [branchRed_eq_X hE T e heS] at h0
  exact PowerSeries.X_ne_zero h0

private theorem coeff_natTrailingDegree_eval₂_X_mul {S : Type*} [CommRing S] (p : Polynomial S)
    (u : PowerSeries S) :
    PowerSeries.coeff p.natTrailingDegree (p.eval₂ (PowerSeries.C) (PowerSeries.X * u))
      = p.trailingCoeff * PowerSeries.constantCoeff u ^ p.natTrailingDegree := by
  rw [Polynomial.trailingCoeff, Polynomial.eval₂_eq_sum_range, map_sum,
    Finset.sum_eq_single p.natTrailingDegree]
  · rw [PowerSeries.coeff_C_mul, mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  · intro i _ hne
    rw [PowerSeries.coeff_C_mul, mul_pow, PowerSeries.coeff_X_pow_mul']
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt, zero_mul]
    · rw [if_neg (not_le.mpr hgt), mul_zero]
  · intro hnot
    rw [Finset.mem_range, not_lt] at hnot
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hnot), map_zero, zero_mul, map_zero]

end BranchReduction

private theorem eval_map_constHom_ne_zero {W : Type*} [CommRing W] {π : W} (hp : (Ideal.span {π}).IsPrime)
    (E : ℕ) (hE : 1 ≤ E) (g : Polynomial W) (hg : ∃ i, g.coeff i ∉ Ideal.span {π})
    (α : UVCrossingModel W (π ^ E)) (hα : IsUnit α) :
    (g.map (constHom (π ^ E))).eval (V (π ^ E) * α) ≠ 0 := by
  haveI := hp
  haveI : IsDomain (W ⧸ Ideal.span {π}) := Ideal.Quotient.isDomain _
  obtain ⟨e, heV, -, heC⟩ := exists_ringEquiv_quotient_span_U_powerSeries (π ^ E)
  intro h0
  have h1 := congrArg (branchRed hE (U (π ^ E)) e) h0
  rw [map_zero, Polynomial.eval_map, Polynomial.hom_eval₂, map_mul, branchRed_eq_X hE _ e heV] at h1
  have hcomp : (branchRed hE (U (π ^ E)) e).comp (constHom (π ^ E))
      = (PowerSeries.C (R := W ⧸ Ideal.span {π})).comp (Ideal.Quotient.mk (Ideal.span {π})) :=
    RingHom.ext fun w => by
      rw [RingHom.comp_apply, RingHom.comp_apply, constHom_apply, branchRed_const hE _ e heC]
  rw [hcomp, ← Polynomial.eval₂_map] at h1
  have hne : g.map (Ideal.Quotient.mk (Ideal.span {π})) ≠ 0 := by
    obtain ⟨i, hi⟩ := hg
    intro hz
    apply hi
    have hzi := congrArg (fun p => Polynomial.coeff p i) hz
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hzi
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzi
  have hu : IsUnit (PowerSeries.constantCoeff (branchRed hE (U (π ^ E)) e α)) :=
    PowerSeries.isUnit_constantCoeff _ (hα.map _)
  have h2 := congrArg (PowerSeries.coeff (g.map (Ideal.Quotient.mk (Ideal.span {π}))).natTrailingDegree) h1
  rw [coeff_natTrailingDegree_eval₂_X_mul, map_zero] at h2
  exact mul_ne_zero (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hne) (pow_ne_zero _ hu.ne_zero) h2

section UnitLift

variable {W : Type*} [CommRing W]

private noncomputable def twistFamily (eu : (MvPowerSeries (Fin 2) W)ˣ) : Fin 2 → MvPowerSeries (Fin 2) W :=
  ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * ((eu⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W),
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) * ((eu : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W)]

private theorem twistFamily_zero (eu : (MvPowerSeries (Fin 2) W)ˣ) :
    twistFamily eu 0 = (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) *
      ((eu⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) := rfl

private theorem twistFamily_one (eu : (MvPowerSeries (Fin 2) W)ˣ) :
    twistFamily eu 1 = (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) *
      ((eu : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) := rfl

private theorem isUnit_of_mul_sub_one_eq [IsLocalRing W] {c : W} (hc : c ∈ IsLocalRing.maximalIdeal W)
    {f g h : MvPowerSeries (Fin 2) W}
    (hfg : h * (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C c) = f * g - 1) : IsUnit f := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  have h0 := congrArg MvPowerSeries.constantCoeff hfg
  simp only [map_sub, map_mul, map_one, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, zero_mul,
    zero_sub, mul_neg] at h0
  have h1 : MvPowerSeries.constantCoeff f * MvPowerSeries.constantCoeff g =
      1 - c * MvPowerSeries.constantCoeff h := by
    linear_combination -h0
  exact isUnit_of_mul_isUnit_left (h1 ▸ IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mul_mem_right _ _ hc)))

private theorem coeff_single_X_mul (i j : Fin 2) (φ : MvPowerSeries (Fin 2) W) :
    MvPowerSeries.coeff (Finsupp.single j 1) (MvPowerSeries.X i * φ) =
      if i = j then MvPowerSeries.constantCoeff φ else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases hij : i = j
  · subst hij
    rw [if_pos le_rfl, if_pos rfl, one_mul, tsub_self, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [if_neg hij, if_neg]
    intro hle
    have := hle i
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij] at this
    exact Nat.not_succ_le_zero 0 this

private theorem exists_unit_mk_eq [IsLocalRing W] {π : W} (hπ : ¬ IsUnit π) {E : ℕ} (hE : 1 ≤ E)
    {α : UVCrossingModel W (π ^ E)} (hα : IsUnit α) :
    ∃ eu : (MvPowerSeries (Fin 2) W)ˣ, mk (π ^ E) eu = α := by
  obtain ⟨f, rfl⟩ := mk_surjective (π ^ E) α
  obtain ⟨β, hβ⟩ := hα.exists_right_inv
  obtain ⟨g, rfl⟩ := mk_surjective (π ^ E) β
  have h0 : mk (π ^ E) (f * g - 1) = 0 := by rw [map_sub, map_mul, map_one, hβ, sub_self]
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hf : IsUnit f := isUnit_of_mul_sub_one_eq
    (Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal π).mpr hπ) E hE) hh
  exact ⟨hf.unit, by rw [IsUnit.unit_spec]⟩

private theorem constantCoeff_twistFamily (eu : (MvPowerSeries (Fin 2) W)ˣ) (i : Fin 2) :
    MvPowerSeries.constantCoeff (twistFamily eu i) = 0 := by
  revert i
  rw [Fin.forall_fin_two, twistFamily_zero, twistFamily_one, map_mul, map_mul, MvPowerSeries.constantCoeff_X,
    MvPowerSeries.constantCoeff_X, zero_mul, zero_mul]
  exact ⟨rfl, rfl⟩

private theorem isUnit_det_coeff_twistFamily (eu : (MvPowerSeries (Fin 2) W)ˣ) :
    IsUnit (Matrix.det (Matrix.of fun i j : Fin 2 =>
      MvPowerSeries.coeff (Finsupp.single j 1) (twistFamily eu i))) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply, twistFamily_zero, twistFamily_one, coeff_single_X_mul, if_true, Fin.one_eq_zero_iff,
    OfNat.ofNat_ne_one, if_false, mul_zero, sub_zero]
  rw [← map_mul, Units.inv_mul, map_one]
  exact isUnit_one

private theorem algEquiv_apply_X_mul_X_sub_C (eu : (MvPowerSeries (Fin 2) W)ˣ)
    (σ : MvPowerSeries (Fin 2) W ≃ₐ[W] MvPowerSeries (Fin 2) W) (hσ : ∀ i, σ (MvPowerSeries.X i) = twistFamily eu i)
    (c : W) :
    σ (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C c) =
      MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C c := by
  have hC : (MvPowerSeries.C c : MvPowerSeries (Fin 2) W) = algebraMap W (MvPowerSeries (Fin 2) W) c := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [map_sub, map_mul, hσ 0, hσ 1, twistFamily_zero, twistFamily_one, hC, AlgEquiv.commutes, mul_mul_mul_comm,
    Units.inv_mul, mul_one]

end UnitLift

section AdicPoint

variable {W : Type*} [CommRing W] {S : Type*} [CommRing S]

private theorem exists_ringHom_mvPowerSeries_apply_X_eq (J : Ideal S) [IsAdicComplete J S] (φ : W →+* S)
    (x : Fin 2 → S) (hx : ∀ i, x i ∈ J.radical) :
    ∃ ev : MvPowerSeries (Fin 2) W →+* S,
      (∀ w : W, ev (MvPowerSeries.C w) = φ w) ∧ ∀ i, ev (MvPowerSeries.X i) = x i := by
  classical
  letI : UniformSpace W := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : CompleteSpace S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).1
  haveI : T2Space S :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J S›).2
  have hnil : ∀ i, IsTopologicallyNilpotent (x i) := by
    intro i
    obtain ⟨k, hk⟩ := hx i
    show Filter.Tendsto (x i ^ ·) Filter.atTop (nhds 0)
    rw [(J.hasBasis_nhds_zero_adic).tendsto_right_iff]
    intro n _
    filter_upwards [Filter.eventually_ge_atTop (k * n)] with m hm
    obtain ⟨r, rfl⟩ : ∃ r, m = k * n + r := ⟨m - k * n, by omega⟩
    rw [pow_add, pow_mul]
    exact SetLike.mem_coe.mpr (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk n))
  have ha : MvPowerSeries.HasEval x := by
    refine ⟨hnil, ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot
  have hφ : Continuous φ := continuous_of_discreteTopology
  refine ⟨MvPowerSeries.eval₂Hom hφ ha, fun w => ?_, fun i => ?_⟩
  · rw [show MvPowerSeries.eval₂Hom hφ ha (MvPowerSeries.C w) = MvPowerSeries.eval₂ φ x (MvPowerSeries.C w) from
      congrFun (MvPowerSeries.coe_eval₂Hom hφ ha) _, MvPowerSeries.eval₂_C]
  · rw [show MvPowerSeries.eval₂Hom hφ ha (MvPowerSeries.X i) = MvPowerSeries.eval₂ φ x (MvPowerSeries.X i) from
      congrFun (MvPowerSeries.coe_eval₂Hom hφ ha) _, MvPowerSeries.eval₂_X]

private theorem exists_ringHom_const_eq_and_apply_V_mul_eq [IsLocalRing W] {π : W} (hπ : ¬ IsUnit π) {E : ℕ}
    (hE : 1 ≤ E) (J : Ideal S) [IsAdicComplete J S] (φ : W →+* S) (u v : S) (hu : u ∈ J.radical)
    (hv : v ∈ J.radical) (huv : u * v = φ (π ^ E)) (α : UVCrossingModel W (π ^ E)) (hα : IsUnit α) :
    ∃ ψ : UVCrossingModel W (π ^ E) →+* S, (∀ w : W, ψ (const (π ^ E) w) = φ w) ∧ ψ (V (π ^ E) * α) = v := by
  obtain ⟨eu, heu⟩ := exists_unit_mk_eq hπ hE hα
  obtain ⟨σ, hσ⟩ := MvPowerSeries.exists_algEquiv_apply_X_eq (twistFamily eu) (constantCoeff_twistFamily eu)
    (isUnit_det_coeff_twistFamily eu)
  obtain ⟨ev, hevC, hevX⟩ := exists_ringHom_mvPowerSeries_apply_X_eq J φ ![u, v]
    (fun i => by fin_cases i <;> simpa)

  have hgen : σ.symm (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (π ^ E)) =
      MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (π ^ E) := by
    conv_lhs => rw [← algEquiv_apply_X_mul_X_sub_C eu σ hσ (π ^ E)]
    exact σ.symm_apply_apply _
  have hu0 : ev (MvPowerSeries.X 0) = u := by simpa using hevX 0
  have hv1 : ev (MvPowerSeries.X 1) = v := by simpa using hevX 1
  have hθ : ∀ a, (ev.comp σ.symm.toRingEquiv.toRingHom) a = ev (σ.symm a) := fun a => rfl
  have hker : ∀ a ∈ uvCrossingIdeal W (π ^ E), (ev.comp σ.symm.toRingEquiv.toRingHom) a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [hθ, map_mul, hgen, map_mul, map_sub, map_mul, hu0, hv1, hevC, huv, sub_self, mul_zero]
  refine ⟨Ideal.Quotient.lift _ _ hker, fun w => ?_, ?_⟩
  · show Ideal.Quotient.lift _ _ hker (Ideal.Quotient.mk _ (MvPowerSeries.C w)) = φ w
    rw [Ideal.Quotient.lift_mk, hθ, show σ.symm (MvPowerSeries.C w) = MvPowerSeries.C w from by
      simpa only [MvPowerSeries.c_eq_algebraMap] using σ.symm.commutes w, hevC]
  · rw [← heu, show V (π ^ E) = mk (π ^ E) (MvPowerSeries.X 1) from rfl, ← map_mul, ← twistFamily_one, ← hσ 1]
    show Ideal.Quotient.lift _ _ hker (Ideal.Quotient.mk _ (σ (MvPowerSeries.X 1))) = v
    rw [Ideal.Quotient.lift_mk, hθ, σ.symm_apply_apply, hv1]

end AdicPoint

private theorem exists_norm_sub_eq_eval_and_eval₂_eq_zero {W : Type*} [CommRing W] {B : Type*}
    [CommRing B] [Algebra W B] [Module.Free W B] [Module.Finite W B] (y : B) :
    ∃ χ : Polynomial W, (∀ t : W, Algebra.norm W (algebraMap W B t - y) = χ.eval t) ∧
      ∀ (S : Type*) [CommRing S] (ψ : B →+* S), χ.eval₂ (ψ.comp (algebraMap W B)) (ψ y) = 0 := by
  refine ⟨(LinearMap.mulLeft W y).charpoly, fun t => ?_, fun S _ ψ => ?_⟩
  · rw [LinearMap.eval_charpoly, Algebra.norm_apply, map_sub, AlgHom.commutes]
    rfl
  · have h : Polynomial.aeval y (LinearMap.mulLeft W y).charpoly = 0 := by
      have hCH := LinearMap.aeval_self_charpoly (LinearMap.mulLeft W y)
      rw [show LinearMap.mulLeft W y = Algebra.lmul W B y from rfl, Polynomial.aeval_algHom_apply] at hCH
      have h__af := (congrArg (fun f : Module.End W B => f 1) hCH)
      simp at h__af
      exact h__af
    have h' := congrArg ψ h
    rwa [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at h'

private theorem algebraMap_eq_const {W : Type*} [CommRing W] (p : W) (t : W) :
    algebraMap W (UVCrossingModel W p) t = const p t := rfl

private theorem exists_polynomial_coeff_notMem_eval_eq_zero (O : Subring (AlgebraicClosure ℚ)) [IsLocalRing O]
    (x : AlgebraicClosure ℚ) :
    ∃ g : Polynomial O, (∃ i, g.coeff i ∉ maximalIdeal O) ∧ (g.map O.subtype).eval x = 0 := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨p, hp0, hpx⟩ := halg
  have hp₁x : Polynomial.aeval x p.primPart = 0 := by
    rw [p.eq_C_content_mul_primPart, map_mul, Polynomial.aeval_C] at hpx
    refine (mul_eq_zero.mp hpx).resolve_left ?_
    rw [eq_intCast, Int.cast_eq_zero, Polynomial.content_eq_zero_iff]
    exact hp0
  have hprim : p.primPart.IsPrimitive := p.isPrimitive_primPart
  have hcoef : ∃ i, ((p.primPart.coeff i : ℤ) : O) ∉ maximalIdeal O := by
    by_contra h
    push Not at h
    have hprinc := (Ideal.comap (Int.castRingHom O) (maximalIdeal O)).span_singleton_generator
    have hdvd : Polynomial.C (Submodule.IsPrincipal.generator (Ideal.comap (Int.castRingHom O) (maximalIdeal O))) ∣
        p.primPart :=
      (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr fun i => Ideal.mem_span_singleton.mp (by
        rw [hprinc, Ideal.mem_comap, eq_intCast]
        exact h i)
    have htop : Ideal.comap (Int.castRingHom O) (maximalIdeal O) = ⊤ := by
      rw [← hprinc, Ideal.span_singleton_eq_top]
      exact hprim _ hdvd
    have h1 : (1 : ℤ) ∈ Ideal.comap (Int.castRingHom O) (maximalIdeal O) := htop ▸ Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨i, hi⟩ := hcoef
  refine ⟨p.primPart.map (Int.castRingHom O), ⟨i, by rwa [Polynomial.coeff_map, eq_intCast]⟩, ?_⟩
  have hZ : O.subtype.comp (Int.castRingHom O) = algebraMap ℤ (AlgebraicClosure ℚ) := RingHom.ext_int _ _
  rw [Polynomial.map_map, hZ, Polynomial.eval_map, ← Polynomial.aeval_def]
  exact hp₁x

section Completion

open Valued

variable (A : ValuationSubring (AlgebraicClosure ℚ))

private noncomputable def coeC : AlgebraicClosure ℚ →+* (A.valuation).Completion :=
  (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).comp
    (WithVal.equiv A.valuation).symm.toRingHom

private theorem coeC_apply (x : AlgebraicClosure ℚ) : coeC A x = (x : (A.valuation).Completion) := rfl

private theorem coeC_injective : Function.Injective (coeC A) :=
  (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).injective.comp
    (WithVal.equiv A.valuation).symm.injective

private theorem v_coeC (x : AlgebraicClosure ℚ) : Valued.v (coeC A x) = A.valuation x := by
  show Valued.v (((WithVal.equiv A.valuation).symm x : WithVal A.valuation) : (A.valuation).Completion) = _
  rw [Valued.valuedCompletion_apply]
  rfl

private noncomputable def intC (O : Subring (AlgebraicClosure ℚ)) (hO : ∀ o : O, (o : AlgebraicClosure ℚ) ∈ A) :
    O →+* 𝒪[(A.valuation).Completion] :=
  ((coeC A).comp O.subtype).codRestrict _ fun o => (Valuation.mem_integer_iff _ _).mpr (by
    rw [RingHom.comp_apply, v_coeC]
    exact A.valuation_le_one ⟨o, hO o⟩)

private theorem coe_intC (O : Subring (AlgebraicClosure ℚ)) (hO : ∀ o : O, (o : AlgebraicClosure ℚ) ∈ A) (o : O) :
    ((intC A O hO o : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = coeC A o := rfl

set_option synthInstance.maxHeartbeats 800000 in

private theorem intC_mem_radical_span (O : Subring (AlgebraicClosure ℚ))
    (hO : ∀ o : O, (o : AlgebraicClosure ℚ) ∈ A) {a b : O} (ha0 : (a : AlgebraicClosure ℚ) ≠ 0)
    (ha : A.valuation (a : AlgebraicClosure ℚ) < 1) (hb0 : (b : AlgebraicClosure ℚ) ≠ 0) :
    intC A O hO a ∈ (Ideal.span {intC A O hO b}).radical := by
  obtain ⟨n, hn⟩ := A.exists_valuation_pow_lt_of_isAlgebraic ((map_ne_zero _).mpr ha0) ha
    (A.valuation (b : AlgebraicClosure ℚ)) ((map_ne_zero _).mpr hb0)
  refine ⟨n, Ideal.mem_span_singleton.mpr (Valuation.Integers.dvd_of_le (Valuation.integer.integers _) ?_)⟩
  show Valued.v (((intC A O hO a ^ n : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) ≤
    Valued.v ((intC A O hO b : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)
  rw [SubmonoidClass.coe_pow, map_pow, coe_intC, coe_intC, v_coeC, v_coeC]
  exact hn.le

private theorem isAdicComplete_span_intC (O : Subring (AlgebraicClosure ℚ))
    (hO : ∀ o : O, (o : AlgebraicClosure ℚ) ∈ A) {b : O} (hb0 : (b : AlgebraicClosure ℚ) ≠ 0)
    (hb : A.valuation (b : AlgebraicClosure ℚ) < 1) :
    IsAdicComplete (Ideal.span {intC A O hO b}) 𝒪[(A.valuation).Completion] := by
  refine Valued.isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt (intC A O hO b) ?_ fun γ hγ => ?_
  · rw [coe_intC]
    exact (map_ne_zero_iff _ (coeC_injective A)).mpr hb0
  · obtain ⟨n, hn⟩ := A.exists_valuation_pow_lt_of_isAlgebraic ((map_ne_zero _).mpr hb0) hb γ hγ
    exact ⟨n, by rwa [coe_intC, v_coeC]⟩

end Completion

end CrossingValueBranch

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
open CrossingValueBranch in
open Valued in

theorem solution
    {A : ValuationSubring (AlgebraicClosure ℚ)} (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (τ : AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτϖ : τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ ϖ) = π)
    (j : AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) →+*
      𝒪[(A.valuation).Completion])
    (hj : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((j (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o) : 𝒪[(A.valuation).Completion]) :
          (A.valuation).Completion) = ((o : AlgebraicClosure ℚ) : (A.valuation).Completion))
    (α : UVCrossingModel W (π ^ E)) (hα : IsUnit α)
    (c₀ : A) (hc₀ : c₀ ∈ maximalIdeal A)
    (hwin : ∃ m ∈ maximalIdeal A,
      (ϖ : AlgebraicClosure ℚ) ^ E = (c₀ : AlgebraicClosure ℚ) * (m : AlgebraicClosure ℚ))
    (g : Polynomial ↥(NodeLocalized.coeffSubring A K))
    (hg : (g.map (NodeLocalized.coeffSubring A K).subtype).eval (c₀ : AlgebraicClosure ℚ) = 0) :
    ∃ Q : PrimeSpectrum (UVCrossingModel W (π ^ E)),
      const (π ^ E) π ∉ Q.asIdeal ∧
      (g.map ((constHom (π ^ E)).comp (τ.toRingHom.comp
          (algebraMap ↥(NodeLocalized.coeffSubring A K)
            (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K))
              ↥(NodeLocalized.coeffSubring A K)))))).eval (V (π ^ E) * α) ∈ Q.asIdeal ∧
      ∃ χ : Polynomial W,
        (∀ t : W, Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (const (π ^ E) t - V (π ^ E) * α)) = χ.eval t) ∧
        χ.eval₂ ((𝒪[(A.valuation).Completion]).subtype.comp (j.comp τ.symm.toRingHom))
          ((c₀ : AlgebraicClosure ℚ) : (A.valuation).Completion) = 0 := by
  classical

  have memA : ∀ o : ↥(NodeLocalized.coeffSubring A K), (o : AlgebraicClosure ℚ) ∈ A := fun o =>
    (Subring.mem_inf.mp (show (o : AlgebraicClosure ℚ) ∈ A.toSubring ⊓ K.toSubalgebra.toSubring from o.2)).1
  have memK : ∀ o : ↥(NodeLocalized.coeffSubring A K), (o : AlgebraicClosure ℚ) ∈ K := fun o =>
    (Subring.mem_inf.mp (show (o : AlgebraicClosure ℚ) ∈ A.toSubring ⊓ K.toSubalgebra.toSubring from o.2)).2
  have hϖ0 : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    apply hπ.ne_zero
    rw [← hτϖ, show ϖ = 0 from Subtype.ext h, map_zero, map_zero]
  have hϖu : ¬ IsUnit ϖ := fun h => hπ.not_isUnit (by
    rw [← hτϖ]
    exact (h.map _).map τ)
  have hvϖ : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) < 1 := by
    by_contra hlt
    have h1 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) = 1 :=
      le_antisymm (A.valuation_le_one ⟨_, memA ϖ⟩) (not_lt.mp hlt)
    obtain ⟨b, hb⟩ := ((A.valuation_eq_one_iff ⟨_, memA ϖ⟩).mpr h1).exists_right_inv
    have hb' : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 :=
      congrArg Subtype.val hb
    have hbK : (b : AlgebraicClosure ℚ) ∈ K := by
      rw [← inv_eq_of_mul_eq_one_right hb']
      exact K.inv_mem (memK ϖ)
    exact hϖu (isUnit_iff_exists_inv.mpr ⟨⟨b, Subring.mem_inf.mpr ⟨b.2, hbK⟩⟩, Subtype.ext hb'⟩)

  obtain ⟨m, hm, hwinm⟩ := hwin
  have hc₀m0 : (c₀ : AlgebraicClosure ℚ) * (m : AlgebraicClosure ℚ) ≠ 0 := by
    rw [← hwinm]
    exact pow_ne_zero E hϖ0
  have hc₀0 : (c₀ : AlgebraicClosure ℚ) ≠ 0 := left_ne_zero_of_mul hc₀m0
  have hm0 : (m : AlgebraicClosure ℚ) ≠ 0 := right_ne_zero_of_mul hc₀m0
  have hvc₀ : A.valuation (c₀ : AlgebraicClosure ℚ) < 1 := (A.valuation_lt_one_iff c₀).mp hc₀
  have hvm : A.valuation (m : AlgebraicClosure ℚ) < 1 := (A.valuation_lt_one_iff m).mp hm

  haveI := isAdicComplete_span_intC A A.toSubring (fun a => a.2)
    (b := ⟨((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ), memA ϖ⟩) hϖ0 hvϖ
  have huv : intC A A.toSubring (fun a => a.2) m * intC A A.toSubring (fun a => a.2) c₀ =
      (j.comp τ.symm.toRingHom) (π ^ E) := by
    apply Subtype.ext
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_pow,
      (RingEquiv.symm_apply_eq τ).mpr hτϖ.symm, map_pow, SubmonoidClass.coe_pow, hj ϖ, MulMemClass.coe_mul,
      coe_intC, coe_intC, ← coeC_apply, ← map_pow, hwinm, map_mul, mul_comm]
  obtain ⟨ψ, hψc, hψV⟩ := exists_ringHom_const_eq_and_apply_V_mul_eq hπ.not_isUnit hE
    (Ideal.span {intC A A.toSubring (fun a => a.2)
      ⟨((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ), memA ϖ⟩}) (j.comp τ.symm.toRingHom)
    (intC A A.toSubring (fun a => a.2) m) (intC A A.toSubring (fun a => a.2) c₀)
    (intC_mem_radical_span A A.toSubring (fun a => a.2)
      (b := ⟨((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ), memA ϖ⟩) hm0 hvm hϖ0)
    (intC_mem_radical_span A A.toSubring (fun a => a.2)
      (b := ⟨((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ), memA ϖ⟩) hc₀0 hvc₀ hϖ0)
    huv α hα

  have hψconst : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ψ (const (π ^ E) (τ (algebraMap _ _ o))) = intC A (NodeLocalized.coeffSubring A K) memA o := by
    intro o
    rw [hψc]
    apply Subtype.ext
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, τ.symm_apply_apply, hj o,
      coe_intC]
    rfl
  have hkey : ∀ p : Polynomial ↥(NodeLocalized.coeffSubring A K),
      (p.map (NodeLocalized.coeffSubring A K).subtype).eval (c₀ : AlgebraicClosure ℚ) = 0 →
        ψ ((p.map ((constHom (π ^ E)).comp (τ.toRingHom.comp
          (algebraMap ↥(NodeLocalized.coeffSubring A K)
            (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K))
              ↥(NodeLocalized.coeffSubring A K)))))).eval (V (π ^ E) * α)) = 0 := by
    intro p hp
    have hcomp : ψ.comp ((constHom (π ^ E)).comp (τ.toRingHom.comp (algebraMap ↥(NodeLocalized.coeffSubring A K)
        (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K))))) =
        intC A (NodeLocalized.coeffSubring A K) memA :=
      RingHom.ext fun o => hψconst o
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, hcomp, hψV]
    apply Subtype.ext
    rw [show (((p.eval₂ (intC A (NodeLocalized.coeffSubring A K) memA) (intC A A.toSubring (fun a => a.2) c₀) :
        𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) =
        p.eval₂ ((𝒪[(A.valuation).Completion]).subtype.comp (intC A (NodeLocalized.coeffSubring A K) memA))
          (coeC A c₀) from Polynomial.hom_eval₂ p _ (𝒪[(A.valuation).Completion]).subtype _,
      show (𝒪[(A.valuation).Completion]).subtype.comp (intC A (NodeLocalized.coeffSubring A K) memA) =
        (coeC A).comp (NodeLocalized.coeffSubring A K).subtype from RingHom.ext fun o => rfl,
      ← Polynomial.hom_eval₂, ← Polynomial.eval_map, hp, map_zero, ZeroMemClass.coe_zero]

  refine ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩, ?_, ?_, ?_⟩
  ·
    show const (π ^ E) π ∉ RingHom.ker ψ
    rw [RingHom.mem_ker, hψc]
    intro h
    apply hϖ0
    have h' := congrArg Subtype.val h
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      (RingEquiv.symm_apply_eq τ).mpr hτϖ.symm, hj ϖ, ZeroMemClass.coe_zero, ← coeC_apply,
      map_eq_zero_iff _ (coeC_injective A)] at h'
    exact h'
  ·
    exact (RingHom.mem_ker).mpr (hkey g hg)
  ·
    show ∃ χ : Polynomial W,
      (∀ t : W, Algebra.norm W (Ideal.Quotient.mk (RingHom.ker ψ) (const (π ^ E) t - V (π ^ E) * α)) = χ.eval t) ∧
        χ.eval₂ ((𝒪[(A.valuation).Completion]).subtype.comp (j.comp τ.symm.toRingHom))
          ((c₀ : AlgebraicClosure ℚ) : (A.valuation).Completion) = 0
    have hQ0 : RingHom.ker ψ ≠ ⊥ := by
      obtain ⟨g₀, ⟨i, hi⟩, hg₀⟩ :=
        exists_polynomial_coeff_notMem_eval_eq_zero (NodeLocalized.coeffSubring A K) (c₀ : AlgebraicClosure ℚ)
      intro hbot
      have hmem := (RingHom.mem_ker).mpr (hkey g₀ hg₀)
      rw [hbot, Ideal.mem_bot, ← Polynomial.map_map] at hmem
      refine eval_map_constHom_ne_zero ((Ideal.span_singleton_prime hπ.ne_zero).mpr
        (UniqueFactorizationMonoid.irreducible_iff_prime.mp hπ)) E hE _ ⟨i, fun hmem' => hi ?_⟩ α hα hmem
      rw [Polynomial.coeff_map] at hmem'
      by_contra hu
      have hunit : IsUnit ((τ.toRingHom.comp (algebraMap ↥(NodeLocalized.coeffSubring A K)
          (AdicCompletion (maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K))))
          (g₀.coeff i)) := ((IsLocalRing.notMem_maximalIdeal.mp hu).map _)
      exact Ideal.span_singleton_ne_top hπ.not_isUnit (Ideal.eq_top_of_isUnit_mem _ hmem' hunit)
    have hQπ : const (π ^ E) π ∉ RingHom.ker ψ := by
      rw [RingHom.mem_ker, hψc]
      intro h
      apply hϖ0
      have h' := congrArg Subtype.val h
      rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        (RingEquiv.symm_apply_eq τ).mpr hτϖ.symm, hj ϖ, ZeroMemClass.coe_zero, ← coeC_apply,
        map_eq_zero_iff _ (coeC_injective A)] at h'
      exact h'
    haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
    obtain ⟨hfree, hfin⟩ := free_and_finite_quotient_of_ne_bot_of_const_notMem π hπ E hE (RingHom.ker ψ) hQ0 hQπ
    haveI := hfree
    haveI := hfin
    obtain ⟨χ, hχ, hCH⟩ := exists_norm_sub_eq_eval_and_eval₂_eq_zero (W := W)
      (Ideal.Quotient.mk (RingHom.ker ψ) (V (π ^ E) * α))
    refine ⟨χ, fun t => ?_, ?_⟩
    · rw [← hχ t, map_sub, ← Ideal.Quotient.mk_algebraMap, algebraMap_eq_const]
    · have h := hCH (A.valuation).Completion
        ((𝒪[(A.valuation).Completion]).subtype.comp (RingHom.kerLift ψ))
      rw [show ((𝒪[(A.valuation).Completion]).subtype.comp (RingHom.kerLift ψ)).comp
          (algebraMap W (UVCrossingModel W (π ^ E) ⧸ RingHom.ker ψ)) =
          (𝒪[(A.valuation).Completion]).subtype.comp (j.comp τ.symm.toRingHom) from RingHom.ext fun w => by
            show ((RingHom.kerLift ψ (algebraMap W (UVCrossingModel W (π ^ E) ⧸ RingHom.ker ψ) w) :
                𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
              (((j.comp τ.symm.toRingHom) w : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)
            rw [← Ideal.Quotient.mk_algebraMap, algebraMap_eq_const, RingHom.kerLift_mk, hψc],
        RingHom.comp_apply, RingHom.kerLift_mk, hψV] at h
      exact h

end S_ModularCurve_UVCrossingModel_exists_prime_const_notMem_and_norm_sub_eq_eval_of_pow_eq_mul
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_prime_const_notMem_and_norm_sub_eq_eval_of_pow_eq_mul (solution)
