-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_prime_V_sub_const_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/77385923-7669-5414-86dd-c8d5e3cb1399

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_prime_V_sub_const_pow_mem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

universe u

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing

namespace RecipQd

section Eval

variable {W : Type u} [CommRing W] (I : Ideal W) (c : W)

theorem eval_mem_pow_of_X_pow_dvd (hc : c ∈ I) {n : ℕ} {p : Polynomial W} (h : Polynomial.X ^ n ∣ p) :
    Polynomial.eval c p ∈ I ^ n := by
  obtain ⟨q, rfl⟩ := h
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hc n)

theorem mk_eval_trunc_coe (hc : c ∈ I) (n : ℕ) (p : Polynomial W) :
    Ideal.Quotient.mk (I ^ n) (Polynomial.eval c (PowerSeries.trunc n (p : PowerSeries W))) =
      Ideal.Quotient.mk (I ^ n) (Polynomial.eval c p) := by
  rw [Ideal.Quotient.eq, ← Polynomial.eval_sub, ← neg_sub, Polynomial.eval_neg, neg_mem_iff]
  apply eval_mem_pow_of_X_pow_dvd I c hc
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd, Polynomial.coeff_coe, sub_self]

noncomputable def evalTruncHom (hc : c ∈ I) (n : ℕ) : PowerSeries W →+* W ⧸ I ^ n where
  toFun F := Ideal.Quotient.mk (I ^ n) (Polynomial.eval c (PowerSeries.trunc n F))
  map_one' := by
    have h := mk_eval_trunc_coe I c hc n (1 : Polynomial W)
    rw [Polynomial.coe_one] at h
    rw [h, Polynomial.eval_one, map_one]
  map_mul' F G := by
    show Ideal.Quotient.mk (I ^ n) (Polynomial.eval c (PowerSeries.trunc n (F * G))) =
      Ideal.Quotient.mk (I ^ n) (Polynomial.eval c (PowerSeries.trunc n F)) *
        Ideal.Quotient.mk (I ^ n) (Polynomial.eval c (PowerSeries.trunc n G))
    rw [← map_mul, ← Polynomial.eval_mul, ← mk_eval_trunc_coe I c hc n (PowerSeries.trunc n F * PowerSeries.trunc n G),
      Polynomial.coe_mul, PowerSeries.trunc_trunc_mul_trunc]
  map_zero' := by rw [map_zero, Polynomial.eval_zero, map_zero]
  map_add' F G := by rw [map_add, Polynomial.eval_add, map_add]

theorem evalTruncHom_apply (hc : c ∈ I) (n : ℕ) (F : PowerSeries W) :
    evalTruncHom I c hc n F = Ideal.Quotient.mk (I ^ n) (Polynomial.eval c (PowerSeries.trunc n F)) := rfl

theorem factorPow_comp_evalTruncHom (hc : c ∈ I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp (evalTruncHom I c hc n) = evalTruncHom I c hc m := by
  ext F
  rw [RingHom.comp_apply, evalTruncHom_apply, evalTruncHom_apply, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    ← PowerSeries.trunc_trunc_of_le F hle, mk_eval_trunc_coe I c hc m]

variable [IsAdicComplete I W]

noncomputable def evalHom (hc : c ∈ I) : PowerSeries W →+* W :=
  IsAdicComplete.liftRingHom I (evalTruncHom I c hc) (fun hle => factorPow_comp_evalTruncHom I c hc hle)

theorem mk_evalHom (hc : c ∈ I) (n : ℕ) (F : PowerSeries W) :
    Ideal.Quotient.mk (I ^ n) (evalHom I c hc F) = Ideal.Quotient.mk (I ^ n) (Polynomial.eval c (PowerSeries.trunc n F)) := by
  rw [evalHom, IsAdicComplete.mk_liftRingHom, evalTruncHom_apply]

theorem eq_of_forall_mk_eq {x y : W} (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (‹IsAdicComplete I W›.toIsHausdorff) (x - y) (fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.mp (h n)

theorem evalHom_coe (hc : c ∈ I) (p : Polynomial W) : evalHom I c hc (p : PowerSeries W) = Polynomial.eval c p := by
  refine eq_of_forall_mk_eq I (fun n => ?_)
  rw [mk_evalHom, mk_eval_trunc_coe I c hc]

theorem evalHom_X (hc : c ∈ I) : evalHom I c hc PowerSeries.X = c := by
  rw [← Polynomial.coe_X, evalHom_coe, Polynomial.eval_X]

theorem evalHom_C (hc : c ∈ I) (w : W) : evalHom I c hc (PowerSeries.C w) = w := by
  rw [← Polynomial.coe_C, evalHom_coe, Polynomial.eval_C]

end Eval

end RecipQd

namespace RecipQd

section Point

variable {W : Type u} [CommRing W]

noncomputable def pointFun (ϖ : W) (e d : ℕ) : Fin 2 → MvPowerSeries Unit W :=
  fun i => if i = 0 then MvPowerSeries.C (ϖ ^ (e - d - 1)) * MvPowerSeries.X ()
    else MvPowerSeries.C (ϖ ^ (d - 1)) * MvPowerSeries.X ()

theorem hasSubst_pointFun (ϖ : W) (e d : ℕ) : MvPowerSeries.HasSubst (pointFun ϖ e d) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    unfold pointFun
    split_ifs <;> rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero])

noncomputable def pointSubst (ϖ : W) (e d : ℕ) : MvPowerSeries (Fin 2) W →ₐ[W] MvPowerSeries Unit W :=
  MvPowerSeries.substAlgHom (hasSubst_pointFun ϖ e d)

theorem pointSubst_X (ϖ : W) (e d : ℕ) (i : Fin 2) :
    pointSubst ϖ e d (MvPowerSeries.X i) = pointFun ϖ e d i := by
  rw [pointSubst, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X (hasSubst_pointFun ϖ e d)]

theorem pointSubst_C (ϖ : W) (e d : ℕ) (w : W) :
    pointSubst ϖ e d (MvPowerSeries.C w) = MvPowerSeries.C w := by
  rw [show (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = algebraMap W _ w from rfl, AlgHom.commutes,
    MvPowerSeries.algebraMap_apply]
  rfl

variable [IsLocalRing W] [IsAdicComplete (maximalIdeal W) W]

noncomputable def pointHomAmbient (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) : MvPowerSeries (Fin 2) W →+* W :=
  (evalHom (maximalIdeal W) ϖ hϖ).comp (pointSubst ϖ e d).toRingHom

theorem pointHomAmbient_X_zero (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (hde : d + 1 ≤ e) :
    pointHomAmbient ϖ hϖ e d (MvPowerSeries.X 0) = ϖ ^ (e - d) := by
  rw [pointHomAmbient, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pointSubst_X]
  unfold pointFun
  rw [if_pos rfl, map_mul]
  erw [evalHom_C, evalHom_X]
  rw [← pow_succ]
  congr 1
  omega

theorem pointHomAmbient_X_one (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (hd1 : 1 ≤ d) :
    pointHomAmbient ϖ hϖ e d (MvPowerSeries.X 1) = ϖ ^ d := by
  rw [pointHomAmbient, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pointSubst_X]
  unfold pointFun
  rw [if_neg (by decide), map_mul]
  erw [evalHom_C, evalHom_X]
  rw [← pow_succ]
  congr 1
  omega

theorem pointHomAmbient_C (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (w : W) :
    pointHomAmbient ϖ hϖ e d (MvPowerSeries.C w) = w := by
  rw [pointHomAmbient, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pointSubst_C]
  exact evalHom_C _ _ _ w

theorem pointHomAmbient_rel (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e) :
    pointHomAmbient ϖ hϖ e d (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C (ϖ ^ e)) = 0 := by
  rw [map_sub, map_mul, pointHomAmbient_X_zero ϖ hϖ e d hde, pointHomAmbient_X_one ϖ hϖ e d hd1, pointHomAmbient_C,
    ← pow_add, Nat.sub_add_cancel (by omega), sub_self]

noncomputable def pointHom (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e) :
    UVCrossingModel W (ϖ ^ e) →+* W :=
  Ideal.Quotient.lift (uvCrossingIdeal W (ϖ ^ e)) (pointHomAmbient ϖ hϖ e d) (fun a ha => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, pointHomAmbient_rel ϖ hϖ e d hd1 hde, mul_zero])

variable (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e)

theorem pointHom_mk (F : MvPowerSeries (Fin 2) W) :
    pointHom ϖ hϖ e d hd1 hde (mk (ϖ ^ e) F) = pointHomAmbient ϖ hϖ e d F :=
  Ideal.Quotient.lift_mk _ _ _

theorem pointHom_U : pointHom ϖ hϖ e d hd1 hde (U (ϖ ^ e)) = ϖ ^ (e - d) := by
  rw [U, pointHom_mk, pointHomAmbient_X_zero ϖ hϖ e d hde]

theorem pointHom_V : pointHom ϖ hϖ e d hd1 hde (V (ϖ ^ e)) = ϖ ^ d := by
  rw [V, pointHom_mk, pointHomAmbient_X_one ϖ hϖ e d hd1]

theorem pointHom_const (w : W) : pointHom ϖ hϖ e d hd1 hde (const (ϖ ^ e) w) = w := by
  rw [const, pointHom_mk, pointHomAmbient_C]

theorem pointHom_surjective : Function.Surjective (pointHom ϖ hϖ e d hd1 hde) :=
  fun w => ⟨const (ϖ ^ e) w, pointHom_const ϖ hϖ e d hd1 hde w⟩

theorem algebraMap_eq_const (w : W) : algebraMap W (UVCrossingModel W (ϖ ^ e)) w = const (ϖ ^ e) w := rfl

noncomputable def pointAlgHom : UVCrossingModel W (ϖ ^ e) →ₐ[W] W :=
  { pointHom ϖ hϖ e d hd1 hde with
    commutes' := fun w => by
      rw [algebraMap_eq_const]
      exact pointHom_const ϖ hϖ e d hd1 hde w }

theorem pointAlgHom_apply (x : UVCrossingModel W (ϖ ^ e)) :
    pointAlgHom ϖ hϖ e d hd1 hde x = pointHom ϖ hϖ e d hd1 hde x :=
  rfl

end Point

end RecipQd

namespace RecipQd

section Kernel

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

noncomputable def branchIdeal (ϖ : W) (e d : ℕ) : Ideal (UVCrossingModel W (ϖ ^ e)) :=
  Ideal.span {U (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ (e - d)), V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d)}

theorem U_sub_mem_branchIdeal (ϖ : W) (e d : ℕ) : U (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ (e - d)) ∈ branchIdeal ϖ e d :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem V_sub_mem_branchIdeal (ϖ : W) (e d : ℕ) : V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ∈ branchIdeal ϖ e d :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem branchIdeal_le_ker (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e) : branchIdeal ϖ e d ≤ RingHom.ker (pointHom ϖ hϖ e d hd1 hde) := by
  rw [branchIdeal, Ideal.span_le]
  intro x hx
  rcases hx with rfl | hx
  · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, pointHom_U, pointHom_const, sub_self]
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, pointHom_V, pointHom_const, sub_self]

theorem const_mem_maximalIdeal (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e)
    (hϖu : ¬ IsUnit ϖ) [IsLocalRing (UVCrossingModel W (ϖ ^ e))] :
    const (ϖ ^ e) ϖ ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hϖu
  have := hu.map (pointHom ϖ hϖ e d hd1 hde)
  rwa [pointHom_const] at this

theorem const_mem_pow_of_mem (ϖ : W) (e : ℕ) {n : ℕ} {w : W} [IsLocalRing (UVCrossingModel W (ϖ ^ e))]
    (hcϖ : const (ϖ ^ e) ϖ ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)))
    (hw : w ∈ Ideal.span {ϖ ^ n}) :
    const (ϖ ^ e) w ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ n := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hw
  rw [← constHom_apply, map_mul, map_pow, constHom_apply, constHom_apply]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hcϖ n)

theorem ker_le_branchIdeal (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e)
    (hϖirr : Irreducible ϖ) (he : 1 ≤ e) :
    RingHom.ker (pointHom ϖ hϖ e d hd1 hde) ≤ branchIdeal ϖ e d := by
  classical
  haveI : IsNoetherianRing (UVCrossingModel W (ϖ ^ e)) := UVCrossingModel.isNoetherianRing (ϖ ^ e)
  obtain ⟨_, hloc, _⟩ := UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖirr e he
  haveI := hloc
  have hcϖ := const_mem_maximalIdeal ϖ hϖ e d hd1 hde hϖirr.not_isUnit
  intro F hF
  rw [RingHom.mem_ker] at hF

  suffices hkr : ∀ n : ℕ, F ∈ branchIdeal ϖ e d ⊔ maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ n by
    haveI : Module.Finite (UVCrossingModel W (ϖ ^ e)) (UVCrossingModel W (ϖ ^ e) ⧸ branchIdeal ϖ e d) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ (UVCrossingModel W (ϖ ^ e)) (branchIdeal ϖ e d)).toLinearMap
        Ideal.Quotient.mk_surjective
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := UVCrossingModel W (ϖ ^ e) ⧸ branchIdeal ϖ e d)
      (maximalIdeal (UVCrossingModel W (ϖ ^ e))) (maximalIdeal.isMaximal _).ne_top
    have hmem : Ideal.Quotient.mk (branchIdeal ϖ e d) F ∈
        (⨅ i : ℕ, maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ i •
          (⊤ : Submodule (UVCrossingModel W (ϖ ^ e)) (UVCrossingModel W (ϖ ^ e) ⧸ branchIdeal ϖ e d))) := by
      rw [Submodule.mem_iInf]
      intro n
      obtain ⟨j, hj, m, hm, hjm⟩ := Submodule.mem_sup.mp (hkr n)
      have h1 : Ideal.Quotient.mk (branchIdeal ϖ e d) m = m • Ideal.Quotient.mk (branchIdeal ϖ e d) (1 : UVCrossingModel W (ϖ ^ e)) := by
        rw [show m • Ideal.Quotient.mk (branchIdeal ϖ e d) (1 : UVCrossingModel W (ϖ ^ e)) =
          Ideal.Quotient.mk (branchIdeal ϖ e d) (m • (1 : UVCrossingModel W (ϖ ^ e))) from rfl, smul_eq_mul, mul_one]
      rw [← hjm, RingHom.map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add, h1]
      exact Submodule.smul_mem_smul hm Submodule.mem_top
    rw [hbot, Submodule.mem_bot] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmem
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_sup_right Submodule.mem_top

  obtain ⟨G, rfl⟩ := mk_surjective (ϖ ^ e) F
  let N : Fin 2 →₀ ℕ := Finsupp.single 0 (n - 1) + Finsupp.single 1 (n - 1)
  have hN : ∀ m : Fin 2 →₀ ℕ, m ≤ N ↔ m 0 < n ∧ m 1 < n := by
    intro m
    rw [Finsupp.le_def]
    constructor
    · intro h
      have h0 := h 0
      have h1 := h 1
      simp only [N, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at h0 h1
      simp at h0 h1
      omega
    · rintro ⟨h0, h1⟩ i
      fin_cases i <;> simp [N, Finsupp.single_apply] <;> omega
  let p : MvPolynomial (Fin 2) W := MvPowerSeries.trunc' W N G

  have hH : ∀ m : Fin 2 →₀ ℕ, m 0 < n → m 1 < n → MvPowerSeries.coeff m (G - (p : MvPowerSeries (Fin 2) W)) = 0 := by
    intro m h0 h1
    rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos ((hN m).mpr ⟨h0, h1⟩), sub_self]
  let H₁ : MvPowerSeries (Fin 2) W := fun m => if n ≤ m 0 then MvPowerSeries.coeff m (G - (p : MvPowerSeries (Fin 2) W)) else 0
  have hH₁ : ∀ m, MvPowerSeries.coeff m H₁ =
      if n ≤ m 0 then MvPowerSeries.coeff m (G - (p : MvPowerSeries (Fin 2) W)) else 0 := fun m => rfl
  obtain ⟨K₁, hK₁⟩ : MvPowerSeries.X (0 : Fin 2) ^ n ∣ H₁ := by
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [hH₁, if_neg (by omega)]
  obtain ⟨K₂, hK₂⟩ : MvPowerSeries.X (1 : Fin 2) ^ n ∣ (G - (p : MvPowerSeries (Fin 2) W)) - H₁ := by
    rw [MvPowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hH₁]
    split_ifs with h0
    · rw [sub_self]
    · rw [sub_zero]
      exact hH m (by omega) hm
  have hG : G = (p : MvPowerSeries (Fin 2) W) + MvPowerSeries.X 0 ^ n * K₁ + MvPowerSeries.X 1 ^ n * K₂ := by
    rw [← hK₁, ← hK₂]
    ring

  have hval : pointHomAmbient ϖ hϖ e d G = 0 := by
    rw [← pointHom_mk ϖ hϖ e d hd1 hde]
    exact hF
  have hα : (ϖ ^ (e - d)) ^ n ∈ Ideal.span {ϖ ^ n} := by
    rw [← pow_mul, Ideal.mem_span_singleton]
    exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (by omega))
  have hβ : (ϖ ^ d) ^ n ∈ Ideal.span {ϖ ^ n} := by
    rw [← pow_mul, Ideal.mem_span_singleton]
    exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (by omega))
  have hp : pointHomAmbient ϖ hϖ e d (p : MvPowerSeries (Fin 2) W) ∈ Ideal.span {ϖ ^ n} := by
    have h := hval
    rw [hG, map_add, map_add, map_mul, map_mul, map_pow, map_pow, pointHomAmbient_X_zero ϖ hϖ e d hde,
      pointHomAmbient_X_one ϖ hϖ e d hd1] at h
    have : pointHomAmbient ϖ hϖ e d (p : MvPowerSeries (Fin 2) W) =
        -((ϖ ^ (e - d)) ^ n * pointHomAmbient ϖ hϖ e d K₁ + (ϖ ^ d) ^ n * pointHomAmbient ϖ hϖ e d K₂) := by
      linear_combination h
    rw [this]
    exact Submodule.neg_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hα) (Ideal.mul_mem_right _ _ hβ))

  have htaylor : Ideal.Quotient.mk (branchIdeal ϖ e d) (mk (ϖ ^ e) (p : MvPowerSeries (Fin 2) W)) =
      Ideal.Quotient.mk (branchIdeal ϖ e d) (const (ϖ ^ e) (pointHomAmbient ϖ hϖ e d (p : MvPowerSeries (Fin 2) W))) := by
    have key : (Ideal.Quotient.mk (branchIdeal ϖ e d)).comp ((mk (ϖ ^ e)).comp
          (MvPolynomial.coeToMvPowerSeries.ringHom : MvPolynomial (Fin 2) W →+* MvPowerSeries (Fin 2) W)) =
        (Ideal.Quotient.mk (branchIdeal ϖ e d)).comp ((constHom (ϖ ^ e)).comp ((pointHomAmbient ϖ hϖ e d).comp
          (MvPolynomial.coeToMvPowerSeries.ringHom : MvPolynomial (Fin 2) W →+* MvPowerSeries (Fin 2) W))) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C,
          pointHomAmbient_C, constHom_apply]
        rfl
      · intro i
        simp only [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X,
          constHom_apply]
        rw [Ideal.Quotient.eq]
        fin_cases i
        · show mk (ϖ ^ e) (MvPowerSeries.X 0) - const (ϖ ^ e) (pointHomAmbient ϖ hϖ e d (MvPowerSeries.X 0)) ∈ branchIdeal ϖ e d
          rw [pointHomAmbient_X_zero ϖ hϖ e d hde]
          exact U_sub_mem_branchIdeal ϖ e d
        · show mk (ϖ ^ e) (MvPowerSeries.X 1) - const (ϖ ^ e) (pointHomAmbient ϖ hϖ e d (MvPowerSeries.X 1)) ∈ branchIdeal ϖ e d
          rw [pointHomAmbient_X_one ϖ hϖ e d hd1]
          exact V_sub_mem_branchIdeal ϖ e d
    have := congrArg (fun f => f p) key
    simpa only [RingHom.comp_apply, MvPolynomial.coeToMvPowerSeries.ringHom_apply, constHom_apply] using this

  have hsurj : Function.Surjective (Ideal.Quotient.mk (branchIdeal ϖ e d)) := Ideal.Quotient.mk_surjective
  have hU : Ideal.Quotient.mk (branchIdeal ϖ e d) (U (ϖ ^ e)) = Ideal.Quotient.mk (branchIdeal ϖ e d) (const (ϖ ^ e) (ϖ ^ (e - d))) :=
    (Ideal.Quotient.eq).mpr (U_sub_mem_branchIdeal ϖ e d)
  have hV : Ideal.Quotient.mk (branchIdeal ϖ e d) (V (ϖ ^ e)) = Ideal.Quotient.mk (branchIdeal ϖ e d) (const (ϖ ^ e) (ϖ ^ d)) :=
    (Ideal.Quotient.eq).mpr (V_sub_mem_branchIdeal ϖ e d)
  have hcα : const (ϖ ^ e) (ϖ ^ (e - d)) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
    rw [show e - d = (e - d - 1) + 1 by omega, pow_succ, ← constHom_apply, map_mul, constHom_apply, constHom_apply]
    exact Ideal.mul_mem_left _ _ hcϖ
  have hcβ : const (ϖ ^ e) (ϖ ^ d) ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) := by
    rw [show d = (d - 1) + 1 by omega, pow_succ, ← constHom_apply, map_mul, constHom_apply, constHom_apply]
    exact Ideal.mul_mem_left _ _ hcϖ
  obtain ⟨X, hXdef⟩ : ∃ X : UVCrossingModel W (ϖ ^ e), X = const (ϖ ^ e) (pointHomAmbient ϖ hϖ e d (p : MvPowerSeries (Fin 2) W)) +
    const (ϖ ^ e) (ϖ ^ (e - d)) ^ n * mk (ϖ ^ e) K₁ + const (ϖ ^ e) (ϖ ^ d) ^ n * mk (ϖ ^ e) K₂ := ⟨_, rfl⟩
  have hX : X ∈ maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ n := by
    rw [hXdef]
    refine Ideal.add_mem _ (Ideal.add_mem _ (const_mem_pow_of_mem ϖ e hcϖ hp) ?_) ?_
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hcα n)
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hcβ n)
  have hGR : mk (ϖ ^ e) G = mk (ϖ ^ e) (p : MvPowerSeries (Fin 2) W) + U (ϖ ^ e) ^ n * mk (ϖ ^ e) K₁ +
      V (ϖ ^ e) ^ n * mk (ϖ ^ e) K₂ := by
    conv_lhs => rw [hG]
    simp only [map_add, map_mul, map_pow]
    rfl
  have hFX : Ideal.Quotient.mk (branchIdeal ϖ e d) (mk (ϖ ^ e) G) = Ideal.Quotient.mk (branchIdeal ϖ e d) X := by
    rw [hGR, hXdef]
    simp only [map_add, map_mul, map_pow, htaylor, hU, hV]
  have hmem : Ideal.Quotient.mk (branchIdeal ϖ e d) (mk (ϖ ^ e) G) ∈
      (maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ n).map (Ideal.Quotient.mk (branchIdeal ϖ e d)) := by
    rw [hFX]
    exact Ideal.mem_map_of_mem _ hX
  have hcomap := Ideal.comap_map_of_surjective (Ideal.Quotient.mk (branchIdeal ϖ e d)) hsurj
    (maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ n)
  have : mk (ϖ ^ e) G ∈ Ideal.comap (Ideal.Quotient.mk (branchIdeal ϖ e d))
      ((maximalIdeal (UVCrossingModel W (ϖ ^ e)) ^ n).map (Ideal.Quotient.mk (branchIdeal ϖ e d))) :=
    Ideal.mem_comap.mpr hmem
  rw [hcomap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm] at this
  exact this

theorem ker_eq_branchIdeal (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e)
    (hϖirr : Irreducible ϖ) (he : 1 ≤ e) :
    RingHom.ker (pointHom ϖ hϖ e d hd1 hde) = branchIdeal ϖ e d :=
  le_antisymm (ker_le_branchIdeal ϖ hϖ e d hd1 hde hϖirr he) (branchIdeal_le_ker ϖ hϖ e d hd1 hde)

end Kernel

end RecipQd

namespace RecipQd

theorem length_localizedModule_quotient_span_singleton {A : Type u} [CommRing A] (p : Submonoid A) (a : A) :
    Module.length (Localization p) (LocalizedModule p (A ⧸ Ideal.span {a})) =
      Module.length (Localization p) (Localization p ⧸ Ideal.span {algebraMap A (Localization p) a}) := by
  rw [← (localizedQuotientEquiv p (Ideal.span {a} : Submodule A A)).length_eq]
  let e₀ : LocalizedModule p A ≃ₗ[A] Localization p :=
    IsLocalizedModule.iso p (Algebra.linearMap A (Localization p))
  let e : LocalizedModule p A ≃ₗ[Localization p] Localization p :=
    LinearEquiv.extendScalarsOfIsLocalization p (Localization p) e₀
  have he : ∀ x, e x = e₀ x := fun x => LinearEquiv.extendScalarsOfIsLocalization_apply p (Localization p) e₀ x
  have hmap : Submodule.map (e : LocalizedModule p A →ₗ[Localization p] Localization p)
      (Submodule.localized p (Ideal.span {a} : Submodule A A)) =
      (Ideal.span {algebraMap A (Localization p) a} : Submodule (Localization p) (Localization p)) := by
    change Submodule.map _ (Submodule.localized' (Localization p) p (LocalizedModule.mkLinearMap p A) (Submodule.span A {a})) = _
    rw [Submodule.localized'_span, Set.image_singleton, Submodule.map_span, Set.image_singleton, Ideal.span]
    congr 2
    change e (LocalizedModule.mk a 1) = _
    rw [he, IsLocalizedModule.iso_mk_one]
    rfl
  exact (Submodule.Quotient.equiv _ _ e hmap).length_eq

end RecipQd

open RecipQd in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e) :
    ∃ Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)),
      Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ∈ Q.asIdeal ∧
      U (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ (e - d)) ∈ Q.asIdeal ∧
      (∀ P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)), const (ϖ ^ e) ϖ ∉ P.asIdeal →
        V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ∈ P.asIdeal → P = Q) ∧
      Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) ∧ Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) ∧
      Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) = 1 ∧
      Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))) = ϖ ^ d ∧
      Module.length (Localization.AtPrime Q.asIdeal)
        (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d)})) = 1 := by
  classical
  have hϖm : ϖ ∈ maximalIdeal W := hϖ.not_isUnit

  have hker : RingHom.ker (pointHom ϖ hϖm e d hd1 hde) = branchIdeal ϖ e d := ker_eq_branchIdeal ϖ hϖm e d hd1 hde hϖ he
  haveI hprime : (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)).IsPrime := RingHom.ker_isPrime _
  have hkerA : RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde) = branchIdeal ϖ e d := hker
  refine ⟨⟨RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde), hprime⟩, ?_⟩
  simp only

  have hsurjA : Function.Surjective (pointAlgHom ϖ hϖm e d hd1 hde) := pointHom_surjective ϖ hϖm e d hd1 hde
  let eqv : (UVCrossingModel W (ϖ ^ e) ⧸ RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)) ≃ₐ[W] W :=
    Ideal.quotientKerAlgEquivOfSurjective hsurjA
  have heqv : ∀ x : UVCrossingModel W (ϖ ^ e),
      eqv (Ideal.Quotient.mk (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)) x) = pointHom ϖ hϖm e d hd1 hde x :=
    fun x => by
      simp only [eqv, Ideal.quotientKerAlgEquivOfSurjective_mk, pointAlgHom_apply]

  have hUV : U (ϖ ^ e) * V (ϖ ^ e) = const (ϖ ^ e) (ϖ ^ e) := UVCrossingModel.U_mul_V (ϖ ^ e)
  have hrel : (U (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ (e - d))) * const (ϖ ^ e) (ϖ ^ d) =
      -(U (ϖ ^ e) * (V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d))) := by
    have hc : const (ϖ ^ e) (ϖ ^ (e - d)) * const (ϖ ^ e) (ϖ ^ d) = const (ϖ ^ e) (ϖ ^ e) := by
      rw [← constHom_apply, ← constHom_apply, ← constHom_apply, ← map_mul, ← pow_add, Nat.sub_add_cancel (by omega)]
    linear_combination hUV - hc

  have hle : ∀ P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)), const (ϖ ^ e) ϖ ∉ P.asIdeal →
      V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ∈ P.asIdeal → branchIdeal ϖ e d ≤ P.asIdeal := by
    intro P hPϖ hPV
    rw [branchIdeal, Ideal.span_le]
    intro y hy
    rcases hy with rfl | hy
    · have hmemP : (U (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ (e - d))) * const (ϖ ^ e) (ϖ ^ d) ∈ P.asIdeal := by
        rw [hrel]; exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hPV)
      rcases P.2.mem_or_mem hmemP with h | h
      · exact h
      · exfalso
        apply hPϖ
        rw [← constHom_apply, map_pow] at h
        rw [← constHom_apply]
        exact P.2.mem_of_pow_mem _ h
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hPV
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hbot
    have hmem : V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ∈ RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde) := by
      rw [hkerA]; exact V_sub_mem_branchIdeal ϖ e d
    rw [hbot, Ideal.mem_bot, sub_eq_zero] at hmem
    obtain ⟨ε, -, hεV, hεc⟩ := UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries (ϖ ^ e)
    have h1 := hεc (ϖ ^ d)
    rw [← hmem, hεV] at h1
    have h2 := congrArg (PowerSeries.coeff 0) h1
    rw [map_zero, PowerSeries.coeff_zero_C] at h2
    have h3 : (ϖ ^ e) ∣ ϖ ^ d := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h2.symm)
    have := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp h3
    omega
  ·
    rw [RingHom.mem_ker, pointAlgHom_apply, pointHom_const]
    exact hϖ.ne_zero
  · rw [hkerA]; exact V_sub_mem_branchIdeal ϖ e d
  · rw [hkerA]; exact U_sub_mem_branchIdeal ϖ e d
  ·
    intro P hPϖ hPV
    apply PrimeSpectrum.ext
    show P.asIdeal = RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)
    rw [hkerA]
    refine le_antisymm ?_ (hle P hPϖ hPV)
    intro x hx
    have hxc : x - const (ϖ ^ e) (pointHom ϖ hϖm e d hd1 hde x) ∈ branchIdeal ϖ e d := by
      rw [← hker, RingHom.mem_ker, map_sub, pointHom_const, sub_self]
    have hc : const (ϖ ^ e) (pointHom ϖ hϖm e d hd1 hde x) ∈ P.asIdeal := by
      have := P.asIdeal.sub_mem hx (hle P hPϖ hPV hxc)
      rwa [sub_sub_cancel] at this
    have hzero : pointHom ϖ hϖm e d hd1 hde x = 0 := by
      by_contra hne
      obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
      apply hPϖ
      rw [hu, ← constHom_apply, map_mul, map_pow] at hc
      have := (Ideal.unit_mul_mem_iff_mem _ ((u.isUnit).map (constHom (ϖ ^ e)))).mp hc
      rw [← constHom_apply]
      exact P.2.mem_of_pow_mem _ this
    rw [hzero, ← constHom_apply, map_zero, sub_zero] at hxc
    exact hxc
  · exact Module.Free.of_equiv eqv.symm.toLinearEquiv
  · exact Module.Finite.equiv eqv.symm.toLinearEquiv
  · rw [LinearEquiv.finrank_eq eqv.toLinearEquiv, Module.finrank_self]
  · rw [← Algebra.norm_eq_of_algEquiv eqv, heqv, Algebra.norm_self, MonoidHom.id_apply]
    exact pointHom_V ϖ hϖm e d hd1 hde
  ·
    rw [length_localizedModule_quotient_span_singleton]
    have hβQ : const (ϖ ^ e) (ϖ ^ d) ∉ RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde) := by
      rw [RingHom.mem_ker, pointAlgHom_apply, pointHom_const]
      exact pow_ne_zero _ hϖ.ne_zero
    have hunit : IsUnit (algebraMap (UVCrossingModel W (ϖ ^ e))
        (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) (const (ϖ ^ e) (ϖ ^ d))) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ _ _).mpr hβQ
    have hspan : Ideal.span {algebraMap (UVCrossingModel W (ϖ ^ e))
          (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) (V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d))} =
        maximalIdeal (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal,
        congrArg (Ideal.map (algebraMap (UVCrossingModel W (ϖ ^ e))
          (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))))) hkerA,
        branchIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, Ideal.span_insert]
      symm
      apply sup_eq_right.mpr
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      obtain ⟨w, hw⟩ := hunit
      refine ⟨-(algebraMap (UVCrossingModel W (ϖ ^ e)) (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) (U (ϖ ^ e))) * ((w⁻¹ : (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))ˣ) : (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))), ?_⟩
      have h := congrArg (algebraMap (UVCrossingModel W (ϖ ^ e)) (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))) hrel
      rw [map_mul, map_neg, map_mul, ← hw] at h
      calc -(algebraMap (UVCrossingModel W (ϖ ^ e)) (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) (U (ϖ ^ e))) * ((w⁻¹ : (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))ˣ) : (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))) * algebraMap (UVCrossingModel W (ϖ ^ e)) (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) (V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d))
          = -(algebraMap (UVCrossingModel W (ϖ ^ e)) (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) (U (ϖ ^ e)) * algebraMap (UVCrossingModel W (ϖ ^ e)) (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) (V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d))) * ((w⁻¹ : (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))ˣ) : (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))) := by ring
        _ = algebraMap (UVCrossingModel W (ϖ ^ e)) (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) (U (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ (e - d))) * (w : (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))) * ((w⁻¹ : (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))ˣ) : (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde)))) := by rw [← h]
        _ = algebraMap (UVCrossingModel W (ϖ ^ e)) (Localization.AtPrime (RingHom.ker (pointAlgHom ϖ hϖm e d hd1 hde))) (U (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ (e - d))) := by rw [mul_assoc, Units.mul_inv, mul_one]
    rw [hspan, Module.length_eq_one_iff]
    exact isSimpleModule_iff_isCoatom.mpr (maximalIdeal.isMaximal _).out

end S_ModularCurve_UVCrossingModel_exists_prime_V_sub_const_pow_mem
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_prime_V_sub_const_pow_mem (solution)
