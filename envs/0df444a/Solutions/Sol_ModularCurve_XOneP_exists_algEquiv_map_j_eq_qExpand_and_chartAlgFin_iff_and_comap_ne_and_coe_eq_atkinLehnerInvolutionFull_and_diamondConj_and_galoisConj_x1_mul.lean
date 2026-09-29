-- Prove2me | solution 1 for ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3add80b0-4f5c-5748-8ea3-524290e04f4b

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.qExpandAlgHomC_apply ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"

set_option autoImplicit false

namespace TWISTReduce

open ModularCurve

theorem order_jqModC (κ : Type) [Field κ] : (jqModC κ).order = -1 := by
  have hu : (HahnSeries.ofPowerSeries ℤ κ (jNum.map (Int.castRingHom κ))) ≠ 0 := by
    intro h
    have := congrArg (fun x : LaurentSeries κ => x.coeff 0) h
    simp only [HahnSeries.coeff_zero] at this
    rw [show (0:ℤ) = ((0:ℕ):ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum] at this
    simp at this
  have hu0 : (HahnSeries.ofPowerSeries ℤ κ (jNum.map (Int.castRingHom κ))).order = 0 := by
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      rw [show (0:ℤ) = ((0:ℕ):ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum]
      simp
    · rw [HahnSeries.le_order_iff_forall hu]
      intro k hk
      exact ModularCurve.ofPowerSeries_coeff_of_neg _ hk
  rw [jqModC, HahnSeries.order_mul (by simp) hu, hu0, HahnSeries.order_single one_ne_zero, add_zero]

theorem jqModC_ne_zero' (κ : Type) [Field κ] : jqModC κ ≠ 0 := by
  intro h
  have := order_jqModC κ
  rw [h, HahnSeries.order_zero] at this
  norm_num at this

theorem pow_ne_jqModC (κ : Type) [Field κ] (n : ℕ) (hn : 2 ≤ n) (G : LaurentSeries κ) :
    G ^ n ≠ jqModC κ := by
  intro h
  have hG : G ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at h
    exact jqModC_ne_zero' κ h.symm
  have h1 := congrArg HahnSeries.order h
  rw [HahnSeries.order_pow, order_jqModC, nsmul_eq_mul] at h1
  have h2 : (n : ℤ) ∣ 1 := ⟨-G.order, by linarith⟩
  have h3 : (n : ℤ) ≤ 1 := Int.le_of_dvd one_pos h2
  omega

open HahnSeries

section Pres

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]

noncomputable abbrev toL (L : Type) [Field L] [Algebra A L] (x : PowerSeries A) : LaurentSeries L :=
  ofPowerSeries ℤ L (x.map (algebraMap A L))

noncomputable abbrev toκ (x : PowerSeries A) : LaurentSeries (IsLocalRing.ResidueField A) :=
  ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A))

variable (L) in

def Pres (f : LaurentSeries L) (x y : PowerSeries A) : Prop :=
  y.map (IsLocalRing.residue A) ≠ 0 ∧ f * toL L y = toL L x

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_mul (x y : PowerSeries A) : toL L (x * y) = toL L x * toL L y := by simp [toL, map_mul]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_sub (x y : PowerSeries A) : toL L (x - y) = toL L x - toL L y := by simp [toL, map_sub]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_one : toL L (1 : PowerSeries A) = 1 := by simp [toL]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_zero : toL L (0 : PowerSeries A) = 0 := by simp [toL]
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in
@[scoped simp] theorem toL_pow (x : PowerSeries A) (n : ℕ) : toL L (x ^ n) = toL L x ^ n := by simp [toL, map_pow]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_mul (x y : PowerSeries A) : toκ (x * y) = toκ x * toκ y := by simp [toκ, map_mul]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_sub (x y : PowerSeries A) : toκ (x - y) = toκ x - toκ y := by simp [toκ, map_sub]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_pow (x : PowerSeries A) (n : ℕ) : toκ (x ^ n) = toκ x ^ n := by simp [toκ, map_pow]
omit [IsFractionRing A L] in
@[scoped simp] theorem toκ_zero : toκ (0 : PowerSeries A) = 0 := by simp [toκ]
omit [IsFractionRing A L] in
theorem toκ_eq_zero_iff (x : PowerSeries A) : toκ x = 0 ↔ x.map (IsLocalRing.residue A) = 0 := by
  constructor
  · intro e; exact ofPowerSeries_injective (e.trans (map_zero _).symm)
  · intro e; rw [toκ, e, map_zero]

omit [IsDomain A] [IsDiscreteValuationRing A] in
theorem toL_injective : Function.Injective (toL (A := A) L) := fun x y h =>
  PowerSeries.map_injective (algebraMap A L) (IsFractionRing.injective A L) (ofPowerSeries_injective h)

theorem Pres.mul {f g : LaurentSeries L} {x y x' y' : PowerSeries A}
    (hf : Pres L f x y) (hg : Pres L g x' y') : Pres L (f * g) (x * x') (y * y') := by
  refine ⟨by rw [map_mul]; exact mul_ne_zero hf.1 hg.1, ?_⟩
  rw [toL_mul, toL_mul, ← hf.2, ← hg.2]; ring

theorem Pres.pow {f : LaurentSeries L} {x y : PowerSeries A} (hf : Pres L f x y) (n : ℕ) :
    Pres L (f ^ n) (x ^ n) (y ^ n) := by
  induction n with
  | zero => exact ⟨by simp, by simp⟩
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem Pres.sub {f g : LaurentSeries L} {x y x' y' : PowerSeries A}
    (hf : Pres L f x y) (hg : Pres L g x' y') : Pres L (f - g) (x * y' - x' * y) (y * y') := by
  refine ⟨by rw [map_mul]; exact mul_ne_zero hf.1 hg.1, ?_⟩
  rw [toL_mul, toL_sub, toL_mul, toL_mul, ← hf.2, ← hg.2]; ring

omit [IsFractionRing A L] in
theorem Pres.one : Pres L (1 : LaurentSeries L) (1 : PowerSeries A) 1 :=
  ⟨by simp, by simp⟩

theorem Pres.unique {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (h' : Pres L f x' y') :
    x.map (IsLocalRing.residue A) * y'.map (IsLocalRing.residue A)
      = x'.map (IsLocalRing.residue A) * y.map (IsLocalRing.residue A) := by
  have : toL L (x * y') = toL L (x' * y) := by
    rw [toL_mul, toL_mul, ← h.2, ← h'.2]; ring
  have := toL_injective this
  rw [← map_mul, ← map_mul, this]

theorem Pres.ne_zero {f : LaurentSeries L} {x y : PowerSeries A} (h : Pres L f x y)
    (hx : x.map (IsLocalRing.residue A) ≠ 0) : f ≠ 0 := by
  rintro rfl
  have h2 := h.2
  rw [zero_mul, eq_comm] at h2
  have : x = 0 := toL_injective (L := L) (h2.trans (toL_zero (L := L)).symm)
  exact hx (by simp [this])

theorem Pres.inv {f : LaurentSeries L} {x y : PowerSeries A} (h : Pres L f x y)
    (hx : x.map (IsLocalRing.residue A) ≠ 0) : Pres L f⁻¹ y x := by
  refine ⟨hx, ?_⟩
  have hf := h.ne_zero hx
  rw [← h.2, ← mul_assoc, inv_mul_cancel₀ hf, one_mul]

theorem Pres.map_ne_zero_of_inv {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (hf : f ≠ 0) (h' : Pres L f⁻¹ x' y') :
    x.map (IsLocalRing.residue A) ≠ 0 := by
  have hp := h.mul h'
  rw [mul_inv_cancel₀ hf] at hp
  have hu := hp.unique Pres.one
  simp only [map_mul, map_one, mul_one, one_mul] at hu
  intro hx0
  rw [hx0, zero_mul] at hu
  exact mul_ne_zero h.1 h'.1 hu.symm

theorem Pres.red_eq {f : LaurentSeries L} {x y x' y' : PowerSeries A}
    (h : Pres L f x y) (h' : Pres L f x' y') :
    toκ x / toκ y = toκ x' / toκ y' := by
  have hy : toκ y ≠ 0 := fun e => h.1 ((toκ_eq_zero_iff y).mp e)
  have hy' : toκ y' ≠ 0 := fun e => h'.1 ((toκ_eq_zero_iff y').mp e)
  have e := congrArg (ofPowerSeries ℤ (IsLocalRing.ResidueField A)) (h.unique h')
  rw [map_mul, map_mul] at e
  rw [div_eq_div_iff hy hy']
  exact e

end Pres

open HahnSeries Polynomial

section LeadingTerm

variable {κ : Type} [Field κ]

theorem order_add_of_order_lt {a b : LaurentSeries κ} (ha : a ≠ 0) (hab : b = 0 ∨ a.order < b.order) :
    (a + b) ≠ 0 ∧ (a + b).order = a.order := by
  rcases hab with rfl | hab
  · simpa using ha
  have hcoeff : (a + b).coeff a.order = a.coeff a.order := by
    rw [HahnSeries.coeff_add', Pi.add_apply, HahnSeries.coeff_eq_zero_of_lt_order hab, add_zero]
  have hne : (a + b).coeff a.order ≠ 0 := by rw [hcoeff]; exact fun h => ha (coeff_order_eq_zero.mp h)
  have hab0 : a + b ≠ 0 := fun h => by rw [h] at hne; exact hne rfl
  refine ⟨hab0, le_antisymm (order_le_of_coeff_ne_zero hne) ?_⟩
  rw [le_order_iff_forall hab0]
  intro k hk
  rw [HahnSeries.coeff_add', Pi.add_apply, coeff_eq_zero_of_lt_order hk,
    coeff_eq_zero_of_lt_order (hk.trans hab), add_zero]

theorem aeval_ne_zero_and_order_of_order_neg (u : LaurentSeries κ) (hu : u ≠ 0) (hord : u.order < 0) :
    ∀ Q : κ[X], Q ≠ 0 → aeval u Q ≠ 0 ∧ (aeval u Q).order = Q.natDegree * u.order := by
  intro Q
  induction Q using Polynomial.recOnHorner with
  | M0 => intro h; exact (h rfl).elim
  | MC p a hp0 ha ih =>

    intro _
    have hCa : aeval u (C a) = single 0 a := by
      rw [Polynomial.aeval_C, ModularCurve.algebraMap_laurentSeries_eq_single]
    have hCa0 : aeval u (C a) ≠ 0 := by rw [hCa]; exact single_ne_zero ha
    have hCaord : (aeval u (C a)).order = 0 := by rw [hCa]; exact order_single ha
    by_cases hp : p = 0
    · subst hp
      refine ⟨by simpa using hCa0, ?_⟩
      rw [zero_add, hCaord, natDegree_C]; simp
    · obtain ⟨hne, hordp⟩ := ih hp
      have hdeg : 0 < p.natDegree := by
        rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
        · exfalso; apply hp
          rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hp0, map_zero]
        · exact h0
      have hlt : (aeval u p).order < (aeval u (C a)).order := by
        rw [hordp, hCaord]
        have : (p.natDegree : ℤ) * u.order ≤ 1 * u.order :=
          Int.mul_le_mul_of_nonpos_right (by exact_mod_cast hdeg) hord.le
        linarith
      obtain ⟨h1, h2⟩ := order_add_of_order_lt hne (Or.inr hlt)
      refine ⟨by rwa [map_add], ?_⟩
      rw [map_add, h2, hordp]
      congr 2
      rw [natDegree_add_C]
  | MX p hp ih =>
    intro _
    obtain ⟨hne, hordp⟩ := ih hp
    refine ⟨?_, ?_⟩
    · rw [map_mul, aeval_X]; exact mul_ne_zero hne hu
    · rw [map_mul, aeval_X, order_mul hne hu, hordp, Polynomial.natDegree_mul_X hp]; push_cast; ring

end LeadingTerm

open HahnSeries Polynomial

section PresPoly

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]

omit [IsDomain A] [IsDiscreteValuationRing A] in
theorem C_powerSeries_injective : Function.Injective (PowerSeries.C (R := A)) :=
  Function.LeftInverse.injective (g := PowerSeries.constantCoeff) fun a => PowerSeries.constantCoeff_C a

private noncomputable def _root_.TWISTReduce.presNum (P : A[X]) (x y : PowerSeries A) : PowerSeries A :=
  ((P.map (PowerSeries.C (R := A))).scaleRoots y).eval x

p2m_export "TWISTReduce" "presNum"
omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L] in

theorem toL_presNum (P : A[X]) {f : LaurentSeries L} {x y : PowerSeries A} (hf : f * toL L y = toL L x) :
    toL L (presNum P x y) = toL L y ^ P.natDegree *
      P.eval₂ ((algebraMap L (LaurentSeries L)).comp (algebraMap A L)) f := by
  set ψ : PowerSeries A →+* LaurentSeries L := (ofPowerSeries ℤ L).comp (PowerSeries.map (algebraMap A L))
  have hψ : ∀ z, toL L z = ψ z := fun z => rfl
  have hdeg : (P.map (PowerSeries.C (R := A))).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective C_powerSeries_injective P
  have hcomp : ψ.comp (PowerSeries.C (R := A)) = (algebraMap L (LaurentSeries L)).comp (algebraMap A L) := by
    ext a
    simp [ψ, ModularCurve.algebraMap_laurentSeries_eq_single]
  rw [hψ, hψ, presNum, ← eval₂_at_apply, show ψ x = ψ y * f by rw [← hψ, ← hψ, ← hf, mul_comm],
    scaleRoots_eval₂_mul, hdeg, eval₂_map, hcomp]

theorem Pres.presNum {f : LaurentSeries L} {x y : PowerSeries A} (h : Pres L f x y) (P : A[X]) :
    Pres L (P.eval₂ ((algebraMap L (LaurentSeries L)).comp (algebraMap A L)) f) (presNum P x y) (y ^ P.natDegree) := by
  refine ⟨by rw [map_pow]; exact pow_ne_zero _ h.1, ?_⟩
  rw [toL_presNum P h.2]
  simp only [toL, map_pow]
  ring

omit [IsFractionRing A L] in

theorem toκ_presNum (P : A[X]) (x y : PowerSeries A) (hy : y.map (IsLocalRing.residue A) ≠ 0) :
    toκ (presNum P x y) = toκ y ^ P.natDegree *
      aeval (toκ x / toκ y) (P.map (IsLocalRing.residue A)) := by
  set ψ : PowerSeries A →+* LaurentSeries (IsLocalRing.ResidueField A) :=
    (ofPowerSeries ℤ _).comp (PowerSeries.map (IsLocalRing.residue A))
  have hψ : ∀ z, toκ z = ψ z := fun z => rfl
  have hy' : ψ y ≠ 0 := by
    rw [← hψ]; intro e; exact hy (ofPowerSeries_injective (e.trans (map_zero _).symm))
  have hdeg : (P.map (PowerSeries.C (R := A))).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective C_powerSeries_injective P
  have hcomp : ψ.comp (PowerSeries.C (R := A)) =
      (algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))).comp
        (IsLocalRing.residue A) := by
    ext a
    simp [ψ, ModularCurve.algebraMap_laurentSeries_eq_single]
  rw [hψ, hψ, hψ, presNum, ← eval₂_at_apply]
  have e : ψ x = ψ y * (ψ x / ψ y) := by rw [mul_div_cancel₀ _ hy']
  conv_lhs => rw [e]
  rw [scaleRoots_eval₂_mul, hdeg, eval₂_map, hcomp, aeval_def, eval₂_map]

end PresPoly

open Polynomial

section Chart

variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]

theorem isIntegral_adjoin_map (τ : K →ₐ[A] K) (t b : K)
    (hb : IsIntegral (Algebra.adjoin A ({t} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({τ t} : Set K)) (τ b) := by
  have hmap : (Algebra.adjoin A ({t} : Set K)).map τ = Algebra.adjoin A {τ t} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
  let φ : Algebra.adjoin A ({t} : Set K) →+* Algebra.adjoin A ({τ t} : Set K) :=
    { toFun := fun s => ⟨τ s, by rw [← hmap]; exact Subalgebra.mem_map.mpr ⟨s, s.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  exact hb.map_of_comp_eq φ τ.toRingHom (by ext s; rfl)

theorem isIntegral_trans_subalgebra (S : Subalgebra A K) (b : K) (hb : IsIntegral (integralClosure S K) b) :
    IsIntegral S b := by
  haveI : IsScalarTower S (integralClosure S K) K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact isIntegral_trans b hb

theorem isIntegral_adjoin_of_isIntegral_adjoin {t t' b : K}
    (ht' : IsIntegral (Algebra.adjoin A ({t} : Set K)) t')
    (hb : IsIntegral (Algebra.adjoin A ({t'} : Set K)) b) :
    IsIntegral (Algebra.adjoin A ({t} : Set K)) b := by
  exact isIntegral_trans_subalgebra (Algebra.adjoin A ({t} : Set K)) b
    (by
      have hle : Algebra.adjoin A ({t'} : Set K) ≤
          (integralClosure (Algebra.adjoin A ({t} : Set K)) K).restrictScalars A := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        exact ht'
      have hle' : (Algebra.adjoin A ({t'} : Set K)).toSubring ≤
          (integralClosure (Algebra.adjoin A ({t} : Set K)) K).toSubring := fun x hx => hle hx
      exact hb.map_of_comp_eq (Subring.inclusion hle') (RingHom.id K) (by ext; rfl))

theorem chartAlg_singleton_eq_of_isIntegral {t t' : K}
    (h1 : IsIntegral (Algebra.adjoin A ({t} : Set K)) t') (h2 : IsIntegral (Algebra.adjoin A ({t'} : Set K)) t) :
    AlgebraicCurve.TwoChartIntegralModel.chartAlg A K {t} = AlgebraicCurve.TwoChartIntegralModel.chartAlg A K {t'} := by
  ext b
  rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
  exact ⟨isIntegral_adjoin_of_isIntegral_adjoin h2, isIntegral_adjoin_of_isIntegral_adjoin h1⟩

end Chart

section ModEq

variable {L : Type} [Field L] [CharZero L]

theorem exists_monic_eval₂_coeffEmb (p : ℕ) [Fact p.Prime] [NeZero p] :
    ∃ Φ : Polynomial (Polynomial ℤ), Φ.Monic ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L ModularCurve.jq)).toRingHom
        (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq)) = 0 ∧
      Φ.eval₂ (aeval (ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))).toRingHom
        (ModularCurve.coeffEmb L ModularCurve.jq) = 0 := by
  obtain ⟨data, hsymm⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p
  have h0 : data.Φ.eval₂ (aeval ModularCurve.jq).toRingHom (ModularCurve.qExpand ℚ p ModularCurve.jq) = 0 := by
    have := data.eval_eq_zero
    rwa [ModularCurve.evalAtJ_def] at this
  have h1 : data.Φ.eval₂ (aeval (ModularCurve.qExpand ℚ p ModularCurve.jq)).toRingHom ModularCurve.jq = 0 := by
    rw [← hsymm]; exact h0
  have key : ∀ x y : LaurentSeries ℚ,
      (ModularCurve.coeffEmb L) (data.Φ.eval₂ (aeval x).toRingHom y)
        = data.Φ.eval₂ (aeval (ModularCurve.coeffEmb L x)).toRingHom (ModularCurve.coeffEmb L y) := by
    intro x y
    rw [hom_eval₂]
    congr 1
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp
    · simp
  refine ⟨data.Φ, data.monic, ?_, ?_⟩
  · rw [← key, h0, map_zero]
  · rw [← key, h1, map_zero]

end ModEq

section Main

open HahnSeries Polynomial

variable {L : Type} [Field L] {K : IntermediateField L (LaurentSeries L)}
variable {A : Type} [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]

omit [Algebra A L] [IsScalarTower A L ↥K] in
theorem coe_aeval' (s : ↥K) (P : A[X]) :
    ((aeval s P : ↥K) : LaurentSeries L) =
      P.eval₂ ((algebraMap ↥K (LaurentSeries L)).comp (algebraMap A ↥K)) (s : LaurentSeries L) := by
  show algebraMap ↥K (LaurentSeries L) (aeval s P) = _
  rw [aeval_def, hom_eval₂]
  rfl

theorem algebraMap_comp_eq :
    (algebraMap ↥K (LaurentSeries L)).comp (algebraMap A ↥K) = (algebraMap L (LaurentSeries L)).comp (algebraMap A L) := by
  refine RingHom.ext fun a => ?_
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [IsScalarTower.algebraMap_apply A L ↥K a, ← IsScalarTower.algebraMap_apply L ↥K (LaurentSeries L)]

theorem coe_aeval (s : ↥K) (P : A[X]) :
    ((aeval s P : ↥K) : LaurentSeries L) = P.eval₂ ((algebraMap L (LaurentSeries L)).comp (algebraMap A L)) (s : LaurentSeries L) := by
  rw [coe_aeval', algebraMap_comp_eq]

omit [Algebra A L] [IsScalarTower A L ↥K] in

theorem isIntegral_adjoin_of_eval₂_coe (a b : ↥K) (Φ : Polynomial (Polynomial ℤ)) (hm : Φ.Monic)
    (h : Φ.eval₂ (aeval (a : LaurentSeries L)).toRingHom (b : LaurentSeries L) = 0) :
    IsIntegral (Algebra.adjoin A ({a} : Set ↥K)) b := by
  let a' : Algebra.adjoin A ({a} : Set ↥K) := ⟨a, Algebra.self_mem_adjoin_singleton A a⟩
  let θ : Polynomial ℤ →+* Algebra.adjoin A ({a} : Set ↥K) := (aeval a').toRingHom
  refine ⟨Φ.map θ, hm.map θ, ?_⟩
  rw [eval₂_map]
  apply (algebraMap ↥K (LaurentSeries L)).injective
  rw [hom_eval₂, map_zero]
  convert h using 2 <;> first | (with_reducible_and_instances rfl) | rfl | skip
  refine Polynomial.ringHom_ext (fun n => by simp) ?_
  simp [θ, a']

omit [Algebra A L] [IsScalarTower A L ↥K] in
theorem isIntegral_adjoin_map_of_eq (τ : ↥K →ₐ[A] ↥K) (t t₀ b : ↥K) (ht : τ t = t₀)
    (hb : IsIntegral (Algebra.adjoin A ({t} : Set ↥K)) b) :
    IsIntegral (Algebra.adjoin A ({t₀} : Set ↥K)) (τ b) := by
  subst ht; exact isIntegral_adjoin_map τ t b hb

variable [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A L]

theorem comap_ne_self (p : ℕ) [Fact p.Prime] [NeZero p] [CharZero L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσ : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (W₀ : ValuationSubring ↥K) (hW : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, Pres L (f : LaurentSeries L) x y) :
    W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ := by
  classical
  intro hEq
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨⟨x₀, y₀, hy₀, hj₀, hr₀⟩, ⟨x₁, y₁, hy₁, hj₁, hr₁⟩⟩ :=
    ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand p L A hAp
  have Pj : Pres L (j : LaurentSeries L) x₀ y₀ := ⟨hy₀, by rw [hj]; exact hj₀⟩
  have Pσj : Pres L ((σ j : ↥K) : LaurentSeries L) x₁ y₁ := ⟨hy₁, by rw [hσ]; exact hj₁⟩
  have hy₀κ : toκ y₀ ≠ 0 := fun e => hy₀ ((toκ_eq_zero_iff y₀).mp e)
  have hy₁κ : toκ y₁ ≠ 0 := fun e => hy₁ ((toκ_eq_zero_iff y₁).mp e)
  have hx₀ : toκ x₀ = ModularCurve.jqModC _ * toκ y₀ := by rw [← hr₀, div_mul_cancel₀ _ hy₀κ]
  have hx₁ : toκ x₁ = ModularCurve.jqModC _ ^ p * toκ y₁ := by rw [← hr₁, div_mul_cancel₀ _ hy₁κ]
  have hmem : ∀ f : ↥K, σ f ∈ W₀ ↔ f ∈ W₀ := fun f => by
    have e := (ValuationSubring.mem_comap (A := W₀) (f := (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) (x := f))
    rw [hEq] at e
    exact e.symm
  have hjW : j ∈ W₀ := (hW j).mpr ⟨x₀, y₀, Pj⟩
  have hg : σ (σ.symm j) = j := σ.apply_symm_apply j
  have hgW : σ.symm j ∈ W₀ := (hmem _).mp (by rw [hg]; exact hjW)
  obtain ⟨x₂, y₂, Pg⟩ := (hW _).mp hgW
  have hy₂κ : toκ y₂ ≠ 0 := fun e => Pg.1 ((toκ_eq_zero_iff y₂).mp e)

  have hσh : σ ((σ.symm j) ^ p - j) = j ^ p - σ j := by rw [map_sub, map_pow, hg]
  have Pσh : Pres L ((σ ((σ.symm j) ^ p - j) : ↥K) : LaurentSeries L) (x₀ ^ p * y₁ - x₁ * y₀ ^ p) (y₀ ^ p * y₁) := by
    rw [hσh]; push_cast; exact (Pj.pow p).sub Pσj
  have hX : (x₀ ^ p * y₁ - x₁ * y₀ ^ p).map (IsLocalRing.residue A) = 0 := by
    rw [← toκ_eq_zero_iff, toκ_sub, toκ_mul, toκ_mul, toκ_pow, toκ_pow, hx₀, hx₁]; ring
  have hnon : (σ.symm j) ^ p - j = 0 ∨ ((σ.symm j) ^ p - j)⁻¹ ∉ W₀ := by
    by_cases h0 : (σ.symm j) ^ p - j = 0
    · exact Or.inl h0
    right
    intro hinv
    have hσinv : (σ ((σ.symm j) ^ p - j))⁻¹ ∈ W₀ := by rw [← map_inv₀]; exact (hmem _).mpr hinv
    obtain ⟨x', y', P'⟩ := (hW _).mp hσinv
    have hσh0 : ((σ ((σ.symm j) ^ p - j) : ↥K) : LaurentSeries L) ≠ 0 := by
      intro e; apply h0
      have : σ ((σ.symm j) ^ p - j) = 0 := by exact_mod_cast e
      exact (map_eq_zero_iff σ σ.injective).mp this
    push_cast at P'
    exact Pσh.map_ne_zero_of_inv hσh0 P' hX
  have Ph : Pres L ((((σ.symm j) ^ p - j : ↥K)) : LaurentSeries L) (x₂ ^ p * y₀ - x₀ * y₂ ^ p) (y₂ ^ p * y₀) := by
    push_cast; exact (Pg.pow p).sub Pj
  have hX₂ : (x₂ ^ p * y₀ - x₀ * y₂ ^ p).map (IsLocalRing.residue A) = 0 := by
    rcases hnon with h0 | hinv
    · have e := Ph.2
      rw [h0, ZeroMemClass.coe_zero, zero_mul, eq_comm] at e
      have := toL_injective (L := L) (e.trans (toL_zero (L := L)).symm)
      rw [this, map_zero]
    · by_contra hne
      apply hinv
      exact (hW _).mpr ⟨y₂ ^ p * y₀, x₂ ^ p * y₀ - x₀ * y₂ ^ p, by push_cast; exact Ph.inv hne⟩
  have hG : (toκ x₂ / toκ y₂) ^ p = ModularCurve.jqModC (IsLocalRing.ResidueField A) := by
    have e : toκ (x₂ ^ p * y₀ - x₀ * y₂ ^ p) = 0 := by rw [toκ_eq_zero_iff]; exact hX₂
    rw [toκ_sub, toκ_mul, toκ_mul, toκ_pow, toκ_pow, hx₀] at e
    have e2 : (toκ x₂ ^ p - ModularCurve.jqModC _ * toκ y₂ ^ p) * toκ y₀ = 0 := by
      rw [← e]; ring
    rcases mul_eq_zero.mp e2 with e3 | e3
    · rw [div_pow, div_eq_iff (pow_ne_zero _ hy₂κ)]; exact sub_eq_zero.mp e3
    · exact absurd e3 hy₀κ
  exact pow_ne_jqModC _ p hp2 _ hG

theorem aeval_mem_and_inv_mem (p : ℕ) [Fact p.Prime] [NeZero p] [CharZero L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (j' : ↥K) (hσ : ((j' : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (W₀ : ValuationSubring ↥K) (hW : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, Pres L (f : LaurentSeries L) x y)
    (P : A[X]) (hP : P.map (IsLocalRing.residue A) ≠ 0) :
    aeval j' P ∈ W₀ ∧ (aeval j' P)⁻¹ ∈ W₀ := by
  classical
  obtain ⟨-, ⟨x₁, y₁, hy₁, hj₁, hr₁⟩⟩ :=
    ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand p L A hAp
  have Pσj : Pres L ((j' : ↥K) : LaurentSeries L) x₁ y₁ := ⟨hy₁, by rw [hσ]; exact hj₁⟩
  have hy₁κ : toκ y₁ ≠ 0 := fun e => hy₁ ((toκ_eq_zero_iff y₁).mp e)
  have PP : Pres L ((aeval j' P : ↥K) : LaurentSeries L) (presNum P x₁ y₁) (y₁ ^ P.natDegree) := by
    rw [coe_aeval]; exact Pσj.presNum P
  have hnum : (presNum P x₁ y₁).map (IsLocalRing.residue A) ≠ 0 := by
    intro e
    have e' : toκ (presNum P x₁ y₁) = 0 := by rw [toκ_eq_zero_iff]; exact e
    rw [toκ_presNum P x₁ y₁ hy₁, hr₁] at e'
    rcases mul_eq_zero.mp e' with e1 | e2
    · exact pow_ne_zero _ hy₁κ e1
    · have hu : (ModularCurve.jqModC (IsLocalRing.ResidueField A)) ^ p ≠ 0 :=
        pow_ne_zero _ (jqModC_ne_zero' _)
      have hord : ((ModularCurve.jqModC (IsLocalRing.ResidueField A)) ^ p).order < 0 := by
        rw [order_pow, order_jqModC, nsmul_eq_mul, mul_neg_one, Left.neg_neg_iff]
        exact_mod_cast (Fact.out : p.Prime).pos
      exact (aeval_ne_zero_and_order_of_order_neg _ hu hord _ hP).1 e2
  refine ⟨(hW _).mpr ⟨_, _, PP⟩, (hW _).mpr ⟨y₁ ^ P.natDegree, presNum P x₁ y₁, ?_⟩⟩
  push_cast; exact PP.inv hnum

end Main

end TWISTReduce
p2m_reactivate "P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul.TWISTReduce"

open TWISTReduce CategoryTheory CategoryTheory.Limits AlgebraicGeometry _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    [NeZero p] :
    ∃ σ : ↥K ≃ₐ[L] ↥K,

      ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) ∧

      (∀ b : ↥K, b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j ↔
        σ b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ∧

      (∀ W₀ : ValuationSubring ↥K,
        (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) →
        W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀ ∧
        (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
          (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom)) ∧

      (∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
        (hfK : ModularCurve.coeffEmb L (f : LaurentSeries ℚ) ∈ K),
        ((σ ⟨ModularCurve.coeffEmb L (f : LaurentSeries ℚ), hfK⟩ : ↥K) : LaurentSeries L) =
          ModularCurve.coeffEmb L ((ModularCurve.atkinLehnerInvolutionFull M p f :
            ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ)) ∧

      (∀ (d d' : ℕ), d.Coprime (M * p) → d'.Coprime (M * p) →
        ((d' : ZMod M) = (d : ZMod M)) → ((d' : ZMod p) * (d : ZMod p) = 1) →
        ∀ (θd θd' : ↥K ≃ₐ[L] ↥K),
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θd x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θd' x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          ∀ x : ↥K, ((σ (θd (σ.symm x)) : ↥K) : LaurentSeries L) = ((θd' x : ↥K) : LaurentSeries L)) ∧

      (∀ (s : L ≃ₐ[ℚ] L) (b : ℕ), b.Coprime p → s ζ = ζ ^ b →
        ∀ (b' : ℕ), b'.Coprime (M * p) → ((b' : ZMod M) = 1) → ((b' : ZMod p) = (b : ZMod p)) →
        ∀ (Ss : ↥K ≃+* ↥K),
          (∀ x : ↥K, ((Ss x : ↥K) : LaurentSeries L) =
            ModularCurve.coeffMap (s.toAlgHom.toRingHom) ((x : ↥K) : LaurentSeries L)) →
        ∀ (θb' : ↥K ≃ₐ[L] ↥K),
          (∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
          (x : LaurentSeries L) = (x' : LaurentSeries L) →
            ((θb' x : ↥K) : LaurentSeries L) =
              ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) b') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) →
          ∀ x : ↥K, ((Ss (σ (Ss.symm x)) : ↥K) : LaurentSeries L) = ((σ (θb' x) : ↥K) : LaurentSeries L)) := by
  classical
  obtain ⟨σ, hσ, h4, h5, h6⟩ :=
    ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul
      p M hpM L ζ hζ K hK j hj
  let σA : ↥K ≃ₐ[A] ↥K := σ.restrictScalars A

  obtain ⟨Φ, hΦm, hΦ1, hΦ2⟩ := exists_monic_eval₂_coeffEmb (L := L) p
  have hint1 : IsIntegral (Algebra.adjoin A ({j} : Set ↥K)) (σ j) :=
    isIntegral_adjoin_of_eval₂_coe j (σ j) Φ hΦm (by rw [hj, hσ]; exact hΦ1)
  have hint2 : IsIntegral (Algebra.adjoin A ({σ j} : Set ↥K)) j :=
    isIntegral_adjoin_of_eval₂_coe (σ j) j Φ hΦm (by rw [hj, hσ]; exact hΦ2)
  have hchart : AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j =
      AlgebraicCurve.TwoChartIntegralModel.chartAlg A (↥K) {σ j} :=
    chartAlg_singleton_eq_of_isIntegral hint1 hint2
  refine ⟨σ, hσ, fun b => ⟨fun hb => ?_, fun hb => ?_⟩, fun W₀ hW₀ => ⟨?_, fun P hP => ?_⟩, h4, h5, h6⟩
  · rw [hchart, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
    rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff] at hb
    exact isIntegral_adjoin_map σA.toAlgHom j b hb
  · rw [hchart, AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff] at hb
    rw [AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff]
    have := isIntegral_adjoin_map_of_eq σA.symm.toAlgHom (σ j) j (σ b) (σ.symm_apply_apply j) hb
    rwa [show σA.symm.toAlgHom (σ b) = b from σ.symm_apply_apply b] at this
  · exact comap_ne_self p hAp j hj σ hσ W₀ hW₀
  · have hσP : σ (aeval j P) = aeval (σ j) P :=
      (Polynomial.aeval_algHom_apply σA.toAlgHom j P).symm
    obtain ⟨h1, h2⟩ := aeval_mem_and_inv_mem p hAp (σ j) hσ W₀ hW₀ P hP
    refine ⟨ValuationSubring.mem_comap.mpr ?_, ValuationSubring.mem_comap.mpr ?_⟩
    · show σ (aeval j P) ∈ W₀
      rw [hσP]; exact h1
    · show σ (aeval j P)⁻¹ ∈ W₀
      rw [map_inv₀, hσP]; exact h2

#print axioms solution

end S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_and_diamondConj_and_galoisConj_x1_mul (solution)
