-- Prove2me | solution 1 for ModularCurve.XOneP.comap_eq_of_map_j_eq_of_map_jp_eq_valuationSubring_pair_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/36a3066b-cfd1-5bd0-ad86-ec5bda7231e7

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_comap_eq_of_map_j_eq_of_map_jp_eq_valuationSubring_pair_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

namespace TWISTReduce

open ModularCurve

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

section Main

open HahnSeries Polynomial

variable {L : Type} [Field L] {K : IntermediateField L (LaurentSeries L)}
variable {A : Type} [CommRing A] [Algebra A L] [Algebra A ↥K] [IsScalarTower A L ↥K]
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

end Main

end TWISTReduce
p2m_reactivate "P2MW.S_ModularCurve_XOneP_comap_eq_of_map_j_eq_of_map_jp_eq_valuationSubring_pair_x1_mul.TWISTReduce"

open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 6400000 in

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
    (jp : ↥K) (hjp : ((jp : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (W₀ W₁ : ValuationSubring ↥K)

    (h1 : ∀ i : Fin 2, (∀ a : A, algebraMap A ↥K a ∈ (![W₀, W₁] i)) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ (![W₀, W₁] i).nonunits)

    (h2 : ∀ i : Fin 2, ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval j P)⁻¹ ∈ (![W₀, W₁] i))

    (h3 : W₀ ≠ W₁)

    (h4 : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (h5 : ∀ V : ValuationSubring ↥K,
      (∀ a : A, algebraMap A ↥K a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁)
    (g : ↥K ≃ₐ[L] ↥K) (hgj : g j = j) (hgjp : g jp = jp) :
    W₀.comap (g : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₀ ∧
    W₁.comap (g : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₁ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hW : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, TWISTReduce.Pres L (f : LaurentSeries L) x y := h4

  have hcommA : ∀ (φ : ↥K ≃ₐ[L] ↥K) (a : A), φ (algebraMap A ↥K a) = algebraMap A ↥K a := fun φ a => by
    rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  have haeval : ∀ (φ : ↥K ≃ₐ[L] ↥K) (P : Polynomial A), φ (Polynomial.aeval j P) = Polynomial.aeval (φ j) P := by
    intro φ P
    have := Polynomial.aeval_algHom_apply ((φ : ↥K ≃ₐ[L] ↥K).toAlgHom.restrictScalars A) j P
    simpa using this.symm

  have hnu : ∀ (B : ValuationSubring ↥K) (x : ↥K), x ∈ B.nonunits ↔ x ∈ B ∧ (x = 0 ∨ x⁻¹ ∉ B) := by
    intro B x
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    constructor
    · rintro ⟨hx, hm⟩
      refine ⟨hx, ?_⟩
      by_cases h0 : x = 0
      · exact Or.inl h0
      · right
        intro hinv
        apply (IsLocalRing.mem_maximalIdeal _).mp hm
        exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    · rintro ⟨hx, h⟩
      refine ⟨hx, (IsLocalRing.mem_maximalIdeal _).mpr ?_⟩
      intro hu
      rcases h with h0 | hinv
      · subst h0
        have hz : (⟨0, hx⟩ : B) = 0 := rfl
        rw [hz] at hu
        exact not_isUnit_zero hu
      · obtain ⟨u, hu⟩ := hu.exists_right_inv
        apply hinv
        have hux : ((u : B) : ↥K) = x⁻¹ := by
          have := congrArg Subtype.val hu
          simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
          have h0 : x ≠ 0 := fun e => by rw [e, zero_mul] at this; exact zero_ne_one this
          exact (eq_inv_of_mul_eq_one_right this)
        rw [← hux]; exact u.2

  have hmemc : ∀ (φ : ↥K ≃ₐ[L] ↥K) (B : ValuationSubring ↥K) (x : ↥K),
      x ∈ B.comap (φ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ↔ φ x ∈ B := fun φ B x => Iff.rfl
  have hnuc : ∀ (φ : ↥K ≃ₐ[L] ↥K) (B : ValuationSubring ↥K) (x : ↥K),
      x ∈ (B.comap (φ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom).nonunits ↔ φ x ∈ B.nonunits := by
    intro φ B x
    rw [hnu, hnu, hmemc, hmemc, map_inv₀, map_eq_zero_iff φ φ.injective]

  have hbranch : ∀ (φ : ↥K ≃ₐ[L] ↥K), φ j = j → ∀ i : Fin 2,
      (∀ a : A, algebraMap A ↥K a ∈ (![W₀, W₁] i).comap (φ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ ((![W₀, W₁] i).comap (φ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom).nonunits) ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ (![W₀, W₁] i).comap (φ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
        (Polynomial.aeval j P)⁻¹ ∈ (![W₀, W₁] i).comap (φ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) := by
    intro φ hφj i
    refine ⟨fun a => ?_, fun a ha => ?_, fun P hP => ?_⟩
    · rw [hmemc, hcommA]; exact (h1 i).1 a
    · rw [hnuc, hcommA]; exact (h1 i).2 a ha
    · rw [hmemc, hmemc, map_inv₀, haeval, hφj]; exact h2 i P hP
  have hcases : ∀ (φ : ↥K ≃ₐ[L] ↥K), φ j = j → ∀ i : Fin 2,
      (![W₀, W₁] i).comap (φ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₀ ∨
      (![W₀, W₁] i).comap (φ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₁ := by
    intro φ hφj i
    obtain ⟨ha, hm, hP⟩ := hbranch φ hφj i
    exact h5 _ ha hm hP

  obtain ⟨σ, hσj, -, hσW⟩ :=
    ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj
  obtain ⟨hσne, hσP⟩ := hσW W₀ h4
  have hσW₁ : W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₁ := by
    rcases h5 _ (fun a => by rw [hmemc, hcommA]; exact (h1 0).1 a)
        (fun a ha => by rw [hnuc, hcommA]; exact (h1 0).2 a ha) hσP with h | h
    · exact absurd h hσne
    · exact h

  have key : ∀ (φ : ↥K ≃ₐ[L] ↥K), φ j = j → φ jp = jp →
      W₀.comap (φ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₀ := by
    intro φ hφj hφjp
    rcases hcases φ hφj 0 with h | h
    · exact h
    exfalso

    let τ : ↥K ≃ₐ[L] ↥K := φ.symm.trans σ
    have hτ : ∀ x, τ x = σ (φ.symm x) := fun x => rfl
    have hσj' : σ j = jp := by
      apply Subtype.ext
      rw [hσj, hjp]
    have hτj : ((τ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) := by
      rw [hτ, show φ.symm j = j from (AlgEquiv.symm_apply_eq φ).mpr hφj.symm, hσj]
    have hτW : W₀.comap (τ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₀ := by
      ext x
      rw [hmemc, hτ]

      have e1 : σ (φ.symm x) ∈ W₀ ↔ φ.symm x ∈ W₁ := by rw [← hσW₁]; rfl
      have e2 : φ (φ.symm x) ∈ W₀ ↔ φ.symm x ∈ W₁ := by
        rw [← hmemc φ W₀ (φ.symm x)]
        change φ.symm x ∈ (![W₀, W₁] 0).comap _ ↔ _
        rw [h]
      rw [e1, ← e2, AlgEquiv.apply_symm_apply]
    exact TWISTReduce.comap_ne_self p hAp j hj τ hτj W₀ hW hτW
  refine ⟨key g hgj hgjp, ?_⟩

  rcases hcases g hgj 1 with h | h
  · exfalso
    have hg' : W₀.comap (g.symm : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₀ :=
      key g.symm ((AlgEquiv.symm_apply_eq g).mpr hgj.symm) ((AlgEquiv.symm_apply_eq g).mpr hgjp.symm)
    apply h3

    ext x
    have e1 : x ∈ W₀ ↔ g.symm x ∈ W₀ := by rw [← hmemc g.symm W₀ x, hg']
    have e2 : g.symm x ∈ (![W₀, W₁] 1).comap (g : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ↔ g (g.symm x) ∈ W₁ := hmemc g W₁ _
    rw [h] at e2
    rw [e1, e2, AlgEquiv.apply_symm_apply]
  · exact h

end S_ModularCurve_XOneP_comap_eq_of_map_j_eq_of_map_jp_eq_valuationSubring_pair_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_comap_eq_of_map_j_eq_of_map_jp_eq_valuationSubring_pair_x1_mul (solution)
