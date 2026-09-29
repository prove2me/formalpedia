-- Prove2me | solution 1 for ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b777293f-4ac3-552c-9871-de5202bd0364

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial
open scoped MatrixGroups

namespace ModularCurve p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC x1FunctionField jNum constantCoeff_jNum jq coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange mem_laurentBaseChange_iff" namespace GaussPresGamma end ModularCurve.GaussPresGamma
p2m_open_scoped "ModularCurve" in
theorem ModularCurve.GaussPresGamma.coeff_ofPowerSeries_neg {R : Type*} [Semiring R] (φ : PowerSeries R) {k : ℤ} (hk : k < 0) :
    (HahnSeries.ofPowerSeries ℤ R φ).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨n, hn⟩
  have : (n : ℤ) = k := hn
  omega

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC x1FunctionField jNum constantCoeff_jNum jq coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange mem_laurentBaseChange_iff"
namespace GaussPresGamma
p2m_open "ModularCurve"

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type*} [Field L] [Algebra A L] [IsFractionRing A L]

noncomputable def toLS (A L : Type*) [CommRing A] [Field L] [Algebra A L] : PowerSeries A →+* LaurentSeries L :=
  (HahnSeries.ofPowerSeries ℤ L).comp (PowerSeries.map (algebraMap A L))

noncomputable def red (A : Type*) [CommRing A] [IsLocalRing A] : PowerSeries A →+* PowerSeries (IsLocalRing.ResidueField A) :=
  PowerSeries.map (IsLocalRing.residue A)

theorem toLS_injective : Function.Injective (toLS A L) := by
  intro x y h
  have h1 : PowerSeries.map (algebraMap A L) x = PowerSeries.map (algebraMap A L) y :=
    HahnSeries.ofPowerSeries_injective h
  exact PowerSeries.map_injective (algebraMap A L) (IsFractionRing.injective A L) h1

@[scoped simp] theorem toLS_C (a : A) : toLS A L (PowerSeries.C a) = HahnSeries.C (algebraMap A L a) := by
  simp [toLS]

def IsPres (f : LaurentSeries L) (x y : PowerSeries A) : Prop := f * toLS A L y = toLS A L x

def HasPres (f : LaurentSeries L) : Prop := ∃ x y : PowerSeries A, y ≠ 0 ∧ IsPres f x y

theorem HasPres.add {f g : LaurentSeries L} (hf : HasPres (A := A) f) (hg : HasPres (A := A) g) :
    HasPres (A := A) (f + g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * y' + x' * y, y * y', mul_ne_zero hy hy', ?_⟩
  unfold IsPres at *
  rw [map_mul, map_add, map_mul, map_mul]
  calc (f + g) * (toLS A L y * toLS A L y')
        = (f * toLS A L y) * toLS A L y' + (g * toLS A L y') * toLS A L y := by ring
    _ = toLS A L x * toLS A L y' + toLS A L x' * toLS A L y := by rw [h, h']

theorem HasPres.mul {f g : LaurentSeries L} (hf : HasPres (A := A) f) (hg : HasPres (A := A) g) :
    HasPres (A := A) (f * g) := by
  obtain ⟨x, y, hy, h⟩ := hf
  obtain ⟨x', y', hy', h'⟩ := hg
  refine ⟨x * x', y * y', mul_ne_zero hy hy', ?_⟩
  unfold IsPres at *
  rw [map_mul, map_mul, show f * g * (toLS A L y * toLS A L y') = (f * toLS A L y) * (g * toLS A L y') by ring, h, h']

theorem HasPres.neg {f : LaurentSeries L} (hf : HasPres (A := A) f) : HasPres (A := A) (-f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  exact ⟨-x, y, hy, by unfold IsPres at *; rw [map_neg, neg_mul, h]⟩

theorem HasPres.inv {f : LaurentSeries L} (hf : HasPres (A := A) f) : HasPres (A := A) f⁻¹ := by
  obtain ⟨x, y, hy, h⟩ := hf
  by_cases hf0 : f = 0
  · exact ⟨0, 1, one_ne_zero, by unfold IsPres; rw [hf0, inv_zero, zero_mul, map_zero]⟩
  have hx : x ≠ 0 := by
    intro hx0
    unfold IsPres at h
    rw [hx0, map_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact hf0 h
    · exact hy (toLS_injective (by rw [h, map_zero]))
  refine ⟨y, x, hx, ?_⟩
  unfold IsPres at *
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hf0, one_mul]

theorem hasPres_algebraMap (c : L) : HasPres (A := A) (algebraMap L (LaurentSeries L) c) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A c
  have hb0 : algebraMap A L b ≠ 0 := fun h0 =>
    nonZeroDivisors.ne_zero hb ((IsFractionRing.injective A L) (by rw [h0, map_zero]))
  refine ⟨PowerSeries.C a, PowerSeries.C b, ?_, ?_⟩
  · intro h
    apply nonZeroDivisors.ne_zero hb
    have := congrArg PowerSeries.constantCoeff h
    simpa using this
  · unfold IsPres
    rw [toLS_C, toLS_C, LaurentSeries.algebraMap_apply, ← map_mul, ← hab, div_mul_cancel₀ _ hb0]

theorem red_ne_zero_mul {y y' : PowerSeries A} (hy : red A y ≠ 0) (hy' : red A y' ≠ 0) : red A (y * y') ≠ 0 := by
  rw [map_mul]; exact mul_ne_zero hy hy'

@[scoped simp] theorem red_C (a : A) : red A (PowerSeries.C a) = PowerSeries.C (IsLocalRing.residue A a) := by
  simp [red]

theorem red_one : red A 1 = 1 := map_one _

theorem red_X_pow (d : ℕ) : red A (PowerSeries.X ^ d) = PowerSeries.X ^ d := by
  rw [map_pow, red, PowerSeries.map_X]

theorem IsPres.cross {f : LaurentSeries L} {x y x' y' : PowerSeries A} (h : IsPres f x y) (h' : IsPres f x' y') :
    x * y' = x' * y := by
  apply toLS_injective (A := A) (L := L)
  unfold IsPres at h h'
  rw [map_mul, map_mul, ← h, ← h']
  ring

theorem exists_eq_C_pow_mul {ϖ : A} (hϖ : Irreducible ϖ) {z : PowerSeries A} (hz : z ≠ 0) :
    ∃ (n : ℕ) (z' : PowerSeries A), z = PowerSeries.C (ϖ ^ n) * z' ∧ red A z' ≠ 0 := by
  classical
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := hϖ.maximalIdeal_eq

  have hex : ∃ n : ℕ, ∃ k : ℕ, ¬ (ϖ ^ (n + 1) ∣ PowerSeries.coeff k z) := by
    obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k z ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hz (PowerSeries.ext (by simpa using hall))
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hk hϖ
    refine ⟨m, k, fun hd => ?_⟩
    rw [hu] at hd

    have h1 : ϖ ^ (m + 1) ∣ ϖ ^ m := Units.dvd_mul_left.mp hd
    have h2 : ϖ ^ m * ϖ ∣ ϖ ^ m * 1 := by rwa [mul_one, ← pow_succ]
    have hϖ0 : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ.ne_zero
    exact hϖ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hϖ0).mp h2))
  let n := Nat.find hex
  obtain ⟨k₀, hk₀⟩ : ∃ k, ¬ (ϖ ^ (n + 1) ∣ PowerSeries.coeff k z) := Nat.find_spec hex
  have hall : ∀ k, ϖ ^ n ∣ PowerSeries.coeff k z := by
    intro k
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero]; exact one_dvd _
    · have hmin := Nat.find_min hex (show n - 1 < n by omega)
      push Not at hmin
      have := hmin k
      rwa [show n - 1 + 1 = n by omega] at this
  choose c hc using hall
  refine ⟨n, PowerSeries.mk c, ?_, ?_⟩
  · ext k
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc k]
  · intro hred
    apply hk₀
    have hk : PowerSeries.coeff k₀ (red A (PowerSeries.mk c)) = 0 := by rw [hred, map_zero]
    rw [red, PowerSeries.coeff_map, PowerSeries.coeff_mk, IsLocalRing.residue_eq_zero_iff, hmax,
      Ideal.mem_span_singleton] at hk
    rw [hc k₀, pow_succ]
    exact mul_dvd_mul (dvd_refl _) hk

theorem exists_gauss_or_inv {f : LaurentSeries L} (hf : HasPres (A := A) f) :
    (∃ x y : PowerSeries A, red A y ≠ 0 ∧ IsPres f x y) ∨
      (∃ x y : PowerSeries A, red A y ≠ 0 ∧ IsPres f⁻¹ x y) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨x, y, hy, h⟩ := hf
  by_cases hx : x = 0
  · left
    refine ⟨0, 1, by rw [red_one]; exact one_ne_zero, ?_⟩
    have hf0 : f = 0 := by
      unfold IsPres at h
      rw [hx, map_zero, mul_eq_zero] at h
      exact h.resolve_right (fun h0 => hy (toLS_injective (by rw [h0, map_zero])))
    unfold IsPres; rw [hf0, zero_mul, map_zero]
  obtain ⟨a, x', hxe, hx'⟩ := exists_eq_C_pow_mul hϖ hx
  obtain ⟨b, y', hye, hy'⟩ := exists_eq_C_pow_mul hϖ hy
  have hϖL : ∀ m : ℕ, (toLS A L (PowerSeries.C (ϖ ^ m))) ≠ 0 := fun m h0 => by
    have h1 : PowerSeries.C (ϖ ^ m) = 0 := toLS_injective (A := A) (L := L) (h0.trans (map_zero _).symm)
    have h2 := congrArg PowerSeries.constantCoeff h1
    rw [PowerSeries.constantCoeff_C, map_zero] at h2
    exact pow_ne_zero m hϖ.ne_zero h2
  unfold IsPres at h
  rw [hxe, hye, map_mul, map_mul] at h

  rcases le_or_gt b a with hba | hab
  · left
    have hCab : toLS A L (PowerSeries.C (ϖ ^ a)) = toLS A L (PowerSeries.C (ϖ ^ b)) * toLS A L (PowerSeries.C (ϖ ^ (a - b))) := by
      rw [← map_mul, ← map_mul, ← pow_add, Nat.add_sub_cancel' hba]
    refine ⟨PowerSeries.C (ϖ ^ (a - b)) * x', y', hy', ?_⟩
    unfold IsPres
    apply mul_left_cancel₀ (hϖL b)
    calc toLS A L (PowerSeries.C (ϖ ^ b)) * (f * toLS A L y')
          = f * (toLS A L (PowerSeries.C (ϖ ^ b)) * toLS A L y') := by ring
      _ = toLS A L (PowerSeries.C (ϖ ^ a)) * toLS A L x' := h
      _ = (toLS A L (PowerSeries.C (ϖ ^ b)) * toLS A L (PowerSeries.C (ϖ ^ (a - b)))) * toLS A L x' := by rw [hCab]
      _ = toLS A L (PowerSeries.C (ϖ ^ b)) * toLS A L (PowerSeries.C (ϖ ^ (a - b)) * x') := by rw [map_mul]; ring
  · right
    have hCba : toLS A L (PowerSeries.C (ϖ ^ b)) = toLS A L (PowerSeries.C (ϖ ^ a)) * toLS A L (PowerSeries.C (ϖ ^ (b - a))) := by
      rw [← map_mul, ← map_mul, ← pow_add, Nat.add_sub_cancel' hab.le]
    have hf0 : f ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      have h1 : toLS A L x' = 0 := (mul_eq_zero.mp h.symm).resolve_left (hϖL a)
      exact hx' (by rw [toLS_injective (A := A) (L := L) (h1.trans (map_zero _).symm), map_zero])
    refine ⟨PowerSeries.C (ϖ ^ (b - a)) * y', x', hx', ?_⟩
    unfold IsPres
    apply mul_left_cancel₀ hf0
    apply mul_left_cancel₀ (hϖL a)
    calc toLS A L (PowerSeries.C (ϖ ^ a)) * (f * (f⁻¹ * toLS A L x'))
          = toLS A L (PowerSeries.C (ϖ ^ a)) * toLS A L x' := by rw [← mul_assoc f, mul_inv_cancel₀ hf0, one_mul]
      _ = f * (toLS A L (PowerSeries.C (ϖ ^ b)) * toLS A L y') := h.symm
      _ = f * ((toLS A L (PowerSeries.C (ϖ ^ a)) * toLS A L (PowerSeries.C (ϖ ^ (b - a)))) * toLS A L y') := by rw [hCba]
      _ = toLS A L (PowerSeries.C (ϖ ^ a)) * (f * toLS A L (PowerSeries.C (ϖ ^ (b - a)) * y')) := by rw [map_mul]; ring

section Ring

variable (K : IntermediateField L (LaurentSeries L)) (hK : ∀ f : ↥K, HasPres (A := A) (f : LaurentSeries L))

def IsGauss (A : Type*) [CommRing A] [IsLocalRing A] {L : Type*} [Field L] [Algebra A L] (f : LaurentSeries L) : Prop :=
  ∃ x y : PowerSeries A, red A y ≠ 0 ∧ IsPres f x y

include hK in

def gaussVS : ValuationSubring ↥K where
  carrier := {f | IsGauss A (f : LaurentSeries L)}
  mul_mem' := by
    rintro f g ⟨x, y, hy, h⟩ ⟨x', y', hy', h'⟩
    refine ⟨x * x', y * y', red_ne_zero_mul hy hy', ?_⟩
    unfold IsPres at *
    rw [MulMemClass.coe_mul, map_mul, map_mul, show (f : LaurentSeries L) * g * (toLS A L y * toLS A L y') =
      ((f : LaurentSeries L) * toLS A L y) * ((g : LaurentSeries L) * toLS A L y') by ring, h, h']
  one_mem' := ⟨1, 1, by rw [red_one]; exact one_ne_zero, by unfold IsPres; rw [OneMemClass.coe_one, one_mul]⟩
  add_mem' := by
    rintro f g ⟨x, y, hy, h⟩ ⟨x', y', hy', h'⟩
    refine ⟨x * y' + x' * y, y * y', red_ne_zero_mul hy hy', ?_⟩
    unfold IsPres at *
    rw [AddMemClass.coe_add, map_mul, map_add, map_mul, map_mul]
    calc ((f : LaurentSeries L) + g) * (toLS A L y * toLS A L y')
          = ((f : LaurentSeries L) * toLS A L y) * toLS A L y' + ((g : LaurentSeries L) * toLS A L y') * toLS A L y := by ring
      _ = toLS A L x * toLS A L y' + toLS A L x' * toLS A L y := by rw [h, h']
  zero_mem' := ⟨0, 1, by rw [red_one]; exact one_ne_zero, by unfold IsPres; rw [ZeroMemClass.coe_zero, zero_mul, map_zero]⟩
  neg_mem' := by
    rintro f ⟨x, y, hy, h⟩
    exact ⟨-x, y, hy, by unfold IsPres at *; rw [NegMemClass.coe_neg, map_neg, neg_mul, h]⟩
  mem_or_inv_mem' := by
    intro f
    rcases exists_gauss_or_inv (hK f) with h | h
    · exact Or.inl h
    · right
      obtain ⟨x, y, hy, h⟩ := h
      refine ⟨x, y, hy, ?_⟩
      unfold IsPres at h ⊢
      rwa [show ((f⁻¹ : ↥K) : LaurentSeries L) = (f : LaurentSeries L)⁻¹ from rfl]

variable {K}

theorem mem_gaussVS_iff (f : ↥K) : f ∈ gaussVS K hK ↔ IsGauss A (f : LaurentSeries L) := Iff.rfl

theorem inv_mem_gaussVS_of_red_ne_zero {f : ↥K} {x y : PowerSeries A} (h : IsPres (f : LaurentSeries L) x y) (hx : red A x ≠ 0) :
    f⁻¹ ∈ gaussVS K hK := by
  have hf0 : (f : LaurentSeries L) ≠ 0 := by
    intro h0; unfold IsPres at h; rw [h0, zero_mul] at h
    apply hx
    have hx0 : x = 0 := toLS_injective (A := A) (L := L) (h.symm.trans (map_zero (toLS A L)).symm)
    rw [hx0, map_zero]
  refine ⟨y, x, hx, ?_⟩
  unfold IsPres at h ⊢
  rw [show ((f⁻¹ : ↥K) : LaurentSeries L) = (f : LaurentSeries L)⁻¹ from rfl, ← h, ← mul_assoc, inv_mul_cancel₀ hf0, one_mul]

theorem red_ne_zero_of_inv_mem_gaussVS {f : ↥K} {x y : PowerSeries A} (hy : red A y ≠ 0) (h : IsPres (f : LaurentSeries L) x y)
    (hf0 : (f : LaurentSeries L) ≠ 0) (hinv : f⁻¹ ∈ gaussVS K hK) : red A x ≠ 0 := by
  obtain ⟨x', y', hy', h'⟩ := hinv
  intro hx
  unfold IsPres at h h'
  rw [show ((f⁻¹ : ↥K) : LaurentSeries L) = (f : LaurentSeries L)⁻¹ from rfl] at h'
  have key : x * x' = y' * y := by
    apply toLS_injective (A := A) (L := L)
    rw [map_mul, map_mul, ← h, ← h']
    field_simp
  have := congrArg (red A) key
  rw [map_mul, map_mul, hx, zero_mul] at this
  exact (mul_ne_zero hy' hy) this.symm

theorem mem_nonunits_gaussVS_iff {f : ↥K} {x y : PowerSeries A} (hy : red A y ≠ 0) (h : IsPres (f : LaurentSeries L) x y) :
    f ∈ (gaussVS K hK).nonunits ↔ red A x = 0 := by
  rw [ValuationSubring.mem_nonunits_iff_or]
  constructor
  · rintro (hf0 | hninv)
    · have hx0 : x = 0 := by
        unfold IsPres at h
        rw [show (f : LaurentSeries L) = 0 from congrArg Subtype.val hf0, zero_mul] at h
        exact toLS_injective (A := A) (L := L) (h.symm.trans (map_zero (toLS A L)).symm)
      rw [hx0, map_zero]
    · by_contra hx
      exact hninv (inv_mem_gaussVS_of_red_ne_zero hK h hx)
  · intro hx
    by_cases hf0 : f = 0
    · exact Or.inl hf0
    · right
      intro hinv
      exact red_ne_zero_of_inv_mem_gaussVS hK hy h (fun h0 => hf0 (Subtype.ext h0)) hinv hx

theorem isPres_algebraMap [Algebra A ↥K] [IsScalarTower A L ↥K] (a : A) :
    IsPres ((algebraMap A ↥K a : ↥K) : LaurentSeries L) (PowerSeries.C a) 1 := by
  unfold IsPres
  rw [map_one, mul_one, toLS_C, IsScalarTower.algebraMap_apply A L ↥K a]
  show ((algebraMap L ↥K (algebraMap A L a) : ↥K) : LaurentSeries L) = _
  rw [show ((algebraMap L ↥K (algebraMap A L a) : ↥K) : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a) from rfl,
    LaurentSeries.algebraMap_apply]

theorem algebraMap_mem_gaussVS [Algebra A ↥K] [IsScalarTower A L ↥K] (a : A) : algebraMap A ↥K a ∈ gaussVS K hK :=
  ⟨PowerSeries.C a, 1, by rw [red_one]; exact one_ne_zero, isPres_algebraMap a⟩

theorem algebraMap_mem_nonunits_gaussVS [Algebra A ↥K] [IsScalarTower A L ↥K] {a : A} (ha : a ∈ IsLocalRing.maximalIdeal A) :
    algebraMap A ↥K a ∈ (gaussVS K hK).nonunits := by
  rw [mem_nonunits_gaussVS_iff hK (by rw [red_one]; exact one_ne_zero) (isPres_algebraMap a), red_C,
    (IsLocalRing.residue_eq_zero_iff a).mpr ha, map_zero]

end Ring

section Presentations

variable [CharZero L]

theorem coeffEmb_intSeriesC (φ : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ φ) = toLS A L (φ.map (Int.castRingHom A)) := by
  ext k
  rw [coeffEmb, coeffMap_coeff]
  show algebraMap ℚ L ((HahnSeries.ofPowerSeries ℤ ℚ (φ.map (Int.castRingHom ℚ))).coeff k) =
    (HahnSeries.ofPowerSeries ℤ L ((φ.map (Int.castRingHom A)).map (algebraMap A L))).coeff k
  rcases lt_or_ge k 0 with hk | hk
  · rw [coeff_ofPowerSeries_neg _ hk, coeff_ofPowerSeries_neg _ hk, map_zero]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast, map_intCast]

theorem hasPres_coeffEmb_intSeriesC (φ : PowerSeries ℤ) : HasPres (A := A) (coeffEmb L (intSeriesC ℚ φ)) :=
  ⟨φ.map (Int.castRingHom A), 1, one_ne_zero, by unfold IsPres; rw [map_one, mul_one, coeffEmb_intSeriesC (A := A)]⟩

theorem hasPres_coeffEmb_of_mem_intFormRatiosC (Γ : Subgroup SL(2, ℤ)) {g : LaurentSeries ℚ} (hg : g ∈ intFormRatiosC ℚ Γ) :
    HasPres (A := A) (coeffEmb L g) := by
  obtain ⟨k, f₁, f₂, pf, pg, -, -, -, rfl⟩ := hg
  rw [map_div₀]
  exact (hasPres_coeffEmb_intSeriesC pf).mul (hasPres_coeffEmb_intSeriesC pg).inv

theorem hasPres_coeffEmb_of_mem_adjoin {S : Set (LaurentSeries ℚ)} (hS : ∀ s ∈ S, HasPres (A := A) (coeffEmb L s))
    {g : LaurentSeries ℚ} (hg : g ∈ IntermediateField.adjoin ℚ S) : HasPres (A := A) (coeffEmb L g) := by
  have hg' : g ∈ (IntermediateField.adjoin ℚ S).toSubfield := hg
  rw [IntermediateField.adjoin_toSubfield] at hg'
  clear hg
  induction hg' using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | hz
      · rw [show coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) by
          rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]]
        exact hasPres_algebraMap _
      · exact hS z hz
  | one => rw [map_one, show (1 : LaurentSeries L) = algebraMap L (LaurentSeries L) 1 from (map_one _).symm]; exact hasPres_algebraMap _
  | add z w _ _ hz hw => rw [map_add]; exact hz.add hw
  | neg z _ hz => rw [map_neg]; exact hz.neg
  | inv z _ hz => rw [map_inv₀]; exact hz.inv
  | mul z w _ _ hz hw => rw [map_mul]; exact hz.mul hw

theorem hasPres_of_mem_laurentBaseChange {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ z ∈ F₀, HasPres (A := A) (coeffEmb L z))
    {f : LaurentSeries L} (hf : f ∈ laurentBaseChange L F₀) : HasPres (A := A) f := by
  rw [mem_laurentBaseChange_iff] at hf
  induction hf using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨w, hw, rfl⟩
      · exact hasPres_algebraMap c
      · exact hF w hw
  | one => rw [show (1 : LaurentSeries L) = algebraMap L (LaurentSeries L) 1 from (map_one _).symm]; exact hasPres_algebraMap _
  | add z w _ _ hz hw => exact hz.add hw
  | neg z _ hz => exact hz.neg
  | inv z _ hz => exact hz.inv
  | mul z w _ _ hz hw => exact hz.mul hw

theorem hasPres_of_mem_laurentBaseChange_qExp (Γ : Subgroup SL(2, ℤ)) {f : LaurentSeries L} (hf : f ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ)) :
    HasPres (A := A) f :=
  hasPres_of_mem_laurentBaseChange (fun _ hz =>
    hasPres_coeffEmb_of_mem_adjoin (fun _ hs => hasPres_coeffEmb_of_mem_intFormRatiosC _ hs) hz) hf

end Presentations

section JClause

variable [CharZero L]

noncomputable def jNumA (A : Type*) [CommRing A] : PowerSeries A := jNum.map (Int.castRingHom A)

theorem constantCoeff_jNumA : PowerSeries.constantCoeff (jNumA A) = 1 := by
  rw [jNumA, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_jNum, map_one]

theorem constantCoeff_red_jNumA : PowerSeries.constantCoeff (red A (jNumA A)) = 1 := by
  rw [red, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_jNumA, map_one]

theorem coeffEmb_jq : coeffEmb L jq = HahnSeries.single (-1 : ℤ) (1 : L) * toLS A L (jNumA A) := by
  rw [jq, map_mul, coeffEmb, coeffMap_single, map_one]
  congr 1
  exact coeffEmb_intSeriesC (A := A) (L := L) jNum

theorem toLS_X : toLS A L PowerSeries.X = HahnSeries.single (1 : ℤ) (1 : L) := by
  rw [toLS, RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]

theorem toLS_X_pow (d : ℕ) : toLS A L (PowerSeries.X ^ d) = HahnSeries.single (d : ℤ) (1 : L) := by
  rw [map_pow, toLS_X, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]

noncomputable def jPolyNum (P : Polynomial A) : PowerSeries A :=
  ∑ i ∈ Finset.range (P.natDegree + 1), PowerSeries.C (P.coeff i) * (PowerSeries.X ^ (P.natDegree - i) * jNumA A ^ i)

variable {K : IntermediateField L (LaurentSeries L)} [Algebra A ↥K] [IsScalarTower A L ↥K]

theorem coe_algebraMap_K (a : A) : ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = toLS A L (PowerSeries.C a) := by
  have := isPres_algebraMap (K := K) (L := L) a
  unfold IsPres at this
  rwa [map_one, mul_one] at this

theorem isPres_aeval (P : Polynomial A) (j : ↥K) (hj : (j : LaurentSeries L) = HahnSeries.single (-1 : ℤ) (1 : L) * toLS A L (jNumA A)) :
    IsPres ((Polynomial.aeval j P : ↥K) : LaurentSeries L) (jPolyNum P) (PowerSeries.X ^ P.natDegree) := by
  unfold IsPres
  have hq : ∀ i ∈ Finset.range (P.natDegree + 1), (j : LaurentSeries L) ^ i * HahnSeries.single (P.natDegree : ℤ) (1 : L) =
      HahnSeries.single ((P.natDegree - i : ℕ) : ℤ) (1 : L) * toLS A L (jNumA A) ^ i := by
    intro i hi
    have hid : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hj, mul_pow, HahnSeries.single_pow, one_pow, mul_right_comm, HahnSeries.single_mul_single, one_mul]
    have e : (i • (-1 : ℤ) + (P.natDegree : ℤ)) = ((P.natDegree - i : ℕ) : ℤ) := by
      rw [nsmul_eq_mul, Nat.cast_sub hid]; ring
    rw [e]
  rw [Polynomial.aeval_eq_sum_range, AddSubmonoidClass.coe_finset_sum, Finset.sum_mul, toLS_X_pow, jPolyNum, map_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Algebra.smul_def, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_algebraMap_K, mul_assoc, hq i hi, map_mul, map_mul,
    toLS_X_pow, map_pow, ← mul_assoc]

theorem red_X : red A PowerSeries.X = PowerSeries.X := by rw [red, PowerSeries.map_X]

theorem red_jPolyNum_ne_zero {P : Polynomial A} (hP : P.map (IsLocalRing.residue A) ≠ 0) : red A (jPolyNum P) ≠ 0 := by
  classical
  set i₀ := (P.map (IsLocalRing.residue A)).natDegree with hi₀
  have hi₀d : i₀ ≤ P.natDegree := Polynomial.natDegree_map_le
  have hlead : (P.map (IsLocalRing.residue A)).coeff i₀ ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  rw [Polynomial.coeff_map] at hlead
  have hred : red A (jPolyNum P) = ∑ i ∈ Finset.range (P.natDegree + 1),
      PowerSeries.C (IsLocalRing.residue A (P.coeff i)) * (PowerSeries.X ^ (P.natDegree - i) * red A (jNumA A) ^ i) := by
    unfold jPolyNum
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_mul, map_pow, red_C, red_X]
  intro h
  have hc : PowerSeries.coeff (P.natDegree - i₀) (∑ i ∈ Finset.range (P.natDegree + 1),
      PowerSeries.C (IsLocalRing.residue A (P.coeff i)) * (PowerSeries.X ^ (P.natDegree - i) * red A (jNumA A) ^ i)) = 0 := by
    rw [← hred, h, map_zero]
  rw [map_sum, Finset.sum_eq_single i₀] at hc
  · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_pow, constantCoeff_red_jNumA, one_pow, mul_one] at hc
    exact hlead hc
  · intro i hi hne
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    by_cases hle : P.natDegree - i ≤ P.natDegree - i₀
    · have hid : i ≤ P.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hgt : i₀ < i := by omega
      have h0 : (P.map (IsLocalRing.residue A)).coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
      rw [Polynomial.coeff_map] at h0
      rw [h0, zero_mul]
    · rw [if_neg hle, mul_zero]
  · intro hi₀'
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hi₀d)) hi₀'

theorem red_X_pow_ne_zero (d : ℕ) : red A (PowerSeries.X ^ d) ≠ 0 := by
  rw [red_X_pow]; exact pow_ne_zero _ PowerSeries.X_ne_zero

end JClause

end ModularCurve.GaussPresGamma
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC.ModularCurve P2MW.S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC.ModularCurve.GaussPresGamma"
p2m_reactivate "P2MW.S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC.ModularCurve ModularCurve.GaussPresGamma in
theorem solution
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ W₀ : ValuationSubring ↥K,
      (∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ∧
      (∀ a : A, algebraMap A ↥K a ∈ W₀) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ W₀.nonunits) ∧
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ W₀ ∧ (Polynomial.aeval j P)⁻¹ ∈ W₀) ∧
      (∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) := by
  have hKpres : ∀ f : ↥K, HasPres (A := A) (f : LaurentSeries L) := fun f =>
    hasPres_of_mem_laurentBaseChange_qExp (A := A) Γ (by rw [← hK]; exact f.2)
  refine ⟨gaussVS K hKpres, fun f => Iff.rfl, fun a => algebraMap_mem_gaussVS hKpres a,
    fun a ha => algebraMap_mem_nonunits_gaussVS hKpres ha, fun P hP => ?_, fun f x y hy h => mem_nonunits_gaussVS_iff hKpres hy h⟩
  have hj' : (j : LaurentSeries L) = HahnSeries.single (-1 : ℤ) (1 : L) * toLS A L (jNumA A) := by rw [hj, coeffEmb_jq (A := A)]
  have hpres := isPres_aeval (A := A) P j hj'
  exact ⟨⟨jPolyNum P, PowerSeries.X ^ P.natDegree, red_X_pow_ne_zero _, hpres⟩,
    inv_mem_gaussVS_of_red_ne_zero hKpres hpres (red_jPolyNum_ne_zero hP)⟩

end S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC (solution)
