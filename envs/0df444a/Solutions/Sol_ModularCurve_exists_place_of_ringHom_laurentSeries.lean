-- Prove2me | solution 1 for ModularCurve.exists_place_of_ringHom_laurentSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/816a0ac1-8eeb-5a37-986c-5bc15dc7a1c4

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_place_of_ringHom_laurentSeries

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open AlgebraicCurve HahnSeries

noncomputable section

namespace S12LaurentPlace

section Orders

variable {K : Type*} [Field K]

theorem order_inv' {f : LaurentSeries K} (hf : f ≠ 0) : (f⁻¹).order = -f.order := by
  have h : f⁻¹ * f = 1 := inv_mul_cancel₀ hf
  have hinv : f⁻¹ ≠ 0 := inv_ne_zero hf
  have := HahnSeries.order_mul hinv hf
  rw [h, HahnSeries.order_one] at this
  omega

theorem order_div' {f g : LaurentSeries K} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f / g).order = f.order - g.order := by
  rw [div_eq_mul_inv, HahnSeries.order_mul hf (inv_ne_zero hg), order_inv' hg]
  ring

theorem order_pow' {f : LaurentSeries K} (hf : f ≠ 0) (n : ℕ) : (f ^ n).order = n * f.order := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, HahnSeries.order_mul (pow_ne_zero _ hf) hf, ih]
    push_cast
    ring

theorem order_zpow' {f : LaurentSeries K} (hf : f ≠ 0) (n : ℤ) : (f ^ n).order = n * f.order := by
  rcases n with (n | n)
  · rw [Int.ofNat_eq_natCast, zpow_natCast, order_pow' hf]
  · rw [zpow_negSucc, order_inv' (pow_ne_zero _ hf), order_pow' hf, Int.negSucc_eq]
    push_cast
    ring

end Orders

section PlaceOfLaurentEmb

variable {k F K : Type*} [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
  (θ : F →+* LaurentSeries K)

def pullbackVS : ValuationSubring F where
  carrier := {x | 0 ≤ (θ x).order}
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, order_zero, le_refl]
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, order_one, le_refl]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    rcases eq_or_ne (θ a + θ b) 0 with h0 | h0
    · rw [h0, order_zero]
    · exact le_trans (le_min ha hb) (min_order_le_order_add h0)
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg] at *
    rwa [order_neg]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul] at *
    rcases eq_or_ne (θ a) 0 with ha0 | ha0
    · rw [ha0, zero_mul, order_zero]
    rcases eq_or_ne (θ b) 0 with hb0 | hb0
    · rw [hb0, mul_zero, order_zero]
    · rw [HahnSeries.order_mul ha0 hb0]; exact add_nonneg ha hb
  mem_or_inv_mem' := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · left; simp only [Set.mem_setOf_eq, map_zero, order_zero, le_refl]
    have hθa : θ a ≠ 0 := fun h => ha (θ.injective (by simp [h]))
    simp only [Set.mem_setOf_eq, map_inv₀, order_inv' hθa]
    omega

@[scoped simp] theorem mem_pullbackVS (x : F) : x ∈ pullbackVS θ ↔ 0 ≤ (θ x).order := Iff.rfl

variable (hθ : ∀ a : k, θ (algebraMap k F a) = HahnSeries.C (algebraMap k K a))
variable {π : F} (hπ : (θ π).order = 1)
include hπ

theorem θπ_ne_zero : θ π ≠ 0 :=
  fun h => one_ne_zero (hπ ▸ h ▸ order_zero)

theorem π_ne_zero : π ≠ 0 :=
  fun h => θπ_ne_zero θ hπ (h ▸ map_zero θ)

def uniformizer : pullbackVS θ :=
  ⟨π, by rw [mem_pullbackVS, hπ]; omega⟩

@[scoped simp] theorem coe_uniformizer : ((uniformizer θ hπ : pullbackVS θ) : F) = π := rfl

omit hπ in
theorem isUnit_pullbackVS_iff {x : pullbackVS θ} (hx : (x : F) ≠ 0) :
    IsUnit x ↔ (θ (x : F)).order = 0 := by
  have hθx : θ (x : F) ≠ 0 := fun h => hx (θ.injective (by simp [h]))
  constructor
  · rintro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp h
    have hb' : (x : F) * (b : F) = 1 := by
      have := congrArg (fun z : pullbackVS θ => (z : F)) hb
      simpa using this
    have hbne : (b : F) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hb'; exact zero_ne_one hb'
    have hθb : θ (b : F) ≠ 0 := fun h => hbne (θ.injective (by simp [h]))
    have hsum : (θ (x : F)).order + (θ (b : F)).order = 0 := by
      rw [← HahnSeries.order_mul hθx hθb, ← map_mul, hb', map_one, order_one]
    have h1 : (0 : ℤ) ≤ (θ (x : F)).order := x.2
    have h2 : (0 : ℤ) ≤ (θ (b : F)).order := b.2
    omega
  · intro h0
    have hinv : (x : F)⁻¹ ∈ pullbackVS θ := by
      rw [mem_pullbackVS, map_inv₀, order_inv' hθx]
      omega
    refine isUnit_iff_exists_inv.mpr ⟨⟨(x : F)⁻¹, hinv⟩, ?_⟩
    refine Subtype.ext ?_
    push_cast
    exact mul_inv_cancel₀ hx

theorem irreducible_uniformizer : Irreducible (uniformizer θ hπ) := by
  constructor
  · rw [isUnit_pullbackVS_iff θ (π_ne_zero θ hπ), coe_uniformizer, hπ]
    omega
  · rintro a b hab
    have hab' : π = (a : F) * (b : F) := congrArg Subtype.val hab
    have ha0 : (a : F) ≠ 0 := fun h => π_ne_zero θ hπ (by rw [hab', h, zero_mul])
    have hb0 : (b : F) ≠ 0 := fun h => π_ne_zero θ hπ (by rw [hab', h, mul_zero])
    have hθa : θ (a : F) ≠ 0 := fun h => ha0 (θ.injective (by simp [h]))
    have hθb : θ (b : F) ≠ 0 := fun h => hb0 (θ.injective (by simp [h]))
    have hsum : (θ (a : F)).order + (θ (b : F)).order = 1 := by
      rw [← HahnSeries.order_mul hθa hθb, ← map_mul, ← hab', hπ]
    have ha' : 0 ≤ (θ (a : F)).order := a.2
    have hb' : 0 ≤ (θ (b : F)).order := b.2
    rcases eq_or_lt_of_le ha' with ha0' | hapos
    · exact .inl ((isUnit_pullbackVS_iff θ ha0).mpr ha0'.symm)
    rcases eq_or_lt_of_le hb' with hb0' | hbpos
    · exact .inr ((isUnit_pullbackVS_iff θ hb0).mpr hb0'.symm)
    omega

theorem pullbackVS_isPrincipalIdealRing : IsPrincipalIdealRing (pullbackVS θ) := by
  refine (IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨uniformizer θ hπ, irreducible_uniformizer θ hπ, ?_⟩).toIsPrincipalIdealRing
  rintro x hx
  have hf : (x : F) ≠ 0 := fun h => hx (Subtype.ext h)
  have hθf : θ (x : F) ≠ 0 := fun h => hf (θ.injective (by simp [h]))
  have hmnonneg : (0 : ℤ) ≤ (θ (x : F)).order := x.2
  set n : ℕ := (θ (x : F)).order.toNat with hn
  have hmn : (n : ℤ) = (θ (x : F)).order := Int.toNat_of_nonneg hmnonneg
  have hπn : (π : F) ^ n ≠ 0 := pow_ne_zero _ (π_ne_zero θ hπ)
  have hθπn : θ (π ^ n) ≠ 0 := fun h => hπn (θ.injective (by simp [h]))
  have hπorder : (θ (π ^ n)).order = n := by
    rw [map_pow, order_pow' (θπ_ne_zero θ hπ), hπ, mul_one]
  have hdiv0 : (x : F) / π ^ n ≠ 0 := div_ne_zero hf hπn
  have hu0 : (θ ((x : F) / π ^ n)).order = 0 := by
    rw [map_div₀, order_div' hθf hθπn, hπorder, ← hmn]
    ring
  have humem : (x : F) / π ^ n ∈ pullbackVS θ := hu0.ge
  have hu : IsUnit (⟨(x : F) / π ^ n, humem⟩ : pullbackVS θ) :=
    (isUnit_pullbackVS_iff θ hdiv0).mpr hu0
  refine ⟨n, hu.unit, Subtype.ext ?_⟩
  have hcoe : ((hu.unit : pullbackVS θ) : F) = (x : F) / π ^ n := by
    rw [IsUnit.unit_spec]
  push_cast
  rw [hcoe, mul_comm, coe_uniformizer, div_mul_cancel₀ _ hπn]

def placeOfLaurentEmb : Place k F where
  toValuationSubring := pullbackVS θ
  algebraMap_mem' a := by
    rw [mem_pullbackVS, hθ a, order_C]
  ne_top' := fun h => by
    have hmem : π⁻¹ ∈ pullbackVS θ := h ▸ ValuationSubring.mem_top _
    rw [mem_pullbackVS, map_inv₀, order_inv' (θπ_ne_zero θ hπ), hπ] at hmem
    omega
  isPrincipalIdealRing' := pullbackVS_isPrincipalIdealRing θ hπ

@[scoped simp] theorem placeOfLaurentEmb_toVS :
    (placeOfLaurentEmb θ hθ hπ).toValuationSubring = pullbackVS θ := rfl

theorem ord_placeOfLaurentEmb (f : F) :
    (placeOfLaurentEmb θ hθ hπ).ord f = (θ f).order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [Place.ord_zero, map_zero, order_zero]
  have hθf : θ f ≠ 0 := fun h => hf (θ.injective (by simp [h]))
  set n : ℤ := (θ f).order with hndef
  have hπn : (π : F) ^ n ≠ 0 := zpow_ne_zero _ (π_ne_zero θ hπ)
  have hθπn : θ (π ^ n) ≠ 0 := by
    rw [map_zpow₀]; exact zpow_ne_zero _ (θπ_ne_zero θ hπ)
  have huord : (θ (f / π ^ n)).order = 0 := by
    rw [map_div₀, order_div' hθf hθπn, map_zpow₀, order_zpow' (θπ_ne_zero θ hπ), hπ, mul_one,
      ← hndef]
    ring
  have humem : f / π ^ n ∈ pullbackVS θ := huord.ge
  have hune : f / π ^ n ≠ 0 := div_ne_zero hf hπn
  have huu : IsUnit (⟨f / π ^ n, humem⟩ : pullbackVS θ) :=
    (isUnit_pullbackVS_iff θ hune).mpr huord
  have hdecomp : f = ((huu.unit : pullbackVS θ) : F) * (((uniformizer θ hπ : _) : F) ^ n) := by
    rw [IsUnit.unit_spec, coe_uniformizer]
    exact (div_mul_cancel₀ f hπn).symm
  rw [hdecomp]
  exact (placeOfLaurentEmb θ hθ hπ).ord_unit_smul_zpow huu.unit (irreducible_uniformizer θ hπ) n

def coeff0OnVS : (placeOfLaurentEmb θ hθ hπ).toValuationSubring →+* K where
  toFun x := (θ (x : F)).coeff 0
  map_zero' := by simp
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    rw [show (1 : LaurentSeries K) = single (0:ℤ) (1:K) from rfl, coeff_single_same]
  map_add' x y := by
    show (θ ((x : F) + (y : F))).coeff 0 = _
    rw [map_add, coeff_add]
  map_mul' x y := by
    show (θ ((x : F) * (y : F))).coeff 0 = _
    rw [map_mul]
    rcases eq_or_ne (θ (x : F)) 0 with hx0 | hx0; · simp [hx0]
    rcases eq_or_ne (θ (y : F)) 0 with hy0 | hy0; · simp [hy0]
    have hx : (0 : ℤ) ≤ (θ (x : F)).order := x.2
    have hy : (0 : ℤ) ≤ (θ (y : F)).order := y.2
    rcases eq_or_lt_of_le hx with hx0' | hxpos
    · rcases eq_or_lt_of_le hy with hy0' | hypos
      · rw [show (0:ℤ) = (θ (x:F)).order + (θ (y:F)).order by omega,
          coeff_mul_order_add_order, leadingCoeff_eq, leadingCoeff_eq, ← hx0', ← hy0',
          zero_add]
      · rw [coeff_eq_zero_of_lt_order hypos, mul_zero,
          coeff_eq_zero_of_lt_order (by rw [HahnSeries.order_mul hx0 hy0]; omega)]
    · rw [coeff_eq_zero_of_lt_order hxpos, zero_mul,
        coeff_eq_zero_of_lt_order (by rw [HahnSeries.order_mul hx0 hy0]; omega)]

theorem coeff0OnVS_mem_maximalIdeal (x : (placeOfLaurentEmb θ hθ hπ).toValuationSubring)
    (hx : x ∈ IsLocalRing.maximalIdeal _) : coeff0OnVS θ hθ hπ x = 0 := by
  rcases eq_or_ne (x : F) 0 with hx0 | hx0
  · show (θ (x : F)).coeff 0 = 0; rw [hx0, map_zero, coeff_zero]
  have hnu : ¬IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hx
  have hxmem : (0 : ℤ) ≤ (θ (x : F)).order := x.2
  have hord : 0 < (θ (x : F)).order := by
    rcases lt_or_eq_of_le hxmem with h | h
    · exact h
    · exact absurd ((isUnit_pullbackVS_iff θ hx0).mpr h.symm) hnu
  show (θ (x : F)).coeff 0 = 0
  exact coeff_eq_zero_of_lt_order hord

def residueToCoeff0 : (placeOfLaurentEmb θ hθ hπ).ResidueField →ₐ[k] K :=
  { Ideal.Quotient.lift _ (coeff0OnVS θ hθ hπ) (coeff0OnVS_mem_maximalIdeal θ hθ hπ) with
    commutes' := fun q => by
      show Ideal.Quotient.lift _ (coeff0OnVS θ hθ hπ) (coeff0OnVS_mem_maximalIdeal θ hθ hπ)
        (Ideal.Quotient.mk _ (algebraMap k (placeOfLaurentEmb θ hθ hπ).toValuationSubring q))
          = algebraMap k K q
      rw [Ideal.Quotient.lift_mk]
      show (θ (algebraMap k F q)).coeff 0 = algebraMap k K q
      rw [hθ]
      show (HahnSeries.single (0 : ℤ) (algebraMap k K q)).coeff 0 = algebraMap k K q
      exact HahnSeries.coeff_single_same _ _ }

theorem residueToCoeff0_residue (x : (placeOfLaurentEmb θ hθ hπ).toValuationSubring) :
    residueToCoeff0 θ hθ hπ (IsLocalRing.residue _ x) = (θ (x : F)).coeff 0 :=
  rfl

include hθ in

theorem exists_place :
    ∃ v : Place k F,
      (∀ f : F, f ∈ v.toValuationSubring ↔ 0 ≤ (θ f).order) ∧
      (∀ f : F, v.ord f = (θ f).order) ∧
      ∃ ι : v.ResidueField →ₐ[k] K,
        ∀ x : v.toValuationSubring, ι (IsLocalRing.residue v.toValuationSubring x) = (θ (x : F)).coeff 0 :=
  ⟨placeOfLaurentEmb θ hθ hπ, fun f => mem_pullbackVS θ f, ord_placeOfLaurentEmb θ hθ hπ,
    residueToCoeff0 θ hθ hπ, residueToCoeff0_residue θ hθ hπ⟩

end PlaceOfLaurentEmb

end S12LaurentPlace
p2m_reactivate "P2MW.S_ModularCurve_exists_place_of_ringHom_laurentSeries.S12LaurentPlace"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_place_of_ringHom_laurentSeries.S12LaurentPlace"

theorem solution
    {k F K : Type*} [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K]
    (θ : F →+* LaurentSeries K)
    (hθ : ∀ a : k, θ (algebraMap k F a) = HahnSeries.C (algebraMap k K a))
    (hunif : ∃ x : F, (θ x).order = 1) :
    ∃ v : AlgebraicCurve.Place k F,
      (∀ f : F, f ∈ v.toValuationSubring ↔ 0 ≤ (θ f).order) ∧
      (∀ f : F, v.ord f = (θ f).order) ∧
      ∃ ι : v.ResidueField →ₐ[k] K,
        ∀ x : v.toValuationSubring, ι (IsLocalRing.residue v.toValuationSubring x) = (θ (x : F)).coeff 0 := by
  obtain ⟨π, hπ⟩ := hunif
  exact S12LaurentPlace.exists_place θ hθ hπ

end S_ModularCurve_exists_place_of_ringHom_laurentSeries
end P2MW
export P2MW.S_ModularCurve_exists_place_of_ringHom_laurentSeries (solution)
