-- Prove2me | solution 1 for ModularCurve.exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1ed2e737-7c51-5a13-b375-79e7eb180835

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq

set_option autoImplicit false

open HahnSeries ModularCurve

namespace CuspSection

variable {L : Type} [Field L] [CharZero L]
variable {K : IntermediateField L (LaurentSeries L)}
variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
variable [Algebra A ↥K] [IsScalarTower A L ↥K]

noncomputable abbrev R₀ (L : Type) [Field L] : Subring (LaurentSeries L) := (algebraMap (PowerSeries L) (LaurentSeries L)).range

omit [CharZero L] in
theorem mem_R₀_iff {x : LaurentSeries L} : x ∈ R₀ L ↔ ∃ y : PowerSeries L, ofPowerSeries ℤ L y = x := by
  simp only [RingHom.mem_range, LaurentSeries.coe_algebraMap]

theorem coe_algebraMap_eq (a : A) :
    ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = ofPowerSeries ℤ L (PowerSeries.C (algebraMap A L a)) := by
  rw [ofPowerSeries_C, IsScalarTower.algebraMap_apply A L ↥K, HahnSeries.C_apply]
  exact (IntermediateField.coe_algebraMap_apply (S := K) (algebraMap A L a)).trans
    (ModularCurve.algebraMap_laurentSeries_eq_single L (algebraMap A L a))

theorem exists_inv_j (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ w : PowerSeries L, ((j⁻¹ : ↥K) : LaurentSeries L) = ofPowerSeries ℤ L w ∧ PowerSeries.constantCoeff w = 0 := by
  have hjL : ((j : LaurentSeries L)) = ModularCurve.jqModC L := by
    rw [hj]; exact ModularCurve.map_jqModC (algebraMap ℚ L)
  set J : PowerSeries L := jNum.map (Int.castRingHom L) with hJ
  have hJ0 : PowerSeries.constantCoeff J = 1 := by
    rw [hJ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      constantCoeff_jNum, map_one]
  have hJu : IsUnit J := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hJ0]; exact isUnit_one)
  obtain ⟨u, hu⟩ := hJu
  refine ⟨(PowerSeries.X : PowerSeries L) * ↑(u⁻¹), ?_, ?_⟩
  · have hjq : ((j : LaurentSeries L)) = single (-1 : ℤ) (1 : L) * ofPowerSeries ℤ L J := by rw [hjL]; rfl
    have hprod : ((j : LaurentSeries L)) * ofPowerSeries ℤ L ((PowerSeries.X : PowerSeries L) * ↑(u⁻¹)) = 1 := by
      rw [hjq, map_mul, ofPowerSeries_X, ← hu]
      calc single (-1 : ℤ) (1 : L) * ofPowerSeries ℤ L ↑u * (single (1 : ℤ) (1 : L) * ofPowerSeries ℤ L ↑(u⁻¹))
          = (single (-1 : ℤ) (1 : L) * single (1 : ℤ) (1 : L)) * (ofPowerSeries ℤ L ↑u * ofPowerSeries ℤ L ↑(u⁻¹)) := by ring
        _ = 1 := by
            rw [← map_mul, Units.mul_inv, (ofPowerSeries ℤ L).map_one, mul_one, HahnSeries.single_mul_single, neg_add_cancel, mul_one]
            rfl
    have e := (eq_inv_of_mul_eq_one_right hprod).symm
    push_cast
    rw [← map_mul]
    exact e
  · simp

theorem coe_mem_R₀_of_mem_adjoin (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    {s : ↥K} (hs : s ∈ Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)) : ((s : ↥K) : LaurentSeries L) ∈ R₀ L := by
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx; subst hx
      obtain ⟨w, hw, -⟩ := exists_inv_j j hj
      exact mem_R₀_iff.mpr ⟨w, hw.symm⟩
  | algebraMap a => exact mem_R₀_iff.mpr ⟨PowerSeries.C (algebraMap A L a), (coe_algebraMap_eq (K := K) a).symm⟩
  | add x y _ _ hx hy => push_cast; exact Subring.add_mem _ hx hy
  | mul x y _ _ hx hy => push_cast; exact Subring.mul_mem _ hx hy

theorem coe_mem_R₀ (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) : ((f : ↥K) : LaurentSeries L) ∈ R₀ L := by
  classical
  have hf : IsIntegral ↥(Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)) (f : ↥K) := f.2
  obtain ⟨P, hPm, hP⟩ := hf
  set φ : ↥(Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)) →+* LaurentSeries L :=
    (K.val.toRingHom).comp (algebraMap ↥(Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)) ↥K) with hφ
  have hlifts : P.map φ ∈ Polynomial.lifts (algebraMap (PowerSeries L) (LaurentSeries L)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact coe_mem_R₀_of_mem_adjoin j hj (P.coeff n).2
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hPm.map φ)
  have hint : IsIntegral (PowerSeries L) (((f : ↥K) : LaurentSeries L)) := by
    refine ⟨Q, hQm, ?_⟩
    rw [← Polynomial.eval_map, hQ, Polynomial.eval_map, hφ,
      show ((f : ↥K) : LaurentSeries L) = K.val.toRingHom (f : ↥K) from rfl, ← Polynomial.hom_eval₂, hP, map_zero]
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := PowerSeries L) (K := LaurentSeries L)).mp hint
  exact ⟨y, hy⟩

omit [CharZero L] in
theorem bijective_rangeRestrict : Function.Bijective (algebraMap (PowerSeries L) (LaurentSeries L)).rangeRestrict :=
  ⟨fun x y h => by
    have := congrArg Subtype.val h
    exact (IsFractionRing.injective (PowerSeries L) (LaurentSeries L)) this,
   RingHom.rangeRestrict_surjective _⟩

noncomputable def θ (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* PowerSeries L :=
  (RingEquiv.ofBijective _ (bijective_rangeRestrict (L := L))).symm.toRingHom.comp
    (((K.val.toRingHom).comp (ModularCurve.TwoChart.chartAlgInf A (↥K) j).val.toRingHom).codRestrict (R₀ L)
      (fun f => coe_mem_R₀ (A := A) j hj f))

theorem ofPowerSeries_θ (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) :
    ofPowerSeries ℤ L (θ (A := A) j hj f) = ((f : ↥K) : LaurentSeries L) := by
  have h := (RingEquiv.ofBijective _ (bijective_rangeRestrict (L := L))).apply_symm_apply
    ((((K.val.toRingHom).comp (ModularCurve.TwoChart.chartAlgInf A (↥K) j).val.toRingHom).codRestrict (R₀ L)
      (fun f => coe_mem_R₀ (A := A) j hj f)) f)
  have h' := congrArg Subtype.val h
  rw [← LaurentSeries.coe_algebraMap]
  exact h'

noncomputable def ψL (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →ₐ[A] L :=
  { (PowerSeries.constantCoeff (R := L)).comp (θ (A := A) j hj) with
    commutes' := fun a => by
      have hθ : θ (A := A) j hj (algebraMap A _ a) = PowerSeries.C (algebraMap A L a) := by
        refine ofPowerSeries_injective (Γ := ℤ) (R := L) ?_
        rw [ofPowerSeries_θ]
        exact coe_algebraMap_eq (K := K) a
      show PowerSeries.constantCoeff (θ (A := A) j hj (algebraMap A _ a)) = algebraMap A L a
      rw [hθ, PowerSeries.constantCoeff_C] }

theorem ψL_apply (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) :
    ψL (A := A) j hj f = (((f : ↥K) : LaurentSeries L)).coeff 0 := by
  show PowerSeries.constantCoeff (θ (A := A) j hj f) = _
  rw [← ofPowerSeries_θ (A := A) j hj f, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, ofPowerSeries_apply_coeff]

theorem ψL_jInv (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ψL (A := A) j hj (ModularCurve.TwoChart.jInvChartInf A (↥K) j) = 0 := by
  obtain ⟨w, hw, hw0⟩ := exists_inv_j j hj
  rw [ψL_apply]
  change (((j⁻¹ : ↥K)) : LaurentSeries L).coeff 0 = 0
  rw [hw, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply, hw0]

theorem isIntegral_ψL (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) : IsIntegral A (ψL (A := A) j hj f) := by
  classical
  have hle : Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K) ≤ ModularCurve.TwoChart.chartAlgInf A (↥K) j :=
    ModularCurve.TwoChart.adjoin_le_chartAlg A (↥K) _
  set χ : ↥(Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)) →ₐ[A] L := (ψL (A := A) j hj).comp (Subalgebra.inclusion hle) with hχ
  have hχrange : ∀ (s : ↥K) (hs : s ∈ Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)), χ ⟨s, hs⟩ ∈ (algebraMap A L).range := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
        have hx' := hx
        rw [Set.mem_singleton_iff] at hx'
        subst hx'
        refine ⟨0, ?_⟩
        rw [map_zero]
        exact (ψL_jInv (A := A) j hj).symm
    | algebraMap a => exact ⟨a, (χ.commutes a).symm⟩
    | add x y hx hy hx' hy' =>
        have : χ ⟨x + y, Subalgebra.add_mem _ hx hy⟩ = χ ⟨x, hx⟩ + χ ⟨y, hy⟩ := by rw [← map_add]; rfl
        rw [this]; exact Subring.add_mem _ hx' hy'
    | mul x y hx hy hx' hy' =>
        have : χ ⟨x * y, Subalgebra.mul_mem _ hx hy⟩ = χ ⟨x, hx⟩ * χ ⟨y, hy⟩ := by rw [← map_mul]; rfl
        rw [this]; exact Subring.mul_mem _ hx' hy'

  obtain ⟨P, hPm, hP⟩ := (f.2 : IsIntegral ↥(Algebra.adjoin A ({(j : ↥K)⁻¹} : Set ↥K)) (f : ↥K))
  have hPB : Polynomial.eval₂ (Subalgebra.inclusion hle).toRingHom f P = 0 := by
    apply Subtype.ext
    rw [show ((Polynomial.eval₂ (Subalgebra.inclusion hle).toRingHom f P : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) : ↥K) =
      (ModularCurve.TwoChart.chartAlgInf A (↥K) j).val.toRingHom (Polynomial.eval₂ (Subalgebra.inclusion hle).toRingHom f P) from rfl,
      Polynomial.hom_eval₂]
    exact hP
  have hχP : Polynomial.eval₂ (χ : _ →+* L) (ψL (A := A) j hj f) P = 0 := by
    have := congrArg (ψL (A := A) j hj) hPB
    rw [map_zero, show (ψL (A := A) j hj) (Polynomial.eval₂ (Subalgebra.inclusion hle).toRingHom f P) =
      (ψL (A := A) j hj).toRingHom (Polynomial.eval₂ (Subalgebra.inclusion hle).toRingHom f P) from rfl, Polynomial.hom_eval₂] at this
    exact this
  have hlifts : P.map (χ : _ →+* L) ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact hχrange _ (P.coeff n).2
  obtain ⟨Q, hQ, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hPm.map _)
  refine ⟨Q, hQm, ?_⟩
  rw [← Polynomial.eval_map, hQ, Polynomial.eval_map]
  exact hχP

end CuspSection

namespace CuspSection

variable {L : Type} [Field L] [CharZero L]
variable {K : IntermediateField L (LaurentSeries L)}
variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
variable [Algebra A ↥K] [IsScalarTower A L ↥K]

theorem exists_eq (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) : ∃ a : A, algebraMap A L a = ψL (A := A) j hj f :=
  (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).mp (isIntegral_ψL (A := A) j hj f)

noncomputable def ψ (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A where
  toFun f := Classical.choose (exists_eq (A := A) j hj f)
  map_one' := IsFractionRing.injective A L (by rw [Classical.choose_spec (exists_eq (A := A) j hj 1), map_one, map_one])
  map_mul' f g := IsFractionRing.injective A L (by
    rw [Classical.choose_spec (exists_eq (A := A) j hj (f * g)), map_mul, map_mul,
      Classical.choose_spec (exists_eq (A := A) j hj f), Classical.choose_spec (exists_eq (A := A) j hj g)])
  map_zero' := IsFractionRing.injective A L (by rw [Classical.choose_spec (exists_eq (A := A) j hj 0), map_zero, map_zero])
  map_add' f g := IsFractionRing.injective A L (by
    rw [Classical.choose_spec (exists_eq (A := A) j hj (f + g)), map_add, map_add,
      Classical.choose_spec (exists_eq (A := A) j hj f), Classical.choose_spec (exists_eq (A := A) j hj g)])

theorem algebraMap_ψ (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j)) : algebraMap A L (ψ (A := A) j hj f) = ψL (A := A) j hj f :=
  Classical.choose_spec (exists_eq (A := A) j hj f)

end CuspSection

open CuspSection HahnSeries in
theorem solution
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    ∃ ψ : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A,
      (∀ a : A, ψ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) a) = a) ∧
      (∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j), ∀ k : ℤ, k < 0 → (((f : ↥K) : LaurentSeries L)).coeff k = 0) ∧
      (∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
        algebraMap A L (ψ f) = (((f : ↥K) : LaurentSeries L)).coeff 0) ∧
      ψ (ModularCurve.TwoChart.jInvChartInf A (↥K) j) = 0 := by
  classical
  refine ⟨ψ (A := A) j hj, fun a => ?_, fun f k hk => ?_, fun f => ?_, ?_⟩
  · apply IsFractionRing.injective A L
    rw [algebraMap_ψ]
    exact (ψL (A := A) j hj).commutes a
  · obtain ⟨y, hy⟩ := mem_R₀_iff.mp (coe_mem_R₀ (A := A) j hj f)
    rw [← hy]
    exact ModularCurve.ofPowerSeries_coeff_of_neg y hk
  · rw [algebraMap_ψ, ψL_apply]
  · apply IsFractionRing.injective A L
    rw [algebraMap_ψ, map_zero]
    exact ψL_jInv (A := A) j hj

#print axioms solution

end S_ModularCurve_exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq
end P2MW
export P2MW.S_ModularCurve_exists_ringHom_chartAlgInf_algebraMap_eq_coeff_zero_of_coe_eq_coeffEmb_jq (solution)
