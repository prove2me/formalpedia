-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.mem_adjoin_of_pow_eq_one_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:01:48.023965+00:00
-- url     : https://prove2.me/submissions/29ff6c4b-c9e5-4463-a2f3-173bebbbf1e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open Polynomial
namespace GlobalTheory.UnitLemma.Unr
theorem _root_.solution {R F L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {z : L} {N : ℕ} (hN : IsUnit (N : R)) (hz : z ^ N = 1) (hadj : Algebra.adjoin F {z} = ⊤)
    {y : L} (hy : IsIntegral R y) : y ∈ Algebra.adjoin R {z} := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hzR : IsIntegral R z := by
    refine ⟨X ^ N - C 1, monic_X_pow_sub_C 1 hN0, ?_⟩
    simp [eval₂_sub, hz]
  have hzF : IsIntegral F z := hzR.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzF hadj
  have hgen : pb.gen = z := PowerBasis.ofAdjoinEqTop_gen hzF hadj
  have hmem := Algebra.discr_mul_isIntegral_mem_adjoin F (R := R) (B := pb) (hint := by rw [hgen]; exact hzR) (hz := hy)
  rw [hgen] at hmem
  haveI : Module.IsTorsionFree R L := .of_smul_eq_zero fun r x hx => by
    rw [Algebra.smul_def, mul_eq_zero, IsScalarTower.algebraMap_apply R F L,
      map_eq_zero_iff _ (algebraMap F L).injective, IsFractionRing.to_map_eq_zero_iff] at hx
    exact hx
  have hIntAe : ∀ p : R[X], IsIntegral R (aeval z p) := fun p =>
    adjoin_le_integralClosure hzR (aeval_mem_adjoin_singleton R z)
  set m := minpoly R z with hm
  obtain ⟨h, hmh⟩ : m ∣ X ^ N - C 1 :=
    minpoly.isIntegrallyClosed_dvd hzR (by simp [hz])
  have hder : (N : L) * z ^ (N - 1) = aeval z (derivative m) * aeval z h := by
    have := congrArg (fun p => aeval z (derivative p)) hmh
    simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add, map_mul] at this
    have h0 : aeval z m = 0 := minpoly.aeval R z
    simpa [h0] using this
  have hint : ∀ x : L, IsIntegral R x → ∃ r : R, algebraMap R F r = Algebra.norm F x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm F hx)
  obtain ⟨ra, hra⟩ := hint _ (hIntAe (derivative m))
  obtain ⟨rb, hrb⟩ := hint _ (hIntAe h)
  obtain ⟨rz, hrz⟩ := hint _ hzR
  have hinj := IsFractionRing.injective R F
  have hrzN : rz ^ N = 1 := hinj (by rw [map_pow, hrz, ← map_pow, hz, map_one, map_one])
  have hprod : ra * rb = (N : R) ^ Module.finrank F L * rz ^ (N - 1) := by
    apply hinj
    have hNL : ((N : L)) = algebraMap F L (N : F) := (map_natCast _ _).symm
    rw [map_mul, hra, hrb, ← map_mul, ← hder, map_mul, map_pow (Algebra.norm F), hNL,
      Algebra.norm_algebraMap, map_mul, map_pow, map_pow, hrz, map_natCast]
  have hra_unit : IsUnit ra := by
    have : IsUnit (ra * rb) := by
      rw [hprod]
      have hrzu : IsUnit rz := isUnit_iff_exists_inv.2 ⟨rz ^ (N - 1), by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN0), hrzN]⟩
      exact (hN.pow _).mul (hrzu.pow _)
    exact isUnit_of_mul_isUnit_left this
  have hdisc : Algebra.discr F pb.basis = algebraMap R F ((-1) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) := by
    rw [Algebra.discr_powerBasis_eq_norm, map_mul, hra, map_pow, map_neg, map_one, hgen,
      minpoly.isIntegrallyClosed_eq_field_fractions' F hzR, derivative_map, aeval_map_algebraMap]
  obtain ⟨v, hv⟩ : IsUnit ((-1 : R) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) :=
    ((isUnit_one.neg).pow _).mul hra_unit
  rw [hdisc, ← hv, algebraMap_smul] at hmem
  have : y = (↑v⁻¹ : R) • ((v : R) • y) := by rw [smul_smul, Units.inv_mul, one_smul]
  rw [this]
  exact Subalgebra.smul_mem _ hmem _
end GlobalTheory.UnitLemma.Unr
