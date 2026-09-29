-- Prove2me | solution 1 for ModularCurve.XHDRLevel.mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d9b6285e-102e-5b6b-8209-9f6c4960940a

import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss

set_option autoImplicit false

open scoped MatrixGroups TensorProduct
open IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel

namespace Ws47
namespace GaussG

open ModularCurve

theorem coeffMap_single_zero_mul {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : R) (x : LaurentSeries R) :
    coeffMap f (HahnSeries.single 0 a * x) = HahnSeries.single 0 (f a) * coeffMap f x := by
  rw [map_mul, coeffMap_single]

end Ws47.GaussG

open Ws47.GaussG in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)
    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (Rg : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hgauss : ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hres : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ Rg.integers,
          ((Rg.residue ⟨_, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y) :
    (∀ t : ↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj), γ t ∈ Rg.integers) ∧
    (∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      ∃ h : γ (a ⊗ₜ b) ∈ Rg.integers,
        ((Rg.residue ⟨γ (a ⊗ₜ b), h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
          IsLocalRing.residue ↥A a • coeffMap ((IsLocalRing.residue ↥A).comp ρ) y) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hRQ : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap (R p) ℚ) = A.subtype.comp ρ := by
    rw [hρ]
    exact (IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ)).symm

  have key : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffMap A.subtype (HahnSeries.single 0 a * coeffMap ρ y) := by
    intro a b y hy
    rw [hγ a b, ← hy, coeffMap_single_zero_mul, coeffMap_coeffMap, ← hRQ, ← coeffMap_coeffMap,
      HahnSeries.single_zero_mul_eq_smul]
    rfl
  have main : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)) (y : LaurentSeries (R p)),
      coeffMap (algebraMap (R p) ℚ) y = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) →
      ∃ h : γ (a ⊗ₜ b) ∈ Rg.integers,
        ((Rg.residue ⟨γ (a ⊗ₜ b), h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
          IsLocalRing.residue ↥A a • coeffMap ((IsLocalRing.residue ↥A).comp ρ) y := by
    intro a b y hy
    have e := key a b y hy
    have hmemF : coeffMap A.subtype (HahnSeries.single 0 a * coeffMap ρ y) ∈ xHFunctionFieldBar M H := by
      rw [← e]; exact (γ (a ⊗ₜ b)).2
    obtain ⟨h, hr⟩ := hres _ hmemF
    have eel : (⟨coeffMap A.subtype (HahnSeries.single 0 a * coeffMap ρ y), hmemF⟩ : ↥(xHFunctionFieldBar M H)) = γ (a ⊗ₜ b) :=
      Subtype.ext e.symm
    have hmem : γ (a ⊗ₜ b) ∈ Rg.integers := eel ▸ h
    refine ⟨hmem, ?_⟩
    have eint : (⟨γ (a ⊗ₜ b), hmem⟩ : Rg.integers) = ⟨_, h⟩ := Subtype.ext eel.symm
    rw [eint, hr, coeffMap_single_zero_mul, coeffMap_coeffMap, HahnSeries.single_zero_mul_eq_smul]
  refine ⟨?_, main⟩

  intro t
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a b =>
    obtain ⟨y, hy⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
      (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt _ hj)).1 b
    exact (main a b y hy).1
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

end S_ModularCurve_XHDRLevel_mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_mem_integers_and_residue_tmul_eq_smul_coeffMap_of_regularProlongation_gauss (solution)
