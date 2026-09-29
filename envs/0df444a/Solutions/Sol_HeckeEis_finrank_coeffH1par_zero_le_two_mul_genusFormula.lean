-- Prove2me | solution 1 for HeckeEis.finrank_coeffH1par_zero_le_two_mul_genusFormula
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8eb9a271-e577-5325-8f4f-e4386cc8dea8

import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_PeriodMap

import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_castAddHom_comp
import Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_genusFormula
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_finrank_coeffH1par_zero_le_two_mul_genusFormula
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "mem_coeffCocycles_iff mem_coeffCoboundaries_iff coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff BinaryForm binarySubst binarySubst_C binaryFormRepSL"
namespace N0Sol
p2m_open "HeckeEis"

open MvPolynomial CongruenceSubgroup ModularCurve.Period

variable (N : ℕ)

abbrev ρ0 : Representation ℂ (Gamma0 N) ↥(BinaryForm ℂ 0) := (binaryFormRepSL ℂ 0).comp (Gamma0 N).subtype

theorem coe_eq_C (P : ↥(BinaryForm ℂ 0)) : (P : MvPolynomial (Fin 2) ℂ) = C (coeff 0 (P : MvPolynomial (Fin 2) ℂ)) := by
  have hP : (P : MvPolynomial (Fin 2) ℂ).IsHomogeneous 0 := (mem_homogeneousSubmodule 0 _).mp P.2
  ext d
  rw [coeff_C]
  split_ifs with hd
  · rw [← hd]
  · by_contra h
    have hw := hP h
    have hdeg : d.degree = 0 := by rw [Finsupp.degree_eq_weight_one]; exact hw
    rw [Finsupp.degree_eq_zero_iff] at hdeg
    exact hd hdeg.symm

theorem ext0 {P Q : ↥(BinaryForm ℂ 0)} (h : coeff 0 (P : MvPolynomial (Fin 2) ℂ) = coeff 0 (Q : MvPolynomial (Fin 2) ℂ)) :
    P = Q := by
  apply Subtype.ext
  rw [coe_eq_C P, coe_eq_C Q, h]

theorem rho0_apply (g : Gamma0 N) (P : ↥(BinaryForm ℂ 0)) : ρ0 N g P = P := by
  apply Subtype.ext
  show binarySubst ℂ (((g : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) ℂ) = P
  conv_lhs => rw [coe_eq_C P]
  rw [binarySubst_C, ← coe_eq_C P]

variable {N}

def toHom (z : ↥(coeffParabolicCocycles (ρ0 N))) : Additive (Gamma0 N) →+ ℂ where
  toFun a := coeff 0 (((z : Gamma0 N → ↥(BinaryForm ℂ 0)) (Additive.toMul a) : ↥(BinaryForm ℂ 0)) : MvPolynomial (Fin 2) ℂ)
  map_zero' := by
    have h := (mem_coeffCocycles_iff (ρ0 N) _).mp z.2.1 1 1
    rw [mul_one, rho0_apply] at h

    have h0 : (z : Gamma0 N → ↥(BinaryForm ℂ 0)) 1 = 0 := by
      have := congrArg (fun v => v - (z : Gamma0 N → ↥(BinaryForm ℂ 0)) 1) h
      have h0' : (0 : ↥(BinaryForm ℂ 0)) = (z : Gamma0 N → ↥(BinaryForm ℂ 0)) 1 := by simpa using this
      exact h0'.symm
    show coeff 0 (((z : Gamma0 N → ↥(BinaryForm ℂ 0)) 1 : ↥(BinaryForm ℂ 0)) : MvPolynomial (Fin 2) ℂ) = 0
    rw [h0]; rfl
  map_add' a b := by
    show coeff 0 (((z : Gamma0 N → ↥(BinaryForm ℂ 0)) (Additive.toMul a * Additive.toMul b) : ↥(BinaryForm ℂ 0)) : MvPolynomial (Fin 2) ℂ)
      = coeff 0 (((z : Gamma0 N → ↥(BinaryForm ℂ 0)) (Additive.toMul a) : ↥(BinaryForm ℂ 0)) : MvPolynomial (Fin 2) ℂ)
        + coeff 0 (((z : Gamma0 N → ↥(BinaryForm ℂ 0)) (Additive.toMul b) : ↥(BinaryForm ℂ 0)) : MvPolynomial (Fin 2) ℂ)
    rw [(mem_coeffCocycles_iff (ρ0 N) _).mp z.2.1, rho0_apply, Submodule.coe_add, coeff_add]

@[scoped simp] theorem toHom_apply (z : ↥(coeffParabolicCocycles (ρ0 N))) (g : Gamma0 N) :
    toHom z (Additive.ofMul g) = coeff 0 (((z : Gamma0 N → ↥(BinaryForm ℂ 0)) g : ↥(BinaryForm ℂ 0)) : MvPolynomial (Fin 2) ℂ) := rfl

theorem toHom_mem (z : ↥(coeffParabolicCocycles (ρ0 N))) : toHom z ∈ parabolicHoms ℂ (Gamma0 N) ℂ := by
  intro γ hγ
  rw [toHom_apply]
  obtain ⟨u, hu⟩ := z.2.2 γ hγ
  rw [LinearMap.sub_apply, Module.End.one_apply, rho0_apply, sub_self] at hu
  rw [← hu]; rfl

def φ : ↥(coeffParabolicCocycles (ρ0 N)) →ₗ[ℂ] ↥(parabolicHoms ℂ (Gamma0 N) ℂ) where
  toFun z := ⟨toHom z, toHom_mem z⟩
  map_add' z w := by
    apply Subtype.ext; apply AddMonoidHom.ext; intro a
    show coeff 0 ((((z + w : ↥(coeffParabolicCocycles (ρ0 N))) : Gamma0 N → ↥(BinaryForm ℂ 0)) (Additive.toMul a) : ↥(BinaryForm ℂ 0)) : MvPolynomial (Fin 2) ℂ) = _
    rw [Submodule.coe_add, Pi.add_apply, Submodule.coe_add, coeff_add]
    rfl
  map_smul' c z := by
    apply Subtype.ext; apply AddMonoidHom.ext; intro a
    show coeff 0 ((((c • z : ↥(coeffParabolicCocycles (ρ0 N))) : Gamma0 N → ↥(BinaryForm ℂ 0)) (Additive.toMul a) : ↥(BinaryForm ℂ 0)) : MvPolynomial (Fin 2) ℂ) = _
    rw [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_smul, coeff_smul]
    rfl

theorem φ_apply_coe (z : ↥(coeffParabolicCocycles (ρ0 N))) (g : Gamma0 N) :
    ((φ z : ↥(parabolicHoms ℂ (Gamma0 N) ℂ)) : Additive (Gamma0 N) →+ ℂ) (Additive.ofMul g)
      = coeff 0 (((z : Gamma0 N → ↥(BinaryForm ℂ 0)) g : ↥(BinaryForm ℂ 0)) : MvPolynomial (Fin 2) ℂ) := rfl

theorem φ_injective : Function.Injective (φ (N := N)) := by
  intro z w h
  apply Subtype.ext; funext g
  apply ext0
  have := congrArg (fun ψ : ↥(parabolicHoms ℂ (Gamma0 N) ℂ) => (ψ : Additive (Gamma0 N) →+ ℂ) (Additive.ofMul g)) h
  simpa [φ_apply_coe] using this

theorem eq_of_mk_eq {a b : ↥(coeffParabolicCocycles (ρ0 N))} (h : coeffH1parMk _ a = coeffH1parMk _ b) : a = b := by
  rw [← sub_eq_zero, ← map_sub, coeffH1parMk_eq_zero_iff, mem_coeffCoboundaries_iff] at h
  obtain ⟨v, hv⟩ := h
  rw [← sub_eq_zero]
  apply Subtype.ext; funext g
  have := congrFun hv g
  rw [rho0_apply, sub_self] at this
  rw [← this]; rfl

def Ψ : coeffH1par (ρ0 N) →ₗ[ℂ] ↥(parabolicHoms ℂ (Gamma0 N) ℂ) where
  toFun x := φ (Function.surjInv (coeffH1parMk_surjective (ρ0 N)) x)
  map_add' x y := by
    rw [← map_add]
    congr 1
    apply eq_of_mk_eq
    rw [map_add, Function.surjInv_eq (coeffH1parMk_surjective _), Function.surjInv_eq (coeffH1parMk_surjective _),
      Function.surjInv_eq (coeffH1parMk_surjective _)]
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    apply eq_of_mk_eq
    rw [map_smul, Function.surjInv_eq (coeffH1parMk_surjective _), Function.surjInv_eq (coeffH1parMk_surjective _)]

theorem Ψ_mk (z : ↥(coeffParabolicCocycles (ρ0 N))) : Ψ (coeffH1parMk _ z) = φ z := by
  show φ (Function.surjInv (coeffH1parMk_surjective (ρ0 N)) (coeffH1parMk _ z)) = φ z
  congr 1
  apply eq_of_mk_eq
  rw [Function.surjInv_eq (coeffH1parMk_surjective _)]

theorem Ψ_injective : Function.Injective (Ψ (N := N)) := by
  intro x y h
  obtain ⟨a, rfl⟩ := coeffH1parMk_surjective _ x
  obtain ⟨b, rfl⟩ := coeffH1parMk_surjective _ y
  rw [Ψ_mk, Ψ_mk] at h
  rw [φ_injective h]

end HeckeEis.N0Sol
p2m_reactivate "P2MW.S_HeckeEis_finrank_coeffH1par_zero_le_two_mul_genusFormula.HeckeEis P2MW.S_HeckeEis_finrank_coeffH1par_zero_le_two_mul_genusFormula.HeckeEis.N0Sol"
p2m_reactivate "P2MW.S_HeckeEis_finrank_coeffH1par_zero_le_two_mul_genusFormula.HeckeEis"

end
p2m_reactivate "P2MW.S_HeckeEis_finrank_coeffH1par_zero_le_two_mul_genusFormula.HeckeEis P2MW.S_HeckeEis_finrank_coeffH1par_zero_le_two_mul_genusFormula.HeckeEis.N0Sol"

theorem solution (N : ℕ) [NeZero N] :
    (Module.finrank ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ 0).comp (CongruenceSubgroup.Gamma0 N).subtype)) : ℚ)
      ≤ 2 * ModularCurve.genusFormula N := by
  obtain ⟨t, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_castAddHom_comp (CongruenceSubgroup.Gamma0 N)
  obtain ⟨bK, -⟩ := hb ℂ
  haveI : FiniteDimensional ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ) := Module.Finite.of_basis bK
  have h1 : Module.finrank ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ 0).comp (CongruenceSubgroup.Gamma0 N).subtype))
      ≤ Module.finrank ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ) :=
    LinearMap.finrank_le_finrank_of_injective (HeckeEis.N0Sol.Ψ_injective (N := N))
  have h2 := ModularCurve.finrank_parabolicHoms_le_two_mul_genusFormula N ℂ
  calc (Module.finrank ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ 0).comp (CongruenceSubgroup.Gamma0 N).subtype)) : ℚ)
      ≤ Module.finrank ℂ ↥(ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ) := by exact_mod_cast h1
    _ ≤ 2 * ModularCurve.genusFormula N := h2

#print axioms solution

end S_HeckeEis_finrank_coeffH1par_zero_le_two_mul_genusFormula
end P2MW
export P2MW.S_HeckeEis_finrank_coeffH1par_zero_le_two_mul_genusFormula (solution)
