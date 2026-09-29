-- Prove2me | solution 1 for ModularCurve.Period.exists_perfectPairing_parabolicHoms_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/3012aace-2035-52cb-bc67-582a6a13c0e1

import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange
p2m_attr_erase "instance" "ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

set_option autoImplicit false

open scoped MatrixGroups

namespace PeriodBaseChange

variable (Γ : Subgroup SL(2, ℤ))

abbrev PZ := ModularCurve.Period.parabolicHoms ℤ Γ ℤ

abbrev PR (R : Type*) [CommRing R] := ModularCurve.Period.parabolicHoms R Γ R

variable {Γ}

theorem isParabolicHom_postcomp {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) {φ : Additive Γ →+ A} (hφ : ModularCurve.Period.IsParabolicHom Γ φ) :
    ModularCurve.Period.IsParabolicHom Γ (f.comp φ) := by
  intro γ hγ
  rw [AddMonoidHom.comp_apply, hφ γ hγ, map_zero]

variable (Γ)

def castP (R : Type*) [CommRing R] : PZ Γ →+ PR Γ R where
  toFun z := ⟨(Int.castAddHom R).comp (z : Additive Γ →+ ℤ), isParabolicHom_postcomp _ z.2⟩
  map_zero' := by apply Subtype.ext; refine AddMonoidHom.ext fun a => ?_; simp
  map_add' z w := by apply Subtype.ext; refine AddMonoidHom.ext fun a => ?_; simp

@[scoped simp] theorem coe_castP (R : Type*) [CommRing R] (z : PZ Γ) :
    ((castP Γ R z : PR Γ R) : Additive Γ →+ R) = (Int.castAddHom R).comp (z : Additive Γ →+ ℤ) :=
  rfl

variable {Γ}

theorem adjoint_of_basis {ι : Type*} [Fintype ι] (R : Type*) [CommRing R]
    (bR : Module.Basis ι R (PR Γ R)) (b' : ι → PZ Γ)
    (hcastb : ∀ i, castP Γ R (b' i) = bR i)
    (B : PR Γ R →ₗ[R] PR Γ R →ₗ[R] R) (IP : PZ Γ →ₗ[ℤ] PZ Γ →ₗ[ℤ] ℤ)
    (hBcast : ∀ z w, B (castP Γ R z) (castP Γ R w) = ((IP z w : ℤ) : R))
    (T T' : PZ Γ →ₗ[ℤ] PZ Γ) (hadj : ∀ z w, IP (T z) w = IP z (T' w))
    (S S' : PR Γ R →ₗ[R] PR Γ R)
    (hS : ∀ z, S (castP Γ R z) = castP Γ R (T z)) (hS' : ∀ z, S' (castP Γ R z) = castP Γ R (T' z))
    (x' y' : PR Γ R) : B (S x') y' = B x' (S' y') := by
  have key : B.comp S = B.compl₂ S' := by
    refine LinearMap.ext_basis bR bR fun i j => ?_
    have e1 : B (S (castP Γ R (b' i))) (castP Γ R (b' j)) = ((IP (T (b' i)) (b' j) : ℤ) : R) := by
      rw [hS, hBcast]
    have e2 : B (castP Γ R (b' i)) (S' (castP Γ R (b' j))) = ((IP (b' i) (T' (b' j)) : ℤ) : R) := by
      rw [hS', hBcast]
    rw [hcastb, hcastb] at e1 e2
    show B (S (bR i)) (bR j) = B (bR i) (S' (bR j))
    rw [e1, e2, hadj]
  exact LinearMap.congr_fun₂ key x' y'

set_option maxHeartbeats 1600000 in

theorem main [Γ.FiniteIndex] (IP : PZ Γ →ₗ[ℤ] PZ Γ →ₗ[ℤ] ℤ)
    (hbij : Function.Bijective IP) (hbijf : Function.Bijective IP.flip)
    (R : Type*) [CommRing R] [IsAddTorsionFree R] :
    ∃ B : PR Γ R →ₗ[R] PR Γ R →ₗ[R] R,
      Function.Bijective B ∧ Function.Bijective B.flip ∧
      (∀ (x y : PZ Γ) (x' y' : PR Γ R),
        ((x' : PR Γ R) : Additive Γ →+ R) = (Int.castAddHom R).comp ((x : PZ Γ) : Additive Γ →+ ℤ) →
        ((y' : PR Γ R) : Additive Γ →+ R) = (Int.castAddHom R).comp ((y : PZ Γ) : Additive Γ →+ ℤ) →
        B x' y' = (IP x y : R)) ∧
      (∀ (T T' : PZ Γ →ₗ[ℤ] PZ Γ) (S S' : PR Γ R →ₗ[R] PR Γ R),
        (∀ x y : PZ Γ, IP (T x) y = IP x (T' y)) →
        (∀ (x : PZ Γ) (x' : PR Γ R),
          ((x' : PR Γ R) : Additive Γ →+ R) = (Int.castAddHom R).comp ((x : PZ Γ) : Additive Γ →+ ℤ) →
          ((S x' : PR Γ R) : Additive Γ →+ R) = (Int.castAddHom R).comp ((T x : PZ Γ) : Additive Γ →+ ℤ)) →
        (∀ (x : PZ Γ) (x' : PR Γ R),
          ((x' : PR Γ R) : Additive Γ →+ R) = (Int.castAddHom R).comp ((x : PZ Γ) : Additive Γ →+ ℤ) →
          ((S' x' : PR Γ R) : Additive Γ →+ R) = (Int.castAddHom R).comp ((T' x : PZ Γ) : Additive Γ →+ ℤ)) →
        ∀ x' y' : PR Γ R, B (S x') y' = B x' (S' y')) := by
  classical

  obtain ⟨n, b', hb'⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree Γ
  obtain ⟨bR, hbR⟩ := hb' R
  have hcastb : ∀ i, castP Γ R (b' i) = bR i := fun i => Subtype.ext (hbR i).symm
  have hIP_surj : Function.Surjective IP := hbij.2
  have hIP_surjf : Function.Surjective IP.flip := hbijf.2

  obtain ⟨B, hBb⟩ : ∃ B : PR Γ R →ₗ[R] PR Γ R →ₗ[R] R,
      ∀ i j, B (bR i) (bR j) = ((IP (b' i) (b' j) : ℤ) : R) :=
    ⟨bR.constr R fun i => bR.constr R fun j => ((IP (b' i) (b' j) : ℤ) : R), fun i j => by
      simp only [Module.Basis.constr_basis]⟩

  have hBcast : ∀ z w : PZ Γ, B (castP Γ R z) (castP Γ R w) = ((IP z w : ℤ) : R) := by
    let L₁ : PZ Γ →ₗ[ℤ] PZ Γ →ₗ[ℤ] R :=
      LinearMap.mk₂ ℤ (fun z w => B (castP Γ R z) (castP Γ R w))
        (fun z z' w => by simp only [map_add, LinearMap.add_apply])
        (fun c z w => by simp only [map_zsmul, LinearMap.smul_apply])
        (fun z w w' => by simp only [map_add])
        (fun c z w => by simp only [map_zsmul])
    let L₂ : PZ Γ →ₗ[ℤ] PZ Γ →ₗ[ℤ] R :=
      LinearMap.mk₂ ℤ (fun z w => ((IP z w : ℤ) : R))
        (fun z z' w => by simp only [map_add, LinearMap.add_apply, Int.cast_add])
        (fun c z w => by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul])
        (fun z w w' => by simp only [map_add, Int.cast_add])
        (fun c z w => by simp only [map_smul, smul_eq_mul, Int.cast_mul, zsmul_eq_mul])
    have hL : L₁ = L₂ := by
      refine LinearMap.ext_basis b' b' fun i j => ?_
      show B (castP Γ R (b' i)) (castP Γ R (b' j)) = ((IP (b' i) (b' j) : ℤ) : R)
      rw [hcastb, hcastb, hBb]
    intro z w
    exact LinearMap.congr_fun₂ hL z w

  have hc : ∀ j, ∃ c : PZ Γ, ∀ i, IP c (b' i) = if i = j then 1 else 0 := by
    intro j
    obtain ⟨c, hc⟩ := hIP_surj (b'.coord j)
    refine ⟨c, fun i => ?_⟩
    rw [hc, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  choose c hc using hc
  have hc' : ∀ i, ∃ c' : PZ Γ, ∀ j, IP (b' j) c' = if j = i then 1 else 0 := by
    intro i
    obtain ⟨c', hc'⟩ := hIP_surjf (b'.coord i)
    refine ⟨c', fun j => ?_⟩
    rw [show IP (b' j) c' = IP.flip c' (b' j) from rfl, hc']
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  choose c' hc' using hc'

  have hBcb : ∀ (z : PZ Γ) (i : Fin n), B (castP Γ R z) (bR i) = ((IP z (b' i) : ℤ) : R) := by
    intro z i; rw [← hcastb, hBcast]
  have hBbc : ∀ (i : Fin n) (w : PZ Γ), B (bR i) (castP Γ R w) = ((IP (b' i) w : ℤ) : R) := by
    intro i w; rw [← hcastb, hBcast]
  have hBinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).mpr fun x' h0 => ?_
    rw [← bR.sum_repr x'] at h0 ⊢
    have hcoef : ∀ i, bR.repr x' i = 0 := by
      intro i
      have := LinearMap.congr_fun h0 (castP Γ R (c' i))
      simpa only [map_sum, LinearMap.sum_apply, LinearMap.zero_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, hBbc, hc', Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true] using this
    exact Finset.sum_eq_zero fun i _ => by rw [hcoef i, zero_smul]
  have hBsurj : Function.Surjective B := by
    intro f
    refine ⟨∑ j, f (bR j) • castP Γ R (c j), ?_⟩
    refine bR.ext fun i => ?_
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hBcb, hc,
      Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hBfinj : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).mpr fun y' h0 => ?_
    rw [← bR.sum_repr y'] at h0 ⊢
    have hcoef : ∀ j, bR.repr y' j = 0 := by
      intro j
      have := LinearMap.congr_fun h0 (castP Γ R (c j))
      simpa only [map_sum, LinearMap.sum_apply, LinearMap.zero_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, LinearMap.flip_apply, hBcb, hc, Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using this
    exact Finset.sum_eq_zero fun j _ => by rw [hcoef j, zero_smul]
  have hBfsurj : Function.Surjective B.flip := by
    intro f
    refine ⟨∑ i, f (bR i) • castP Γ R (c' i), ?_⟩
    refine bR.ext fun j => ?_
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.flip_apply, hBbc, hc', Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨B, ⟨hBinj, hBsurj⟩, ⟨hBfinj, hBfsurj⟩, ?_, ?_⟩
  ·
    intro x y x' y' hx' hy'
    have hx : x' = castP Γ R x := Subtype.ext hx'
    have hy : y' = castP Γ R y := Subtype.ext hy'
    rw [hx, hy, hBcast]
  ·
    intro T T' S S' hadj hS hS' x' y'
    have hS1 : ∀ z, S (castP Γ R z) = castP Γ R (T z) := fun z => Subtype.ext (hS z _ rfl)
    have hS'1 : ∀ z, S' (castP Γ R z) = castP Γ R (T' z) := fun z => Subtype.ext (hS' z _ rfl)
    exact adjoint_of_basis R bR (fun i => b' i) hcastb B IP hBcast T T' hadj S S' hS1 hS'1 x' y'

end PeriodBaseChange
p2m_reactivate "P2MW.S_ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange.PeriodBaseChange"

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (IP : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ℤ)
    (hIP : Function.Bijective IP) (hIPf : Function.Bijective IP.flip)
    (R : Type*) [CommRing R] [IsAddTorsionFree R] :
    ∃ B : ModularCurve.Period.parabolicHoms R Γ R →ₗ[R] ModularCurve.Period.parabolicHoms R Γ R →ₗ[R] R,
      Function.Bijective B ∧ Function.Bijective B.flip ∧
      (∀ (x y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x' y' : ModularCurve.Period.parabolicHoms R Γ R),
        ((x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
          (Int.castAddHom R).comp ((x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
        ((y' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
          (Int.castAddHom R).comp ((y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
        B x' y' = (IP x y : R)) ∧
      (∀ (T T' : ModularCurve.Period.parabolicHoms ℤ Γ ℤ →ₗ[ℤ] ModularCurve.Period.parabolicHoms ℤ Γ ℤ)
          (S S' : ModularCurve.Period.parabolicHoms R Γ R →ₗ[R] ModularCurve.Period.parabolicHoms R Γ R),
        (∀ x y : ModularCurve.Period.parabolicHoms ℤ Γ ℤ, IP (T x) y = IP x (T' y)) →
        (∀ (x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x' : ModularCurve.Period.parabolicHoms R Γ R),
          ((x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
          ((S x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((T x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ)) →
        (∀ (x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (x' : ModularCurve.Period.parabolicHoms R Γ R),
          ((x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ) →
          ((S' x' : ModularCurve.Period.parabolicHoms R Γ R) : Additive Γ →+ R) =
            (Int.castAddHom R).comp ((T' x : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) : Additive Γ →+ ℤ)) →
        ∀ x' y' : ModularCurve.Period.parabolicHoms R Γ R, B (S x') y' = B x' (S' y')) :=
  PeriodBaseChange.main IP hIP hIPf R

end S_ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange
end P2MW
export P2MW.S_ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange (solution)
