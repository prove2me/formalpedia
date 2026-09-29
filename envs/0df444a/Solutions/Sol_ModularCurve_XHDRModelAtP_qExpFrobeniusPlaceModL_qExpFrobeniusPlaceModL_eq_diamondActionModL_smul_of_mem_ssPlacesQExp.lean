-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_diamondActionModL_smul_of_mem_ssPlacesQExp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/3c8453e6-ce42-5e3c-b9c7-6cd5364ab51e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_diamondActionModL_smul_of_mem_ssPlacesQExp

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_diamondActionModL_smul_of_mem_ssPlacesQExp.ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.fibreMap XHDRLevel.ΓN XHDRModelAtP ssPlacesQExp diamondActionModL infSubgroup qExpFunctionFieldC qExpFrobeniusPlaceModL jqModC"
namespace XHDRFrobSq
p2m_open "ModularCurve"

theorem fibreMap_comp_fibreMap {p : ℕ} {Γ : Subgroup SL(2, ℤ)}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (φ ψ : NeronModelInfra.SchemeHomOver (toBase p Γ hj) (toBase p Γ hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap φ toκ ≫ XHDRLevel.fibreMap ψ toκ =
      XHDRLevel.fibreMap (Γ := Γ) (Γ' := Γ) (hj := hj) ⟨φ.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, φ.2]⟩ toκ := by
  apply pullback.hom_ext
  · simp only [XHDRLevel.fibreMap, pullback.map, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc, Category.comp_id]
  · simp only [XHDRLevel.fibreMap, pullback.map, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id]

theorem fibreMap_congr {p : ℕ} {Γ Γ' : Subgroup SL(2, ℤ)}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (φ ψ : NeronModelInfra.SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) (h : φ.1 = ψ.1)
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    XHDRLevel.fibreMap φ toκ = XHDRLevel.fibreMap ψ toκ := by
  obtain ⟨φ, hφ⟩ := φ
  obtain ⟨ψ, hψ⟩ := ψ
  cases h
  rfl

end ModularCurve.XHDRFrobSq

open ModularCurve.XHDRFrobSq in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hdia0 : (∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P))
    (e : (ZMod (M / p))ˣ) (he : ((e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (y : Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM)))
    (hy : y ∈ ssPlacesQExp (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p) :
    qExpFrobeniusPlaceModL (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p
        (qExpFrobeniusPlaceModL (ResidueField ↥A) (XHDRLevel.ΓN p M H hpM) p y) =
      SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) e)) • y := by

  obtain ⟨d, hd⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM) e

  have hn : 𝔛.nodeEquiv A hA ρ hρ ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩) = ⟨y, hy⟩ :=
    Equiv.apply_symm_apply _ _
  obtain ⟨⟨h1, hpl1⟩, ⟨h0, hpl0⟩⟩ := 𝔛.node_pin A hA ρ hρ ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩)
  rw [hn] at hpl1 hpl0
  simp only [Subtype.coe_mk] at hpl1 hpl0
  have hx : (𝔛.comp A hA ρ hρ 0).base
        ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩)) =
      (𝔛.comp A hA ρ hρ 1).base
        ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩)) := by
    have h := congrArg (fun φ => φ.base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩)) (pullback.condition
      (f := 𝔛.comp A hA ρ hρ 0) (g := 𝔛.comp A hA ρ hρ 1))
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app] using h

  have hE1 := 𝔛.comp_w A hA ρ hρ
  have hww : XHDRLevel.fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ) ≫
      XHDRLevel.fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ) =
      XHDRLevel.fibreMap (overOfIso (𝔛.dia d) (𝔛.dia_over d)) ((IsLocalRing.residue ↥A).comp ρ) := by
    rw [fibreMap_comp_fibreMap]
    exact fibreMap_congr _ _ (𝔛.w_sq d (hd ▸ he)) _
  have hE2 : 𝔛.comp A hA ρ hρ 1 ≫ XHDRLevel.fibreMap (overOfIso 𝔛.w 𝔛.w_over) ((IsLocalRing.residue ↥A).comp ρ) =
      XHDRLevel.fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ) ≫
        𝔛.comp A hA ρ hρ 0 := by
    rw [← hE1, Category.assoc, hww, ← hd]
    exact 𝔛.comp_dia A hA ρ hρ 0 d

  have hx' : (𝔛.comp A hA ρ hρ 0).base
        ((XHDRLevel.fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
          ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩))) =
      (𝔛.comp A hA ρ hρ 1).base
        ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩)) := by
    have e2 := congrArg (fun φ => φ.base
      ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩))) hE2
    have e1 := congrArg (fun φ => φ.base
      ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩))) hE1
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e1 e2
    rw [← e2, ← hx, e1]
  obtain ⟨n', hn'0, hn'1⟩ := Scheme.Pullback.exists_preimage_pullback _ _ hx'
  obtain ⟨⟨h1', hpl1'⟩, ⟨h0', hpl0'⟩⟩ := 𝔛.node_pin A hA ρ hρ n'

  have hy' : ((𝔛.nodeEquiv A hA ρ hρ n' : ↥(ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p)) :
      Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y := by
    rw [← hpl1', ← hpl0]
    congr 1
    exact Subtype.ext (by simp only [hn'1])

  have hz₁' : (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base
      ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩))) =
      (pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩) := by
    have h := congrArg (fun φ => φ.base
      ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨y, hy⟩)))
      (IsIso.inv_hom_id (𝔛.efib A hA ρ hρ))
    simpa only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.id_base, TopCat.id_app] using h
  obtain ⟨hQ, hplQ⟩ := hdia0 e ⟨_, h1⟩
  have hFy' : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
      ((𝔛.nodeEquiv A hA ρ hρ n' : ↥(ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p)) :
        Place (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (ΓN p M H hpM))) =
      SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) e)) • y := by
    rw [← hpl0', ← hpl1, ← hplQ]
    congr 1
    refine Subtype.ext ?_
    simp only [hn'0]
    rw [hz₁']
  rw [← hy', hFy']

end S_ModularCurve_XHDRModelAtP_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_diamondActionModL_smul_of_mem_ssPlacesQExp
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_diamondActionModL_smul_of_mem_ssPlacesQExp (solution)
