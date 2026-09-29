-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.ofAlgAut_smul_ofAlgAut_smul_eq_ofAlgAut_diamondAutHBar_inv_smul_of_unitsMap_mul_eq_one_prolongationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/27f0cc80-b317-58b4-bff6-c9d8b253582d

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_ofAlgAut_smul_ofAlgAut_smul_eq_ofAlgAut_diamondAutHBar_inv_smul_of_unitsMap_mul_eq_one_prolongationDatum

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace Ws49PlaceWsq

theorem exists_point_comp_eq
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔛 : XHDRModelAtP p M H hpM hj) (g : X p (ΓM M H) hj ⟶ X p (ΓM M H) hj) (hg : g ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) :
    ∃ y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ g := by
  haveI := 𝔛.eeta_iso
  have hcond : (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ g) ≫ toBase p (ΓM M H) hj =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [Category.assoc, Category.assoc, Category.assoc, hg, pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta,
      ← Category.assoc, y.2]
  let q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) :=
    pullback.lift (y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ g) (𝟙 _) hcond
  refine ⟨⟨q ≫ inv 𝔛.eeta, ?_⟩, ?_⟩
  · rw [Category.assoc, ← 𝔛.heeta, IsIso.inv_hom_id_assoc, pullback.lift_snd]
  · show (q ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

end Ws49PlaceWsq

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : (∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    SemilinearAut.ofAlgAut θ • (SemilinearAut.ofAlgAut θ • W) = (SemilinearAut.ofAlgAut (diamondAutHBar M H d))⁻¹ • W := by
  clear hcomp Rpd hδ hpb hα_coe hα hβ

  obtain ⟨y₀, rfl⟩ := 𝔛.Meta.pointEquivPlace.surjective W

  have hwinv : 𝔛.w.inv ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj := by
    rw [Iso.inv_comp_eq, 𝔛.w_over]
  obtain ⟨y₁, hy₁⟩ := Ws49PlaceWsq.exists_point_comp_eq 𝔛 𝔛.w.inv hwinv y₀
  obtain ⟨y₂, hy₂⟩ := Ws49PlaceWsq.exists_point_comp_eq 𝔛 𝔛.w.inv hwinv y₁
  have h₁ : 𝔛.Meta.pointEquivPlace y₁ = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y₀ := by
    apply hwgen y₀ y₁
    rw [reassoc_of% hy₁]
    simp only [Iso.inv_hom_id, Category.comp_id]
  have h₂ : 𝔛.Meta.pointEquivPlace y₂ = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y₁ := by
    apply hwgen y₁ y₂
    rw [reassoc_of% hy₂]
    simp only [Iso.inv_hom_id, Category.comp_id]

  have hsq := 𝔛.w_sq d hd
  have h₃ : 𝔛.Meta.pointEquivPlace y₀ = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔛.Meta.pointEquivPlace y₂ := by
    apply 𝔛.dia_generic d y₂ y₀
    rw [← hsq, reassoc_of% hy₂, reassoc_of% hy₁]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h₁, ← h₂, h₃, inv_smul_smul]

end S_ModularCurve_XHDRModelAtP_ofAlgAut_smul_ofAlgAut_smul_eq_ofAlgAut_diamondAutHBar_inv_smul_of_unitsMap_mul_eq_one_prolongationDatum
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_ofAlgAut_smul_ofAlgAut_smul_eq_ofAlgAut_diamondAutHBar_inv_smul_of_unitsMap_mul_eq_one_prolongationDatum (solution)
