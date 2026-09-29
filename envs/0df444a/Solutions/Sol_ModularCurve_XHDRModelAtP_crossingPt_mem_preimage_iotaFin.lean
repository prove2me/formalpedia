-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.crossingPt_mem_preimage_iotaFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/6bef6975-6900-5735-8609-40eb330a51a3

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_iotaInf_mem_range_iotaFin_iff
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_crossingPt_mem_preimage_iotaFin

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

set_option maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] (ρO : R p →+* O)
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).base (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ∈ Set.range (ιFin p (ΓM M H) hj).base := by
  classical
  haveI : Fact p.Prime := inferInstance

  set z : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) :=
    (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) with hz
  have hx : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).base (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) = (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base z := by
    show ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ) ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).base n = _
    rw [Category.assoc, Category.assoc, bcMap_fst]; rfl
  rw [hx]

  set y₀ : ↥(fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n with hy₀
  have hfin₀ : (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y₀ ∈ Set.range (ιFin p (ΓN p M H hpM) hj).base := by

    obtain ⟨-, ⟨hc, hplace⟩⟩ := 𝔛.node_pin A hA ρ hρ n
    haveI := 𝔛.Mfib_chart_nonempty A hA ρ hρ
    set v : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) := (𝔛.nodeEquiv A hA ρ hρ n).1 with hv
    have hvss : v ∈ ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p := (𝔛.nodeEquiv A hA ρ hρ n).2

    obtain ⟨xj, a, hxj, hval, -⟩ := (mem_ssPlacesQExp_iff v).mp hvss
    have hxjv : xj ∈ v.toValuationSubring := hval.mem

    have hfrob : qExpFrobeniusModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p xj = xj ^ p := by
      apply Subtype.ext
      rw [coe_qExpFrobeniusModL, hxj, SubmonoidClass.coe_pow, hxj]
      refine qExpand_eq_pow_of_coeff_fixed (IsLocalRing.ResidueField ↥A) p _ (fun k => ?_)
      rw [← map_jqModC (Int.castRingHom (IsLocalRing.ResidueField ↥A)), HahnSeries.map_coeff, Int.coe_castRingHom]
      have h := map_intCast (frobenius (IsLocalRing.ResidueField ↥A) p) ((jqModC ℤ).coeff k)
      rwa [frobenius_def] at h
    have hxjw : xj ∈ (qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p v).toValuationSubring := by
      rw [mem_qExpFrobeniusPlaceModL_iff, hfrob]
      exact pow_mem hxjv p

    have hread := 𝔛.Mfib_pin A hA ρ hρ (jChartFin p (ΓN p M H hpM) hj) (jqModC ↥A) (by
      show (jqModC ↥A).map A.subtype = (((jChartFin p (ΓN p M H hpM) hj : ↥(chartAlgFin p (ΓN p M H hpM) hj)) :
        ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
      rw [map_jqModC, show (((jChartFin p (ΓN p M H hpM) hj : ↥(chartAlgFin p (ΓN p M H hpM) hj)) :
        ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ) = jqModC ℚ from rfl, map_jqModC])
    rw [show coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC (IsLocalRing.ResidueField ↥A) from map_jqModC _] at hread

    have heq := Subtype.ext (hread.trans hxj.symm)
    have key := AlgebraicCurve.TwoChartIntegralModel.mem_range_iotaFin_of_ffEquiv_symm_germ_mem_placeOfPoint
      (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) (𝔛.Mfib A hA ρ hρ)
      (𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
      (hMne := 𝔛.Mfib_chart_nonempty A hA ρ hρ) ⟨_, hc⟩ (by
        rw [hplace]
        rw [heq]
        exact hxjw)

    have e1 : (𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base ((inv (𝔛.efib A hA ρ hρ)).base y₀) = (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y₀ := by
      rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (inv _), IsIso.inv_hom_id]; rfl
    rw [← e1]; exact key

  have hπ : (𝔛.π.1).base ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base z) = (pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base y₀ := by
    have hmap : fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) = pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ≫ 𝔛.π.1 := by
      rw [fibreMap]; erw [pullback.lift_fst]
    have h1 : (fibreMap 𝔛.π ((IsLocalRing.residue ↥A).comp ρ)).base z = y₀ := by
      rw [hz, ← Scheme.Hom.comp_apply, 𝔛.comp_pi A hA ρ hρ]; rfl
    rw [← Scheme.Hom.comp_apply, ← hmap, Scheme.Hom.comp_apply, h1]

  by_contra hnot
  obtain ⟨𝔮, hj𝔮, h𝔮⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_jInvChartInf_mem_and_iotaInf_eq_of_not_mem_range_iotaFin
    (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) _ hnot
  have hπq : (𝔛.π.1).base ((pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base z) =
      (ιInf p (ΓN p M H hpM) hj).base (PrimeSpectrum.comap (𝔛.iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →+* ↥(chartAlgInf p (ΓM M H) hj)) 𝔮) := by
    rw [← h𝔮, ← Scheme.Hom.comp_apply, 𝔛.pi_chartInf, Scheme.Hom.comp_apply]; rfl

  have hjinv : 𝔛.iotaInf (TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj)) =
      TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) := by
    apply Subtype.ext; apply Subtype.ext
    rw [𝔛.iotaInf_spec]
    simp [TwoChartIntegralModel.coe_jInvChartInf]
  have hmem : TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) ∈
      (PrimeSpectrum.comap (𝔛.iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →+* ↥(chartAlgInf p (ΓM M H) hj)) 𝔮).asIdeal := by
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    show 𝔛.iotaInf _ ∈ 𝔮.asIdeal
    rw [hjinv]; exact hj𝔮
  have hoff := (not_congr (AlgebraicCurve.TwoChartIntegralModel.iotaInf_mem_range_iotaFin_iff (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))
    (jAt (ΓN p M H hpM) hj) (PrimeSpectrum.comap (𝔛.iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →+* ↥(chartAlgInf p (ΓM M H) hj)) 𝔮))).mpr (not_not.mpr hmem)
  apply hoff
  rw [← hπq, hπ]; exact hfin₀

end S_ModularCurve_XHDRModelAtP_crossingPt_mem_preimage_iotaFin
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_crossingPt_mem_preimage_iotaFin (solution)
