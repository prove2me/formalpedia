-- Prove2me | solution 1 for ModularCurve.XHDRLevel.chart_comp_fibreMap_eq_specMap_tensor_comp_chart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/940f6cc4-6573-5dbf-aceb-7baa73cfaa3c

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_chart_comp_fibreMap_eq_specMap_tensor_comp_chart

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) {Γ Γ' : Subgroup SL(2, ℤ)} (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (φ : SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj))
    (ψ : ↥(chartAlgFin p Γ' hj) →ₐ[R p] ↥(chartAlgFin p Γ hj))
    (hφchart : ιFin p Γ hj ≫ φ.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ιFin p Γ' hj)
    (κ : Type) [CommRing κ] [Algebra (R p) κ]
    (c : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p Γ hj))) ⟶ fibre (Γ := Γ) (hj := hj) (algebraMap (R p) κ))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj))).toRingHom) ≫ ιFin p Γ hj)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ hj)))))
    (c' : Spec (CommRingCat.of (κ ⊗[R p] ↥(chartAlgFin p Γ' hj))) ⟶ fibre (Γ := Γ') (hj := hj) (algebraMap (R p) κ))
    (hc'fst : c' ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ' hj))).toRingHom) ≫ ιFin p Γ' hj)
    (hc'snd : c' ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ' hj))))) :
    c ≫ fibreMap φ (algebraMap (R p) κ) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) ψ).toRingHom) ≫ c' := by
  apply pullback.hom_ext
  ·
    rw [Category.assoc, Category.assoc, hc'fst]
    unfold fibreMap
    rw [pullback.lift_fst, reassoc_of% hcfst, hφchart, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
  ·
    rw [Category.assoc, Category.assoc, hc'snd]
    unfold fibreMap
    rw [pullback.lift_snd, reassoc_of% hcsnd, Category.comp_id, ← Spec.map_comp]
    congr 1
    change _ = CommRingCat.ofHom ((Algebra.TensorProduct.map (AlgHom.id κ κ) ψ).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := κ) (B := ↥(chartAlgFin p Γ' hj))))
    congr 1
    ext a
    simp [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul]

end S_ModularCurve_XHDRLevel_chart_comp_fibreMap_eq_specMap_tensor_comp_chart
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_chart_comp_fibreMap_eq_specMap_tensor_comp_chart (solution)
