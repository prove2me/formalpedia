-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d8ac67c2-1bbb-576a-b423-c17541f3dbcd

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve P2MW.S_ModularCurve_XHDRModelAtP_exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia.ModularCurve ModularCurve.XHDRLevel P2MW.S_ModularCurve_XHDRModelAtP_exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia.ModularCurve.XHDRLevel"
open scoped MatrixGroups TensorProduct

namespace ModularCurve p2m_export "ModularCurve" "XHDRModelAtP qExpFunctionFieldC jqModC" namespace XHDRLevel p2m_export "ModularCurve.XHDRLevel" "R toBase chartAlgInf ιInf fibre fibreMap overOfIso ΓM" end ModularCurve.XHDRLevel
p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in

theorem ModularCurve.XHDRLevel.fibreMap_comp_snd {p : ℕ} {Γ Γ' : Subgroup SL(2, ℤ)}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (φ : NeronModelInfra.SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  unfold fibreMap
  rw [pullback.lift_snd, Category.comp_id]

p2m_open_scoped "ModularCurve ModularCurve.XHDRLevel" in

theorem ModularCurve.XHDRLevel.fibreMap_comp_fst {p : ℕ} {Γ Γ' : Subgroup SL(2, ℤ)}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (φ : NeronModelInfra.SchemeHomOver (toBase p Γ hj) (toBase p Γ' hj)) {κ : Type} [CommRing κ] (toκ : R p →+* κ) :
    fibreMap φ toκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ φ.1 := by
  unfold fibreMap
  rw [pullback.lift_fst]

theorem includeRight_comp_algebraMap_eq_includeLeftRingHom_comp
    {R κ O : Type*} [CommRing R] [CommRing κ] [CommRing O] [Algebra R κ] [Algebra R O]
    (toκ : R →+* κ) (halg : algebraMap R κ = toκ) :
    (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom.comp (algebraMap R O) =
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O)).comp toκ := by
  refine RingHom.ext fun r => ?_
  show Algebra.TensorProduct.includeRight (algebraMap R O r) = Algebra.TensorProduct.includeLeftRingHom (toκ r)
  rw [← halg, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeLeftRingHom_apply]

theorem map_id_comp_includeRight {R κ O : Type*} [CommRing R] [CommRing κ] [CommRing O] [Algebra R κ] [Algebra R O]
    (σ : O ≃ₐ[R] O) :
    (Algebra.TensorProduct.map (AlgHom.id R κ) (σ : O →ₐ[R] O)).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := O)).toRingHom.comp σ.toRingEquiv.toRingHom := by
  refine RingHom.ext fun b => ?_
  show Algebra.TensorProduct.map (AlgHom.id R κ) (σ : O →ₐ[R] O) ((1 : κ) ⊗ₜ[R] b) = (1 : κ) ⊗ₜ[R] (σ b)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem map_id_comp_includeLeftRingHom {R κ O : Type*} [CommRing R] [CommRing κ] [CommRing O] [Algebra R κ] [Algebra R O]
    (σ : O →ₐ[R] O) :
    (Algebra.TensorProduct.map (AlgHom.id R κ) σ).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O)) =
      Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := O) := by
  refine RingHom.ext fun a => ?_
  show Algebra.TensorProduct.map (AlgHom.id R κ) σ (a ⊗ₜ[R] (1 : O)) = a ⊗ₜ[R] (1 : O)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem solution
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))}
    (𝔓 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) (IsLocalRing.ResidueField ↥A)]
    (halg : algebraMap (R p) (IsLocalRing.ResidueField ↥A) = (IsLocalRing.residue ↥A).comp ρ)
    (d : (ZMod M)ˣ)
    (σ : ↥(chartAlgInf p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj))
    (hdia : ιInf p (ΓM M H) hj ≫ (𝔓.dia d).hom =
      Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ ιInf p (ΓM M H) hj) :
    ∃ c' : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgInf p (ΓM M H) hj))) ⟶
        fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
      c' ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫
          ιInf p (ΓM M H) hj ∧
      c' ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgInf p (ΓM M H) hj)))) ∧
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (R p) (IsLocalRing.ResidueField ↥A)) (σ : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] _)).toRingHom) ≫ c' =
        c' ≫ fibreMap (overOfIso (𝔓.dia d) (𝔓.dia_over d)) ((IsLocalRing.residue ↥A).comp ρ) := by

  have hsq : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓM M H) hj))).toRingHom) ≫ ιInf p (ΓM M H) hj) ≫
        toBase p (ΓM M H) hj =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := (IsLocalRing.ResidueField ↥A)) (B := ↥(chartAlgInf p (ΓM M H) hj)))) ≫
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc]
    erw [TwoChartIntegralModel.ιInf_toBase]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact includeRight_comp_algebraMap_eq_includeLeftRingHom_comp _ halg
  refine ⟨pullback.lift _ _ hsq, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩

  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      map_id_comp_includeRight, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← hdia]
    rw [ModularCurve.XHDRLevel.fibreMap_comp_fst, pullback.lift_fst_assoc, Category.assoc]
    rfl
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      map_id_comp_includeLeftRingHom]
    rw [ModularCurve.XHDRLevel.fibreMap_comp_snd, pullback.lift_snd]

end S_ModularCurve_XHDRModelAtP_exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_chartInf_fibre_spec_map_tensor_comp_eq_comp_fibreMap_dia (solution)
