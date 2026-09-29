-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_chart_pair_fibreMap_atkinLehner_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/e8177ade-9938-5fcf-aa95-f70b6f285e94

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_chart_pair_fibreMap_atkinLehner_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups TensorProduct

universe u

namespace NodeWrapGen

section Chart
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (A : Type u) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X)
  (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (κ : Type u) [CommRing κ] [Algebra R κ]

include hι in

theorem exists_chart :
    ∃ c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      c ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom) ≫ ι ∧
      c ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, hι]; exact sq.w.symm
  exact ⟨pullback.lift _ _ hcompat, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

include hι in

theorem mem_range_chart
    (c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom) ≫ ι)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))))
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))
    (hx : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base x ∈ Set.range ι.base) :
    x ∈ Set.range c.base := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ι ≫ f) := by
    rw [hcsnd, hι]; exact sq
  have H : IsPullback c
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (pullback.fst _ _) ι :=
    IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip
  have hx' : x ∈ Set.range (pullback.fst (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))) ι).base := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨t, rfl⟩ := hx'
  exact ⟨H.isoPullback.inv.base t, by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst]⟩

end Chart

section Invol
variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
  (κ : Type u) [CommRing κ] [Algebra R κ]

theorem chart_comp_eq_specMap_tensor_comp_chart
    (w : TwoChartIntegralModel R F j ≅ TwoChartIntegralModel R F j)
    (theta : ↥(TwoChartIntegralModel.chartAlgFin R F j) ≃ₐ[R] ↥(TwoChartIntegralModel.chartAlgFin R F j))
    (hwchart : TwoChartIntegralModel.ιFin R F j ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ TwoChartIntegralModel.ιFin R F j)
    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(TwoChartIntegralModel.chartAlgFin R F j))) ⟶ pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(TwoChartIntegralModel.chartAlgFin R F j))).toRingHom) ≫ TwoChartIntegralModel.ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(TwoChartIntegralModel.chartAlgFin R F j)))))
    (wκ : pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))) ⟶
      pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hwκfst : wκ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ w.hom)
    (hwκsnd : wκ ≫ pullback.snd _ _ = pullback.snd _ _) :
    c ≫ wκ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id κ κ) theta.toAlgHom).toRingHom) ≫ c := by
  apply pullback.hom_ext
  · rw [Category.assoc, hwκfst, ← Category.assoc, hcfst, Category.assoc, hwchart, Category.assoc, hcfst,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
  · rw [Category.assoc, hwκsnd, hcsnd, Category.assoc, hcsnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun a => by simp [Algebra.TensorProduct.includeLeftRingHom_apply]

end Invol

end NodeWrapGen

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

    (w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (w_over : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    letI := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∃ (c₀ : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓN p M H hpM) hj))) ⟶
          fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (c : Spec (CommRingCat.of ((IsLocalRing.ResidueField ↥A) ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) ⟶
          fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      c₀ ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj))).toRingHom) ≫ ιFin p (ΓN p M H hpM) hj ∧
      c₀ ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓN p M H hpM) hj)))) ∧
      c ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫ ιFin p (ΓM M H) hj ∧
      c ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := R p) (A := IsLocalRing.ResidueField ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj)))) ∧
      c ≫ fibreMap (overOfIso w w_over) ((IsLocalRing.residue ↥A).comp ρ) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map
          (AlgHom.id (IsLocalRing.ResidueField ↥A) (IsLocalRing.ResidueField ↥A)) theta.toAlgHom).toRingHom) ≫ c := by
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra

  obtain ⟨c₀, h₁, h₂⟩ := NodeWrapGen.exists_chart (toBase p (ΓN p M H hpM) hj) ↥(chartAlgFin p (ΓN p M H hpM) hj)
    (ιFin p (ΓN p M H hpM) hj) (TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj))
    (IsLocalRing.ResidueField ↥A)
  obtain ⟨c, h₃, h₄⟩ := NodeWrapGen.exists_chart (toBase p (ΓM M H) hj) ↥(chartAlgFin p (ΓM M H) hj)
    (ιFin p (ΓM M H) hj) (TwoChartIntegralModel.ιFin_toBase (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj))
    (IsLocalRing.ResidueField ↥A)

  have hwfst : fibreMap (overOfIso w w_over) (algebraMap (R p) (IsLocalRing.ResidueField ↥A)) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ w.hom := by
    unfold XHDRLevel.fibreMap; rw [pullback.lift_fst]; rfl
  have hwsnd : fibreMap (overOfIso w w_over) (algebraMap (R p) (IsLocalRing.ResidueField ↥A)) ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
    unfold XHDRLevel.fibreMap; rw [pullback.lift_snd, Category.comp_id]
  exact ⟨c₀, c, h₁, h₂, h₃, h₄, NodeWrapGen.chart_comp_eq_specMap_tensor_comp_chart (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H))
    (jAt (ΓM M H) hj) (IsLocalRing.ResidueField ↥A) w theta hwchart c h₃ h₄ _ hwfst hwsnd⟩

end S_ModularCurve_XHDRLevel_exists_chart_pair_fibreMap_atkinLehner_eq
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_chart_pair_fibreMap_atkinLehner_eq (solution)
