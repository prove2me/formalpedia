-- Prove2me | solution 1 for ModularCurve.DRModelPackage.iotaFin_mem_smoothLocus_of_aeval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5876157a-4289-58c5-9914-ff51127d5402

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_ModularCurve_HpoolLevelRing
import Theorems.Thm_ModularCurve_DRModelPackage_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_iotaFin_mem_smoothLocus_of_aeval_mem
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve AlgebraicGeometry.RelPicard

namespace ZSmooth
section L1
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem mem_smoothLocus_of_mem_basicOpen (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (y : ↥(DRModel p))
    (hy : (DRModel.toBase p).base y ∈ (PrimeSpectrum.basicOpen ((p : ℕ) : ℤ) : Set (PrimeSpectrum ℤ))) :
    y ∈ 𝔛.smoothLocus := by

  let loc := Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away ((p : ℕ) : ℤ))))
  haveI : IsOpenImmersion loc := IsOpenImmersion.of_isLocalization ((p : ℕ) : ℤ)
  let g := pullback.fst (DRModel.toBase p) loc
  haveI : IsOpenImmersion g := inferInstance
  haveI hsm : Smooth (pullback.snd (DRModel.toBase p) loc) := 𝔛.smooth_away

  let U : (DRModel p).Opens := g.opensRange
  have hU : Smooth (U.ι ≫ DRModel.toBase p) := by
    have h1 : U.ι = g.isoOpensRange.inv ≫ g := by
      rw [Iso.eq_inv_comp, Scheme.Hom.isoOpensRange_hom_ι]
    have h : U.ι ≫ DRModel.toBase p = g.isoOpensRange.inv ≫ pullback.snd (DRModel.toBase p) loc ≫ loc := by
      rw [h1, Category.assoc]
      erw [pullback.condition]
    rw [h]
    infer_instance
  have hle := 𝔛.smoothLocus_maximal U hU

  have hrange : (DRModel.toBase p).base y ∈ Set.range loc.base := by
    rw [show Set.range loc.base = (PrimeSpectrum.basicOpen ((p : ℕ) : ℤ) : Set (PrimeSpectrum ℤ)) from
      PrimeSpectrum.localization_away_comap_range (Localization.Away ((p : ℕ) : ℤ)) ((p : ℕ) : ℤ)]
    exact hy
  obtain ⟨s, hs⟩ := hrange
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := DRModel.toBase p) (g := loc) y s hs.symm
  have hyU : y ∈ U := ⟨w, hw⟩
  exact hle hyU

end L1

section L4
p2m_open "Polynomial AlgebraicGeometry.Polynomial"

theorem not_le_of_mem_of_aeval_mem {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime) (Pz : Ideal A) (v : A) (hv : v ∈ Pz)
    (g : ℤ[X]) (hg0 : ¬ (p : ℤ) ∣ g.eval 0) (𝔮 : Ideal A) [𝔮.IsPrime]
    (hp𝔮 : ((p : ℕ) : A) ∈ 𝔮) (hg𝔮 : aeval v g ∈ 𝔮) : ¬ Pz ≤ 𝔮 := by
  intro hle
  have hv𝔮 : v ∈ 𝔮 := hle hv

  have hdvd : (X : ℤ[X]) ∣ g - C (g.eval 0) := by
    rw [X_dvd_iff, coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero, sub_self]
  obtain ⟨h, hh⟩ := hdvd
  have hev : aeval v g = algebraMap ℤ A (g.eval 0) + v * aeval v h := by
    have := congrArg (aeval v) hh
    rw [map_sub, aeval_C, map_mul, aeval_X] at this
    rw [← sub_eq_iff_eq_add'] ; exact this
  have hg0𝔮 : (algebraMap ℤ A (g.eval 0)) ∈ 𝔮 := by
    have h1 : algebraMap ℤ A (g.eval 0) = aeval v g - v * aeval v h := by rw [hev]; ring
    rw [h1]
    exact 𝔮.sub_mem hg𝔮 (𝔮.mul_mem_right _ hv𝔮)

  have hcop : IsCoprime (p : ℤ) (g.eval 0) :=
    (Int.prime_iff_natAbs_prime.mpr (by simpa using hp) |> Prime.irreducible).coprime_iff_not_dvd.mpr hg0
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : A) ∈ 𝔮 := by
    have := congrArg (algebraMap ℤ A) hab
    rw [map_add, map_mul, map_mul, map_one, map_natCast] at this
    rw [← this]
    exact 𝔮.add_mem (𝔮.mul_mem_left _ hp𝔮) (𝔮.mul_mem_left _ hg0𝔮)
  exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr h1)

end L4

section Geom

theorem charP_of_ringHom_apply_eq_zero {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (φ : ℤ →+* K)
    (h : φ p = 0) : CharP K p := by
  have : ((p : ℕ) : K) = 0 := by rw [← map_natCast φ p]; exact h
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr this

theorem exists_geometricPoint_over (p : ℕ) [Fact p.Prime] (y : ↥(DRModel p))
    (hy : ((p : ℕ) : ℤ) ∈ ((DRModel.toBase p).base y).asIdeal) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k p) (_ : IsAlgClosed k)
      (y' : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))),
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y' = y := by
  classical

  let κ : Type := ↥((DRModel p).residueField y)
  let z := (DRModel.toBase p).base y
  have hφ : ((DRModel.toBase p).residueFieldMap y)
      ((Spec (CommRingCat.of ℤ)).Γevaluation z ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv (p : ℤ))) = 0 := by
    have h0 : (Spec (CommRingCat.of ℤ)).Γevaluation z ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv (p : ℤ)) = 0 := by
      rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, basicOpen_eq_of_affine]
      intro hz
      exact (show ((p : ℕ) : ℤ) ∉ z.asIdeal from hz) hy
    rw [h0, map_zero]
  let φ : ℤ →+* κ := ((DRModel.toBase p).residueFieldMap y).hom.comp
    (((Spec (CommRingCat.of ℤ)).Γevaluation z).hom.comp ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom))
  have hφp : φ p = 0 := hφ
  haveI : CharP κ p := charP_of_ringHom_apply_eq_zero p φ (by exact_mod_cast hφp)

  let k : Type := AlgebraicClosure κ
  haveI : CharP k p := charP_of_injective_algebraMap (algebraMap κ k).injective p

  let a : Spec (CommRingCat.of k) ⟶ DRModel p :=
    Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ (DRModel p).fromSpecResidueField y
  have ha : a ≫ DRModel.toBase p = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) :=
    specZIsTerminal.hom_ext _ _
  refine ⟨k, inferInstance, inferInstance, inferInstance,
    (pullback.lift a (𝟙 _) ha).base (IsLocalRing.closedPoint k), ?_⟩
  have hcomp : pullback.lift a (𝟙 _) ha ≫ pullback.fst _ _ = a := pullback.lift_fst _ _ _
  have hpt := congrArg (fun g => g.base (IsLocalRing.closedPoint k)) hcomp
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hpt
  refine hpt.trans ?_
  change (Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ (DRModel p).fromSpecResidueField y).base _ = y
  rw [Scheme.Hom.comp_base, TopCat.comp_app]
  exact Scheme.fromSpecResidueField_apply _ _

end Geom

section L5

theorem toBase_ιFin_apply_asIdeal (p : ℕ) [Fact p.Prime] [NeZero p]
    (𝔮 : PrimeSpectrum ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) :
    ((DRModel.toBase p).base
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮)).asIdeal =
      Ideal.comap (algebraMap ℤ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
        𝔮.asIdeal := by
  rw [← TopCat.comp_app, ← Scheme.Hom.comp_base]
  change ((AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ≫
      AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮).asIdeal = _
  rw [AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase, Spec.map_base]
  rfl

theorem natCast_mem_toBase_ιFin_apply_asIdeal_iff (p : ℕ) [Fact p.Prime] [NeZero p]
    (𝔮 : PrimeSpectrum ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (n : ℕ) :
    ((n : ℕ) : ℤ) ∈ ((DRModel.toBase p).base
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮)).asIdeal ↔
      ((n : ℕ) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) ∈ 𝔮.asIdeal := by
  rw [toBase_ιFin_apply_asIdeal, Ideal.mem_comap, map_natCast]

end L5
end ZSmooth

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (v : HpoolLevelRing.Afin p)
    (hdict : ∀ (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
      (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
      (𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p)),
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y =
        (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 →
      v ∉ 𝔮.asIdeal →
      y ∈ Set.range (𝔛.compInf k).base ∧ y ∉ Set.range (𝔛.compZero k).base)
    (g : Polynomial ℤ) (hg0 : ¬ (p : ℤ) ∣ g.coeff 0)
    (𝔮 : PrimeSpectrum (HpoolLevelRing.Afin p)) (hg : Polynomial.aeval v g ∈ 𝔮.asIdeal) :
    (AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(ModularCurve.modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮 ∈ 𝔛.smoothLocus := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  by_cases hp𝔮 : ((p : ℕ) : HpoolLevelRing.Afin p) ∈ 𝔮.asIdeal
  ·
    have hv : v ∉ 𝔮.asIdeal := by
      intro hv
      have hg0' : ¬ (p : ℤ) ∣ g.eval 0 := by rwa [← Polynomial.coeff_zero_eq_eval_zero]
      exact ZSmooth.not_le_of_mem_of_aeval_mem p Fact.out (Ideal.span {v}) v (Ideal.subset_span (Set.mem_singleton v))
        g hg0' 𝔮.asIdeal hp𝔮 hg ((Ideal.span_singleton_le_iff_mem _).mpr hv)
    have hp' : ((p : ℕ) : ℤ) ∈ ((DRModel.toBase p).base
        ((AlgebraicCurve.TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).base 𝔮)).asIdeal :=
      (ZSmooth.natCast_mem_toBase_ιFin_apply_asIdeal_iff p 𝔮 p).mpr hp𝔮
    obtain ⟨k, _, _, _, y', hy'⟩ := ZSmooth.exists_geometricPoint_over p _ hp'
    obtain ⟨hyI, hyZ⟩ := hdict k y' 𝔮 hy' hv
    have h := (ModularCurve.DRModelPackage.mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf p 𝔛 k y' hyI hyZ).1
    rwa [hy'] at h
  ·
    refine ZSmooth.mem_smoothLocus_of_mem_basicOpen p 𝔛 _ ?_
    show ((p : ℕ) : ℤ) ∉ ((DRModel.toBase p).base _).asIdeal
    rwa [ZSmooth.natCast_mem_toBase_ιFin_apply_asIdeal_iff p 𝔮 p]

end S_ModularCurve_DRModelPackage_iotaFin_mem_smoothLocus_of_aeval_mem
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_iotaFin_mem_smoothLocus_of_aeval_mem (solution)
