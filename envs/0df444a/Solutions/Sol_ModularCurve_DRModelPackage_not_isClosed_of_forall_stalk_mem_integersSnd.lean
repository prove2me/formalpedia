-- Prove2me | solution 1 for ModularCurve.DRModelPackage.not_isClosed_of_forall_stalk_mem_integersSnd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9b0f4bca-be3b-5a5d-9a5d-9b91ee2f6b24

import Mathlib
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_residue_jFun_sub_jQFun_sub
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_not_isClosed_of_forall_stalk_mem_integersSnd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_not_isClosed_of_forall_stalk_mem_integersSnd.AlgebraicGeometry"
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackage_not_isClosed_of_forall_stalk_mem_integersSnd.AlgebraicGeometry IsLocalRing Polynomial AlgebraicGeometry.Polynomial"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.fromSpecResidueField Spec.map_apply IsProper Scheme.toSpecΓ_naturality_assoc Scheme.Hom LocallyOfFiniteType Spec IsIntegral Scheme.Opens.toScheme Spec.map Scheme isClosed_singleton_iff_isClosedImmersion Scheme.Hom.naturality IsClosedImmersion HasRingHomProperty.Spec_iff SpecMap_ΓSpecIso_hom Spec.map_id Scheme.fromSpecResidueField_apply Scheme.Opens Scheme.fromSpecStalk_toSpecΓ_assoc HasRingHomProperty Scheme.Hom.comp_apply Scheme.ΓSpecIso"
p2m_open "AlgebraicGeometry"

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "fromSpecResidueField germToFunctionField toSpecΓ_naturality_assoc Hom Γ Opens.toScheme functionField Hom.naturality residueField fromSpecResidueField_apply Opens residue fromSpecStalk_toSpecΓ_assoc residue_surjective restrict Hom.comp_apply ΓSpecIso" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.exists_monic_eval₂_mem_maximalIdeal_of_isClosed_singleton
    {O : Type u} [CommRing O] [IsLocalRing O] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of O)) [LocallyOfFiniteType f]
    (c : X) (hc : IsClosed ({c} : Set X)) (hcO : f.base c = IsLocalRing.closedPoint O)
    (s : X.presheaf.stalk c) :
    ∃ g : Polynomial O, g.Monic ∧
      Polynomial.eval₂ ((X.presheaf.germ ⊤ c trivial).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)) s g ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk c) := by
  classical

  set θ : CommRingCat.of O ⟶ X.presheaf.stalk c :=
    (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ c trivial with hθ
  have hθhom : θ.hom = (X.presheaf.germ ⊤ c trivial).hom.comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom) := rfl
  rw [← hθhom]
  let ψ : CommRingCat.of O ⟶ X.residueField c := θ ≫ X.residue c

  have hψ : Spec.map ψ = X.fromSpecResidueField c ≫ f := by
    simp only [ψ, hθ, Scheme.fromSpecResidueField, Spec.map_comp, Category.assoc]
    congr 1
    rw [← Scheme.fromSpecStalk_toSpecΓ_assoc, ← Scheme.toSpecΓ_naturality_assoc,
      ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

  haveI : IsClosedImmersion (X.fromSpecResidueField c) :=
    isClosed_singleton_iff_isClosedImmersion.mp hc
  haveI : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  have hft : ψ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance

  have hker : ∀ a ∈ IsLocalRing.maximalIdeal O, ψ.hom a = 0 := by
    intro a ha
    have hpt : (Spec.map ψ).base (closedPoint (X.residueField c)) = closedPoint O := by
      rw [hψ, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hcO]
    rw [Spec.map_apply] at hpt
    have hmem : ψ.hom a ∈ (closedPoint (X.residueField c)).asIdeal := by
      have : a ∈ (PrimeSpectrum.comap ψ.hom (closedPoint (X.residueField c))).asIdeal := by
        rw [hpt]; exact ha
      simpa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] using this
    by_contra hne
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_iff_ne_zero.mpr hne)

  let ψbar : ResidueField O →+* X.residueField c :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) ψ.hom hker
  have hψbar : ψbar.comp (IsLocalRing.residue O) = ψ.hom := Ideal.Quotient.lift_comp_mk _ _ _
  have hft' : ψbar.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := IsLocalRing.residue O)
    rw [hψbar]; exact hft
  letI : Algebra (ResidueField O) (X.residueField c) := ψbar.toAlgebra
  haveI : Algebra.FiniteType (ResidueField O) (X.residueField c) := hft'
  haveI : Module.Finite (ResidueField O) (X.residueField c) :=
    finite_of_finite_type_of_isJacobsonRing _ _

  have hint : _root_.IsIntegral (ResidueField O) ((X.residue c).hom s) :=
    Algebra.IsIntegral.isIntegral _
  obtain ⟨gbar, hgm, hg0⟩ := hint
  obtain ⟨g, hgmap, -, hgmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := IsLocalRing.residue O) IsLocalRing.residue_surjective gbar)
    hgm
  refine ⟨g, hgmonic, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  change (X.residue c).hom (Polynomial.eval₂ θ.hom s g) = 0
  rw [Polynomial.hom_eval₂, ← CommRingCat.hom_comp]
  change Polynomial.eval₂ ψ.hom _ g = 0
  rw [← hψbar, ← Polynomial.eval₂_map, hgmap]
  exact hg0

end AlgebraicGeometry

theorem glue_block
    (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    [hneF : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    [hneI : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))] :
    ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))).hom
        (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) *
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))).hom
        (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) = 1 := by
  classical

  let F := ↥(modularFunctionFieldFull p)
  let j₀ := IgusaScheme.jFull p
  let X := pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
  let fst : X ⟶ DRModel p := pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
  let U : (DRModel p).Opens := (TwoChartIntegralModel.ιFin ℤ F j₀) ''ᵁ ⊤
  let V : (DRModel p).Opens := (TwoChartIntegralModel.ιInf ℤ F j₀) ''ᵁ ⊤

  have key := TwoChartIntegralModel.TwoChartsAux.res_f_mul_res_g ℤ F j₀
  have key' := congrArg (fst.app (U ⊓ V)).hom key
  rw [map_mul, map_one] at key'

  have n1 : ∀ (W W' : (DRModel p).Opens) (h : W' ≤ W) (s : Γ(DRModel p, W)),
      (fst.app W').hom (((DRModel p).presheaf.map (homOfLE h).op).hom s) =
        (X.presheaf.map (homOfLE (show fst ⁻¹ᵁ W' ≤ fst ⁻¹ᵁ W from fun x hx => h hx)).op).hom ((fst.app W).hom s) := by
    intro W W' h s
    have := Scheme.Hom.naturality fst (homOfLE h).op
    have h2 := congrArg (fun φ => φ.hom s) this
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    exact h2
  rw [n1 U (U ⊓ V) inf_le_left, n1 V (U ⊓ V) inf_le_right] at key'

  obtain ⟨⟨xF, hxF⟩⟩ := hneF
  obtain ⟨⟨xI, hxI⟩⟩ := hneI
  have hηU : genericPoint X ∈ fst ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (fst ⁻¹ᵁ U).isOpen).mpr ⟨xF, Set.mem_univ _, hxF⟩
  have hηV : genericPoint X ∈ fst ⁻¹ᵁ V :=
    ((genericPoint_spec X).mem_open_set_iff (fst ⁻¹ᵁ V).isOpen).mpr ⟨xI, Set.mem_univ _, hxI⟩
  have hηW : genericPoint X ∈ fst ⁻¹ᵁ (U ⊓ V) := ⟨hηU, hηV⟩

  have key'' := congrArg (X.presheaf.germ (fst ⁻¹ᵁ (U ⊓ V)) (genericPoint X) hηW).hom key'
  rw [map_mul, map_one] at key''
  erw [TopCat.Presheaf.germ_res_apply X.presheaf _ (genericPoint X) hηW,
    TopCat.Presheaf.germ_res_apply X.presheaf _ (genericPoint X) hηW] at key''
  exact key''

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)
    (c : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hcO : (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base c = IsLocalRing.closedPoint O)
    (hdom : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk c,
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) s) ∈ R.R₂.integers)
    (hdom' : ∀ s ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk c),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) s) ∈ R.R₂.integers.nonunits) :
    ¬ IsClosed ({c} : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) := by
  classical
  intro hcl
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let X : Scheme := (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
  let FB := ↥(modularFunctionFieldBar (1 * p))
  let V := R.R₂.integers
  let Fbar := ↥(modularFunctionFieldFullC (IsLocalRing.ResidueField ↥A) 1)

  haveI : IsProper (DRModel.toBase p) := 𝔛.isProper
  haveI : IsProper (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := MorphismProperty.pullback_snd _ _ inferInstance

  let θ₀ : X.presheaf.stalk c →+* ↥V :=
    ((φ.comp (algebraMap (X.presheaf.stalk c) ↥X.functionField)).codRestrict V.toSubring (fun s => hdom s))
  let θ : X.presheaf.stalk c →+* ↥(modularFunctionFieldC k 1) := R.residue₂.comp θ₀
  have hθ : ∀ s, θ s = R.residue₂ ⟨φ (algebraMap _ ↥X.functionField s), hdom s⟩ := fun s => rfl

  have hθm : ∀ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk c), θ s = 0 := by
    intro s hs
    rw [hθ, ProlongationTuple.residue₂_apply]
    have : R.R₂.residue ⟨φ (algebraMap _ ↥X.functionField s), hdom s⟩ = 0 := by
      rw [← RingHom.mem_ker, R.R₂.ker_residue]
      exact (ValuationSubring.coe_mem_nonunits_iff (a := (⟨_, hdom s⟩ : ↥V))).mp (hdom' s hs)
    rw [this, map_zero]

  let cst : O →+* X.presheaf.stalk c :=
    (X.presheaf.germ ⊤ c trivial).hom.comp ((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)
  let toA : O →+* ↥A := (ιK.comp (algebraMap O K)).codRestrict A.toSubring (fun a => hιA a)
  let ρk : O →+* k := red.comp toA
  have hqN : ¬ p ∣ 1 := fun h => (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp h)
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨c, trivial⟩⟩
  have hgerm : ∀ (U : X.Opens) [Nonempty U] (y : X) (hy : y ∈ U) (s : Γ(X, U)),
      algebraMap (X.presheaf.stalk y) ↥X.functionField ((X.presheaf.germ U y hy).hom s) = (X.germToFunctionField U).hom s := by
    intro U _ y hy s
    show (X.presheaf.germ U y hy ≫ X.presheaf.stalkSpecializes (genericPoint_specializes y)).hom s = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]

  have hres2const : ∀ (a : ↥A) (hm : algebraMap (AlgebraicClosure ℚ) FB (a : AlgebraicClosure ℚ) ∈ V),
      R.residue₂ ⟨_, hm⟩ = algebraMap k ↥(modularFunctionFieldC k 1) (red a) := by
    intro a hm
    obtain ⟨-, h₂, -, -, -, e2, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN a
    obtain ⟨-, h₂', -, -, -, e2', -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : ↥A)
    have : (⟨_, hm⟩ : ↥V) = ⟨_, h₂'⟩ - ⟨_, h₂⟩ := Subtype.ext (by
      rw [AddSubgroupClass.coe_sub]; push_cast; ring)
    rw [this, map_sub, e2, e2', map_zero, map_zero, sub_zero, sub_sub_cancel]
  have hconst : ∀ a : O, θ (cst a) = algebraMap k ↥(modularFunctionFieldC k 1) (ρk a) := by
    intro a
    rw [hθ]
    have e1 : φ (algebraMap _ ↥X.functionField (cst a)) = algebraMap (AlgebraicClosure ℚ) FB (ιK (algebraMap O K a)) := by
      rw [← hφO a]
      show φ (algebraMap _ ↥X.functionField ((X.presheaf.germ ⊤ c trivial).hom _)) = φ (algebraMap _ ↥X.functionField ((X.presheaf.germ ⊤ x trivial).hom _))
      rw [hgerm, hgerm]
      rfl
    have e2 : (⟨φ (algebraMap _ ↥X.functionField (cst a)), hdom _⟩ : ↥V) =
        ⟨algebraMap (AlgebraicClosure ℚ) FB ((toA a : ↥A) : AlgebraicClosure ℚ), (R.R₂.algebraMap_mem_iff _).mpr (toA a).2⟩ :=
      Subtype.ext e1
    rw [e2, hres2const]
    rfl
  have hθcst : θ.comp cst = (algebraMap k ↥(modularFunctionFieldC k 1)).comp ρk := RingHom.ext hconst

  have hjV : ∃ h : (ProlongationTuple.jFun 1 p : FB) ∈ V, R.residue₂ ⟨_, h⟩ = jGeomGen k 1 ^ p := by
    obtain ⟨-, h₂, -, -, -, e2, -, -⟩ := R.residue_jFun_sub_jQFun_sub hqN (0 : ↥A)
    have e : (ProlongationTuple.jFun 1 p : FB) - algebraMap (AlgebraicClosure ℚ) FB ((0 : ↥A) : AlgebraicClosure ℚ) = ProlongationTuple.jFun 1 p := by
      rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
    have key : ∀ (f : FB) (hf : (ProlongationTuple.jFun 1 p : FB) - algebraMap (AlgebraicClosure ℚ) FB ((0 : ↥A) : AlgebraicClosure ℚ) = f)
        (h' : f ∈ V), R.residue₂ ⟨f, h'⟩ = jGeomGen k 1 ^ p := by
      rintro f rfl h'
      rw [e2, map_zero, map_zero, sub_zero]
    exact ⟨e ▸ h₂, key _ e _⟩
  obtain ⟨hjmem, hjres⟩ := hjV
  have hjtr : Transcendental k (jqModC k) := ModularCurve.transcendental_jqModC _

  have finish : ∀ (w : X.presheaf.stalk c), θ w = jGeomGen k 1 ^ p ∨ θ w * jGeomGen k 1 ^ p = 1 → False := by
    intro w hw
    obtain ⟨g, hgmon, hgm⟩ := Scheme.exists_monic_eval₂_mem_maximalIdeal_of_isClosed_singleton (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) c hcl hcO w
    have h0 : θ (Polynomial.eval₂ cst w g) = 0 := hθm _ hgm
    rw [Polynomial.hom_eval₂, hθcst, ← Polynomial.eval₂_map] at h0
    have hint' : IsIntegral k ((θ w : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) := by
      refine ⟨g.map ρk, hgmon.map _, ?_⟩
      have h2 := congrArg (modularFunctionFieldC k 1).val.toRingHom h0
      rw [Polynomial.hom_eval₂, map_zero] at h2
      convert h2 using 2 <;> first | (with_reducible_and_instances rfl) | rfl | skip
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    rcases hw with hw | hw
    · rw [hw] at hint'
      apply hjtr
      refine IsAlgebraic.of_pow hp0 ?_
      simpa using hint'.isAlgebraic
    · have halg : IsAlgebraic k (((jGeomGen k 1 ^ p : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)) := by
        have hne : ((θ w : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) ≠ 0 := fun h => by
          have := congrArg (fun z : ↥(modularFunctionFieldC k 1) => (z : LaurentSeries k)) hw
          simp only [MulMemClass.coe_mul, OneMemClass.coe_one, h, zero_mul] at this
          exact zero_ne_one this
        have hw' : ((θ w : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) * ((jGeomGen k 1 ^ p : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = 1 := by
          have := congrArg (fun z : ↥(modularFunctionFieldC k 1) => (z : LaurentSeries k)) hw
          simpa only [MulMemClass.coe_mul, OneMemClass.coe_one] using this
        rw [eq_inv_of_mul_eq_one_right hw']
        exact hint'.isAlgebraic.inv
      apply hjtr
      refine IsAlgebraic.of_pow hp0 ?_
      simpa using halg
  by_cases hcU : c ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
  ·
    haveI : Nonempty (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) : X.Opens) := ⟨⟨c, hcU⟩⟩
    let jc : X.presheaf.stalk c := (X.presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) c hcU).hom
      (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv
                  (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))
    have hjc : φ (algebraMap _ ↥X.functionField jc) = ProlongationTuple.jFun 1 p := by
      apply Subtype.ext
      rw [hgerm]
      rw [hφj]
      rfl
    refine finish jc (Or.inl ?_)
    rw [hθ]
    have : (⟨φ (algebraMap _ ↥X.functionField jc), hdom jc⟩ : ↥V) = ⟨_, hjmem⟩ := Subtype.ext hjc
    rw [this, hjres]
  ·
    have hcI : c ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) := by
      have hcov : (c : ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O)) ∈ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ⊔
          TwoChartIntegralModel.chartInfOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O : (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O).Opens) := by
        rw [TwoChartIntegralModel.chartFinOpenBC_sup_chartInfOpenBC]; trivial
      rcases hcov with h | h
      · change c ∈ TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ⁻¹ᵁ
          TwoChartIntegralModel.chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) at h
        rw [← TwoChartIntegralModel.TwoChartsAux.U_eq] at h
        exact absurd h hcU
      · change c ∈ TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) O ⁻¹ᵁ
          TwoChartIntegralModel.chartInfOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) at h
        rw [← TwoChartIntegralModel.TwoChartsAux.V_eq] at h
        exact h
    haveI : Nonempty (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) : X.Opens) := ⟨⟨c, hcI⟩⟩

    let wc : X.presheaf.stalk c := (X.presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) c hcI).hom
      (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))
    have hglue : (X.germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) * (X.germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jInvChartInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) = 1 :=
      glue_block p O
    have hjF : φ ((X.germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))) = ProlongationTuple.jFun 1 p := by
      apply Subtype.ext; rw [hφj]; rfl
    have hjne : (ProlongationTuple.jFun 1 p : FB) ≠ 0 := by
      intro h0
      apply hjtr
      refine IsAlgebraic.of_pow (Fact.out : p.Prime).pos ?_
      have : ((jGeomGen k 1 ^ p : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = 0 := by
        rw [← hjres]
        have : (⟨(ProlongationTuple.jFun 1 p : FB), hjmem⟩ : ↥V) = 0 := Subtype.ext h0
        rw [this, map_zero]; rfl
      have h' : (jqModC k) ^ p = 0 := by simpa using this
      rw [h']; exact isAlgebraic_zero
    have hwc : φ (algebraMap _ ↥X.functionField wc) = (ProlongationTuple.jFun 1 p : FB)⁻¹ := by
      rw [hgerm]
      apply eq_inv_of_mul_eq_one_left
      rw [← hjF, ← map_mul, (mul_comm _ _).trans hglue, map_one]
    refine finish wc (Or.inr ?_)
    rw [hθ]
    have hprod : (⟨φ (algebraMap _ ↥X.functionField wc), hdom wc⟩ : ↥V) * ⟨_, hjmem⟩ = 1 :=
      Subtype.ext (by rw [Subring.coe_mul]; show φ (algebraMap _ ↥X.functionField wc) * ProlongationTuple.jFun 1 p = 1; rw [hwc, inv_mul_cancel₀ hjne])
    have := congrArg R.residue₂ hprod
    rwa [map_mul, map_one, hjres] at this

end S_ModularCurve_DRModelPackage_not_isClosed_of_forall_stalk_mem_integersSnd
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_not_isClosed_of_forall_stalk_mem_integersSnd (solution)
