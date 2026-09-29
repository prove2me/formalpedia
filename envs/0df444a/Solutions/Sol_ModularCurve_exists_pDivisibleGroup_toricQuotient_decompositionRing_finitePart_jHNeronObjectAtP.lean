-- Prove2me | solution 1 for ModularCurve.exists_pDivisibleGroup_toricQuotient_decompositionRing_finitePart_jHNeronObjectAtP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e86cb1d5-6524-50e5-8b1a-ba522f946977

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup
import Theorems.Thm_ValuationSubring_henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Theorems.Thm_ValuationSubring_mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_pDivisibleGroup_toricQuotient_decompositionRing_finitePart_jHNeronObjectAtP
p2m_attr_erase "simp" "PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace Ws47
namespace HTDIV

set_option linter.unusedSectionVars false

noncomputable abbrev RD (Pl : ValuationSubring (AlgebraicClosure ℚ)) : Subring (AlgebraicClosure ℚ) :=
  Pl.toSubring ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring

variable (Pl : ValuationSubring (AlgebraicClosure ℚ))

@[reducible] noncomputable def algK : Algebra (FractionRing ↥(RD Pl)) (AlgebraicClosure ℚ) :=
  (IsFractionRing.lift (K := FractionRing ↥(RD Pl)) (g := algebraMap ↥(RD Pl) (AlgebraicClosure ℚ))
    (FaithfulSMul.algebraMap_injective ↥(RD Pl) (AlgebraicClosure ℚ))).toAlgebra

attribute [local instance] algK

theorem towerRD : IsScalarTower ↥(RD Pl) (FractionRing ↥(RD Pl)) (AlgebraicClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective ↥(RD Pl) (AlgebraicClosure ℚ)) x).symm

theorem towerQ : IsScalarTower ℚ (FractionRing ↥(RD Pl)) (AlgebraicClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    have := RingHom.ext_rat ((algebraMap (FractionRing ↥(RD Pl)) (AlgebraicClosure ℚ)).comp (algebraMap ℚ (FractionRing ↥(RD Pl))))
      (algebraMap ℚ (AlgebraicClosure ℚ))
    exact (RingHom.congr_fun this q).symm

theorem isAlgebraicK : Algebra.IsAlgebraic (FractionRing ↥(RD Pl)) (AlgebraicClosure ℚ) :=
  haveI := towerQ Pl
  Algebra.IsAlgebraic.tower_top (K := ℚ) (L := FractionRing ↥(RD Pl))

end Ws47.HTDIV

open ModularCurve in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    [IsDiscreteValuationRing ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)]

    {h : ℕ} (𝒢D : PDivisibleGroup ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) p h)
    (ΔD : 𝒢D.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔDinj : Function.Injective ΔD)
    (hΔDlev : ∀ (v : ℕ) (x : ModularCurve.JH M H),
      (∃ y : 𝒢D.Point (AlgebraicClosure ℚ) v, ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = x) ↔ x ∈ O.finPts (p ^ v))
    (hΔDgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) → ∀ z : 𝒢D.Points (AlgebraicClosure ℚ), ΔD (τ' • z) = τ • ΔD z)
    (htorD : ∀ v : ℕ, O.toricPts (p ^ v) ≤ O.finPts (p ^ v))

    (ρD : ModularCurve.XHDRLevel.R p →+* (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)))
    (ιD : ∀ v : ℕ, Spec (CommRingCat.of (𝒢D.level v)) ⟶ O.G)
    (hρD : (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (AlgebraicClosure ℚ)).comp ρD = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιDbase : ∀ v : ℕ, ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD))
    (hιDcl : ∀ (v : ℕ) (h1 : ιD v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρD)) (ιD v)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h1))
    (hιDp : ∀ v : ℕ, ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιDmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B] (x y : 𝒢D.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] B) : 𝒢D.level v →+* B)) ≫ ιD v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) B)) ≫ Spec.map (CommRingCat.ofHom ρD)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιDt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢D.transition v : 𝒢D.level (v + 1) →+* 𝒢D.level v)) ≫ ιD (v + 1) = ιD v)
    (hιDfin : ∀ (v : ℕ)
      (h3 : ιD v ≫ O.L.schemeNsmul (p ^ v) = (ιD v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v))) ≫ Spec.map (CommRingCat.ofHom ρD)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρD))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ιD v) (ιD v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) (𝒢D.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρD))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρD))).base x = IsLocalRing.closedPoint (↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)) →
          x ∈ Set.range jv.base)

    (hιDpts : ∀ (v : ℕ) (x : 𝒢D.Point (AlgebraicClosure ℚ) v),
      (O.pts (ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢D.level v →ₐ[(↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring))] (AlgebraicClosure ℚ)) : 𝒢D.level v →+* (AlgebraicClosure ℚ))) ≫ ιD v)
    :
    ∃ (𝒯 : PDivisibleGroup ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) p O.toricRank) (π : ∀ v : ℕ, 𝒢D.level v →ₐc[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] 𝒯.level v),
      (∀ v, Function.Surjective (π v)) ∧
      (∀ v : ℕ, (𝒯.transition v).comp (π (v + 1)) = (π v).comp (𝒢D.transition v)) ∧

      (∀ (v : ℕ) (x : 𝒢D.Point (AlgebraicClosure ℚ) v),
(∃ y : 𝒯.Point (AlgebraicClosure ℚ) v,
          PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (π v : 𝒢D.level v →ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] 𝒯.level v)) = x) ↔
        ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v)) ∧

      (∀ (v : ℕ) (y : 𝒯.Point (AlgebraicClosure ℚ) v) (c : 𝒯.level v),
        Pl.valuation (PDivisibleGroup.Point.toAlgHom y c - algebraMap ↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring) (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1) ∧

      (∀ (v : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[↥((Pl.toSubring) ⊓ (IntermediateField.fixedField (Pl.decompositionSubgroup ℚ)).toSubring)] AlgebraicClosure ℚ),
        (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
        ∀ z : ModularCurve.JH M H, z ∈ O.toricPts (p ^ v) → τ • z ∈ O.toricPts (p ^ v)) := by
  classical
  haveI : IsPrincipalIdealRing ↥(Ws47.HTDIV.RD Pl) := inferInstance
  have hp : 0 < p := Nat.Prime.pos Fact.out

  obtain ⟨-, ⟨πr, -, hπr⟩, hunit⟩ :=
    ValuationSubring.henselianLocalRing_and_exists_residue_zmod_inf_fixedField_decompositionSubgroup Pl p hPl
  letI : Algebra ↥(Ws47.HTDIV.RD Pl) (ZMod p) := πr.toAlgebra
  have hresD : ∀ x : ↥(Ws47.HTDIV.RD Pl), algebraMap ↥(Ws47.HTDIV.RD Pl) (ZMod p) x = 0 ↔
      x ∈ IsLocalRing.maximalIdeal ↥(Ws47.HTDIV.RD Pl) := fun x => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    exact hπr x

  have hDst : ∀ (v : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (τ' : AlgebraicClosure ℚ ≃ₐ[↥(Ws47.HTDIV.RD Pl)] AlgebraicClosure ℚ), (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : ModularCurve.JH M H, z ∈ O.toricPts (p ^ v) → τ • z ∈ O.toricPts (p ^ v) := by
    intro v τ τ' hτ z hz
    have hτD : τ ∈ Pl.decompositionSubgroup ℚ :=
      ValuationSubring.mem_decompositionSubgroup_of_forall_apply_eq_of_mem_inf_fixedField Pl τ
        (fun x hxP hxZ => by rw [← hτ]; exact τ'.commutes (⟨x, Subring.mem_inf.mpr ⟨hxP, hxZ⟩⟩ : ↥(Ws47.HTDIV.RD Pl)))
    obtain ⟨-, -, hiff, -⟩ :=
      ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard p M H hpM Pl hPl Λ O
        (p ^ v) (pow_pos hp v)
    obtain ⟨χ, rfl⟩ := (hiff z).mp hz
    obtain ⟨χ', hχ'⟩ := O.toricLift_dec (p ^ v) (pow_pos hp v) τ hτD χ
    exact (hiff _).mpr ⟨χ', hχ'.symm⟩

  letI := Ws47.HTDIV.algK Pl
  haveI := Ws47.HTDIV.towerRD Pl
  haveI := Ws47.HTDIV.towerQ Pl
  haveI := Ws47.HTDIV.isAlgebraicK Pl
  have lev : ∀ v : ℕ, ∃ (Cv : Type) (_ : CommRing Cv) (_ : HopfAlgebra ↥(Ws47.HTDIV.RD Pl) Cv),
      Module.Finite ↥(Ws47.HTDIV.RD Pl) Cv ∧ Module.Flat ↥(Ws47.HTDIV.RD Pl) Cv ∧ Coalgebra.IsCocomm ↥(Ws47.HTDIV.RD Pl) Cv ∧
      ∃ πv : 𝒢D.level v →ₐc[↥(Ws47.HTDIV.RD Pl)] Cv, Function.Surjective πv ∧
        ∀ x : 𝒢D.Point (AlgebraicClosure ℚ) v,
          (∃ χ : Cv →ₐ[↥(Ws47.HTDIV.RD Pl)] AlgebraicClosure ℚ,
              χ.comp (πv : 𝒢D.level v →ₐ[↥(Ws47.HTDIV.RD Pl)] Cv) = PDivisibleGroup.Point.toAlgHom x) ↔
            ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v) := by
    intro v
    let N : Submonoid (WithConv (𝒢D.level v →ₐ[↥(Ws47.HTDIV.RD Pl)] AlgebraicClosure ℚ)) :=
      { carrier := {f | ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v
          (Additive.ofMul (PDivisibleGroup.Point.ofConv f : 𝒢D.Point (AlgebraicClosure ℚ) v))) ∈ O.toricPts (p ^ v)}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, PDivisibleGroup.Point.ofConv_mul, ofMul_mul, map_add] at ha hb ⊢
          exact (O.toricPts (p ^ v)).add_mem ha hb
        one_mem' := by
          change ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (1 : 𝒢D.Point (AlgebraicClosure ℚ) v))) ∈ O.toricPts (p ^ v)
          rw [ofMul_one, map_zero, map_zero]
          exact (O.toricPts (p ^ v)).zero_mem }
    have hN : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[FractionRing ↥(Ws47.HTDIV.RD Pl)] AlgebraicClosure ℚ), ∀ f ∈ N,
        ∀ f' : WithConv (𝒢D.level v →ₐ[↥(Ws47.HTDIV.RD Pl)] AlgebraicClosure ℚ),
          (∀ x : 𝒢D.level v, f'.ofConv x = σ (f.ofConv x)) → f' ∈ N := by
      intro σ f hf f' hf'
      let σR : AlgebraicClosure ℚ ≃ₐ[↥(Ws47.HTDIV.RD Pl)] AlgebraicClosure ℚ := σ.restrictScalars ↥(Ws47.HTDIV.RD Pl)
      let τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ.restrictScalars ℚ
      have hf'eq : (PDivisibleGroup.Point.ofConv f' : 𝒢D.Point (AlgebraicClosure ℚ) v) =
          𝒢D.pointMap (σR : AlgebraicClosure ℚ →ₐ[↥(Ws47.HTDIV.RD Pl)] AlgebraicClosure ℚ) v
            (PDivisibleGroup.Point.ofConv f : 𝒢D.Point (AlgebraicClosure ℚ) v) := by
        apply PDivisibleGroup.Point.ext
        intro a
        rw [PDivisibleGroup.toAlgHom_pointMap]
        exact hf' a
      change ΔD (𝒢D.pointsMkAdd (AlgebraicClosure ℚ) v
        (Additive.ofMul (PDivisibleGroup.Point.ofConv f' : 𝒢D.Point (AlgebraicClosure ℚ) v))) ∈ O.toricPts (p ^ v)
      rw [hf'eq, ← PDivisibleGroup.Points.smul_pointsMkAdd, hΔDgal τ σR (fun x => rfl)]
      exact hDst v τ σR (fun x => rfl) _ hf
    obtain ⟨Hv, i1, i2, hfin, hflat, hcocomm, πv, hπv, -, -, hpts, -⟩ :=
      HopfAlgebra.exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup
        (R := ↥(Ws47.HTDIV.RD Pl)) (K := FractionRing ↥(Ws47.HTDIV.RD Pl)) (L := AlgebraicClosure ℚ) (𝒢D.level v) N hN
    refine ⟨Hv, i1, i2, hfin, hflat, hcocomm, πv, hπv, fun x => ?_⟩
    exact (hpts x).symm
  choose C iC iH hfin hflat hcocomm π hπ hπpts using lev
  letI : ∀ v, CommRing (C v) := iC
  letI : ∀ v, HopfAlgebra ↥(Ws47.HTDIV.RD Pl) (C v) := iH
  haveI : ∀ v, Module.Finite ↥(Ws47.HTDIV.RD Pl) (C v) := hfin
  haveI : ∀ v, Module.Flat ↥(Ws47.HTDIV.RD Pl) (C v) := hflat
  haveI : ∀ v, Coalgebra.IsCocomm ↥(Ws47.HTDIV.RD Pl) (C v) := hcocomm
  haveI : ∀ v, Module.Free ↥(Ws47.HTDIV.RD Pl) (C v) := fun v => Module.free_of_flat_of_isLocalRing

  obtain ⟨-, hRED, tC, htCsurj, htCcomp, htCker, hrank⟩ :=
    ModularCurve.exists_verschiebung_bialgEquiv_and_reducesToOne_and_tower_toricClosure_finitePart_jHNeronObjectAtP
      p M H hpM hpM2 hHp Pl hPl hj 𝔛 Λ O hrep hrepΛ 𝒢D ΔD hΔDinj hΔDlev hΔDgal htorD ρD ιD hρD hιDbase hιDcl hιDp hιDmul hιDt hιDfin
      hιDpts hresD C π hπ hπpts

  let 𝒯 : PDivisibleGroup ↥(Ws47.HTDIV.RD Pl) p O.toricRank :=
    { level := C
      transition := tC
      transition_surjective := htCsurj
      finrank_level := hrank
      ker_transition := htCker }

  refine ⟨𝒯, π, hπ, htCcomp, ?_, ?_, ?_⟩
  · intro v x
    rw [← hπpts v x]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨PDivisibleGroup.Point.toAlgHom y, by rw [← hy, PDivisibleGroup.Point.toAlgHom_ofAlgHom]⟩
    · rintro ⟨χ, hχ⟩
      exact ⟨PDivisibleGroup.Point.ofAlgHom χ, by rw [PDivisibleGroup.Point.toAlgHom_ofAlgHom, hχ, PDivisibleGroup.Point.ofAlgHom_toAlgHom]⟩
  · intro v y c
    exact hRED v (PDivisibleGroup.Point.toAlgHom y) c
  · intro v τ τ' hτ z hz
    exact hDst v τ τ' hτ z hz

end S_ModularCurve_exists_pDivisibleGroup_toricQuotient_decompositionRing_finitePart_jHNeronObjectAtP
end P2MW
export P2MW.S_ModularCurve_exists_pDivisibleGroup_toricQuotient_decompositionRing_finitePart_jHNeronObjectAtP (solution)
