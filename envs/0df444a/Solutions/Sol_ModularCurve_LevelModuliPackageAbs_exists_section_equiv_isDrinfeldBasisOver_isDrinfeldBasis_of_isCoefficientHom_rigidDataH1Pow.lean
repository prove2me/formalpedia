-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_section_equiv_isDrinfeldBasisOver_isDrinfeldBasis_of_isCoefficientHom_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c312881a-f548-54b6-ba96-9944ca3c7788

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
import Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_projMap_comp_projModelStrCR_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_of_specMap_comp_eq_originChart
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_reducesToOrigin_of_originParam_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_comp_projMap_eq_of_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_section_equiv_isDrinfeldBasisOver_isDrinfeldBasis_of_isCoefficientHom_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X"

set_option autoImplicit false

p2m_open "ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup AlgebraicGeometry CategoryTheory NeronModelInfra Polynomial AlgebraicGeometry.Polynomial"

attribute [local instance] MvPolynomial.gradedAlgebra

theorem glueTr_coefHom_unique {T T' : Type} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ φ' : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (h : IsCoefficientHom W f φ) (h' : IsCoefficientHom W f φ') : φ = φ' := by
  have key : (φ : ProjModelRingCR W →+* ProjModelRingCR (W.map f)).comp (Ideal.Quotient.mk _) =
      (φ' : ProjModelRingCR W →+* ProjModelRingCR (W.map f)).comp (Ideal.Quotient.mk _) := by
    apply MvPolynomial.ringHom_ext
    · intro a; show φ (cls W (MvPolynomial.C a)) = φ' (cls W (MvPolynomial.C a)); rw [h.1 a, h'.1 a]
    · intro i; show φ (cls W (MvPolynomial.X i)) = φ' (cls W (MvPolynomial.X i)); rw [h.2 i, h'.2 i]
  have key' := Ideal.Quotient.ringHom_ext key
  exact GradedRingHom.ext fun x => congrArg (fun g : ProjModelRingCR W →+* _ => g x) key'

set_option maxHeartbeats 25600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) [NeZero M']
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓg : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    [Algebra W₀ R] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)
    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P₀.B₀, Φ (ι b) = φ b)

    (hℓ' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))

    (h𝒢r : (𝒢.restrictScalars W₀).IsChordTangent) (h𝒢Or : (𝒢.restrictScalars W₀).IsOriginIdentity)
    (Pet : LevelModuliPackageAbs W₀
      ((((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.gamma1Component W₀ ℓg hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL' _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum)
    (xet : ((((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.gamma1Component W₀ ℓg hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL' _ W C _ _ _ _ (hx hmem))).toRigid).Raw Pet.B₀)
    (hxet : (Quot.mk _ xet :
      ((((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.gamma1Component W₀ ℓg hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL' _ W C _ _ _ _ (hx hmem))).toRigid).Pt Pet.B₀) =
        Pet.univ)
    (CQ : Type) [CommRing CQ] [Algebra Pet.B₀ CQ] [Algebra W₀ CQ] [IsScalarTower W₀ Pet.B₀ CQ]
    (Qu : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ CQ))) (projModelStrCR xet.curve))
    (hQu : ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q Qu =
      ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _)
    (hrep : ∀ (T : Type) [CommRing T] [Algebra Pet.B₀ T]
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ T))) (projModelStrCR xet.curve)),
        ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q Q =
            ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _ ↔
          ∃! χ : CQ →ₐ[Pet.B₀] T, Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Qu.1 = Q.1)

    (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    [Algebra W₀ S] (ιS : CQ →ₐ[W₀] S)
    (resS : S →+* k) (hresS : Function.Surjective resS) (hkerS : RingHom.ker resS = maximalIdeal S)
    (hresS₀ : ∀ w : W₀, resS (algebraMap W₀ S w) = res₀ w)
    (hfacS : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : CQ →ₐ[W₀] T, (∀ c : CQ, resT (φ c) = resS (ιS c)) →
          ∃! Φ : S →ₐ[W₀] T, (∀ s : S, resT (Φ s) = resS s) ∧ ∀ c : CQ, Φ (ιS c) = φ c)

    (FS : FormalGroup S)
    (hFS : FS.toPowerSeries = (xet.curve.map ((ιS : CQ →+* S).comp (algebraMap Pet.B₀ CQ))).formalGroupLawFixed)
    (g : S[X]) (v : PowerSeries S) (hgm : g.Monic) (hgdeg : g.natDegree = q - 1)
    (hgcoeff : ∀ i < q - 1, g.coeff i ∈ maximalIdeal S) (hg0 : ∃ w : S, IsUnit w ∧ g.coeff 0 = (q : S) * w)
    (hv : IsUnit v)
    (hfacq : FS.nthSeries q = PowerSeries.X * (↑g : PowerSeries S) * v)

    [Algebra A₀ k] [Algebra W₀ k] [IsScalarTower A₀ W₀ k] [Algebra Pet.B₀ k]
    (hk₀ : ∀ w : W₀, algebraMap W₀ k w = res₀ w)
    (ρ : P₀.B₀ →ₐ[A₀] k) (hρ : ∀ b : P₀.B₀, ρ b = resR (ι b))
    (ψet : Pet.B₀ →ₐ[W₀] k) (hψet : ∀ b : Pet.B₀, ψet b = resS (ιS (algebraMap Pet.B₀ CQ b)))
    (hψalg : ∀ b : Pet.B₀, algebraMap Pet.B₀ k b = ψet b)
    (hΔk : IsUnit (xet.curve.map ψet.toRingHom).Δ)
    (Qk : Section (xet.curve.map ψet.toRingHom))
    (hQk_pin : ∃ (φ : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψet.toRingHom))
        (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψet.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φ),
        IsCoefficientHom xet.curve ψet.toRingHom φ ∧
          Qk.1 ≫ Proj.map φ hφ = Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1)
    (hQk : Qk ≠ (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))))

    (hhk : ∀ p : ↥M'.primeFactors, ModularCurve.IsGamma0PowAt (xet.curve.map ψet.toRingHom) (p : ℕ) (M'.factorization (p : ℕ))
      ((xet.level.1 p).map ψet.toRingHom))
    (hDk : ModularCurve.IsGamma1Point (xet.curve.map ψet.toRingHom) ℓg (xet.level.2.1.map ψet.toRingHom))
    (hLk : ModularCurve.IsGamma1Link (xet.curve.map ψet.toRingHom) ℓg M'
      (fun p => (xet.level.1 p).map ψet.toRingHom) (xet.level.2.1.map ψet.toRingHom))
    (hyk : RawDrinfeldPair.IsLevel 𝒢 q (xet.curve.map ψet.toRingHom)
      ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩)
    (hρyk : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map ρ P₀.univ =
      (Quot.mk _ (⟨xet.curve.map ψet.toRingHom, hΔk,
          ⟨fun p => (xet.level.1 p).map ψet.toRingHom, xet.level.2.1.map ψet.toRingHom,
            ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩⟩,
          ⟨⟨hhk, hDk, hyk⟩, hLk⟩⟩ : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw k) :
        (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt k))
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (ψ : Pet.B₀ →ₐ[W₀] T) (hψ₀ : ∀ b : Pet.B₀, resT (ψ b) = ψet b)
    (Qm : base (T := T) ⟶ projModelCR xet.curve)
    (hQover : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom ψ.toRingHom))
    (hQtors : ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨Qm, hQover⟩ = ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _)
    (hQred : Spec.map (CommRingCat.ofHom resT) ≫ Qm = Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1) :
    ∃ Q : Section (xet.curve.map (ψ).toRingHom),
      ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).nsmul (𝟙 _) q Q =
        ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).one (𝟙 _) ∧
      (∀ χ : OriginChartRing (xet.curve.map ψ.toRingHom) →+* T, ¬ ReducesToOrigin Q χ (maximalIdeal T)) ∧
      (∀ (φ : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψ.toRingHom))
          (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψ.toRingHom)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φ),
          IsCoefficientHom xet.curve ψ.toRingHom φ → Q.1 ≫ Proj.map φ hφ = Qm) ∧
      ∃ e : {Pm : base (T := T) ⟶ projModelCR xet.curve //
              (∃ (hP : Pm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom))
                 (hQ : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom)),
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                   (Spec.map (CommRingCat.ofHom (ψ).toRingHom)) ⟨Pm, hP⟩ ⟨Qm, hQ⟩) ∧
              Spec.map (CommRingCat.ofHom resT) ≫ Pm =
                (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1} ≃
          {P : Section (xet.curve.map (ψ).toRingHom) //
            (∃ χ : OriginChartRing (xet.curve.map ψ.toRingHom) →+* T, ReducesToOrigin P χ (maximalIdeal T)) ∧
            IsDrinfeldBasis ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)) q P Q},
        ∀ (Pm : {Pm : base (T := T) ⟶ projModelCR xet.curve //
              (∃ (hP : Pm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom))
                 (hQ : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom)),
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                   (Spec.map (CommRingCat.ofHom (ψ).toRingHom)) ⟨Pm, hP⟩ ⟨Qm, hQ⟩) ∧
              Spec.map (CommRingCat.ofHom resT) ≫ Pm =
                (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1})
          (φ : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψ.toRingHom))
          (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψ.toRingHom)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φ),
          IsCoefficientHom xet.curve ψ.toRingHom φ → ((e Pm).1).1 ≫ Proj.map φ hφ = Pm.1 := by
  classical

  obtain ⟨φc, hφc, hcoef⟩ := WeierstrassProjModel.exists_isCoefficientHom xet.curve ψ.toRingHom
  have hPB := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom xet.curve ψ.toRingHom φc hφc hcoef
  have hsq := WeierstrassCurve.DrinfeldGlobal.projMap_comp_projModelStrCR_of_isCoefficientHom xet.curve ψ.toRingHom φc hφc hcoef

  obtain ⟨χB, hχB, hχBx, hχBz⟩ := h𝒢Or Pet.B₀ xet.curve xet.isUnit_Δ
  obtain ⟨χT, hχT, hχTx, hχTz⟩ := h𝒢Or T (xet.curve.map ψ.toRingHom) (xet.curve.isUnit_Δ_map ψ.toRingHom xet.isUnit_Δ)
  have h1 : (((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).one (𝟙 _)).1 ≫ Proj.map φc hφc =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (𝟙 _)).1 :=
    WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection xet.curve ψ.toRingHom φc hφc hcoef
      _ _ χB hχB hχBx hχBz χT hχT hχTx hχTz

  have hone : ∀ {Ssch : Scheme} (s : Ssch ⟶ Spec (CommRingCat.of Pet.B₀)),
      (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one s).1 = s ≫ (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (𝟙 _)).1 := by
    intro Ssch s
    have := congrArg Subtype.val (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one_natural (𝟙 _) s s (Category.comp_id s))
    rw [schemeHomOverComp_coe] at this
    exact this.symm

  let Ql : base (T := T) ⟶ projModelCR (xet.curve.map ψ.toRingHom) :=
    hPB.lift Qm (𝟙 _) (by rw [hQover, Category.id_comp])
  have hQl_fst : Ql ≫ Proj.map φc hφc = Qm := hPB.lift_fst _ _ _
  have hQl_snd : Ql ≫ projModelStrCR (xet.curve.map ψ.toRingHom) = 𝟙 _ := hPB.lift_snd _ _ _
  let Q : Section (xet.curve.map ψ.toRingHom) := ⟨Ql, hQl_snd⟩

  have hQφ : ∀ (φ : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψ.toRingHom))
      (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψ.toRingHom)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φ),
      IsCoefficientHom xet.curve ψ.toRingHom φ → Q.1 ≫ Proj.map φ hφ = Qm := by
    intro φ hφ hc
    obtain rfl : φ = φc := glueTr_coefHom_unique xet.curve ψ.toRingHom φ φc hc hcoef
    exact hQl_fst

  haveI : (xet.curve).toAffine.IsElliptic := ⟨xet.isUnit_Δ⟩
  have hns : ∀ n : ℕ, (((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).nsmul (𝟙 _) n Q).1 ≫ Proj.map φc hφc =
      (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) n
        ⟨Q.1 ≫ Proj.map φc hφc, by rw [Category.assoc, hsq, ← Category.assoc, Q.2]⟩).1 := by
    intro n
    induction n with
    | zero =>
      rw [RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero, h1,
        hone (𝟙 _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)), Category.id_comp]
    | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ,
        WeierstrassCurve.DrinfeldGlobal.comp_projMap_mul_eq_mul_comp_projMap_of_one_comp_eq xet.curve ψ.toRingHom φc hφc hcoef
          ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ) ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)) h1 hsq (𝟙 _)]
      congr 2
      exact Subtype.ext ih
  have htorsQ : ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).nsmul (𝟙 _) q Q = ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).one (𝟙 _) := by
    have aux : ∀ {t : base (T := T) ⟶ Spec (CommRingCat.of Pet.B₀)} (ht : t = Spec.map (CommRingCat.ofHom ψ.toRingHom))
        (x : SchemeHomOver t (projModelStrCR xet.curve)), x.1 = Qm →
        (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul t q x).1 = (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one t).1 := by
      rintro t rfl x hx
      have : x = ⟨Qm, hQover⟩ := Subtype.ext hx
      rw [this, hQtors]
    apply Subtype.ext
    apply hPB.hom_ext
    · rw [hns q, aux (Category.id_comp _) _ hQl_fst, hone, h1, Category.id_comp]
    · rw [(((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).nsmul (𝟙 _) q Q).2, (((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).one (𝟙 _)).2]

  have hmkbot : maximalIdeal k = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).mp (Field.toIsField k)
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [hmkbot]; infer_instance
  have RED : ∀ (P : Section (xet.curve.map ψ.toRingHom)) (χ : OriginChartRing (xet.curve.map ψ.toRingHom) →+* T), ReducesToOrigin P χ (maximalIdeal T) →
      Spec.map (CommRingCat.ofHom resT) ≫ P.1 = Spec.map (CommRingCat.ofHom resT) ≫ (((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).one (𝟙 _)).1 := by
    intro P χ hP
    obtain ⟨φr, hφr, hcoefr⟩ := WeierstrassProjModel.exists_isCoefficientHom (xet.curve.map ψ.toRingHom) resT
    have hPBr := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom (xet.curve.map ψ.toRingHom) resT φr hφr hcoefr
    let P'l : base (T := k) ⟶ projModelCR ((xet.curve.map ψ.toRingHom).map resT) :=
      hPBr.lift (Spec.map (CommRingCat.ofHom resT) ≫ P.1) (𝟙 _)
        (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp])
    let P' : Section ((xet.curve.map ψ.toRingHom).map resT) := ⟨P'l, hPBr.lift_snd _ _ _⟩
    have hP'fst : P'.1 ≫ Proj.map φr hφr = Spec.map (CommRingCat.ofHom resT) ≫ P.1 := hPBr.lift_fst _ _ _
    obtain ⟨χ', hP'red, hpar, -⟩ :=
      WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_map_originParam_eq_of_isCoefficientHom (xet.curve.map ψ.toRingHom) resT φr hφr hcoefr
        P χ (maximalIdeal T) hP P' hP'fst
    have hmap0 : (maximalIdeal T).map resT = ⊥ := by rw [Ideal.map_eq_bot_iff_le_ker, hT₂]
    have hP'red' : ReducesToOrigin P' χ' (maximalIdeal k) := by
      obtain ⟨h1', h2', h3'⟩ := hP'red
      rw [hmap0, Ideal.mem_bot] at h2' h3'
      exact ⟨h1', by rw [h2']; exact Ideal.zero_mem _, by rw [h3']; exact Ideal.zero_mem _⟩
    have hpar0 : originParam χ' = 0 := by
      rw [hpar]
      have hm : originParam χ ∈ maximalIdeal T := hP.2.1
      rw [← hT₂, RingHom.mem_ker] at hm
      exact hm
    obtain ⟨χ₀', h₀sec, h₀x, h₀z⟩ :=
      h𝒢Or k ((xet.curve.map ψ.toRingHom).map resT) (WeierstrassCurve.isUnit_Δ_map _ resT (xet.curve.isUnit_Δ_map ψ.toRingHom xet.isUnit_Δ))
    have h₀par : originParam χ₀' = 0 := by unfold originParam; rw [h₀x, neg_zero]
    have h₀red : ReducesToOrigin
        (((𝒢.restrictScalars W₀) k ((xet.curve.map ψ.toRingHom).map resT) (WeierstrassCurve.isUnit_Δ_map _ resT (xet.curve.isUnit_Δ_map ψ.toRingHom xet.isUnit_Δ))).one (𝟙 _))
        χ₀' (maximalIdeal k) := by
      refine ⟨h₀sec, ?_, ?_⟩
      · rw [h₀par]; exact Ideal.zero_mem _
      · unfold originW; rw [h₀z, neg_zero]; exact Ideal.zero_mem _
    obtain ⟨hPeq, -⟩ :=
      WeierstrassCurve.DrinfeldGlobal.section_eq_of_reducesToOrigin_of_originParam_eq ((xet.curve.map ψ.toRingHom).map resT) P' _ χ' χ₀'
        hP'red' h₀red (hpar0.trans h₀par.symm)
    have h1r := WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection (xet.curve.map ψ.toRingHom) resT φr hφr hcoefr
      ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)) _ χT hχT hχTx hχTz χ₀' h₀sec h₀x h₀z
    rw [← hP'fst, hPeq, h1r]

  have hψet' : CommRingCat.ofHom ψ.toRingHom ≫ CommRingCat.ofHom resT = CommRingCat.ofHom ψet.toRingHom := by
    rw [← CommRingCat.ofHom_comp]; congr 1; exact RingHom.ext hψ₀
  have hinst : (algebraRestrict A₀ W₀ k : Algebra A₀ k) = ‹Algebra A₀ k› :=
    Algebra.algebra_ext _ _ (fun a => (IsScalarTower.algebraMap_apply A₀ W₀ k a).symm)
  have hlawk : ((𝒢.restrictScalars W₀) k (xet.curve.map ψet.toRingHom) hΔk) = 𝒢 k (xet.curve.map ψet.toRingHom) hΔk := by
    show @𝒢 k _ (algebraRestrict A₀ W₀ k) (xet.curve.map ψet.toRingHom) hΔk = _
    rw [hinst]
  have hnot : ∀ χ : OriginChartRing (xet.curve.map ψ.toRingHom) →+* T, ¬ ReducesToOrigin Q χ (maximalIdeal T) := by
    intro χ hQ0
    have e2 := congrArg (fun m => m ≫ Proj.map φc hφc) (RED Q χ hQ0)
    simp only [Category.assoc] at e2
    rw [hQl_fst, hQred, h1, ← Category.assoc, ← Spec.map_comp, hψet'] at e2
    obtain ⟨φe, hφe, hcoefe, hQk1⟩ := hQk_pin
    obtain ⟨χk, hχk, hχkx, hχkz⟩ := h𝒢Or k (xet.curve.map ψet.toRingHom) hΔk
    have h1e := WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection xet.curve ψet.toRingHom φe hφe hcoefe
      ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ) ((𝒢.restrictScalars W₀) k (xet.curve.map ψet.toRingHom) hΔk) χB hχB hχBx hχBz χk hχk hχkx hχkz
    have hQk' := WeierstrassCurve.DrinfeldGlobal.section_eq_of_comp_projMap_eq_of_isCoefficientHom xet.curve ψet.toRingHom φe hφe hcoefe
      Qk (((𝒢.restrictScalars W₀) k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 _)) (by rw [hQk1, e2, h1e])
    apply hQk
    rw [hQk', hlawk]

  have hov : ∀ (P : Section (xet.curve.map ψ.toRingHom)), (P.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc) ≫ projModelStrCR xet.curve =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
    intro P
    rw [eqToHom_refl, Category.id_comp, Category.assoc, hsq, ← Category.assoc, P.2, Category.id_comp]
  have hdict : ∀ (P : Section (xet.curve.map ψ.toRingHom)),
      RawDrinfeldPair.IsLevel (𝒢.restrictScalars W₀) q (xet.curve.map ψ.toRingHom) ⟨(xet.curve.map ψ.toRingHom), P, Q⟩ ↔
        ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q (Spec.map (CommRingCat.ofHom ψ.toRingHom))
          ⟨P.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc, hov P⟩
          ⟨Q.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc, hov Q⟩ :=
    fun P => WeierstrassCurve.DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap q (𝒢.restrictScalars W₀) h𝒢Or
      Pet.B₀ xet.curve xet.isUnit_Δ T ψ φc hφc hcoef hsq ⟨(xet.curve.map ψ.toRingHom), P, Q⟩ rfl (hov P) (hov Q)
  have hQpt : (⟨Q.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc, hov Q⟩ :
      SchemeHomOver (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (projModelStrCR xet.curve)) = ⟨Qm, hQover⟩ := by
    apply Subtype.ext
    show Q.1 ≫ eqToHom _ ≫ Proj.map φc hφc = Qm
    rw [eqToHom_refl, Category.id_comp]; exact hQl_fst

  have hone_red : Spec.map (CommRingCat.ofHom resT) ≫ (((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).one (𝟙 _)).1 ≫ Proj.map φc hφc =
      (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1 := by
    rw [h1, ← Category.assoc, ← Spec.map_comp, hψet', hone (Spec.map (CommRingCat.ofHom ψet.toRingHom))]

  let liftP : {Pm : base (T := T) ⟶ projModelCR xet.curve //
              (∃ (hP : Pm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom))
                 (hQ : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom)),
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                   (Spec.map (CommRingCat.ofHom (ψ).toRingHom)) ⟨Pm, hP⟩ ⟨Qm, hQ⟩) ∧
              Spec.map (CommRingCat.ofHom resT) ≫ Pm =
                (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1} → Section (xet.curve.map ψ.toRingHom) := fun Pm =>
    ⟨hPB.lift Pm.1 (𝟙 _) (by obtain ⟨⟨hP, -, -⟩, -⟩ := Pm.2; rw [hP, Category.id_comp]), hPB.lift_snd _ _ _⟩
  have liftP_fst : ∀ Pm, (liftP Pm).1 ≫ Proj.map φc hφc = Pm.1 := fun Pm => hPB.lift_fst _ _ _
  have liftP_mem : ∀ Pm, (∃ χ : OriginChartRing (xet.curve.map ψ.toRingHom) →+* T, ReducesToOrigin (liftP Pm) χ (maximalIdeal T)) ∧
      IsDrinfeldBasis ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)) q (liftP Pm) Q := by
    intro Pm
    obtain ⟨⟨hP, hQ, hDB⟩, hred⟩ := Pm.2
    refine ⟨?_, ?_⟩
    ·
      have hk : Spec.map (CommRingCat.ofHom resT) ≫ (liftP Pm).1 =
          Spec.map (CommRingCat.ofHom resT) ≫ (((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).one (𝟙 _)).1 := by
        apply hPB.hom_ext
        · rw [Category.assoc, liftP_fst, hred, Category.assoc, hone_red]
        · rw [Category.assoc, (liftP Pm).2, Category.assoc, (((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)).one (𝟙 _)).2]
      have hk' : Spec.map (CommRingCat.ofHom resT) ≫ (liftP Pm).1 =
          Spec.map (CommRingCat.ofHom (resT.comp χT)) ≫ originChartι (xet.curve.map ψ.toRingHom) := by
        rw [hk, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
        congr 1
      obtain ⟨χ, hχ, -⟩ :=
        WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_of_specMap_comp_eq_originChart (xet.curve.map ψ.toRingHom) (liftP Pm) resT hT₂
          (resT.comp χT) hk' (by rw [RingHom.comp_apply, hχTx, map_zero]) (by rw [RingHom.comp_apply, hχTz, map_zero])
      exact ⟨χ, hχ⟩
    · have hPpt : (⟨(liftP Pm).1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc, hov (liftP Pm)⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (projModelStrCR xet.curve)) = ⟨Pm.1, hP⟩ := by
        apply Subtype.ext
        show (liftP Pm).1 ≫ eqToHom _ ≫ Proj.map φc hφc = Pm.1
        rw [eqToHom_refl, Category.id_comp]; exact liftP_fst Pm
      have hlev := (hdict (liftP Pm)).mpr (by rw [hPpt, hQpt]; exact hDB)
      obtain ⟨-, hΔ'', hDB'⟩ := hlev
      exact hDB'
  have pushP_mem : ∀ P : {P : Section (xet.curve.map (ψ).toRingHom) //
            (∃ χ : OriginChartRing (xet.curve.map ψ.toRingHom) →+* T, ReducesToOrigin P χ (maximalIdeal T)) ∧
            IsDrinfeldBasis ((𝒢.restrictScalars W₀) T (xet.curve.map (ψ).toRingHom) (xet.curve.isUnit_Δ_map (ψ).toRingHom xet.isUnit_Δ)) q P Q},
      ((∃ (hP : (P.1.1 ≫ Proj.map φc hφc) ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom))
                 (hQ : Qm ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom)),
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                   (Spec.map (CommRingCat.ofHom (ψ).toRingHom)) ⟨(P.1.1 ≫ Proj.map φc hφc), hP⟩ ⟨Qm, hQ⟩) ∧
              Spec.map (CommRingCat.ofHom resT) ≫ (P.1.1 ≫ Proj.map φc hφc) =
                (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1) := by
    intro P
    obtain ⟨⟨χ, hχ⟩, hDB⟩ := P.2
    have hP : (P.1.1 ≫ Proj.map φc hφc) ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
      rw [Category.assoc, hsq, ← Category.assoc, P.1.2, Category.id_comp]
    refine ⟨⟨hP, hQover, ?_⟩, ?_⟩
    · have hlev : RawDrinfeldPair.IsLevel (𝒢.restrictScalars W₀) q (xet.curve.map ψ.toRingHom) ⟨(xet.curve.map ψ.toRingHom), P.1, Q⟩ :=
        ⟨rfl, xet.curve.isUnit_Δ_map ψ.toRingHom xet.isUnit_Δ, hDB⟩
      have hov' := (hdict P.1).mp hlev
      rw [hQpt] at hov'
      have hPpt : (⟨P.1.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc, hov P.1⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (projModelStrCR xet.curve)) = ⟨P.1.1 ≫ Proj.map φc hφc, hP⟩ := by
        apply Subtype.ext
        show P.1.1 ≫ eqToHom _ ≫ Proj.map φc hφc = P.1.1 ≫ Proj.map φc hφc
        rw [eqToHom_refl, Category.id_comp]
      rw [hPpt] at hov'
      exact hov'
    · rw [← Category.assoc, RED P.1 χ hχ, Category.assoc, hone_red]
  refine ⟨Q, htorsQ, hnot, hQφ,
    ⟨{ toFun := fun Pm => ⟨liftP Pm, liftP_mem Pm⟩
       invFun := fun P => ⟨P.1.1 ≫ Proj.map φc hφc, pushP_mem P⟩
       left_inv := fun Pm => Subtype.ext (liftP_fst Pm)
       right_inv := fun P => by
         apply Subtype.ext; apply Subtype.ext
         apply hPB.hom_ext
         · exact liftP_fst _
         · rw [(liftP _).2, P.1.2] }, ?_⟩⟩
  intro Pm φ hφ hc
  obtain rfl : φ = φc := glueTr_coefHom_unique xet.curve ψ.toRingHom φ φc hc hcoef
  exact liftP_fst Pm

end S_ModularCurve_LevelModuliPackageAbs_exists_section_equiv_isDrinfeldBasisOver_isDrinfeldBasis_of_isCoefficientHom_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_section_equiv_isDrinfeldBasisOver_isDrinfeldBasis_of_isCoefficientHom_rigidDataH1Pow (solution)
