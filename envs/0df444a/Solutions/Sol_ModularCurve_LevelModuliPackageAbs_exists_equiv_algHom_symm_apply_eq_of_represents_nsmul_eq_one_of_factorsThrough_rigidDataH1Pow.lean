-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_equiv_algHom_symm_apply_eq_of_represents_nsmul_eq_one_of_factorsThrough_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/62fa7d09-22f8-5c67-b3b4-e24b77d42210

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
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

import Theorems.Thm_IsLocalRing_residueMap_comp_algHom_eq_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_equiv_algHom_symm_apply_eq_of_represents_nsmul_eq_one_of_factorsThrough_rigidDataH1Pow

set_option autoImplicit false

p2m_open "ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup AlgebraicGeometry CategoryTheory NeronModelInfra Polynomial AlgebraicGeometry.Polynomial"

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 6400000 in
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
        (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt k)) :
    ∃ β : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w),
          {d : (Pet.B₀ →ₐ[W₀] T) × (base (T := T) ⟶ projModelCR xet.curve) //
            (∀ b : Pet.B₀, resT (d.1 b) = ψet b) ∧
            (∃ hQ : d.2 ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom d.1.toRingHom),
              ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨d.2, hQ⟩ =
                ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _) ∧
            Spec.map (CommRingCat.ofHom resT) ≫ d.2 =
              Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1} ≃ (S →ₐ[W₀] T),
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) (Φ : S →ₐ[W₀] T),
          (((β T resT hT₁ hT₂ hT₃).symm Φ).1 :
              (Pet.B₀ →ₐ[W₀] T) × (base (T := T) ⟶ projModelCR xet.curve)) =
            ((Φ.comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ),
              Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1) := by
  classical

  have nsmul_nat : ∀ {Tsch Tsch' : Scheme} (t : Tsch ⟶ Spec (CommRingCat.of Pet.B₀))
      (t' : Tsch' ⟶ Spec (CommRingCat.of Pet.B₀)) (ψm : Tsch' ⟶ Tsch) (hψm : ψm ≫ t = t')
      (x : SchemeHomOver t (projModelStrCR xet.curve)) (n : ℕ),
      schemeHomOverComp ψm hψm (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul t n x) =
        ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul t' n (schemeHomOverComp ψm hψm x) := by
    intro Tsch Tsch' t t' ψm hψm x n
    induction n with
    | zero => exact ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one_natural t t' ψm hψm
    | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).mul_natural, ih]

  have memΦ : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) (Φ : S →ₐ[W₀] T),
      (∀ b : Pet.B₀, resT (((Φ.comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ)) b) = ψet b) ∧
      (∃ hQ : (Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1) ≫ projModelStrCR xet.curve =
          Spec.map (CommRingCat.ofHom ((Φ.comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ)).toRingHom),
        ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1, hQ⟩ =
          ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _) ∧
      Spec.map (CommRingCat.ofHom resT) ≫ (Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1) =
        Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1 := by
    intro T _ _ _ _ resT hT₁ hT₂ hT₃ Φ
    have hcomp : ∀ s : S, resT (Φ s) = resS s :=
      IsLocalRing.residueMap_comp_algHom_eq_of_surjective W₀ k res₀ hres₀ S resS hkerS hresS₀ T resT hT₃ Φ
    have hover : (Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1) ≫ projModelStrCR xet.curve =
        Spec.map (CommRingCat.ofHom ((Φ.comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ)).toRingHom) := by
      rw [Category.assoc, Qu.2, ← Spec.map_comp]
      rfl
    refine ⟨fun b => ?_, ⟨hover, ?_⟩, ?_⟩
    · exact (hcomp _).trans (hψet b).symm
    · have hψ' : Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ CQ)) =
          Spec.map (CommRingCat.ofHom ((Φ.comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ)).toRingHom) := by
        rw [← Spec.map_comp]; rfl
      have hn := nsmul_nat _ _ (Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S)))) hψ' Qu q
      rw [hQu, ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one_natural] at hn
      exact hn.symm
    · rw [← Category.assoc, ← Spec.map_comp]
      show Spec.map (CommRingCat.ofHom (resT.comp (Φ.toRingHom.comp (ιS : CQ →+* S)))) ≫ Qu.1 = _
      congr 3
      ext c
      exact hcomp (ιS c)

  let F : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w), (S →ₐ[W₀] T) →
      {d : (Pet.B₀ →ₐ[W₀] T) × (base (T := T) ⟶ projModelCR xet.curve) //
            (∀ b : Pet.B₀, resT (d.1 b) = ψet b) ∧
            (∃ hQ : d.2 ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom d.1.toRingHom),
              ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨d.2, hQ⟩ =
                ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _) ∧
            Spec.map (CommRingCat.ofHom resT) ≫ d.2 =
              Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1} :=
    fun T _ _ _ _ resT hT₁ hT₂ hT₃ Φ => ⟨(((Φ).comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ), Spec.map (CommRingCat.ofHom ((Φ).toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1), memΦ T resT hT₁ hT₂ hT₃ Φ⟩

  have inj : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w), Function.Injective (F T resT hT₁ hT₂ hT₃) := by
    intro T _ _ _ _ resT hT₁ hT₂ hT₃ Φ₁ Φ₂ h
    have h' := congrArg Subtype.val h
    have hψ : ((Φ₁).comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ) = ((Φ₂).comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ) := congrArg Prod.fst h'
    have hQm : Spec.map (CommRingCat.ofHom ((Φ₁).toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1 = Spec.map (CommRingCat.ofHom ((Φ₂).toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1 := congrArg Prod.snd h'
    letI : Algebra Pet.B₀ T := (((Φ₁).comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ)).toRingHom.toAlgebra
    obtain ⟨-, ⟨hQ, htors⟩, -⟩ := memΦ T resT hT₁ hT₂ hT₃ Φ₁
    obtain ⟨χ, -, huniq⟩ := (hrep T ⟨_, hQ⟩).mp htors
    let χ₁ : CQ →ₐ[Pet.B₀] T :=
      { toRingHom := Φ₁.toRingHom.comp (ιS : CQ →+* S), commutes' := fun b => rfl }
    let χ₂ : CQ →ₐ[Pet.B₀] T :=
      { toRingHom := Φ₂.toRingHom.comp (ιS : CQ →+* S)
        commutes' := fun b => by
          show Φ₂ (ιS (algebraMap Pet.B₀ CQ b)) = (((Φ₁).comp ιS).comp (IsScalarTower.toAlgHom W₀ Pet.B₀ CQ)) b
          rw [hψ]; rfl }
    have e1 : χ₁ = χ := huniq χ₁ rfl
    have e2 : χ₂ = χ := huniq χ₂ hQm.symm
    have e12 : ∀ c : CQ, Φ₂ (ιS c) = Φ₁ (ιS c) := fun c =>
      congrArg (fun χ' : CQ →ₐ[Pet.B₀] T => χ' c) (e2.trans e1.symm)
    have hcomp₁ : ∀ s : S, resT (Φ₁ s) = resS s :=
      IsLocalRing.residueMap_comp_algHom_eq_of_surjective W₀ k res₀ hres₀ S resS hkerS hresS₀ T resT hT₃ Φ₁
    have hcomp₂ : ∀ s : S, resT (Φ₂ s) = resS s :=
      IsLocalRing.residueMap_comp_algHom_eq_of_surjective W₀ k res₀ hres₀ S resS hkerS hresS₀ T resT hT₃ Φ₂
    obtain ⟨Φ, -, hΦuniq⟩ := hfacS T resT hT₁ hT₂ hT₃ (Φ₁.comp ιS) (fun c => hcomp₁ (ιS c))
    have u1 : Φ₁ = Φ := hΦuniq Φ₁ ⟨hcomp₁, fun c => rfl⟩
    have u2 : Φ₂ = Φ := hΦuniq Φ₂ ⟨hcomp₂, fun c => e12 c⟩
    exact u1.trans u2.symm

  have surj : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w), Function.Surjective (F T resT hT₁ hT₂ hT₃) := by
    intro T _ _ _ _ resT hT₁ hT₂ hT₃ d
    obtain ⟨hn1, ⟨hQ, htors⟩, hn4⟩ := d.2
    letI : Algebra Pet.B₀ T := d.1.1.toRingHom.toAlgebra
    obtain ⟨χ, hχ0, -⟩ := (hrep T ⟨d.1.2, hQ⟩).mp htors
    have hχ : Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Qu.1 = d.1.2 := hχ0
    let χW : CQ →ₐ[W₀] T :=
      { toRingHom := χ.toRingHom
        commutes' := fun w => by
          show χ (algebraMap W₀ CQ w) = algebraMap W₀ T w
          rw [IsScalarTower.algebraMap_apply W₀ Pet.B₀ CQ, χ.commutes]
          exact d.1.1.commutes w }

    have hres : ∀ c : CQ, resT (χW c) = resS (ιS c) := by
      letI algk : Algebra Pet.B₀ k := ψet.toRingHom.toAlgebra
      have hψet' : Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ CQ)) = Spec.map (CommRingCat.ofHom (algebraMap Pet.B₀ k)) := by
        rw [← Spec.map_comp]
        show Spec.map (CommRingCat.ofHom ((resS.comp (ιS : CQ →+* S)).comp (algebraMap Pet.B₀ CQ))) = _
        congr 2
        exact RingHom.ext (fun b => (hψet b).symm)
      have htorsk : ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q (schemeHomOverComp _ hψet' Qu) = ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _ := by
        rw [← nsmul_nat, hQu, ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one_natural]
      obtain ⟨χk, -, hunik⟩ := (hrep k (schemeHomOverComp _ hψet' Qu)).mp htorsk
      let c1 : CQ →ₐ[Pet.B₀] k :=
        { toRingHom := resS.comp (ιS : CQ →+* S), commutes' := fun b => (hψet b).symm }
      let c2 : CQ →ₐ[Pet.B₀] k :=
        { toRingHom := resT.comp χ.toRingHom
          commutes' := fun b => by
            show resT (χ (algebraMap Pet.B₀ CQ b)) = ψet b
            rw [χ.commutes]; exact hn1 b }
      have e1 : c1 = χk := hunik c1 rfl
      have e2 : c2 = χk := hunik c2 (by
        show Spec.map (CommRingCat.ofHom (resT.comp χ.toRingHom)) ≫ Qu.1 =
          Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1
        rw [← hn4, ← hχ, ← Category.assoc, ← Spec.map_comp]; rfl)
      intro c
      exact congrArg (fun φ : CQ →ₐ[Pet.B₀] k => φ c) (e2.trans e1.symm)
    obtain ⟨Φ, ⟨-, hΦι⟩, -⟩ := hfacS T resT hT₁ hT₂ hT₃ χW hres
    refine ⟨Φ, Subtype.ext (Prod.ext ?_ ?_)⟩
    · apply AlgHom.ext; intro b
      show Φ (ιS (algebraMap Pet.B₀ CQ b)) = d.1.1 b
      rw [hΦι]; show χ (algebraMap Pet.B₀ CQ b) = _; rw [χ.commutes]; rfl
    · show Spec.map (CommRingCat.ofHom (Φ.toRingHom.comp (ιS : CQ →+* S))) ≫ Qu.1 = d.1.2
      have : Φ.toRingHom.comp (ιS : CQ →+* S) = χ.toRingHom := RingHom.ext hΦι
      rw [this]; exact hχ
  refine ⟨fun T _ _ _ _ resT hT₁ hT₂ hT₃ =>
    (Equiv.ofBijective (F T resT hT₁ hT₂ hT₃) ⟨inj T resT hT₁ hT₂ hT₃, surj T resT hT₁ hT₂ hT₃⟩).symm, ?_⟩
  intro T _ _ _ _ resT hT₁ hT₂ hT₃ Φ
  rfl

end S_ModularCurve_LevelModuliPackageAbs_exists_equiv_algHom_symm_apply_eq_of_represents_nsmul_eq_one_of_factorsThrough_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_equiv_algHom_symm_apply_eq_of_represents_nsmul_eq_one_of_factorsThrough_rigidDataH1Pow (solution)
