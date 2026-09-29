-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.exists_algHom_equiv_isDrinfeldBasisOver_natural_of_factorsThrough_gamma0Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/15a90833-7c4d-5ac0-8957-8a608b027fb0

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

import Theorems.Thm_IsLocalRing_residueMap_comp_algHom_eq_of_surjective
import Theorems.Thm_WeierstrassProjModel_exists_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isPullback_projMap_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_projMap_comp_projModelStrCR_of_isCoefficientHom
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_one_comp_projMap_eq_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_isLevel_iff_isDrinfeldBasisOver_comp_projMap
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_IsDrinfeldBasisOver_exists_comp_fst_schemeKer_eq
import Theorems.Thm_ModularCurve_FullLevel_variableChange_map_eq_one_of_eq_act_of_map_residue_eq_gamma0Pow
import Theorems.Thm_WeierstrassCurve_VariableChange_eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_section_eq_of_comp_projMap_eq_of_isCoefficientHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algHom_equiv_isDrinfeldBasisOver_natural_of_factorsThrough_gamma0Pow
p2m_attr_erase "instance" "WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup AlgebraicGeometry CategoryTheory NeronModelInfra Polynomial AlgebraicGeometry.Polynomial"

attribute [local instance] MvPolynomial.gradedAlgebra

theorem glueNF_rel_of_quot_mk_eq {A : Type} [CommRing A] (Rg : ModularCurve.RigidWeierstrassData A)
    {T : Type} [CommRing T] [Algebra A T] {a b : Rg.Raw T}
    (h : (Quot.mk _ a : Rg.Pt T) = Quot.mk _ b) : Rg.Rel a b := by
  have hE : Equivalence (Rg.Rel (T := T)) :=
    { refl := fun x => ModularCurve.RigidWeierstrassData.Rel.refl Rg x
      symm := by
        rintro x y ⟨C, rfl⟩
        exact ⟨C⁻¹, by rw [← Rg.act_mul, inv_mul_cancel, Rg.act_one]⟩
      trans := fun h h' => ModularCurve.RigidWeierstrassData.Rel.trans Rg h h' }
  exact hE.eqvGen_iff.mp (Quot.eqvGen_exact h)

theorem glueNF_coefHom_unique {T T' : Type} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ φ' : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (h : IsCoefficientHom W f φ) (h' : IsCoefficientHom W f φ') : φ = φ' := by
  have key : (φ : ProjModelRingCR W →+* ProjModelRingCR (W.map f)).comp (Ideal.Quotient.mk _) =
      (φ' : ProjModelRingCR W →+* ProjModelRingCR (W.map f)).comp (Ideal.Quotient.mk _) := by
    apply MvPolynomial.ringHom_ext
    · intro a; show φ (cls W (MvPolynomial.C a)) = φ' (cls W (MvPolynomial.C a)); rw [h.1 a, h'.1 a]
    · intro i; show φ (cls W (MvPolynomial.X i)) = φ' (cls W (MvPolynomial.X i)); rw [h.2 i, h'.2 i]
  have key' := Ideal.Quotient.ringHom_ext key
  exact GradedRingHom.ext fun x => congrArg (fun g : ProjModelRingCR W →+* _ => g x) key'

theorem glueNF_nsmul_natural_aux {B : Type} [CommRing B] {V : WeierstrassCurve.Projective B}
    (G : WeierstrassProjModel.RelativeGroupLaw B (projModelStrCR V))
    {Tsch Tsch' : Scheme} (t : Tsch ⟶ Spec (CommRingCat.of B)) (t' : Tsch' ⟶ Spec (CommRingCat.of B))
    (ψm : Tsch' ⟶ Tsch) (hψm : ψm ≫ t = t') (x : SchemeHomOver t (projModelStrCR V)) (n : ℕ) :
    schemeHomOverComp ψm hψm (G.nsmul t n x) = G.nsmul t' n (schemeHomOverComp ψm hψm x) := by
  induction n with
  | zero => exact G.one_natural t t' ψm hψm
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, G.mul_natural, ih]

theorem glueNF_projMap_comp {B T K : Type} [CommRing B] [CommRing T] [CommRing K] (V : WeierstrassCurve.Projective B)
    (f : B →+* T) (g : T →+* K)
    (φ₁ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map f))
    (hφ₁ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map f)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map φ₁)
    (c₁ : IsCoefficientHom V f φ₁)
    (φ₂ : projModelGradingCR (V.map f) →+*ᵍ projModelGradingCR ((V.map f).map g))
    (hφ₂ : HomogeneousIdeal.irrelevant (projModelGradingCR ((V.map f).map g)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR (V.map f))).map φ₂)
    (c₂ : IsCoefficientHom (V.map f) g φ₂)
    (φ₃ : projModelGradingCR V →+*ᵍ projModelGradingCR (V.map (g.comp f)))
    (hφ₃ : HomogeneousIdeal.irrelevant (projModelGradingCR (V.map (g.comp f))) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR V)).map φ₃)
    (c₃ : IsCoefficientHom V (g.comp f) φ₃) :
    Proj.map φ₂ hφ₂ ≫ Proj.map φ₁ hφ₁ = Proj.map φ₃ hφ₃ := by
  have c₁₂ : IsCoefficientHom V (g.comp f) (φ₂.comp φ₁) := by
    refine ⟨fun a => ?_, fun i => ?_⟩
    · show φ₂ (φ₁ (cls V (MvPolynomial.C a))) = _
      rw [c₁.1 a, c₂.1 (f a)]; rfl
    · show φ₂ (φ₁ (cls V (MvPolynomial.X i))) = _
      rw [c₁.2 i, c₂.2 i]; rfl
  obtain rfl : φ₃ = φ₂.comp φ₁ := glueNF_coefHom_unique V (g.comp f) _ _ c₃ c₁₂
  exact (Proj.map_comp _ _ hφ₁ hφ₂).symm

theorem glueNF_nsmul_eq_one_of_comp_fst_schemeKer
    {R : Type} [CommRing R] {V : WeierstrassCurve.Projective R}
    (G : WeierstrassProjModel.RelativeGroupLaw R (projModelStrCR V)) (n : ℕ)
    {T : Scheme} {t : T ⟶ Spec (CommRingCat.of R)} (Q : SchemeHomOver t (projModelStrCR V))
    (p : T ⟶ G.schemeKer n)
    (hp : p ≫ CategoryTheory.Limits.pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 = Q.1) :
    G.nsmul t n Q = G.one t := by
  have hQ : schemeHomOverComp Q.1 Q.2 (RelativeGroupLaw.idPoint (f := projModelStrCR V)) = Q :=
    Subtype.ext (by rw [schemeHomOverComp_coe]; exact Category.comp_id _)
  have h1 : CategoryTheory.Limits.pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ projModelStrCR V =
      CategoryTheory.Limits.pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1 := by
    calc CategoryTheory.Limits.pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ projModelStrCR V
        = CategoryTheory.Limits.pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ (G.schemeNsmul n ≫ projModelStrCR V) := by
          rw [RelativeGroupLaw.schemeNsmul_over]
      _ = (CategoryTheory.Limits.pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ G.schemeNsmul n) ≫ projModelStrCR V :=
          (Category.assoc _ _ _).symm
      _ = (CategoryTheory.Limits.pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ (G.one (𝟙 _)).1) ≫ projModelStrCR V := by
          rw [CategoryTheory.Limits.pullback.condition]
      _ = CategoryTheory.Limits.pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ ((G.one (𝟙 _)).1 ≫ projModelStrCR V) :=
          Category.assoc _ _ _
      _ = CategoryTheory.Limits.pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1 := by
          rw [(G.one (𝟙 _)).2, Category.comp_id]
  have hsnd : (p ≫ CategoryTheory.Limits.pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1) ≫ 𝟙 _ = t := by
    rw [Category.comp_id, ← h1, ← Category.assoc, hp]; exact Q.2
  apply Subtype.ext
  have hnat := congrArg Subtype.val
    (G.nsmul_natural (projModelStrCR V) t Q.1 Q.2 n (RelativeGroupLaw.idPoint (f := projModelStrCR V)))
  rw [hQ, schemeHomOverComp_coe] at hnat
  rw [← hnat]
  have h2 := congrArg Subtype.val (G.one_natural (𝟙 _) t (p ≫ CategoryTheory.Limits.pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1) hsnd)
  rw [schemeHomOverComp_coe] at h2
  rw [← h2, ← hp, Category.assoc, Category.assoc]
  show p ≫ CategoryTheory.Limits.pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ G.schemeNsmul n = _
  rw [CategoryTheory.Limits.pullback.condition]

set_option maxHeartbeats 16000000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
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
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))

    (h𝒢r : (𝒢.restrictScalars W₀).IsChordTangent) (h𝒢Or : (𝒢.restrictScalars W₀).IsOriginIdentity)
    (Pet : LevelModuliPackageAbs W₀
      (((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid).toLevelModuliDatum)
    (xet : (((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid).Raw Pet.B₀)
    (hxet : (Quot.mk _ xet :
      (((ModularCurve.gamma0PowComponent W₀ M' hM').prod
        ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid).Pt Pet.B₀) =
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
    (hDk : ModularCurve.IsLevelPStructure (xet.curve.map ψet.toRingHom) ℓ (xet.level.2.1.map ψet.toRingHom))
    (hyk : RawDrinfeldPair.IsLevel 𝒢 q (xet.curve.map ψet.toRingHom)
      ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩)
    (hρyk : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ρ P₀.univ =
      (Quot.mk _ (⟨xet.curve.map ψet.toRingHom, hΔk,
          ⟨fun p => (xet.level.1 p).map ψet.toRingHom, xet.level.2.1.map ψet.toRingHom,
            ⟨xet.curve.map ψet.toRingHom, (𝒢 k (xet.curve.map ψet.toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩⟩,
          ⟨hhk, hDk, hyk⟩⟩ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw k) :
        (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt k)) :
    ∃ α : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w),
          (R →ₐ[W₀] T) ≃
          {d : (Pet.B₀ →ₐ[W₀] T) ×
              ((base (T := T) ⟶ projModelCR xet.curve) × (base (T := T) ⟶ projModelCR xet.curve)) //
            (∀ b : Pet.B₀, resT (d.1 b) = ψet b) ∧
            (∃ (hP : d.2.1 ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom d.1.toRingHom))
               (hQ : d.2.2 ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom d.1.toRingHom)),
               ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                 (Spec.map (CommRingCat.ofHom d.1.toRingHom)) ⟨d.2.1, hP⟩ ⟨d.2.2, hQ⟩ ∧
               ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨d.2.2, hQ⟩ =
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _) ∧
            Spec.map (CommRingCat.ofHom resT) ≫ d.2.1 =
              (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1 ∧
            Spec.map (CommRingCat.ofHom resT) ≫ d.2.2 =
              Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1},
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
        (T' : Type) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [Algebra W₀ T']
        (resT' : T' →+* k) (hT'₁ : Function.Surjective resT') (hT'₂ : RingHom.ker resT' = maximalIdeal T')
        (hT'₃ : ∀ w : W₀, resT' (algebraMap W₀ T' w) = res₀ w)
        (f : T →ₐ[W₀] T') (_ : ∀ t : T, resT' (f t) = resT t) (φ : R →ₐ[W₀] T),
        ((α T' resT' hT'₁ hT'₂ hT'₃ (f.comp φ)).1 :
            (Pet.B₀ →ₐ[W₀] T') × ((base (T := T') ⟶ projModelCR xet.curve) × (base (T := T') ⟶ projModelCR xet.curve))) =
          (f.comp (α T resT hT₁ hT₂ hT₃ φ).1.1,
            (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (α T resT hT₁ hT₂ hT₃ φ).1.2.1,
             Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (α T resT hT₁ hT₂ hT₃ φ).1.2.2)) := by
  classical

  obtain ⟨x, hx⟩ := Quot.exists_rep P₀.univ

  have NFE : ∀ (T : Type) [CommRing T] [Algebra W₀ T] [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
      (z : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T),
      ∃ (ψ : Pet.B₀ →ₐ[W₀] T) (P Q : Section (xet.curve.map ψ.toRingHom)) (C : WeierstrassCurve.VariableChange T),
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z).curve = xet.curve.map ψ.toRingHom ∧
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z).level =
          ((fun p => (xet.level.1 p).map ψ.toRingHom), (xet.level.2.1.map ψ.toRingHom, (⟨xet.curve.map ψ.toRingHom, P, Q⟩ : RawDrinfeldPair T))) := by
    intro T _ _ _ _ z
    let Det := (((ModularCurve.gamma0PowComponent W₀ M' hM').prod ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid)
    let zet : Det.Raw T :=
      ⟨z.curve, z.isUnit_Δ, ⟨z.level.1, z.level.2.1, PUnit.unit⟩, ⟨z.isLevel.1, z.isLevel.2.1, trivial⟩⟩
    let ψ : Pet.B₀ →ₐ[W₀] T := Pet.classify (Quot.mk _ zet : Det.Pt T)
    have hclass : (Quot.mk _ (Det.mapRing ψ xet) : Det.Pt T) = Quot.mk _ zet := by
      have := Pet.map_classify (Quot.mk _ zet : Det.Pt T)
      rw [← hxet] at this
      exact this
    obtain ⟨Cb, hCb⟩ := glueNF_rel_of_quot_mk_eq Det hclass
    have hback : Det.act Cb⁻¹ zet = Det.mapRing ψ xet := by
      rw [hCb, ← Det.act_mul, inv_mul_cancel, Det.act_one]
    have E1' : Cb⁻¹ • z.curve = xet.curve.map ψ.toRingHom := congrArg (fun w => w.curve) hback
    have E2' : (fun p : ↥M'.primeFactors => ModularCurve.kernelVariableChangeDeg Cb⁻¹ (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (z.level.1 p)) = (fun p => (xet.level.1 p).map ψ.toRingHom) :=
      congrArg (fun w => w.level.1) hback
    have E3' : z.level.2.1.variableChange Cb⁻¹ = xet.level.2.1.map ψ.toRingHom :=
      congrArg (fun w => w.level.2.1) hback

    have hpc : z.level.2.2.curve = z.curve := z.isLevel.2.2.1
    obtain ⟨hc1, -⟩ := h𝒯.1 T Cb⁻¹ z.level.2.2
    have hcurve' : (𝒯.act Cb⁻¹ z.level.2.2).curve = xet.curve.map ψ.toRingHom := by
      rw [hc1, hpc, E1']
    generalize hp : 𝒯.act Cb⁻¹ z.level.2.2 = p' at hcurve'
    obtain ⟨c, P, Q⟩ := p'
    obtain rfl : c = xet.curve.map ψ.toRingHom := hcurve'
    refine ⟨ψ, P, Q, Cb⁻¹, E1', ?_⟩
    exact Prod.ext E2' (Prod.ext E3' hp)

  have NFU : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T] [Algebra A₀ T]
      [IsScalarTower A₀ W₀ T] (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
      (z : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T)
      (ψ : Pet.B₀ →ₐ[W₀] T) (P Q : Section (xet.curve.map ψ.toRingHom)) (C : WeierstrassCurve.VariableChange T)
      (ψ' : Pet.B₀ →ₐ[W₀] T) (P' Q' : Section (xet.curve.map ψ'.toRingHom)) (C' : WeierstrassCurve.VariableChange T),
      ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z).curve = xet.curve.map (ψ).toRingHom ∧
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z).level =
          ((fun p => (xet.level.1 p).map (ψ).toRingHom), (xet.level.2.1.map (ψ).toRingHom, (⟨xet.curve.map (ψ).toRingHom, P, Q⟩ : RawDrinfeldPair T))) →
      ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C' z).curve = xet.curve.map (ψ').toRingHom ∧
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C' z).level =
          ((fun p => (xet.level.1 p).map (ψ').toRingHom), (xet.level.2.1.map (ψ').toRingHom, (⟨xet.curve.map (ψ').toRingHom, P', Q'⟩ : RawDrinfeldPair T))) →
      ψ = ψ' ∧ C = C' := by
    intro T _ _ _ _ _ _ resT hT₁ hT₂ z ψ P Q C ψ' P' Q' C' h h'
    obtain ⟨hc, hl⟩ := h
    obtain ⟨hc', hl'⟩ := h'
    let Det := (((ModularCurve.gamma0PowComponent W₀ M' hM').prod ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid)
    have hw' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C' z = (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act (C' * C⁻¹) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z) := by
      rw [← (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act_mul, inv_mul_cancel_right]
    have e1 : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z).level.1 = (fun p => (xet.level.1 p).map ψ.toRingHom) := by rw [hl]
    have e2 : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z).level.2.1 = xet.level.2.1.map ψ.toRingHom := by rw [hl]
    have e1' : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C' z).level.1 = (fun p => (xet.level.1 p).map ψ'.toRingHom) := by rw [hl']
    have e2' : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C' z).level.2.1 = xet.level.2.1.map ψ'.toRingHom := by rw [hl']
    have hcw : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act (C' * C⁻¹) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z)).curve = (C' * C⁻¹) • ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z).curve := rfl
    have hl1w : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act (C' * C⁻¹) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z)).level.1 =
        (fun p : ↥M'.primeFactors => ModularCurve.kernelVariableChangeDeg (C' * C⁻¹) (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z).level.1 p)) := rfl
    have hl2w : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act (C' * C⁻¹) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z)).level.2.1 = ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z).level.2.1.variableChange (C' * C⁻¹) := rfl

    have het : (Quot.mk _ (Det.mapRing ψ xet) : Det.Pt T) = Quot.mk _ (Det.mapRing ψ' xet) := by
      apply Quot.sound
      refine ⟨C' * C⁻¹, ?_⟩
      apply ModularCurve.LevelComponent.Raw.ext'
      · show xet.curve.map ψ'.toRingHom = (C' * C⁻¹) • xet.curve.map ψ.toRingHom
        rw [← hc, ← hc', hw', hcw]
      · show ((fun p => (xet.level.1 p).map ψ'.toRingHom), (xet.level.2.1.map ψ'.toRingHom, PUnit.unit)) =
          ((fun p : ↥M'.primeFactors => ModularCurve.kernelVariableChangeDeg (C' * C⁻¹) (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
              ((fun p => (xet.level.1 p).map ψ.toRingHom) p)),
            ((xet.level.2.1.map ψ.toRingHom).variableChange (C' * C⁻¹), PUnit.unit))
        rw [← e1, ← e2, ← e1', ← e2', hw', hl1w, hl2w]
    have u1 : ψ = Pet.classify (Quot.mk _ (Det.mapRing ψ xet) : Det.Pt T) :=
      Pet.classify_unique _ ψ (by rw [← hxet]; try rfl)
    have u2 : ψ' = Pet.classify (Quot.mk _ (Det.mapRing ψ xet) : Det.Pt T) :=
      Pet.classify_unique _ ψ' (by rw [← hxet, het]; try rfl)
    have hψ : ψ = ψ' := u1.trans u2.symm
    subst hψ
    refine ⟨rfl, ?_⟩
    have hmod := ModularCurve.FullLevel.variableChange_map_eq_one_of_eq_act_of_map_residue_eq_gamma0Pow q ℓ M' hℓ3 A₀ hℓ hM 𝒢 𝒯
      T k resT hℓk ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C z) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C' z) (C' * C⁻¹) hw' (by rw [hc, hc']) (by rw [e2, e2'])
    have hfix : (C' * C⁻¹) • xet.curve.map ψ.toRingHom = xet.curve.map ψ.toRingHom := by
      have := hcw
      rw [hc, ← hw', hc'] at this
      exact this.symm
    have h1 := WeierstrassCurve.VariableChange.eq_one_of_map_eq_one_of_smul_eq_of_isArtinianRing k T resT hT₁ hT₂
      (xet.curve.map ψ.toRingHom) (xet.curve.isUnit_Δ_map ψ.toRingHom xet.isUnit_Δ) (C' * C⁻¹) hmod hfix
    exact (mul_inv_eq_one.mp h1).symm

  have hone : ∀ {Ssch : Scheme} (s : Ssch ⟶ Spec (CommRingCat.of Pet.B₀)),
      (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one s).1 = s ≫ (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (𝟙 _)).1 := by
    intro Ssch s
    have := congrArg Subtype.val (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one_natural (𝟙 _) s s (Category.comp_id s))
    rw [schemeHomOverComp_coe] at this
    exact this.symm
  obtain ⟨χB, hχB, hχBx, hχBz⟩ := h𝒢Or Pet.B₀ xet.curve xet.isUnit_Δ
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  have MEM : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
      (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
      (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) (φ : R →ₐ[W₀] T),
      letI : Algebra A₀ T := algebraRestrict A₀ W₀ T
      letI : IsScalarTower A₀ W₀ T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      ∀ (ψ : Pet.B₀ →ₐ[W₀] T) (P Q : Section (xet.curve.map ψ.toRingHom)) (C : WeierstrassCurve.VariableChange T),
      ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).curve = xet.curve.map (ψ).toRingHom ∧
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).level =
          ((fun p => (xet.level.1 p).map (ψ).toRingHom), (xet.level.2.1.map (ψ).toRingHom, (⟨xet.curve.map (ψ).toRingHom, P, Q⟩ : RawDrinfeldPair T))) →
      ∀ (φc : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψ.toRingHom))
        (hφc : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψ.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φc),
        IsCoefficientHom xet.curve ψ.toRingHom φc →
        ((∀ b : Pet.B₀, resT ((ψ) b) = ψet b) ∧
            (∃ (hP : (P.1 ≫ Proj.map φc hφc) ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom))
               (hQ : (Q.1 ≫ Proj.map φc hφc) ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom (ψ).toRingHom)),
               ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                 (Spec.map (CommRingCat.ofHom (ψ).toRingHom)) ⟨P.1 ≫ Proj.map φc hφc, hP⟩ ⟨Q.1 ≫ Proj.map φc hφc, hQ⟩ ∧
               ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨Q.1 ≫ Proj.map φc hφc, hQ⟩ =
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _) ∧
            Spec.map (CommRingCat.ofHom resT) ≫ (P.1 ≫ Proj.map φc hφc) =
              (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1 ∧
            Spec.map (CommRingCat.ofHom resT) ≫ (Q.1 ≫ Proj.map φc hφc) =
              Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1) := by
    intro T _ _ _ _ resT hT₁ hT₂ hT₃ φ
    letI instA : Algebra A₀ T := algebraRestrict A₀ W₀ T
    letI instT : IsScalarTower A₀ W₀ T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    intro ψ P Q C hNF φc hφc hcoef
    obtain ⟨hc, hl⟩ := hNF
    have e2 : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).level.2.1 = xet.level.2.1.map ψ.toRingHom := by rw [hl]
    have e3 : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).level.2.2 = ⟨xet.curve.map ψ.toRingHom, P, Q⟩ := by rw [hl]
    have e1 : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).level.1 = (fun p => (xet.level.1 p).map ψ.toRingHom) := by rw [hl]
    have hsq := WeierstrassCurve.DrinfeldGlobal.projMap_comp_projModelStrCR_of_isCoefficientHom xet.curve ψ.toRingHom φc hφc hcoef

    let resTW : T →ₐ[W₀] k := { toRingHom := resT, commutes' := fun w => (hT₃ w).trans (hk₀ w).symm }
    let resTA : T →ₐ[A₀] k :=
      { toRingHom := resT
        commutes' := fun a => by
          show resT (algebraMap W₀ T (algebraMap A₀ W₀ a)) = algebraMap A₀ k a
          rw [hT₃, ← hk₀, IsScalarTower.algebraMap_apply A₀ W₀ k] }

    have hφρ : resTA.comp ((φ.restrictScalars A₀).comp ι) = ρ := by
      apply AlgHom.ext; intro b
      show resT (φ (ι b)) = ρ b
      rw [hρ]
      exact IsLocalRing.residueMap_comp_algHom_eq_of_surjective W₀ k res₀ hres₀ R resR hkerR hresR₀ T resT hT₃ φ (ι b)
    have hzred : (Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing resTA ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x))) : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt k) =
        (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ρ P₀.univ := by
      rw [(rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing_act, ← (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing_comp, hφρ, ← hx]
      exact Quot.sound ⟨(C.map resTA.toRingHom)⁻¹, by rw [← (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act_mul, inv_mul_cancel, (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act_one]⟩
    rw [hρyk] at hzred
    obtain ⟨Cb, hCb⟩ := glueNF_rel_of_quot_mk_eq (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯) hzred

    let Det := (((ModularCurve.gamma0PowComponent W₀ M' hM').prod ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid)
    have ycurve : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act Cb ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing resTA ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)))).curve =
        Cb • (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).curve.map resT) := rfl
    have ylev1 : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act Cb ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing resTA ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)))).level.1 =
        (fun p : ↥M'.primeFactors => ModularCurve.kernelVariableChangeDeg Cb (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) ((((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).level.1 p).map resT)) := rfl
    have ylev21 : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act Cb ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing resTA ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)))).level.2.1 =
        (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).level.2.1.map resT).variableChange Cb := rfl
    rw [hc] at ycurve
    rw [e1] at ylev1
    rw [e2] at ylev21
    have hetk : (Quot.mk _ (Det.mapRing (resTW.comp ψ) xet) : Det.Pt k) = Quot.mk _ (Det.mapRing ψet xet) := by
      apply Quot.sound
      refine ⟨Cb, ?_⟩
      rw [Det.mapRing_comp]
      apply ModularCurve.LevelComponent.Raw.ext'
      · exact (congrArg (fun w => w.curve) hCb).trans ycurve
      · refine Prod.ext ((congrArg (fun w => w.level.1) hCb).trans ylev1) (Prod.ext ((congrArg (fun w => w.level.2.1) hCb).trans ylev21) rfl)
    have u1 : resTW.comp ψ = Pet.classify (Quot.mk _ (Det.mapRing ψet xet) : Det.Pt k) :=
      Pet.classify_unique _ _ (by rw [← hxet, ← hetk]; try rfl)
    have u2 : ψet = Pet.classify (Quot.mk _ (Det.mapRing ψet xet) : Det.Pt k) :=
      Pet.classify_unique _ _ (by rw [← hxet]; try rfl)
    have n1 : resTW.comp ψ = ψet := u1.trans u2.symm
    subst n1

    have hCb1 : Cb = 1 := by
      have h := ModularCurve.FullLevel.variableChange_map_eq_one_of_eq_act_of_map_residue_eq_gamma0Pow q ℓ M' hℓ3 A₀ hℓ hM 𝒢 𝒯
        k k (RingHom.id k) hℓk ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing resTA ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x))) _ Cb hCb
        (by
          show (xet.curve.map (resTW.comp ψ).toRingHom).map (RingHom.id k) = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).curve.map resT).map (RingHom.id k)
          rw [hc]; rfl)
        (by
          show (xet.level.2.1.map (resTW.comp ψ).toRingHom).map (RingHom.id k) = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).level.2.1.map resT).map (RingHom.id k)
          rw [e2]; rfl)
      rwa [WeierstrassCurve.VariableChange.map_id] at h
    rw [hCb1, (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act_one] at hCb

    have hpair : 𝒯.map resTA ⟨xet.curve.map ψ.toRingHom, P, Q⟩ =
        ⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ := by
      rw [← e3]
      exact (congrArg (fun w => w.level.2.2) hCb).symm

    obtain ⟨φr, hφr, hcoefr⟩ := WeierstrassProjModel.exists_isCoefficientHom (xet.curve.map ψ.toRingHom) resT
    obtain ⟨hc2, hpin⟩ := h𝒯.2 T k resTA ⟨xet.curve.map ψ.toRingHom, P, Q⟩
    obtain ⟨hP2, hQ2⟩ := hpin φr hφr hcoefr
    have pinTransfer : ∀ (m m' : RawDrinfeldPair k) (_ : m = m') (W' : WeierstrassCurve k)
        (h : m.curve = W') (h' : m'.curve = W'),
        m.P.1 ≫ eqToHom (congrArg projModelCR h) = m'.P.1 ≫ eqToHom (congrArg projModelCR h') ∧
        m.Q.1 ≫ eqToHom (congrArg projModelCR h) = m'.Q.1 ≫ eqToHom (congrArg projModelCR h') := by
      rintro m m' rfl W' h h'; exact ⟨rfl, rfl⟩
    have hc2' : (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).curve =
        (xet.curve.map ψ.toRingHom).map resTA.toRingHom := rfl
    obtain ⟨tP, tQ⟩ := pinTransfer _ _ hpair _ hc2 hc2'
    rw [← Category.assoc, tP, Category.assoc] at hP2
    rw [← Category.assoc, tQ, Category.assoc] at hQ2
    have heq : ∀ {Z : Scheme} (g : projModelCR ((xet.curve.map ψ.toRingHom).map resTA.toRingHom) ⟶ Z),
        eqToHom (congrArg projModelCR hc2') ≫ g = g := by
      intro Z g
      have : eqToHom (congrArg projModelCR hc2') = 𝟙 _ := eqToHom_refl _ _
      rw [this]; exact Category.id_comp g
    rw [heq] at hP2 hQ2

    obtain ⟨φe, hφe, hcoefe, hQk1⟩ := hQk_pin
    have hcomp : Proj.map φr hφr ≫ Proj.map φc hφc = Proj.map φe hφe :=
      glueNF_projMap_comp xet.curve ψ.toRingHom resT φc hφc hcoef φr hφr hcoefr φe hφe hcoefe
    obtain ⟨χk, hχk, hχkx, hχkz⟩ := h𝒢O k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk
    have h1e := WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection xet.curve (resTW.comp ψ).toRingHom
      φe hφe hcoefe ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ) (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk) χB hχB hχBx hχBz χk hχk hχkx hχkz
    have n3 : Spec.map (CommRingCat.ofHom resT) ≫ (P.1 ≫ Proj.map φc hφc) =
        (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom (resTW.comp ψ).toRingHom))).1 := by
      rw [← Category.assoc, ← hP2, Category.assoc]
      have step : (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P.1 ≫ (Proj.map φr hφr ≫ Proj.map φc hφc) = (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P.1 ≫ Proj.map φe hφe :=
        congrArg (fun g => (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P.1 ≫ g) hcomp
      refine step.trans ?_
      rw [hone]
      exact h1e
    have n4 : Spec.map (CommRingCat.ofHom resT) ≫ (Q.1 ≫ Proj.map φc hφc) =
        Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1 := by
      rw [← Category.assoc, ← hQ2, Category.assoc]
      have step : (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q.1 ≫ (Proj.map φr hφr ≫ Proj.map φc hφc) = (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q.1 ≫ Proj.map φe hφe :=
        congrArg (fun g => (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q.1 ≫ g) hcomp
      refine step.trans ?_
      exact hQk1

    have hPov : (P.1 ≫ Proj.map φc hφc) ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
      rw [Category.assoc, hsq, ← Category.assoc, P.2, Category.id_comp]
    have hQov : (Q.1 ≫ Proj.map φc hφc) ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
      rw [Category.assoc, hsq, ← Category.assoc, Q.2, Category.id_comp]
    have hlev : RawDrinfeldPair.IsLevel (𝒢.restrictScalars W₀) q (xet.curve.map ψ.toRingHom)
        ⟨xet.curve.map ψ.toRingHom, P, Q⟩ := by
      have := ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).isLevel.2.2
      rw [e3, hc] at this
      exact this
    have hov' : ∀ (R' : Section (xet.curve.map ψ.toRingHom)),
        (R'.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc) ≫ projModelStrCR xet.curve =
          Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
      intro R'
      rw [eqToHom_refl, Category.id_comp, Category.assoc, hsq, ← Category.assoc, R'.2, Category.id_comp]
    have hDB := (WeierstrassCurve.DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap q (𝒢.restrictScalars W₀) h𝒢Or
      Pet.B₀ xet.curve xet.isUnit_Δ T ψ φc hφc hcoef hsq ⟨xet.curve.map ψ.toRingHom, P, Q⟩ rfl (hov' P) (hov' Q)).mp hlev
    have hPpt : (⟨P.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc, hov' P⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (projModelStrCR xet.curve)) = ⟨P.1 ≫ Proj.map φc hφc, hPov⟩ := by
      apply Subtype.ext; show P.1 ≫ eqToHom _ ≫ Proj.map φc hφc = _; rw [eqToHom_refl, Category.id_comp]
    have hQpt : (⟨Q.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc, hov' Q⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (projModelStrCR xet.curve)) = ⟨Q.1 ≫ Proj.map φc hφc, hQov⟩ := by
      apply Subtype.ext; show Q.1 ≫ eqToHom _ ≫ Proj.map φc hφc = _; rw [eqToHom_refl, Category.id_comp]
    rw [hPpt, hQpt] at hDB
    obtain ⟨-, pK, hpK⟩ :=
      WeierstrassProjModel.RelativeGroupLaw.IsDrinfeldBasisOver.exists_comp_fst_schemeKer_eq _ hq2 hDB
    have htors := glueNF_nsmul_eq_one_of_comp_fst_schemeKer _ q _ pK hpK
    exact ⟨fun b => rfl, ⟨hPov, hQov, hDB, htors⟩, n3, n4⟩

  have COEF : ∀ {T : Type} [CommRing T] (g : Pet.B₀ →+* T),
      ∃ φc : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map g),
        ∃ (hφc : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map g)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φc), IsCoefficientHom xet.curve g φc :=
    fun g => WeierstrassProjModel.exists_isCoefficientHom xet.curve g
  have NFE' : ∀ (T : Type) [CommRing T] [Algebra W₀ T] [Algebra A₀ T] [IsScalarTower A₀ W₀ T] (z : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T),
      ∃ s : ((ψ : Pet.B₀ →ₐ[W₀] T) × (Section (xet.curve.map (ψ).toRingHom) × Section (xet.curve.map (ψ).toRingHom))) × WeierstrassCurve.VariableChange T,
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act s.2 z).curve = xet.curve.map s.1.1.toRingHom ∧
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act s.2 z).level =
          ((fun p => (xet.level.1 p).map s.1.1.toRingHom), (xet.level.2.1.map s.1.1.toRingHom,
            (⟨xet.curve.map s.1.1.toRingHom, s.1.2.1, s.1.2.2⟩ : RawDrinfeldPair T))) := by
    intro T _ _ _ _ z
    obtain ⟨ψ, P, Q, C, h⟩ := NFE T z
    exact ⟨⟨⟨ψ, (P, Q)⟩, C⟩, h⟩

  let Ffun : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w), (R →ₐ[W₀] T) →
      {d : (Pet.B₀ →ₐ[W₀] T) ×
              ((base (T := T) ⟶ projModelCR xet.curve) × (base (T := T) ⟶ projModelCR xet.curve)) //
            (∀ b : Pet.B₀, resT (d.1 b) = ψet b) ∧
            (∃ (hP : d.2.1 ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom d.1.toRingHom))
               (hQ : d.2.2 ≫ projModelStrCR xet.curve = Spec.map (CommRingCat.ofHom d.1.toRingHom)),
               ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).IsDrinfeldBasisOver q
                 (Spec.map (CommRingCat.ofHom d.1.toRingHom)) ⟨d.2.1, hP⟩ ⟨d.2.2, hQ⟩ ∧
               ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).nsmul _ q ⟨d.2.2, hQ⟩ =
                 ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one _) ∧
            Spec.map (CommRingCat.ofHom resT) ≫ d.2.1 =
              (((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ).one (Spec.map (CommRingCat.ofHom ψet.toRingHom))).1 ∧
            Spec.map (CommRingCat.ofHom resT) ≫ d.2.2 =
              Spec.map (CommRingCat.ofHom (resS.comp (ιS : CQ →+* S))) ≫ Qu.1} :=
    fun T _ _ _ _ resT hT₁ hT₂ hT₃ φ =>
      letI : Algebra A₀ T := algebraRestrict A₀ W₀ T
      letI : IsScalarTower A₀ W₀ T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      let s := (NFE' T ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).choose
      let hs := (NFE' T ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).choose_spec
      let c := (COEF s.1.1.toRingHom).choose
      let hc := (COEF s.1.1.toRingHom).choose_spec
      ⟨(s.1.1, (s.1.2.1.1 ≫ Proj.map c hc.fst, s.1.2.2.1 ≫ Proj.map c hc.fst)),
        MEM T resT hT₁ hT₂ hT₃ φ s.1.1 s.1.2.1 s.1.2.2 s.2 hs c hc.fst hc.snd⟩

  have VALUE : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) (φ : R →ₐ[W₀] T),
      letI : Algebra A₀ T := algebraRestrict A₀ W₀ T
      letI : IsScalarTower A₀ W₀ T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      ∀ (ψ : Pet.B₀ →ₐ[W₀] T) (P Q : Section (xet.curve.map (ψ).toRingHom)) (C : WeierstrassCurve.VariableChange T),
      ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).curve = xet.curve.map (ψ).toRingHom ∧
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).level =
          ((fun p => (xet.level.1 p).map (ψ).toRingHom), (xet.level.2.1.map (ψ).toRingHom, (⟨xet.curve.map (ψ).toRingHom, P, Q⟩ : RawDrinfeldPair T))) →
      ∀ (φc : projModelGradingCR xet.curve →+*ᵍ projModelGradingCR (xet.curve.map ψ.toRingHom))
        (hφc : HomogeneousIdeal.irrelevant (projModelGradingCR (xet.curve.map ψ.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR xet.curve)).map φc),
        IsCoefficientHom xet.curve ψ.toRingHom φc →
        ((Ffun T resT hT₁ hT₂ hT₃ φ).1 : (Pet.B₀ →ₐ[W₀] T) × ((base (T := T) ⟶ projModelCR xet.curve) × (base (T := T) ⟶ projModelCR xet.curve))) =
          (ψ, (P.1 ≫ Proj.map φc hφc, Q.1 ≫ Proj.map φc hφc)) := by
    intro T _ _ _ _ resT hT₁ hT₂ hT₃ φ
    letI instA : Algebra A₀ T := algebraRestrict A₀ W₀ T
    letI instT : IsScalarTower A₀ W₀ T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    intro ψ P Q C hNF φc hφc hcoef

    have hs := (NFE' T ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).choose_spec
    obtain ⟨hψ, hC⟩ := NFU T resT hT₁ hT₂ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x) _ _ _ _ ψ P Q C hs hNF

    show ((NFE' T ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).choose.1.1, _) = _
    generalize hsc : (NFE' T ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).choose = sc at hs hψ hC
    obtain ⟨⟨ψ₀, P₀', Q₀⟩, C₀⟩ := sc
    simp only at hψ hC hs
    subst hψ hC

    have hPQ : (⟨xet.curve.map ψ₀.toRingHom, P₀', Q₀⟩ : RawDrinfeldPair T) = ⟨xet.curve.map ψ₀.toRingHom, P, Q⟩ := by
      have a := congrArg (fun l => l.2.2) hs.2
      have b := congrArg (fun l => l.2.2) hNF.2
      exact a.symm.trans b
    simp only [RawDrinfeldPair.mk.injEq, true_and] at hPQ
    obtain ⟨rfl, rfl⟩ := hPQ

    have hφ : (COEF ψ₀.toRingHom).choose = φc :=
      glueNF_coefHom_unique xet.curve ψ₀.toRingHom _ _ (COEF ψ₀.toRingHom).choose_spec.snd hcoef
    show (ψ₀, (P₀'.1 ≫ Proj.map (COEF ψ₀.toRingHom).choose _, Q₀.1 ≫ Proj.map (COEF ψ₀.toRingHom).choose _)) = _
    congr 1
    refine Prod.ext ?_ ?_ <;> (show _ ≫ Proj.map _ _ = _ ≫ Proj.map _ _; congr 1; exact hφ ▸ rfl)

  have INJ : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w), Function.Injective (Ffun T resT hT₁ hT₂ hT₃) := by
    intro T _ _ _ _ resT hT₁ hT₂ hT₃ φ₁ φ₂ heq
    letI instA : Algebra A₀ T := algebraRestrict A₀ W₀ T
    letI instT : IsScalarTower A₀ W₀ T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨⟨⟨ψ₁, P₁, Q₁⟩, C₁⟩, h₁⟩ := NFE' T ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₁.restrictScalars A₀).comp ι) x)
    obtain ⟨⟨⟨ψ₂, P₂, Q₂⟩, C₂⟩, h₂⟩ := NFE' T ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₂.restrictScalars A₀).comp ι) x)
    obtain ⟨c₁, hc₁, cc₁⟩ := COEF ψ₁.toRingHom
    obtain ⟨c₂, hc₂, cc₂⟩ := COEF ψ₂.toRingHom
    have v₁ := VALUE T resT hT₁ hT₂ hT₃ φ₁ ψ₁ P₁ Q₁ C₁ h₁ c₁ hc₁ cc₁
    have v₂ := VALUE T resT hT₁ hT₂ hT₃ φ₂ ψ₂ P₂ Q₂ C₂ h₂ c₂ hc₂ cc₂
    have heq' := congrArg Subtype.val heq
    rw [v₁, v₂] at heq'
    obtain ⟨hψ, hPQ⟩ := Prod.ext_iff.mp heq'
    simp only at hψ hPQ
    subst hψ
    obtain rfl : c₁ = c₂ := glueNF_coefHom_unique xet.curve ψ₁.toRingHom _ _ cc₁ cc₂
    obtain ⟨hPm, hQm⟩ := Prod.ext_iff.mp hPQ
    simp only at hPm hQm
    have hPB := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom xet.curve ψ₁.toRingHom c₁ hc₁ cc₁
    have eP : P₁ = P₂ := Subtype.ext (hPB.hom_ext hPm (by rw [P₁.2, P₂.2]))
    have eQ : Q₁ = Q₂ := Subtype.ext (hPB.hom_ext hQm (by rw [Q₁.2, Q₂.2]))
    subst eP eQ

    have hw : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C₁ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₁.restrictScalars A₀).comp ι) x) = (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C₂ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₂.restrictScalars A₀).comp ι) x) :=
      ModularCurve.LevelComponent.Raw.ext' (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
    have hcl : (Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₁.restrictScalars A₀).comp ι) x) : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt T) = Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₂.restrictScalars A₀).comp ι) x) := by
      have a : (Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₁.restrictScalars A₀).comp ι) x) : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt T) = Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C₁ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₁.restrictScalars A₀).comp ι) x)) := Quot.sound ⟨C₁, rfl⟩
      have b : (Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₂.restrictScalars A₀).comp ι) x) : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt T) = Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C₂ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ₂.restrictScalars A₀).comp ι) x)) := Quot.sound ⟨C₂, rfl⟩
      rw [a, b, hw]
    have hmap : ∀ (g : P₀.B₀ →ₐ[A₀] T), (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map g P₀.univ = Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing g x) := by
      intro g; rw [← hx]; try rfl
    have u₁ := P₀.classify_unique _ ((φ₁.restrictScalars A₀).comp ι) (hmap _)
    have u₂ := P₀.classify_unique _ ((φ₂.restrictScalars A₀).comp ι) ((hmap _).trans hcl.symm)
    have hA : (φ₁.restrictScalars A₀).comp ι = (φ₂.restrictScalars A₀).comp ι := u₁.trans u₂.symm
    have hcomp₁ : ∀ r : R, resT (φ₁ r) = resR r :=
      IsLocalRing.residueMap_comp_algHom_eq_of_surjective W₀ k res₀ hres₀ R resR hkerR hresR₀ T resT hT₃ φ₁
    have hcomp₂ : ∀ r : R, resT (φ₂ r) = resR r :=
      IsLocalRing.residueMap_comp_algHom_eq_of_surjective W₀ k res₀ hres₀ R resR hkerR hresR₀ T resT hT₃ φ₂
    obtain ⟨Φ, -, hΦu⟩ := hfac T resT hT₁ hT₂ hT₃ ((φ₁.restrictScalars A₀).comp ι) (fun b => hcomp₁ (ι b))
    have e₁ : φ₁ = Φ := hΦu φ₁ ⟨hcomp₁, fun b => rfl⟩
    have e₂ : φ₂ = Φ := hΦu φ₂ ⟨hcomp₂, fun b => by
      show φ₂ (ι b) = ((φ₁.restrictScalars A₀).comp ι) b
      rw [hA]; rfl⟩
    exact e₁.trans e₂.symm

  have strTransport : ∀ {Tk : Type} [CommRing Tk] {V₁ V₂ : WeierstrassCurve Tk} (h : V₁ = V₂),
      eqToHom (congrArg projModelCR h) ≫ projModelStrCR V₂ = projModelStrCR V₁ := by
    rintro Tk _ V₁ V₂ rfl; exact Category.id_comp _
  have pairEq : ∀ {Tk : Type} [CommRing Tk] (m : RawDrinfeldPair Tk) (W' : WeierstrassCurve Tk) (h : m.curve = W')
      (P' Q' : Section W'),
      m.P.1 ≫ eqToHom (congrArg projModelCR h) = P'.1 → m.Q.1 ≫ eqToHom (congrArg projModelCR h) = Q'.1 →
        m = ⟨W', P', Q'⟩ := by
    rintro Tk _ ⟨c, mP, mQ⟩ W' h P' Q' hP' hQ'
    subst h
    have e1 : mP = P' := Subtype.ext (by rw [← hP']; exact (Category.comp_id _).symm)
    have e2 : mQ = Q' := Subtype.ext (by rw [← hQ']; exact (Category.comp_id _).symm)
    rw [e1, e2]
  have SURJ : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k) (hT₁ : Function.Surjective resT) (hT₂ : RingHom.ker resT = maximalIdeal T)
        (hT₃ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w), Function.Surjective (Ffun T resT hT₁ hT₂ hT₃) := by
    intro T _ _ _ _ resT hT₁ hT₂ hT₃ d
    obtain ⟨⟨ψ, Pm, Qm⟩, hd⟩ := d
    letI instA : Algebra A₀ T := algebraRestrict A₀ W₀ T
    letI instT : IsScalarTower A₀ W₀ T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨hn1, ⟨hP, hQ, hDB, htors⟩, hn3, hn4⟩ := hd
    obtain ⟨φc, hφc, hcoef⟩ := COEF ψ.toRingHom
    have hPB := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom xet.curve ψ.toRingHom φc hφc hcoef
    have hsq := WeierstrassCurve.DrinfeldGlobal.projMap_comp_projModelStrCR_of_isCoefficientHom xet.curve ψ.toRingHom φc hφc hcoef

    let P : Section (xet.curve.map ψ.toRingHom) := ⟨hPB.lift Pm (𝟙 _) (by rw [hP, Category.id_comp]), hPB.lift_snd _ _ _⟩
    let Q : Section (xet.curve.map ψ.toRingHom) := ⟨hPB.lift Qm (𝟙 _) (by rw [hQ, Category.id_comp]), hPB.lift_snd _ _ _⟩
    have hPfst : P.1 ≫ Proj.map φc hφc = Pm := hPB.lift_fst _ _ _
    have hQfst : Q.1 ≫ Proj.map φc hφc = Qm := hPB.lift_fst _ _ _

    have hov' : ∀ (R' : Section (xet.curve.map ψ.toRingHom)),
        (R'.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc) ≫ projModelStrCR xet.curve =
          Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
      intro R'
      rw [eqToHom_refl, Category.id_comp, Category.assoc, hsq, ← Category.assoc, R'.2, Category.id_comp]
    have hPpt : (⟨P.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc, hov' P⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (projModelStrCR xet.curve)) = ⟨Pm, hP⟩ := by
      apply Subtype.ext; show P.1 ≫ eqToHom _ ≫ Proj.map φc hφc = _; rw [eqToHom_refl, Category.id_comp]; exact hPfst
    have hQpt : (⟨Q.1 ≫ eqToHom (congrArg projModelCR rfl) ≫ Proj.map φc hφc, hov' Q⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (projModelStrCR xet.curve)) = ⟨Qm, hQ⟩ := by
      apply Subtype.ext; show Q.1 ≫ eqToHom _ ≫ Proj.map φc hφc = _; rw [eqToHom_refl, Category.id_comp]; exact hQfst
    have hlev : RawDrinfeldPair.IsLevel (𝒢.restrictScalars W₀) q (xet.curve.map ψ.toRingHom) ⟨(xet.curve.map ψ.toRingHom), P, Q⟩ := by
      apply (WeierstrassCurve.DrinfeldGlobal.isLevel_iff_isDrinfeldBasisOver_comp_projMap q (𝒢.restrictScalars W₀) h𝒢Or
        Pet.B₀ xet.curve xet.isUnit_Δ T ψ φc hφc hcoef hsq ⟨(xet.curve.map ψ.toRingHom), P, Q⟩ rfl (hov' P) (hov' Q)).mpr
      rw [hPpt, hQpt]; exact hDB

    let Det := (((ModularCurve.gamma0PowComponent W₀ M' hM').prod ((ModularCurve.levelPComponent W₀ ℓ hℓ').prod (ModularCurve.LevelComponent.trivial (A := W₀)))).toRigid)
    let w : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T :=
      ⟨(xet.curve.map ψ.toRingHom), xet.curve.isUnit_Δ_map ψ.toRingHom xet.isUnit_Δ,
        ((fun p => (xet.level.1 p).map ψ.toRingHom), (xet.level.2.1.map ψ.toRingHom, ⟨(xet.curve.map ψ.toRingHom), P, Q⟩)),
        ⟨(Det.mapRing ψ xet).isLevel.1, (Det.mapRing ψ xet).isLevel.2.1, hlev⟩⟩
    let φw : P₀.B₀ →ₐ[A₀] T := P₀.classify (Quot.mk _ w : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt T)
    have hφw : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φw P₀.univ = Quot.mk _ w := P₀.map_classify _

    let resTW : T →ₐ[W₀] k := { toRingHom := resT, commutes' := fun w' => (hT₃ w').trans (hk₀ w').symm }
    let resTA : T →ₐ[A₀] k :=
      { toRingHom := resT
        commutes' := fun a => by
          show resT (algebraMap W₀ T (algebraMap A₀ W₀ a)) = algebraMap A₀ k a
          rw [hT₃, ← hk₀, IsScalarTower.algebraMap_apply A₀ W₀ k] }
    have n1 : resTW.comp ψ = ψet := AlgHom.ext hn1
    subst n1

    obtain ⟨φr, hφr, hcoefr⟩ := WeierstrassProjModel.exists_isCoefficientHom (xet.curve.map ψ.toRingHom) resT
    have hPBr := WeierstrassCurve.DrinfeldGlobal.isPullback_projMap_of_isCoefficientHom (xet.curve.map ψ.toRingHom) resT φr hφr hcoefr
    have hsqr := WeierstrassCurve.DrinfeldGlobal.projMap_comp_projModelStrCR_of_isCoefficientHom (xet.curve.map ψ.toRingHom) resT φr hφr hcoefr
    obtain ⟨φe, hφe, hcoefe, hQk1⟩ := hQk_pin
    have hcomp : Proj.map φr hφr ≫ Proj.map φc hφc = Proj.map φe hφe :=
      glueNF_projMap_comp xet.curve ψ.toRingHom resT φc hφc hcoef φr hφr hcoefr φe hφe hcoefe
    obtain ⟨χk, hχk, hχkx, hχkz⟩ := h𝒢O k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk
    have h1e := WeierstrassCurve.DrinfeldGlobal.one_comp_projMap_eq_of_isOriginChartSection xet.curve (resTW.comp ψ).toRingHom
      φe hφe hcoefe ((𝒢.restrictScalars W₀) Pet.B₀ xet.curve xet.isUnit_Δ) (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk) χB hχB hχBx hχBz χk hχk hχkx hχkz

    have kP : ((⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P.1 ≫ Proj.map φr hφr) = Spec.map (CommRingCat.ofHom resT) ≫ P.1 := by
      apply hPB.hom_ext
      · rw [Category.assoc, Category.assoc, hPfst, hn3, hone]
        exact (congrArg (fun g => (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P.1 ≫ g) hcomp).trans h1e
      · rw [Category.assoc, Category.assoc, P.2, Category.comp_id]
        have litP2 : (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P.1 ≫ projModelStrCR ((xet.curve.map ψ.toRingHom).map resT) = 𝟙 _ :=
          ((⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P).2
        have a := congrArg (fun g => (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P.1 ≫ g) hsqr
        have b : (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P.1 ≫ (projModelStrCR ((xet.curve.map ψ.toRingHom).map resT) ≫
            Spec.map (CommRingCat.ofHom resT)) = Spec.map (CommRingCat.ofHom resT) := by
          rw [← Category.assoc, litP2, Category.id_comp]
        exact a.trans b
    have kQ : ((⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q.1 ≫ Proj.map φr hφr) = Spec.map (CommRingCat.ofHom resT) ≫ Q.1 := by
      apply hPB.hom_ext
      · rw [Category.assoc, Category.assoc, hQfst, hn4]
        exact (congrArg (fun g => (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q.1 ≫ g) hcomp).trans hQk1
      · rw [Category.assoc, Category.assoc, Q.2, Category.comp_id]
        have litQ2 : (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q.1 ≫ projModelStrCR ((xet.curve.map ψ.toRingHom).map resT) = 𝟙 _ :=
          ((⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q).2
        have a := congrArg (fun g => (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q.1 ≫ g) hsqr
        have b : (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q.1 ≫ (projModelStrCR ((xet.curve.map ψ.toRingHom).map resT) ≫
            Spec.map (CommRingCat.ofHom resT)) = Spec.map (CommRingCat.ofHom resT) := by
          rw [← Category.assoc, litQ2, Category.id_comp]
        exact a.trans b

    obtain ⟨hc2, hpin⟩ := h𝒯.2 T k resTA ⟨(xet.curve.map ψ.toRingHom), P, Q⟩
    obtain ⟨hP2, hQ2⟩ := hpin φr hφr hcoefr
    have hpair : 𝒯.map resTA ⟨(xet.curve.map ψ.toRingHom), P, Q⟩ = (⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k) := by
      apply pairEq _ _ hc2
      · apply hPBr.hom_ext
        · rw [Category.assoc, hP2]; exact kP.symm
        · rw [Category.assoc, strTransport hc2, (𝒯.map resTA _).P.2]
          exact (((⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).P).2).symm
      · apply hPBr.hom_ext
        · rw [Category.assoc, hQ2]; exact kQ.symm
        · rw [Category.assoc, strTransport hc2, (𝒯.map resTA _).Q.2]
          exact (((⟨xet.curve.map (resTW.comp ψ).toRingHom,
          (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩ : RawDrinfeldPair k).Q).2).symm
    have hwk : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing resTA w =
        (⟨xet.curve.map (resTW.comp ψ).toRingHom, hΔk,
          ⟨(fun p => (xet.level.1 p).map (resTW.comp ψ).toRingHom), xet.level.2.1.map (resTW.comp ψ).toRingHom,
            ⟨xet.curve.map (resTW.comp ψ).toRingHom,
              (𝒢 k (xet.curve.map (resTW.comp ψ).toRingHom) hΔk).one (𝟙 (base (T := k))), Qk⟩⟩,
          ⟨hhk, hDk, hyk⟩⟩ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw k) := by
      apply ModularCurve.LevelComponent.Raw.ext'
      · rfl
      · refine Prod.ext ?_ (Prod.ext rfl hpair)
        exact funext fun p => Polynomial.map_map ψ.toRingHom resT _

    have hmapw : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map (resTA.comp φw) P₀.univ = (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ρ P₀.univ := by
      rw [hρyk, ← hwk]
      obtain ⟨C₀, hC₀⟩ := glueNF_rel_of_quot_mk_eq (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯) ((show (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φw P₀.univ =
        Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing φw x) from by rw [← hx]; try rfl).symm.trans hφw)

      rw [← hx]
      show Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing (resTA.comp φw) x) = Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing resTA w)
      rw [(rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing_comp, hC₀, (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing_act]
      exact Quot.sound ⟨C₀.map resTA.toRingHom, rfl⟩
    have hφwρ : resTA.comp φw = ρ :=
      (P₀.classify_unique _ _ hmapw).trans (P₀.classify_unique _ _ rfl).symm
    have hcompat : ∀ b : P₀.B₀, resT (φw b) = resR (ι b) := fun b => by
      rw [← hρ b]; exact congrArg (fun g : P₀.B₀ →ₐ[A₀] k => g b) hφwρ
    obtain ⟨Φ, ⟨hΦres, hΦι⟩, -⟩ := hfac T resT hT₁ hT₂ hT₃ φw hcompat
    refine ⟨Φ, ?_⟩

    have hzΦ : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((Φ.restrictScalars A₀).comp ι) x = ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing φw x) := by
      congr 1; exact AlgHom.ext hΦι
    obtain ⟨C₀, hC₀⟩ := glueNF_rel_of_quot_mk_eq (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯) ((show (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map φw P₀.univ =
      Quot.mk _ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing φw x) from by rw [← hx]; try rfl).symm.trans hφw)
    have hNF : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C₀ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((Φ.restrictScalars A₀).comp ι) x)).curve = xet.curve.map ψ.toRingHom ∧
        ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C₀ ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((Φ.restrictScalars A₀).comp ι) x)).level =
          ((fun p => (xet.level.1 p).map ψ.toRingHom), (xet.level.2.1.map ψ.toRingHom, (⟨(xet.curve.map ψ.toRingHom), P, Q⟩ : RawDrinfeldPair T))) := by
      rw [hzΦ, ← hC₀]; exact ⟨rfl, rfl⟩
    apply Subtype.ext
    rw [VALUE T resT hT₁ hT₂ hT₃ Φ ψ P Q C₀ hNF φc hφc hcoef, hPfst, hQfst]

  refine ⟨fun T _ _ _ _ resT hT₁ hT₂ hT₃ =>
    Equiv.ofBijective (Ffun T resT hT₁ hT₂ hT₃) ⟨INJ T resT hT₁ hT₂ hT₃, SURJ T resT hT₁ hT₂ hT₃⟩, ?_⟩
  intro T _ _ _ _ resT hT₁ hT₂ hT₃ T' _ _ _ _ resT' hT'₁ hT'₂ hT'₃ f hf φ
  show ((Ffun T' resT' hT'₁ hT'₂ hT'₃ (f.comp φ)).1 :
      (Pet.B₀ →ₐ[W₀] T') × ((base (T := T') ⟶ projModelCR xet.curve) × (base (T := T') ⟶ projModelCR xet.curve))) =
    (f.comp (Ffun T resT hT₁ hT₂ hT₃ φ).1.1,
      (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (Ffun T resT hT₁ hT₂ hT₃ φ).1.2.1,
       Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (Ffun T resT hT₁ hT₂ hT₃ φ).1.2.2))
  letI instA : Algebra A₀ T := algebraRestrict A₀ W₀ T
  letI instT : IsScalarTower A₀ W₀ T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI instA' : Algebra A₀ T' := algebraRestrict A₀ W₀ T'
  letI instT' : IsScalarTower A₀ W₀ T' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨⟨⟨ψ, P, Q⟩, C⟩, hNF⟩ := NFE' T ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)
  obtain ⟨φc, hφc, hcoef⟩ := COEF ψ.toRingHom
  rw [VALUE T resT hT₁ hT₂ hT₃ φ ψ P Q C hNF φc hφc hcoef]

  let fA : T →ₐ[A₀] T' := f.restrictScalars A₀
  have hz' : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing (((f.comp φ).restrictScalars A₀).comp ι) x) = (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing fA ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x) := by
    rw [← (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing_comp]; congr 1
  have hw' : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act (C.map f.toRingHom) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing (((f.comp φ).restrictScalars A₀).comp ι) x) = (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing fA ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)) := by
    rw [hz']; exact ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing_act fA C _).symm
  obtain ⟨hcf, hpinf⟩ := h𝒯.2 T T' fA ⟨(xet.curve.map ψ.toRingHom), P, Q⟩
  obtain ⟨φf, hφf, hcoeff⟩ := WeierstrassProjModel.exists_isCoefficientHom (xet.curve.map ψ.toRingHom) f.toRingHom
  obtain ⟨hPf, hQf⟩ := hpinf φf hφf hcoeff
  let P' : Section (xet.curve.map (f.comp ψ).toRingHom) :=
    ⟨(𝒯.map fA ⟨(xet.curve.map ψ.toRingHom), P, Q⟩).P.1 ≫ eqToHom (congrArg projModelCR hcf), by
      rw [Category.assoc]
      show _ ≫ eqToHom (congrArg projModelCR hcf) ≫ projModelStrCR ((xet.curve.map ψ.toRingHom).map fA.toRingHom) = 𝟙 _
      rw [strTransport hcf]; exact (𝒯.map fA _).P.2⟩
  let Q' : Section (xet.curve.map (f.comp ψ).toRingHom) :=
    ⟨(𝒯.map fA ⟨(xet.curve.map ψ.toRingHom), P, Q⟩).Q.1 ≫ eqToHom (congrArg projModelCR hcf), by
      rw [Category.assoc]
      show _ ≫ eqToHom (congrArg projModelCR hcf) ≫ projModelStrCR ((xet.curve.map ψ.toRingHom).map fA.toRingHom) = 𝟙 _
      rw [strTransport hcf]; exact (𝒯.map fA _).Q.2⟩
  have hm : 𝒯.map fA ⟨(xet.curve.map ψ.toRingHom), P, Q⟩ = (⟨(xet.curve.map (f.comp ψ).toRingHom), P', Q'⟩ : RawDrinfeldPair T') :=
    pairEq _ _ hcf P' Q' rfl rfl
  have hNF' : ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act (C.map f.toRingHom) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing (((f.comp φ).restrictScalars A₀).comp ι) x)).curve = (xet.curve.map (f.comp ψ).toRingHom) ∧
      ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act (C.map f.toRingHom) ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing (((f.comp φ).restrictScalars A₀).comp ι) x)).level =
        ((fun p => (xet.level.1 p).map (f.comp ψ).toRingHom), (xet.level.2.1.map (f.comp ψ).toRingHom,
          (⟨(xet.curve.map (f.comp ψ).toRingHom), P', Q'⟩ : RawDrinfeldPair T'))) := by
    rw [hw']
    refine ⟨?_, ?_⟩
    · show ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).curve.map fA.toRingHom = _
      rw [hNF.1]; rfl
    · show ModularCurve.LevelComponent.map _ fA ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).act C ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ((φ.restrictScalars A₀).comp ι) x)).level = _
      rw [hNF.2, ← hm]
      refine Prod.ext ?_ (Prod.ext rfl rfl)
      exact funext fun p => Polynomial.map_map ψ.toRingHom f.toRingHom _
  obtain ⟨φc', hφc', hcoef'⟩ := COEF (f.comp ψ).toRingHom
  rw [VALUE T' resT' hT'₁ hT'₂ hT'₃ (f.comp φ) (f.comp ψ) P' Q' (C.map f.toRingHom) hNF' φc' hφc' hcoef']
  have hcomp : Proj.map φf hφf ≫ Proj.map φc hφc = Proj.map φc' hφc' :=
    glueNF_projMap_comp xet.curve ψ.toRingHom f.toRingHom φc hφc hcoef φf hφf hcoeff φc' hφc' hcoef'
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show P'.1 ≫ Proj.map φc' hφc' = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (P.1 ≫ Proj.map φc hφc)
    have a := (congrArg (fun g => P'.1 ≫ g) hcomp).symm
    refine a.trans ?_
    show ((𝒯.map fA ⟨(xet.curve.map ψ.toRingHom), P, Q⟩).P.1 ≫ eqToHom (congrArg projModelCR hcf)) ≫ Proj.map φf hφf ≫ Proj.map φc hφc = _
    rw [← Category.assoc, Category.assoc _ (eqToHom _) _, hPf, Category.assoc]
    rfl
  · show Q'.1 ≫ Proj.map φc' hφc' = Spec.map (CommRingCat.ofHom f.toRingHom) ≫ (Q.1 ≫ Proj.map φc hφc)
    have a := (congrArg (fun g => Q'.1 ≫ g) hcomp).symm
    refine a.trans ?_
    show ((𝒯.map fA ⟨(xet.curve.map ψ.toRingHom), P, Q⟩).Q.1 ≫ eqToHom (congrArg projModelCR hcf)) ≫ Proj.map φf hφf ≫ Proj.map φc hφc = _
    rw [← Category.assoc, Category.assoc _ (eqToHom _) _, hQf, Category.assoc]
    rfl

end S_ModularCurve_LevelModuliPackageAbs_exists_algHom_equiv_isDrinfeldBasisOver_natural_of_factorsThrough_gamma0Pow
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_exists_algHom_equiv_isDrinfeldBasisOver_natural_of_factorsThrough_gamma0Pow (solution)
