-- Prove2me | solution 1 for ModularCurve.exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow_of_isPrimitiveRoot_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/00637fb8-9f12-5dc5-997b-548244ccd7f7

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd
import Theorems.Thm_IsPrimitiveRoot_exists_ringHom_zeta_eq_of_isCyclotomicExtension
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Theorems.Thm_Ideal_IsMaximal_exists_adicCompletion_localization_ringEquiv
import Theorems.Thm_RingHom_exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow_of_isPrimitiveRoot_mul_of_dvd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

universe u

namespace AdicIso

p2m_open "Ideal AlgebraicGeometry.Ideal Ideal.Quotient AdicCompletion"

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hle a

theorem exists_ringEquiv (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
    (he : ∀ {m n : ℕ} (hle : m ≤ n) (x : R ⧸ I ^ n),
      e m (Ideal.Quotient.factorPow I hle x) = Ideal.Quotient.factorPow J hle (e n x)) :
    ∃ E : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ (n : ℕ) (x : AdicCompletion I R), AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x) := by
  have he' : ∀ {m n : ℕ} (hle : m ≤ n) (y : S ⧸ J ^ n),
      (e m).symm (Ideal.Quotient.factorPow J hle y) = Ideal.Quotient.factorPow I hle ((e n).symm y) := by
    intro m n hle y
    apply (e m).injective
    rw [RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]
  let F : AdicCompletion I R →+* AdicCompletion J S :=
    AdicCompletion.liftRingHom J (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) (by
      intro m n hle
      ext x
      show Ideal.Quotient.factorPow J hle (e n (AdicCompletion.evalₐ I n x)) = e m (AdicCompletion.evalₐ I m x)
      rw [← he, factorPow_evalₐ])
  let G : AdicCompletion J S →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I (fun n => (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom) (by
      intro m n hle
      ext y
      show Ideal.Quotient.factorPow I hle ((e n).symm (AdicCompletion.evalₐ J n y)) =
        (e m).symm (AdicCompletion.evalₐ J m y)
      rw [← he', factorPow_evalₐ])
  have hF : ∀ n x, AdicCompletion.evalₐ J n (F x) = e n (AdicCompletion.evalₐ I n x) :=
    fun n x => AdicCompletion.evalₐ_liftRingHom J _ _ n x
  have hG : ∀ n y, AdicCompletion.evalₐ I n (G y) = (e n).symm (AdicCompletion.evalₐ J n y) :=
    fun n y => AdicCompletion.evalₐ_liftRingHom I _ _ n y
  refine ⟨RingEquiv.ofRingHom F G (RingHom.ext fun y => ?_) (RingHom.ext fun x => ?_), hF⟩
  · apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hF, hG, RingEquiv.apply_symm_apply, RingHom.id_apply]
  · apply AdicCompletion.ext_evalₐ
    intro n
    rw [RingHom.comp_apply, hG, hF, RingEquiv.symm_apply_apply, RingHom.id_apply]

theorem apply_of_eq_of (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n) (E : AdicCompletion I R ≃+* AdicCompletion J S)
    (hE : ∀ (n : ℕ) (x : AdicCompletion I R), AdicCompletion.evalₐ J n (E x) = e n (AdicCompletion.evalₐ I n x))
    (θ : R → S) (hθ : ∀ (n : ℕ) (r : R), e n (Ideal.Quotient.mk (I ^ n) r) = Ideal.Quotient.mk (J ^ n) (θ r)) (r : R) :
    E (AdicCompletion.of I R r) = AdicCompletion.of J S (θ r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [hE, AdicCompletion.evalₐ_of, hθ, AdicCompletion.evalₐ_of]

end AdicIso

open AdicIso in
theorem B_compl_local_equiv
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    ∃ ê : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* AdicCompletion (IsLocalRing.maximalIdeal S) S,
      ∀ r : R, ê (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) r) =
        algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (e r) := by
  classical
  have hmax : (IsLocalRing.maximalIdeal R).map (e : R →+* S) = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
  have hpow : ∀ n : ℕ, (IsLocalRing.maximalIdeal S) ^ n = ((IsLocalRing.maximalIdeal R) ^ n).map (e : R →+* S) := by
    intro n
    rw [Ideal.map_pow, hmax]
  let d : ∀ n : ℕ, R ⧸ (IsLocalRing.maximalIdeal R) ^ n ≃+* S ⧸ (IsLocalRing.maximalIdeal S) ^ n := fun n =>
    Ideal.quotientEquiv _ _ e (hpow n)
  have hd_mk : ∀ (n : ℕ) (r : R), d n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (e r) := fun n r => rfl
  have hd : ∀ {m n : ℕ} (hle : m ≤ n) (x : R ⧸ (IsLocalRing.maximalIdeal R) ^ n),
      d m (Ideal.Quotient.factorPow _ hle x) = Ideal.Quotient.factorPow _ hle (d n x) := by
    intro m n hle x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.factor_mk, hd_mk, hd_mk, Ideal.Quotient.factor_mk]
  obtain ⟨E, hE⟩ := exists_ringEquiv _ _ d hd
  refine ⟨E, fun r => ?_⟩
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, Algebra.algebraMap_self,
    RingHom.id_apply, RingHom.id_apply]
  exact apply_of_eq_of _ _ d E hE e hd_mk r

set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (A₀ : Type) [CommRing A₀] [Algebra A₀ ↥K]
    (D : ModularCurve.LevelModuliDatum A₀) (P₀ : LevelModuliPackageAbs A₀ D)
    (x : D.Pt ↥K)
    (hxj : ((D.jOf x : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L q)
    (hmem : ∀ b : P₀.B₀, P₀.classify x b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hsurj : ∀ c : ↥K, c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j → ∃ b : P₀.B₀, P₀.classify x b = c)

    (hker : ∀ n : ℕ, RingHom.ker (P₀.classify x).toRingHom ≤
      (Ideal.comap ((P₀.classify x).toRingHom.codRestrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hmem)
        y.asIdeal) ^ n) :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
      let θ : P₀.B₀ →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
        (P₀.classify x).toRingHom.codRestrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hmem
      let 𝔭 : Ideal P₀.B₀ := Ideal.comap θ y.asIdeal
      𝔭.IsMaximal ∧ algebraMap A₀ P₀.B₀ (q : A₀) ∈ 𝔭 ∧
      ∃ β : CMP ≃+* AdicCompletion 𝔭 P₀.B₀,
        ∀ b : P₀.B₀, β (toC (germY (θ b))) = algebraMap P₀.B₀ (AdicCompletion 𝔭 P₀.B₀) b := by
  classical
  dsimp only
  set θ : P₀.B₀ →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
    (P₀.classify x).toRingHom.codRestrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hmem with hθ
  set 𝔭 : Ideal P₀.B₀ := Ideal.comap θ y.asIdeal with h𝔭
  have hθsurj : Function.Surjective θ := by
    intro c
    obtain ⟨b, hb⟩ := hsurj c.1 c.2
    exact ⟨b, Subtype.ext (by rw [hθ]; exact hb)⟩

  have hι : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)) := by
    haveI hnz : NeZero (q * ℓ) := ⟨(Nat.mul_pos (Fact.out : q.Prime).pos (Fact.out : ℓ.Prime).pos).ne'⟩
    haveI : Module.Finite ℚ L := IsCyclotomicExtension.finite {q * ℓ} ℚ L
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    obtain ⟨φ₁, hφ₁⟩ := IsPrimitiveRoot.exists_ringHom_zeta_eq_of_isCyclotomicExtension (q * ℓ) L L ξ hξ
    have hC : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (q * ℓ))) (q * ℓ) := by
      have h := Complex.isPrimitiveRoot_exp (q * ℓ) (NeZero.ne _)
      simpa [Nat.cast_mul] using h
    obtain ⟨φ₂, hφ₂⟩ := IsPrimitiveRoot.exists_ringHom_zeta_eq_of_isCyclotomicExtension (q * ℓ) L ℂ _ hC
    have hbij : Function.Bijective φ₁ := Algebra.IsAlgebraic.algHom_bijective φ₁.toRatAlgHom
    let e := RingEquiv.ofBijective φ₁ hbij
    refine ⟨φ₂.comp e.symm.toRingHom, ?_⟩
    have he : e.symm ξ = IsCyclotomicExtension.zeta (q * ℓ) ℚ L := by
      apply e.injective
      rw [RingEquiv.apply_symm_apply]
      exact hφ₁.symm
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he, hφ₂]

  have hιζ : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q) := by
    obtain ⟨ι, hι'⟩ := hι
    refine ⟨ι, ?_⟩
    have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    rw [hζξ, map_pow, hι', ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp

  obtain ⟨hymax, hϖy⟩ := ModularCurve.FullLevel.AuxLevelOne.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hιζ H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ z ϖz hϖz hz y hy hss
  haveI : y.asIdeal.IsMaximal := hymax

  have h𝔭max : 𝔭.IsMaximal := by
    rw [h𝔭]; exact Ideal.comap_isMaximal_of_surjective θ hθsurj

  have hq𝔭 : algebraMap A₀ P₀.B₀ (q : A₀) ∈ 𝔭 := by
    rw [h𝔭, Ideal.mem_comap]
    have hqA : (q : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAq
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hqA
    have hθq : θ (algebraMap A₀ P₀.B₀ (q : A₀)) =
        algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) (q : A) := by
      apply Subtype.ext
      rw [hθ]
      simp [map_natCast]
    rw [hθq, ← ha, map_mul]
    exact Ideal.mul_mem_left _ _ hϖy
  refine ⟨h𝔭max, hq𝔭, ?_⟩

  have hzmem : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y ∈
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤ := ⟨y, trivial, rfl⟩
  obtain ⟨eSt, -, heSt⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_chartAlgFin A (↥K) j y hzmem
  subst hy
  obtain ⟨e₁, he₁⟩ := B_compl_local_equiv (S := Localization.AtPrime y.asIdeal) eSt.commRingCatIsoToRingEquiv
  obtain ⟨e₂, he₂⟩ := Ideal.IsMaximal.exists_adicCompletion_localization_ringEquiv y.asIdeal
  have hkerθ : ∀ n : ℕ, RingHom.ker θ ≤ Ideal.comap θ y.asIdeal ^ n := by
    intro n b hb
    have hb' : b ∈ RingHom.ker (P₀.classify x).toRingHom := by
      rw [RingHom.mem_ker] at hb ⊢
      have := congrArg Subtype.val hb
      rw [hθ] at this
      simpa using this
    have := hker n hb'
    rw [h𝔭] at this
    exact this
  obtain ⟨e₃, he₃⟩ := RingHom.exists_adicCompletion_ringEquiv_of_surjective_of_ker_le_comap_pow θ hθsurj y.asIdeal hkerθ
  rw [h𝔭]
  refine ⟨(e₁.trans e₂).trans e₃.symm, fun b => ?_⟩
  show e₃.symm (e₂ (e₁ (algebraMap _ _ _))) = _
  rw [RingEquiv.symm_apply_eq, he₁, he₃]
  have hgerm := heSt (θ b)
  rw [show eSt.commRingCatIsoToRingEquiv _ = eSt.hom.hom _ from rfl, RingHom.comp_apply, RingHom.comp_apply, hgerm, he₂]

end S_ModularCurve_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow_of_isPrimitiveRoot_mul_of_dvd
end P2MW
export P2MW.S_ModularCurve_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow_of_isPrimitiveRoot_mul_of_dvd (solution)
