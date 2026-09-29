-- Prove2me | solution 1 for ModularCurve.forall_map_j0_mem_ssJSet_of_ker_eq_comap_of_jOf_eq_jqNModC_of_isPrimitiveRoot_mul_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/677aa642-0677-53a7-9f91-ef5ae1000b92

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
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_modularPolynomial_kronecker
import Theorems.Thm_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_map_j0_mem_ssJSet_of_ker_eq_comap_of_jOf_eq_jqNModC_of_isPrimitiveRoot_mul_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
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
    (hsurj : ∀ c : ↥K, c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j → ∃ b : P₀.B₀, P₀.classify x b = c) :
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
      ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (φ : P₀.B₀ →+* Ω),
        RingHom.ker φ = 𝔭 → φ P₀.j₀ ∈ ModularCurve.ssJSet q Ω := by
  intro STK CMP toC germY θ 𝔭 Ω _ _ _ _ φ hφ
  classical

  have hθsurj : Function.Surjective θ := by
    intro c
    obtain ⟨b, hb⟩ := hsurj c.1 c.2
    exact ⟨b, Subtype.ext hb⟩
  have hkerθ : RingHom.ker θ ≤ RingHom.ker φ := by
    intro b hb
    rw [hφ]
    rw [RingHom.mem_ker] at hb
    show θ b ∈ y.asIdeal
    rw [hb]
    exact Ideal.zero_mem _

  let φ' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω :=
    (Ideal.Quotient.lift (RingHom.ker θ) φ (fun b hb => hkerθ hb)).comp
      (RingHom.quotientKerEquivOfSurjective hθsurj).symm.toRingHom
  have hφ' : ∀ b : P₀.B₀, φ' (θ b) = φ b := by
    intro b
    show (Ideal.Quotient.lift (RingHom.ker θ) φ (fun b hb => hkerθ hb)) ((RingHom.quotientKerEquivOfSurjective hθsurj).symm (θ b)) = φ b
    have : (RingHom.quotientKerEquivOfSurjective hθsurj).symm (θ b) = Ideal.Quotient.mk (RingHom.ker θ) b := by
      apply (RingHom.quotientKerEquivOfSurjective hθsurj).injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [this, Ideal.Quotient.lift_mk]
  have hkerφ' : RingHom.ker φ' = y.asIdeal := by
    ext c
    obtain ⟨b, rfl⟩ := hθsurj c
    rw [RingHom.mem_ker, hφ', ← RingHom.mem_ker, hφ]
    rfl

  have hssj : φ' (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω := hss Ω φ' hkerφ'

  have hjq : ((j : ↥K) : LaurentSeries L) = jqModC L := by
    rw [hj, ← jqModC_rat]; exact map_jqModC (algebraMap ℚ L)
  let c₁ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j
  let cN : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := θ P₀.j₀

  let ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* LaurentSeries L := (algebraMap ↥K (LaurentSeries L)).comp (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j).val.toRingHom
  have hι : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    exact hab
  have hι₁ : ι c₁ = jqNModC L 1 := by
    rw [jqNModC_one, ← hjq]; rfl
  have hclj : (P₀.classify x) P₀.j₀ = D.jOf x := by
    rw [ModularCurve.LevelModuliPackageAbs.j₀, ← D.jOf_map (P₀.classify x) P₀.univ, P₀.map_classify]
  have hgen : ∀ m n : ℕ, m = n → ∀ [NeZero m] [NeZero n], jqNModC L m = jqNModC L n := by
    intro m n h; subst h; intro _ _; rfl
  have hcomm : jqNModC L (1 * q) = jqNModC L q := hgen _ _ (Nat.one_mul q)
  have hιN : ι cN = jqNModC L (1 * q) := by
    rw [hcomm]
    show (((P₀.classify x) P₀.j₀ : ↥K) : LaurentSeries L) = jqNModC L q
    rw [hclj]; exact hxj

  obtain ⟨dq⟩ := ModularCurve.nonempty_modularPolynomialData q
  have rel2 : dq.Φ.eval₂ (Polynomial.aeval (R := ℤ) c₁).toRingHom cN = 0 := by
    apply hι
    rw [map_zero, Polynomial.hom_eval₂, hιN]
    have e : ι.comp (Polynomial.aeval (R := ℤ) c₁).toRingHom = (Polynomial.aeval (R := ℤ) (jqNModC L 1)).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro n; simp
      · simp [hι₁]
    rw [e]
    exact dq.eval_jqNModC_mul_eq_zero L 1

  have toRoot : ∀ {N : ℕ} [NeZero N] (d : ModularCurve.ModularPolynomialData N) (a b : Ω),
      d.Φ.eval₂ (Polynomial.aeval (R := ℤ) a).toRingHom b = 0 →
      (d.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) a)).IsRoot b := by
    intro N _ d a b h
    have e : (Polynomial.aeval (R := ℤ) a).toRingHom = Polynomial.eval₂RingHom (Int.castRingHom Ω) a := by
      apply Polynomial.ringHom_ext
      · intro n; simp
      · simp
    rw [Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map, ← e]
    exact h
  have push : ∀ {N : ℕ} [NeZero N] (d : ModularCurve.ModularPolynomialData N) (u v : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
      d.Φ.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom v = 0 →
      d.Φ.eval₂ (Polynomial.aeval (R := ℤ) (φ' u)).toRingHom (φ' v) = 0 := by
    intro N _ d u v h
    have h' := congrArg φ' h
    rw [map_zero, Polynomial.hom_eval₂] at h'
    have e : φ'.comp (Polynomial.aeval (R := ℤ) u).toRingHom = (Polynomial.aeval (R := ℤ) (φ' u)).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro n; simp
      · simp
    rwa [e] at h'
  have r2 := toRoot dq _ _ (push dq c₁ cN rel2)

  have hKr := ModularCurve.modularPolynomial_kronecker q dq
  have hcast : Int.castRingHom Ω = (ZMod.castHom (dvd_refl q) Ω).comp (Int.castRingHom (ZMod q)) :=
    RingHom.ext_int _ _
  have hcomp : Polynomial.eval₂RingHom (Int.castRingHom Ω) (φ' c₁) =
      (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl q) Ω) (φ' c₁)).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod q))) := by
    apply Polynomial.ringHom_ext
    · intro n
      rw [hcast]
      simp
    · simp
  have hfac : dq.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) (φ' c₁)) =
      (Polynomial.C ((φ' c₁) ^ q) - Polynomial.X) * (Polynomial.C (φ' c₁) - Polynomial.X ^ q) := by
    rw [hcomp, ← Polynomial.map_map, hKr]
    simp [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow]
  have hb : φ' cN ∈ ModularCurve.ssJSet q Ω := by
    haveI : PerfectField Ω := inferInstance
    have h := r2
    rw [hfac, Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h
    rcases mul_eq_zero.mp h with h | h
    · rw [sub_eq_zero] at h
      rw [← h]
      exact (ModularCurve.pow_mem_ssJSet_iff q (φ' c₁)).mpr hssj
    · rw [sub_eq_zero] at h
      exact (ModularCurve.pow_mem_ssJSet_iff q (φ' cN)).mp (h ▸ hssj)

  rw [← hφ' P₀.j₀]
  exact hb

end S_ModularCurve_forall_map_j0_mem_ssJSet_of_ker_eq_comap_of_jOf_eq_jqNModC_of_isPrimitiveRoot_mul_of_dvd
end P2MW
export P2MW.S_ModularCurve_forall_map_j0_mem_ssJSet_of_ker_eq_comap_of_jOf_eq_jqNModC_of_isPrimitiveRoot_mul_of_dvd (solution)
