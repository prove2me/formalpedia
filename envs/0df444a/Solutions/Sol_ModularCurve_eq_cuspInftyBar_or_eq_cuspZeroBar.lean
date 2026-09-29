-- Prove2me | solution 1 for ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/dbf3629f-a03b-5832-8812-b9a975b556ab

import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_le_finrank
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_pos
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionField
import Theorems.Thm_ModularCurve_full_eq_of_prime
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData_of_squarefree
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_le
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jqNModC
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_cuspZeroBar_ne_cuspInftyBar
import Theorems.Thm_ModularCurve_isCusp_cuspZeroBar
import Theorems.Thm_ModularCurve_isCusp_cuspInftyBar
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "ModularCurve~dedekindPsi_prime AlgebraicCurve IntermediateField"
open scoped Polynomial

noncomputable section

namespace TwoCuspAux

local notation "𝕂" => AlgebraicClosure ℚ

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem prime' : ℓ.Prime := Fact.out

theorem dedekindPsi_prime : dedekindPsi ℓ = ℓ + 1 := by
  have hℓ : ℓ.Prime := Fact.out
  rw [dedekindPsi, hℓ.divisors, Finset.filter_true_of_mem, Finset.sum_pair hℓ.one_lt.ne, Nat.div_one,
    Nat.div_self hℓ.pos, add_comm]
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact squarefree_one
  · exact hℓ.squarefree

def jb : modularFunctionFieldBar ℓ := ⟨coeffEmb 𝕂 jq, coeffEmb_mem_laurentBaseChange 𝕂 (jq_mem_full ℓ)⟩

theorem coe_jb : (jb ℓ : LaurentSeries 𝕂) = jqModC 𝕂 := coeffEmb_jq 𝕂

theorem bar_eq_restrictScalars :
    modularFunctionFieldBar ℓ = (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯).restrictScalars 𝕂 := by
  have hℓ : ℓ.Prime := Fact.out
  show laurentBaseChange 𝕂 (modularFunctionFieldFull ℓ) = _
  rw [full_eq_of_prime hℓ, laurentBaseChange_modularFunctionField]
  exact (adjoin_simple_adjoin_simple 𝕂 (jqModC 𝕂) (jqNModC 𝕂 ℓ)).symm

def σa : RatFunc 𝕂 ≃ₐ[𝕂] 𝕂⟮jqModC 𝕂⟯ :=
  RatFunc.algEquivOfTranscendental (jqModC 𝕂) (transcendental_jqModC 𝕂)

theorem coe_σa_X : ((σa (RatFunc.X : RatFunc 𝕂) : 𝕂⟮jqModC 𝕂⟯) : LaurentSeries 𝕂) = jqModC 𝕂 :=
  RatFunc.algEquivOfTranscendental_X (jqModC 𝕂) (transcendental_jqModC 𝕂)

theorem mem_bar_iff (x : LaurentSeries 𝕂) :
    x ∈ modularFunctionFieldBar ℓ ↔ x ∈ 𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯ := by
  rw [bar_eq_restrictScalars ℓ, mem_restrictScalars]

def jTr : (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) ≃+* modularFunctionFieldBar ℓ where
  toFun x := ⟨x, (mem_bar_iff ℓ _).mpr x.2⟩
  invFun y := ⟨y, (mem_bar_iff ℓ _).mp y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem coe_jTr (x : 𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) :
    ((jTr ℓ x : modularFunctionFieldBar ℓ) : LaurentSeries 𝕂) = x := by
  unfold jTr; rfl

def φ : RatFunc 𝕂 →+* modularFunctionFieldBar ℓ :=
  (jTr ℓ).toRingHom.comp
    ((algebraMap (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯)).comp (σa).toRingEquiv.toRingHom)

theorem φ_apply (x : RatFunc 𝕂) :
    φ ℓ x = jTr ℓ (algebraMap (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) (σa x)) := rfl

theorem coe_algebraMap_tower (y : 𝕂⟮jqModC 𝕂⟯) :
    ((algebraMap (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) y : 𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯) :
      LaurentSeries 𝕂) = y := rfl

theorem coe_φ (x : RatFunc 𝕂) :
    ((φ ℓ x : modularFunctionFieldBar ℓ) : LaurentSeries 𝕂) = (σa x : LaurentSeries 𝕂) := by
  rw [φ_apply, coe_jTr, coe_algebraMap_tower]

theorem φ_algebraMap (k : 𝕂) : φ ℓ (algebraMap 𝕂 (RatFunc 𝕂) k) = algebraMap 𝕂 (modularFunctionFieldBar ℓ) k := by
  apply Subtype.ext
  rw [coe_φ, AlgEquiv.commutes]
  rfl

theorem φ_X : φ ℓ (RatFunc.X : RatFunc 𝕂) = jb ℓ := by
  apply Subtype.ext
  rw [coe_φ, coe_jb, coe_σa_X]

abbrev algRatFunc : Algebra (RatFunc 𝕂) (modularFunctionFieldBar ℓ) := (φ ℓ).toAlgebra

attribute [local instance] algRatFunc

theorem algebraMap_eq : algebraMap (RatFunc 𝕂) (modularFunctionFieldBar ℓ) = φ ℓ := rfl

theorem isScalarTower_ratFunc : IsScalarTower 𝕂 (RatFunc 𝕂) (modularFunctionFieldBar ℓ) :=
  IsScalarTower.of_algebraMap_eq fun k => (φ_algebraMap ℓ k).symm

attribute [local instance] isScalarTower_ratFunc

theorem he_compat :
    (algebraMap (RatFunc 𝕂) (modularFunctionFieldBar ℓ)).comp
        (σa.symm.toRingEquiv : 𝕂⟮jqModC 𝕂⟯ ≃+* RatFunc 𝕂).toRingHom
      = (jTr ℓ).toRingHom.comp (algebraMap (𝕂⟮jqModC 𝕂⟯) (𝕂⟮jqModC 𝕂⟯⟮jqNModC 𝕂 ℓ⟯)) := by
  apply RingHom.ext
  intro y
  show φ ℓ (σa.symm y) = jTr ℓ (algebraMap _ _ y)
  rw [φ_apply, AlgEquiv.apply_symm_apply]

theorem finite_ratFunc : Module.Finite (RatFunc 𝕂) (modularFunctionFieldBar ℓ) := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree ℓ hℓ.squarefree hℓ.one_lt
  haveI := finiteDimensional_adjoin_jqNModC 𝕂 data
  exact Module.Finite.of_equiv_equiv (σa.symm.toRingEquiv : 𝕂⟮jqModC 𝕂⟯ ≃+* RatFunc 𝕂) (jTr ℓ)
    (he_compat ℓ)

attribute [local instance] finite_ratFunc

theorem finrank_le : Module.finrank (RatFunc 𝕂) (modularFunctionFieldBar ℓ) ≤ ℓ + 1 := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨data⟩ := nonempty_modularPolynomialData_of_squarefree ℓ hℓ.squarefree hℓ.one_lt
  rw [← Algebra.finrank_eq_of_equiv_equiv (σa.symm.toRingEquiv : 𝕂⟮jqModC 𝕂⟯ ≃+* RatFunc 𝕂) (jTr ℓ)
    (he_compat ℓ), ← dedekindPsi_prime ℓ]
  exact finrank_adjoin_jqNModC_le 𝕂 data

theorem isSeparable_ratFunc : Algebra.IsSeparable (RatFunc 𝕂) (modularFunctionFieldBar ℓ) :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

attribute [local instance] isSeparable_ratFunc

theorem restrict_eq_of_isCusp (u : Place 𝕂 (modularFunctionFieldBar ℓ)) (hu : IsCusp (jb ℓ) u) :
    u.restrict (RatFunc 𝕂) = (cuspInftyBar ℓ).restrict (RatFunc 𝕂) := by
  have key : ∀ u' : Place 𝕂 (modularFunctionFieldBar ℓ), IsCusp (jb ℓ) u' →
      ∀ p : IsDedekindDomain.HeightOneSpectrum 𝕂[X],
        u'.restrict (RatFunc 𝕂) ≠ Place.ofHeightOneSpectrum p := by
    intro u' hu' p heq
    apply hu'
    have hX : (RatFunc.X : RatFunc 𝕂) ∈ (u'.restrict (RatFunc 𝕂)).toValuationSubring := by
      rw [heq, Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff,
        ← RatFunc.algebraMap_X]
      exact p.valuation_le_one _
    rw [Place.mem_restrict_iff, algebraMap_eq, φ_X] at hX
    exact hX
  exact RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum (key u hu)
    (key _ (isCusp_cuspInftyBar ℓ))

theorem e_infty : ((cuspInftyBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) = 1 ∧
    ((cuspInftyBar ℓ).restrict (RatFunc 𝕂)).ord RatFunc.X = -1 := by
  have h := (cuspInftyBar ℓ).ord_restrict (F := RatFunc 𝕂) RatFunc.X
  rw [algebraMap_eq, φ_X] at h
  have hj : (cuspInftyBar ℓ).ord (jb ℓ) = -1 := ord_cuspInftyBar_coeffEmb_jq ℓ
  rw [hj] at h
  have epos : (0 : ℤ) < (cuspInftyBar ℓ).ramificationIndex (RatFunc 𝕂) := by
    exact_mod_cast (cuspInftyBar ℓ).ramificationIndex_pos (F := RatFunc 𝕂)
  have h1 : ((cuspInftyBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) *
      (-((cuspInftyBar ℓ).restrict (RatFunc 𝕂)).ord RatFunc.X) = 1 := by linarith
  have he := Int.eq_one_of_mul_eq_one_right epos.le h1
  refine ⟨he, ?_⟩
  rw [he, one_mul] at h1
  linarith

theorem e_zero (hw : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ)) :
    ((cuspZeroBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) = ℓ := by
  have h := (cuspZeroBar ℓ).ord_restrict (F := RatFunc 𝕂) RatFunc.X
  rw [algebraMap_eq, φ_X, restrict_eq_of_isCusp ℓ _ (isCusp_cuspZeroBar ℓ hw), (e_infty ℓ).2] at h
  have hj : (cuspZeroBar ℓ).ord (jb ℓ) = -ℓ := ord_cuspZeroBar_coeffEmb_jq ℓ hw
  rw [hj] at h
  linarith

theorem eq_cuspInftyBar_or_eq_cuspZeroBar (hw : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ))
    (w : Place 𝕂 (modularFunctionFieldBar ℓ)) (hc : IsCusp (jb ℓ) w) :
    w = cuspInftyBar ℓ ∨ w = cuspZeroBar ℓ := by
  classical
  by_contra hnot
  have h1 : w ≠ cuspInftyBar ℓ := fun h => hnot (Or.inl h)
  have h2 : w ≠ cuspZeroBar ℓ := fun h => hnot (Or.inr h)
  have hℓ : ℓ.Prime := Fact.out
  have hne : cuspZeroBar ℓ ≠ cuspInftyBar ℓ := cuspZeroBar_ne_cuspInftyBar ℓ hw hℓ.one_lt
  have r0 := restrict_eq_of_isCusp ℓ _ (isCusp_cuspZeroBar ℓ hw)
  have rw' := restrict_eq_of_isCusp ℓ _ hc
  have hS : ∀ u ∈ ({cuspInftyBar ℓ, cuspZeroBar ℓ, w} : Finset (Place 𝕂 (modularFunctionFieldBar ℓ))),
      u.restrict (RatFunc 𝕂) = (cuspInftyBar ℓ).restrict (RatFunc 𝕂) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · rfl
    · exact r0
    · exact rw'
  have hsum := Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank _ _ hS
  rw [Finset.sum_insert (by simp [hne.symm, Ne.symm h1]), Finset.sum_insert (by simp [Ne.symm h2]),
    Finset.sum_singleton] at hsum
  have hrank : (Module.finrank (RatFunc 𝕂) (modularFunctionFieldBar ℓ) : ℤ) ≤ ℓ + 1 := by
    exact_mod_cast finrank_le ℓ
  have e1 := (e_infty ℓ).1
  have e0 := e_zero ℓ hw
  have ew : (1 : ℤ) ≤ w.ramificationIndex (RatFunc 𝕂) := by
    exact_mod_cast w.ramificationIndex_pos (F := RatFunc 𝕂)
  have f1 : (1 : ℤ) ≤ (cuspInftyBar ℓ).inertiaDeg (RatFunc 𝕂) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc 𝕂) (cuspInftyBar ℓ)
  have f0 : (1 : ℤ) ≤ (cuspZeroBar ℓ).inertiaDeg (RatFunc 𝕂) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc 𝕂) (cuspZeroBar ℓ)
  have fw : (1 : ℤ) ≤ w.inertiaDeg (RatFunc 𝕂) := by
    exact_mod_cast Place.inertiaDeg_pos (F := RatFunc 𝕂) w
  have p0 : (ℓ : ℤ) ≤ ((cuspZeroBar ℓ).ramificationIndex (RatFunc 𝕂) : ℤ) *
      ((cuspZeroBar ℓ).inertiaDeg (RatFunc 𝕂) : ℤ) := by
    rw [e0]; nlinarith
  have pw : (1 : ℤ) ≤ (w.ramificationIndex (RatFunc 𝕂) : ℤ) * (w.inertiaDeg (RatFunc 𝕂) : ℤ) :=
    one_le_mul_of_one_le_of_one_le ew fw
  rw [e1, one_mul] at hsum
  linarith

end TwoCuspAux

open TwoCuspAux in

theorem solution (ℓ : ℕ) [Fact ℓ.Prime] (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar ℓ)) (hc : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full ℓ)⟩ : modularFunctionFieldBar ℓ) w) :
    w = cuspInftyBar ℓ ∨ w = cuspZeroBar ℓ :=
  TwoCuspAux.eq_cuspInftyBar_or_eq_cuspZeroBar ℓ (isFrickeAutFull_frickeInvolutionFull_prime ℓ) w hc

end
end S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
end P2MW
export P2MW.S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar (solution)
