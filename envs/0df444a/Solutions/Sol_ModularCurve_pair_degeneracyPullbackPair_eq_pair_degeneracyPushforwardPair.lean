-- Prove2me | solution 1 for ModularCurve.pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f400dd8e-68e6-56d3-b19e-7f4ced1d71c9

import Mathlib
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_pullback
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "DegeneracyPullbackInputs degeneracyPullbackPair heckeAlphaBar heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral modularFunctionFieldBar JZero modularFunctionFieldFull laurentBaseChange DegeneracyPushforwardInputs degeneracyPushforwardPair degeneracyPushforwardPair_eq isCurveOver_laurentBaseChange_modularFunctionFieldFull"
namespace PEdge
p2m_open "ModularCurve"

theorem isRational_of_isAlgClosed {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

section PullWrapper

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def pullbackAlongHom' (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hP : HasPrincipalDivisors K F') (hFI : FundamentalIdentityAlong K φ hφ) :
    Pic0 K F →+ Pic0 K F' :=
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI := hP
  haveI : FundamentalIdentity K F F' := hFI
  Pic0.pullbackHom _

theorem pullbackAlongHom'_mk (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hP : HasPrincipalDivisors K F') (hFI : FundamentalIdentityAlong K φ hφ)
    (D : Divisor.degZero (K := K) (F := F)) :
    pullbackAlongHom' φ hφ hP hFI (Pic0.mk D) =
      (letI := algebraAlong φ
       haveI := isScalarTower_along φ
       haveI := isIntegral_along φ hφ
       haveI := hP
       haveI : FundamentalIdentity K F F' := hFI
       Pic0.mk (Pic0.pullbackDegZeroHom F' D)) := rfl

end PullWrapper

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [HasPrincipalDivisors K F] [hP : HasPrincipalDivisors K F'] {n : ℕ} [NeZero n]

theorem pair_pullbackAlong_eq_pair_pushforwardAlong
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)
    (hsep : letI := algebraAlong φ; Algebra.IsSeparable F F')
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    (e : DivisorialWeilPairingData K F n) (e' : DivisorialWeilPairingData K F' n)
    (x : Pic0.torsion K F n) (x' : Pic0.torsion K F' n) (y' : Pic0.torsion K F' n)
    (y : Pic0.torsion K F n)
    (hx : (x' : Pic0 K F') = pullbackAlongHom' φ hφ hP hFI (x : Pic0 K F))
    (hy : (y : Pic0 K F) = Pic0.pushforwardAlongHom φ hφ hfin hN (y' : Pic0 K F')) :
    e'.pair x' y' = e.pair x y := by
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  haveI : FundamentalIdentity K F F' := hFI
  have hNF : Divisor.PushforwardNormFormula K F F' := hN

  obtain ⟨D₁, hD₁x, -, -⟩ := e.move x ∅
  obtain ⟨f₁, hf₁0, hord₁⟩ := DivisorialWeilPairingData.exists_witness x D₁ hD₁x
  obtain ⟨D₂, hD₂y, -, hD₂avoid⟩ :=
    e'.move y' ((D₁ : Divisor K F).support.biUnion fun v => v.fiber F')
  obtain ⟨f₂, hf₂0, hord₂⟩ := DivisorialWeilPairingData.exists_witness y' D₂ hD₂y

  have hdis : ∀ w ∈ (D₂ : Divisor K F').support, (D₁ : Divisor K F) (w.restrict F) = 0 := by
    intro w hw
    by_contra h
    exact hD₂avoid w hw (Finset.mem_biUnion.mpr
      ⟨w.restrict F, Finsupp.mem_support_iff.mpr h, Place.restrict_mem_fiber w⟩)
  have hdis' : ∀ w : Place K F', (D₁ : Divisor K F) (w.restrict F) ≠ 0 → (D₂ : Divisor K F') w = 0 := by
    intro w h
    by_contra h2
    exact h (hdis w (Finsupp.mem_support_iff.mpr h2))

  let d' : WeilDatum K F' n :=
    { D₁ := Divisor.pullback F' (D₁ : Divisor K F)
      D₂ := (D₂ : Divisor K F')
      f₁ := algebraMap F F' f₁
      f₂ := f₂
      f₁_ne_zero := (map_ne_zero_iff _ (algebraMap F F').injective).mpr hf₁0
      f₂_ne_zero := hf₂0
      ord_f₁ := fun w => by
        rw [Place.ord_restrict, hord₁, Divisor.pullback_apply]
        ring
      ord_f₂ := hord₂
      disjoint := fun w => by
        by_cases h : (D₁ : Divisor K F) (w.restrict F) = 0
        · exact Or.inl (by rw [Divisor.pullback_apply, h, mul_zero])
        · exact Or.inr (hdis' w h)
      rational := fun w _ => hratF' w }

  let d : WeilDatum K F n :=
    { D₁ := (D₁ : Divisor K F)
      D₂ := Divisor.pushforward F (D₂ : Divisor K F')
      f₁ := f₁
      f₂ := Algebra.norm F f₂
      f₁_ne_zero := hf₁0
      f₂_ne_zero := Algebra.norm_ne_zero_iff.mpr hf₂0
      ord_f₁ := hord₁
      ord_f₂ := fun v => by
        have h := hNF f₂ hf₂0 ((n : ℤ) • (D₂ : Divisor K F'))
          (fun w => by rw [Finsupp.smul_apply, smul_eq_mul, hord₂]) v
        rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h
        exact h.symm
      disjoint := fun v => by
        by_cases h : (D₁ : Divisor K F) v = 0
        · exact Or.inl h
        · refine Or.inr ?_
          rw [Divisor.pushforward_apply]
          refine Finset.sum_eq_zero fun w hw => ?_
          rw [if_neg]
          intro hwv
          rw [← hwv] at h
          exact h (hdis w hw)
      rational := fun v _ => hratF v }

  have hcl' : d'.classLeft = x' := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classLeft, hx, ← hD₁x, pullbackAlongHom'_mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  have hcr' : d'.classRight = y' := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classRight, ← hD₂y]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  have hcl : d.classLeft = x := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classLeft, ← hD₁x]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  have hcr : d.classRight = y := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classRight, hy, ← hD₂y, Pic0.pushforwardAlongHom_mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)

  have legA : Divisor.evalFun (algebraMap F F' f₁) (D₂ : Divisor K F')
      = Divisor.evalFun f₁ (Divisor.pushforward F (D₂ : Divisor K F')) :=
    Divisor.evalFun_algebraMap_pushforward hf₁0 (D₂ : Divisor K F') (fun w _ => hratF' w)
      (fun w _ => hratF _) (fun w hw => by rw [hord₁, hdis w hw, mul_zero])
  have legB : Divisor.evalFun f₂ (Divisor.pullback F' (D₁ : Divisor K F))
      = Divisor.evalFun (Algebra.norm F f₂) (D₁ : Divisor K F) :=
    Divisor.evalFun_pullback hf₂0 (D₁ : Divisor K F) (fun v _ => hratF v)
      (fun v _ w _ => hratF' w) (fun v hv w hw => by
        rw [hord₂, hdis' w ?_, mul_zero]
        rw [Place.mem_fiber.mp hw]
        exact Finsupp.mem_support_iff.mp hv)
  calc e'.pair x' y' = e'.pair d'.classLeft d'.classRight := by rw [hcl', hcr']
    _ = d'.pairing := e'.compatible d'
    _ = Divisor.evalFun (algebraMap F F' f₁) (D₂ : Divisor K F')
          / Divisor.evalFun f₂ (Divisor.pullback F' (D₁ : Divisor K F)) := rfl
    _ = Divisor.evalFun f₁ (Divisor.pushforward F (D₂ : Divisor K F'))
          / Divisor.evalFun (Algebra.norm F f₂) (D₁ : Divisor K F) := by rw [legA, legB]
    _ = d.pairing := rfl
    _ = e.pair d.classLeft d.classRight := (e.compatible d).symm
    _ = e.pair x y := by rw [hcl, hcr]

end Generic

section Degeneracy

variable (N q : ℕ) [NeZero N] [NeZero q]

theorem degeneracyPullbackPair_eq
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q) (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hP : HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q))))
    (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
    (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ) :
    degeneracyPullbackPair N q =
      ![pullbackAlongHom' (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα hP hFIα,
        pullbackAlongHom' (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ hP hFIβ] := by
  rw [degeneracyPullbackPair, dif_pos ⟨hα, hβ, hP, hFIα, hFIβ⟩]
  rfl

omit [NeZero N] [NeZero q] in

theorem isSeparable_along
    (φ : modularFunctionFieldBar N →ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar (N * q))
    (hφ : φ.toRingHom.IsIntegral) :
    letI := algebraAlong φ; Algebra.IsSeparable (modularFunctionFieldBar N) (modularFunctionFieldBar (N * q)) := by
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  haveI : CharZero (modularFunctionFieldBar N) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end Degeneracy

end ModularCurve.PEdge

open ModularCurve.PEdge in
theorem solution
    (N q n : ℕ) [NeZero N] [NeZero q] [NeZero n]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar N)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar (N * q))]
    (hpull : ModularCurve.DegeneracyPullbackInputs N q)
    (hpush : ModularCurve.DegeneracyPushforwardInputs N q)
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar N) n)
    (e' : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar (N * q)) n)
    (i : Fin 2)
    (x : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar N) n)
    (x' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar (N * q)) n)
    (y' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar (N * q)) n)
    (y : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
      (ModularCurve.modularFunctionFieldBar N) n)
    (hx : (x' : ModularCurve.JZero (N * q)) =
      ModularCurve.degeneracyPullbackPair N q i (x : ModularCurve.JZero N))
    (hy : (y : ModularCurve.JZero N) =
      ModularCurve.degeneracyPushforwardPair N q i (y' : ModularCurve.JZero (N * q))) :
    e'.pair x' y' = e.pair x y := by
  haveI : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne q)⟩
  haveI := ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) N
  haveI := ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) (N * q)
  have hratN : ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N),
      v.IsRational := fun v => isRational_of_isAlgClosed v
  have hratNq : ∀ w : AlgebraicCurve.Place (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar (N * q)),
      w.IsRational := fun w => isRational_of_isAlgClosed w
  obtain ⟨hα, hβ, hP, hFIα, hFIβ⟩ := hpull
  obtain ⟨hα', hβ', hfinα, hfinβ, hNα, hNβ⟩ := hpush
  fin_cases i
  · exact pair_pullbackAlong_eq_pair_pushforwardAlong _ hα hFIα hfinα hNα (isSeparable_along N q _ hα)
      hratN hratNq e e' x x' y' y
      (hx.trans (by rw [degeneracyPullbackPair_eq N q hα hβ hP hFIα hFIβ]; rfl))
      (hy.trans (by rw [ModularCurve.degeneracyPushforwardPair_eq hα' hβ' hfinα hNα hfinβ hNβ]; rfl))
  · exact pair_pullbackAlong_eq_pair_pushforwardAlong _ hβ hFIβ hfinβ hNβ (isSeparable_along N q _ hβ)
      hratN hratNq e e' x x' y' y
      (hx.trans (by rw [degeneracyPullbackPair_eq N q hα hβ hP hFIα hFIβ]; rfl))
      (hy.trans (by rw [ModularCurve.degeneracyPushforwardPair_eq hα' hβ' hfinα hNα hfinβ hNβ]; rfl))

end
end S_ModularCurve_pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair
end P2MW
export P2MW.S_ModularCurve_pair_degeneracyPullbackPair_eq_pair_degeneracyPushforwardPair (solution)
