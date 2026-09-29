-- Prove2me | solution 1 for ModularCurve.JH.weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c43f8da5-30ec-5658-991e-ee43edf43fb8

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_ModularCurve_finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_Pic0_nonempty_divisorialWeilPairingData_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_Pic0_weilPairing_tateModule_apply_eq_of_forall_pair_eq
import Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_pair_pullbackAlong_eq_pair_pushforwardAlongHom
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JH_weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "RatFunc.denom_X_pow RatFunc.powerBasisAdjoinXPow_dim RatFunc.powerBasisAdjoinXPow_gen RatFunc.intDegree_X_pow RatFunc.num_X_pow"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace PAIRPULL

section Tmap

variable {p : ℕ} [Fact p.Prime] {A B : Type} [AddCommGroup A] [AddCommGroup B]

variable (p) in

noncomputable def tmap (f : A →+ B) : TateModule p A →ₗ[ℤ_[p]] TateModule p B where
  toFun x := ⟨fun n => f ((x : ℕ → A) n), fun n =>
    ⟨by
      show ((p ^ n : ℕ) : ℤ) • f ((x : ℕ → A) n) = 0
      rw [← map_zsmul, TateModule.torsion, map_zero],
     by
      show ((p : ℕ) : ℤ) • f ((x : ℕ → A) (n + 1)) = f ((x : ℕ → A) n)
      rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    show f (((x + y : TateModule p A) : ℕ → A) n) = f ((x : ℕ → A) n) + f ((y : ℕ → A) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    show f (((a.appr n : ℕ) : ℤ) • (x : ℕ → A) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → A) n)
    exact map_zsmul f _ _)

@[scoped simp] theorem tmap_apply (f : A →+ B) (x : TateModule p A) (n : ℕ) :
    ((tmap p f x : TateModule p B) : ℕ → B) n = f ((x : ℕ → A) n) := rfl

end Tmap

theorem pair_eq_pair_of_pin {K F F' : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F] [Field F'] [Algebra K F'] [IsCurveOver K F']
    (u : F →ₐ[K] F') (hu : u.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K u hu) (hfin : FiniteAlong K u) (hN : NormFormulaAlong K u hfin)
    (Pl : Pic0 K F →+ Pic0 K F') (Ps : Pic0 K F' →+ Pic0 K F)
    (hPl : ∀ x, Pl x = Pic0.pullbackAlongHom u hu hFI x) (hPs : ∀ y, Ps y = Pic0.pushforwardAlongHom u hu hfin hN y)
    (n : ℕ) [NeZero n] (W : DivisorialWeilPairingData K F n) (W' : DivisorialWeilPairingData K F' n)
    (x Ty : Pic0.torsion K F n) (Sx y : Pic0.torsion K F' n)
    (hSx : (Sx : Pic0 K F') = Pl x) (hTy : (Ty : Pic0 K F) = Ps y) :
    W'.pair Sx y = W.pair x Ty := by
  obtain ⟨D₀, hD₀⟩ := Pic0.mk_surjective (x : Pic0 K F)
  have hx : (n : ℤ) • (x : Pic0 K F) = 0 := Pic0.mem_torsion.mp x.2
  have hy : (n : ℤ) • (y : Pic0 K F') = 0 := Pic0.mem_torsion.mp y.2
  have hSx' : (Sx : Pic0 K F') = Pic0.mk ⟨Divisor.pullbackAlong u hu (D₀ : Divisor K F),
      Divisor.pullbackAlong_mem_degZero u hu hFI D₀.2⟩ := by
    rw [hSx, hPl, ← hD₀, Pic0.pullbackAlongHom_mk]
    rfl
  have hx' : (n : ℤ) • (Sx : Pic0 K F') = 0 := Pic0.mem_torsion.mp Sx.2
  have hy₀ : (n : ℤ) • Pic0.pushforwardAlongHom u hu hfin hN (y : Pic0 K F') = 0 := by
    rw [← hPs, ← hTy]; exact Pic0.mem_torsion.mp Ty.2
  have h := DivisorialWeilPairingData.pair_pullbackAlong_eq_pair_pushforwardAlongHom u hu hFI hfin hN W' W
    (x : Pic0 K F) hx (y : Pic0 K F') hy D₀ hD₀ (Sx : Pic0 K F') hSx' hx' hy₀
  have hTy' : Ty = ⟨Pic0.pushforwardAlongHom u hu hfin hN (y : Pic0 K F'), Pic0.mem_torsion.mpr hy₀⟩ :=
    Subtype.ext (hTy.trans (hPs _))
  rw [hTy']
  exact h

section Inclusion

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem xHFunctionFieldBar_le_x1FunctionFieldBar : xHFunctionFieldBar M H ≤ x1FunctionFieldBar M :=
  IntermediateField.adjoin.mono _ _ _
    (Set.image_mono (SetLike.coe_subset_coe.mpr (xHFunctionFieldC_le_x1 ℚ M H)))

theorem eq_inclusion
    (ι : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar M))
    (hι : ∀ x : ↥(xHFunctionFieldBar M H),
      ((ι x : ↥(x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ))) :
    ι = IntermediateField.inclusion (xHFunctionFieldBar_le_x1FunctionFieldBar M H) :=
  AlgHom.ext fun x => Subtype.ext
    ((hι x).trans (IntermediateField.coe_inclusion (xHFunctionFieldBar_le_x1FunctionFieldBar M H) x).symm)

theorem finiteAlong_of_qexp [NeZero M]
    (ι : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar M))
    (hι : ∀ x : ↥(xHFunctionFieldBar M H),
      ((ι x : ↥(x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ))) :
    FiniteAlong (AlgebraicClosure ℚ) ι := by
  rw [eq_inclusion M H ι hι]
  exact ModularCurve.finiteAlong_inclusion_xHFunctionFieldBar_x1FunctionFieldBar M H _

theorem isIntegral_of_finiteAlong {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) : φ.toRingHom.IsIntegral := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Module.Finite F F' := hfin
  intro x
  exact Algebra.IsIntegral.isIntegral (R := F) x

theorem hfg_xH [NeZero M] :
    ∃ x : ↥(xHFunctionFieldBar M H), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(xHFunctionFieldBar M H)))
        ↥(xHFunctionFieldBar M H) :=
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ)
    (CohCarrier.GammaH M H) (translation_mem_GammaH M H)

theorem hfg_x1 [NeZero M] :
    ∃ x : ↥(x1FunctionFieldBar M), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(x1FunctionFieldBar M)))
        ↥(x1FunctionFieldBar M) := by
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [← GammaH_bot M]; exact translation_mem_GammaH M ⊥
  exact ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ)
    (CongruenceSubgroup.Gamma1 M) hT

end Inclusion

end PAIRPULL
p2m_reactivate "P2MW.S_ModularCurve_JH_weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul.PAIRPULL"

set_option maxHeartbeats 3200000 in

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]

    (ζ : ℕ → AlgebraicClosure ℚ) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (p ^ n))

    (eH : TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] ℤ_[p])
    (heH : ∀ (n : ℕ)
        (W : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (p ^ n))
        (a b : TateModule p (ModularCurve.JH M H))
        (a' b' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) (p ^ n)),
        (a' : ModularCurve.JH M H) = (a : ℕ → ModularCurve.JH M H) n →
        (b' : ModularCurve.JH M H) = (b : ℕ → ModularCurve.JH M H) n →
        W.pair a' b' = ζ n ^ ((eH a b).appr n))

    (e₁ : TateModule p (ModularCurve.JOne M) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne M) →ₗ[ℤ_[p]] ℤ_[p])
    (he₁ : ∀ (n : ℕ)
        (W : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) (p ^ n))
        (a b : TateModule p (ModularCurve.JOne M))
        (a' b' : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) (p ^ n)),
        (a' : ModularCurve.JOne M) = (a : ℕ → ModularCurve.JOne M) n →
        (b' : ModularCurve.JOne M) = (b : ℕ → ModularCurve.JOne M) n →
        W.pair a' b' = ζ n ^ ((e₁ a b).appr n))

    (ι : ↥(ModularCurve.xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar M))
    (hι : ∀ x : ↥(ModularCurve.xHFunctionFieldBar M H),
      ((ι x : ↥(ModularCurve.x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (x : LaurentSeries (AlgebraicClosure ℚ)))

    (pull : ModularCurve.JH M H →+ ModularCurve.JOne M) (push : ModularCurve.JOne M →+ ModularCurve.JH M H) (c : ℕ)
    (hpinPull : ∀ (hint : ι.toRingHom.IsIntegral)
        (hFI : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint)
        (x : ModularCurve.JH M H),
      pull x = AlgebraicCurve.Pic0.pullbackAlongHom ι hint hFI x)
    (hpinPush : ∀ (hint : ι.toRingHom.IsIntegral)
        (hfin : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ) ι)
        (hN : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ) ι hfin)
        (y : ModularCurve.JOne M),
      push y = AlgebraicCurve.Pic0.pushforwardAlongHom ι hint hfin hN y)
    (hdeg : ∀ x : ModularCurve.JH M H, push (pull x) = c • x)

    (tpull : TateModule p (ModularCurve.JH M H) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JOne M))
    (htpull : ∀ (a : TateModule p (ModularCurve.JH M H)) (n : ℕ),
      ((tpull a : TateModule p (ModularCurve.JOne M)) : ℕ → ModularCurve.JOne M) n =
        pull ((a : ℕ → ModularCurve.JH M H) n))
    (a b : TateModule p (ModularCurve.JH M H)) :
    e₁ (tpull a) (tpull b) = (c : ℤ_[p]) * eH a b := by
  classical
  haveI hC₁ : IsCurveOver (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) := ModularCurve.isCurveOver_x1FunctionFieldBar M
  haveI hCH : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  haveI : CharZero ↥(xHFunctionFieldBar M H) :=
    charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective

  have hfin : FiniteAlong (AlgebraicClosure ℚ) ι := PAIRPULL.finiteAlong_of_qexp M H ι hι
  have hint : ι.toRingHom.IsIntegral := PAIRPULL.isIntegral_of_finiteAlong ι hfin
  have hsep : SeparableAlong (AlgebraicClosure ℚ) ι := AlgebraicCurve.separableAlong_of_charZero ι hint
  have hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hint :=
    AlgebraicCurve.fundamentalIdentityAlong ι hint hfin hsep
  have hN : NormFormulaAlong (AlgebraicClosure ℚ) ι hfin :=
    AlgebraicCurve.normFormulaAlong_of_separableAlong ι hfin hsep
  have hPl : ∀ x, pull x = Pic0.pullbackAlongHom ι hint hFI x := hpinPull hint hFI
  have hPs : ∀ y, push y = Pic0.pushforwardAlongHom ι hint hfin hN y := hpinPush hint hfin hN

  have hWH : ∀ n : ℕ,
      Nonempty (DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (p ^ n)) :=
    fun n => haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
      AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed (AlgebraicClosure ℚ) _
        (PAIRPULL.hfg_xH M H) (p ^ n)
  have hW₁ : ∀ n : ℕ,
      Nonempty (DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(x1FunctionFieldBar M) (p ^ n)) :=
    fun n => haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
      AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData_of_isAlgClosed (AlgebraicClosure ℚ) _
        (PAIRPULL.hfg_x1 M) (p ^ n)

  have hADJ : ∀ (x : TateModule p (JH M H)) (y : TateModule p (JOne M)),
      e₁ (tpull x) y = eH x (PAIRPULL.tmap p push y) :=
    fun x y => AlgebraicCurve.Pic0.weilPairing_tateModule_apply_eq_of_forall_pair_eq (AlgebraicClosure ℚ)
      ↥(xHFunctionFieldBar M H) ↥(x1FunctionFieldBar M) p ζ hζ eH heH e₁ he₁ hWH hW₁ pull push
      (fun n W W' x' Ty Sx y' hSx hTy =>
        haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
        PAIRPULL.pair_eq_pair_of_pin ι hint hFI hfin hN pull push hPl hPs (p ^ n) W W' x' Ty Sx y' hSx hTy)
      tpull htpull (PAIRPULL.tmap p push) (fun _ _ => rfl) x y

  have hpp : PAIRPULL.tmap p push (tpull b) = (c : ℤ_[p]) • b :=
    Subtype.ext (funext fun n => by
      rw [PAIRPULL.tmap_apply, htpull, hdeg, TateModule.natCast_padicInt_smul_apply, natCast_zsmul])
  rw [hADJ, hpp, map_smul, smul_eq_mul]

end S_ModularCurve_JH_weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul
end P2MW
export P2MW.S_ModularCurve_JH_weilPairing_tateModule_jOne_pull_pull_eq_natCast_mul_of_pushforward_pullback_eq_nsmul (solution)
