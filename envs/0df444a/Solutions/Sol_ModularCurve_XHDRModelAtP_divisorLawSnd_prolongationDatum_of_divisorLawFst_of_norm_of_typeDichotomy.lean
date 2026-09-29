-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.divisorLawSnd_prolongationDatum_of_divisorLawFst_of_norm_of_typeDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b546191f-7732-5ca0-a68b-ed18e1a4149e

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_finiteAlong_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_single_one_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_normFormulaAlong_of_separableAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_divisorLawSnd_prolongationDatum_of_divisorLawFst_of_norm_of_typeDichotomy
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace Ws49NormDock

theorem gamma1_le_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro γ hγ
  obtain ⟨-, h11, h10⟩ := (CongruenceSubgroup.Gamma1_mem M γ).mp hγ
  refine CohCarrier.mem_GammaH_iff.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr h10, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr h10⟩ = 1 :=
    Units.ext (by rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11)
  rw [h1]
  exact Subgroup.one_mem _

theorem T_mem_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  gamma1_le_gammaH M H (by rw [CongruenceSubgroup.Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T])

theorem finiteIndex_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex := by
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma1 M
  exact Subgroup.finiteIndex_of_le (gamma1_le_gammaH M H)

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]

theorem finiteAlong_alpha
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) :
    FiniteAlong (AlgebraicClosure ℚ) α := by
  haveI := finiteIndex_gammaH (M / p) (infSubgroup p M H hpM)
  haveI := finiteIndex_gammaH M H
  exact ModularCurve.finiteAlong_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ)
    (Γ := CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) (Γ' := CohCarrier.GammaH M H)
    (T_mem_gammaH (M / p) _) (T_mem_gammaH M H) α

theorem separableAlong_alpha
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) : SeparableAlong (AlgebraicClosure ℚ) α :=
  AlgebraicCurve.separableAlong_of_charZero α hα

theorem isCurveOver_xHFunctionFieldBar (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar N H') :=
  (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) N H').1

theorem hasPrincipalDivisors_xHFunctionFieldBar (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar N H') :=
  (isCurveOver_xHFunctionFieldBar N H').toHasPrincipalDivisors

theorem mapDomain_restrictAlong_eq_pushforwardAlong
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Finsupp.mapDomain (fun W => W.restrictAlong α hα) E = Divisor.pushforwardAlong α hα E := by
  haveI := isCurveOver_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)
  have hfin := finiteAlong_alpha p M H hpM α
  induction E using Finsupp.induction with
  | zero => simp only [Finsupp.mapDomain_zero, map_zero]
  | single_add W n E hW hn ih =>
    rw [Finsupp.mapDomain_add, map_add, ih, Finsupp.mapDomain_single]
    congr 1
    have h1 := AlgebraicCurve.Divisor.pushforwardAlong_single_one_of_isAlgClosed α hα hfin W
    have hs : (Finsupp.single W n : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = n • Finsupp.single W 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_zsmul, h1, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem mapDomain_restrictAlong_div_eq_ord_norm
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD : ∀ W, D W = W.ord f)
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    letI := algebraAlong α
    Finsupp.mapDomain (fun W => W.restrictAlong α hα) D V =
      V.ord (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f) := by
  haveI := hasPrincipalDivisors_xHFunctionFieldBar M H
  have hfin := finiteAlong_alpha p M H hpM α
  have hsep := separableAlong_alpha p M H hpM α hα
  have hnf := AlgebraicCurve.normFormulaAlong_of_separableAlong α hfin hsep
  rw [mapDomain_restrictAlong_eq_pushforwardAlong]

  unfold NormFormulaAlong Divisor.PushforwardNormFormula at hnf
  exact hnf f hf D hD V

end Ws49NormDock

namespace Ws49DivSnd

variable {X Y : Type*} [DecidableEq Y]

theorem mapDomain_apply_eq_sum (r : X → Y) (E : X →₀ ℤ) (s : Finset X) (hs : E.support ⊆ s) (y : Y) :
    Finsupp.mapDomain r E y = ∑ x ∈ s, if r x = y then E x else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_of_support_subset E hs _ (fun x _ => by simp)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.single_apply]

theorem support_filter_subset' (E : X →₀ ℤ) (P : X → Prop) [DecidablePred P] : (E.filter P).support ⊆ E.support := by
  classical
  rw [Finsupp.support_filter]
  exact Finset.filter_subset _ _

theorem mapDomain_filter_snd_eq_sub (D : X →₀ ℤ) (r₁ r₂ : X → Y) (Fst Snd : X → Prop)
    [DecidablePred Fst] [DecidablePred Snd] (w v' : Y)
    (h1 : ∀ x ∈ D.support, Snd x → (r₂ x = v' ↔ r₁ x = w))
    (h2 : ∀ x ∈ D.support, r₁ x = w → Fst x ∨ Snd x)
    (h3 : ∀ x, ¬ (Fst x ∧ Snd x)) :
    Finsupp.mapDomain r₂ (D.filter Snd) v' = Finsupp.mapDomain r₁ D w - Finsupp.mapDomain r₁ (D.filter Fst) w := by
  classical
  rw [mapDomain_apply_eq_sum r₂ (D.filter Snd) D.support (support_filter_subset' D Snd) v',
    mapDomain_apply_eq_sum r₁ D D.support (Finset.Subset.refl _) w,
    mapDomain_apply_eq_sum r₁ (D.filter Fst) D.support (support_filter_subset' D Fst) w,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hS : Snd x
  · have hF : ¬ Fst x := fun hF => h3 x ⟨hF, hS⟩
    by_cases hr : r₁ x = w
    · have hr2 : r₂ x = v' := (h1 x hx hS).mpr hr
      simp [hS, hF, hr, hr2]
    · have hr2 : ¬ r₂ x = v' := fun h => hr ((h1 x hx hS).mp h)
      simp [hS, hF, hr, hr2]
  · by_cases hr : r₁ x = w
    · have hF : Fst x := (h2 x hx hr).resolve_right hS
      simp [hS, hF, hr]
    · simp [hS, hr]

end Ws49DivSnd

namespace Ws49DivSnd

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

open Classical in

theorem count_identity
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
    {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Psp : JHPlaceSpecialization p M H hpM A)
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hcomm : ∀ v, δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v) =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ v))
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv' : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v') :
    Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D.filter (Psp.IsStrictSnd α β hα hβ δ)) v' =
      Finsupp.mapDomain (Psp.reduceFst α hα) D (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v') -
        Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (Psp.IsStrictFst α β hα hβ δ))
          (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v') := by
  have hφinj : Function.Injective (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) :=
    (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM)).1
  set φ := qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p with hφdef
  set r₁ := Psp.reduceFst α hα with hr₁
  set r₂ := Psp.reduceSnd β hβ δ with hr₂

  have hv'φ : ¬ (φ (δ (φ v')) = v') := hv'
  have hwφ : ¬ (φ (δ (φ (φ v'))) = φ v') := by
    intro h
    apply hv'φ
    apply hφinj
    rw [← hcomm (φ v')]
    exact h
  have h1 : ∀ W ∈ D.support, Psp.IsStrictSnd α β hα hβ δ W → (r₂ W = v' ↔ r₁ W = φ v') := by
    intro W _ hW
    have hrel : r₁ W = φ (r₂ W) := hW.1
    constructor
    · intro h; rw [hrel, h]
    · intro h; exact hφinj (hrel.symm.trans h)
  have h3 : ∀ W, ¬ (Psp.IsStrictFst α β hα hβ δ W ∧ Psp.IsStrictSnd α β hα hβ δ W) := by
    rintro W ⟨hF, hS⟩
    have e1 : δ (φ (r₁ W)) = r₂ W := hF.1
    have e2 : r₁ W = φ (r₂ W) := hS.1
    have hfix : ¬ (φ (δ (φ (r₂ W))) = r₂ W) := hS.2
    apply hfix
    rw [← hcomm, ← e2]
    exact e1
  have h2 : ∀ W ∈ D.support, r₁ W = φ v' → Psp.IsStrictFst α β hα hβ δ W ∨ Psp.IsStrictSnd α β hα hβ δ W := by
    intro W _ hW
    rcases hTD W with hA | hB
    · right
      have hA' : r₁ W = φ (r₂ W) := hA
      have hr2 : r₂ W = v' := hφinj (hA'.symm.trans hW)
      refine ⟨hA, ?_⟩
      show ¬ (φ (δ (φ (r₂ W))) = r₂ W)
      rw [hr2]; exact hv'φ
    · left
      refine ⟨hB, ?_⟩
      show ¬ (φ (δ (φ (r₁ W))) = r₁ W)
      rw [hW]; exact hwφ
  exact mapDomain_filter_snd_eq_sub D r₁ r₂ (Psp.IsStrictFst α β hα hβ δ) (Psp.IsStrictSnd α β hα hβ δ) (φ v') v' h1 h2 h3

end Ws49DivSnd

set_option synthInstance.maxHeartbeats 1600000 in
open Classical in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hN : ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        letI := algebraAlong α
        ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
          (∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
            (∀ V, D V = V.ord (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f)) →
            ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g) ∧
          ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord g =
              (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord (Rpd.R₁.residue ⟨f, h₁⟩) +
                u.ord (Rpd.R₂.residue ⟨f, h₂⟩))
    (hDF : Rpd.DivisorLawFst α (θ.toAlgHom.comp α) hα hβ δ)
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hcomm : ∀ v, δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v) = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ v)) :
    Rpd.DivisorLawSnd α (θ.toAlgHom.comp α) hα hβ δ := by
  intro f h₁ h₂ hr1 hr2 D hD v' hv'
  have hφinj : Function.Injective (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) :=
    (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM)).1

  have hwφ : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ
      (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v') := by
    intro h
    apply hv'
    apply hφinj
    have h' : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p
          (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v'))) =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v' := h
    rw [hcomm] at h'
    exact h'

  have hcount := Ws49DivSnd.count_identity Psp α (θ.toAlgHom.comp α) hα hβ δ hcomm hTD D v' hv'
  have hfst := hDF f h₁ h₂ hr1 hr2 D hD (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v') hwφ
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hr1 (map_zero _)
  obtain ⟨g, -, hg1, hg2⟩ := hN f h₁ h₂ hr1 hr2
  have hDα := Ws49NormDock.mapDomain_restrictAlong_div_eq_ord_norm p M H hpM α hα f hf0 D hD
  have htot : Finsupp.mapDomain (Psp.reduceFst α hα) D (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v') =
      (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v').ord g := by
    have e : Finsupp.mapDomain (Psp.reduceFst α hα) D =
        Finsupp.mapDomain Psp.sp (Finsupp.mapDomain (fun W => W.restrictAlong α hα) D) := by
      rw [← Finsupp.mapDomain_comp]; rfl
    rw [e]
    exact hg1 _ hDα _
  show Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D.filter (Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ)) v' =
    v'.ord (Rpd.R₂.residue ⟨f, h₂⟩)
  rw [hcount, htot, hg2 v']
  have hfst' : Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ))
      (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v') =
      (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v').ord (Rpd.R₁.residue ⟨f, h₁⟩) := hfst
  rw [hfst']
  ring

end S_ModularCurve_XHDRModelAtP_divisorLawSnd_prolongationDatum_of_divisorLawFst_of_norm_of_typeDichotomy
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_divisorLawSnd_prolongationDatum_of_divisorLawFst_of_norm_of_typeDichotomy (solution)
