-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.comp_surjective_of_depthCompLaw_of_annulusInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/de012e8e-8c15-59af-aaec-620f355709ec

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf

import Theorems.Thm_ModularCurve_comp_surjective_of_forall_exists_eq_crossingCoord
import Theorems.Thm_ModularCurve_exists_mem_dom_forall_inertia_smul_eq_and_evalAt_param_eq
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul
import Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_nonneg_of_mem
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_comp_surjective_of_depthCompLaw_of_annulusInf
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace SurjAux

theorem isCurveOver_up (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := by
  obtain ⟨x, htr, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H)
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd

theorem restrictAlong_semilinearAut_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : SemilinearAut.IntertwinesAlong φ.toRingHom g g') (w : Place K F') :
    (g' • w).restrictAlong φ hφ = g • (w.restrictAlong φ hφ) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact SemilinearAut.restrict_smul (F := F) (g := g) (g' := g') (fun x => hgg' x) w

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p]

theorem smul_alpha
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • α u =
      α (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ • u) := by
  apply Subtype.ext
  rw [coe_arithmeticGalois_smul, hα_coe, hα_coe, coe_arithmeticGalois_smul]

theorem reduceFst_smul (Psp : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceFst α hα (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) = Psp.reduceFst α hα W := by
  show Psp.sp ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W).restrictAlong α hα) = Psp.sp (W.restrictAlong α hα)
  rw [restrictAlong_semilinearAut_smul α hα
      (g := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ)
      (g' := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ)
      (fun x => smul_alpha α hα_coe σ x) W]
  exact Psp.d6_inertia σ hσ _

theorem reduceSnd_smul (Psp : JHPlaceSpecialization p M H hpM A)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W) =
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W := by
  show δ (Psp.sp ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W).restrictAlong (θ.toAlgHom.comp α) hβ)) =
    δ (Psp.sp (W.restrictAlong (θ.toAlgHom.comp α) hβ))
  rw [restrictAlong_semilinearAut_smul (θ.toAlgHom.comp α) hβ
      (g := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField (M / p) (infSubgroup p M H hpM)) σ)
      (g' := arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ)
      (fun x => by
        show arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ (α x) = θ (α _)
        rw [← hθgal, smul_alpha α hα_coe σ x]) W]
  exact congrArg δ (Psp.d6_inertia σ hσ _)

theorem mk_mem_inertiaInvariants
    (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))))
    (h : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) :
    Pic0.mk D ∈ JHPlaceSpecialization.inertiaInvariants M H A := by
  intro σ hσ
  show arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • Pic0.mk D = Pic0.mk D
  rw [SemilinearAut.pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [SemilinearAut.coe_degZeroSMulHom, SemilinearAut.divisor_smul_def]
  calc Finsupp.mapDomain (fun x => arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • x)
          (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
        = Finsupp.mapDomain id (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :=
          Finsupp.mapDomain_congr fun V hV => h V hV σ hσ
    _ = _ := Finsupp.mapDomain_id

theorem not_isStrictSnd_of_isStrictFst (Psp : JHPlaceSpecialization p M H hpM A)
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (h : Psp.IsStrictFst α β hα hβ δ W) :
    ¬ Psp.IsStrictSnd α β hα hβ δ W := by
  intro h'
  apply h.2

  show qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (Psp.reduceFst α hα W))) = Psp.reduceFst α hα W
  rw [h.1]
  exact h'.1.symm

theorem frob_injective [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)] :
    Function.Injective (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p) := by
  intro v w h
  rw [ModularCurve.qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul, ModularCurve.qExpFrobeniusPlaceModL_eq_qExpArithFrobC_smul] at h
  exact smul_left_cancel _ h

theorem eq_one_of_pow_eq_self {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Γ₀} (hv0 : 0 < v) (hv1 : v < 1)
    {n : ℕ} (h : v ^ n = v) : n = 1 := by
  rcases Nat.lt_trichotomy n 1 with hn | hn | hn
  · have : n = 0 := by omega
    subst this
    rw [pow_zero] at h
    exact absurd hv1 (h ▸ lt_irrefl _)
  · exact hn
  · have := pow_lt_pow_right_of_lt_one₀ hv0 hv1 hn
    rw [pow_one, h] at this
    exact absurd this (lt_irrefl _)

theorem twoPoint {K F : Type*} [Field K] [Field F] [Algebra K F] (V V₀ : Place K F) (h : V.deg = 1) (h₀ : V₀.deg = 1) :
    ∃ D : ↥(Divisor.degZero (K := K) (F := F)), (D : Divisor K F) = Finsupp.single V 1 + Finsupp.single V₀ (-1) := by
  refine ⟨⟨Finsupp.single V 1 + Finsupp.single V₀ (-1), ?_⟩, rfl⟩
  rw [Divisor.mem_degZero, map_add, Divisor.degree_single, Divisor.degree_single, h, h₀]
  norm_num

theorem mem_support_twoPoint {K F : Type*} [Field K] [Field F] [Algebra K F] (V V₀ V' : Place K F)
    (hV' : V' ∈ (Finsupp.single V (1 : ℤ) + Finsupp.single V₀ (-1)).support) : V' = V ∨ V' = V₀ := by
  classical
  rcases Finset.mem_union.mp (Finsupp.support_add hV') with h | h
  · exact Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h))
  · exact Or.inr (Finset.mem_singleton.mp (Finsupp.support_single_subset h))

end SurjAux

namespace SurjAux

set_option maxHeartbeats 6400000 in

theorem widthOne
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
    {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (e : ↥SS → ℕ) (depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ)
    (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e)
    (hlaw : Psp.DepthCompLaw α (θ.toAlgHom.comp α) hα hβ δ SS e depth comp)
    (hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1)
    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV₀s : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V₀)
    (hV₀fix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V₀ = V₀)
    (V₁ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV₁s : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V₁)
    (hV₁fix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V₁ = V₁)
    (s : ↥SS) (hes : e s = 1) :
    ∃ x, comp x = componentGroupProj e (crossingCoord s) := by
  classical

  have hnode : ∀ s' : ↥SS, JHPlaceSpecialization.Fixed p M H hpM A δ (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 ∧
      (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 ∧
      (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := by
    intro s'
    obtain ⟨hss, heq⟩ := (hSS s'.1).mp s'.2
    exact ⟨heq ▸ (hFix _ hss).2, heq, hss⟩
  have hV₀ne : ∀ s' : ↥SS, Psp.reduceFst α hα V₀ ≠ (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 :=
    fun s' h => hV₀s.2 (h ▸ (hnode s').1)
  have hV₀nS : ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V₀ :=
    SurjAux.not_isStrictSnd_of_isStrictFst Psp α _ hα hβ δ V₀ hV₀s
  have hdepthDiv0 : ∀ (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s' : ↥SS),
      Psp.depthDiv α hα depth (Finsupp.single V 1 + Finsupp.single V₀ (-1)) (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
        (Finsupp.single (Psp.reduceFst α hα V) (depth V : ℤ) : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
          (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 := by
    intro V s'
    simp only [JHPlaceSpecialization.depthDiv]
    rw [Finsupp.sum_add_index' (fun a => by simp) (fun a b₁ b₂ => by rw [add_mul, Finsupp.single_add]),
      Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), Finsupp.add_apply,
      Finsupp.single_eq_of_ne (hV₀ne s').symm, add_zero, one_mul]
  have hV₁ne : ∀ s' : ↥SS, Psp.reduceFst α hα V₁ ≠ (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 := by
    intro s' h
    apply hV₁s.2
    have h2 : Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V₁ = (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 :=
      SurjAux.frob_injective (hV₁s.1.symm.trans (h.trans (hnode s').2.1))
    rw [h2]
    exact (hFix _ (hnode s').2.2).1
  have hTP := SurjAux.twoPoint (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) V₁ V₀ (hdeg1 V₁) (hdeg1 V₀)
  obtain ⟨D, hDval⟩ := hTP
  have hfixD : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V := by
    intro V hV σ hσ
    rcases SurjAux.mem_support_twoPoint V₁ V₀ V (hDval ▸ hV) with rfl | rfl
    · exact hV₁fix σ hσ
    · exact hV₀fix σ hσ
  have hH := SurjAux.mk_mem_inertiaInvariants (A := A) D hfixD
  have hsupp : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) ∧
        (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨
          ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) := by
    intro V hV
    refine ⟨hfixD V hV, ?_⟩
    rcases SurjAux.mem_support_twoPoint V₁ V₀ V (hDval ▸ hV) with rfl | rfl
    · exact Or.inr (Or.inl hV₁s)
    · exact Or.inl hV₀s
  refine ⟨⟨Pic0.mk D, hH⟩, (hlaw D hH hsupp s).trans ?_⟩
  simp only [hDval]
  have hsnd : Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (Finsupp.single V₁ 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Finsupp.single V₁ 1 := by
    unfold JHPlaceSpecialization.sndDiv
    rw [Finsupp.filter_add, Finsupp.filter_single_of_pos _ hV₁s, Finsupp.filter_single_of_neg _ hV₀nS, add_zero]
  have hdeg : Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (Finsupp.single V₁ 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) = 1 := by
    rw [hsnd, Divisor.degree_single, hdeg1]; rfl
  congr 1
  apply LinearMap.ext
  intro x
  have hterm : ∀ s' : ↥SS, (Psp.depthDiv α hα depth (Finsupp.single V₁ 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 • crossingCoord s') x = 0 := by
    intro s'
    have hz : Psp.depthDiv α hα depth (Finsupp.single V₁ 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 = 0 := by
      rw [hdepthDiv0]; exact Finsupp.single_eq_of_ne (hV₁ne s').symm
    rw [LinearMap.smul_apply, hz, zero_smul]
  have h1 : Psp.depthDual α hα SS depth (Finsupp.single V₁ 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) x = 0 := by
    unfold JHPlaceSpecialization.depthDual
    rw [LinearMap.coe_sum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun s' _ => hterm s'
  have h2 : (Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (Finsupp.single V₁ 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) • ((e s : ℤ) • crossingCoord s)) x = crossingCoord s x := by
    rw [hdeg, hes, LinearMap.smul_apply, LinearMap.smul_apply, Nat.cast_one, one_smul, one_smul]
  rw [LinearMap.add_apply, h1, h2, zero_add]

set_option maxHeartbeats 6400000 in

theorem widthTwo
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
    {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (e : ↥SS → ℕ) (depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ)
    (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e)
    (hlaw : Psp.DepthCompLaw α (θ.toAlgHom.comp α) hα hβ δ SS e depth comp)
    (hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1)
    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV₀s : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V₀)
    (hV₀fix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V₀ = V₀)
    (s : ↥SS) (Vs : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hVs1 : Psp.reduceFst α hα Vs = (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1)
    (hVsnS : ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Vs)
    (hVsfix : ∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • Vs = Vs)
    (hdepthVs : depth Vs = 1) :
    ∃ x, comp x = componentGroupProj e (crossingCoord s) := by
  classical

  have hnode : ∀ s' : ↥SS, JHPlaceSpecialization.Fixed p M H hpM A δ (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 ∧
      (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 ∧
      (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := by
    intro s'
    obtain ⟨hss, heq⟩ := (hSS s'.1).mp s'.2
    exact ⟨heq ▸ (hFix _ hss).2, heq, hss⟩
  have hV₀ne : ∀ s' : ↥SS, Psp.reduceFst α hα V₀ ≠ (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 :=
    fun s' h => hV₀s.2 (h ▸ (hnode s').1)
  have hV₀nS : ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V₀ :=
    SurjAux.not_isStrictSnd_of_isStrictFst Psp α _ hα hβ δ V₀ hV₀s
  have hdepthDiv0 : ∀ (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s' : ↥SS),
      Psp.depthDiv α hα depth (Finsupp.single V 1 + Finsupp.single V₀ (-1)) (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
        (Finsupp.single (Psp.reduceFst α hα V) (depth V : ℤ) : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
          (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 := by
    intro V s'
    simp only [JHPlaceSpecialization.depthDiv]
    rw [Finsupp.sum_add_index' (fun a => by simp) (fun a b₁ b₂ => by rw [add_mul, Finsupp.single_add]),
      Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), Finsupp.add_apply,
      Finsupp.single_eq_of_ne (hV₀ne s').symm, add_zero, one_mul]
  have hinjS : ∀ s' : ↥SS, (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 = (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 → s' = s := by
    intro s' h
    apply Subtype.ext
    apply Prod.ext h
    exact SurjAux.frob_injective (((hnode s').2.1).symm.trans (h.trans (hnode s).2.1))
  have hTP := SurjAux.twoPoint (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) Vs V₀ (hdeg1 Vs) (hdeg1 V₀)
  obtain ⟨D, hDval⟩ := hTP
  have hfixD : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V := by
    intro V hV σ hσ
    rcases SurjAux.mem_support_twoPoint Vs V₀ V (hDval ▸ hV) with rfl | rfl
    · exact hVsfix σ hσ
    · exact hV₀fix σ hσ
  have hH := SurjAux.mk_mem_inertiaInvariants (A := A) D hfixD
  have hsupp : ∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) ∧
        (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨
          ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) := by
    intro V hV
    refine ⟨hfixD V hV, ?_⟩
    rcases SurjAux.mem_support_twoPoint Vs V₀ V (hDval ▸ hV) with rfl | rfl
    · exact Or.inr (Or.inr ⟨s.1, s.2, hVs1⟩)
    · exact Or.inl hV₀s
  refine ⟨⟨Pic0.mk D, hH⟩, (hlaw D hH hsupp s).trans ?_⟩
  simp only [hDval]
  have hne : ∀ s' : ↥SS, s' ≠ s → Psp.reduceFst α hα Vs ≠ (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 := by
    intro s' hs' h
    exact hs' (hinjS s' (h.symm.trans hVs1))
  have hsnd : Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (Finsupp.single Vs 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = 0 := by
    unfold JHPlaceSpecialization.sndDiv
    rw [Finsupp.filter_add, Finsupp.filter_single_of_neg _ hVsnS, Finsupp.filter_single_of_neg _ hV₀nS, add_zero]
  congr 1
  apply LinearMap.ext
  intro x
  have hmain : (Psp.depthDiv α hα depth (Finsupp.single Vs 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 • crossingCoord s) x = crossingCoord s x := by
    have hv : Psp.depthDiv α hα depth (Finsupp.single Vs 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 = 1 := by
      rw [hdepthDiv0, ← hVs1, Finsupp.single_eq_same, hdepthVs, Nat.cast_one]
    rw [LinearMap.smul_apply, hv, one_smul]
  have hterm : ∀ s' : ↥SS, s' ≠ s → (Psp.depthDiv α hα depth (Finsupp.single Vs 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 • crossingCoord s') x = 0 := by
    intro s' hs'
    have hz : Psp.depthDiv α hα depth (Finsupp.single Vs 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s' : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 = 0 := by
      rw [hdepthDiv0]; exact Finsupp.single_eq_of_ne (hne s' hs').symm
    rw [LinearMap.smul_apply, hz, zero_smul]
  have h1 : Psp.depthDual α hα SS depth (Finsupp.single Vs 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) x = crossingCoord s x := by
    unfold JHPlaceSpecialization.depthDual
    rw [LinearMap.coe_sum, Finset.sum_apply, Finset.sum_eq_single s (fun s' _ hs' => hterm s' hs') (fun h => absurd (Finset.mem_univ s) h)]
    exact hmain
  have h2 : (Divisor.degree (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ (Finsupp.single Vs 1 + Finsupp.single V₀ (-1) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) • ((e s : ℤ) • crossingCoord s)) x = 0 := by
    rw [hsnd, map_zero, LinearMap.smul_apply, zero_smul]
  rw [LinearMap.add_apply, h1, h2, add_zero]

end SurjAux

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ)
    (hdepth : ∀ (s : ↥SS) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H)),
      ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
          W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
        (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
          (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
        algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
        (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

        (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
          ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
            (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
              ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
        (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
          s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
          ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
            (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
              ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
                (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))) →
      Psp.AnnulusDepthLawInf α hα (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) An depth)
    (comp : ↥(JHPlaceSpecialization.inertiaInvariants M H A) →+ componentGroup e)
    (hlaw : Psp.DepthCompLaw α (θ.toAlgHom.comp α) hα hβ δ SS e depth comp)
    (hV₀ : ∃ V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V₀ ∧ (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
          (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V₀ = V₀))
    (hV₁ : ∃ V₁ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V₁ ∧ (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
          (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V₁ = V₁)) :
    Function.Surjective comp := by
  classical
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := SurjAux.isCurveOver_up M H
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed

  apply ModularCurve.comp_surjective_of_forall_exists_eq_crossingCoord e comp
  intro s
  refine hV₀.elim fun V₀ hV₀' => ?_
  by_cases hes : e s = 1
  ·
    exact hV₁.elim fun V₁ hV₁' =>
      SurjAux.widthOne θ α hα hβ δ SS hSS Psp hFix e depth comp hlaw hdeg1 V₀ hV₀'.1 hV₀'.2 V₁ hV₁'.1 hV₁'.2 s hes
  ·
    refine (hAnn s).elim fun An hAn => ?_
    refine hAn.2.1.elim fun u hu => ?_
    have hdom := hAn.1
    have hmod : An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u := hu.2
    have hz := hAn.2.2.1
    have hADL : Psp.AnnulusDepthLawInf α hα (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) An depth := hdepth s An hAn

    have hdomσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W ∈ An.dom,
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • W ∈ An.dom := by
      intro σ hσ W hW
      rw [hdom] at hW ⊢
      simp only [JHPlaceSpecialization.IsStrictFst, JHPlaceSpecialization.IsStrictSnd,
        SurjAux.reduceFst_smul Psp α hα hα_coe σ hσ, SurjAux.reduceSnd_smul Psp θ hθgal α hβ hα_coe δ σ hσ] at hW ⊢
      exact hW
    have hpA : ((p : ℕ) : ↥A) ∈ maximalIdeal ↥A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      exact (ValuationSubring.mem_nonunits_iff A).mp hA
    have hp0Q : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

    refine (Nat.exists_eq_add_one_of_ne_zero (he s).ne').elim fun k hk => ?_
    have hk0 : k ≠ 0 := fun h0 => hes (by rw [hk, h0])
    have hc : ((p : ℕ) : ↥A) ^ k ∈ maximalIdeal ↥A := Ideal.pow_mem_of_mem _ hpA _ (Nat.pos_of_ne_zero hk0)
    have hc0 : ((((p : ℕ) : ↥A) ^ k : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
      push_cast
      exact pow_ne_zero _ hp0Q
    have hcm : ∃ m ∈ maximalIdeal ↥A, ((An.modulus : ↥A) : AlgebraicClosure ℚ) = ((((p : ℕ) : ↥A) ^ k : ↥A) : AlgebraicClosure ℚ) * m := by
      refine ⟨((p : ℕ) : ↥A) * u, Ideal.mul_mem_right _ _ hpA, ?_⟩
      rw [hmod, hk]
      push_cast
      ring
    have hcσ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ ((((p : ℕ) : ↥A) ^ k : ↥A) : AlgebraicClosure ℚ) = ((((p : ℕ) : ↥A) ^ k : ↥A) : AlgebraicClosure ℚ) := by
      intro σ _
      push_cast
      rw [map_pow, map_natCast]

    refine (ModularCurve.exists_mem_dom_forall_inertia_smul_eq_and_evalAt_param_eq A (xHFunctionField M H) An hz hdomσ
        (((p : ℕ) : ↥A) ^ k) hc hc0 hcm hcσ).elim fun Vs hVs => ?_
    have hVsdom : Vs ∈ An.dom := hVs.1
    have hVsfix := hVs.2.1
    have hVsval : Vs.evalAt An.param = ((((p : ℕ) : ↥A) ^ k : ↥A) : AlgebraicClosure ℚ) := hVs.2.2
    have hVs3 := (hdom Vs).mp hVsdom

    have hdepthVs : depth Vs = 1 := by
      have hrat : Vs.IsRational := (An.mem_dom Vs hVsdom).1
      have hzO : An.param ∈ Vs.toValuationSubring := (An.mem_dom Vs hVsdom).2.1
      have hz0 : An.param ≠ 0 := by
        intro h
        apply hc0
        rw [← hVsval, h, ← map_zero (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
          AlgebraicCurve.Place.evalAt_algebraMap]
      have hord : Vs.ord An.param = 0 := by
        have h0 := AlgebraicCurve.Place.ord_nonneg_of_mem Vs hzO
        have h1 : ¬ (1 ≤ Vs.ord An.param) := fun h1 =>
          hc0 (hVsval ▸ (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord Vs hrat hz0 hzO).mpr h1)
        have hlt : Vs.ord An.param < 1 := not_le.mp h1
        exact le_antisymm (Int.le_of_lt_add_one (by rwa [zero_add])) h0
      have hinvO : An.param⁻¹ ∈ Vs.toValuationSubring := by
        rw [AlgebraicCurve.Place.mem_iff_ord_nonneg Vs (inv_ne_zero hz0), AlgebraicCurve.Place.ord_inv, hord, neg_zero]
      have hev : Vs.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An.modulus : ↥A) : AlgebraicClosure ℚ)) * An.param⁻¹) =
          ((An.modulus : ↥A) : AlgebraicClosure ℚ) * (((((p : ℕ) : ↥A) ^ k : ↥A) : AlgebraicClosure ℚ))⁻¹ := by
        rw [AlgebraicCurve.Place.evalAt_mul Vs hrat (Vs.algebraMap_mem' _) hinvO, AlgebraicCurve.Place.evalAt_algebraMap,
          AlgebraicCurve.Place.evalAt_inv Vs hrat hz0 hord, hVsval]
      have hpu : ((An.modulus : ↥A) : AlgebraicClosure ℚ) * (((((p : ℕ) : ↥A) ^ k : ↥A) : AlgebraicClosure ℚ))⁻¹ =
          ((p : ℕ) : AlgebraicClosure ℚ) * ((u : ↥A) : AlgebraicClosure ℚ) := by
        rw [hmod, hk]
        push_cast
        rw [pow_succ', mul_right_comm, mul_inv_cancel_right₀ (pow_ne_zero k hp0Q)]
      have h := hADL Vs hVs3.1 hVsfix
      rw [hev, hpu, map_mul, (ValuationSubring.valuation_eq_one_iff A u).mp hu.1, mul_one] at h
      have hv0 : 0 < A.valuation ((p : ℕ) : AlgebraicClosure ℚ) := (Valuation.pos_iff A.valuation).mpr hp0Q
      have hcoe : (((p : ℕ) : ↥A) : AlgebraicClosure ℚ) = ((p : ℕ) : AlgebraicClosure ℚ) := rfl
      have hv1 : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := hcoe ▸ (ValuationSubring.valuation_lt_one_iff A _).mp hpA
      exact SurjAux.eq_one_of_pow_eq_self hv0 hv1 h.symm
    exact SurjAux.widthTwo θ α hα hβ δ SS hSS Psp hFix e depth comp hlaw hdeg1 V₀ hV₀'.1 hV₀'.2 s Vs hVs3.1 hVs3.2.2 hVsfix hdepthVs

#print axioms solution

end S_ModularCurve_JHPlaceSpecialization_comp_surjective_of_depthCompLaw_of_annulusInf
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_comp_surjective_of_depthCompLaw_of_annulusInf (solution)
