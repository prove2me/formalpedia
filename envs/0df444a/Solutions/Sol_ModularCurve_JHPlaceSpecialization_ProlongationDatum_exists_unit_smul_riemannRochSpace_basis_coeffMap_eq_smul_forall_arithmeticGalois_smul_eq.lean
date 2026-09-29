-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/29c37048-343b-5f2e-8d8c-090fea4a249a

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq_xH
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg_xH
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jqNGen ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace BDH

open AlgebraicCurve IsLocalRing ModularCurve

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem poles_mul (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (U : ↥(xHFunctionFieldBar M H)) (hU0 : U ≠ 0)
    (T : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → Prop)
    (hUint : ∀ W, T W → 0 ≤ W.ord U)
    (hUT : ∀ W, 0 < E W → T W → E W ≤ W.ord U)
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ riemannRochSpace E) (hf0 : f ≠ 0)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hW : W.ord (U * f) < 0) : ¬ T W := by
  intro hT
  have hU : 0 ≤ W.ord U := hUint W hT
  rw [W.ord_mul hU0 hf0] at hW
  rcases (mem_riemannRochSpace_iff.mp hf) W with h | h
  · exact hf0 h
  · have hEW : 0 < E W := by omega
    have h2 := hUT W hEW hT
    omega

set_option maxHeartbeats 6400000 in

theorem hint (A : ValuationSubring (AlgebraicClosure ℚ)) (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (x xq : ↥(xHFunctionFieldBar M H)) (hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) (hθxq : θ xq = x)
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)]
    (hE : ∀ σ ∈ S, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • E = E)
    (U : ↥(xHFunctionFieldBar M H)) (hU0 : U ≠ 0)
    (hUfix : ∀ σ ∈ S, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • U = U)
    (hpJ : ∀ f ∈ riemannRochSpace E, f ≠ 0 → ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord (U * f) < 0 →
        ∃ a : ↥A, 0 < W.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)))
    (hpJq : ∀ f ∈ riemannRochSpace E, f ≠ 0 → ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord (U * f) < 0 →
        ∃ a : ↥A, 0 < W.ord (xq - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)))
    (V : Submodule (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : V = (riemannRochSpace E).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U))
    [FiniteDimensional (AlgebraicClosure ℚ) ↥V] :
    ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) ↥V) → ↥(xHFunctionFieldBar M H),
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      (∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries ↥A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries ↥A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((θ (b i) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))) ∧
      ∀ i, ∀ σ ∈ S, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • b i = b i := by
  classical
  have hinj : Function.Injective (LinearMap.mulLeft (AlgebraicClosure ℚ) U) := by
    intro a b h
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at h
    exact mul_left_cancel₀ hU0 h
  have hn : Module.finrank (AlgebraicClosure ℚ) ↥V = Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E) := by
    subst hV
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (riemannRochSpace E))).symm
  obtain ⟨b₀, hb₀V, hb₀li, hb₀fix⟩ :=
    ModularCurve.exists_linearIndependent_riemannRochSpace_forall_arithmeticGalois_smul_eq_xH M H S E hE
  let e : Fin (Module.finrank (AlgebraicClosure ℚ) ↥V) ≃ Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) := finCongr hn
  have hb₀ne : ∀ j, b₀ j ≠ 0 := fun j => hb₀li.ne_zero j
  have hmem : ∀ i, U * b₀ (e i) ∈ V := fun i => hV.ge (Submodule.mem_map_of_mem (hb₀V (e i)))

  have bd : ∀ g : ↥(xHFunctionFieldBar M H), g ≠ 0 →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord g < 0 →
        ∃ a : ↥A, 0 < W.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))) →
      ∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries ↥A), c ≠ 0 ∧
        coeffMap A.subtype y = c • ((g : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro g hg hpole
    obtain ⟨c, hc0, hc⟩ := ModularCurve.exists_forall_coeff_smul_mem_of_forall_ord_neg_xH A M H x hx g hg hpole
    refine ⟨c, ⟨fun k => ⟨_, hc k⟩, ?_⟩, hc0, ?_⟩
    ·
      exact (c • ((g : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))).isPWO_support.mono (by
        intro k hk
        simp only [Function.mem_support, ne_eq] at hk ⊢
        intro h0
        exact hk (Subtype.ext h0))
    · ext k
      rfl
  refine ⟨fun i => U * b₀ (e i), hmem, ?_, fun i => ⟨?_, ?_⟩, fun i σ hσ => ?_⟩
  · have h1 : LinearIndependent (AlgebraicClosure ℚ) (LinearMap.mulLeft (AlgebraicClosure ℚ) U ∘ b₀) :=
      hb₀li.map' (LinearMap.mulLeft (AlgebraicClosure ℚ) U) (LinearMap.ker_eq_bot.mpr hinj)
    exact h1.comp e e.injective
  · exact bd _ (mul_ne_zero hU0 (hb₀ne _)) (fun W hW => hpJ (b₀ (e i)) (hb₀V _) (hb₀ne _) W hW)
  · have hne : U * b₀ (e i) ≠ 0 := mul_ne_zero hU0 (hb₀ne _)
    have hwne : θ (U * b₀ (e i)) ≠ 0 := (map_ne_zero _).mpr hne
    refine bd _ hwne (fun W hW => ?_)
    have hcancel : SemilinearAut.ofAlgAut θ • (SemilinearAut.ofAlgAut θ.symm • W) = W := by
      rw [← mul_smul, ← map_mul, show θ * θ.symm = 1 from mul_inv_cancel θ, map_one, one_smul]
    have hordθ : ∀ g : ↥(xHFunctionFieldBar M H), W.ord (θ g) = (SemilinearAut.ofAlgAut θ.symm • W).ord g := fun g => by
      have := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut θ) (SemilinearAut.ofAlgAut θ.symm • W) g
      rwa [hcancel, SemilinearAut.ofAlgAut_smul] at this
    have hW' : (SemilinearAut.ofAlgAut θ.symm • W).ord (U * b₀ (e i)) < 0 := by
      rw [← hordθ]; simpa using hW
    obtain ⟨a, ha⟩ := hpJq (b₀ (e i)) (hb₀V _) (hb₀ne _) _ hW'
    refine ⟨a, ?_⟩
    have := hordθ (xq - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))
    rw [map_sub, AlgEquiv.commutes, hθxq] at this
    rw [this]
    exact ha
  · show arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • (U * b₀ (e i)) = U * b₀ (e i)
    rw [smul_mul', hUfix σ hσ, hb₀fix (e i) σ hσ]

end BDH

open Classical in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
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
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

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
    (S : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hS : ∀ σ ∈ S, σ ∈ A.inertiaSubgroupIn ℚ)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD : 0 ≤ D) (hgood : Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ D)
    (hDfix : ∀ V ∈ D.support, ∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V)
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace D)] :
    ∃ U : ↥(xHFunctionFieldBar M H),
      (∃ h₁ : U ∈ Rpd.R₁.integers, IsUnit (⟨U, h₁⟩ : Rpd.R₁.integers)) ∧
      (∃ h₂ : U ∈ Rpd.R₂.integers, IsUnit (⟨U, h₂⟩ : Rpd.R₂.integers)) ∧
      (∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • U = U) ∧
      ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) ↥((riemannRochSpace D).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U))) → ↥(xHFunctionFieldBar M H),
        (∀ i, b i ∈ (riemannRochSpace D).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U)) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
        (∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries ↥A), c ≠ 0 ∧
                coeffMap A.subtype y = c • ((b i : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))) ∧
             (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries ↥A), c ≠ 0 ∧
                coeffMap A.subtype y = c • ((θ (b i) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)))) ∧
        ∀ i, ∀ σ ∈ S, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • b i = b i := by
  classical

  have hjmem : jqModC ℚ ∈ xHFunctionField M H := by
    unfold xHFunctionField xHFunctionFieldC
    exact ModularCurve.intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  let x : ↥(xHFunctionFieldBar M H) := ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange _ hjmem⟩
  have hx : (x : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := map_jqModC _

  obtain ⟨U, hU₁, hU₂, hUfix, hpJ, hpJq⟩ :=
    ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_commonUnit_forall_pole_integral_forall_arithmeticGalois_smul_eq_of_riemannRochSpace
      p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn S hS D hD hgood hDfix x hx
  have hU0 : U ≠ 0 := by
    obtain ⟨h₁, hu⟩ := hU₁
    intro h
    exact hu.ne_zero (Subtype.ext h)

  have hE : ∀ σ ∈ S, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • D = D := by
    intro σ hσ
    calc arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • D
        = Finsupp.mapDomain (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • ·) D := SemilinearAut.divisor_smul_def _ D
      _ = Finsupp.mapDomain id D := Finsupp.mapDomain_congr fun W hW => hDfix W hW σ hσ
      _ = D := Finsupp.mapDomain_id
  obtain ⟨b, hbV, hbli, hbint, hbfix⟩ := BDH.hint A S θ x (θ.symm x) hx (θ.apply_symm_apply x) D hE U hU0 hUfix hpJ hpJq
    ((riemannRochSpace D).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U)) rfl
  exact ⟨U, hU₁, hU₂, hUfix, b, hbV, hbli, hbint, hbfix⟩

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_unit_smul_riemannRochSpace_basis_coeffMap_eq_smul_forall_arithmeticGalois_smul_eq (solution)
