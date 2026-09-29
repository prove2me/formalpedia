-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/af3d0936-ca93-5419-a34a-1f63117dbbb3

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope.ModularCurve ModularCurve.JHNeronObjectAtP"
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.ΓN JHNeronObjectAtP.Fbar JHNeronObjectAtP arithmeticGalois qExpand ssPlacesQExp diamondActionModL infSubgroup ssNodePairsQExp mem_ssNodePairsQExp_iff translation_mem_GammaH xHFunctionField xHFunctionFieldBar qExpFrobeniusPlaceModL JHPlaceSpecialization.IsAffinePlace JHPlaceSpecialization.Fixed JHPlaceSpecialization JHPlaceSpecialization.fstDiv JHPlaceSpecialization.sndDiv JHPlaceSpecialization.IsInftySide JHPlaceSpecialization.IsZeroSide JHPlaceSpecialization.ProlongationDatum JHPlaceSpecialization.exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope hasPrincipalDivisors_xHFunctionFieldBar JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC"
namespace PrincGoodHCount
p2m_open "ModularCurve"

theorem degree_eq_sum {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = D.sum (fun _ n => n) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply]
  exact Finsupp.sum_congr fun v _ => by rw [AddMonoidHom.mulRight_apply, hdeg, Nat.cast_one, mul_one]

theorem sum_mapDomain_eq {X Y : Type*} (g : X → Y) (D : X →₀ ℤ) :
    (Finsupp.mapDomain g D).sum (fun _ n => n) = D.sum (fun _ n => n) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem sum_eq_neg_sum {X : Type*} (M Dr : X →₀ ℤ) (W : Finset X) (o : X → ℤ)
    (hDr : ∀ v, Dr v = o v) (hdeg : Dr.sum (fun _ n => n) = 0)
    (hM : ∀ v, v ∉ W → M v = o v) (hMW : ∀ w ∈ W, M w = 0) :
    M.sum (fun _ n => n) = -(∑ w ∈ W, o w) := by
  classical
  have hMeq : M = Dr.filter (fun v => v ∉ W) := by
    ext v
    by_cases hv : v ∈ W
    · rw [hMW v hv, Finsupp.filter_apply, if_neg (fun h => h hv)]
    · rw [hM v hv, Finsupp.filter_apply, if_pos hv, hDr v]
  have hsplit : Dr.sum (fun _ n => n)
      = (Dr.filter (fun v => v ∉ W)).sum (fun _ n => n)
        + (Dr.filter (fun v => ¬ (v ∉ W))).sum (fun _ n => n) := by
    conv_lhs => rw [← Finsupp.filter_add_filter_not Dr (fun v => v ∉ W)]
    exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)
  have hW : (Dr.filter (fun v => ¬ (v ∉ W))).sum (fun _ n => n) = ∑ w ∈ W, o w := by
    rw [Finsupp.sum]
    have hsub : (Dr.filter (fun v => ¬ (v ∉ W))).support ⊆ W := by
      intro v hv
      rw [Finsupp.support_filter, Finset.mem_filter] at hv
      exact not_not.mp hv.2
    rw [Finset.sum_subset hsub (fun v hvW hvn => by
      exact not_not.mp (mt Finsupp.mem_support_iff.mpr hvn))]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finsupp.filter_apply, if_pos (not_not.mpr hw), hDr]
  rw [hMeq]
  linarith [hsplit, hW, hdeg]

theorem mapDomain_filter_apply_eq_zero {X Y : Type*} (D : X →₀ ℤ) (p : X → Prop)
    [DecidablePred p] (g : X → Y) (y : Y) (h : ∀ x, p x → g x ≠ y) :
    Finsupp.mapDomain g (D.filter p) y = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finsupp.single_apply]
  split_ifs with hxy
  · exfalso
    have hpx : p x := by
      by_contra hnp
      exact (Finsupp.mem_support_iff.mp hx) (by rw [Finsupp.filter_apply, if_neg hnp])
    exact h x hpx hxy
  · rfl

theorem degree_eq_neg_sum {K F K' F' : Type*} [Field K] [Field F] [Algebra K F]
    [Field K'] [Field F'] [Algebra K' F']
    (hdegK : ∀ V : Place K F, V.deg = 1) (hdegK' : ∀ v : Place K' F', v.deg = 1)
    (D : Divisor K F) (g : Place K F → Place K' F') (W : Finset (Place K' F'))
    (o : Place K' F' → ℤ) (Dr : Divisor K' F')
    (hDr : ∀ v, Dr v = o v) (hDrdeg : Divisor.degree Dr = 0)
    (hM : ∀ v, v ∉ W → Finsupp.mapDomain g D v = o v)
    (hMW : ∀ w ∈ W, Finsupp.mapDomain g D w = 0) :
    Divisor.degree D = -(∑ w ∈ W, o w) := by
  rw [degree_eq_sum hdegK, ← sum_mapDomain_eq g D]
  rw [degree_eq_sum hdegK'] at hDrdeg
  exact sum_eq_neg_sum _ Dr W o hDr hDrdeg hM hMW

theorem neg_sum_eq_cast {ι : Type*} [Fintype ι] (a : ι → ℤ) (b : ι → ℕ)
    (h : ∀ i, a i = -((b i : ℕ) : ℤ)) :
    -(∑ i, a i) = ((∑ i, b i : ℕ) : ℤ) := by
  rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [h i, neg_neg]

theorem deg_eq_one_of_surjective {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (h : Function.Surjective (algebraMap K v.ResidueField)) : v.deg = 1 := by
  have e : K ≃ₗ[K] v.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap K v.ResidueField)
      ⟨(algebraMap K v.ResidueField).injective, h⟩
  show Module.finrank K v.ResidueField = 1
  rw [← e.finrank_eq, Module.finrank_self]

end ModularCurve.PrincGoodHCount

open ModularCurve.PrincGoodHCount in
open Classical in

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

    (hVSlope : ∀ An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ s : ↥SS, ((∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            W ∈ (An s).dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
          (∃ u : ↥A, IsUnit u ∧ (An s).modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
            (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (An s).param = (An s).param) ∧
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : AlgebraicClosure ℚ))⁻¹ * (An s).param ∈ Rpd.R₁.integers ∧
          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨(An s).param, h₂⟩ ≠ 0) ∧

          (∃ h₂ : (An s).param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨(An s).param, h₂⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (An s).param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
          (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹ ∈ Rpd.R₁.integers,
            s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
            ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
              (∀ P ∈ (An s).dom, P.ord f = 0) → ∀ P ∈ (An s).dom,
                ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (((An s).modulus : ↥A) : AlgebraicClosure ℚ) * (An s).param⁻¹)) ^
                  (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))) →
      ∀ k : ℕ, (∀ s : ↥SS, e s ∣ k) →
        ∃ (f : ↥(xHFunctionFieldBar M H)) (c : AlgebraicClosure ℚ) (hc : c • f ∈ Rpd.R₁.integers),
          f ≠ 0 ∧ Rpd.R₁.residue ⟨c • f, hc⟩ ≠ 0 ∧
          (∀ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, G V = V.ord f) → Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) →
            (∀ s ∈ SS, Psp.reduceFst α hα V ≠ s.1) → V.ord f = 0) ∧
          (∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → (∀ s ∈ SS, v ≠ s.1) →
            v.ord (Rpd.R₁.residue ⟨c • f, hc⟩ : Fbar p M H hpM (ResidueField ↥A)) = 0) ∧
          (∀ s : ↥SS, ∃ a : AlgebraicClosure ℚ, a ≠ 0 ∧ ∀ P ∈ (An s).dom, P.ord f = 0 ∧
            ∃ h : P.evalAt f * a * (P.evalAt (An s).param) ^ (-((k / e s : ℕ) : ℤ)) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hOSFst : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ E) v = v.ord (Rpd.R₁.residue ⟨g, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSSnd : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ E) v = v.ord (Rpd.R₂.residue ⟨g, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSInf : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) c →
          Finsupp.mapDomain (Psp.reduceFst α hα) (E.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα c) =
            (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨g, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hOSZero : ∀ (g : ↥(xHFunctionFieldBar M H)) (h₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ W, E W = W.ord g) →
        ∀ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) c →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (E.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ c).ord (Rpd.R₂.residue ⟨g, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) :
    ∃ G : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Divisor.IsPrincipal G ∧ Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ G ∧
        (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = ((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) ∧
        (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = -((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) := by
  classical
  obtain ⟨f, hf, c, hc, h1, h2, h3, h4⟩ :=
    ModularCurve.JHPlaceSpecialization.exists_isGoodDiv_ord_residue_eq_neg_lcm_div_of_annulus_of_verticalSlope
      p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal
      hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn hVSlope
      hOSFst hOSSnd hOSInf hOSZero

  haveI := hasPrincipalDivisors_xHFunctionFieldBar M H
  obtain ⟨G, hG, hGdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf

  obtain ⟨hPDb, -, hsurj⟩ :=
    JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2 (ResidueField ↥A)
  haveI := hPDb
  obtain ⟨Dr, hDr, hDrdeg⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField ↥A) (Rpd.R₁.residue ⟨c • f, hc⟩) h1
  have hdegK : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.deg = 1 := fun V =>
    place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)
      (translation_mem_GammaH M H) (xHFunctionField M H) rfl V
  have hdegk : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), v.deg = 1 := fun v =>
    deg_eq_one_of_surjective v (hsurj v)

  have hmem : ∀ s ∈ SS, s.2 ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p ∧ s.1 = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p s.2 :=
    fun s hs => (mem_ssNodePairsQExp_iff s).mp ((hSS s).mp hs)

  have hFix1 : ∀ s ∈ SS, JHPlaceSpecialization.Fixed p M H hpM A δ s.1 := fun s hs => by
    obtain ⟨hs2, hs1⟩ := hmem s hs
    rw [hs1]
    exact (hFix s.2 hs2).2

  have hinj : ∀ x ∈ SS, ∀ y ∈ SS, x.1 = y.1 → x = y := by
    intro x hx y hy hxy
    obtain ⟨hx2, hx1⟩ := hmem x hx
    obtain ⟨hy2, hy1⟩ := hmem y hy
    have ex : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p x.2)) = x.2 := (hFix x.2 hx2).1
    have ey : qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y.2)) = y.2 := (hFix y.2 hy2).1
    have h2 : x.2 = y.2 := by
      rw [← ex, ← ey, ← hx1, ← hy1, hxy]
    exact Prod.ext hxy h2

  let W : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) := SS.image Prod.fst

  have hMW : ∀ w ∈ W, Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G) w = 0 := by
    intro w hw
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
    exact mapDomain_filter_apply_eq_zero G (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ) (Psp.reduceFst α hα) _
      (fun V hV hVw => hV.2 (by rw [hVw]; exact hFix1 s hs))

  have hM : ∀ v, v ∉ W → Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G) v = v.ord (Rpd.R₁.residue ⟨c • f, hc⟩) := by
    intro v hv
    exact h4 G hG v (fun s hs hvs => hv (Finset.mem_image.mpr ⟨s, hs, hvs.symm⟩))

  have key : (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = -(∑ w ∈ W, w.ord (Rpd.R₁.residue ⟨c • f, hc⟩)) :=
    degree_eq_neg_sum hdegK hdegk (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G) (Psp.reduceFst α hα) W _ Dr hDr hDrdeg hM hMW
  have hsumW : (∑ w ∈ W, w.ord (Rpd.R₁.residue ⟨c • f, hc⟩)) = ∑ s ∈ SS, s.1.ord (Rpd.R₁.residue ⟨c • f, hc⟩) :=
    Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)
  have hsumSS : (∑ s ∈ SS, s.1.ord (Rpd.R₁.residue ⟨c • f, hc⟩)) = ∑ s : ↥SS, s.1.1.ord (Rpd.R₁.residue ⟨c • f, hc⟩) :=
    (Finset.sum_coe_sort SS _).symm
  have hfst : (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = ((∑ s : ↥SS, Finset.univ.lcm e / e s : ℕ) : ℤ) := by
    rw [key, hsumW, hsumSS]
    exact neg_sum_eq_cast (fun s : ↥SS => s.1.1.ord (Rpd.R₁.residue ⟨c • f, hc⟩)) (fun s => Finset.univ.lcm e / e s) h3

  have hdisj : ∀ V, Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V :=
    fun V hF hS => hF.2 (by
      unfold JHPlaceSpecialization.Fixed
      rw [hF.1, ← hS.1])
  have hsplit : Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G + Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ G = G := by
    ext V
    simp only [JHPlaceSpecialization.fstDiv, JHPlaceSpecialization.sndDiv, Finsupp.add_apply, Finsupp.filter_apply]
    by_cases hF : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V
    · rw [if_pos hF, if_neg (hdisj V hF), add_zero]
    · rw [if_neg hF, zero_add]
      by_cases hS : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V
      · rw [if_pos hS]
      · rw [if_neg hS]
        by_contra hne
        have hVs : V ∈ G.support := Finsupp.mem_support_iff.mpr (Ne.symm hne)
        rcases h2 G hG V hVs with h | h
        · exact hF h
        · exact hS h
  have hdeg0 : (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree + (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ G).degree = 0 := by
    rw [← map_add, hsplit]
    exact hGdeg
  refine ⟨G, ⟨f, hf, hG⟩, h2 G hG, hfst, ?_⟩
  rw [← hfst]
  linarith

end S_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_isPrincipal_isGoodDiv_degree_fstDiv_eq_sum_lcm_div_of_annulus_of_verticalSlope (solution)
