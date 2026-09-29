-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevelOne.blowupChart_drinfeldFibre_levelAut_linkedScalars_inertia_of_decomposition_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart_inertia_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/0692f1e8-912a-542f-8823-113e9402cc57

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_mem_maximalIdeal_iff_mem_span_image_of_blowupChart_exceptionalValuation_of_isPrime_of_dvd
import Theorems.Thm_DrinfeldCurve_isDomain_coordRing_of_ne_one
import Theorems.Thm_IsDiscreteValuationRing_exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul
import Theorems.Thm_ValuationSubring_mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_centre_stable_of_coeffMap_ringEquiv_of_localCentre_stable_of_drinfeldChartWitness_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_levelAut_linkedScalars_inertia_of_decomposition_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart_inertia_of_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

namespace A5Asm

theorem isUnit_mk_iff {K : Type} [Field K] (W : ValuationSubring K) (x : K) (hx : x ∈ W) :
    IsUnit (⟨x, hx⟩ : ↥W) ↔ x ≠ 0 ∧ x⁻¹ ∈ W := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : ((u : ↥W) : K) * ((u⁻¹ : (↥W)ˣ) : ↥W) = 1 := by
      rw [← Subring.coe_mul]
      have := u.mul_inv
      rw [show ((u : ↥W) * ((u⁻¹ : (↥W)ˣ) : ↥W)) = 1 from this]
      rfl
    rw [hu] at h1
    have hx0 : x ≠ 0 := by
      intro h0; rw [show ((⟨x, hx⟩ : ↥W) : K) = x from rfl, h0, zero_mul] at h1; exact zero_ne_one h1
    refine ⟨hx0, ?_⟩
    have : x⁻¹ = ((u⁻¹ : (↥W)ˣ) : ↥W) := by
      rw [show ((⟨x, hx⟩ : ↥W) : K) = x from rfl] at h1
      exact (eq_inv_of_mul_eq_one_right h1).symm ▸ rfl
    rw [this]; exact SetLike.coe_mem _
  · rintro ⟨hx0, hinv⟩
    exact ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem mem_maximalIdeal_iff_of_forall_mem_iff {K F : Type} [Field K] [EquivLike F K K] [RingEquivClass F K K]
    (W : ValuationSubring K) (τ : F) (hτ : ∀ f : K, f ∈ W ↔ τ f ∈ W)
    (x : K) (hx : x ∈ W) (hτx : τ x ∈ W) :
    (⟨x, hx⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W ↔ (⟨τ x, hτx⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_mk_iff, isUnit_mk_iff, ← map_inv₀, ← hτ]
  have : x ≠ 0 ↔ τ x ≠ 0 := by rw [ne_eq, ne_eq, map_eq_zero_iff τ (EquivLike.injective τ)]
  rw [this]

@[reducible] noncomputable def algebraGaloisField (q : ℕ) [Fact q.Prime] (A : Type) [CommRing A] [IsLocalRing A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) :
    Algebra (GaloisField q 2) (IsLocalRing.ResidueField A) := by
  have hq : (q : IsLocalRing.ResidueField A) = 0 := by
    have : (q : IsLocalRing.ResidueField A) = IsLocalRing.residue A (q : A) := by simp
    rw [this, IsLocalRing.residue_eq_zero_iff]
    exact hAq
  haveI : CharP (IsLocalRing.ResidueField A) q := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hq
  letI : Algebra (ZMod q) (IsLocalRing.ResidueField A) := ZMod.algebra _ q
  exact (IsAlgClosed.lift : GaloisField q 2 →ₐ[ZMod q] IsLocalRing.ResidueField A).toRingHom.toAlgebra

end A5Asm

namespace A5Asm

theorem exists_zmod_of_pow_eq (q : ℕ) [Fact q.Prime] (x : GaloisField q 2) (hx : x ^ q = x) :
    ∃ d : ZMod q, algebraMap (ZMod q) (GaloisField q 2) d = x := by
  classical
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  set f : Polynomial (GaloisField q 2) := Polynomial.X ^ q - Polynomial.X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (GaloisField q 2) hq1
  have hdeg : f.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq (GaloisField q 2) hq1
  let S : Finset (GaloisField q 2) := Finset.univ.image (algebraMap (ZMod q) (GaloisField q 2))
  have hmemroot : ∀ z : GaloisField q 2, z ∈ f.roots.toFinset ↔ z ^ q = z := by
    intro z
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, sub_eq_zero]
  have hS : S ⊆ f.roots.toFinset := by
    intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
    rw [hmemroot, ← map_pow, ZMod.pow_card]
  have hcardS : S.card = q := by
    rw [Finset.card_image_of_injective _ (algebraMap (ZMod q) (GaloisField q 2)).injective, Finset.card_univ, ZMod.card]
  have hcardR : f.roots.toFinset.card ≤ q := by
    calc f.roots.toFinset.card ≤ f.roots.card := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ = q := hdeg
  have hEq : S = f.roots.toFinset := Finset.eq_of_subset_of_card_le hS (by rw [hcardS]; exact hcardR)
  have hxr : x ∈ f.roots.toFinset := (hmemroot x).mpr hx
  rw [← hEq] at hxr
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hxr
  exact ⟨a, ha⟩

theorem exists_units_zmod_eq_pow_succ (q : ℕ) [Fact q.Prime] (α : (GaloisField q 2)ˣ) :
    ∃ d : (ZMod q)ˣ, algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) := by
  classical
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  haveI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card q 2 two_ne_zero
  have hα0 : (α : GaloisField q 2) ≠ 0 := Units.ne_zero α
  have hpow : ((α : GaloisField q 2) ^ (q + 1)) ^ q = (α : GaloisField q 2) ^ (q + 1) := by
    have h1 : (α : GaloisField q 2) ^ (q ^ 2 - 1) = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one (α : GaloisField q 2) hα0
      rwa [hcard] at this
    have h2 : (q + 1) * q = (q ^ 2 - 1) + (q + 1) := by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [this]; ring
    rw [← pow_mul, h2, pow_add, h1, one_mul]
  obtain ⟨d, hd⟩ := exists_zmod_of_pow_eq q _ hpow
  have hd0 : d ≠ 0 := by
    rintro rfl; rw [map_zero] at hd; exact pow_ne_zero _ hα0 hd.symm
  exact ⟨Units.mk0 d hd0, by simpa using hd⟩

theorem apply_algebraMap_of_coeffMap {L : Type} [Field L] (K : IntermediateField L (LaurentSeries L))
    (σL : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L))
    (c : L) : τ (algebraMap L ↥K c) = algebraMap L ↥K (σL c) := by
  apply Subtype.ext
  rw [hτ]
  change ModularCurve.coeffMap σL.toRingHom (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) (σL c)
  exact ModularCurve.coeffMap_algebraMap σL.toRingHom c

theorem coeffMap_symm {L : Type} [Field L] (K : IntermediateField L (LaurentSeries L))
    (σL : L ≃+* L) (τ : ↥K ≃+* ↥K)
    (hτ : ∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L))
    (x : ↥K) : ((τ.symm x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.symm.toRingHom ((x : ↥K) : LaurentSeries L) := by
  have h := hτ (τ.symm x)
  rw [RingEquiv.apply_symm_apply] at h
  rw [h, ModularCurve.coeffMap_coeffMap]
  have : σL.symm.toRingHom.comp σL.toRingHom = RingHom.id L := by
    ext c; simp
  rw [ModularCurve.coeffMap_congr this, ModularCurve.coeffMap_id]

end A5Asm

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [HenselianLocalRing A] [IsAlgClosed (ResidueField A)]
    (hAq : (q : A) ∈ maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})

    (ϖt : A) (hϖt : ∃ u : A, IsUnit u ∧ ϖt ^ (q ^ 2 - 1) = (q : A) * u)

    (y : Ideal ↥(chartAlgFin A (↥K) j)) (hy : y.IsMaximal) (hϖy : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω), RingHom.ker φ = y → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (hArig : ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω),
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
        (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
        (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
        (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
        (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W, (a ∉ IsLocalRing.maximalIdeal W ∨ b ∉ IsLocalRing.maximalIdeal W) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (hArigI :
    ∀ (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
    (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y'.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
    (hσϖ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (e : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
      MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u}),

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
      let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ (ϖt ^ (q + 1))) * v - f * u})
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A, e (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) →

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
              ∃ (θ : S ≃+* S) (c : W) (M : Matrix (Fin 2) (Fin 2) W),

                (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                  θ (e (toC (germY a))) = e (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                    mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                  (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W) ∧
                (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W) ∈ IsLocalRing.maximalIdeal W) ∧
                (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W) ∧

                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W)) →

    ∀ (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A),
      (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →

      (∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A) →

      ∀ (π : A), π ^ (q ^ 2 - 1) = (q : A) → ∀ (αt : A), σA π = αt * π →
      αt ^ (q + 1) - (((d : ZMod q).val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A →
      ∀ τ : ↥K ≃+* ↥K,

        (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →

        (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
          τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧
        ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
            τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),

          (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            (((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal)) ∧

          ∃ (θ : S ≃+* S) (σW : W ≃+* W) (ct : W) (M : Matrix (Fin 2) (Fin 2) W),
            (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
              θ (e (toC (germY a))) = e (toC (germY ((τ.toRingHom.restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
              (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧
            (∀ a : A, σW (σ a) = σ (σA a)) ∧
            (∀ w : W, σW w - w ∈ IsLocalRing.maximalIdeal W) ∧
            (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C (σW w))) ∧
            (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
              (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧

            (ct - σ (αt ^ (q + 1)) ∈ IsLocalRing.maximalIdeal W) ∧
            (∀ ii jj : Fin 2, M ii jj -
                ct * (((((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
                    Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W) ∈ IsLocalRing.maximalIdeal W))

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
        (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
        (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        (y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
        (hy' : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y' = z)
        (hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y'.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)
    (hy'y : y'.asIdeal = y)
      (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
        [IsAdicComplete (IsLocalRing.maximalIdeal W₁) W₁] (σ₁ : A →+* W₁)
        (hσ₁ : IsLocalRing.maximalIdeal W₁ = Ideal.span {σ₁ ϖ})
        (f₁ u₁ v₁ : MvPowerSeries (Fin 2) W₁) (hu₁ : IsUnit u₁) (hv₁ : IsUnit v₁)
        (hf₁ : f₁ - DrinfeldCurve.LocalChart.drinfeldForm q W₁ ∈
          (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ (q + 2))
        (e₁ : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+*
          MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})

    (hW₁ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

        (∀ a : A, e₁ (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
              (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
            (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
          Ideal.Quotient.mk _ (MvPowerSeries.C (σ₁ a))) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
              τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' → ((γ 1 1 : ℤ) : ZMod ℓ) = 1 →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) ∧

        (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hpres : (∀ a : ↥K, a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →
                τ a ∈ (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)),
              (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) - a ∈ y'.asIdeal) →
                ∃ (θ : S ≃+* S) (c : W₁) (M : Matrix (Fin 2) (Fin 2) W₁),

                  (∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
                    θ (e₁ (toC (germY a))) = e₁ (toC (germY (((τ : ↥K →+* ↥K).restrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
                (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hpres) a)))) ∧

                  (∀ w : W₁, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧

                  (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
                      mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
                    (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
                  (c ^ (q + 1) - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (∀ ii jj : Fin 2, M ii jj - c * ((γ ii jj : ℤ) : W₁) ∈ IsLocalRing.maximalIdeal W₁) ∧
                  (((γ 1 1 : ℤ) : ZMod ℓ) = 1 → c - 1 ∈ IsLocalRing.maximalIdeal W₁) ∧

                  (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c - 1 ∉ IsLocalRing.maximalIdeal W₁)) ∧

        (∀ (a₁ b₁ a₂ b₂ : ℤ) (P₁ P₂ : Ideal S), P₁.IsPrime → P₂.IsPrime →

          (mkS (MvPowerSeries.X 0) ∉ P₁ ∨ mkS (MvPowerSeries.X 1) ∉ P₁) →
          (mkS (MvPowerSeries.X 0) ∉ P₂ ∨ mkS (MvPowerSeries.X 1) ∉ P₂) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₁ → mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P₂ →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₁ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₁ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₁) →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C ((a₂ : ℤ) : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C ((b₂ : ℤ) : W₁) * MvPowerSeries.X 1 + h)
                ∈ P₂) →
          ¬ ((q : ℤ) ∣ a₁ * b₂ - a₂ * b₁) →
            Ideal.comap ((e₁ : CMP →+* S).comp toC) P₁ ≠ Ideal.comap ((e₁ : CMP →+* S).comp toC) P₂) ∧

        (∀ P : Ideal S, P.IsPrime → (mkS (MvPowerSeries.X 0) ∉ P ∨ mkS (MvPowerSeries.X 1) ∉ P) →
          mkS (MvPowerSeries.C (σ₁ ϖ)) ∈ P →
          (∃ h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ 2,
              mkS (MvPowerSeries.C (1 : W₁) * MvPowerSeries.X 0 + MvPowerSeries.C (0 : W₁) * MvPowerSeries.X 1 + h) ∈ P) →
          ∀ a : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
            toC (germY a) ∈ Ideal.comap (e₁ : CMP →+* S) P ↔
              ∀ n : ℤ, ∃ m ∈ IsLocalRing.maximalIdeal A,
                (((a : ↥K) : LaurentSeries L).coeff n) = algebraMap A L m) ∧

        (∃ (hjK : ModularCurve.jqNModC L q ∈ K)
           (hjC : (⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
           (a₀ : A) (_ : (⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀ ∈ y'.asIdeal)
           (e₀ : ℕ) (_ : 1 ≤ e₀) (h : MvPowerSeries (Fin 2) W₁)
           (_ : h ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₁), MvPowerSeries.X 1}) ^ e₀),
           (∀ a b : W₁, (a ∉ IsLocalRing.maximalIdeal W₁ ∨ b ∉ IsLocalRing.maximalIdeal W₁) →
              a ^ q * b - a * b ^ q ∈ IsLocalRing.maximalIdeal W₁ →
              IsUnit (∑ i ∈ Finset.range (e₀ + 1),
                MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (e₀ - i)) h * a ^ i * b ^ (e₀ - i))) ∧
           (e₁ : CMP →+* S) (toC (germY ((⟨(⟨ModularCurve.jqNModC L q, hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) -
              algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) a₀))) = mkS h))

    (J : Ideal ↥(chartAlgFin A (↥K) j))
    (hJ :
        let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
        let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
        let toC : STK →+* CMP := algebraMap STK CMP
        let S := (MvPowerSeries (Fin 2) W₁ ⧸ Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let mkS : MvPowerSeries (Fin 2) W₁ →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ₁ (ϖt ^ (q + 1))) * v₁ - f₁ * u₁})
        let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
          ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
              ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y', trivial, hy'⟩).hom.comp
            ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
              (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
        J = sInf {J' : Ideal ↥(chartAlgFin A (↥K) j) | ∃ (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma q)
          (_ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
          (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ)
          (hpres : ∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j),
          J' = Ideal.comap ((τ : ↥K →+* ↥K).restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hpres)
            (Ideal.comap ((e₁ : CMP →+* S).comp (toC.comp germY))
              (Ideal.span {mkS (MvPowerSeries.C (σ₁ ϖt)), mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}))})

    (B : Subalgebra A ↥K)
    (hB : B = (Algebra.adjoin ↥(chartAlgFin A (↥K) j)
        {x : ↥K | ∃ i ∈ J, x * algebraMap A ↥K ϖt = ((i : ↥(chartAlgFin A (↥K) j)) : ↥K)}).restrictScalars A)

    (W : ValuationSubring ↥K) (hBW : ∀ f : ↥K, f ∈ B → f ∈ W)
    (hR1 :

      chartAlgFin A (↥K) j ≤ B ∧
      (∀ f : ↥K, ∃ g h : ↥B, (h : ↥K) ≠ 0 ∧ f * (h : ↥K) = (g : ↥K)))
    (hR2 :

      Algebra.FormallySmooth A ↥B ∧ Algebra.FinitePresentation A ↥B ∧
      Ring.KrullDimLE 1 (↥B ⧸ Ideal.span {algebraMap A ↥B ϖ}))
    (hR3 :

      (∀ x : L, algebraMap L ↥K x ∈ W ↔ ∃ a : A, algebraMap A L a = x) ∧
      maximalIdeal ↥W = Ideal.span {(⟨algebraMap A ↥K ϖ, hBW _ (B.algebraMap_mem ϖ)⟩ : ↥W)} ∧
      IsDiscreteValuationRing ↥W ∧
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ y ↔
        ∃ hb : (b : ↥K) ∈ W, (⟨(b : ↥K), hb⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
      (∀ f : ↥K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : ↥K), hBW _ h.2⟩ : ↥W) ∉ maximalIdeal ↥W ∧ f * (h : ↥K) = (g : ↥K)))
    (hEQ :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1))) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          ∀ f : ↥K, f ∈ B → τ f ∈ B) ∧
      (∀ Q : Ideal ↥B, Q.IsPrime → algebraMap A ↥B ϖ ∈ Q →
        ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
          ∃ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ ∧
            ∀ b : ↥B, (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W → τ (b : ↥K) ∈ B ∧ ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hb⟩ : ↥B) ∈ Q) ∧
      (∀ b : ↥B, (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            ∀ hb : τ (b : ↥K) ∈ B, (⟨τ (b : ↥K), hBW _ hb⟩ : ↥W) ∈ maximalIdeal ↥W) →
        algebraMap A ↥B ϖ ∣ b) ∧

      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
          (∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
              b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y) →
          ∀ f : ↥K, f ∈ W ↔ τ f ∈ W)) :

      (∀ (inst : Algebra (GaloisField q 2) (ResidueField A)),
        ∃ (ρ : ↥B →+* DrinfeldCurve.CoordRing q (ResidueField A)),
          Function.Surjective ρ ∧
          (∀ b : ↥B, ρ b = 0 ↔ (⟨(b : ↥K), hBW _ b.2⟩ : ↥W) ∈ maximalIdeal ↥W) ∧
          (∀ a : A, ρ (algebraMap A ↥B a) = algebraMap (ResidueField A) (DrinfeldCurve.CoordRing q (ResidueField A)) (residue A a)) ∧
          (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
            ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
              (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
              ∃ (c : (GaloisField q 2)ˣ) (hmem : (ModularCurve.FullLevel.redQ q γ, c) ∈ DrinfeldCurve.hSubgroup q),
                (∀ (b : ↥B) (hb : τ (b : ↥K) ∈ B), ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b)) ∧
                (γ ∈ CongruenceSubgroup.Gamma q → (¬ ∀ k : ↥K, τ k = k) → c ≠ 1) ∧

                (∃ (γ' : SL(2, ℤ)) (_ : γ' ∈ CongruenceSubgroup.Gamma q) (_ : γ' ∈ CongruenceSubgroup.Gamma0 M') (τ' : ↥K ≃ₐ[L] ↥K)
                    (_ : ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ'⁻¹ K τ') (_ : ∀ f : ↥K, f ∈ W ↔ τ' f ∈ W)
                    (hmem' : ((1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)), c) ∈ DrinfeldCurve.hSubgroup q),
                  ∀ (b : ↥B) (hb : τ' (b : ↥K) ∈ B), ρ ⟨τ' (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem'⟩ (ρ b))) ∧

          (∃ η : ℕ, (η = 1 ∨ η = q) ∧ ∀ (π : A), π ^ (q ^ 2 - 1) = (q : A) →
            ∀ (σL : L ≃+* L) (σA : A ≃+* A), (∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a)) →
              (∀ a : A, σA a - a ∈ maximalIdeal A) →
              ∀ (αt : A), σA π = αt * π →
              ∀ (α : (GaloisField q 2)ˣ), algebraMap (GaloisField q 2) (ResidueField A) (α : GaloisField q 2) = residue A αt →
              ∀ τ : ↥K ≃+* ↥K,
                (∀ x : ↥K, ((τ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL.toRingHom ((x : ↥K) : LaurentSeries L)) →
                (∀ f : ↥K, f ∈ B → τ f ∈ B) ∧ (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) ∧
                ∀ (d : (ZMod q)ˣ), algebraMap (ZMod q) (GaloisField q 2) (d : ZMod q) = (α : GaloisField q 2) ^ (q + 1) →
                  ∀ (hmem : (ModularCurve.FullLevel.diagOneElem q (d ^ η)⁻¹, α ^ η) ∈ DrinfeldCurve.hSubgroup q)
                    (b : ↥B) (hb : τ (b : ↥K) ∈ B),
                    ρ ⟨τ (b : ↥K), hb⟩ = DrinfeldCurve.hAction q (ResidueField A) ⟨_, hmem⟩ (ρ b))) := by
  classical

  have hW := hW₁
  obtain ⟨hconstW, hfin, -, hlinW, -, -, -⟩ := hW

  have hK2 := ModularCurve.FullLevel.AuxLevelOne.comap_eq_and_dense_and_flat_drinfeldChartWitness_chartAlgFin_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hconstW

  have hK1 := ModularCurve.FullLevel.AuxLevelOne.blowupChart_centre_levelAut_stable_of_eq_adjoin_of_drinfeldChartWitness_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
  have hK1i := hK1.1
  have hK1iii := hK1.2.2

  have hK3 := ModularCurve.FullLevel.AuxLevelOne.map_orbitCentre_eq_span_drinfeldChartWitness_of_stabilizes_of_dense_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ hK1i hK2.1 hK2.2.1 hK2.2.2.2.1 ⟨hK2.2.2.2.2.2.2.1, hK2.2.2.2.2.2.2.2.1⟩

  let instκ : Algebra (GaloisField q 2) (ResidueField A) := A5Asm.algebraGaloisField q A hAq
  haveI hdom : IsDomain (DrinfeldCurve.CoordRing q (ResidueField A)) :=
    DrinfeldCurve.isDomain_coordRing_of_ne_one q (Nat.Prime.one_lt (Fact.out : q.Prime)).ne' (ResidueField A)

  have hK4₀ := ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ J B hB hR1.1 hK2 hK3 instκ
  obtain ⟨Φ₀, hιR₀, hx₀₀, hx₁₀, hΦR₀, tW₀, cR₀, ρR₀, ρ₀, -, -, -, -, -, -, -, -, -, hsurj₀, hker₀, -⟩ := hK4₀
  have hprime : (Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j)))).IsPrime := by
    have hk : RingHom.ker ρ₀ = Ideal.span ((fun c : ↥(chartAlgFin A (↥K) j) => (⟨(c : ↥K), hR1.1 c.2⟩ : ↥B)) '' (y : Set ↥(chartAlgFin A (↥K) j))) := by
      ext b; rw [RingHom.mem_ker]; exact hker₀ b
    rw [← hk]; exact RingHom.ker_isPrime ρ₀
  have hK6 := ModularCurve.FullLevel.AuxLevelOne.mem_maximalIdeal_iff_mem_span_image_of_blowupChart_exceptionalValuation_of_isPrime_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss J B hB W hBW hR1 hR2 hR3 hprime
  obtain ⟨hPid, hleast⟩ := hK6

  have hfix_of_W : ∀ τ : ↥K ≃ₐ[L] ↥K, (∀ a : ↥K, a ∈ chartAlgFin A (↥K) j → τ a ∈ chartAlgFin A (↥K) j) →
      (∀ f : ↥K, f ∈ W ↔ τ f ∈ W) →
      ∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
        b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y := by
    intro τ hpres hWτ b hb
    have hcen := hR3.2.2.2.1
    rw [hcen b, hcen ⟨τ (b : ↥K), hb⟩]
    constructor
    · rintro ⟨hbW, hbm⟩
      refine ⟨(hWτ _).mp hbW, ?_⟩
      exact (A5Asm.mem_maximalIdeal_iff_of_forall_mem_iff W τ hWτ (b : ↥K) hbW ((hWτ _).mp hbW)).mp hbm
    · rintro ⟨hbW, hbm⟩
      have hbW' : (b : ↥K) ∈ W := (hWτ _).mpr hbW
      exact ⟨hbW', (A5Asm.mem_maximalIdeal_iff_of_forall_mem_iff W τ hWτ (b : ↥K) hbW' hbW).mpr hbm⟩

  intro inst
  have hK4 := ModularCurve.FullLevel.AuxLevelOne.exists_blowupChart_ringHom_localBlowupChart_surjective_ker_eq_span_of_dense_of_flat_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ J B hB hR1.1 hK2 hK3 inst
  obtain ⟨Φ, hιR, hx₀, hx₁, hΦR, tW, cR, ρR, ρ, hΦC, hΦJ, htW1, htW2, hcR, hρRS, hρRx0, hρRx1, hρΦ, hsurj, hker, hconstρ⟩ := hK4
  have hK5 := ModularCurve.FullLevel.AuxLevelOne.blowupChart_drinfeldFibre_hAction_of_isLevelAutAt_of_fibrePackage_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB hR1.1 hK1 hK2 hK3 inst Φ hιR hx₀ hx₁ hΦR tW cR ρR ρ hΦC hΦJ htW1 htW2 hcR hρRS hρRx0 hρRx1 hρΦ
  obtain ⟨hmain, -⟩ := hK5
  refine ⟨ρ, hsurj, fun b => (hker b).trans (hPid b).symm, hconstρ, ?_, ?_⟩
  ·
    intro γ hγ τ hτ hWτ
    have hfixy := hfix_of_W τ (hfin γ hγ τ hτ) hWτ
    obtain ⟨c, hmem, hequiv, hfaith, hlinked⟩ := hmain γ hγ τ hτ hfixy
    obtain ⟨γ', hγ'q, hγ'0, τ', hτ', hfix', hmem', hequiv'⟩ := hlinked
    have hR5d := hEQ.2.2.2.2
    exact ⟨c, hmem, hequiv, hfaith, γ', hγ'q, hγ'0, τ', hτ', hR5d γ' hγ'0 τ' hτ' hfix', hmem', hequiv'⟩
  ·
    refine ⟨q, Or.inr rfl, ?_⟩
    intro π hπ σL σA hcompat hinert αt hαt α hα τ hτ

    have hq0 : (q : A) ≠ 0 := by
      intro h
      have h1 : (q : L) = 0 := by rw [← map_natCast (algebraMap A L), h, map_zero]
      exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) h1
    have hn1 : 1 ≤ q ^ 2 - 1 := by
      have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    have hres_ne : residue A αt ≠ 0 := by
      rw [← hα]
      exact (map_ne_zero_iff _ (algebraMap (GaloisField q 2) (ResidueField A)).injective).mpr (Units.ne_zero α)
    have hαt_unit : IsUnit αt := by
      by_contra h
      exact hres_ne ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
    set u : Aˣ := hαt_unit.unit with hu_def
    have hu : (u : A) = αt := hαt_unit.unit_spec
    have hres_inert : ∀ (σ : A ≃+* A), (∀ a : A, σ a - a ∈ maximalIdeal A) → ∀ x : A, residue A (σ x) = residue A x := by
      intro σ hσ x
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact hσ x

    have hunit1 : ∀ m : A, m ∈ maximalIdeal A → IsUnit (1 + m) := by
      intro m hm
      have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-m)
        ((IsLocalRing.mem_maximalIdeal _).mp (Submodule.neg_mem _ hm))
      simpa using this

    have mkcong : ∀ (β : (GaloisField q 2)ˣ) (dd : (ZMod q)ˣ) (a : A),
        algebraMap (GaloisField q 2) (ResidueField A) (β : GaloisField q 2) = residue A a →
        algebraMap (ZMod q) (GaloisField q 2) (dd : ZMod q) = (β : GaloisField q 2) ^ (q + 1) →
        a ^ (q + 1) - (((dd : ZMod q).val : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
      intro β dd a hβ hdd
      have hval : algebraMap (ZMod q) (GaloisField q 2) (dd : ZMod q) = (((dd : ZMod q).val : ℕ) : GaloisField q 2) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val (dd : ZMod q)]
        rw [map_natCast]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_natCast, ← hβ, ← map_pow, ← hdd, hval, map_natCast,
        sub_self]
    obtain ⟨d₀, hd₀⟩ := A5Asm.exists_units_zmod_eq_pow_succ q α
    have hcong := mkcong α d₀ αt hα hd₀

    have hcompat' : ∀ a : A, algebraMap A L (σA.symm a) = σL.symm (algebraMap A L a) := by
      intro a
      have h := hcompat (σA.symm a)
      rw [RingEquiv.apply_symm_apply] at h
      rw [h, RingEquiv.symm_apply_apply]
    have hinert' : ∀ a : A, σA.symm a - a ∈ maximalIdeal A := by
      intro a
      have h := hinert (σA.symm a)
      rw [RingEquiv.apply_symm_apply] at h
      rw [← neg_sub]
      exact Submodule.neg_mem _ h
    have hαt' : σA.symm π = σA.symm ((u⁻¹ : Aˣ) : A) * π := by
      have h1 : π = σA.symm αt * σA.symm π := by
        conv_lhs => rw [← σA.symm_apply_apply π]
        rw [hαt, map_mul]
      calc σA.symm π = σA.symm (((u⁻¹ : Aˣ) : A) * (u : A)) * σA.symm π := by simp
        _ = σA.symm ((u⁻¹ : Aˣ) : A) * (σA.symm αt * σA.symm π) := by rw [map_mul, mul_assoc, hu]
        _ = σA.symm ((u⁻¹ : Aˣ) : A) * π := by rw [← h1]
    have hα' : algebraMap (GaloisField q 2) (ResidueField A) ((α⁻¹ : (GaloisField q 2)ˣ) : GaloisField q 2) =
        residue A (σA.symm ((u⁻¹ : Aˣ) : A)) := by
      have hinv : residue A ((u⁻¹ : Aˣ) : A) = (residue A (u : A))⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, Units.inv_mul, map_one]
      rw [hres_inert σA.symm hinert', hinv, hu, ← hα, Units.val_inv_eq_inv_val, map_inv₀]
    have hd₀' : algebraMap (ZMod q) (GaloisField q 2) ((d₀⁻¹ : (ZMod q)ˣ) : ZMod q) =
        ((α⁻¹ : (GaloisField q 2)ˣ) : GaloisField q 2) ^ (q + 1) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hd₀, Units.val_inv_eq_inv_val, inv_pow]
    have hcong' := mkcong α⁻¹ d₀⁻¹ (σA.symm ((u⁻¹ : Aˣ) : A)) hα' hd₀'
    have hτ' := A5Asm.coeffMap_symm K σL τ hτ

    have HI := hArigI z ϖz hϖz hz y' hy' hss' W₁ inferInstance inferInstance inferInstance inferInstance σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁
      hconstW hlinW d₀ σL σA hcompat hinert π hπ αt hαt hcong τ hτ
    obtain ⟨hτC, HI2⟩ := HI
    obtain ⟨hτfix, θ, σW, ct, Mx, hθΨ, hσWσ, hσWid, hθC, hθlin, hct, hM⟩ := HI2 hτC
    have HI' := hArigI z ϖz hϖz hz y' hy' hss' W₁ inferInstance inferInstance inferInstance inferInstance σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁
      hconstW hlinW d₀⁻¹ σL.symm σA.symm hcompat' hinert' π hπ (σA.symm ((u⁻¹ : Aˣ) : A)) hαt' hcong' τ.symm hτ'
    obtain ⟨hτC', HI2'⟩ := HI'
    obtain ⟨hτfix', θ', σW', ct', Mx', hθΨ', hσWσ', hσWid', hθC', hθlin', -, -⟩ := HI2' hτC'

    obtain ⟨m, hm, hσAϖt⟩ := IsDiscreteValuationRing.exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul A σA hinert (q ^ 2 - 1) hn1 (q : A) hq0 π hπ ϖt hϖt αt hαt
    obtain ⟨m', hm', hσAϖt'⟩ := IsDiscreteValuationRing.exists_mem_maximalIdeal_map_eq_mul_mul_one_add_of_pow_eq_of_pow_eq_mul A σA.symm hinert' (q ^ 2 - 1) hn1 (q : A) hq0 π hπ ϖt hϖt _ hαt'

    have hτconst : ∀ (σL₀ : L ≃+* L) (σA₀ : A ≃+* A) (τ₀ : ↥K ≃+* ↥K),
        (∀ a : A, algebraMap A L (σA₀ a) = σL₀ (algebraMap A L a)) →
        (∀ x : ↥K, ((τ₀ x : ↥K) : LaurentSeries L) = ModularCurve.coeffMap σL₀.toRingHom ((x : ↥K) : LaurentSeries L)) →
        ∀ a : A, τ₀ (algebraMap A ↥K a) = algebraMap A ↥K (σA₀ a) := by
      intro σL₀ σA₀ τ₀ hc₀ hτ₀ a
      rw [IsScalarTower.algebraMap_apply A L ↥K a, A5Asm.apply_algebraMap_of_coeffMap K σL₀ τ₀ hτ₀, ← hc₀,
        ← IsScalarTower.algebraMap_apply]

    have HC := ModularCurve.FullLevel.AuxLevelOne.blowupChart_centre_stable_of_coeffMap_ringEquiv_of_localCentre_stable_of_drinfeldChartWitness_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB
    have hσ₁σA : ∀ (σA₀ : A ≃+* A) (σW₀ : W₁ ≃+* W₁) (a₀ m₀ : A), (∀ a : A, σW₀ (σ₁ a) = σ₁ (σA₀ a)) →
        σA₀ ϖt = a₀ * ϖt * (1 + m₀) → σW₀ (σ₁ ϖt) = σ₁ (a₀ * (1 + m₀)) * σ₁ ϖt := by
      intro σA₀ σW₀ a₀ m₀ h1 h2
      rw [h1, h2, ← map_mul]; congr 1; ring
    have hτB : ∀ f : ↥K, f ∈ B → τ f ∈ B :=
      (HC σL τ hτ hτC (by intro a ha; exact hτC' a ha)
        ⟨αt * (1 + m), hαt_unit.mul (hunit1 m hm), by rw [hτconst σL σA τ hcompat hτ, hσAϖt]; congr 1; ring⟩
        ⟨θ, σW, Mx, hθΨ, hθC, ⟨σ₁ (αt * (1 + m)), (hαt_unit.mul (hunit1 m hm)).map σ₁, hσ₁σA σA σW αt m hσWσ hσAϖt⟩, hθlin⟩).2
    have hτB' : ∀ f : ↥K, f ∈ B → τ.symm f ∈ B :=
      (HC σL.symm τ.symm hτ' hτC' (by intro a ha; simpa using hτC a ha)
        ⟨σA.symm ((u⁻¹ : Aˣ) : A) * (1 + m'), ((u⁻¹).isUnit.map σA.symm).mul (hunit1 m' hm'),
          by rw [hτconst σL.symm σA.symm τ.symm hcompat' hτ', hσAϖt']; congr 1; ring⟩
        ⟨θ', σW', Mx', hθΨ', hθC', ⟨σ₁ (σA.symm ((u⁻¹ : Aˣ) : A) * (1 + m')),
          (((u⁻¹).isUnit.map σA.symm).mul (hunit1 m' hm')).map σ₁, hσ₁σA σA.symm σW' _ m' hσWσ' hσAϖt'⟩, hθlin'⟩).2

    have hyfix : ∀ (b : ↥(chartAlgFin A (↥K) j)) (hb : τ (b : ↥K) ∈ chartAlgFin A (↥K) j),
        b ∈ y ↔ (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) ∈ y := by
      intro b hb
      have h := hτfix b
      rw [hy'y] at h

      have hb' : (⟨τ (b : ↥K), hb⟩ : ↥(chartAlgFin A (↥K) j)) =
          (τ.toRingHom.restrict (chartAlgFin A (↥K) j) (chartAlgFin A (↥K) j) hτC) b := rfl
      rw [hb']
      constructor
      · intro hby; simpa using y.add_mem h hby
      · intro hτby; simpa using y.sub_mem hτby h
    have hτW : ∀ f : ↥K, f ∈ W ↔ τ f ∈ W :=
      ValuationSubring.mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime (chartAlgFin A (↥K) j) B hR1.1 W hBW y ϖ hϖy
        hR3.2.2.2.2 hR3.2.2.2.1 hleast τ hτC (by intro a ha; exact hτC' a ha) hτB hτB' hyfix
    refine ⟨hτB, hτW, ?_⟩

    intro d hd hmem b hb

    have hdd : d = d₀ := by
      apply Units.ext
      exact (algebraMap (ZMod q) (GaloisField q 2)).injective (hd.trans hd₀.symm)
    subst hdd
    have hmσ₁ : σ₁ m ∈ IsLocalRing.maximalIdeal W₁ := by
      have := hK2.2.2.2.2.2.1

      rw [← this] at hm
      exact hm
    have hσWϖt : σW (σ₁ ϖt) = σ₁ αt * σ₁ ϖt * (1 + σ₁ m) := by
      rw [hσWσ, hσAϖt, map_mul, map_mul, map_add, map_one]

    have htWct : tW ct = algebraMap (GaloisField q 2) (ResidueField A) ((α : GaloisField q 2) ^ (q + 1)) := by
      have h1 : tW (ct - σ₁ (αt ^ (q + 1))) = 0 := htW2 _ hct
      rw [map_sub, sub_eq_zero] at h1
      rw [h1, htW1, map_pow, ← hα, map_pow]
    have hres : ∀ ii jj : Fin 2, tW (Mx ii jj) =
        tW (σ₁ αt) * algebraMap (GaloisField q 2) (ResidueField A) (((α ^ q : (GaloisField q 2)ˣ)) : GaloisField q 2) *
          ((((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) :
              Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ResidueField A) := by
      intro ii jj
      have h1 : tW (Mx ii jj - ct * (((((ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹ : CuspidalType.GL2 q) :
          Matrix (Fin 2) (Fin 2) (ZMod q)) ii jj).val : ℕ) : W₁)) = 0 := htW2 _ (hM ii jj)
      rw [map_sub, sub_eq_zero, map_mul, map_natCast] at h1
      rw [h1, htWct, htW1, ← hα, Units.val_pow_eq_pow_val, map_pow, map_pow, ← pow_succ']
    exact ModularCurve.FullLevel.AuxLevelOne.blowupChart_drinfeldFibre_hAction_of_semilinear_chartAut_of_fibrePackage_of_dvd q M' hqM' ℓ hℓ12 hℓM' L ζ hζ hι H₁ hH₁ K hK A hAq hζA j hj ϖ hϖ ϖt hϖt y hy hϖy hss z ϖz hϖz hz y' hy' hss' hy'y W₁ σ₁ hσ₁ f₁ u₁ v₁ hu₁ hv₁ hf₁ e₁ hW₁ J hJ B hB hR1.1 hK2 hK3 inst Φ hιR hx₀ hx₁ hΦR tW cR ρR ρ hΦC hΦJ htW1 htW2 hcR hρRS hρRx0 hρRx1 hρΦ
      τ hτC hτB θ σW (σ₁ αt) (σ₁ m) Mx (ModularCurve.FullLevel.diagOneElem q (d ^ q)⁻¹) (α ^ q) hmem
      hθΨ hθC hσWid (hαt_unit.map σ₁) hmσ₁ hσWϖt hθlin hres b hb

end S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_levelAut_linkedScalars_inertia_of_decomposition_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart_inertia_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevelOne_blowupChart_drinfeldFibre_levelAut_linkedScalars_inertia_of_decomposition_of_eq_adjoin_of_drinfeldChartWitness_of_stalk_drinfeldChart_inertia_of_dvd (solution)
