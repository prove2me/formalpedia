-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/bfa901cd-4c9e-5c15-92c4-1e570371ac52

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic
import Theorems.Thm_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_coe_lt_one_of_maximalIdeal_eq_span
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_forall_evalAt_eq_of_reduceFst_eq
import Theorems.Thm_ModularCurve_UVCrossingModel_moduleFinite_quotient_of_not_le_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finrank_quotient_of_forall_ker_eq
import Theorems.Thm_Algebra_algebraMap_norm_eq_prod_apply_of_card_eq_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
set_option autoImplicit false

universe u

p2m_open "AlgebraicCurve IsLocalRing P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq.IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq.ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces NodeLocalized.coeffSubring NodeLocalized.fieldOver uvCrossingIdeal UVCrossingModel PlaceSpecialization.ProlongationTuple.valuation_coe_lt_one_of_maximalIdeal_eq_span"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const mk_surjective S moduleFinite_quotient_of_not_le_span_pair maximalIdeal_eq_map_maximalIdeal_sup_span_pair"
p2m_open "ModularCurve.UVCrossingModel ModularCurve"

variable {W : Type u} [CommRing W]

noncomputable def axisFun (π : W) (j : Fin 2) : Fin 2 → MvPowerSeries Unit (W ⧸ Ideal.span {π}) :=
  fun i => if i = j then MvPowerSeries.X () else 0

theorem hasSubst_axisFun (π : W) (j : Fin 2) : MvPowerSeries.HasSubst (axisFun π j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    unfold axisFun
    split_ifs <;> simp)

noncomputable def axisHomAmbient (π : W) (j : Fin 2) :
    MvPowerSeries (Fin 2) W →ₐ[W] MvPowerSeries Unit (W ⧸ Ideal.span {π}) :=
  MvPowerSeries.substAlgHom (hasSubst_axisFun π j)

theorem axisHomAmbient_X (π : W) (j i : Fin 2) :
    axisHomAmbient π j (MvPowerSeries.X i) = axisFun π j i := by
  rw [axisHomAmbient, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X (hasSubst_axisFun π j)]

theorem axisHomAmbient_C (π : W) (j : Fin 2) (w : W) :
    axisHomAmbient π j (MvPowerSeries.C w) = MvPowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by
  rw [show (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = algebraMap W _ w from rfl, AlgHom.commutes,
    MvPowerSeries.algebraMap_apply]
  rfl

theorem axisHomAmbient_rel (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) :
    axisHomAmbient π j (MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C θ) = 0 := by
  rw [map_sub, map_mul, axisHomAmbient_X, axisHomAmbient_X, axisHomAmbient_C,
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hdiv), map_zero, sub_zero]
  unfold axisFun
  fin_cases j <;> simp

noncomputable def axisHom (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) :
    UVCrossingModel W θ →+* MvPowerSeries Unit (W ⧸ Ideal.span {π}) :=
  Ideal.Quotient.lift (uvCrossingIdeal W θ) (axisHomAmbient π j).toRingHom (fun a ha => by
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, axisHomAmbient_rel θ π hdiv j, mul_zero])

theorem axisHom_mk (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) (F : MvPowerSeries (Fin 2) W) :
    axisHom θ π hdiv j (mk θ F) = axisHomAmbient π j F :=
  Ideal.Quotient.lift_mk _ _ _

theorem axisHom_U (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) : axisHom θ π hdiv j (U θ) = axisFun π j 0 := by
  rw [U, axisHom_mk, axisHomAmbient_X]

theorem axisHom_V (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) : axisHom θ π hdiv j (V θ) = axisFun π j 1 := by
  rw [V, axisHom_mk, axisHomAmbient_X]

theorem axisHom_const (θ π : W) (hdiv : π ∣ θ) (j : Fin 2) (w : W) :
    axisHom θ π hdiv j (const θ w) = MvPowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) w) := by
  rw [const, axisHom_mk, axisHomAmbient_C]

theorem exists_isPrime_U_mem_const_mem_V_notMem (θ π : W) (hdiv : π ∣ θ) [IsDomain (W ⧸ Ideal.span {π})] :
    ∃ P : Ideal (UVCrossingModel W θ), P.IsPrime ∧ U θ ∈ P ∧ const θ π ∈ P ∧ V θ ∉ P := by
  refine ⟨RingHom.ker (axisHom θ π hdiv 1), RingHom.ker_isPrime _, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, axisHom_U]; simp [axisFun]
  · rw [RingHom.mem_ker, axisHom_const, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π), map_zero]
  · rw [RingHom.mem_ker, axisHom_V]
    simp only [axisFun, if_true]
    intro h
    have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single () 1)) h
    rw [MvPowerSeries.coeff_X, map_zero, if_pos rfl] at h1
    exact one_ne_zero h1

theorem exists_isPrime_V_mem_const_mem_U_notMem (θ π : W) (hdiv : π ∣ θ) [IsDomain (W ⧸ Ideal.span {π})] :
    ∃ P : Ideal (UVCrossingModel W θ), P.IsPrime ∧ V θ ∈ P ∧ const θ π ∈ P ∧ U θ ∉ P := by
  refine ⟨RingHom.ker (axisHom θ π hdiv 0), RingHom.ker_isPrime _, ?_, ?_, ?_⟩
  · rw [RingHom.mem_ker, axisHom_V]; simp [axisFun]
  · rw [RingHom.mem_ker, axisHom_const, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self π), map_zero]
  · rw [RingHom.mem_ker, axisHom_U]
    simp only [axisFun, if_true]
    intro h
    have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single () 1)) h
    rw [MvPowerSeries.coeff_X, map_zero, if_pos rfl] at h1
    exact one_ne_zero h1

end ModularCurve.UVCrossingModel

namespace IsLocalRing p2m_export "IsLocalRing" "of_surjective maximalIdeal mem_maximalIdeal of_surjective'" end IsLocalRing
p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.not_map_le_of_forall_lt_eq_bot
    {B R : Type*} [CommRing B] [IsLocalRing B] [CommRing R] [IsLocalRing R]
    (φ : B →+* R) (hmR : (maximalIdeal B).map φ = maximalIdeal R)
    (hht : ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (𝔮 : Ideal B) [𝔮.IsPrime] (h𝔮0 : 𝔮 ≠ ⊥)
    (P : Ideal R) [P.IsPrime] (hP : ¬ maximalIdeal R ≤ P)
    (b : B) (hbP : φ b ∈ P) (hb𝔮 : b ∉ 𝔮) :
    ¬ 𝔮.map φ ≤ P := by
  intro hle
  set 𝔭₁ : Ideal B := P.comap φ with h𝔭₁
  haveI : 𝔭₁.IsPrime := Ideal.IsPrime.comap φ
  have h1 : 𝔮 ≤ 𝔭₁ := by rw [h𝔭₁, ← Ideal.map_le_iff_le_comap]; exact hle
  have h2 : 𝔮 < 𝔭₁ := lt_of_le_of_ne h1 (fun h => hb𝔮 (h ▸ (show b ∈ 𝔭₁ from hbP)))
  have h3 : 𝔭₁ ≠ maximalIdeal B := by
    intro h
    apply hP
    rw [← hmR, Ideal.map_le_iff_le_comap, ← h]
  exact h𝔮0 (hht 𝔮 𝔭₁ inferInstance inferInstance h3 h2)

namespace RingEquiv p2m_export "RingEquiv" "symm_apply_apply mk coe_toRingHom toRingHom toRingHom_eq_coe finite ext apply_symm_apply symm_apply_eq" end RingEquiv
p2m_open_scoped "RingEquiv" in

theorem RingEquiv.map_maximalIdeal_eq {S T : Type*} [CommRing S] [IsLocalRing S] [CommRing T] [IsLocalRing T]
    (e : S ≃+* T) : (maximalIdeal S).map e.toRingHom = maximalIdeal T := by
  ext t
  rw [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff]
  exact (isUnit_map_iff e.symm t).not

p2m_open_scoped "IsLocalRing" in

theorem IsLocalRing.map_maximalIdeal_comp_adicCompletion_eq
    {B : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {R : Type*} [CommRing R] [IsLocalRing R]
    (ι : AdicCompletion (maximalIdeal B) B ≃+* R) :
    (maximalIdeal B).map (ι.toRingHom.comp (algebraMap B (AdicCompletion (maximalIdeal B) B))) = maximalIdeal R := by
  rw [← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map, RingEquiv.map_maximalIdeal_eq]

namespace BranchKer

p2m_open "IsLocalRing P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq.IsLocalRing IsDiscreteValuationRing"

variable {Ô : Type u} [CommRing Ô] [IsDomain Ô] [IsDiscreteValuationRing Ô]
variable {C : Type*} [Field C] [Algebra Ô C]
variable {S : Type u} [CommRing S] [Algebra Ô S]

theorem algebraMap_eq_zero_imp {ϖ : Ô} (hϖ : Irreducible ϖ) (hCϖ : algebraMap Ô C ϖ ≠ 0) {a : Ô}
    (ha : algebraMap Ô C a = 0) : a = 0 := by
  by_contra ha0
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha0 hϖ
  rw [map_mul, map_pow, mul_eq_zero] at ha
  rcases ha with hu | hp
  · exact (u.isUnit.map (algebraMap Ô C)).ne_zero hu
  · exact hCϖ (pow_eq_zero_iff'.mp hp).1

theorem comap_ker_eq_bot {ϖ : Ô} (hϖ : Irreducible ϖ) (hCϖ : algebraMap Ô C ϖ ≠ 0) (φ : S →ₐ[Ô] C) :
    (RingHom.ker φ.toRingHom).comap (algebraMap Ô S) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes] at ha
  rw [Ideal.mem_bot]
  exact algebraMap_eq_zero_imp hϖ hCϖ ha

theorem algebraMap_quotient_ker_injective {ϖ : Ô} (hϖ : Irreducible ϖ) (hCϖ : algebraMap Ô C ϖ ≠ 0)
    (φ : S →ₐ[Ô] C) : Function.Injective (algebraMap Ô (S ⧸ RingHom.ker φ.toRingHom)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [IsScalarTower.algebraMap_apply Ô S (S ⧸ RingHom.ker φ.toRingHom), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem] at ha
  have : a ∈ (RingHom.ker φ.toRingHom).comap (algebraMap Ô S) := ha
  rwa [comap_ker_eq_bot hϖ hCϖ φ, Ideal.mem_bot] at this

theorem ker_mem_minimalPrimes [Module.Finite Ô S] {ϖ : Ô} (hϖ : Irreducible ϖ) (hCϖ : algebraMap Ô C ϖ ≠ 0)
    (φ : S →ₐ[Ô] C) : RingHom.ker φ.toRingHom ∈ minimalPrimes S := by
  set P := RingHom.ker φ.toRingHom with hP
  haveI hPp : P.IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨hPp, bot_le⟩, ?_⟩
  rintro q ⟨hq, -⟩ hqP
  haveI := hq

  have hPq : (P.map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hcomap : (P.map (Ideal.Quotient.mk q)).comap (algebraMap Ô (S ⧸ q)) = ⊥ := by
    rw [IsScalarTower.algebraMap_eq Ô S (S ⧸ q), Ideal.Quotient.algebraMap_eq, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hqP]
    exact comap_ker_eq_bot hϖ hCϖ φ
  have h0 : P.map (Ideal.Quotient.mk q) = ⊥ := Ideal.eq_bot_of_comap_eq_bot hcomap
  intro s hs
  have : Ideal.Quotient.mk q s ∈ P.map (Ideal.Quotient.mk q) := Ideal.mem_map_of_mem _ hs
  rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

omit [IsDomain Ô] [IsDiscreteValuationRing Ô] [Algebra Ô S] in

theorem minimalPrimes_eq_image_comap_mk (J : Ideal S) :
    J.minimalPrimes = Ideal.comap (Ideal.Quotient.mk J) '' minimalPrimes (S ⧸ J) := by
  have h := Ideal.comap_minimalPrimes_eq_of_surjective (Ideal.Quotient.mk_surjective (I := J)) ⊥
  rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at h

end BranchKer

section Generic
set_option maxHeartbeats 1600000
p2m_open "AdicCompletion P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq.AdicCompletion Valued"

namespace AdicCompletion
p2m_export "AdicCompletion" "map eval mk eval_of of mk_surjective map_zero ext algebraMap_apply lift pow_smul_top_eq_ker_eval mkₐ of_surjective maximalIdeal_eq_map"
namespace ValuedLift
p2m_open "AdicCompletion"

theorem ringHom_ext_of_comp_algebraMap_eq {B : Type*} [CommRing B] (𝔪 : Ideal B) (h𝔪 : 𝔪.FG)
    {S : Type*} [CommRing S] (J : Ideal S) [IsHausdorff J S]
    (χ₁ χ₂ : AdicCompletion 𝔪 B →+* S)
    (hagree : χ₁.comp (algebraMap B (AdicCompletion 𝔪 B)) = χ₂.comp (algebraMap B (AdicCompletion 𝔪 B)))
    (h₁ : ∀ k : ℕ, ∃ n : ℕ, ∀ x ∈ (𝔪 ^ n • ⊤ : Submodule B (AdicCompletion 𝔪 B)), χ₁ x ∈ J ^ k)
    (h₂ : ∀ k : ℕ, ∃ n : ℕ, ∀ x ∈ (𝔪 ^ n • ⊤ : Submodule B (AdicCompletion 𝔪 B)), χ₂ x ∈ J ^ k) :
    χ₁ = χ₂ := by
  apply RingHom.ext
  intro x
  apply eq_of_sub_eq_zero
  apply IsHausdorff.haus (‹IsHausdorff J S›)
  intro k
  obtain ⟨n₁, hn₁⟩ := h₁ k
  obtain ⟨n₂, hn₂⟩ := h₂ k
  set n := max n₁ n₂ with hn

  obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (eval 𝔪 B n x)
  have hker : x - algebraMap B (AdicCompletion 𝔪 B) b ∈ (𝔪 ^ n • ⊤ : Submodule B (AdicCompletion 𝔪 B)) := by
    rw [pow_smul_top_eq_ker_eval h𝔪, LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, eval_of, Submodule.mkQ_apply, hb, sub_self]
  have hmono : ∀ {m m' : ℕ}, m ≤ m' →
      (𝔪 ^ m' • ⊤ : Submodule B (AdicCompletion 𝔪 B)) ≤ 𝔪 ^ m • ⊤ := fun h =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  have e : χ₁ x - χ₂ x = χ₁ (x - algebraMap B _ b) - χ₂ (x - algebraMap B _ b) := by
    have hab : χ₁ (algebraMap B _ b) = χ₂ (algebraMap B _ b) := by
      rw [← RingHom.comp_apply, hagree, RingHom.comp_apply]
    rw [map_sub, map_sub, hab]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, e]
  exact sub_mem (hn₁ _ (hmono (le_max_left _ _) hker)) (hn₂ _ (hmono (le_max_right _ _) hker))

theorem forall_mem_smul_top_imp {B : Type*} [CommRing B] (𝔪 : Ideal B) {S : Type*} [CommRing S] (J : Ideal S)
    (χ : AdicCompletion 𝔪 B →+* S) (n k : ℕ) (h : 𝔪 ^ n ≤ (J ^ k).comap (χ.comp (algebraMap B _))) :
    ∀ x ∈ (𝔪 ^ n • ⊤ : Submodule B (AdicCompletion 𝔪 B)), χ x ∈ J ^ k := by
  intro x hx
  refine Submodule.smul_induction_on (p := fun x => χ x ∈ J ^ k) hx ?_ ?_
  · intro r hr y _
    change χ (r • y) ∈ J ^ k
    rw [Algebra.smul_def, map_mul]
    exact Ideal.mul_mem_right _ _ (h hr)
  · intro x y hx hy
    change χ (x + y) ∈ J ^ k
    rw [map_add]; exact add_mem hx hy

end AdicCompletion.ValuedLift

end Generic

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces NodeLocalized.coeffSubring NodeLocalized.fieldOver uvCrossingIdeal UVCrossingModel PlaceSpecialization.ProlongationTuple.valuation_coe_lt_one_of_maximalIdeal_eq_span" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple reduceFst mk ProlongationTuple.valuation_coe_lt_one_of_maximalIdeal_eq_span" namespace ProlongationTuple p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "ValueIntegralityLaw nodeIntegersOver nodeConst NodeCoordinates mk ι valuation_coe_lt_one_of_maximalIdeal_eq_span exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt eq_of_forall_evalAt_eq_of_reduceFst_eq card_le_finrank_quotient_of_forall_ker_eq" end ModularCurve.PlaceSpecialization.ProlongationTuple
namespace ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple" in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
open Valued _root_.ModularCurve.UVCrossingModel _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq.ModularCurve.UVCrossingModel _root_.ModularCurve.PlaceSpecialization.ProlongationTuple AdicCompletion.ValuedLift in

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.exists_algHom_of_completedEvaluation
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    {W : Type u} [CommRing W]
    (π : W) (E : ℕ)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (αU : UVCrossingModel W (π ^ E)) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    [IsLocalRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
        ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτo : ∀ o : ↥(NodeLocalized.coeffSubring A K),
        ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap _ _ o)))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (ψ : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+* 𝒪[(A.valuation).Completion])

    (ιC : AlgebraicClosure ℚ →+* (A.valuation).Completion)
    (hψ' : ∀ g : ↥(R.nodeIntegersOver K w),
      ((ψ (algebraMap _ _ g) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))))
    (ϖC : 𝒪[(A.valuation).Completion])
    (hϖC : (ϖC : (A.valuation).Completion) = ιC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ))
    [IsAdicComplete (Ideal.span {ϖC}) 𝒪[(A.valuation).Completion]]
    (ιOC : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K)
        →+* 𝒪[(A.valuation).Completion])
    (hιOC : ∀ o : ↥(NodeLocalized.coeffSubring A K),
        ((ιOC (algebraMap _ _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          ιC ((o : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ))
    [Algebra W (A.valuation).Completion]
    (halg : ∀ a : W, algebraMap W (A.valuation).Completion a =
        ((ιOC (τ.symm a) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) :
    ∃ φ : UVCrossingModel W (π ^ E) →ₐ[W] (A.valuation).Completion,
      (∀ z, φ z = ((ψ (ι.symm z) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) ∧
      (∀ g : ↥(R.nodeIntegersOver K w),
        φ (ι (algebraMap _ _ g)) = ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))))) ∧
      φ (U (π ^ E) * αU) = ιC (V.evalAt ((c.x : ↥(modularFunctionFieldBar (N * q))))) := by
  classical

  let χ : UVCrossingModel W (π ^ E) →+* (A.valuation).Completion :=
    ((𝒪[(A.valuation).Completion]).subtype.comp ψ).comp ι.symm.toRingHom
  have hχι : ∀ y, χ (ι y) = ((ψ y : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := fun y => by
    show ((ψ (ι.symm (ι y)) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = _
    rw [RingEquiv.symm_apply_apply]

  let χ₁ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K)
      →+* 𝒪[(A.valuation).Completion] :=
    ψ.comp (ι.symm.toRingHom.comp ((algebraMap W (UVCrossingModel W (π ^ E))).comp τ.toRingHom))
  have hconst : ∀ a : W, algebraMap W (UVCrossingModel W (π ^ E)) a = const (π ^ E) a := fun a => rfl
  have hχ₁o : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      χ₁ (algebraMap _ _ o) = ψ (algebraMap _ _ (R.nodeConst K w o)) := by
    intro o
    show ψ (ι.symm (algebraMap W _ (τ (algebraMap _ _ o)))) = _
    rw [hconst, ← hτo, RingEquiv.symm_apply_apply]
  have hevconst : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      V.evalAt ((R.nodeConst K w o : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) =
        ((o : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := fun o =>
    V.evalAt_algebraMap _
  have hagree : χ₁.comp (algebraMap _ _) = ιOC.comp (algebraMap ↥(NodeLocalized.coeffSubring A K) _) := by
    apply RingHom.ext
    intro o
    show χ₁ (algebraMap _ _ o) = ιOC (algebraMap _ _ o)
    apply Subtype.ext
    rw [hχ₁o, hψ', hevconst, hιOC]
  have hϖ₁ : χ₁ (algebraMap _ _ ϖ) = ϖC := Subtype.ext (by rw [hχ₁o, hψ', hevconst, hϖC])
  have hϖ₂ : ιOC (algebraMap _ _ ϖ) = ϖC := Subtype.ext (by rw [hιOC, hϖC])
  have hcontχ : ∀ χ' : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
      ↥(NodeLocalized.coeffSubring A K) →+* 𝒪[(A.valuation).Completion], χ' (algebraMap _ _ ϖ) = ϖC →
      ∀ k' : ℕ, ∃ n : ℕ, ∀ x ∈ (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) ^ n • ⊤ :
        Submodule ↥(NodeLocalized.coeffSubring A K) (AdicCompletion (IsLocalRing.maximalIdeal
          ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K))), χ' x ∈ Ideal.span {ϖC} ^ k' := by
    intro χ' hχ' k'
    refine ⟨k', forall_mem_smul_top_imp _ _ χ' k' k' ?_⟩
    intro a ha
    rw [hϖgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [Ideal.mem_comap, RingHom.comp_apply, map_mul, map_pow, map_mul, map_pow, hχ', Ideal.span_singleton_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr (dvd_refl _))
  haveI : IsHausdorff (Ideal.span {ϖC}) 𝒪[(A.valuation).Completion] := IsAdicComplete.toIsHausdorff
  have hFG : (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)).FG :=
    ⟨{ϖ}, by rw [hϖgen, Finset.coe_singleton]⟩
  have hχeq : χ₁ = ιOC :=
    ringHom_ext_of_comp_algebraMap_eq _ hFG _ χ₁ ιOC hagree (hcontχ χ₁ hϖ₁) (hcontχ ιOC hϖ₂)

  have hcommR : ∀ a : W, χ (algebraMap W (UVCrossingModel W (π ^ E)) a) = algebraMap W (A.valuation).Completion a := by
    intro a
    rw [halg, ← hχeq]
    show ((ψ (ι.symm (algebraMap W _ a)) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
      ((ψ (ι.symm (algebraMap W _ (τ (τ.symm a)))) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)
    rw [RingEquiv.apply_symm_apply]
  let χₐ : UVCrossingModel W (π ^ E) →ₐ[W] (A.valuation).Completion := { toRingHom := χ, commutes' := hcommR }
  refine ⟨χₐ, fun z => rfl, fun g => ?_, ?_⟩
  · show χ (ι (algebraMap _ _ g)) = _
    rw [hχι, hψ']
  · show χ (U (π ^ E) * αU) = _
    rw [← hιx, hχι, hψ']

end ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_export "" "ModularCurve.PlaceSpecialization.ProlongationTuple.exists_algHom_of_completedEvaluation"
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 800000 in
open _root_.ModularCurve.UVCrossingModel _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq.ModularCurve.UVCrossingModel Valued in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)] [IsNoetherianRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hres : ∀ g : ↥(R.nodeIntegersOver K w), ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o))
    (hVI : R.ValueIntegralityLaw w) [DecidableEq k] (hwss : w ∈ ssPlaces q N k)
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)
          ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap _ _ (R.nodeConst K w ϖ)) = const (π ^ E) π)
    (αU : UVCrossingModel W (π ^ E)) (hαU : IsUnit αU) (hιx : ι (algebraMap _ _ c.x) = U (π ^ E) * αU)
    (hht : ∀ 𝔭 𝔮 : Ideal ↥(R.nodeIntegersOver K w), 𝔭.IsPrime → 𝔮.IsPrime →
      𝔮 ≠ IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) → 𝔭 < 𝔮 → 𝔭 = ⊥)
    (hfrac : ∀ z ∈ NodeLocalized.fieldOver (N * q) K, ∃ x y : ↥(modularFunctionFieldBar (N * q)),
      x ∈ R.nodeIntegersOver K w ∧ y ∈ R.nodeIntegersOver K w ∧ y ≠ 0 ∧
        z * ((y : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) = ((x : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) ≃+* W)
    (hτ : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o)))
    (hτϖ : τ (algebraMap ↥(NodeLocalized.coeffSubring A K) _ ϖ) = π)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w)) [𝔮.IsPrime]
    (h𝔮 : ∀ o : ↥(NodeLocalized.coeffSubring A K), o ≠ 0 → R.nodeConst K w o ∉ 𝔮)
    (h𝔮0 : 𝔮 ≠ ⊥)

    (j : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) ↥(NodeLocalized.coeffSubring A K) →+*
          𝒪[(A.valuation).Completion])
    (hj : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((j (algebraMap ↥(NodeLocalized.coeffSubring A K) _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
        ((o : AlgebraicClosure ℚ) : (A.valuation).Completion))
    (g : ↥(R.nodeIntegersOver K w))
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V, V ∈ S ↔ (P.reduceFst V = w ∧
      ∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0))
    (hcard : (S.card : ℕ∞) = ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
          (_ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
              (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧
            const (π ^ E) π ∉ Q.asIdeal),
          (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞))
    (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
    (hQ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
        (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧
      const (π ^ E) π ∉ Q.asIdeal)
    (SQ : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hSQ : ∀ V, V ∈ SQ ↔ (V ∈ S ∧
      ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+*
          𝒪[(A.valuation).Completion],
        (∀ g' : ↥(R.nodeIntegersOver K w),
          ((ψ (algebraMap ↥(R.nodeIntegersOver K w) _ g') : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
            ((V.evalAt (g' : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion)) ∧
        Q.asIdeal = RingHom.ker (ψ.comp ι.symm.toRingHom))) :
    ((∏ V ∈ SQ, V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) : AlgebraicClosure ℚ) :
        (A.valuation).Completion) =
      ((j (τ.symm (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal
            (ι (algebraMap ↥(R.nodeIntegersOver K w) _ g))))) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := by
  classical

  set J : Ideal (UVCrossingModel W (π ^ E)) := Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
    (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮 with hJ
  haveI : Nontrivial (UVCrossingModel W (π ^ E)) := ι.injective.nontrivial
  haveI : IsLocalRing (UVCrossingModel W (π ^ E)) := IsLocalRing.of_surjective' ι.toRingHom ι.surjective
  haveI : IsDomain (W ⧸ Ideal.span {π}) :=
    (Ideal.Quotient.isDomain_iff_prime _).2
      ((Ideal.span_singleton_prime hπ.ne_zero).2 ((UniqueFactorizationMonoid.irreducible_iff_prime).1 hπ))
  have hE0 : E ≠ 0 := by omega
  have hdiv : π ∣ π ^ E := dvd_pow_self π hE0
  have hπE : ¬ IsUnit (π ^ E) := fun h => hπ.not_isUnit (isUnit_of_dvd_unit hdiv h)
  have hmRsup := maximalIdeal_eq_map_maximalIdeal_sup_span_pair (W := W) hπE
  have hUm : U (π ^ E) ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rw [hmRsup]; exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
  have hVm : V (π ^ E) ∈ maximalIdeal (UVCrossingModel W (π ^ E)) := by
    rw [hmRsup]; exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
  have hmR : (maximalIdeal ↥(R.nodeIntegersOver K w)).map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) = maximalIdeal (UVCrossingModel W (π ^ E)) :=
    IsLocalRing.map_maximalIdeal_comp_adicCompletion_eq ι
  have hφϖ : (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) (R.nodeConst K w ϖ) = const (π ^ E) π := hιϖ
  have hϖ𝔮 : R.nodeConst K w ϖ ∉ 𝔮 := h𝔮 ϖ hϖ0
  have hJU : ¬ J ≤ Ideal.span {const (π ^ E) π, U (π ^ E)} := by
    obtain ⟨P₁, hP₁, hUP, hcP, hVP⟩ := exists_isPrime_U_mem_const_mem_V_notMem (π ^ E) π hdiv
    haveI := hP₁
    intro hle
    have hle' : J ≤ P₁ := hle.trans (Ideal.span_le.2 (by rintro z (rfl | rfl); exacts [hcP, hUP]))
    exact IsLocalRing.not_map_le_of_forall_lt_eq_bot _ hmR hht 𝔮 h𝔮0 P₁
      (fun h => hVP (h hVm)) (R.nodeConst K w ϖ) (hφϖ ▸ hcP) hϖ𝔮 hle'
  have hJV : ¬ J ≤ Ideal.span {const (π ^ E) π, V (π ^ E)} := by
    obtain ⟨P₂, hP₂, hVP, hcP, hUP⟩ := exists_isPrime_V_mem_const_mem_U_notMem (π ^ E) π hdiv
    haveI := hP₂
    intro hle
    have hle' : J ≤ P₂ := hle.trans (Ideal.span_le.2 (by rintro z (rfl | rfl); exacts [hcP, hVP]))
    exact IsLocalRing.not_map_le_of_forall_lt_eq_bot _ hmR hht 𝔮 h𝔮0 P₂
      (fun h => hUP (h hUm)) (R.nodeConst K w ϖ) (hφϖ ▸ hcP) hϖ𝔮 hle'
  haveI hJfin : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ J) := moduleFinite_quotient_of_not_le_span_pair π hπ E hE _ hJU hJV

  obtain ⟨ιC, hιC, hvC⟩ : ∃ ιC : AlgebraicClosure ℚ →+* (A.valuation).Completion,
      (∀ x, ιC x = (x : (A.valuation).Completion)) ∧ ∀ x, Valued.v (ιC x) = A.valuation x := by
    refine ⟨(UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* (A.valuation).Completion).comp
      (WithVal.equiv A.valuation).symm.toRingHom, fun x => rfl, fun x => ?_⟩
    show Valued.v (((WithVal.equiv A.valuation).symm x : WithVal A.valuation) : (A.valuation).Completion) = A.valuation x
    rw [Valued.valuedCompletion_apply]
    rfl

  have hvϖ1 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) < 1 :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.valuation_coe_lt_one_of_maximalIdeal_eq_span R K w c ϖ hmax
  have hϖ0' : ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := fun h => hϖ0 (Subtype.ext h)
  have hvϖ0 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ≠ 0 := by
    rwa [Valuation.ne_zero_iff]
  have hOmem : ∀ x : AlgebraicClosure ℚ, A.valuation x ≤ 1 → ιC x ∈ 𝒪[(A.valuation).Completion] := fun x hx => by
    change Valued.v (ιC x) ≤ 1; rw [hvC]; exact hx
  obtain ⟨ϖC, hϖC⟩ : ∃ ϖC : 𝒪[(A.valuation).Completion],
      (ϖC : (A.valuation).Completion) = ιC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) :=
    ⟨⟨ιC _, hOmem _ hvϖ1.le⟩, rfl⟩
  have hvϖC : Valued.v (ϖC : (A.valuation).Completion) =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by rw [hϖC, hvC]
  have hϖC0 : (ϖC : (A.valuation).Completion) ≠ 0 := by
    rw [hϖC]; exact (map_ne_zero ιC).mpr hϖ0'
  haveI hAC : IsAdicComplete (Ideal.span {ϖC}) 𝒪[(A.valuation).Completion] := by
    apply Valued.isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt ϖC hϖC0
    intro γ hγ
    rw [hvϖC]
    exact A.exists_valuation_pow_lt_of_isAlgebraic hvϖ0 hvϖ1 γ hγ

  have hj' : ∀ o : ↥(NodeLocalized.coeffSubring A K),
      ((j (algebraMap _ _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = ιC ((o : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := fun o => by
    rw [hj, hιC]
  letI algWC : Algebra W (A.valuation).Completion :=
    ((𝒪[(A.valuation).Completion]).subtype.comp (j.comp τ.symm.toRingHom)).toAlgebra
  have halg : ∀ a : W, algebraMap W (A.valuation).Completion a =
      ((j (τ.symm a) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := fun a => rfl
  have hτsymm : τ.symm π = algebraMap _ _ ϖ := by rw [RingEquiv.symm_apply_eq, hτϖ]
  have hπC : algebraMap W (A.valuation).Completion π = ιC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by
    rw [halg, hτsymm, hj']
  have hCπ : algebraMap W (A.valuation).Completion π ≠ 0 := by
    rw [hπC]; exact (map_ne_zero ιC).mpr hϖ0'

  have hxw : ∀ x : S, P.reduceFst x.1 = w := fun x => ((hS x.1).mp x.2).1
  have hx𝔮 : ∀ x : S, ∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ x.1.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0 := fun x => ((hS x.1).mp x.2).2

  have key : ∀ V ∈ S, ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+* 𝒪[(A.valuation).Completion],
      ∃ χ : UVCrossingModel W (π ^ E) →ₐ[W] (A.valuation).Completion,
        (∀ g' : ↥(R.nodeIntegersOver K w), ((ψ (algebraMap _ _ g') : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = ((V.evalAt (g' : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion)) ∧
        (∀ z, χ z = ((ψ (ι.symm z) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion)) ∧
        (∀ g' : ↥(R.nodeIntegersOver K w), χ (ι (algebraMap _ _ g')) = ιC (V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))))) := by
    intro V hVS
    obtain ⟨hVw, -⟩ := (hS V).mp hVS
    obtain ⟨ψ, -, hψ⟩ := R.exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt K w c ϖ hϖ0 hmax hVI V hVw
    have hψ' : ∀ g' : ↥(R.nodeIntegersOver K w), ((ψ (algebraMap _ _ g') : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = ιC (V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q))))) :=
      fun g' => by rw [hψ, hιC]
    obtain ⟨χ, hχψ, hχg, -⟩ := R.exists_algHom_of_completedEvaluation K w c ϖ π E ι αU hιx hϖgen τ hτ V ψ ιC hψ'
      ϖC hϖC j hj' halg
    exact ⟨ψ, χ, hψ, hχψ, hχg⟩
  choose Ψ Φ hΨ hΦψ hΦg using key
  let χ : S → (UVCrossingModel W (π ^ E) →ₐ[W] (A.valuation).Completion) := fun x => Φ x.1 x.2
  have hχ : ∀ x : S, ∀ g' : ↥(R.nodeIntegersOver K w), χ x (ι (algebraMap _ _ g')) = ιC (x.1.evalAt ((g' : ↥(modularFunctionFieldBar (N * q))))) :=
    fun x => hΦg x.1 x.2
  have hχψ : ∀ x : S, ∀ z, χ x z = ((Ψ x.1 x.2 (ι.symm z) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := fun x => hΦψ x.1 x.2

  let κ : S → PrimeSpectrum (UVCrossingModel W (π ^ E)) := fun x => ⟨RingHom.ker (χ x : UVCrossingModel W (π ^ E) →+* (A.valuation).Completion), RingHom.ker_isPrime _⟩
  have hmemκ : ∀ x : S, ∀ z, z ∈ (κ x).asIdeal ↔ χ x z = 0 := fun x z => Iff.rfl
  have hκψ : ∀ x : S, (κ x).asIdeal = RingHom.ker ((Ψ x.1 x.2).comp ι.symm.toRingHom) := by
    intro x
    ext z
    rw [hmemκ, RingHom.mem_ker, hχψ]
    show ((Ψ x.1 x.2 (ι.symm z) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = 0 ↔ Ψ x.1 x.2 (ι.symm z) = 0
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  have hJle : ∀ x : S, J ≤ (κ x).asIdeal := by
    intro x
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro g' hg'
    rw [Ideal.mem_comap, hmemκ]
    show χ x (ι (algebraMap _ _ g')) = 0
    rw [hχ, (hx𝔮 x g').mp hg', map_zero]
  have hπκ : ∀ x : S, const (π ^ E) π ∉ (κ x).asIdeal := by
    intro x h
    rw [hmemκ] at h
    apply hCπ
    rw [← h]
    exact (AlgHom.commutes (χ x) π).symm
  have hmin : J.minimalPrimes = Ideal.comap (Ideal.Quotient.mk J) '' minimalPrimes (UVCrossingModel W (π ^ E) ⧸ J) :=
    BranchKer.minimalPrimes_eq_image_comap_mk J
  have hκmin : ∀ x : S, (κ x).asIdeal ∈ J.minimalPrimes := by
    intro x
    let φb : (UVCrossingModel W (π ^ E) ⧸ J) →ₐ[W] (A.valuation).Completion := Ideal.Quotient.liftₐ J (χ x) (fun a ha => (hmemκ x a).mp (hJle x ha))
    have hmem := BranchKer.ker_mem_minimalPrimes (S := UVCrossingModel W (π ^ E) ⧸ J) hπ hCπ φb
    rw [hmin]
    refine ⟨_, hmem, ?_⟩
    ext z
    rw [Ideal.mem_comap, RingHom.mem_ker, hmemκ]
    exact Iff.rfl

  set MinBr : Set (PrimeSpectrum (UVCrossingModel W (π ^ E))) := {Q | Q.asIdeal ∈ J.minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal}
    with hMinBr
  haveI : IsNoetherianRing (UVCrossingModel W (π ^ E) ⧸ J) := isNoetherian_of_tower W (inferInstance : IsNoetherian W (UVCrossingModel W (π ^ E) ⧸ J))
  have hfin : MinBr.Finite := by
    have h1 : {Q : PrimeSpectrum (UVCrossingModel W (π ^ E)) | Q.asIdeal ∈ J.minimalPrimes}.Finite := by
      rw [hmin]
      exact ((minimalPrimes.finite_of_isNoetherianRing (UVCrossingModel W (π ^ E) ⧸ J)).image _).preimage
        (fun a _ b _ h => PrimeSpectrum.ext h)
    exact h1.subset fun Q hQ => hQ.1
  have hκF : ∀ x : S, κ x ∈ hfin.toFinset := fun x => by
    rw [Set.Finite.mem_toFinset]; exact ⟨hκmin x, hπκ x⟩

  have hcard' : S.card = ∑ Q ∈ hfin.toFinset, Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := by
    have h := hcard
    change (S.card : ℕ∞) = ∑ᶠ Q ∈ MinBr, (Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) : ℕ∞) at h
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Nat.cast_sum] at h
    exact_mod_cast h
  have hcardS : S.card = ∑ Q ∈ hfin.toFinset, (Finset.univ.filter (fun x : S => κ x = Q)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset S)) (t := hfin.toFinset) (f := κ)
      (fun x _ => hκF x)
    rwa [Finset.card_univ, Fintype.card_coe] at h
  have hsepS : ∀ x x' : S, (∀ g' : ↥(R.nodeIntegersOver K w), x.1.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = x'.1.evalAt ((g' : ↥(modularFunctionFieldBar (N * q))))) → x = x' :=
    fun x x' h => Subtype.ext (R.eq_of_forall_evalAt_eq_of_reduceFst_eq K w hht hfrac x.1 x'.1 (hxw x) (hxw x') h)
  have hle : ∀ Q ∈ hfin.toFinset,
      (Finset.univ.filter (fun x : S => κ x = Q)).card ≤ Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := by
    intro Q hQF

    set SQ : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :=
      (Finset.univ.filter (fun x : S => κ x = Q)).map (Function.Embedding.subtype _) with hSQ
    have hcardSQ : SQ.card = (Finset.univ.filter (fun x : S => κ x = Q)).card := Finset.card_map _
    have hmemSQ : ∀ V, V ∈ SQ ↔ ∃ h : V ∈ S, κ ⟨V, h⟩ = Q := by
      intro V
      rw [hSQ, Finset.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Finset.mem_filter] at hx
        exact ⟨x.2, hx.2⟩
      · rintro ⟨h, hκ⟩
        exact ⟨⟨V, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hκ⟩, rfl⟩
    have hSQprop : ∀ V ∈ SQ, P.reduceFst V = w ∧
        (∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0) ∧
        ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+* 𝒪[(A.valuation).Completion],
          (∀ g' : ↥(R.nodeIntegersOver K w),
            ((ψ (algebraMap ↥(R.nodeIntegersOver K w) _ g') : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
              ((V.evalAt (g' : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion)) ∧
          Q.asIdeal = RingHom.ker (ψ.comp ι.symm.toRingHom) := by
      intro V hV
      obtain ⟨hVS, hκ⟩ := (hmemSQ V).mp hV
      refine ⟨hxw ⟨V, hVS⟩, hx𝔮 ⟨V, hVS⟩, Ψ V hVS, hΨ V hVS, ?_⟩
      rw [← hκ]
      exact hκψ ⟨V, hVS⟩
    have hSQsep : ∀ V ∈ SQ, ∀ V' ∈ SQ,
        (∀ g' : ↥(R.nodeIntegersOver K w), V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = V'.evalAt ((g' : ↥(modularFunctionFieldBar (N * q))))) → V = V' := by
      intro V hV V' hV' hVV'
      obtain ⟨hVS, -⟩ := (hmemSQ V).mp hV
      obtain ⟨hV'S, -⟩ := (hmemSQ V').mp hV'
      exact congrArg Subtype.val (hsepS ⟨V, hVS⟩ ⟨V', hV'S⟩ hVV')
    have h := R.card_le_finrank_quotient_of_forall_ker_eq K w c ϖ hϖ0 hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx
      hϖgen ⟨τ, hτ, hτϖ⟩ 𝔮 hJfin Q SQ hSQprop hSQsep
    rw [hcardSQ] at h
    exact_mod_cast h
  have heq : ∀ Q ∈ hfin.toFinset,
      (Finset.univ.filter (fun x : S => κ x = Q)).card = Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := by
    have hsum : ∑ Q ∈ hfin.toFinset, (Finset.univ.filter (fun x : S => κ x = Q)).card =
        ∑ Q ∈ hfin.toFinset, Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := by rw [← hcardS, hcard']
    exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum

  have hQF : Q ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hQ
  haveI hQp : Q.asIdeal.IsPrime := Q.isPrime
  have hJQ : J ≤ Q.asIdeal := hQ.1.1.2
  have hSQS : ∀ V ∈ SQ, V ∈ S := fun V hV => ((hSQ V).mp hV).1
  have hSQprop : ∀ V ∈ SQ, P.reduceFst V = w ∧
      (∀ g' : ↥(R.nodeIntegersOver K w), g' ∈ 𝔮 ↔ V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = 0) ∧
      ∃ ψ : AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w) →+* 𝒪[(A.valuation).Completion],
        (∀ g' : ↥(R.nodeIntegersOver K w),
          ((ψ (algebraMap ↥(R.nodeIntegersOver K w) _ g') : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
            ((V.evalAt (g' : ↥(modularFunctionFieldBar (N * q))) : AlgebraicClosure ℚ) : (A.valuation).Completion)) ∧
        Q.asIdeal = RingHom.ker (ψ.comp ι.symm.toRingHom) := by
    intro V hV
    obtain ⟨hVS, ψ, hψ, hQψ⟩ := (hSQ V).mp hV
    exact ⟨hxw ⟨V, hVS⟩, hx𝔮 ⟨V, hVS⟩, ψ, hψ, hQψ⟩
  have hSQsep : ∀ V ∈ SQ, ∀ V' ∈ SQ,
      (∀ g' : ↥(R.nodeIntegersOver K w), V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q)))) = V'.evalAt ((g' : ↥(modularFunctionFieldBar (N * q))))) → V = V' :=
    fun V hV V' hV' h => congrArg Subtype.val (hsepS ⟨V, hSQS V hV⟩ ⟨V', hSQS V' hV'⟩ h)
  have hSQle : SQ.card ≤ Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := by
    have h := R.card_le_finrank_quotient_of_forall_ker_eq K w c ϖ hϖ0 hmax hres hVI hwss π hπ E hE ι hιϖ αU hαU hιx
      hϖgen ⟨τ, hτ, hτϖ⟩ 𝔮 hJfin Q SQ hSQprop hSQsep
    exact_mod_cast h
  have hSQge : Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) ≤ SQ.card := by
    rw [← heq Q hQF]
    have hsub : (Finset.univ.filter (fun x : S => κ x = Q)).map (Function.Embedding.subtype _) ⊆ SQ := by
      intro V hV
      rw [Finset.mem_map] at hV
      obtain ⟨x, hx, rfl⟩ := hV
      rw [Finset.mem_filter] at hx
      rw [hSQ]
      refine ⟨x.2, Ψ x.1 x.2, hΨ x.1 x.2, ?_⟩
      rw [← hx.2]
      exact hκψ x
    have h := Finset.card_le_card hsub
    rwa [Finset.card_map] at h
  have hSQcard : SQ.card = Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := le_antisymm hSQle hSQge

  haveI : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := by
    let f : (UVCrossingModel W (π ^ E) ⧸ J) →ₐ[W] (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) :=
      Ideal.Quotient.liftₐ J (Ideal.Quotient.mkₐ W Q.asIdeal) (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hJQ ha))
    refine Module.Finite.of_surjective f.toLinearMap ?_
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk J z, rfl⟩
  have hinjQ : Function.Injective (algebraMap W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
    rw [IsScalarTower.algebraMap_apply W (UVCrossingModel W (π ^ E)) (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow] at ha
    rcases hQp.mem_or_mem ha with hu | hp
    · exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ hu (u.isUnit.map (algebraMap W (UVCrossingModel W (π ^ E)))))
    · exact hQ.2 (hQp.mem_of_pow_mem n hp)
  haveI : Module.IsTorsionFree W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinjQ
  haveI : Module.Free W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := Module.free_of_finite_type_torsion_free'

  have keyQ : ∀ V ∈ SQ, ∃ φ : (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) →ₐ[W] (A.valuation).Completion,
      ∀ g' : ↥(R.nodeIntegersOver K w),
        φ (Ideal.Quotient.mk Q.asIdeal (ι (algebraMap _ _ g'))) = ιC (V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q))))) := by
    intro V hV
    obtain ⟨hVS, ψ, hψ, hQψ⟩ := (hSQ V).mp hV
    have hψ' : ∀ g' : ↥(R.nodeIntegersOver K w),
        ((ψ (algebraMap _ _ g') : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          ιC (V.evalAt ((g' : ↥(modularFunctionFieldBar (N * q))))) := fun g' => by rw [hψ, hιC]
    obtain ⟨χ', hχψ', hχg', -⟩ := R.exists_algHom_of_completedEvaluation K w c ϖ π E ι αU hιx hϖgen τ hτ V ψ ιC hψ'
      ϖC hϖC j hj' halg
    have hmemQ : ∀ z, z ∈ Q.asIdeal ↔ χ' z = 0 := by
      intro z
      rw [hQψ, RingHom.mem_ker, hχψ']
      show ψ (ι.symm z) = 0 ↔ ((ψ (ι.symm z) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = 0
      exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
    refine ⟨Ideal.Quotient.liftₐ Q.asIdeal χ' (fun z hz => (hmemQ z).mp hz), fun g' => ?_⟩
    show χ' (ι (algebraMap _ _ g')) = _
    exact hχg' g'
  choose φQ hφQ using keyQ
  let σ : SQ → ((UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) →ₐ[W] (A.valuation).Completion) := fun y => φQ y.1 y.2
  have hσinj : Function.Injective σ := by
    intro y y' hyy
    apply Subtype.ext
    apply hSQsep y.1 y.2 y'.1 y'.2
    intro g'
    apply ιC.injective
    rw [← hφQ y.1 y.2 g', ← hφQ y'.1 y'.2 g']
    show σ y _ = σ y' _
    rw [hyy]
  have hcardι : Fintype.card SQ = Module.finrank W (UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) := by
    rw [Fintype.card_coe]; exact hSQcard
  have hN := Algebra.algebraMap_norm_eq_prod_apply_of_card_eq_finrank (T := UVCrossingModel W (π ^ E) ⧸ Q.asIdeal) σ hσinj hcardι
    (Ideal.Quotient.mk Q.asIdeal (ι (algebraMap ↥(R.nodeIntegersOver K w) _ g)))

  have hL : (((∏ V ∈ SQ, V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) : AlgebraicClosure ℚ) : (A.valuation).Completion) =
      ιC (∏ V ∈ SQ, V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) := (hιC _).symm
  rw [hL, map_prod, ← halg, hN, ← Finset.prod_coe_sort SQ (fun V => ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))))]
  exact Fintype.prod_congr _ _ (fun y => (hφQ y.1 y.2 g).symm)

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_prod_evalAt_eq_norm_quotient_of_forall_iff_exists_ker_eq (solution)
