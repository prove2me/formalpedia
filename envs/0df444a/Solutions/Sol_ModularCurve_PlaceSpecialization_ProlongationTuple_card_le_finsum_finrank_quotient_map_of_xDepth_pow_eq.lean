-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.card_le_finsum_finrank_quotient_map_of_xDepth_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7b24bcb5-1930-5d0c-996e-6a5b598ba0cb

import Mathlib
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic
import Theorems.Thm_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic
import Theorems.Thm_Valued_isAdicComplete_integer_span_singleton_of_forall_exists_pow_lt
import Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
import Theorems.Thm_Valued_forall_exists_pow_le_comap_span_singleton_pow_of_eq_span
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_coe_lt_one_of_maximalIdeal_eq_span
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_valuation_evalAt_lt_one_iff_mem_maximalIdeal
import Theorems.Thm_Algebra_card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finsum_finrank_quotient_map_of_xDepth_pow_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

universe u

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finsum_finrank_quotient_map_of_xDepth_pow_eq.ModularCurve ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finsum_finrank_quotient_map_of_xDepth_pow_eq.ModularCurve.PlaceSpecialization ModularCurve.UVCrossingModel"

section Generic
set_option maxHeartbeats 1600000
p2m_open "AdicCompletion P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finsum_finrank_quotient_map_of_xDepth_pow_eq.AdicCompletion Valued"

namespace AdicCompletion
p2m_export "AdicCompletion" "map eval mk eval_of of mk_surjective map_zero ext algebraMap_apply pow_smul_top_eq_ker_eval sum mkₐ exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap"
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

namespace BranchReindex

variable {W : Type*} [CommRing W] {R S : Type*} [CommRing R] [CommRing S] [Algebra W R] [Algebra W S]

theorem comap_eq_ker (ρ : R →ₐ[W] S) (𝔓 : PrimeSpectrum S) :
    (PrimeSpectrum.comap (ρ : R →+* S) 𝔓).asIdeal = RingHom.ker ((Ideal.Quotient.mkₐ W 𝔓.asIdeal).comp ρ) := by
  ext a
  simp [Ideal.mem_comap, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

noncomputable def quotEquiv (ρ : R →ₐ[W] S) (hρ : Function.Surjective ρ) (𝔓 : PrimeSpectrum S) :
    (R ⧸ (PrimeSpectrum.comap (ρ : R →+* S) 𝔓).asIdeal) ≃ₐ[W] S ⧸ 𝔓.asIdeal :=
  (Ideal.quotientEquivAlgOfEq W (comap_eq_ker ρ 𝔓)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := (Ideal.Quotient.mkₐ W 𝔓.asIdeal).comp ρ)
      ((Ideal.Quotient.mkₐ_surjective W 𝔓.asIdeal).comp hρ))

theorem quotEquiv_mk (ρ : R →ₐ[W] S) (hρ : Function.Surjective ρ) (𝔓 : PrimeSpectrum S) (x : R) :
    quotEquiv ρ hρ 𝔓 (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk 𝔓.asIdeal (ρ x) := by
  simp [quotEquiv]
  rfl

theorem finrank_quot_comap_eq (ρ : R →ₐ[W] S) (hρ : Function.Surjective ρ) (𝔓 : PrimeSpectrum S) :
    Module.finrank W (R ⧸ (PrimeSpectrum.comap (ρ : R →+* S) 𝔓).asIdeal) = Module.finrank W (S ⧸ 𝔓.asIdeal) :=
  (quotEquiv ρ hρ 𝔓).toLinearEquiv.finrank_eq

theorem length_quot_comap_eq (ρ : R →ₐ[W] S) (hρ : Function.Surjective ρ) (𝔓 : PrimeSpectrum S) (x : R) :
    Module.length W ((R ⧸ (PrimeSpectrum.comap (ρ : R →+* S) 𝔓).asIdeal) ⧸
        Ideal.span {Ideal.Quotient.mk (PrimeSpectrum.comap (ρ : R →+* S) 𝔓).asIdeal x}) =
      Module.length W ((S ⧸ 𝔓.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk 𝔓.asIdeal (ρ x)}) := by
  refine (Ideal.quotientEquivAlg (Ideal.span {Ideal.Quotient.mk (PrimeSpectrum.comap (ρ : R →+* S) 𝔓).asIdeal x})
    (Ideal.span {Ideal.Quotient.mk 𝔓.asIdeal (ρ x)}) (quotEquiv ρ hρ 𝔓) ?_).toLinearEquiv.length_eq
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun y => Ideal.span {y}) (quotEquiv_mk ρ hρ 𝔓 x).symm

theorem algebraMap_mem_comap_iff (ρ : R →ₐ[W] S) (𝔓 : PrimeSpectrum S) (π : W) :
    algebraMap W R π ∈ (PrimeSpectrum.comap (ρ : R →+* S) 𝔓).asIdeal ↔ algebraMap W S π ∈ 𝔓.asIdeal := by
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  show ρ (algebraMap W R π) ∈ 𝔓.asIdeal ↔ _
  rw [AlgHom.commutes]

theorem finsum_finrank_eq (ρ : R →ₐ[W] S) (hρ : Function.Surjective ρ) (π : W) (x : R) (r p : ℕ)
    (J : Ideal R) (hJ : RingHom.ker (ρ : R →+* S) = J) (πR : R) (hπR : ρ πR = algebraMap W S π)
    (xS : S) (hxS : ρ x = xS) :
    (∑ᶠ (𝔓 : PrimeSpectrum S) (_ : 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap W S π ∉ 𝔓.asIdeal ∧
        (r : ℕ∞) * Module.length W ((S ⧸ 𝔓.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk 𝔓.asIdeal xS}) =
          ((p * Module.finrank W (S ⧸ 𝔓.asIdeal) : ℕ) : ℕ∞)),
      (Module.finrank W (S ⧸ 𝔓.asIdeal) : ℕ∞)) =
    ∑ᶠ (Q : PrimeSpectrum R) (_ : Q.asIdeal ∈ J.minimalPrimes ∧ πR ∉ Q.asIdeal ∧
        (r : ℕ∞) * Module.length W ((R ⧸ Q.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk Q.asIdeal x}) =
          ((p * Module.finrank W (R ⧸ Q.asIdeal) : ℕ) : ℕ∞)),
      (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞) := by
  classical
  subst hJ
  subst hxS
  have hπmem : ∀ 𝔓 : PrimeSpectrum S, πR ∈ (PrimeSpectrum.comap (ρ : R →+* S) 𝔓).asIdeal ↔ algebraMap W S π ∈ 𝔓.asIdeal := by
    intro 𝔓
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    show ρ πR ∈ 𝔓.asIdeal ↔ _
    rw [hπR]
  set condS : PrimeSpectrum S → Prop := fun 𝔓 => 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap W S π ∉ 𝔓.asIdeal ∧
      (r : ℕ∞) * Module.length W ((S ⧸ 𝔓.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk 𝔓.asIdeal (ρ x)}) =
        ((p * Module.finrank W (S ⧸ 𝔓.asIdeal) : ℕ) : ℕ∞) with hcondS
  set condR : PrimeSpectrum R → Prop := fun Q => Q.asIdeal ∈ (RingHom.ker (ρ : R →+* S)).minimalPrimes ∧
      πR ∉ Q.asIdeal ∧
      (r : ℕ∞) * Module.length W ((R ⧸ Q.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk Q.asIdeal x}) =
        ((p * Module.finrank W (R ⧸ Q.asIdeal) : ℕ) : ℕ∞) with hcondR
  change (∑ᶠ 𝔓 ∈ {𝔓 | condS 𝔓}, (Module.finrank W (S ⧸ 𝔓.asIdeal) : ℕ∞)) =
    ∑ᶠ Q ∈ {Q | condR Q}, (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞)

  have hmin : (RingHom.ker (ρ : R →+* S)).minimalPrimes = Ideal.comap (ρ : R →+* S) '' minimalPrimes S := by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_minimalPrimes_eq_of_surjective hρ ⊥

  have hset : {Q | condR Q} = PrimeSpectrum.comap (ρ : R →+* S) '' {𝔓 | condS 𝔓} := by
    ext Q
    constructor
    · rintro ⟨hQmin, hQπ, hQd⟩
      have hQmin' : Q.asIdeal ∈ Ideal.comap (ρ : R →+* S) '' minimalPrimes S := by rwa [← hmin]
      obtain ⟨𝔓₀, h𝔓₀, hcomap⟩ := hQmin'
      haveI : 𝔓₀.IsPrime := h𝔓₀.1.1
      let 𝔓 : PrimeSpectrum S := ⟨𝔓₀, inferInstance⟩
      have hQ : PrimeSpectrum.comap (ρ : R →+* S) 𝔓 = Q := PrimeSpectrum.ext hcomap
      subst hQ
      refine ⟨𝔓, ⟨h𝔓₀, ?_, ?_⟩, rfl⟩
      · rwa [hπmem] at hQπ
      · rwa [length_quot_comap_eq ρ hρ, finrank_quot_comap_eq ρ hρ] at hQd
    · rintro ⟨𝔓, ⟨h𝔓min, h𝔓π, h𝔓d⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [hmin]; exact ⟨𝔓.asIdeal, h𝔓min, rfl⟩
      · rw [hπmem]; exact h𝔓π
      · rw [length_quot_comap_eq ρ hρ, finrank_quot_comap_eq ρ hρ]; exact h𝔓d
  rw [hset]
  rw [finsum_mem_image ((PrimeSpectrum.comap_injective_of_surjective (ρ : R →+* S) hρ).injOn)]
  refine finsum_congr fun 𝔓 => finsum_congr fun _ => ?_
  rw [finrank_quot_comap_eq ρ hρ]

theorem finsum_finrank_quotient_mk_eq (J : Ideal R) (π : W) (x : R) (r p : ℕ) (πR : R)
    (hπR : Ideal.Quotient.mk J πR = algebraMap W (R ⧸ J) π) (xS : R ⧸ J) (hxS : Ideal.Quotient.mk J x = xS) :
    (∑ᶠ (𝔓 : PrimeSpectrum (R ⧸ J)) (_ : 𝔓.asIdeal ∈ minimalPrimes (R ⧸ J) ∧ algebraMap W (R ⧸ J) π ∉ 𝔓.asIdeal ∧
        (r : ℕ∞) * Module.length W (((R ⧸ J) ⧸ 𝔓.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk 𝔓.asIdeal xS}) =
          ((p * Module.finrank W ((R ⧸ J) ⧸ 𝔓.asIdeal) : ℕ) : ℕ∞)),
      (Module.finrank W ((R ⧸ J) ⧸ 𝔓.asIdeal) : ℕ∞)) =
    ∑ᶠ (Q : PrimeSpectrum R) (_ : Q.asIdeal ∈ J.minimalPrimes ∧ πR ∉ Q.asIdeal ∧
        (r : ℕ∞) * Module.length W ((R ⧸ Q.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk Q.asIdeal x}) =
          ((p * Module.finrank W (R ⧸ Q.asIdeal) : ℕ) : ℕ∞)),
      (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞) :=
  finsum_finrank_eq (Ideal.Quotient.mkₐ W J) (Ideal.Quotient.mkₐ_surjective W J) π x r p J
    (Ideal.Quotient.mkₐ_ker W J) πR hπR xS hxS

theorem finsum_finrank_eq_depthFree (ρ : R →ₐ[W] S) (hρ : Function.Surjective ρ) (π : W)
    (J : Ideal R) (hJ : RingHom.ker (ρ : R →+* S) = J) (πR : R) (hπR : ρ πR = algebraMap W S π) :
    (∑ᶠ (𝔓 : PrimeSpectrum S) (_ : 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap W S π ∉ 𝔓.asIdeal),
      (Module.finrank W (S ⧸ 𝔓.asIdeal) : ℕ∞)) =
    ∑ᶠ (Q : PrimeSpectrum R) (_ : Q.asIdeal ∈ J.minimalPrimes ∧ πR ∉ Q.asIdeal),
      (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞) := by
  classical
  subst hJ
  have hπmem : ∀ 𝔓 : PrimeSpectrum S, πR ∈ (PrimeSpectrum.comap (ρ : R →+* S) 𝔓).asIdeal ↔ algebraMap W S π ∈ 𝔓.asIdeal := by
    intro 𝔓
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    show ρ πR ∈ 𝔓.asIdeal ↔ _
    rw [hπR]
  change (∑ᶠ 𝔓 ∈ {𝔓 : PrimeSpectrum S | 𝔓.asIdeal ∈ minimalPrimes S ∧ algebraMap W S π ∉ 𝔓.asIdeal},
      (Module.finrank W (S ⧸ 𝔓.asIdeal) : ℕ∞)) =
    ∑ᶠ Q ∈ {Q : PrimeSpectrum R | Q.asIdeal ∈ (RingHom.ker (ρ : R →+* S)).minimalPrimes ∧ πR ∉ Q.asIdeal},
      (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞)
  have hmin : (RingHom.ker (ρ : R →+* S)).minimalPrimes = Ideal.comap (ρ : R →+* S) '' minimalPrimes S := by
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_minimalPrimes_eq_of_surjective hρ ⊥
  have hset : {Q : PrimeSpectrum R | Q.asIdeal ∈ (RingHom.ker (ρ : R →+* S)).minimalPrimes ∧ πR ∉ Q.asIdeal} =
      PrimeSpectrum.comap (ρ : R →+* S) '' {𝔓 : PrimeSpectrum S | 𝔓.asIdeal ∈ minimalPrimes S ∧
        algebraMap W S π ∉ 𝔓.asIdeal} := by
    ext Q
    constructor
    · rintro ⟨hQmin, hQπ⟩
      have hQmin' : Q.asIdeal ∈ Ideal.comap (ρ : R →+* S) '' minimalPrimes S := by rwa [← hmin]
      obtain ⟨𝔓₀, h𝔓₀, hcomap⟩ := hQmin'
      haveI : 𝔓₀.IsPrime := h𝔓₀.1.1
      let 𝔓 : PrimeSpectrum S := ⟨𝔓₀, inferInstance⟩
      have hQ : PrimeSpectrum.comap (ρ : R →+* S) 𝔓 = Q := PrimeSpectrum.ext hcomap
      subst hQ
      refine ⟨𝔓, ⟨h𝔓₀, ?_⟩, rfl⟩
      rwa [hπmem] at hQπ
    · rintro ⟨𝔓, ⟨h𝔓min, h𝔓π⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hmin]; exact ⟨𝔓.asIdeal, h𝔓min, rfl⟩
      · rw [hπmem]; exact h𝔓π
  rw [hset]
  rw [finsum_mem_image ((PrimeSpectrum.comap_injective_of_surjective (ρ : R →+* S) hρ).injOn)]
  refine finsum_congr fun 𝔓 => finsum_congr fun _ => ?_
  rw [finrank_quot_comap_eq ρ hρ]

theorem finsum_finrank_quotient_mk_eq_depthFree (J : Ideal R) (π : W) (πR : R)
    (hπR : Ideal.Quotient.mk J πR = algebraMap W (R ⧸ J) π) :
    (∑ᶠ (𝔓 : PrimeSpectrum (R ⧸ J)) (_ : 𝔓.asIdeal ∈ minimalPrimes (R ⧸ J) ∧ algebraMap W (R ⧸ J) π ∉ 𝔓.asIdeal),
      (Module.finrank W ((R ⧸ J) ⧸ 𝔓.asIdeal) : ℕ∞)) =
    ∑ᶠ (Q : PrimeSpectrum R) (_ : Q.asIdeal ∈ J.minimalPrimes ∧ πR ∉ Q.asIdeal),
      (Module.finrank W (R ⧸ Q.asIdeal) : ℕ∞) :=
  finsum_finrank_eq_depthFree (Ideal.Quotient.mkₐ W J) (Ideal.Quotient.mkₐ_surjective W J) π J
    (Ideal.Quotient.mkₐ_ker W J) πR hπR

end BranchReindex

namespace DVRValued

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
variable {C : Type*} [Field C] [Algebra W C] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation C Γ₀)

theorem lt_one_iff_and_eq_zero_imp {π : W} (hπ : Irreducible π) (hint : ∀ a : W, v (algebraMap W C a) ≤ 1)
    (hπ1 : v (algebraMap W C π) < 1) (hπ0 : v (algebraMap W C π) ≠ 0) :
    (∀ a : W, v (algebraMap W C a) < 1 ↔ a ∈ IsLocalRing.maximalIdeal W) ∧
      (∀ a : W, v (algebraMap W C a) = 0 → a = 0) := by
  have hunit : ∀ a : W, IsUnit a → v (algebraMap W C a) = 1 := by
    intro a ha
    obtain ⟨u, rfl⟩ := ha
    have hprod : v (algebraMap W C u) * v (algebraMap W C ↑u⁻¹) = 1 := by
      rw [← Valuation.map_mul, ← map_mul, Units.mul_inv, map_one, Valuation.map_one]
    refine le_antisymm (hint u) ?_
    by_contra hlt
    push Not at hlt
    have : v (algebraMap W C u) * v (algebraMap W C ↑u⁻¹) < 1 := by
      calc v (algebraMap W C u) * v (algebraMap W C ↑u⁻¹) ≤ v (algebraMap W C u) * 1 :=
            mul_le_mul_right (hint _) _
        _ = v (algebraMap W C u) := mul_one _
        _ < 1 := hlt
    rw [hprod] at this
    exact (lt_irrefl _) this
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  refine ⟨fun a => ⟨fun h => ?_, fun h => ?_⟩, fun a h => ?_⟩
  · by_contra hn
    have hu : IsUnit a := by
      by_contra hu; exact hn ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))
    rw [hunit a hu] at h
    exact (lt_irrefl _) h
  · rw [hmax, Ideal.mem_span_singleton] at h
    obtain ⟨b, rfl⟩ := h
    rw [map_mul, Valuation.map_mul]
    calc v (algebraMap W C π) * v (algebraMap W C b) ≤ v (algebraMap W C π) * 1 := mul_le_mul_right (hint b) _
      _ < 1 := by rw [mul_one]; exact hπ1
  · by_contra ha
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow, hunit _ u.isUnit, one_mul] at h
    exact pow_ne_zero n hπ0 h

end DVRValued

end Generic

namespace ModularCurve p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence ssPlaces NodeLocalized.coeffSubring UVCrossingModel" namespace PlaceSpecialization p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple reduceFst mk" namespace ProlongationTuple p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "ValueIntegralityLaw nodeIntegersOver nodeConst NodeCoordinates mk ι valuation_coe_lt_one_of_maximalIdeal_eq_span exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt" end ModularCurve.PlaceSpecialization.ProlongationTuple
namespace ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_open_scoped "ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple" in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
open Valued _root_.ModularCurve.PlaceSpecialization.ProlongationTuple AdicCompletion.ValuedLift in

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.exists_algHom_quotient_of_place
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (w : Place k (modularFunctionFieldC k N)) (c : R.NodeCoordinates K w)
    (ϖ : ↥(NodeLocalized.coeffSubring A K)) (hϖ0 : ϖ ≠ 0)
    [IsLocalRing ↥(R.nodeIntegersOver K w)]
    (hmax : IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w) = Ideal.span {R.nodeConst K w ϖ, c.x, c.y})
    (hVI : R.ValueIntegralityLaw w)
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
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w)
    (h𝔮V : ∀ g ∈ 𝔮, V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0)

    (ιC : AlgebraicClosure ℚ →+* (A.valuation).Completion)
    (hιC : ∀ x, ιC x = (x : (A.valuation).Completion))
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
    ∃ φ : (UVCrossingModel W (π ^ E) ⧸ Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
        (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮)
          →ₐ[W] (A.valuation).Completion,
      (∀ g : ↥(R.nodeIntegersOver K w),
        φ (Ideal.Quotient.mk _ (ι (algebraMap _ _ g))) = ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))))) ∧
      φ (Ideal.Quotient.mk _ (U (π ^ E) * αU)) = ιC (V.evalAt ((c.x : ↥(modularFunctionFieldBar (N * q))))) := by
  classical

  obtain ⟨ψ, -, hψ⟩ := R.exists_ringHom_adicCompletion_nodeIntegersOver_comp_eq_evalAt K w c ϖ hϖ0 hmax hVI V hV
  have hψ' : ∀ g : ↥(R.nodeIntegersOver K w),
      ((ψ (algebraMap _ _ g) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
        ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) := fun g => by rw [hψ, hιC]

  let χ : UVCrossingModel W (π ^ E) →+* (A.valuation).Completion :=
    ((𝒪[(A.valuation).Completion]).subtype.comp ψ).comp ι.symm.toRingHom
  have hχι : ∀ y, χ (ι y) = ((ψ y : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := fun y => by
    show ((ψ (ι.symm (ι y)) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) = _
    rw [RingEquiv.symm_apply_apply]
  have hJ : ∀ z ∈ Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮, χ z = 0 := by
    have hle : Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
        (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮 ≤
        RingHom.ker χ := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
      show χ (ι (algebraMap _ _ g)) = 0
      rw [hχι, hψ', h𝔮V g hg, map_zero]
    intro z hz
    exact hle hz

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
  have hJₐ : ∀ z ∈ Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮, χₐ z = 0 := hJ
  refine ⟨Ideal.Quotient.liftₐ _ χₐ hJₐ, fun g => ?_, ?_⟩
  · rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    show χ (ι (algebraMap _ _ g)) = _
    rw [hχι, hψ']
  · rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    show χ (U (π ^ E) * αU) = _
    rw [← hιx, hχι, hψ']

end ModularCurve.PlaceSpecialization.ProlongationTuple
p2m_export "" "ModularCurve.PlaceSpecialization.ProlongationTuple.exists_algHom_quotient_of_place"
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 800000 in
open Valued _root_.ModularCurve.PlaceSpecialization.ProlongationTuple _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finsum_finrank_quotient_map_of_xDepth_pow_eq.ModularCurve.PlaceSpecialization.ProlongationTuple in

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
    [IsDiscreteValuationRing ↥(NodeLocalized.coeffSubring A K)]
    (hϖgen : IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) = Ideal.span {ϖ})
    (hτ : ∃ τ : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
        ↥(NodeLocalized.coeffSubring A K) ≃+* W,
      (∀ o : ↥(NodeLocalized.coeffSubring A K),
        ι (algebraMap _ _ (R.nodeConst K w o)) = const (π ^ E) (τ (algebraMap _ _ o))) ∧
      τ (algebraMap _ _ ϖ) = π)
    (𝔮 : Ideal ↥(R.nodeIntegersOver K w))
    (hJfin : Module.Finite W (UVCrossingModel W (π ^ E) ⧸ Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮))
    (r : ℕ) (hr : 1 ≤ r) (p : ℕ)
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))))
    (hS : ∀ V ∈ S, P.reduceFst V = w ∧
      (∀ g : ↥(R.nodeIntegersOver K w), g ∈ 𝔮 ↔ V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))) = 0) ∧
      c.xDepth V ^ r = A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) ^ p)
    (hsep : ∀ V ∈ S, ∀ V' ∈ S,
      (∀ g : ↥(R.nodeIntegersOver K w), V.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))
        = V'.evalAt ((g : ↥(modularFunctionFieldBar (N * q))))) → V = V') :
    (S.card : ℕ∞) ≤
      ∑ᶠ (Q : PrimeSpectrum (UVCrossingModel W (π ^ E)))
        (_ : Q.asIdeal ∈ (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮).minimalPrimes ∧ const (π ^ E) π ∉ Q.asIdeal ∧
          (r : ℕ∞) * Module.length W (((UVCrossingModel W (π ^ E)) ⧸ Q.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk Q.asIdeal (U (π ^ E) * αU)}) =
            ((p * Module.finrank W ((UVCrossingModel W (π ^ E)) ⧸ Q.asIdeal) : ℕ) : ℕ∞)),
        (Module.finrank W ((UVCrossingModel W (π ^ E)) ⧸ Q.asIdeal) : ℕ∞) := by
  classical
  obtain ⟨τ, hτo, hτϖ⟩ := hτ
  haveI := hJfin

  obtain ⟨ιC, hιC, hvC⟩ : ∃ ιC : AlgebraicClosure ℚ →+* (A.valuation).Completion,
      (∀ x, ιC x = (x : (A.valuation).Completion)) ∧ ∀ x, Valued.v (ιC x) = A.valuation x := by
    refine ⟨(UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* (A.valuation).Completion).comp
      (WithVal.equiv A.valuation).symm.toRingHom, fun x => rfl, fun x => ?_⟩
    show Valued.v (((WithVal.equiv A.valuation).symm x : WithVal A.valuation) : (A.valuation).Completion) = A.valuation x
    rw [Valued.valuedCompletion_apply]
    rfl

  have hvϖ1 : A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) < 1 :=
    valuation_coe_lt_one_of_maximalIdeal_eq_span R K w c ϖ hmax
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

  obtain ⟨ιOC, hιOC⟩ : ∃ ιOC : AdicCompletion (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K))
      ↥(NodeLocalized.coeffSubring A K) →+* 𝒪[(A.valuation).Completion],
      ∀ o : ↥(NodeLocalized.coeffSubring A K),
        ((ιOC (algebraMap _ _ o) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) =
          ιC ((o : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by
    have hmemO : ∀ o : ↥(NodeLocalized.coeffSubring A K),
        (ιC.comp (NodeLocalized.coeffSubring A K).subtype) o ∈ 𝒪[(A.valuation).Completion] := fun o =>
      hOmem _ (A.valuation_le_one ⟨_, o.2.1⟩)
    let evO' : ↥(NodeLocalized.coeffSubring A K) →+* 𝒪[(A.valuation).Completion] :=
      (ιC.comp (NodeLocalized.coeffSubring A K).subtype).codRestrict _ hmemO
    have hevO'ϖ : evO' ϖ = ϖC := Subtype.ext (by rw [hϖC]; rfl)
    have hcontO : ∀ k' : ℕ, ∃ n : ℕ, IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K) ^ n ≤
        (Ideal.span {ϖC} ^ k').comap evO' := by
      intro k'
      refine ⟨k', fun a ha => ?_⟩
      rw [hϖgen, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [Ideal.mem_comap, map_mul, map_pow, hevO'ϖ, Ideal.span_singleton_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton.mpr (dvd_refl _))
    obtain ⟨ιOC, hιOCcomp⟩ := AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
      (IsLocalRing.maximalIdeal ↥(NodeLocalized.coeffSubring A K)) (Ideal.span {ϖC}) evO' hcontO
    refine ⟨ιOC, fun o => ?_⟩
    have : ιOC (algebraMap _ _ o) = evO' o := by rw [← RingHom.comp_apply, hιOCcomp]
    rw [this]
    rfl

  letI algWC : Algebra W (A.valuation).Completion :=
    ((𝒪[(A.valuation).Completion]).subtype.comp (ιOC.comp τ.symm.toRingHom)).toAlgebra
  have halg : ∀ a : W, algebraMap W (A.valuation).Completion a =
      ((ιOC (τ.symm a) : 𝒪[(A.valuation).Completion]) : (A.valuation).Completion) := fun a => rfl
  have hτsymm : τ.symm π = algebraMap _ _ ϖ := by rw [RingEquiv.symm_apply_eq, hτϖ]
  have hπC : algebraMap W (A.valuation).Completion π =
      ιC ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by rw [halg, hτsymm, hιOC]
  have hvπ : Valued.v (algebraMap W (A.valuation).Completion π) =
      A.valuation ((ϖ : ↥(NodeLocalized.coeffSubring A K)) : AlgebraicClosure ℚ) := by rw [hπC, hvC]
  obtain ⟨hv, hv0⟩ := DVRValued.lt_one_iff_and_eq_zero_imp (Valued.v : Valuation (A.valuation).Completion _) hπ
    (fun a => by rw [halg]; exact (ιOC (τ.symm a)).2) (by rw [hvπ]; exact hvϖ1) (by rw [hvπ]; exact hvϖ0)

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : (UVCrossingModel W (π ^ E) ⧸ Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮), x₀ = Ideal.Quotient.mk _ (U (π ^ E) * αU) := ⟨_, rfl⟩

  have key : ∀ V ∈ S, ∃ φ : (UVCrossingModel W (π ^ E) ⧸ Ideal.map (ι.toRingHom.comp
        (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w))
          ↥(R.nodeIntegersOver K w)))) 𝔮) →ₐ[W] (A.valuation).Completion,
      (∀ g : ↥(R.nodeIntegersOver K w),
        φ (Ideal.Quotient.mk _ (ι (algebraMap _ _ g))) = ιC (V.evalAt ((g : ↥(modularFunctionFieldBar (N * q)))))) ∧
      φ x₀ = ιC (V.evalAt ((c.x : ↥(modularFunctionFieldBar (N * q))))) := by
    intro V hVS
    obtain ⟨hVw, h𝔮V, -⟩ := hS V hVS
    obtain ⟨φ, h1, h2⟩ := R.exists_algHom_quotient_of_place K w c ϖ hϖ0 hmax hVI π E ι αU hιx hϖgen τ hτo 𝔮 V hVw
      (fun g hg => (h𝔮V g).mp hg) ιC hιC ϖC hϖC ιOC hιOC halg
    exact ⟨φ, h1, by rw [hx₀]; exact h2⟩
  choose Φf hΦf using key

  have hinj : Function.Injective (fun V : {V // V ∈ S} => Φf V.1 V.2) := by
    intro V V' hEq
    apply Subtype.ext
    apply hsep V.1 V.2 V'.1 V'.2
    intro g
    have h1 := (hΦf V.1 V.2).1 g
    have h2 := (hΦf V'.1 V'.2).1 g
    have hEq' : Φf V.1 V.2 = Φf V'.1 V'.2 := hEq
    rw [hEq'] at h1
    exact ιC.injective (h1.symm.trans h2)
  have hcard : (S.attach.image (fun V : {V // V ∈ S} => Φf V.1 V.2)).card = S.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]

  have hΦ : ∀ φ ∈ (S.attach.image (fun V : {V // V ∈ S} => Φf V.1 V.2)),
      Valued.v (φ x₀) ^ r = Valued.v (algebraMap W (A.valuation).Completion π) ^ p := by
    intro φ hφ
    obtain ⟨V, -, rfl⟩ := Finset.mem_image.mp hφ
    rw [(hΦf V.1 V.2).2, hvC, hvπ]
    exact (hS V.1 V.2).2.2
  have hcount := Algebra.card_algHom_le_finsum_finrank_quotient_of_valuation_pow_eq π hπ
    (UVCrossingModel W (π ^ E) ⧸ Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w) (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮) x₀ (A.valuation).Completion (Valued.v) hv hv0 r hr p
    (S.attach.image (fun V : {V // V ∈ S} => Φf V.1 V.2)) hΦ

  have hconst : algebraMap W (UVCrossingModel W (π ^ E)) π = const (π ^ E) π := rfl
  have hreidx := BranchReindex.finsum_finrank_quotient_mk_eq (W := W)
    (Ideal.map (ι.toRingHom.comp (algebraMap ↥(R.nodeIntegersOver K w)
      (AdicCompletion (IsLocalRing.maximalIdeal ↥(R.nodeIntegersOver K w)) ↥(R.nodeIntegersOver K w)))) 𝔮)
    π (U (π ^ E) * αU) r p (const (π ^ E) π) (by rw [← hconst, Ideal.Quotient.mk_algebraMap]) x₀ hx₀.symm
  calc (S.card : ℕ∞) = ((S.attach.image (fun V : {V // V ∈ S} => Φf V.1 V.2)).card : ℕ∞) := by rw [hcard]
    _ ≤ _ := hcount
    _ = _ := hreidx

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finsum_finrank_quotient_map_of_xDepth_pow_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_card_le_finsum_finrank_quotient_map_of_xDepth_pow_eq (solution)
