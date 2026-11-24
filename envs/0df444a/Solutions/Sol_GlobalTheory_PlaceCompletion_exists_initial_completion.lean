-- Prove2me | solution 1 for GlobalTheory.PlaceCompletion.exists_initial_completion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:45:08.076649+00:00
-- url     : https://prove2.me/submissions/c9d6cfec-7d00-4d19-852d-07c4954cd186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_ModelAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAlgebraMapEqOfValVLeOne
import Theorems.Thm_GlobalTheory_PlaceCompletion_valV_algebraMap_of_isUnit
import Theorems.Thm_GlobalTheory_PlaceCompletion_valuation_of_irreducible
import Theorems.Thm_GlobalTheory_PlaceCompletion_overLa_one_of_irreducible
import Theorems.Thm_GlobalTheory_PlaceCompletion_valV_eq_pow_of_overLa
import Theorems.Thm_GlobalTheory_PlaceCompletion_exists_localHom_of_overLa
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_exists_extend_adicCompletion
import Theorems.Thm_GlobalTheory_isLocalHom_of_extend_adicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
namespace GlobalTheory.PlaceCompletion
open scoped WithZero
section Val
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
end Val
section Place
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K] (la : HeightOneSpectrum R)
variable {la} {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
private theorem maximalIdeal_adicCompletion_eq_span' {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) = Ideal.span {algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ} := by
  rw [AdicCompletion.maximalIdeal_eq_map, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Ideal.map_span, Set.image_singleton]
private theorem adicCompletion_eq_unit_mul_pow {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ϖ : A} (hϖ : Irreducible ϖ)
    (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (IsLocalRing.maximalIdeal A) A)ˣ), x = u * algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ ^ n := by
  have hpow : ∀ k, IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) ^ k =
      Ideal.span {algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ ^ k} := fun k => by
    rw [maximalIdeal_adicCompletion_eq_span' hϖ, Ideal.span_singleton_pow]
  have hex : ∃ N, x ∉ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) ^ N := by
    by_contra h
    push_neg at h
    apply hx
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)) inferInstance x fun n => ?_
    simpa [SModEq.zero] using h n
  classical
  have hN0 : Nat.find hex ≠ 0 := fun h0 => Nat.find_spec hex (by rw [h0, pow_zero]; rw [Ideal.one_eq_top]; trivial)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hxn : x ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) ^ n := by
    by_contra h
    exact Nat.find_min hex (by omega) h
  rw [hpow, Ideal.mem_span_singleton'] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hyu : IsUnit y := by
    by_contra hyn
    have hym : y ∈ IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) := (IsLocalRing.mem_maximalIdeal y).2 hyn
    rw [maximalIdeal_adicCompletion_eq_span' hϖ, Ideal.mem_span_singleton'] at hym
    obtain ⟨z, hz⟩ := hym
    have hN := Nat.find_spec hex
    rw [hn, hpow, Ideal.mem_span_singleton'] at hN
    exact hN ⟨z, by rw [← hy, ← hz, pow_succ]; ring⟩
  exact ⟨n, hyu.unit, by rw [IsUnit.unit_spec, hy]⟩
private theorem algebraMap_adicCompletion_injective' {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    Function.Injective (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := fun _ _ h =>
  AdicCompletion.of_injective (IsLocalRing.maximalIdeal A) A h
private theorem isDomain_adicCompletion_of_dvr' {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hp : ∀ k, algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ ^ k ≠ 0 := fun k h => by
    rw [← map_pow] at h
    exact pow_ne_zero k hϖ.ne_zero (algebraMap_adicCompletion_injective' (by rw [h, map_zero]))
  have hnzd : NoZeroDivisors (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨n, u, rfl⟩ := adicCompletion_eq_unit_mul_pow hϖ a hne.1
    obtain ⟨m, v, rfl⟩ := adicCompletion_eq_unit_mul_pow hϖ b hne.2
    apply hp (n + m)
    have h2 : ((u * v : (AdicCompletion (IsLocalRing.maximalIdeal A) A)ˣ) : AdicCompletion (IsLocalRing.maximalIdeal A) A) * algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ ^ (n + m) = 0 := by
      rw [← hab, Units.val_mul, pow_add]
      ring
    exact (Units.mul_right_eq_zero (u * v)).1 h2
  exact NoZeroDivisors.to_isDomain _
private theorem irreducible_algebraMap_adicCompletion' {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)] {ϖ : A} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (fun h => hϖ.ne_zero (algebraMap_adicCompletion_injective' (by rw [h, map_zero])))
    (maximalIdeal_adicCompletion_eq_span' hϖ)
private theorem isDVR_adicCompletion_of_isDomain {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)] :
    IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) ϖ, irreducible_algebraMap_adicCompletion' hϖ, fun {x} hx => ?_⟩
  obtain ⟨n, u, rfl⟩ := adicCompletion_eq_unit_mul_pow hϖ x hx
  exact ⟨n, u, mul_comm _ _⟩
end Place
end GlobalTheory.PlaceCompletion
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open GlobalTheory GlobalTheory.PlaceCompletion
open scoped WithZero
namespace GlobalTheory.PlaceCompletion
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)), ∃ (T₀ : CDVR) (io₀ : K →+* T₀.Fr), OverLa la T₀.V io₀ 1 ∧ T₀.FinRes ∧ ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∃ (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr), IsLocalHom g ∧ χ.comp io₀ = io ∧ χ.comp (algebraMap T₀.V T₀.Fr) = (algebraMap T.V T.Fr).comp g ∧ ∀ ϖ : T₀.V, Irreducible ϖ → vV (K' := T.Fr) T.V (algebraMap T.V T.Fr (g ϖ)) = e := by
  intro K _ _ la
  have := la.isPrime
  have := la.isMaximal
  have hdvr : IsDiscreteValuationRing (la.valuationSubringAtPrime K) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) la.ne_bot _
  have hdom : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) := isDomain_adicCompletion_of_dvr'
  have hcdvr : IsDiscreteValuationRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) := isDVR_adicCompletion_of_isDomain
  have hch : CharZero (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) := by
    have : CharZero (la.valuationSubringAtPrime K) :=
      (RingHom.charZero_iff (ϕ := (la.valuationSubringAtPrime K).subtype) Subtype.val_injective).2 inferInstance
    exact (RingHom.charZero_iff (ϕ := algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K))) algebraMap_adicCompletion_injective').1 inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (la.valuationSubringAtPrime K)
  have hpπ := irreducible_algebraMap_adicCompletion' (A := la.valuationSubringAtPrime K) hπ
  have hinj : Function.Injective ((algebraMap (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)))).comp
      (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)))) :=
    (IsFractionRing.injective (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) (FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)))).comp algebraMap_adicCompletion_injective'
  obtain ⟨io₀, hio₀⟩ : ∃ f : K →+* FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)), ∀ x : la.valuationSubringAtPrime K,
      f (algebraMap (la.valuationSubringAtPrime K) K x) = algebraMap (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) _ (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) x) :=
    ⟨IsFractionRing.lift hinj, fun x => IsFractionRing.lift_algebraMap hinj x⟩
  refine ⟨{ V := AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K) }, io₀, ?_, ?_, ?_⟩
  · exact overLa_one_of_irreducible io₀ (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K))) (fun x => (hio₀ x).symm) hπ hpπ
  · haveI : Finite (IsLocalRing.ResidueField (la.valuationSubringAtPrime K)) :=
      Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal la.asIdeal (la.valuationSubringAtPrime K)).toEquiv
    exact Finite.of_surjective _ (AdicCompletion.residueField_map_bijective (la.valuationSubringAtPrime K)).2
  intro T io e hT
  obtain ⟨o, ho, hloc⟩ := exists_localHom_of_overLa hT
  have hk : (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)).map o ^ 1 ≤ IsLocalRing.maximalIdeal T.V := by
    rw [pow_one, Ideal.map_le_iff_le_comap]
    exact fun x hx => hloc x hx
  obtain ⟨g, hg, -⟩ := exists_extend_adicCompletion o (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K))
    (IsLocalRing.maximalIdeal T.V) hk
  have hoLoc : IsLocalHom o := ⟨fun a ha => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).1 (hloc a ((IsLocalRing.mem_maximalIdeal a).2 h)) ha⟩
  have hgLoc : IsLocalHom g := by
    have : IsLocalHom (g.comp (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)))) := by rw [hg]; exact hoLoc
    exact isLocalHom_of_extend_adicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)).fg_of_isNoetherianRing g
  have hgπ : g (algebraMap (la.valuationSubringAtPrime K) (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) π) = o π := by rw [← RingHom.comp_apply, hg]
  have hoπ : o π ≠ 0 := fun h0 => by
    have h1 := ho π
    rw [h0, map_zero] at h1
    exact hπ.ne_zero (Subtype.ext ((map_eq_zero io).1 h1.symm))
  have ginj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, u, rfl⟩ := adicCompletion_eq_unit_mul_pow hπ x hx0
    rw [map_mul, map_pow, hgπ] at hx
    exact pow_ne_zero n hoπ ((IsUnit.mul_right_eq_zero (u.isUnit.map g)).1 hx)
  have hginj : Function.Injective ((algebraMap T.V T.Fr).comp g) :=
    (IsFractionRing.injective T.V T.Fr).comp ginj
  obtain ⟨χ, hχ⟩ : ∃ χ : FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) →+* T.Fr, ∀ y,
      χ (algebraMap (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) _ y) = algebraMap T.V T.Fr (g y) :=
    ⟨IsFractionRing.lift (A := AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) (K := FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K))) hginj,
      fun y => IsFractionRing.lift_algebraMap (A := AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K)) (K := FractionRing (AdicCompletion (IsLocalRing.maximalIdeal (la.valuationSubringAtPrime K)) (la.valuationSubringAtPrime K))) hginj y⟩
  refine ⟨g, χ, hgLoc, ?_, RingHom.ext hχ, ?_⟩
  · refine IsLocalization.ringHom_ext (nonZeroDivisors (la.valuationSubringAtPrime K)) (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    rw [hio₀, hχ, ← RingHom.comp_apply g, hg]
    exact ho x
  · intro ϖ hϖ
    obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hpπ hϖ
    unfold vV
    rw [map_mul, map_mul, map_mul, hgπ, valV_algebraMap_of_isUnit ((u.isUnit).map g), _root_.mul_one,
      ho π, valV_eq_pow_of_overLa hT, valuation_of_irreducible la hπ, ← WithZero.exp_nsmul,
      WithZero.log_exp]
    simp
end GlobalTheory.PlaceCompletion
