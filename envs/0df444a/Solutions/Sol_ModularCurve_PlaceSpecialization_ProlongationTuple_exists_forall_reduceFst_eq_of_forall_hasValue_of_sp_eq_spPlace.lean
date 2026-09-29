-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_forall_reduceFst_eq_of_forall_hasValue_of_sp_eq_spPlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/90ee7606-2401-5513-ae2d-c6c68621b6f6

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap
import Theorems.Thm_ModularCurve_finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_separable_phi_map
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_coe_piFin_eq_coeffRed
import Theorems.Thm_ModularCurve_mem_integralCoeffs_of_integral_affineBaseFin
import Theorems.Thm_ModularCurve_exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_reduceFst_eq_of_forall_hasValue_of_sp_eq_spPlace
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_reduceFst_eq_of_forall_hasValue_of_sp_eq_spPlace.ModularCurve"
open ModularCurve.NodeLocalized ModularCurve.CharPModel
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open Polynomial IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar jq ModularPolynomialData modularFunctionFieldFull coeffMap coeffMap_coeff coeffMap_coeffMap coeffEmb laurentBaseChange jqModC jqModC_rat modularFunctionFieldC PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence IsSupersingularPlace ssPlaces IsSupersingularPlace.isCentreOf_evalAt jGeomGen jGeomGen_sub_algebraMap_ne_zero IsAffineGeomPlace transcendental_jqModC coeffMap_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed_coeff CharPModel.FibreModel finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC isSeparable_jqNModC_of_separable_phi_map transcendental_coeffEmb_jq mem_integralCoeffs_of_integral_affineBaseFin exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin"
namespace C5SpecNq
p2m_open "ModularCurve"

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {j : F}

theorem isPrincipalIdealRing_adjoin_singleton (hj : Transcendental K j) :
    IsPrincipalIdealRing (Algebra.adjoin K ({j} : Set F)) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental K j hj).toRingHom
    (Polynomial.algEquivOfTranscendental K j hj).surjective

theorem isDedekindDomain_adjoin_singleton (hj : Transcendental K j) :
    IsDedekindDomain (Algebra.adjoin K ({j} : Set F)) :=
  haveI := isPrincipalIdealRing_adjoin_singleton hj
  inferInstance

theorem isDedekindDomain_integralClosure_adjoin (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F] [Algebra.IsSeparable K⟮j⟯ F] :
    IsDedekindDomain (integralClosure (Algebra.adjoin K ({j} : Set F)) F) :=
  haveI := isDedekindDomain_adjoin_singleton hj
  integralClosure.isDedekindDomain (Algebra.adjoin K ({j} : Set F)) K⟮j⟯ F

theorem isFractionRing_integralClosure_adjoin (hj : Transcendental K j) [FiniteDimensional K⟮j⟯ F] :
    IsFractionRing (integralClosure (Algebra.adjoin K ({j} : Set F)) F) F :=
  haveI := isDedekindDomain_adjoin_singleton hj
  integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin K ({j} : Set F)) K⟮j⟯ F

theorem integralClosure_adjoin_le_valuationSubring (O : ValuationSubring F)
    (hK : ∀ c : K, algebraMap K F c ∈ O) (hjO : j ∈ O)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) : (r : F) ∈ O := by
  let O' : Subalgebra K F :=
    { O.toSubring with
      algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({j} : Set F) ≤ O' :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjO)
  let φ : Algebra.adjoin K ({j} : Set F) →+* O :=
    (Subalgebra.val _).toRingHom.codRestrict O.toSubring (fun y => hle y.2)
  obtain ⟨p, hp, hpr⟩ : IsIntegral (Algebra.adjoin K ({j} : Set F)) (r : F) := r.2
  have hint : IsIntegral O (r : F) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [eval₂_map]
    exact hpr
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

theorem exists_monic_of_mem_integralClosure_adjoin (S : Subring F)
    (hK : ∀ c : K, algebraMap K F c ∈ S) (hjS : j ∈ S)
    (r : integralClosure (Algebra.adjoin K ({j} : Set F)) F) :
    ∃ p : Polynomial S, p.Monic ∧ Polynomial.eval₂ S.subtype (r : F) p = 0 := by
  let S' : Subalgebra K F :=
    { S with
      algebraMap_mem' := hK }
  have hle : Algebra.adjoin K ({j} : Set F) ≤ S' :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjS)
  let φ : Algebra.adjoin K ({j} : Set F) →+* S :=
    (Subalgebra.val _).toRingHom.codRestrict S (fun y => hle y.2)
  obtain ⟨p, hp, hpr⟩ : IsIntegral (Algebra.adjoin K ({j} : Set F)) (r : F) := r.2
  refine ⟨p.map φ, hp.map φ, ?_⟩
  rw [eval₂_map]
  exact hpr

theorem place_eq_of_forall_integral_mem_nonunits (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F] [Algebra.IsSeparable K⟮j⟯ F]
    (Q₁ Q₂ : Place K F) (hj₁ : j ∈ Q₁.toValuationSubring) (hj₂ : j ∈ Q₂.toValuationSubring)
    (h : ∀ r : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      (r : F) ∈ Q₂.toValuationSubring.nonunits → (r : F) ∈ Q₁.toValuationSubring.nonunits) :
    Q₁ = Q₂ := by
  haveI := isDedekindDomain_integralClosure_adjoin (F := F) hj
  haveI := isFractionRing_integralClosure_adjoin (F := F) hj
  have hw₁ : ∀ r : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      algebraMap _ F r ∈ Q₁.toValuationSubring :=
    fun r => integralClosure_adjoin_le_valuationSubring _ Q₁.algebraMap_mem' hj₁ r
  have hw₂ : ∀ r : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      algebraMap _ F r ∈ Q₂.toValuationSubring :=
    fun r => integralClosure_adjoin_le_valuationSubring _ Q₂.algebraMap_mem' hj₂ r
  have hle : Place.center _ Q₂ hw₂ ≤ Place.center _ Q₁ hw₁ := by
    intro r hr
    rw [Place.mem_center_iff] at hr ⊢
    exact ValuationSubring.coe_mem_nonunits_iff.mp (h r (ValuationSubring.coe_mem_nonunits_iff.mpr hr))
  have hmax : (Place.center _ Q₂ hw₂).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime (Place.center_ne_bot Q₂ hw₂) inferInstance
  have hne : Place.center _ Q₁ hw₁ ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have heq : Place.center _ Q₂ hw₂ = Place.center _ Q₁ hw₁ := hmax.eq_of_le hne hle
  have hc : Place.centerHeightOneSpectrum _ Q₁ hw₁ = Place.centerHeightOneSpectrum _ Q₂ hw₂ := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [Place.centerHeightOneSpectrum_asIdeal, Place.centerHeightOneSpectrum_asIdeal, heq]
  apply Place.ext
  rw [Place.toValuationSubring_eq_of_forall_mem Q₁ hw₁, Place.toValuationSubring_eq_of_forall_mem Q₂ hw₂, hc]

theorem exists_mem_forall_isMaximal_mem_imp_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    (m : Ideal R) [hm : m.IsMaximal] {r₀ : R} (hr₀ : r₀ ≠ 0) (hr₀m : r₀ ∈ m) :
    ∃ u ∈ m, ∀ P : Ideal R, P.IsMaximal → r₀ ∈ P → u ∈ P → P = m := by
  classical
  have hfin : {v : IsDedekindDomain.HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {r₀}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hr₀)
  let T : Finset (IsDedekindDomain.HeightOneSpectrum R) := hfin.toFinset.filter fun v => v.asIdeal ≠ m
  have hnot : ¬ ((m : Set R) ⊆ ⋃ v ∈ (↑T : Set (IsDedekindDomain.HeightOneSpectrum R)), (v.asIdeal : Set R)) := by
    intro hsub
    rcases T.eq_empty_or_nonempty with hT | ⟨v₀, hv₀⟩
    · have : (r₀ : R) ∈ ⋃ v ∈ (↑T : Set (IsDedekindDomain.HeightOneSpectrum R)), (v.asIdeal : Set R) :=
        hsub hr₀m
      rw [hT] at this
      simp at this
    · have hprime : ∀ v ∈ T, (v.asIdeal).IsPrime := fun v _ => v.isPrime
      obtain ⟨v, hvT, hmv⟩ := (Ideal.subset_union_prime v₀ v₀ (fun v hv _ _ => hprime v hv)).mp hsub
      have hvne : v.asIdeal ≠ m := (Finset.mem_filter.mp hvT).2
      exact hvne ((hm.eq_of_le v.isPrime.ne_top hmv).symm)
  obtain ⟨u, hum, hu⟩ := Set.not_subset.mp hnot
  refine ⟨u, hum, fun P hP hr₀P huP => ?_⟩
  by_contra hPm
  have hPbot : P ≠ ⊥ := fun h => hr₀ (by rw [h] at hr₀P; exact (Ideal.mem_bot).mp hr₀P)
  let v : IsDedekindDomain.HeightOneSpectrum R := ⟨P, hP.isPrime, hPbot⟩
  have hvT : v ∈ T := by
    refine Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr ?_, hPm⟩
    show P ∣ Ideal.span {r₀}
    rw [Ideal.dvd_span_singleton]
    exact hr₀P
  apply hu
  simp only [Set.mem_iUnion, Finset.mem_coe]
  exact ⟨v, hvT, huP⟩

theorem exists_separator (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F] [Algebra.IsSeparable K⟮j⟯ F]
    (Q₂ : Place K F) (hj₂ : j ∈ Q₂.toValuationSubring) (a : K)
    (ha₂ : (j - algebraMap K F a) ∈ Q₂.toValuationSubring.nonunits) :
    ∃ u : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      (u : F) ∈ Q₂.toValuationSubring.nonunits ∧
      ∀ Q₁ : Place K F, j ∈ Q₁.toValuationSubring →
        (j - algebraMap K F a) ∈ Q₁.toValuationSubring.nonunits →
        (u : F) ∈ Q₁.toValuationSubring.nonunits → Q₁ = Q₂ := by
  haveI := isDedekindDomain_integralClosure_adjoin (F := F) hj
  haveI := isFractionRing_integralClosure_adjoin (F := F) hj
  have hw₂ : ∀ r : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      algebraMap _ F r ∈ Q₂.toValuationSubring :=
    fun r => integralClosure_adjoin_le_valuationSubring _ Q₂.algebraMap_mem' hj₂ r
  haveI hm : (Place.center _ Q₂ hw₂).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime (Place.center_ne_bot Q₂ hw₂) inferInstance

  have hj₀mem : (j - algebraMap K F a) ∈ integralClosure (Algebra.adjoin K ({j} : Set F)) F := by
    refine sub_mem ?_ ?_
    · rw [mem_integralClosure_iff]
      exact isIntegral_algebraMap (R := Algebra.adjoin K ({j} : Set F))
        (x := ⟨j, Algebra.subset_adjoin (Set.mem_singleton _)⟩)
    · rw [IsScalarTower.algebraMap_apply K (Algebra.adjoin K ({j} : Set F)) F a]
      exact Subalgebra.algebraMap_mem _ _
  obtain ⟨j₀, hj₀val⟩ : ∃ j₀ : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      (j₀ : F) = j - algebraMap K F a := ⟨⟨_, hj₀mem⟩, rfl⟩
  have hjne : (j - algebraMap K F a) ≠ 0 :=
    sub_ne_zero.mpr fun h => hj (h ▸ isAlgebraic_algebraMap a)
  have hj₀0 : j₀ ≠ 0 := by
    intro h
    apply hjne
    rw [← hj₀val, h, ZeroMemClass.coe_zero]
  have hj₀m : j₀ ∈ Place.center _ Q₂ hw₂ := by
    rw [Place.mem_center_iff]
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    show (j₀ : F) ∈ _
    rw [hj₀val]
    exact ha₂
  obtain ⟨u, hum, hu⟩ := exists_mem_forall_isMaximal_mem_imp_eq (Place.center _ Q₂ hw₂) hj₀0 hj₀m
  refine ⟨u, ?_, fun Q₁ hj₁ ha₁ hu₁ => ?_⟩
  · have := (Place.mem_center_iff Q₂ hw₂).mp hum
    exact ValuationSubring.coe_mem_nonunits_iff.mpr this
  have hw₁ : ∀ r : integralClosure (Algebra.adjoin K ({j} : Set F)) F,
      algebraMap _ F r ∈ Q₁.toValuationSubring :=
    fun r => integralClosure_adjoin_le_valuationSubring _ Q₁.algebraMap_mem' hj₁ r
  have hc₁max : (Place.center _ Q₁ hw₁).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime (Place.center_ne_bot Q₁ hw₁) inferInstance
  have hj₀c₁ : j₀ ∈ Place.center _ Q₁ hw₁ := by
    rw [Place.mem_center_iff]
    apply ValuationSubring.coe_mem_nonunits_iff.mp
    show (j₀ : F) ∈ _
    rw [hj₀val]
    exact ha₁
  have huc₁ : u ∈ Place.center _ Q₁ hw₁ := by
    rw [Place.mem_center_iff]
    exact ValuationSubring.coe_mem_nonunits_iff.mp hu₁
  have hc : Place.center _ Q₁ hw₁ = Place.center _ Q₂ hw₂ := hu _ hc₁max hj₀c₁ huc₁
  refine place_eq_of_forall_integral_mem_nonunits hj Q₁ Q₂ hj₁ hj₂ (fun r hr => ?_)
  have hr₂ : r ∈ Place.center _ Q₂ hw₂ := by
    rw [Place.mem_center_iff]
    exact ValuationSubring.coe_mem_nonunits_iff.mp hr
  rw [← hc, Place.mem_center_iff] at hr₂
  exact ValuationSubring.coe_mem_nonunits_iff.mpr hr₂

end Generic

section FibreField

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}

theorem transcendental_jGeomGen (k : Type*) [Field k] (N : ℕ) [NeZero N] :
    Transcendental k (jGeomGen k N : modularFunctionFieldC k N) := by
  have hinj : Function.Injective (algebraMap (modularFunctionFieldC k N) (LaurentSeries k)) :=
    Subtype.val_injective
  exact (transcendental_algebraMap_iff hinj).mp (transcendental_jqModC k)

theorem exists_piFin_eq_of_mem_integralClosure (fm : FibreModel N A q k red)
    (hred : Function.Surjective red)
    (r : integralClosure (Algebra.adjoin k ({(jGeomGen k N : modularFunctionFieldC k N)} :
        Set (modularFunctionFieldC k N))) (modularFunctionFieldC k N)) :
    ∃ b : fm.BFin, fm.piFin b = (r : modularFunctionFieldC k N) := by
  have hK : ∀ c : k, algebraMap k (modularFunctionFieldC k N) c ∈ fm.piFin.range := by
    intro c
    obtain ⟨a, rfl⟩ := hred c
    exact ⟨⟨constantsHom N A a, fm.constFin_mem a⟩, fm.piFin_const a⟩
  have hjS : (jGeomGen k N : modularFunctionFieldC k N) ∈ fm.piFin.range :=
    ⟨⟨jBar N, fm.jBar_mem⟩, fm.piFin_j⟩
  obtain ⟨p, hp, heval⟩ := exists_monic_of_mem_integralClosure_adjoin fm.piFin.range hK hjS r
  obtain ⟨b, hb⟩ := fm.intClosed_piFin _ ⟨p, hp, heval⟩
  exact ⟨b, hb⟩

theorem hasValue_zero_iff_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (g : F) : v.HasValue g 0 ↔ g ∈ v.toValuationSubring.nonunits := by
  constructor
  · rintro ⟨h, hres⟩
    rw [map_zero] at hres
    exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hres)
  · intro h
    have hmem : g ∈ v.toValuationSubring := v.toValuationSubring.nonunits_subset h
    refine ⟨hmem, ?_⟩
    rw [map_zero]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (ValuationSubring.coe_mem_nonunits_iff.mp h)

end FibreField

section CharZero

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}

theorem jBar_sub_algebraMap_ne_zero (c : AlgebraicClosure ℚ) :
    jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c ≠ 0 := by
  refine sub_ne_zero.mpr fun heq => ?_
  have htr : Transcendental (AlgebraicClosure ℚ) (jBar N : modularFunctionFieldBar N) := by
    show Transcendental (AlgebraicClosure ℚ)
      (⟨coeffEmb (AlgebraicClosure ℚ) jq, _⟩ : modularFunctionFieldBar N)
    exact transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  exact htr (heq ▸ isAlgebraic_algebraMap c)

theorem ord_pos_of_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F] (P : Place K F) {x : F}
    (hx0 : x ≠ 0) (h : x ∈ P.toValuationSubring.nonunits) : 0 < P.ord x := by
  have hmem : x ∈ P.toValuationSubring := P.toValuationSubring.nonunits_subset h
  exact (P.mem_maximalIdeal_iff_ord_pos hx0 hmem).mp (ValuationSubring.coe_mem_nonunits_iff.mp h)

theorem jGeomGen_mem_spPlace (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a₀ : A)
    (ha₀ : 0 < P.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a₀ : AlgebraicClosure ℚ))) :
    (jGeomGen k N : modularFunctionFieldC k N) ∈ (fm.spPlace hred dataAll hsep P).toValuationSubring := by
  set Q := fm.spPlace hred dataAll hsep P with hQdef
  have hmem_b : (jBar N - constantsHom N A a₀) ∈ fm.BFin := sub_mem fm.jBar_mem (fm.constFin_mem a₀)
  set b : fm.BFin := ⟨jBar N - constantsHom N A a₀, hmem_b⟩ with hb_def
  have hconst : constantsHom N A a₀
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ) := rfl
  have hrhs : ∃ a : A, a ∈ maximalIdeal A ∧
      ((b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) -
          algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionFieldFull N)) (a : AlgebraicClosure ℚ))
        ∈ P.toValuationSubring.nonunits := by
    refine ⟨0, zero_mem _, ?_⟩
    simp only [ZeroMemClass.coe_zero, map_zero, sub_zero]
    show (jBar N - constantsHom N A a₀) ∈ P.toValuationSubring.nonunits
    rw [hconst]
    have hx0 := jBar_sub_algebraMap_ne_zero (N := N) (a₀ : AlgebraicClosure ℚ)
    have hmem : (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        (a₀ : AlgebraicClosure ℚ)) ∈ P.toValuationSubring :=
      P.mem_of_ord_nonneg hx0 (le_of_lt ha₀)
    exact ValuationSubring.coe_mem_nonunits_iff.mpr ((P.mem_maximalIdeal_iff_ord_pos hx0 hmem).mpr ha₀)
  have hlhs : (fm.piFin b : modularFunctionFieldC k N) ∈ Q.toValuationSubring.nonunits :=
    (FibreModel.piFin_mem_spPlace_nonunits_iff fm hred dataAll hsep P a₀ ha₀ b).mpr hrhs
  have hpi : fm.piFin b = (jGeomGen k N : modularFunctionFieldC k N)
        - algebraMap k (modularFunctionFieldC k N) (red a₀) := by
    have : b = (⟨jBar N, fm.jBar_mem⟩ : fm.BFin) - ⟨constantsHom N A a₀, fm.constFin_mem a₀⟩ := rfl
    rw [this, map_sub, fm.piFin_j, fm.piFin_const]
    rfl
  rw [hpi] at hlhs
  have h1 := Q.toValuationSubring.nonunits_subset hlhs
  have h2 : algebraMap k (modularFunctionFieldC k N) (red a₀) ∈ Q.toValuationSubring := Q.algebraMap_mem' _
  have := add_mem h1 h2
  simpa using this

theorem piFin_mem_spPlace_nonunits (fm : FibreModel N A q k red) (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (a₀ : A)
    (ha₀ : 0 < P.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      (a₀ : AlgebraicClosure ℚ)))
    (b : fm.BFin) (a : A) (ha : a ∈ maximalIdeal A)
    (hb : ((b : modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a : AlgebraicClosure ℚ))
      ∈ P.toValuationSubring.nonunits) :
    (fm.piFin b : modularFunctionFieldC k N) ∈ (fm.spPlace hred dataAll hsep P).toValuationSubring.nonunits :=
  (FibreModel.piFin_mem_spPlace_nonunits_iff fm hred dataAll hsep P a₀ ha₀ b).mpr ⟨a, ha, hb⟩

theorem sub_mem_nonunits_restrictAlong_of_hasValue
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (g : modularFunctionFieldBar N) (c : AlgebraicClosure ℚ)
    (h : W.HasValue (heckeAlphaBar (AlgebraicClosure ℚ) N q g) c) :
    (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) ∈
      (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).toValuationSubring.nonunits := by
  obtain ⟨hmemW, hres⟩ := h
  by_cases h0 : g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c = 0
  · rw [h0]
    have := (ValuationSubring.coe_mem_nonunits_iff
      (a := (0 : (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).toValuationSubring))).mpr
      (zero_mem _)
    simpa using this

  have hsubW : (heckeAlphaBar (AlgebraicClosure ℚ) N q g
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c) ∈ W.toValuationSubring :=
    sub_mem hmemW (W.algebraMap_mem' c)
  have hmaxW : (⟨_, hsubW⟩ : W.toValuationSubring) ∈ maximalIdeal W.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have e1 : (⟨_, hsubW⟩ : W.toValuationSubring) =
        ⟨heckeAlphaBar (AlgebraicClosure ℚ) N q g, hmemW⟩
          - ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c, W.algebraMap_mem' c⟩ := rfl
    rw [e1, map_sub, hres, sub_eq_zero]
    exact (W.residue_algebraMap c).symm
  have hαsub : heckeAlphaBar (AlgebraicClosure ℚ) N q (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
      = heckeAlphaBar (AlgebraicClosure ℚ) N q g
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c := by
    rw [map_sub, AlgHom.commutes]
  have hne : heckeAlphaBar (AlgebraicClosure ℚ) N q g
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c ≠ 0 := by
    rw [← hαsub]
    exact fun h => h0 ((map_eq_zero_iff _ (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.injective).mp h)
  have hordW : 0 < W.ord (heckeAlphaBar (AlgebraicClosure ℚ) N q g
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) c) :=
    (W.mem_maximalIdeal_iff_ord_pos hne hsubW).mp hmaxW

  have hord := Place.ord_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα W
    (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)
  rw [hαsub] at hord
  rw [hord] at hordW
  have hVpos : 0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).ord
      (g - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c) :=
    pos_of_mul_pos_right hordW (by exact_mod_cast Nat.zero_le _)
  have hmemV := (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).mem_of_ord_nonneg h0 hVpos.le
  exact ValuationSubring.coe_mem_nonunits_iff.mpr
    (((W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).mem_maximalIdeal_iff_ord_pos h0 hmemV).mpr hVpos)

def packA (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : x ∈ CharPReduction.integralCoeffs A.toSubring) : LaurentSeries A where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (fun _ hn h => hn (Subtype.ext h))

theorem packA_coeff (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : x ∈ CharPReduction.integralCoeffs A.toSubring) (n : ℤ) :
    ((packA (A := A) x hx).coeff n : AlgebraicClosure ℚ) = x.coeff n := rfl

theorem coeffMap_subtype_packA (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : x ∈ CharPReduction.integralCoeffs A.toSubring) :
    coeffMap A.subtype (packA x hx) = x := by
  ext n
  rw [coeffMap_coeff]
  exact packA_coeff x hx n

theorem exists_residue₁_heckeAlphaBar_eq_piFin
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ h₁ : heckeAlphaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) ∈ R.R₁.integers,
      R.residue₁ ⟨_, h₁⟩ = fm.piFin b := by
  have hmem : ((b : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.integralCoeffs A.toSubring :=
    mem_integralCoeffs_of_integral_affineBaseFin A N b (fm.integralFin b)

  have hcoeα : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = ((b : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) :=
    coe_heckeAlphaBar N q (b : modularFunctionFieldBar N)
  have hyb : coeffMap A.subtype (packA _ hmem)
      = ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) :
          modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    (coeffMap_subtype_packA _ hmem).trans hcoeα.symm
  have hy : coeffMap A.subtype (packA _ hmem) ∈ modularFunctionFieldBar (N * q) := by
    rw [hyb]
    exact (heckeAlphaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N)).2
  obtain ⟨hint, hres⟩ := R.residue₁_coeffMap (packA _ hmem) hy
  have helt : (⟨coeffMap A.subtype (packA _ hmem), hy⟩ : modularFunctionFieldBar (N * q))
      = heckeAlphaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) := Subtype.ext hyb
  have h₁ : heckeAlphaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N) ∈ R.R₁.integers := helt ▸ hint
  refine ⟨h₁, ?_⟩
  have eR : (⟨heckeAlphaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N), h₁⟩ : R.R₁.integers)
      = ⟨⟨coeffMap A.subtype (packA _ hmem), hy⟩, hint⟩ := Subtype.ext helt.symm
  apply Subtype.ext
  rw [residue₁_apply, eR, R.ι_coe, hres, coeffMap_coeffMap,
    FibreModel.coe_piFin_eq_coeffRed N A q k red fm b hmem]
  have hcomp : R.redBar.comp (IsLocalRing.residue A) = red := RingHom.ext R.redBar_residue
  rw [hcomp]
  ext n
  rw [coeffMap_coeff, CharPReduction.coeffRed_coeff]
  rfl

theorem heckeAlphaBar_constantsHom (a : A) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (constantsHom N A a) = constantsHom (N * q) A a :=
  AlgHom.commutes _ _

theorem heckeAlphaBar_jBar :
    heckeAlphaBar (AlgebraicClosure ℚ) N q (jBar N) = jBar (N * q) :=
  Subtype.ext rfl

theorem heckeAlphaBar_mem_affineBaseFin {x : modularFunctionFieldBar N} (hx : x ∈ affineBaseFin N A) :
    heckeAlphaBar (AlgebraicClosure ℚ) N q x ∈ affineBaseFin (N * q) A := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | hx
      · rw [heckeAlphaBar_constantsHom]
        exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [heckeAlphaBar_jBar]
        exact Subring.subset_closure (Or.inr rfl)
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_monic_affineBaseFin_heckeAlphaBar (fm : FibreModel N A q k red) (b : fm.BFin) :
    ∃ p : Polynomial (affineBaseFin (N * q) A), p.Monic ∧
      Polynomial.eval₂ (affineBaseFin (N * q) A).subtype
        (heckeAlphaBar (AlgebraicClosure ℚ) N q (b : modularFunctionFieldBar N)) p = 0 := by
  obtain ⟨p, hp, heval⟩ := fm.integralFin b
  let φ : affineBaseFin N A →+* affineBaseFin (N * q) A :=
    ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.comp (affineBaseFin N A).subtype).codRestrict
      (affineBaseFin (N * q) A) (fun x => heckeAlphaBar_mem_affineBaseFin x.2)
  refine ⟨p.map φ, hp.map φ, ?_⟩
  rw [eval₂_map]
  have hcomp : (affineBaseFin (N * q) A).subtype.comp φ
      = (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.comp (affineBaseFin N A).subtype :=
    RingHom.ext fun x => rfl
  rw [hcomp]
  have h2 := Polynomial.hom_eval₂ p (affineBaseFin N A).subtype
    (heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom (b : modularFunctionFieldBar N)
  rw [heval, map_zero] at h2
  exact h2.symm

end CharZero

section Main

theorem coe_jBar_eq_jqModC (M : ℕ) [NeZero M] :
    ((jBar M : modularFunctionFieldBar M) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq = jqModC (AlgebraicClosure ℚ)
  rw [← jqModC_rat]
  exact coeffMap_jqModC _

theorem main
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (fm : CharPModel.FibreModel N A q k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hP : P.sp = fm.spPlace hred dataAll hsep)
    (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K →
      ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
        ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ K'' → K' ≤ K'' →
          ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            (∀ (t : ↥(modularFunctionFieldBar (N * q)))
                (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K''),
                ∃ a : A, W.HasValue t (a : AlgebraicClosure ℚ) ∧
                  ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
                    a ∈ IsLocalRing.maximalIdeal A)) →
            P.reduceFst W = w := by
  intro K hKfd
  classical
  haveI := hKfd

  have haff : IsAffineGeomPlace k N w := hw.2.1
  have hcen := IsSupersingularPlace.isCentreOf_evalAt hw
  have hjw : (jGeomGen k N : modularFunctionFieldC k N) ∈ w.toValuationSubring := haff.1
  have hordw : 0 < w.ord ((jGeomGen k N : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N))) := hcen.1
  have hj0ne : ((jGeomGen k N : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N))) ≠ 0 :=
    jGeomGen_sub_algebraMap_ne_zero k N _
  have hj0w : ((jGeomGen k N : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N))) ∈ w.toValuationSubring.nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr
      ((w.mem_maximalIdeal_iff_ord_pos hj0ne (sub_mem hjw (w.algebraMap_mem' _))).mpr hordw)

  obtain ⟨x₁, hx₁⟩ := hred (w.evalAt (jGeomGen k N))

  have hsepE := isSeparable_jqNModC_of_separable_phi_map k N (dataAll N (dvd_refl N)) hsep
  obtain ⟨hFD, hSep⟩ := finiteDimensional_and_isSeparable_adjoin_jGeomGen_of_isSeparable_jqNModC
    k N (dataAll N (dvd_refl N)) hsepE
  haveI hFD' : FiniteDimensional k⟮(jGeomGen k N : modularFunctionFieldC k N)⟯ (modularFunctionFieldC k N) := hFD
  haveI hSep' : Algebra.IsSeparable k⟮(jGeomGen k N : modularFunctionFieldC k N)⟯ (modularFunctionFieldC k N) := hSep
  have hjtr : Transcendental k (jGeomGen k N : modularFunctionFieldC k N) := transcendental_jGeomGen k N

  obtain ⟨u, huw, hcrit⟩ := exists_separator (F := modularFunctionFieldC k N) hjtr w hjw
    (w.evalAt (jGeomGen k N)) hj0w
  obtain ⟨bu, hbu⟩ := exists_piFin_eq_of_mem_integralClosure fm hred u

  obtain ⟨K₁, hK₁fd, hKK₁, hdesc⟩ := exists_forall_mem_jIntegralClosure_of_integral_affineBaseFin A N
    (heckeAlphaBar (AlgebraicClosure ℚ) N q (bu : modularFunctionFieldBar N))
    (exists_monic_affineBaseFin_heckeAlphaBar fm bu) K
  haveI := hK₁fd
  have hx₁int : IsIntegral ℚ (x₁ : AlgebraicClosure ℚ) := Algebra.IsIntegral.isIntegral _
  haveI hKxfd : FiniteDimensional ℚ ℚ⟮(x₁ : AlgebraicClosure ℚ)⟯ :=
    IntermediateField.adjoin.finiteDimensional hx₁int
  refine ⟨K₁ ⊔ ℚ⟮(x₁ : AlgebraicClosure ℚ)⟯, IntermediateField.finiteDimensional_sup _ _,
    le_trans hKK₁ le_sup_left, ?_⟩
  intro K'' hK''fd hle W hW
  haveI := hK''fd
  have hK₁le : K₁ ≤ K'' := le_trans le_sup_left hle
  have hx₁K : (x₁ : AlgebraicClosure ℚ) ∈ K'' :=
    hle ((le_sup_right : ℚ⟮(x₁ : AlgebraicClosure ℚ)⟯ ≤ K₁ ⊔ ℚ⟮(x₁ : AlgebraicClosure ℚ)⟯)
      (IntermediateField.mem_adjoin_simple_self ℚ _))

  show P.sp (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = w
  rw [hP]
  set V := W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα with hVdef

  have hb₀mem : (jBar N - constantsHom N A x₁) ∈ fm.BFin := sub_mem fm.jBar_mem (fm.constFin_mem x₁)
  obtain ⟨b₀, hb₀val⟩ : ∃ b₀ : fm.BFin, (b₀ : modularFunctionFieldBar N) = jBar N - constantsHom N A x₁ :=
    ⟨⟨_, hb₀mem⟩, rfl⟩
  have hconst : constantsHom N A x₁
      = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (x₁ : AlgebraicClosure ℚ) := rfl
  have hcoe_b₀ : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b₀ : modularFunctionFieldBar N) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ)
        - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (x₁ : AlgebraicClosure ℚ) := by

    rw [coe_heckeAlphaBar N q (b₀ : modularFunctionFieldBar N), hb₀val, hconst, AddSubgroupClass.coe_sub,
      coe_jBar_eq_jqModC]
    congr 1
  have ht₀ : ((heckeAlphaBar (AlgebraicClosure ℚ) N q (b₀ : modularFunctionFieldBar N) :
      modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K'' := by
    rw [hcoe_b₀]
    have hx₁A : (x₁ : AlgebraicClosure ℚ) ∈ coeffSubring A K'' := Subring.mem_inf.mpr ⟨x₁.2, hx₁K⟩
    have hmemR : jqModC (AlgebraicClosure ℚ)
        - algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (x₁ : AlgebraicClosure ℚ)
        ∈ jRing A K'' :=
      sub_mem (Subring.subset_closure (Or.inr rfl))
        (Subring.subset_closure (Or.inl ⟨⟨(x₁ : AlgebraicClosure ℚ), hx₁A⟩, rfl⟩))
    refine ⟨sub_mem (Subfield.subset_closure (Or.inr (Set.mem_insert _ _)))
      (Subfield.subset_closure (Or.inl ⟨⟨(x₁ : AlgebraicClosure ℚ), hx₁K⟩, rfl⟩)), ?_⟩
    exact isIntegral_algebraMap (R := jRing A K'') (x := ⟨_, hmemR⟩)
  obtain ⟨a₀, hWa₀, hiff₀⟩ := hW _ ht₀

  obtain ⟨h₁₀, hres₀⟩ := exists_residue₁_heckeAlphaBar_eq_piFin R fm b₀
  have hpi₀ : fm.piFin b₀ = (jGeomGen k N : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N)) := by
    have : b₀ = (⟨jBar N, fm.jBar_mem⟩ : fm.BFin) - ⟨constantsHom N A x₁, fm.constFin_mem x₁⟩ :=
      Subtype.ext (by rw [hb₀val]; rfl)
    rw [this, map_sub, fm.piFin_j, fm.piFin_const, hx₁]
    rfl
  have ha₀𝔪 : a₀ ∈ maximalIdeal A := by
    refine hiff₀.mp ⟨h₁₀, ?_⟩
    rw [hres₀, hpi₀]
    exact (hasValue_zero_iff_mem_nonunits w _).mpr hj0w
  have hVb₀ := sub_mem_nonunits_restrictAlong_of_hasValue (hα := hα) W (b₀ : modularFunctionFieldBar N)
    (a₀ : AlgebraicClosure ℚ) hWa₀

  have hanchor_eq : jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((x₁ + a₀ : A) : AlgebraicClosure ℚ)
      = (b₀ : modularFunctionFieldBar N)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (a₀ : AlgebraicClosure ℚ) := by
    rw [hb₀val, hconst, show ((x₁ + a₀ : A) : AlgebraicClosure ℚ) = (x₁ : AlgebraicClosure ℚ) + a₀ from rfl,
      map_add]
    ring
  have hanchor : 0 < V.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      ((x₁ + a₀ : A) : AlgebraicClosure ℚ)) := by
    rw [hanchor_eq]
    refine ord_pos_of_mem_nonunits V ?_ hVb₀
    rw [← hanchor_eq]
    exact jBar_sub_algebraMap_ne_zero _

  have hjQ₁ := jGeomGen_mem_spPlace fm hred dataAll hsep V (x₁ + a₀) hanchor
  have hjaQ₁ : ((jGeomGen k N : modularFunctionFieldC k N)
      - algebraMap k (modularFunctionFieldC k N) (w.evalAt (jGeomGen k N)))
      ∈ (fm.spPlace hred dataAll hsep V).toValuationSubring.nonunits := by
    have hpi := piFin_mem_spPlace_nonunits fm hred dataAll hsep V (x₁ + a₀) hanchor b₀ a₀ ha₀𝔪 hVb₀
    rwa [hpi₀] at hpi

  have ht_u := hdesc K'' hK''fd hK₁le
  obtain ⟨a_u, hWu, hiffu⟩ := hW _ ht_u
  obtain ⟨h₁u, hresu⟩ := exists_residue₁_heckeAlphaBar_eq_piFin R fm bu
  have hau𝔪 : a_u ∈ maximalIdeal A := by
    refine hiffu.mp ⟨h₁u, ?_⟩
    rw [hresu, hbu]
    exact (hasValue_zero_iff_mem_nonunits w _).mpr huw
  have hVbu := sub_mem_nonunits_restrictAlong_of_hasValue (hα := hα) W (bu : modularFunctionFieldBar N)
    (a_u : AlgebraicClosure ℚ) hWu
  have huQ₁ : ((u : modularFunctionFieldC k N)) ∈ (fm.spPlace hred dataAll hsep V).toValuationSubring.nonunits := by
    have hpi := piFin_mem_spPlace_nonunits fm hred dataAll hsep V (x₁ + a₀) hanchor bu a_u hau𝔪 hVbu
    rwa [hbu] at hpi

  exact hcrit _ hjQ₁ hjaQ₁ huQ₁

end Main

end ModularCurve.C5SpecNq

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [IsAlgClosed k] [DecidableEq k] (hqN : ¬ q ∣ N) (fm : CharPModel.FibreModel N A q k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (P : PlaceSpecialization A q N data hKr k red hα hβ) (hP : P.sp = fm.spPlace hred dataAll hsep)
    (R : ProlongationTuple P)
    (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∀ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K →
      ∃ (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K'), K ≤ K' ∧
        ∀ (K'' : IntermediateField ℚ (AlgebraicClosure ℚ)), FiniteDimensional ℚ K'' → K' ≤ K'' →
          ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
            (∀ (t : ↥(modularFunctionFieldBar (N * q)))
                (ht : (t : LaurentSeries (AlgebraicClosure ℚ)) ∈ jIntegralClosure (N * q) A K''),
                ∃ a : A, W.HasValue t (a : AlgebraicClosure ℚ) ∧
                  ((∃ h₁ : t ∈ R.R₁.integers, w.HasValue (R.residue₁ ⟨t, h₁⟩ : ↥(modularFunctionFieldC k N)) (0 : k)) ↔
                    a ∈ IsLocalRing.maximalIdeal A)) →
            P.reduceFst W = w :=
  ModularCurve.C5SpecNq.main hqN fm hred dataAll hsep P hP R w hw

end

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_reduceFst_eq_of_forall_hasValue_of_sp_eq_spPlace
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_forall_reduceFst_eq_of_forall_hasValue_of_sp_eq_spPlace (solution)
