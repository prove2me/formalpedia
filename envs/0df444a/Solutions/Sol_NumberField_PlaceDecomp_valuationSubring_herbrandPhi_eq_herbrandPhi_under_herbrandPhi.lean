-- Prove2me | solution 1 for NumberField.PlaceDecomp.valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2c6785f9-fade-5336-9fc1-6800d1a3b7b0

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Theorems.Thm_IsLocalRing_herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq
import Theorems.Thm_IsDiscreteValuationRing_map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers
import Theorems.Thm_NumberField_PlaceDecomp_lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers
import Theorems.Thm_NumberField_PlaceDecomp_map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

namespace XCSTAR
namespace Herb

open IsLocalRing

section inv
variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R]
variable {R' : Type*} [CommRing R'] [IsLocalRing R'] {G' : Type*} [Group G'] [MulSemiringAction G' R']

theorem map_maximalIdeal_pow_of_equiv (e : R ≃+* R') (k : ℕ) :
    (maximalIdeal R ^ k).map (e : R →+* R') = maximalIdeal R' ^ k := by
  have h1 : (maximalIdeal R).map (e : R →+* R') = maximalIdeal R' :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
  rw [Ideal.map_pow, h1]

theorem mem_maximalIdeal_pow_iff_of_equiv (e : R ≃+* R') (k : ℕ) (z : R) :
    z ∈ maximalIdeal R ^ k ↔ e z ∈ maximalIdeal R' ^ k := by
  constructor
  · intro hz
    rw [← map_maximalIdeal_pow_of_equiv e k]
    exact Ideal.mem_map_of_mem _ hz
  · intro hz
    have := Ideal.mem_map_of_mem (e.symm : R' →+* R) hz
    rw [map_maximalIdeal_pow_of_equiv e.symm k] at this
    simpa using this

theorem mem_lowerRamificationGroup_iff_of_equiv (e : R ≃+* R') (f : G ≃* G') (hef : ∀ (g : G) (x : R), e (g • x) = f g • e x)
    (g : G) (i : ℕ) : g ∈ lowerRamificationGroup R G i ↔ f g ∈ lowerRamificationGroup R' G' i := by
  rw [mem_lowerRamificationGroup, mem_lowerRamificationGroup]
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← hef, ← map_sub]
    exact (mem_maximalIdeal_pow_iff_of_equiv e _ _).1 (h y)
  · intro h y
    have := h (e y)
    rw [← hef, ← map_sub] at this
    exact (mem_maximalIdeal_pow_iff_of_equiv e _ _).2 this

theorem lowerRamificationCard_eq_of_equiv (e : R ≃+* R') (f : G ≃* G') (hef : ∀ (g : G) (x : R), e (g • x) = f g • e x) (i : ℕ) :
    lowerRamificationCard R G i = lowerRamificationCard R' G' i := by
  unfold lowerRamificationCard
  refine Nat.card_congr (Equiv.ofBijective (fun s => ⟨f s, (mem_lowerRamificationGroup_iff_of_equiv e f hef s i).1 s.2⟩) ⟨?_, ?_⟩)
  · intro a b h; exact Subtype.ext (f.injective (congrArg Subtype.val h))
  · intro t; refine ⟨⟨f.symm t, (mem_lowerRamificationGroup_iff_of_equiv e f hef _ i).2 (by simpa using t.2)⟩, Subtype.ext (by simp)⟩

theorem herbrandPhi_eq_of_equiv (e : R ≃+* R') (f : G ≃* G') (hef : ∀ (g : G) (x : R), e (g • x) = f g • e x) (u : ℚ) :
    herbrandPhi R G u = herbrandPhi R' G' u := by
  unfold herbrandPhi
  simp only [lowerRamificationCard_eq_of_equiv e f hef]

theorem lowerRamificationGroup_map_equiv (e : R ≃+* R') (f : G ≃* G') (hef : ∀ (g : G) (x : R), e (g • x) = f g • e x) (i : ℕ) :
    (lowerRamificationGroup R G i).map f.toMonoidHom = lowerRamificationGroup R' G' i := by
  ext g'
  constructor
  · rintro ⟨g, hg, rfl⟩; exact (mem_lowerRamificationGroup_iff_of_equiv e f hef g i).1 hg
  · intro hg'; refine ⟨f.symm g', (mem_lowerRamificationGroup_iff_of_equiv e f hef _ i).2 (by simpa using hg'), by simp⟩

end inv

end XCSTAR.Herb

namespace XCSTAR
namespace HerbPhi
open IsDedekindDomain IsLocalRing

section kitc
variable (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  (w : HeightOneSpectrum (𝓞 M))

theorem faithfulSMul_decomp_integers :
    FaithfulSMul ↥(NumberField.PlaceDecomp.decomp K M w) ↥(w.adicCompletionIntegers M) := by
  refine ⟨fun {σ τ} h => Subtype.ext (AlgEquiv.ext fun m => ?_)⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) m
  have h' : ∀ r : 𝓞 M, (σ : M ≃ₐ[K] M) (r : M) = (τ : M ≃ₐ[K] M) (r : M) := by
    intro r
    have hr : ((r : M) : w.adicCompletion M) ∈ w.adicCompletionIntegers M := w.coe_mem_adicCompletionIntegers r
    have := congrArg (fun y : ↥(w.adicCompletionIntegers M) => (y : w.adicCompletion M)) (h ⟨_, hr⟩)
    simp only [NumberField.PlaceDecomp.coe_smul_integers] at this
    rw [NumberField.PlaceDecomp.smul_def, NumberField.PlaceDecomp.smul_def] at this
    change NumberField.PlaceDecomp.actRingEquiv σ ((WithVal.equiv (w.valuation M)).symm (r : M) : w.adicCompletion M) =
      NumberField.PlaceDecomp.actRingEquiv τ ((WithVal.equiv (w.valuation M)).symm (r : M) : w.adicCompletion M) at this
    rw [NumberField.PlaceDecomp.actRingEquiv_coe, NumberField.PlaceDecomp.actRingEquiv_coe] at this
    have := UniformSpace.Completion.coe_injective _ (congrArg HeightOneSpectrum.adicCompletion.toCompletion this)
    simpa [WithVal.congr] using this
  rw [map_div₀, map_div₀]
  change (σ : M ≃ₐ[K] M) (a : M) / (σ : M ≃ₐ[K] M) (b : M) = (τ : M ≃ₐ[K] M) (a : M) / (τ : M ≃ₐ[K] M) (b : M)
  rw [h' a, h' b]

scoped instance liesOver_integers (N : Subgroup ↥(NumberField.PlaceDecomp.decomp K M w)) :
    (maximalIdeal ↥(w.adicCompletionIntegers M)).LiesOver (maximalIdeal (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥N)) :=
  ⟨by rw [Ideal.under_def, FixedPoints.maximalIdeal_subring_eq_comap]; rfl⟩

scoped instance liesOver_integers' :
    (maximalIdeal ↥(w.adicCompletionIntegers M)).LiesOver
      (maximalIdeal (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w))) :=
  ⟨by rw [Ideal.under_def, FixedPoints.maximalIdeal_subring_eq_comap]; rfl⟩

theorem finite_residue_integers : Finite (↥(w.adicCompletionIntegers M) ⧸ maximalIdeal ↥(w.adicCompletionIntegers M)) := by
  haveI : Finite (𝓞 M ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  exact IsDedekindDomain.HeightOneSpectrum.finite_residueField_adicCompletionIntegers M w

theorem isSeparable_integers :
    Algebra.IsSeparable
      (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w) ⧸
        maximalIdeal (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w)))
      (↥(w.adicCompletionIntegers M) ⧸ maximalIdeal ↥(w.adicCompletionIntegers M)) := by
  letI : Field (↥(w.adicCompletionIntegers M) ⧸ maximalIdeal ↥(w.adicCompletionIntegers M)) := Ideal.Quotient.field _
  letI : Field (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w) ⧸
      maximalIdeal (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w))) := Ideal.Quotient.field _
  haveI : Finite (↥(w.adicCompletionIntegers M) ⧸ maximalIdeal ↥(w.adicCompletionIntegers M)) := finite_residue_integers M w
  haveI : Finite (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w) ⧸
      maximalIdeal (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w))) :=
    Finite.of_injective _ (algebraMap _ (↥(w.adicCompletionIntegers M) ⧸ maximalIdeal ↥(w.adicCompletionIntegers M))).injective
  haveI : Module.Finite (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w) ⧸
      maximalIdeal (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w)))
      (↥(w.adicCompletionIntegers M) ⧸ maximalIdeal ↥(w.adicCompletionIntegers M)) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w) ⧸
      maximalIdeal (FixedPoints.subring ↥(w.adicCompletionIntegers M) ↥(NumberField.PlaceDecomp.decomp K M w)))
      (↥(w.adicCompletionIntegers M) ⧸ maximalIdeal ↥(w.adicCompletionIntegers M)) := Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem herbrandPhi_congr {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    {R' : Type*} [CommRing R'] [IsLocalRing R'] [MulSemiringAction G R']
    (h : ∀ i : ℕ, IsLocalRing.lowerRamificationGroup R G i = IsLocalRing.lowerRamificationGroup R' G i) (u : ℚ) :
    IsLocalRing.herbrandPhi R G u = IsLocalRing.herbrandPhi R' G u := by
  have hc : ∀ i : ℕ, IsLocalRing.lowerRamificationCard R G i = IsLocalRing.lowerRamificationCard R' G i := fun i => by
    unfold IsLocalRing.lowerRamificationCard; rw [h i]
  unfold IsLocalRing.herbrandPhi
  simp only [hc]

end kitc
end XCSTAR.HerbPhi
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi.XCSTAR P2MW.S_NumberField_PlaceDecomp_valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi.XCSTAR.HerbPhi"
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi.XCSTAR"

theorem solution
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [Normal E L]
    (w : HeightOneSpectrum (𝓞 F)) (u : ℚ) (hu : 0 ≤ u) :
    ValuationSubring.herbrandPhi E ((w.valuation F).valuationSubring) u =
      ValuationSubring.herbrandPhi E (((w.under (𝓞 L)).valuation L).valuationSubring)
        (ValuationSubring.herbrandPhi L ((w.valuation F).valuationSubring) u) := by
  classical

  obtain ⟨r, hrsurj, hrcoe, hrker, hrL, hreq⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E L F w
  haveI : r.ker.Normal := inferInstance
  haveI := XCSTAR.HerbPhi.faithfulSMul_decomp_integers E F w
  haveI := XCSTAR.HerbPhi.isSeparable_integers E F w
  set e : ↥(NumberField.PlaceDecomp.decomp E F w) ⧸ r.ker ≃* ↥(NumberField.PlaceDecomp.decomp E L (w.under (𝓞 L))) :=
    QuotientGroup.quotientKerEquivOfSurjective r hrsurj with he
  letI : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w) ⧸ r.ker) ↥((w.under (𝓞 L)).adicCompletionIntegers L) :=
    MulSemiringAction.compHom _ e.toMonoidHom

  have hFIX := NumberField.PlaceDecomp.map_lowerRamificationGroup_fixedPoints_adicCompletionIntegers_eq_of_restrict E L F w r hrsurj hrcoe
  have hpull : ∀ j : ℕ,
      IsLocalRing.lowerRamificationGroup ↥(FixedPoints.subring ↥(w.adicCompletionIntegers F) ↥r.ker)
          (↥(NumberField.PlaceDecomp.decomp E F w) ⧸ r.ker) j =
        IsLocalRing.lowerRamificationGroup ↥((w.under (𝓞 L)).adicCompletionIntegers L)
          (↥(NumberField.PlaceDecomp.decomp E F w) ⧸ r.ker) j := by
    intro j
    ext x
    rw [XCSTAR.Herb.mem_lowerRamificationGroup_iff_of_equiv
      (R := ↥((w.under (𝓞 L)).adicCompletionIntegers L)) (R' := ↥((w.under (𝓞 L)).adicCompletionIntegers L))
      (RingEquiv.refl _) e (fun g y => rfl) x j, ← hFIX j, Subgroup.mem_map]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      subst this
      exact hy

  have hH : ∀ n : ℕ,
      (IsLocalRing.lowerRamificationGroup ↥(w.adicCompletionIntegers F) ↥(NumberField.PlaceDecomp.decomp E F w) n).map (QuotientGroup.mk' r.ker) =
        IsLocalRing.lowerRamificationGroup ↥((w.under (𝓞 L)).adicCompletionIntegers L) (↥(NumberField.PlaceDecomp.decomp E F w) ⧸ r.ker)
          ⌈IsLocalRing.herbrandPhi ↥(w.adicCompletionIntegers F) ↥r.ker (n : ℚ)⌉₊ := fun n =>
    (IsDiscreteValuationRing.map_lowerRamificationGroup_mk_eq_of_isSeparable_residueField (H := r.ker) n).trans (hpull _)
  have htrans := IsLocalRing.herbrandPhi_eq_herbrandPhi_quotient_comp_of_map_lowerRamificationGroup_mk_eq hH hu

  have hφD : ValuationSubring.herbrandPhi E ((w.valuation F).valuationSubring) u =
      IsLocalRing.herbrandPhi ↥(w.adicCompletionIntegers F) ↥(NumberField.PlaceDecomp.decomp E F w) u :=
    XCSTAR.HerbPhi.herbrandPhi_congr (NumberField.PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers E F w) u
  have hφDL : ∀ x : ℚ, IsLocalRing.herbrandPhi ↥((w.under (𝓞 L)).adicCompletionIntegers L) (↥(NumberField.PlaceDecomp.decomp E F w) ⧸ r.ker) x =
      ValuationSubring.herbrandPhi E (((w.under (𝓞 L)).valuation L).valuationSubring) x := fun x => by
    rw [XCSTAR.Herb.herbrandPhi_eq_of_equiv (R' := ↥((w.under (𝓞 L)).adicCompletionIntegers L)) (RingEquiv.refl _) e (fun g y => rfl) x]
    exact (XCSTAR.HerbPhi.herbrandPhi_congr
      (NumberField.PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers E L (w.under (𝓞 L))) x).symm
  have hφN : IsLocalRing.herbrandPhi ↥(w.adicCompletionIntegers F) ↥r.ker u =
      ValuationSubring.herbrandPhi L ((w.valuation F).valuationSubring) u := by

    have hmemD : ∀ τ : ↥(NumberField.PlaceDecomp.decomp L F w),
        AlgEquiv.restrictScalars E (τ : F ≃ₐ[L] F) ∈ NumberField.PlaceDecomp.decomp E F w := fun τ => τ.2
    have hmemN : ∀ τ : ↥(NumberField.PlaceDecomp.decomp L F w),
        (⟨AlgEquiv.restrictScalars E (τ : F ≃ₐ[L] F), hmemD τ⟩ : ↥(NumberField.PlaceDecomp.decomp E F w)) ∈ r.ker := by
      intro τ
      obtain ⟨σ, hσ, hσ1⟩ := hrL τ
      have : σ = ⟨AlgEquiv.restrictScalars E (τ : F ≃ₐ[L] F), hmemD τ⟩ := Subtype.ext hσ
      rw [← this]; exact hσ1
    have hlin : ∀ σ : ↥r.ker, ∀ x : L, ((σ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) (algebraMap L F x) = algebraMap L F x :=
      fun σ => (hrker _).1 σ.2
    let g : ↥r.ker → ↥(NumberField.PlaceDecomp.decomp L F w) := fun σ =>
      ⟨{ ((σ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) with commutes' := hlin σ }, by
        have h := ((σ : ↥(NumberField.PlaceDecomp.decomp E F w))).2
        exact h⟩
    let f : ↥(NumberField.PlaceDecomp.decomp L F w) ≃* ↥r.ker :=
      { toFun := fun τ => ⟨⟨AlgEquiv.restrictScalars E (τ : F ≃ₐ[L] F), hmemD τ⟩, hmemN τ⟩
        invFun := g
        left_inv := fun τ => by apply Subtype.ext; apply AlgEquiv.ext; intro x; rfl
        right_inv := fun σ => by apply Subtype.ext; apply Subtype.ext; apply AlgEquiv.ext; intro x; rfl
        map_mul' := fun τ τ' => by apply Subtype.ext; apply Subtype.ext; apply AlgEquiv.ext; intro x; rfl }
    rw [← XCSTAR.Herb.herbrandPhi_eq_of_equiv (R := ↥(w.adicCompletionIntegers F)) (RingEquiv.refl _) f (fun τ y => rfl) u]
    exact (XCSTAR.HerbPhi.herbrandPhi_congr
      (NumberField.PlaceDecomp.lowerRamificationGroup_valuationSubring_eq_adicCompletionIntegers L F w) u).symm

  rw [hφD, htrans, hφN, hφDL]

end S_NumberField_PlaceDecomp_valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi
end P2MW
export P2MW.S_NumberField_PlaceDecomp_valuationSubring_herbrandPhi_eq_herbrandPhi_under_herbrandPhi (solution)
