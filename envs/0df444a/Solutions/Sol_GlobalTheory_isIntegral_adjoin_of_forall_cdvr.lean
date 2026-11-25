-- Prove2me | solution 1 for GlobalTheory.isIntegral_adjoin_of_forall_cdvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:48.366409+00:00
-- url     : https://prove2.me/submissions/afebbe07-adf1-4709-a0a9-f7b9350b4eb7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralAdjoinOfForallCdvr
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_of_valuationSubring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Pj
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K Ω : Type) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (gens : Finset Ω)
    (hcl : Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤) (x : Ω)
    (hx : ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr,
      (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) →
      (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) :
    IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by
  classical
  set A := Algebra.adjoin K (gens : Set Ω) with hAdef

  have hfrac : ∀ z : Ω, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ z * b = a := by
    intro z
    have hz : z ∈ Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) := hcl ▸ trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hz
    have hc : Subring.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = A.toSubring :=
      (Algebra.adjoin_eq_ring_closure _).symm
    rw [hc] at ha hb
    rcases eq_or_ne b 0 with rfl | hb0
    · exact ⟨0, A.zero_mem, 1, A.one_mem, one_ne_zero, by simp⟩
    · exact ⟨a, ha, b, hb, hb0, div_mul_cancel₀ a hb0⟩

  have hKc : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have hΩc : Countable Ω := by
    have hs : (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)).Countable :=
      (Set.countable_range _).union gens.finite_toSet.countable
    have h1 : Cardinal.mk (Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω))) ≤
        Cardinal.aleph0 :=
      (Subfield.cardinalMk_closure_le_max _).trans
        (max_le (Cardinal.mk_le_aleph0_iff.2 hs.to_subtype) le_rfl)
    have h2 := Cardinal.mk_le_aleph0_iff.1 h1
    rw [hcl] at h2
    exact Function.Injective.countable (f := fun (z : Ω) => (⟨z, trivial⟩ : (⊤ : Subfield Ω)))
      fun a b h => congrArg Subtype.val h

  have hAft : Algebra.FiniteType K A := .adjoin_of_finite gens.finite_toSet
  have hAn : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hess : Algebra.EssFiniteType A Ω := by
    refine (Algebra.essFiniteType_iff A Ω).mpr ⟨∅, fun z => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hab⟩ := hfrac z
    simp only [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot]
    exact ⟨b, ⟨⟨b, hb⟩, rfl⟩, isUnit_iff_ne_zero.mpr hb0, ⟨⟨a, ha⟩, hab.symm⟩⟩
  by_contra hni
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hni isIntegral_zero

  letI := invertibleOfNonzero (inv_ne_zero hx0)
  let B := Algebra.adjoin A {x⁻¹}
  let xinv : B := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
  have hne : (⊥ : Ideal A).map (algebraMap A B) ⊔ Ideal.span {xinv} ≠ ⊤ := by
    intro heq
    obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
      x⁻¹ (⊥ : Ideal A) bot_ne_top heq
    have hm : p.Monic := by
      rw [Ideal.mem_bot, sub_eq_zero] at hp
      exact hp
    rw [invOf_eq_inv, inv_inv] at hpx
    exact hni ⟨p, hm, by rw [← Polynomial.aeval_def, hpx]⟩
  obtain ⟨W, hW, hW'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ hne
  have hxW : x⁻¹ ∈ W.nonunits := hW' ⟨xinv, Ideal.mem_sup_right (Ideal.subset_span rfl), rfl⟩

  obtain ⟨V, hV, hAV, -, hxV⟩ := exists_discreteValuationSubring_of_valuationSubring (R := A)
    W (fun r => hW (B.algebraMap_mem r)) (s := ∅) (t := {x⁻¹}) Set.finite_empty
    (Set.finite_singleton _) (by simp) (by simpa using hxW) ⟨x⁻¹, rfl, inv_ne_zero hx0⟩
  have hxV' : x⁻¹ ∈ V.nonunits := hxV _ rfl
  have hKV : ∀ k : K, algebraMap K Ω k ∈ V := fun k => hAV (algebraMap K A k)
  have hgV : ∀ g ∈ gens, g ∈ V := fun g hg => hAV ⟨g, Algebra.subset_adjoin hg⟩

  let ι := algebraMap V (AdicCompletion (maximalIdeal V) V)
  have hch : CharZero (AdicCompletion (maximalIdeal V) V) :=
    (RingHom.charZero_iff (ι.comp ((algebraMap K Ω).codRestrict V hKV)).injective).1 inferInstance
  let T : CDVR := { V := AdicCompletion (maximalIdeal V) V, ch0 := hch }
  have hVc : Countable V := Subtype.countable
  have hres : Countable (ResidueField T.V) := by
    have hsurj : Function.Surjective ((residue T.V).comp ι) := by
      intro t0
      obtain ⟨t, rfl⟩ := residue_surjective t0
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (maximalIdeal V) 1 t)
      refine ⟨r, ?_⟩
      change residue T.V (ι r) = residue T.V t
      change Ideal.Quotient.mk _ (ι r) = Ideal.Quotient.mk _ t
      rw [Ideal.Quotient.eq]
      intro hu
      have hnt : Nontrivial (V ⧸ maximalIdeal V ^ 1) := by
        rw [pow_one]; infer_instance
      have h1 := hu.map (AdicCompletion.evalₐ (maximalIdeal V) 1)
      rw [map_sub] at h1
      change IsUnit ((AdicCompletion.evalₐ (maximalIdeal V) 1) (AdicCompletion.of _ _ r) - _) at h1
      rw [AdicCompletion.evalₐ_of, hr, sub_self] at h1
      exact not_isUnit_zero h1
    exact hsurj.countable
  have hg : Function.Injective ((algebraMap T.V T.Fr).comp ι) :=
    (IsFractionRing.injective T.V T.Fr).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let φ : Ω →+* T.Fr := IsFractionRing.lift (A := V) hg
  have hφ : ∀ v : V, φ v = algebraMap T.V T.Fr (ι v) := fun v => IsFractionRing.lift_algebraMap hg v
  obtain ⟨t, ht⟩ := hx T hres φ (fun k => ⟨ι ⟨_, hKV k⟩, (hφ ⟨_, hKV k⟩).symm⟩)
    (fun g hg' => ⟨ι ⟨g, hgV g hg'⟩, (hφ ⟨g, hgV g hg'⟩).symm⟩)
  let y : V := ⟨x⁻¹, V.nonunits_subset hxV'⟩
  have h1 : algebraMap T.V T.Fr (t * ι y) = 1 := by
    rw [map_mul, ht, ← hφ y]
    change φ x * φ x⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
  have h2 : t * ι y = 1 := IsFractionRing.injective T.V T.Fr (h1.trans (map_one _).symm)
  have h3 : IsUnit (ι y) := isUnit_iff_exists_inv.mpr ⟨t, by rw [mul_comm]; exact h2⟩
  exact (ValuationSubring.coe_mem_nonunits_iff (a := y)).mp hxV' (isUnit_of_map_unit ι y h3)
end GlobalTheory
