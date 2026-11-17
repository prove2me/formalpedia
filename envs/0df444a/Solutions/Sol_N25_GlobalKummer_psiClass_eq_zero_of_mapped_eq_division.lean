-- Prove2me | solution 1 for N25.GlobalKummer.psiClass_eq_zero_of_mapped_eq_division
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:09:12.588553+00:00
-- url     : https://prove2.me/submissions/17f61463-470b-45c9-ac1f-2a8933a26cb8

import Mathlib
import Theorems.Thm_N25_GlobalKummer_psi_cocycle_class_zero
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_N25_CharacterField
import Definitions.Def_N25_LocalKummerCharacter
import Definitions.Def_N25
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic
import Theorems.Thm_NumberField_exists_valuationSubring_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_map_subtype_inertiaSubgroup_valuationSubring_eq_inertia
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_restrictNormal_eq
import Theorems.Thm_M4aHerbrand_exists_adeleBaseChange_normCoset_index_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_NumberField_TateGlobal_index_unitIdelesOutside_sup_range_unitsMap_algebraMap_eq_classNumber
import Theorems.Thm_groupCohomology_exists_corestriction_map_map_res_eq_map_norm
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Theorems.Thm_groupCohomology_H1pi_map_of_values
import Theorems.Thm_N25_GlobalKummer_divisionCocycle_isFiniteFlat_of_ordinary
import Definitions.Def_N25_LocalFiniteFlatClasses
import Definitions.Def_N25_OrdinaryKummerFiniteFlat
import Definitions.Def_N25_LocalKummerOperators
import Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_of_map_add_coboundary
import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
import Theorems.Thm_N25_K2Rows_local_coboundary_lift_at_five
import Definitions.Def_N25_LocalKummerKernel
import Theorems.Thm_N25_kummer_at_five_is_coboundary_of_N5Surj
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_N25_n5Surj
import Definitions.Def_N25_LocalFiveCondition
import Definitions.Def_N25_RatPointModel
import Definitions.Def_N25_LocalCarrier
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Theorems.Thm_N25_psi_inertia_eq_one_of_ne_five
import Theorems.Thm_ValuationSubring_smul_eq_self_of_mem_inertiaSubgroupIn_of_pow_eq_one
import Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_eq_zero_on_inertia
import Theorems.Thm_HopfAlgebra_act_eq_self_of_inertiaTrivialChain_padicInt
import Theorems.Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime
import Theorems.Thm_ValuationSubring_mem_inertiaSubgroupIn_pointwise_smul_iff
import Theorems.Thm_localGaloisToGlobal_mem_inertiaSubgroupIn
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

open CategoryTheory groupCohomology

open scoped Pointwise

namespace N25.GlobalKummer

local instance psiMappedPrimeSeventyOne_sd9d3f7 : Fact (Nat.Prime 71) := ⟨by decide⟩

local instance psiMappedPrimeFive_sd9d3f7 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A lifted psi-class of the geometric division class has zero restriction to
the quintic field: its local conditions at five and seventy-one are unramified.
Class-field theory and restriction-corestriction then kill the global class. -/
theorem _root_.solution
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN71 : OrdinaryKummerFiniteFlat)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J))
    (z : ↥(continuousH1S ramificationSet psiRep))
    (hmap : (groupCohomology.map (MonoidHom.id Gal) (kernelInclusion hPhi K2) 1).hom
      (z : H1 psiRep) = H1π (vRep hPhi) (divisionCocycle hPhi P Q hQ)) :
    (z : H1 psiRep) = 0 := by
  classical
  letI := vModule hPhi
  obtain ⟨c, hc, hz⟩ := (mem_continuousH1S_iff ramificationSet psiRep z).mp z.property
  rw [← hz] at hmap ⊢
  let d := divisionCocycle hPhi P Q hQ
  let ic : cocycles₁ (vRep hPhi) :=
    ⟨fun σ => K2.i (c σ), by
      apply (mem_cocycles₁_iff _).mpr
      intro σ τ
      change K2.i (c (σ * τ)) = vAct σ (K2.i (c τ)) + K2.i (c σ)
      rw [(mem_cocycles₁_iff c).mp c.property σ τ, map_add]
      exact congrArg (fun x => x + K2.i (c σ)) (K2.i_galois σ (c τ)).symm⟩
  have hicclass : H1π (vRep hPhi) ic = H1π (vRep hPhi) d := by
    rw [← H1pi_map_of_values (MonoidHom.id Gal) psiRep (vRep hPhi)
      (kernelInclusion hPhi K2) c ic (fun _ => rfl)]
    exact hmap
  obtain ⟨b, hb⟩ := (H1π_eq_iff ic d).mp hicclass
  change ↥V at b
  have hib (σ : Gal) : K2.i (c σ) = (show ↥V from d σ) + (vAct σ b - b) := by
    have h := congrArg (fun f : Gal → vRep hPhi => (show ↥V from f σ)) hb
    change vAct σ b - b = K2.i (c σ) - (show ↥V from d σ) at h
    exact (sub_eq_iff_eq_add.mp h.symm).trans (add_comm _ _)
  have hmul (σ τ : Gal) : c (σ * τ) = (psi σ : ZMod 71) * c τ + c σ :=
    (mem_cocycles₁_iff c).mp c.property σ τ
  have hfive : ∀ σ : Gal,
      σ ∈ (ExtCitation.primeLocalPlace q5).inertiaSubgroupIn ℚ →
      psi σ = 1 → c σ = 0 := by
    obtain ⟨v, hv⟩ := kummer_at_five_is_coboundary_of_N5Surj hPhi K2 n5Surj
      (P : J) Q P.property hQ
    have hlocal (τ : G5) : K2.i (c (r5 τ)) = vAct (r5 τ) (v + b) - (v + b) := by
      rw [hib]
      have hd : (show ↥V from d (r5 τ)) = vAct (r5 τ) v - v := by
        apply Subtype.ext
        exact hv τ
      rw [hd]
      change (r5 τ • v - v) + (r5 τ • b - b) = r5 τ • (v + b) - (v + b)
      rw [smul_add]
      abel
    obtain ⟨a, ha⟩ := K2Rows.local_coboundary_lift_at_five K2
      (fun τ => c (r5 τ)) (v + b) hlocal
    intro σ hσ hψ
    obtain ⟨τ, _, hτ⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq 5 σ hσ
    have h := ha τ
    change c (localGaloisToGlobal 5 τ) =
      (psi (localGaloisToGlobal 5 τ) : ZMod 71) * a - a at h
    rw [hτ, hψ, Units.val_one, one_mul, sub_self] at h
    exact h
  have hseventyOne : ∀ σ : Gal,
      σ ∈ (ExtCitation.primeLocalPlace (⟨71, by decide⟩ : Nat.Primes)).inertiaSubgroupIn ℚ →
      psi σ = 1 → c σ = 0 := by
    let r := localGaloisToGlobal 71
    let cl : cocycles₁ localPsiRep :=
      ⟨fun σ => c (r σ), by
        apply (mem_cocycles₁_iff _).mpr
        intro σ τ
        change c (r (σ * τ)) = psiRep.ρ (r σ) (c (r τ)) + c (r σ)
        rw [map_mul]
        exact (mem_cocycles₁_iff c).mp c.property (r σ) (r τ)⟩
    let dl : cocycles₁ (localKernelRep hPhi) :=
      ⟨fun σ => d (r σ), by
        apply (mem_cocycles₁_iff _).mpr
        intro σ τ
        change d (r (σ * τ)) = (vRep hPhi).ρ (r σ) (d (r τ)) + d (r σ)
        rw [map_mul]
        exact (mem_cocycles₁_iff d).mp d.property (r σ) (r τ)⟩
    have hflat := divisionCocycle_isFiniteFlat_of_ordinary hPhi hN71 P Q hQ
    have hcflat := IsFiniteFlatCocycle.of_map_add_coboundary 71
      localPsiRep.ρ (localKernelRep hPhi).ρ cl dl
      (kernelInclusion hPhi K2).hom.toLinearMap K2.i_injective
      (fun σ a => Rep.hom_comm_apply (kernelInclusion hPhi K2) (r σ) a)
      (-b) (by
        intro σ
        change (show ↥V from d (r σ)) = K2.i (c (r σ)) + (vAct (r σ) (-b) - (-b))
        have hneg : vAct (r σ) (-b) = -vAct (r σ) b := by
          apply Subtype.ext
          exact smul_neg (r σ) (b : J)
        rw [hib, hneg]
        abel) hflat
    have hzero := IsFiniteFlatCocycle.eq_zero_on_inertia 71 (by decide)
      localPsiRep.ρ cl hcflat (by
        intro σ hσ a
        have hψ : psi (r σ) = 1 := psi_inertia_eq_one_of_ne_five (q := 71)
          (by decide) (by decide) (ExtCitation.primeLocalPlace (⟨71, by decide⟩ : Nat.Primes))
          (ExtCitation.liesOverPrime_primeLocalPlace (⟨71, by decide⟩ : Nat.Primes)) (r σ)
          (localGaloisToGlobal_mem_inertiaSubgroupIn 71 σ hσ)
        change (psi (r σ) : ZMod 71) * a = a
        rw [hψ, Units.val_one, one_mul])
    intro σ hσ _
    obtain ⟨τ, hτ, hτglobal⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq 71 σ hσ
    have h := hzero τ hτ
    change c (localGaloisToGlobal 71 τ) = 0 at h
    rwa [hτglobal] at h
  apply psi_cocycle_class_zero c hc.isLevelConstant₁
  intro q hq A hA σ hσ hψ
  by_cases hq5 : q = 5
  · subst q
    obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime (q := 5)
      (by decide) (ExtCitation.primeLocalPlace q5) A
      (ExtCitation.liesOverPrime_primeLocalPlace q5) hA
    have hconj : g⁻¹ * σ * g ∈ (ExtCitation.primeLocalPlace q5).inertiaSubgroupIn ℚ :=
      (ValuationSubring.mem_inertiaSubgroupIn_pointwise_smul_iff g σ _).mp (hg.symm ▸ hσ)
    have hψconj : psi (g⁻¹ * σ * g) = 1 := by simp [hψ]
    have hzconj := hfive _ hconj hψconj
    have heq : σ * g = g * (g⁻¹ * σ * g) := by group
    have h := congrArg c heq
    rw [hmul, hmul, hψ, Units.val_one, one_mul, hzconj, mul_zero, zero_add] at h
    exact add_eq_left.mp h
  · by_cases hq71 : q = 71
    · subst q
      obtain ⟨g, hg⟩ := ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime (q := 71)
        (by decide) (ExtCitation.primeLocalPlace (⟨71, by decide⟩ : Nat.Primes)) A
        (ExtCitation.liesOverPrime_primeLocalPlace (⟨71, by decide⟩ : Nat.Primes)) hA
      have hconj : g⁻¹ * σ * g ∈
          (ExtCitation.primeLocalPlace (⟨71, by decide⟩ : Nat.Primes)).inertiaSubgroupIn ℚ :=
        (ValuationSubring.mem_inertiaSubgroupIn_pointwise_smul_iff g σ _).mp (hg.symm ▸ hσ)
      have hψconj : psi (g⁻¹ * σ * g) = 1 := by simp [hψ]
      have hzconj := hseventyOne _ hconj hψconj
      have heq : σ * g = g * (g⁻¹ * σ * g) := by group
      have h := congrArg c heq
      rw [hmul, hmul, hψ, Units.val_one, one_mul, hzconj, mul_zero, zero_add] at h
      exact add_eq_left.mp h
    · obtain ⟨F, hF, hFc⟩ := hc
      have hqS : (⟨q, hq⟩ : Nat.Primes) ∉ ramificationSet := by
        intro hmem
        change (⟨q, hq⟩ : Nat.Primes) ∈
          ({⟨5, by decide⟩, ⟨71, by decide⟩} : Finset Nat.Primes) at hmem
        rcases Finset.mem_insert.mp hmem with heq | hmem
        · exact hq5 (congrArg Subtype.val heq)
        · exact hq71 (congrArg Subtype.val (Finset.mem_singleton.mp hmem))
      have hs := hF.2 ⟨q, hq⟩ hqS A hA hσ
      have h := hFc 1 σ hs
      simpa only [one_mul, cocycles₁_map_one] using h

end N25.GlobalKummer
