-- Prove2me | solution 1 for M4aHerbrand.exists_classAct_eq_and_pow_mem_range_ideleClassNorm_iff_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2f6bcae3-ebdc-520e-88f0-d97f0421acee

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_and_unitIdeles_le_range_idelicNorm
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_unitIdeles_le
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_M4aHerbrand_GenuineDescent_unitsMap_beta_mem_principalIdeles_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_classAct_eq_and_pow_mem_range_ideleClassNorm_iff_of_isCyclic
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin Deep.NTSupply
open scoped IsMulCommutative

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsCyclic (F ≃ₐ[E] F)] (D : IdeleGaloisDescent (𝓞 F) E F) :
    ∃ c : IdeleClassGroup (𝓞 F) F, (∀ g : F ≃ₐ[E] F, D.classAct g c = c) ∧
      ∀ k : ℕ, c ^ k ∈ (ideleClassNorm D).range ↔ Nat.card (F ≃ₐ[E] F) ∣ k := by
  classical

  obtain ⟨𝔣, h𝔣, hram, hunits⟩ := LanglandsTunnell.P2.Artin.exists_ne_bot_and_unitIdeles_le_range_idelicNorm E F
  obtain ⟨r, -, hker, hsurj, -⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_unitIdeles_le E F 𝔣 h𝔣 hram hunits
  obtain ⟨-, hfixed, -, hprod⟩ :=
    M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm E F D

  let βu : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 F) F)ˣ := Units.map (genuineBaseChange E F).β.toMonoidHom
  let Nrm : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 E) E)ˣ := (genuineBaseChange E F).idelicNorm

  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := F ≃ₐ[E] F)
  obtain ⟨u, hu⟩ := hsurj s
  refine ⟨QuotientGroup.mk (βu u), fun g => ?_, fun k => ?_⟩
  ·
    show (QuotientGroup.mk (D.unitsAct g (βu u)) : IdeleClassGroup (𝓞 F) F) = QuotientGroup.mk (βu u)
    rw [(hfixed (βu u)).mpr ⟨u, rfl⟩ g]
  ·
    have hnorm_mk : ∀ v : (AdeleRing (𝓞 F) F)ˣ,
        ideleClassNorm D (QuotientGroup.mk v) = QuotientGroup.mk (βu (Nrm v)) := by
      intro v
      have h2 : (QuotientGroup.mk (βu (Nrm v)) : IdeleClassGroup (𝓞 F) F)
          = ∏ τ : F ≃ₐ[E] F, D.classAct τ (QuotientGroup.mk v) := by
        show QuotientGroup.mk' (principalIdeles (𝓞 F) F) (βu (Nrm v)) = _
        rw [← hprod v, map_prod]
        rfl
      rw [h2]
      unfold ideleClassNorm
      simp only [MonoidHom.coe_mk, OneHom.coe_mk]
      exact Finset.prod_congr (by ext; simp) (fun _ _ => rfl)
    constructor
    · rintro ⟨c', hc'⟩
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective c'
      rw [hnorm_mk, ← QuotientGroup.mk_pow, ← map_pow, QuotientGroup.eq, ← map_inv, ← map_mul,
        M4aHerbrand.GenuineDescent.unitsMap_beta_mem_principalIdeles_iff] at hc'

      have hk : u ^ k ∈ r.ker := by
        rw [hker, ← mul_inv_cancel_left (Nrm v) (u ^ k)]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨v, rfl⟩) (Subgroup.mem_sup_left hc')
      rw [MonoidHom.mem_ker, map_pow, hu] at hk
      rw [← orderOf_eq_card_of_forall_mem_zpowers hs]
      exact orderOf_dvd_of_pow_eq_one hk
    · intro hk
      have hk' : u ^ k ∈ r.ker := by
        rw [MonoidHom.mem_ker, map_pow, hu, ← orderOf_dvd_iff_pow_eq_one, orderOf_eq_card_of_forall_mem_zpowers hs]
        exact hk
      rw [hker] at hk'
      obtain ⟨p, hp, w, ⟨v, rfl⟩, hpw⟩ := Subgroup.mem_sup.mp hk'
      refine ⟨QuotientGroup.mk v, ?_⟩
      rw [hnorm_mk, ← QuotientGroup.mk_pow, ← map_pow, QuotientGroup.eq, ← map_inv, ← map_mul,
        M4aHerbrand.GenuineDescent.unitsMap_beta_mem_principalIdeles_iff, ← hpw]
      rw [show (Nrm v)⁻¹ * (p * Nrm v) = p from by rw [mul_comm p, ← mul_assoc, inv_mul_cancel, one_mul]]
      exact hp

end S_M4aHerbrand_exists_classAct_eq_and_pow_mem_range_ideleClassNorm_iff_of_isCyclic
end P2MW
export P2MW.S_M4aHerbrand_exists_classAct_eq_and_pow_mem_range_ideleClassNorm_iff_of_isCyclic (solution)
