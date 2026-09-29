-- Prove2me | solution 1 for NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3f708997-4b55-572d-9b32-3bae2bccf25b

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_nonempty_tate_addEquiv_ideleClass
import Theorems.Thm_Rep_natCard_tateCohomology_zero_and_neg_one_of_isCyclic
import Theorems.Thm_M4aHerbrand_ideleClassGroup_tateCard_zero_ne_zero_and_finrank_dvd
import Theorems.Thm_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_res_iso_fixedField_and_groupCohomology_iso
import Theorems.Thm_NumberField_PrimeNormIndex_ideleClassGroup_tateCard_zero_dvd_of_finrank_eq_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_card_prime
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

private theorem res_iso_fixedField
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (S : Subgroup (F ≃ₐ[E] F))
    (D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField S) F)
    [MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F)]
    (hact' : ∀ (g : F ≃ₐ[IntermediateField.fixedField S] F) (c : IdeleClassGroup (𝓞 F) F),
      g • c = D'.classAct g c)
    (ι : S ≃* (F ≃ₐ[IntermediateField.fixedField S] F))
    (hι : ∀ (s : S) (x : F), ι s x = (s : F ≃ₐ[E] F) x) :
    Nonempty (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ≅
        Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F)
          (IdeleClassGroup (𝓞 F) F))) ∧
      ∀ n : ℕ, Nonempty (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) n ≅
        groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F)
          (IdeleClassGroup (𝓞 F) F)) n) :=
  NumberField.IdeleClassGroup.nonempty_res_iso_fixedField_and_groupCohomology_iso E F D hact S D' hact' ι hι

private theorem tateCard_zero_dvd_of_finrank_eq_prime
    (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    [IsGalois E F] (p : ℕ) (hp : p.Prime) (hdeg : Module.finrank E F = p)
    (D : M4aHerbrand.IdeleGaloisDescent (NumberField.RingOfIntegers F) E F) :
    ∀ σ : F ≃ₐ[E] F, (∀ τ, τ ∈ Subgroup.zpowers σ) →
      Nat.card ((M4aHerbrand.ideleClassDerive D σ).ker ⧸
        ((M4aHerbrand.ideleClassNorm D).range.subgroupOf
          (M4aHerbrand.ideleClassDerive D σ).ker)) ∣ p :=
  NumberField.PrimeNormIndex.ideleClassGroup_tateCard_zero_dvd_of_finrank_eq_prime E F p hp hdeg D

section Glue

private theorem isZero_of_iso_of_natCard_eq_one {X Y : ModuleCat ℤ} (e : X ≅ Y) (h : Nat.card Y = 1) :
    Limits.IsZero X := by
  have h1 : Nat.card X = 1 := (Nat.card_congr e.toLinearEquiv.toEquiv).trans h
  haveI : Subsingleton X := (Nat.card_eq_one_iff_unique.mp h1).1
  exact ModuleCat.isZero_of_subsingleton X

private theorem natCard_eq_of_iso {X Y : ModuleCat ℤ} (e : X ≅ Y) : Nat.card X = Nat.card Y :=
  Nat.card_congr e.toLinearEquiv.toEquiv

private theorem natCard_tateCohomology_zero {G : Type} [Group G] [Fintype G] (B : Rep ℤ G) :
    Nat.card (B.tateCohomology 0) = Nat.card B.tateH0 := rfl

private theorem natCard_tateCohomology_neg_one {G : Type} [Group G] [Fintype G] (B : Rep ℤ G) :
    Nat.card (B.tateCohomology (-1)) = Nat.card B.tateHneg1 := rfl

private theorem finrank_eq_of_natCard_aut {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (n : ℕ) (h : Nat.card (L ≃ₐ[K] L) = n) : Module.finrank K L = n := by
  rw [← IsGalois.card_aut_eq_finrank]
  exact h

private theorem eq_prime_and_eq_one {p a b : ℕ} (hp : p.Prime) (hap : a ∣ p) (hpa : p ∣ a) (hab : a = p * b) :
    a = p ∧ b = 1 := by
  have ha : a = p := Nat.dvd_antisymm hap hpa
  refine ⟨ha, Nat.eq_of_mul_eq_mul_left hp.pos ?_⟩
  rw [Nat.mul_one, ← hab, ha]

end Glue

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (S : Subgroup (F ≃ₐ[E] F)) [Fintype S] (hS : (Fintype.card S).Prime) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype
        (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1) ∧
      Nat.card (groupCohomology (Rep.res S.subtype
        (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S := by
  haveI : Fact (Fintype.card S).Prime := ⟨hS⟩

  let D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField S) F :=
    GenuineDescent.genuineDescentDatum (IntermediateField.fixedField S) F
  letI : MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F) :=
    D'.classMulDistribMulAction
  have hact' : ∀ (g : F ≃ₐ[IntermediateField.fixedField S] F) (c : IdeleClassGroup (𝓞 F) F),
      g • c = D'.classAct g c := fun _ _ => rfl
  let ι : S ≃* (F ≃ₐ[IntermediateField.fixedField S] F) :=
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField S).symm).trans
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField S))
  have hι : ∀ (s : S) (x : F), ι s x = (s : F ≃ₐ[E] F) x := fun _ _ => rfl
  obtain ⟨-, hcoh⟩ := res_iso_fixedField E F D hact S D' hact' ι hι

  have hcard : Nat.card (F ≃ₐ[IntermediateField.fixedField S] F) = Fintype.card S :=
    (Nat.card_congr ι.toEquiv).symm.trans Nat.card_eq_fintype_card
  haveI : IsCyclic (F ≃ₐ[IntermediateField.fixedField S] F) := isCyclic_of_prime_card hcard
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := F ≃ₐ[IntermediateField.fixedField S] F)
  have hdeg := finrank_eq_of_natCard_aut (Fintype.card S) hcard

  have h2 := tateCard_zero_dvd_of_finrank_eq_prime (IntermediateField.fixedField S) F (Fintype.card S) hS hdeg D' σ hσ
  have h1 := ideleClassGroup_tateCard_zero_ne_zero_and_finrank_dvd (IntermediateField.fixedField S) F D' σ hσ
  have hq := ideleClass_herbrandQuotient_eq_finrank (IntermediateField.fixedField S) F D' σ hσ
  rw [hdeg] at h1 hq
  obtain ⟨hQ0, hQ1⟩ := eq_prime_and_eq_one hS h2 h1.2 hq.1

  obtain ⟨-, -, hc0, hc1⟩ := nonempty_tate_addEquiv_ideleClass D' σ hσ hact'
  obtain ⟨hp0, hpneg⟩ := Rep.natCard_tateCohomology_zero_and_neg_one_of_isCyclic
    (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F))
  have hH2 := hp0.symm.trans ((natCard_tateCohomology_zero _).trans (hc0.trans hQ0))
  have hH1 := hpneg.symm.trans ((natCard_tateCohomology_neg_one _).trans (hc1.trans hQ1))

  obtain ⟨t1⟩ := hcoh 1
  obtain ⟨t2⟩ := hcoh 2
  exact ⟨isZero_of_iso_of_natCard_eq_one t1 hH1, (natCard_eq_of_iso t2).trans hH2⟩

end S_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_card_prime
end P2MW
export P2MW.S_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_card_prime (solution)
