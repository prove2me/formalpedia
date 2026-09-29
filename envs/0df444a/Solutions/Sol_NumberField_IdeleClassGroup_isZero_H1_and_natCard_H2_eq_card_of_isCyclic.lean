-- Prove2me | solution 1 for NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a8b32ef1-a4d8-5cfd-91d2-78b2a8ad88f5

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_res_iso_fixedField_and_groupCohomology_iso
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_fixedField
import Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_card_prime
import Theorems.Thm_M4aHerbrand_ideleClass_herbrandQuotient_eq_finrank
import Theorems.Thm_M4aHerbrand_nonempty_tate_addEquiv_ideleClass
import Theorems.Thm_Rep_natCard_tateCohomology_zero_and_neg_one_of_isCyclic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_isCyclic
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

section Furniture
variable {S G' V : Type} [Group S] [Group G'] [AddCommGroup V]

private theorem map_eq_id (ρ : Representation ℤ S V) (f : S →* S) (hf : f = MonoidHom.id S)
    (X : Rep.res f (Rep.of ρ) ⟶ Rep.of ρ) (hX : X.hom.toLinearMap = LinearMap.id) (n : ℕ) :
    groupCohomology.map f X n = 𝟙 (groupCohomology (Rep.of ρ) n) := by
  subst hf
  have hX' : X = 𝟙 (Rep.of ρ) := Rep.hom_ext (Representation.IntertwiningMap.ext hX)
  rw [hX']
  exact groupCohomology.map_id n

private theorem nonempty_groupCohomology_res_iso (ι : S ≃* G') (ρ : Representation ℤ G' V) (n : ℕ) :
    Nonempty (groupCohomology (Rep.res ι.toMonoidHom (Rep.of ρ)) n ≅ groupCohomology (Rep.of ρ) n) := by
  let ψ₀ : Representation.IntertwiningMap ((ρ.comp ι.toMonoidHom).comp ι.symm.toMonoidHom) ρ :=
    LinearMap.id.intertwiningMap_of_isIntertwiningMap (ρ := (ρ.comp ι.toMonoidHom).comp ι.symm.toMonoidHom)
      (σ := ρ) (fun g' v => by
        show ρ (ι (ι.symm g')) v = ρ g' v
        rw [MulEquiv.apply_symm_apply])
  let ψ : Rep.res ι.symm.toMonoidHom (Rep.res ι.toMonoidHom (Rep.of ρ)) ⟶ Rep.of ρ := Rep.ofHom ψ₀
  refine ⟨{ hom := groupCohomology.map ι.symm.toMonoidHom ψ n
            inv := groupCohomology.map ι.toMonoidHom (𝟙 (Rep.res ι.toMonoidHom (Rep.of ρ))) n
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · rw [← groupCohomology.map_comp]
    exact map_eq_id (ρ.comp ι.toMonoidHom) _ (MonoidHom.ext fun s => ι.symm_apply_apply s) _
      (LinearMap.ext fun _ => rfl) n
  · rw [← groupCohomology.map_comp]
    exact map_eq_id ρ _ (MonoidHom.ext fun g' => ι.apply_symm_apply g') _ (LinearMap.ext fun _ => rfl) n

end Furniture

section Transport
variable {S G' V : Type} [Group S] [Group G'] [AddCommGroup V]

private theorem isZero_res_of_isZero (ι : S ≃* G') (ρ : Representation ℤ G' V) (n : ℕ)
    (h : Limits.IsZero (groupCohomology (Rep.of ρ) n)) :
    Limits.IsZero (groupCohomology (Rep.res ι.toMonoidHom (Rep.of ρ)) n) := by
  obtain ⟨t⟩ := nonempty_groupCohomology_res_iso ι ρ n
  exact h.of_iso t

private theorem isZero_res_ofMulDistribMulAction {C : Type} [CommGroup C] [MulDistribMulAction G' C] (ι : S ≃* G')
    (n : ℕ) (h : Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G' C) n)) :
    Limits.IsZero (groupCohomology (Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction G' C)) n) :=
  isZero_res_of_isZero ι (Representation.ofMulDistribMulAction G' C) n h

end Transport

section Glue

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

private theorem natCard_eq_one_of_isZero {X : ModuleCat ℤ} (h : Limits.IsZero X) : Nat.card X = 1 :=
  Nat.card_eq_one_iff_unique.mpr ⟨ModuleCat.subsingleton_of_isZero h, ⟨0⟩⟩

private theorem eq_of_eq_mul_of_eq_one {a n b : ℕ} (hab : a = n * b) (hb : b = 1) : a = n := by
  rw [hab, hb, mul_one]

end Glue

section Tower

open M4aHerbrand.GenuineDescent

private theorem isZero_H1_top_of_isCyclic (m : ℕ) :
    ∀ (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
      (D : IdeleGaloisDescent (𝓞 F) E F)
      [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
      (_hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c),
      IsCyclic (F ≃ₐ[E] F) → Nat.card (F ≃ₐ[E] F) = m →
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 1) := by
  induction' m using Nat.strong_induction_on with m ih
  intro E F _ _ _ _ _ _ D _ hact hcyc hm
  haveI := hcyc
  rw [← hm] at ih
  by_cases hone : Nat.card (F ≃ₐ[E] F) = 1
  ·
    haveI : Subsingleton (F ≃ₐ[E] F) := (Nat.card_eq_one_iff_unique.mp hone).1
    exact isZero_groupCohomology_succ_of_subsingleton _ 0

  have hq : (Nat.card (F ≃ₐ[E] F)).minFac.Prime := Nat.minFac_prime hone
  haveI : Fact (Nat.card (F ≃ₐ[E] F)).minFac.Prime := ⟨hq⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (Nat.card (F ≃ₐ[E] F)).minFac (Nat.minFac_dvd _)
  have hNcard : Nat.card (Subgroup.zpowers g) = (Nat.card (F ≃ₐ[E] F)).minFac := by
    rw [Nat.card_zpowers, hg]
  haveI hNn : (Subgroup.zpowers g).Normal := inferInstance

  haveI : Fintype (Subgroup.zpowers g) := @Fintype.ofFinite _ (@Subtype.finite _ (Finite.of_fintype _) _)
  have hprime : (Fintype.card (Subgroup.zpowers g)).Prime := by
    rw [← Nat.card_eq_fintype_card, hNcard]; exact hq
  have hX₃ := (NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime E F D hact (Subgroup.zpowers g) hprime).1

  have hX₁ : Limits.IsZero (groupCohomology ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)).quotientToInvariants (Subgroup.zpowers g)) 1) := by
    let D₂ : IdeleGaloisDescent (𝓞 (IntermediateField.fixedField (Subgroup.zpowers g))) E (IntermediateField.fixedField (Subgroup.zpowers g)) := genuineDescentDatum E (IntermediateField.fixedField (Subgroup.zpowers g))
    letI : MulDistribMulAction ((IntermediateField.fixedField (Subgroup.zpowers g)) ≃ₐ[E] (IntermediateField.fixedField (Subgroup.zpowers g))) (IdeleClassGroup (𝓞 (IntermediateField.fixedField (Subgroup.zpowers g))) (IntermediateField.fixedField (Subgroup.zpowers g))) := D₂.classMulDistribMulAction
    haveI : IsGalois E (IntermediateField.fixedField (Subgroup.zpowers g)) := IsGalois.of_fixedField_normal_subgroup (Subgroup.zpowers g)
    let ι : (F ≃ₐ[E] F) ⧸ Subgroup.zpowers g ≃* ((IntermediateField.fixedField (Subgroup.zpowers g)) ≃ₐ[E] (IntermediateField.fixedField (Subgroup.zpowers g))) := IsGalois.normalAutEquivQuotient (Subgroup.zpowers g)
    obtain ⟨e₃⟩ := NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_fixedField E F D hact (Subgroup.zpowers g) D₂
      (fun _ _ => rfl) ι (fun a x => AlgEquiv.restrictNormalHom_apply (IntermediateField.fixedField (Subgroup.zpowers g)) a x)
    haveI : IsCyclic ((F ≃ₐ[E] F) ⧸ Subgroup.zpowers g) :=
      isCyclic_of_surjective (QuotientGroup.mk' (Subgroup.zpowers g)) (QuotientGroup.mk'_surjective _)
    haveI hcyc' : IsCyclic ((IntermediateField.fixedField (Subgroup.zpowers g)) ≃ₐ[E] (IntermediateField.fixedField (Subgroup.zpowers g))) := isCyclic_of_surjective ι ι.surjective
    have hlt : Nat.card ((IntermediateField.fixedField (Subgroup.zpowers g)) ≃ₐ[E] (IntermediateField.fixedField (Subgroup.zpowers g))) < Nat.card (F ≃ₐ[E] F) := by
      rw [← Nat.card_congr ι.toEquiv, ← Subgroup.index_eq_card]
      have h := (Subgroup.zpowers g).card_mul_index
      rw [hNcard] at h
      have hpos : 0 < (Subgroup.zpowers g).index := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, mul_zero] at h
        exact Nat.card_pos.ne' h.symm
      rw [← h]
      exact lt_mul_of_one_lt_left hpos hq.one_lt
    have hIH := ih _ hlt E (IntermediateField.fixedField (Subgroup.zpowers g)) D₂ (fun _ _ => rfl) hcyc' rfl
    exact Limits.IsZero.of_iso (isZero_res_ofMulDistribMulAction ι 1 hIH)
      ((groupCohomology.functor ℤ ((F ≃ₐ[E] F) ⧸ Subgroup.zpowers g) 1).mapIso e₃)

  have hX₁' : Limits.IsZero (groupCohomology.H1InfRes (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) (Subgroup.zpowers g)).X₁ := by
    rw [groupCohomology.H1InfRes_X₁]; exact hX₁
  have hX₃' : Limits.IsZero (groupCohomology.H1InfRes (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) (Subgroup.zpowers g)).X₃ := by
    rw [groupCohomology.H1InfRes_X₃]; exact hX₃
  have hz := (groupCohomology.H1InfRes_exact (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) (Subgroup.zpowers g)).isZero_X₂ (hX₁'.eq_of_src _ _) (hX₃'.eq_of_tgt _ _)
  rw [groupCohomology.H1InfRes_X₂] at hz
  exact hz

end Tower

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], IsCyclic S →
      Limits.IsZero
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1) ∧
      Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S := by
  intro S _ hScyc
  haveI := hScyc

  let D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField S) F := GenuineDescent.genuineDescentDatum (IntermediateField.fixedField S) F
  letI : MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F) := D'.classMulDistribMulAction
  let ι : S ≃* (F ≃ₐ[IntermediateField.fixedField S] F) :=
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField S).symm).trans
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField S))
  obtain ⟨-, h8⟩ :=
    NumberField.IdeleClassGroup.nonempty_res_iso_fixedField_and_groupCohomology_iso E F D hact S D' (fun _ _ => rfl) ι
      (fun _ _ => rfl)
  obtain ⟨t1⟩ := h8 1
  obtain ⟨t2⟩ := h8 2
  haveI hcyc : IsCyclic (F ≃ₐ[IntermediateField.fixedField S] F) := isCyclic_of_surjective ι ι.surjective

  have hH1 : Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F)) 1) :=
    isZero_H1_top_of_isCyclic _ (IntermediateField.fixedField S) F D' (fun _ _ => rfl) hcyc rfl

  have hcard : Nat.card (F ≃ₐ[IntermediateField.fixedField S] F) = Fintype.card S := (Nat.card_congr ι.toEquiv).symm.trans Nat.card_eq_fintype_card
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := (F ≃ₐ[IntermediateField.fixedField S] F))
  have hdeg := finrank_eq_of_natCard_aut (Fintype.card S) hcard
  have hherb := (ideleClass_herbrandQuotient_eq_finrank (IntermediateField.fixedField S) F D' σ hσ).1
  obtain ⟨-, -, hc0, hc1⟩ := nonempty_tate_addEquiv_ideleClass D' σ hσ (fun _ _ => rfl)
  obtain ⟨hp0, hpneg⟩ := Rep.natCard_tateCohomology_zero_and_neg_one_of_isCyclic (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F))
  have hQ1 := hc1.symm.trans ((natCard_tateCohomology_neg_one _).symm.trans (hpneg.trans (natCard_eq_one_of_isZero hH1)))
  have hH2 : Nat.card (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F)) 2) = Fintype.card S :=
    hp0.symm.trans ((natCard_tateCohomology_zero _).trans (hc0.trans ((eq_of_eq_mul_of_eq_one hherb hQ1).trans hdeg)))
  exact ⟨hH1.of_iso t1, (natCard_eq_of_iso t2).trans hH2⟩

end S_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_isCyclic
end P2MW
export P2MW.S_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_isCyclic (solution)
