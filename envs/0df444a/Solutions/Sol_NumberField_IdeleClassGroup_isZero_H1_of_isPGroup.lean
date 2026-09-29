-- Prove2me | solution 1 for NumberField.IdeleClassGroup.isZero_H1_of_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/597fe9ee-2be0-5467-8693-2a412c7f95db

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_res_iso_fixedField_and_groupCohomology_iso
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_fixedField
import Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_card_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

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

private theorem isZero_of_isZero_res (ι : S ≃* G') (ρ : Representation ℤ G' V) (n : ℕ)
    (h : Limits.IsZero (groupCohomology (Rep.res ι.toMonoidHom (Rep.of ρ)) n)) :
    Limits.IsZero (groupCohomology (Rep.of ρ) n) := by
  obtain ⟨t⟩ := nonempty_groupCohomology_res_iso ι ρ n
  exact h.of_iso t.symm

end Transport

section Induction

open M4aHerbrand.GenuineDescent

private theorem isZero_H1_top (m : ℕ) :
    ∀ (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
      (p : ℕ) [Fact p.Prime] (_hG : IsPGroup p (F ≃ₐ[E] F))
      (D : IdeleGaloisDescent (𝓞 F) E F)
      [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
      (_hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c),
      Nat.card (F ≃ₐ[E] F) = m →
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 1) := by
  induction' m using Nat.strong_induction_on with m ih
  intro E F _ _ _ _ _ _ p _ hG D _ hact hm
  have hp : p.Prime := Fact.out
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hG
  rw [← hm] at ih
  rcases e with _ | e
  ·
    rw [pow_zero] at he
    haveI : Subsingleton (F ≃ₐ[E] F) := (Nat.card_eq_one_iff_unique.mp he).1
    exact isZero_groupCohomology_succ_of_subsingleton _ 0

  obtain ⟨N, hN⟩ := Sylow.exists_subgroup_card_pow_prime p (n := e)
    (show p ^ e ∣ Nat.card (F ≃ₐ[E] F) by rw [he]; exact pow_dvd_pow p e.le_succ)
  have hidx : N.index = p := by
    have h1 := N.card_mul_index
    rw [hN, he, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos e) h1
  haveI hNn : N.Normal := Subgroup.normal_of_index_eq_minFac_card
    (by rw [hidx, he, Nat.Prime.pow_minFac hp (k := e + 1) (Nat.succ_ne_zero e)])

  have hX₃ : Limits.IsZero (groupCohomology (Rep.res N.subtype
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1) := by
    let D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField N) F :=
      genuineDescentDatum (IntermediateField.fixedField N) F
    letI : MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField N] F) (IdeleClassGroup (𝓞 F) F) :=
      D'.classMulDistribMulAction
    let ι : N ≃* (F ≃ₐ[IntermediateField.fixedField N] F) :=
      (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField N).symm).trans
        (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField N))
    obtain ⟨-, h8⟩ :=
      NumberField.IdeleClassGroup.nonempty_res_iso_fixedField_and_groupCohomology_iso E F D hact N D' (fun _ _ => rfl) ι (fun _ _ => rfl)
    obtain ⟨t⟩ := h8 1
    have hcard : Nat.card (F ≃ₐ[IntermediateField.fixedField N] F) = p ^ e := by
      rw [← Nat.card_congr ι.toEquiv, hN]
    have hlt : Nat.card (F ≃ₐ[IntermediateField.fixedField N] F) < Nat.card (F ≃ₐ[E] F) := by
      rw [hcard, he]
      exact Nat.pow_lt_pow_right hp.one_lt e.lt_succ_self
    exact Limits.IsZero.of_iso
      (ih _ hlt (IntermediateField.fixedField N) F p ((hG.to_subgroup N).of_equiv ι) D' (fun _ _ => rfl) rfl) t

  have hX₁ : Limits.IsZero (groupCohomology
      ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)).quotientToInvariants N) 1) := by
    let D₂ : IdeleGaloisDescent (𝓞 (IntermediateField.fixedField N)) E (IntermediateField.fixedField N) :=
      genuineDescentDatum E (IntermediateField.fixedField N)
    letI : MulDistribMulAction ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N))
        (IdeleClassGroup (𝓞 (IntermediateField.fixedField N)) (IntermediateField.fixedField N)) :=
      D₂.classMulDistribMulAction
    haveI : IsGalois E (IntermediateField.fixedField N) := IsGalois.of_fixedField_normal_subgroup N
    let ι : (F ≃ₐ[E] F) ⧸ N ≃* ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N)) :=
      IsGalois.normalAutEquivQuotient N
    obtain ⟨e₃⟩ :=
      NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_fixedField E F D hact N D₂ (fun _ _ => rfl) ι
      (fun a x => AlgEquiv.restrictNormalHom_apply (IntermediateField.fixedField N) a x)
    refine Limits.IsZero.of_iso ?_ ((groupCohomology.functor ℤ ((F ≃ₐ[E] F) ⧸ N) 1).mapIso e₃)

    show Limits.IsZero (groupCohomology (Rep.res ι.toMonoidHom (Rep.of (Representation.ofMulDistribMulAction
      ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N))
      (IdeleClassGroup (𝓞 (IntermediateField.fixedField N)) (IntermediateField.fixedField N))))) 1)
    refine isZero_res_of_isZero ι _ 1 ?_
    haveI : Fintype (⊤ : Subgroup ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N))) :=
      Fintype.ofFinite _
    have hprime : (Fintype.card
        (⊤ : Subgroup ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N)))).Prime := by
      rw [← Nat.card_eq_fintype_card, Subgroup.card_top, ← Nat.card_congr ι.toEquiv, ← Subgroup.index_eq_card, hidx]
      exact hp
    have h2 :=
      (NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime E (IntermediateField.fixedField N) D₂ (fun _ _ => rfl) ⊤ hprime).1
    let τ : (⊤ : Subgroup ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N))) ≃*
        ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N)) := Subgroup.topEquiv
    have htop : τ.toMonoidHom =
        (⊤ : Subgroup ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N))).subtype :=
      MonoidHom.ext fun _ => rfl
    refine isZero_of_isZero_res τ _ 1 ?_
    rw [htop]
    exact h2

  have hX₁' : Limits.IsZero (groupCohomology.H1InfRes
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) N).X₁ := by
    rw [groupCohomology.H1InfRes_X₁]; exact hX₁
  have hX₃' : Limits.IsZero (groupCohomology.H1InfRes
      (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) N).X₃ := by
    rw [groupCohomology.H1InfRes_X₃]; exact hX₃
  have hz := (groupCohomology.H1InfRes_exact
    (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) N).isZero_X₂
    (hX₁'.eq_of_src _ _) (hX₃'.eq_of_tgt _ _)
  rw [groupCohomology.H1InfRes_X₂] at hz
  exact hz

end Induction

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∀ S : Subgroup (F ≃ₐ[E] F), Limits.IsZero
      (groupCohomology (Rep.res S.subtype
        (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1) := by
  intro S
  let D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField S) F :=
    GenuineDescent.genuineDescentDatum (IntermediateField.fixedField S) F
  letI : MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F) :=
    D'.classMulDistribMulAction
  let ι : S ≃* (F ≃ₐ[IntermediateField.fixedField S] F) :=
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField S).symm).trans
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField S))
  obtain ⟨-, h8⟩ :=
    NumberField.IdeleClassGroup.nonempty_res_iso_fixedField_and_groupCohomology_iso E F D hact S D' (fun _ _ => rfl) ι (fun _ _ => rfl)
  obtain ⟨t⟩ := h8 1
  exact Limits.IsZero.of_iso
    (isZero_H1_top _ (IntermediateField.fixedField S) F p ((hG.to_subgroup S).of_equiv ι) D' (fun _ _ => rfl) rfl) t

end S_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup
end P2MW
export P2MW.S_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup (solution)
