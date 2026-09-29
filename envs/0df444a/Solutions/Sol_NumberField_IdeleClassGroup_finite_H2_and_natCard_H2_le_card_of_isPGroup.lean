-- Prove2me | solution 1 for NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cc95c88e-3a66-5272-a66f-b0b77080eb6c

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_groupCohomology_finite_H2_and_natCard_H2_le_of_isSolvable
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_res_iso_fixedField_and_groupCohomology_iso
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_fixedField
import Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_card_prime
import Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card_of_isPGroup
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

private theorem natCard_res_eq (ι : S ≃* G') (ρ : Representation ℤ G' V) (n : ℕ) :
    Nat.card (groupCohomology (Rep.res ι.toMonoidHom (Rep.of ρ)) n) =
      Nat.card (groupCohomology (Rep.of ρ) n) := by
  obtain ⟨t⟩ := nonempty_groupCohomology_res_iso ι ρ n
  exact Nat.card_congr t.toLinearEquiv.toEquiv

private theorem natCard_eq_of_repIso {X Y : Rep ℤ S} (e : X ≅ Y) (n : ℕ) :
    Nat.card (groupCohomology X n) = Nat.card (groupCohomology Y n) :=
  Nat.card_congr ((groupCohomology.functor ℤ S n).mapIso e).toLinearEquiv.toEquiv

end Transport

section QuotientTransport
variable {H G₂ V : Type} [Group H] [Group G₂] [AddCommGroup V]

private theorem invariants_comp_eq (θ : H ≃* G₂) (ρ : Representation ℤ G₂ V) (N : Subgroup H) :
    Representation.invariants ((ρ.comp θ.toMonoidHom).comp N.subtype) =
      Representation.invariants (ρ.comp (N.map θ.toMonoidHom).subtype) := by
  ext v
  simp only [Representation.mem_invariants]
  constructor
  · rintro h ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    exact h ⟨n, hn⟩
  · intro h n
    exact h ⟨θ.toMonoidHom n, Subgroup.mem_map_of_mem θ.toMonoidHom n.2⟩

private theorem map_normal (θ : H ≃* G₂) (N : Subgroup H) [hN : N.Normal] : (N.map θ.toMonoidHom).Normal :=
  hN.map θ.toMonoidHom θ.surjective

private noncomputable def quotCongr (θ : H ≃* G₂) (N : Subgroup H) [N.Normal] [(N.map θ.toMonoidHom).Normal] :
    H ⧸ N ≃* G₂ ⧸ N.map θ.toMonoidHom :=
  QuotientGroup.congr N (N.map θ.toMonoidHom) θ rfl

private noncomputable def quotientToInvariantsIso (θ : H ≃* G₂) (ρ : Representation ℤ G₂ V) (N : Subgroup H) [N.Normal]
    [(N.map θ.toMonoidHom).Normal] :
    (Rep.of (ρ.comp θ.toMonoidHom)).quotientToInvariants N ≅
      Rep.res (quotCongr θ N).toMonoidHom ((Rep.of ρ).quotientToInvariants (N.map θ.toMonoidHom)) :=
  Rep.mkIso (Representation.Equiv.mk
    (ρ := Representation.quotientToInvariants (ρ.comp θ.toMonoidHom) N)
    (σ := (Representation.quotientToInvariants ρ (N.map θ.toMonoidHom)).comp (quotCongr θ N).toMonoidHom)
    (LinearEquiv.ofEq _ _ (invariants_comp_eq θ ρ N))
    (fun x => QuotientGroup.induction_on x fun _ => LinearMap.ext fun _ => Subtype.ext rfl))

private theorem natCard_quotientToInvariants (θ : H ≃* G₂) (ρ : Representation ℤ G₂ V) (N : Subgroup H)
    [N.Normal] [(N.map θ.toMonoidHom).Normal] (n : ℕ) :
    Nat.card (groupCohomology ((Rep.of (ρ.comp θ.toMonoidHom)).quotientToInvariants N) n) =
      Nat.card (groupCohomology ((Rep.of ρ).quotientToInvariants (N.map θ.toMonoidHom)) n) :=
  (natCard_eq_of_repIso (quotientToInvariantsIso θ ρ N) n).trans (natCard_res_eq (quotCongr θ N) _ n)

end QuotientTransport

section Generic
variable {G K G₂ G₃ C C₃ : Type} [Group G] [Group K] [Group G₂] [Group G₃] [CommGroup C] [CommGroup C₃]
  [MulDistribMulAction G C] [MulDistribMulAction G₂ C] [MulDistribMulAction G₃ C₃]

private theorem subsingleton_H1_res (φ : K →* G) (hφ : Function.Injective φ)
    (h : Limits.IsZero (groupCohomology (Rep.res φ.range.subtype (Rep.ofMulDistribMulAction G C)) 1)) :
    Subsingleton (groupCohomology.H1 (Rep.res φ (Rep.ofMulDistribMulAction G C))) := by
  have hφ' : φ.range.subtype.comp (MonoidHom.ofInjective hφ).toMonoidHom = φ := MonoidHom.ext fun _ => rfl
  rw [← hφ']
  exact ModuleCat.subsingleton_of_isZero (isZero_res_of_isZero (MonoidHom.ofInjective hφ)
    ((Representation.ofMulDistribMulAction G C).comp φ.range.subtype) 1 h)

private theorem natCard_H2_quotientToInvariants_res (φ : K →* G) (hφ : Function.Injective φ) (ι : φ.range ≃* G₂)
    (e₈ : Rep.res φ.range.subtype (Rep.ofMulDistribMulAction G C) ≅
      Rep.res ι.toMonoidHom (Rep.ofMulDistribMulAction G₂ C))
    (N : Subgroup K) [N.Normal] [(N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom).Normal] :
    Nat.card (groupCohomology ((Rep.res φ (Rep.ofMulDistribMulAction G C)).quotientToInvariants N) 2) =
      Nat.card (groupCohomology ((Rep.ofMulDistribMulAction G₂ C).quotientToInvariants
        (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) 2) := by
  have hφ' : φ.range.subtype.comp (MonoidHom.ofInjective hφ).toMonoidHom = φ := MonoidHom.ext fun _ => rfl
  have c₀ : Nat.card (groupCohomology ((Rep.res φ (Rep.ofMulDistribMulAction G C)).quotientToInvariants N) 2) =
      Nat.card (groupCohomology ((Rep.res (φ.range.subtype.comp (MonoidHom.ofInjective hφ).toMonoidHom)
        (Rep.ofMulDistribMulAction G C)).quotientToInvariants N) 2) := by
    rw [hφ']
  exact c₀.trans ((natCard_eq_of_repIso ((Rep.quotientToInvariantsFunctor ℤ N).mapIso
    ((Rep.resFunctor (MonoidHom.ofInjective hφ).toMonoidHom).mapIso e₈)) 2).trans
    (natCard_quotientToInvariants ((MonoidHom.ofInjective hφ).trans ι) (Representation.ofMulDistribMulAction G₂ C) N 2))

private theorem natCard_H2_quotientToInvariants_eq_top (M : Subgroup G₂) [M.Normal] (ι₃ : G₂ ⧸ M ≃* G₃)
    (e₃ : (Rep.ofMulDistribMulAction G₂ C).quotientToInvariants M ≅
      Rep.res ι₃.toMonoidHom (Rep.ofMulDistribMulAction G₃ C₃)) :
    Nat.card (groupCohomology ((Rep.ofMulDistribMulAction G₂ C).quotientToInvariants M) 2) =
      Nat.card (groupCohomology (Rep.res (⊤ : Subgroup G₃).subtype (Rep.ofMulDistribMulAction G₃ C₃)) 2) := by
  have htop : (Subgroup.topEquiv : (⊤ : Subgroup G₃) ≃* G₃).toMonoidHom = (⊤ : Subgroup G₃).subtype :=
    MonoidHom.ext fun _ => rfl
  have c₅ := natCard_res_eq (Subgroup.topEquiv : (⊤ : Subgroup G₃) ≃* G₃)
    (Representation.ofMulDistribMulAction G₃ C₃) 2
  rw [htop] at c₅
  exact (natCard_eq_of_repIso e₃ 2).trans
    ((natCard_res_eq ι₃ (Representation.ofMulDistribMulAction G₃ C₃) 2).trans c₅.symm)

end Generic

section Dock

open M4aHerbrand.GenuineDescent

private theorem finite_H2_top
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    Finite (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) ≤
        Nat.card (F ≃ₐ[E] F) := by
  haveI := hG.isNilpotent
  refine groupCohomology.finite_H2_and_natCard_H2_le_of_isSolvable
    (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ?_ ?_
  ·
    intro K _ _ φ hφ
    exact subsingleton_H1_res φ hφ (NumberField.IdeleClassGroup.isZero_H1_of_isPGroup E F p hG D hact φ.range)
  ·
    intro K _ _ φ hφ N hNn hq

    let D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField φ.range) F := genuineDescentDatum (IntermediateField.fixedField φ.range) F
    letI : MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField φ.range] F) (IdeleClassGroup (𝓞 F) F) := D'.classMulDistribMulAction
    let ι : φ.range ≃* (F ≃ₐ[IntermediateField.fixedField φ.range] F) :=
      (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField φ.range).symm).trans
        (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField φ.range))
    obtain ⟨⟨e₈⟩, -⟩ := NumberField.IdeleClassGroup.nonempty_res_iso_fixedField_and_groupCohomology_iso E F D hact φ.range D' (fun _ _ => rfl) ι (fun _ _ => rfl)
    haveI := map_normal ((MonoidHom.ofInjective hφ).trans ι) N
    have cA := natCard_H2_quotientToInvariants_res φ hφ ι e₈ N

    let D₂ : IdeleGaloisDescent (𝓞 (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom))) (IntermediateField.fixedField φ.range) (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) := genuineDescentDatum (IntermediateField.fixedField φ.range) (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom))
    letI : MulDistribMulAction ((IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) ≃ₐ[IntermediateField.fixedField φ.range] (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom))) (IdeleClassGroup (𝓞 (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom))) (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom))) := D₂.classMulDistribMulAction
    haveI : IsGalois (IntermediateField.fixedField φ.range) (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) := IsGalois.of_fixedField_normal_subgroup (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)
    let ι₃ : (F ≃ₐ[IntermediateField.fixedField φ.range] F) ⧸ N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom ≃* ((IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) ≃ₐ[IntermediateField.fixedField φ.range] (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom))) :=
      IsGalois.normalAutEquivQuotient (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)
    obtain ⟨e₃⟩ := NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_fixedField (IntermediateField.fixedField φ.range) F D' (fun _ _ => rfl)
      (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom) D₂ (fun _ _ => rfl) ι₃ (fun a x => AlgEquiv.restrictNormalHom_apply (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) a x)
    have cB := natCard_H2_quotientToInvariants_eq_top (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom) ι₃ e₃
    haveI : FiniteDimensional (IntermediateField.fixedField φ.range) (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) := IntermediateField.finiteDimensional_left (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom))
    haveI : Fintype ((IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) ≃ₐ[IntermediateField.fixedField φ.range] (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom))) := AlgEquiv.fintype (IntermediateField.fixedField φ.range) (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom))
    haveI : Fintype (⊤ : Subgroup ((IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) ≃ₐ[IntermediateField.fixedField φ.range] (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)))) := @Fintype.ofFinite _ (@Subtype.finite _ (Finite.of_fintype _) _)
    have hcardTop : Fintype.card (⊤ : Subgroup ((IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) ≃ₐ[IntermediateField.fixedField φ.range] (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)))) = Nat.card (K ⧸ N) := by
      rw [← Nat.card_eq_fintype_card, Subgroup.card_top, ← Nat.card_congr ι₃.toEquiv,
        ← Nat.card_congr (quotCongr ((MonoidHom.ofInjective hφ).trans ι) N).toEquiv]
    have r2 := (NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime (IntermediateField.fixedField φ.range) (IntermediateField.fixedField (N.map ((MonoidHom.ofInjective hφ).trans ι).toMonoidHom)) D₂ (fun _ _ => rfl) ⊤ (by rw [hcardTop]; exact hq)).2
    have hcard : Nat.card (groupCohomology ((Rep.res φ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F)
        (IdeleClassGroup (𝓞 F) F))).quotientToInvariants N) 2) = Nat.card (K ⧸ N) :=
      cA.trans (cB.trans (r2.trans hcardTop))
    have hne : Nat.card (groupCohomology ((Rep.res φ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F)
        (IdeleClassGroup (𝓞 F) F))).quotientToInvariants N) 2) ≠ 0 := by
      rw [hcard]; exact hq.ne_zero
    exact ⟨Nat.finite_of_card_ne_zero hne, hcard.le⟩

end Dock

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Finite
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ∧
      Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ≤ Fintype.card S := by
  intro S _
  let D' : IdeleGaloisDescent (𝓞 F) (IntermediateField.fixedField S) F :=
    GenuineDescent.genuineDescentDatum (IntermediateField.fixedField S) F
  letI : MulDistribMulAction (F ≃ₐ[IntermediateField.fixedField S] F) (IdeleClassGroup (𝓞 F) F) :=
    D'.classMulDistribMulAction
  let ι : S ≃* (F ≃ₐ[IntermediateField.fixedField S] F) :=
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField S).symm).trans
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField S))
  obtain ⟨-, h8⟩ := NumberField.IdeleClassGroup.nonempty_res_iso_fixedField_and_groupCohomology_iso E F D hact S D' (fun _ _ => rfl) ι (fun _ _ => rfl)
  obtain ⟨t⟩ := h8 2
  obtain ⟨hfin, hle⟩ :=
    finite_H2_top (IntermediateField.fixedField S) F p ((hG.to_subgroup S).of_equiv ι) D' (fun _ _ => rfl)
  haveI := hfin
  refine ⟨Finite.of_equiv _ t.toLinearEquiv.toEquiv.symm, ?_⟩
  exact (Nat.card_congr t.toLinearEquiv.toEquiv).trans_le (hle.trans_eq
    (by rw [← Nat.card_eq_fintype_card, Nat.card_congr ι.toEquiv]))

end S_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card_of_isPGroup
end P2MW
export P2MW.S_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card_of_isPGroup (solution)
