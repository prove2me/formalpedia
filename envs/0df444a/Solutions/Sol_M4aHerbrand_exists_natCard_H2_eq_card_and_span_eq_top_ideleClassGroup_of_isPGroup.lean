-- Prove2me | solution 1 for M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup_of_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/7b416a97-0001-5d4a-8b93-c5af4a1ea6ee

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_GroupCohomology_CyclicCarry
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup
import Theorems.Thm_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card_of_isPGroup
import Theorems.Thm_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_of_isScalarTower
import Theorems.Thm_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq
import Theorems.Thm_NumberField_exists_isGalois_compositum
import Theorems.Thm_NumberField_exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow
import Theorems.Thm_NumberField_compositum_isPGroup_and_normal_and_inf_eq_bot_and_exists_generators
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct
import Theorems.Thm_groupCohomology_nonempty_linearEquiv_of_iso_res_mulEquiv
import Theorems.Thm_M4aHerbrand_exists_addOrderOf_carry_eq_card_and_span_eq_top_ideleClassGroup_of_isCyclic
import Theorems.Thm_groupCohomology_map_carry_H2pi_eq_smul_carry
import Theorems.Thm_groupCohomology_carryFun_mem_cocycles2
import Theorems.Thm_NumberField_IdeleClassGroup_exists_sum_rho_pow_eq_of_forall_rho_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup_of_isPGroup
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory CategoryTheory.Limits groupCohomology Rep

namespace Ws23D1TopSketch

theorem glue_transport_card_span {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module ℤ A] [Module ℤ B]
    (e : A ≃ₗ[ℤ] B) (n : ℕ) (y : A) (hcard : Nat.card A = n) (hspan : Submodule.span ℤ {y} = ⊤) :
    Nat.card B = n ∧ Submodule.span ℤ {e y} = ⊤ := by
  refine ⟨by rw [← hcard]; exact Nat.card_congr e.toEquiv.symm, ?_⟩
  have : Submodule.span ℤ {e y} = (Submodule.span ℤ {y}).map e.toLinearMap := by
    rw [Submodule.map_span, Set.image_singleton]; rfl
  rw [this, hspan, Submodule.map_top, LinearMap.range_eq_top]
  exact e.surjective

theorem nonempty_H2_res_top_linearEquiv {k H : Type} [CommRing k] [Group H] (B : Rep k H) (n : ℕ) :
    Nonempty (groupCohomology (Rep.res (⊤ : Subgroup H).subtype B) n ≃ₗ[k] groupCohomology B n) := by
  obtain ⟨ψ, -⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv
    (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H) (Rep.res (⊤ : Subgroup H).subtype B) B (Iso.refl _) n
  exact ⟨ψ⟩

theorem exists_quotient_mulEquiv_restrict
    (E F N : Type) [Field E] [Field F] [Field N] [Algebra E F] [Algebra E N] [Algebra F N] [IsScalarTower E F N]
    [Normal E F] [FiniteDimensional E N] [Normal E N]
    (S : Subgroup (N ≃ₐ[E] N)) [S.Normal]
    (hS : ∀ g : N ≃ₐ[E] N, g ∈ S ↔ ∀ x : F, g (algebraMap F N x) = algebraMap F N x) :
    ∃ ι : (N ≃ₐ[E] N) ⧸ S ≃* (F ≃ₐ[E] F),
      ∀ (g : N ≃ₐ[E] N) (x : F), algebraMap F N (ι (QuotientGroup.mk g) x) = g (algebraMap F N x) := by
  set r : (N ≃ₐ[E] N) →* (F ≃ₐ[E] F) := AlgEquiv.restrictNormalHom F with hr
  have hker : r.ker = S := by
    ext g
    rw [MonoidHom.mem_ker, hS, AlgEquiv.ext_iff]
    refine forall_congr' fun x => ?_
    rw [AlgEquiv.one_apply, ← (algebraMap F N).injective.eq_iff, hr]
    exact Iff.of_eq (congrArg (· = _) (AlgEquiv.restrictNormal_commutes g F x))
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective r (AlgEquiv.restrictNormalHom_surjective N)), fun g x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes g F x

theorem nonempty_H2_quotientToInvariants_linearEquiv
    (E F N : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field N] [NumberField N]
    [Algebra E F] [Algebra E N] [Algebra F N] [IsScalarTower E F N] [IsGalois E F] [IsGalois E N]
    (D : IdeleGaloisDescent (𝓞 N) E N)
    [MulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)]
    (hact : ∀ (g : N ≃ₐ[E] N) (c : IdeleClassGroup (𝓞 N) N), g • c = D.classAct g c)
    (D' : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact' : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D'.classAct g c)
    (S : Subgroup (N ≃ₐ[E] N)) [S.Normal]
    (hS : ∀ g : N ≃ₐ[E] N, g ∈ S ↔ ∀ x : F, g (algebraMap F N x) = algebraMap F N x) :
    Nonempty (groupCohomology ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants S) 2 ≃ₗ[ℤ]
      groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) := by
  obtain ⟨ι, hι⟩ := exists_quotient_mulEquiv_restrict E F N S hS
  obtain ⟨φ⟩ := NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_of_isScalarTower E F N D hact D' hact' S ι hι
  obtain ⟨ψ, -⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv ι _ _ φ 2
  exact ⟨ψ⟩

theorem finite_and_natCard_H2_quotientToInvariants_le
    (E F N : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field N] [NumberField N]
    [Algebra E F] [Algebra E N] [Algebra F N] [IsScalarTower E F N] [IsGalois E F] [IsGalois E N]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 N) E N)
    [MulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)]
    (hact : ∀ (g : N ≃ₐ[E] N) (c : IdeleClassGroup (𝓞 N) N), g • c = D.classAct g c)
    (D' : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact' : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D'.classAct g c)
    (S : Subgroup (N ≃ₐ[E] N)) [S.Normal]
    (hS : ∀ g : N ≃ₐ[E] N, g ∈ S ↔ ∀ x : F, g (algebraMap F N x) = algebraMap F N x) :
    Finite (groupCohomology ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants S) 2) ∧
      Nat.card (groupCohomology ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants S) 2)
        ≤ Nat.card (F ≃ₐ[E] F) := by
  set B : Rep ℤ (F ≃ₐ[E] F) := Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F) with hB
  obtain ⟨ψ₁⟩ := nonempty_H2_quotientToInvariants_linearEquiv E F N D hact D' hact' S hS
  obtain ⟨ψ₀⟩ := nonempty_H2_res_top_linearEquiv B 2
  haveI : Fintype (⊤ : Subgroup (F ≃ₐ[E] F)) := Fintype.ofFinite _
  obtain ⟨hfin, hle⟩ :=
    NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup E F p hG D' hact' ⊤
  haveI := hfin
  refine ⟨Finite.of_equiv _ (ψ₀.toEquiv.trans ψ₁.toEquiv.symm), ?_⟩
  calc Nat.card (groupCohomology ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants S) 2)
      = Nat.card (groupCohomology B 2) := Nat.card_congr ψ₁.toEquiv
    _ = Nat.card (groupCohomology (Rep.res (⊤ : Subgroup (F ≃ₐ[E] F)).subtype B) 2) := Nat.card_congr ψ₀.toEquiv.symm
    _ ≤ Fintype.card (⊤ : Subgroup (F ≃ₐ[E] F)) := hle
    _ = Nat.card (F ≃ₐ[E] F) := by rw [← Nat.card_eq_fintype_card, Subgroup.card_top]

theorem exists_carry_generator_quotientToInvariants
    (E L N : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field N] [NumberField N]
    [Algebra E L] [Algebra E N] [Algebra L N] [IsScalarTower E L N] [IsGalois E L] [IsGalois E N]
    (D : IdeleGaloisDescent (𝓞 N) E N)
    [MulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)]
    (hact : ∀ (g : N ≃ₐ[E] N) (c : IdeleClassGroup (𝓞 N) N), g • c = D.classAct g c)
    (DL : IdeleGaloisDescent (𝓞 L) E L)
    [MulDistribMulAction (L ≃ₐ[E] L) (IdeleClassGroup (𝓞 L) L)]
    (hactL : ∀ (g : L ≃ₐ[E] L) (c : IdeleClassGroup (𝓞 L) L), g • c = DL.classAct g c)
    (T : Subgroup (N ≃ₐ[E] N)) [T.Normal]
    (hT : ∀ g : N ≃ₐ[E] N, g ∈ T ↔ ∀ x : L, g (algebraMap L N x) = algebraMap L N x)
    (s : (N ≃ₐ[E] N) ⧸ T) (hs : ∀ g, g ∈ Subgroup.zpowers s) (hsfin : IsOfFinOrder s) :
    ∃ (a₀T : (Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants T)
      (hzT : carryFun s hs hsfin a₀T ∈ cocycles₂ ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants T)),
      (∀ g : N ≃ₐ[E] N, (Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).ρ g
          (a₀T : Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)) = a₀T) ∧
      addOrderOf ((H2π ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants T)).hom
          ⟨carryFun s hs hsfin a₀T, hzT⟩) = Nat.card ((N ≃ₐ[E] N) ⧸ T) := by
  classical
  set C : Rep ℤ (N ≃ₐ[E] N) := Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N) with hC
  set BT : Rep ℤ (L ≃ₐ[E] L) := Rep.ofMulDistribMulAction (L ≃ₐ[E] L) (IdeleClassGroup (𝓞 L) L) with hBT
  obtain ⟨ιT, hιT⟩ := exists_quotient_mulEquiv_restrict E L N T hT
  obtain ⟨φT⟩ := NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_of_isScalarTower E L N D hact DL hactL T ιT hιT
  obtain ⟨ψT, hψT⟩ := groupCohomology.nonempty_linearEquiv_of_iso_res_mulEquiv ιT _ _ φT 2

  set sT : L ≃ₐ[E] L := ιT s with hsT_def
  have hsT : ∀ g : L ≃ₐ[E] L, g ∈ Subgroup.zpowers sT := by
    intro g
    obtain ⟨g', rfl⟩ := ιT.surjective g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hs g')
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk, map_zpow]⟩
  have hsTfin : IsOfFinOrder sT := isOfFinOrder_of_finite _

  obtain ⟨a, hz, hinv, hord, -⟩ :=
    M4aHerbrand.exists_addOrderOf_carry_eq_card_and_span_eq_top_ideleClassGroup_of_isCyclic E L DL hactL sT hsT hsTfin

  set a₀T : C.quotientToInvariants T := φT.inv.hom a with ha₀T_def
  have hinvT : (C.quotientToInvariants T).ρ s a₀T = a₀T := by
    rw [ha₀T_def, ← Rep.hom_comm_apply φT.inv s a]
    exact congrArg _ hinv
  have hzT : carryFun s hs hsfin a₀T ∈ cocycles₂ (C.quotientToInvariants T) :=
    groupCohomology.carryFun_mem_cocycles2 s hs hsfin a₀T hinvT
  have h3 := groupCohomology.map_carry_H2pi_eq_smul_carry ιT.toMonoidHom ιT.injective sT hsT hsTfin 1 s
    (by rw [pow_one]; rfl) hs hsfin BT (C.quotientToInvariants T) φT.inv a hinv hz hzT
  have hclass : (H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩
      = ψT.symm ((H2π BT).hom ⟨carryFun sT hsT hsTfin a, hz⟩) := by
    rw [hψT, h3, Nat.gcd_one_right, Nat.div_one, one_smul]
  refine ⟨a₀T, hzT, ?_, ?_⟩
  · intro g
    obtain ⟨k, hk⟩ := (IsOfFinOrder.mem_powers_iff_mem_zpowers hsfin).mpr (hs (QuotientGroup.mk g))
    have hfix : (C.quotientToInvariants T).ρ (QuotientGroup.mk g) a₀T = a₀T := by
      rw [← hk, map_pow]
      clear hk
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hinvT, ih]
    exact congrArg Subtype.val hfix
  · rw [hclass]
    change addOrderOf (ψT.symm.toAddEquiv ((H2π BT).hom ⟨carryFun sT hsT hsTfin a, hz⟩)) = _
    rw [AddEquiv.addOrderOf_eq, hord, ← Nat.card_eq_fintype_card, ← Nat.card_congr ιT.toEquiv]

end Ws23D1TopSketch

open Ws23D1TopSketch in

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∃ u : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)
          = Nat.card (F ≃ₐ[E] F) ∧
      Submodule.span ℤ {u} = ⊤ := by
  classical

  obtain ⟨a, ha⟩ := hG.exists_card_eq

  obtain ⟨kcyc, L, hLgal, hLcyc, hLdeg⟩ :=
    NumberField.exists_intermediateField_cyclotomicField_isCyclic_finrank_eq_pow E p a
  haveI : IsGalois E L := hLgal
  have hdeg : Module.finrank E L = Module.finrank E F := by
    rw [hLdeg, ← ha, IsGalois.card_aut_eq_finrank]

  obtain ⟨N, _, _, _, _, _, _, _, hNgal, hgen⟩ := NumberField.exists_isGalois_compositum E F L
  haveI : IsGalois E N := hNgal

  set FN : IntermediateField E N := (IsScalarTower.toAlgHom E F N).fieldRange with hFN
  set LN : IntermediateField E N := (IsScalarTower.toAlgHom E L N).fieldRange with hLN
  set S : Subgroup (N ≃ₐ[E] N) := FN.fixingSubgroup with hS_def
  set T : Subgroup (N ≃ₐ[E] N) := LN.fixingSubgroup with hT_def
  have hS : ∀ g : N ≃ₐ[E] N, g ∈ S ↔ ∀ x : F, g (algebraMap F N x) = algebraMap F N x := by
    intro g
    rw [hS_def, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x; exact h _ ⟨x, rfl⟩
    · rintro h _ ⟨x, rfl⟩; exact h x
  have hT : ∀ g : N ≃ₐ[E] N, g ∈ T ↔ ∀ x : L, g (algebraMap L N x) = algebraMap L N x := by
    intro g
    rw [hT_def, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x; exact h _ ⟨x, rfl⟩
    · rintro h _ ⟨x, rfl⟩; exact h x

  obtain ⟨hΓ, hSn, hTn, hST, hcardq, ⟨s, hs, hn⟩, ⟨t, ht⟩⟩ :=
    NumberField.compositum_isPGroup_and_normal_and_inf_eq_bot_and_exists_generators E F L N p hG hLcyc hdeg hgen
  haveI : S.Normal := hSn
  haveI : T.Normal := hTn
  haveI : Fintype ((N ≃ₐ[E] N) ⧸ S) := Fintype.ofFinite _
  have hn' : orderOf s = Fintype.card ((N ≃ₐ[E] N) ⧸ S) := by rw [← Nat.card_eq_fintype_card]; exact hn
  have hsfin : IsOfFinOrder s := isOfFinOrder_of_finite s

  set DN : IdeleGaloisDescent (𝓞 N) E N := M4aHerbrand.GenuineDescent.genuineDescentDatum E N with hDN
  obtain ⟨instN, hactN⟩ := M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct E N DN
  set DL : IdeleGaloisDescent (𝓞 L) E L := M4aHerbrand.GenuineDescent.genuineDescentDatum E L with hDL
  obtain ⟨instL, hactL⟩ := M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct E L DL

  obtain ⟨hfin, hle⟩ := finite_and_natCard_H2_quotientToInvariants_le E F N p hG DN hactN D hact S hS

  obtain ⟨a₀T, hzT, ha₀, hord⟩ := exists_carry_generator_quotientToInvariants E L N DN hactN DL hactL T hT s hs hsfin

  have hnorm := NumberField.IdeleClassGroup.exists_sum_rho_pow_eq_of_forall_rho_eq E F L N DN hactN S T hS hT hST
    s hs (dvd_of_eq hn) t ht (a₀T : Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)) ha₀

  have hS1 := NumberField.IdeleClassGroup.isZero_H1_of_isPGroup E N p hΓ DN hactN S
  have hT1 := NumberField.IdeleClassGroup.isZero_H1_of_isPGroup E N p hΓ DN hactN T

  have hord' : addOrderOf ((H2π ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants T)).hom
      ⟨carryFun s hs hsfin a₀T, hzT⟩) = Fintype.card ((N ≃ₐ[E] N) ⧸ S) := by
    rw [hord, ← orderOf_eq_card_of_forall_mem_zpowers hs, hn']
  have hle' : Nat.card (groupCohomology ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants S) 2)
      ≤ Fintype.card ((N ≃ₐ[E] N) ⧸ S) := by
    rw [← Nat.card_eq_fintype_card]; exact hle.trans_eq hcardq.symm
  have hnorm' : ∃ b : Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N),
      (∑ i ∈ Finset.range (orderOf t),
        (Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).ρ ((t : N ≃ₐ[E] N) ^ i) b) =
          (Fintype.card ((N ≃ₐ[E] N) ⧸ S) / Fintype.card ((N ≃ₐ[E] N) ⧸ S)) •
            (a₀T : Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)) := by
    rw [Nat.div_self Fintype.card_pos, one_smul]; exact hnorm

  obtain ⟨y, hcard, hspan, -⟩ :=
    groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq
      (Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)) S T hST hS1 hT1
      s hs hsfin t ht (isOfFinOrder_of_finite t) _ hn' dvd_rfl a₀T _ rfl ha₀ hzT hord' hnorm' hfin hle'

  obtain ⟨e⟩ := nonempty_H2_quotientToInvariants_linearEquiv E F N DN hactN D hact S hS
  obtain ⟨hcardF, hspanF⟩ := glue_transport_card_span e _ y hcard hspan
  refine ⟨e y, hcardF.trans ?_, hspanF⟩
  rw [← Nat.card_eq_fintype_card]; exact hcardq

end S_M4aHerbrand_exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup_of_isPGroup
end P2MW
export P2MW.S_M4aHerbrand_exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup_of_isPGroup (solution)
