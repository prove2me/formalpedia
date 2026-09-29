-- Prove2me | solution 1 for NumberField.IdeleClassGroup.exists_sum_rho_pow_eq_of_forall_rho_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/cfbfb8d4-a376-531a-a700-451222a3dda0

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_NumberField_pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_M4aHerbrand_Bridge_genuineBeta_comp_of_tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleClassGroup_exists_sum_rho_pow_eq_of_forall_rho_eq
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false
set_option maxHeartbeats 3200000
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin CategoryTheory
open scoped IsMulCommutative

theorem solution
    (E F L N : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field L] [NumberField L]
    [Field N] [NumberField N]
    [Algebra E F] [Algebra E L] [Algebra E N] [Algebra F N] [Algebra L N]
    [IsScalarTower E F N] [IsScalarTower E L N] [IsGalois E F] [IsGalois E L] [IsGalois E N]
    (D : IdeleGaloisDescent (𝓞 N) E N)
    [MulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)]
    (hact : ∀ (g : N ≃ₐ[E] N) (c : IdeleClassGroup (𝓞 N) N), g • c = D.classAct g c)
    (S T : Subgroup (N ≃ₐ[E] N)) [S.Normal] [T.Normal]
    (hS : ∀ g : N ≃ₐ[E] N, g ∈ S ↔ ∀ x : F, g (algebraMap F N x) = algebraMap F N x)
    (hT : ∀ g : N ≃ₐ[E] N, g ∈ T ↔ ∀ x : L, g (algebraMap L N x) = algebraMap L N x)
    (hST : S ⊓ T = ⊥)
    (s : (N ≃ₐ[E] N) ⧸ T) (hs : ∀ g, g ∈ Subgroup.zpowers s) (hn : orderOf s ∣ Nat.card ((N ≃ₐ[E] N) ⧸ S))
    (t : S) (ht : ∀ g : S, g ∈ Subgroup.zpowers t)
    (a₀ : Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N))
    (ha₀ : ∀ g : N ≃ₐ[E] N, (Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).ρ g a₀ = a₀) :
    ∃ b : Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N),
      (∑ i ∈ Finset.range (orderOf t),
        (Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).ρ ((t : N ≃ₐ[E] N) ^ i) b) = a₀ := by
  classical

  haveI : FiniteDimensional E N := Module.Finite.of_restrictScalars_finite ℚ E N
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : IsGalois F N := IsGalois.tower_top_of_isGalois E F N

  let rS : (N ≃ₐ[F] N) →* (N ≃ₐ[E] N) :=
    { toFun := fun σ => σ.restrictScalars E
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  have hrS : ∀ (σ : N ≃ₐ[F] N) (x : N), rS σ x = σ x := fun _ _ => rfl
  have hrS_inj : Function.Injective rS := fun σ σ' h => AlgEquiv.ext fun x => by
    rw [← hrS σ x, ← hrS σ' x, h]
  have hrS_mem : ∀ σ : N ≃ₐ[F] N, rS σ ∈ S := fun σ => (hS _).mpr fun x => by rw [hrS]; exact σ.commutes x

  have hScomm : ∀ a b : S, a * b = b * a := by
    intro a b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (ht a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (ht b)
    rw [← zpow_add, ← zpow_add, add_comm]
  haveI : IsMulCommutative (N ≃ₐ[F] N) := ⟨⟨fun σ σ' => hrS_inj (by
    have h := congrArg Subtype.val (hScomm ⟨rS σ, hrS_mem σ⟩ ⟨rS σ', hrS_mem σ'⟩)
    simpa using h)⟩⟩

  let liftS : S → (N ≃ₐ[F] N) := fun g =>
    AlgEquiv.ofRingEquiv (f := (g : N ≃ₐ[E] N).toRingEquiv) (fun x => (hS g).mp g.2 x)
  have hliftS : ∀ (g : S) (x : N), liftS g x = (g : N ≃ₐ[E] N) x := fun _ _ => rfl
  let eS : (N ≃ₐ[F] N) ≃ S :=
    { toFun := fun σ => ⟨rS σ, hrS_mem σ⟩
      invFun := liftS
      left_inv := fun σ => AlgEquiv.ext fun x => by rw [hliftS]; rfl
      right_inv := fun g => Subtype.ext (AlgEquiv.ext fun x => by
        show rS (liftS g) x = _
        rw [hrS, hliftS]) }

  let rL : (N ≃ₐ[E] N) →* (L ≃ₐ[E] L) := AlgEquiv.restrictNormalHom L
  have memT : ∀ σ : N ≃ₐ[E] N, σ ∈ T ↔ rL σ = 1 := by
    intro σ
    rw [hT]
    constructor
    · intro h
      apply AlgEquiv.ext
      intro y
      apply (algebraMap L N).injective
      show algebraMap L N (σ.restrictNormal L y) = algebraMap L N y
      rw [AlgEquiv.restrictNormal_commutes, h y]
    · intro h y
      have hy := AlgEquiv.restrictNormal_commutes σ L y
      have h' : σ.restrictNormal L = 1 := h
      rw [h', AlgEquiv.one_apply] at hy
      exact hy.symm
  have surjL : Function.Surjective rL := AlgEquiv.restrictNormalHom_surjective N
  haveI : IsMulCommutative (L ≃ₐ[E] L) := ⟨⟨fun g g' => by
    obtain ⟨γ, rfl⟩ := surjL g
    obtain ⟨γ', rfl⟩ := surjL g'
    rw [← map_mul, ← map_mul]

    have hq : (QuotientGroup.mk (γ * γ') : (N ≃ₐ[E] N) ⧸ T) = QuotientGroup.mk (γ' * γ) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hs (QuotientGroup.mk γ))
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hs (QuotientGroup.mk γ'))
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    rw [QuotientGroup.eq] at hq
    have hk : (γ * γ')⁻¹ * (γ' * γ) ∈ rL.ker := (memT _).mp hq
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
    exact hk⟩⟩

  let rF : (N ≃ₐ[E] N) →* (F ≃ₐ[E] F) := AlgEquiv.restrictNormalHom F
  have memS : ∀ σ : N ≃ₐ[E] N, σ ∈ S ↔ rF σ = 1 := by
    intro σ
    rw [hS]
    constructor
    · intro h
      apply AlgEquiv.ext
      intro y
      apply (algebraMap F N).injective
      show algebraMap F N (σ.restrictNormal F y) = algebraMap F N y
      rw [AlgEquiv.restrictNormal_commutes, h y]
    · intro h y
      have hy := AlgEquiv.restrictNormal_commutes σ F y
      have h' : σ.restrictNormal F = 1 := h
      rw [h', AlgEquiv.one_apply] at hy
      exact hy.symm
  have kerF : S = rF.ker := Subgroup.ext fun σ => by rw [memS, MonoidHom.mem_ker]
  have surjF : Function.Surjective rF := AlgEquiv.restrictNormalHom_surjective N
  have hcardS : Nat.card ((N ≃ₐ[E] N) ⧸ S) = Module.finrank E F := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq kerF).trans
      (QuotientGroup.quotientKerEquivOfSurjective rF surjF)).toEquiv, IsGalois.card_aut_eq_finrank]

  have hexp : ∀ g : L ≃ₐ[E] L, g ^ Module.finrank E F = 1 := by
    intro g
    obtain ⟨γ, rfl⟩ := surjL g
    rw [← map_pow]
    have hT' : γ ^ Module.finrank E F ∈ T := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hs (QuotientGroup.mk γ))
      rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        orderOf_dvd_iff_pow_eq_one.mp (hn.trans (dvd_of_eq hcardS)), one_zpow]
    exact (memT _).mp hT'

  have hinj : Function.Injective (resHom E L F N) := by
    intro σ σ' h
    have h1 : resHom E L F N (σ * σ'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have hTmem : rS (σ * σ'⁻¹) ∈ T := (memT _).mpr h1
    have hbot : rS (σ * σ'⁻¹) ∈ S ⊓ T := ⟨hrS_mem _, hTmem⟩
    rw [hST, Subgroup.mem_bot] at hbot
    exact mul_inv_eq_one.mp (hrS_inj (by rw [hbot, map_one]))

  let A := Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)
  have hρ : ∀ (g : N ≃ₐ[E] N) (c : IdeleClassGroup (𝓞 N) N),
      A.ρ g (Additive.ofMul c) = Additive.ofMul (D.classAct g c) := fun g c => by
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply, hact]; rfl
  obtain ⟨ũ, hũ⟩ := QuotientGroup.mk_surjective (Additive.toMul a₀)
  have hclass : ∀ τ : N ≃ₐ[E] N, D.classAct τ (Additive.toMul a₀) = Additive.toMul a₀ := by
    intro τ
    have h := ha₀ τ
    rw [show a₀ = Additive.ofMul (Additive.toMul a₀) from rfl, hρ] at h
    exact Additive.ofMul.injective h
  have hfix : ∀ τ : N ≃ₐ[E] N, (D.unitsAct τ ũ)⁻¹ * ũ ∈ principalIdeles (𝓞 N) N := by
    intro τ
    rw [← QuotientGroup.eq]
    show D.classAct τ (QuotientGroup.mk ũ) = QuotientGroup.mk ũ
    rw [hũ]
    exact hclass τ
  obtain ⟨-, -, hH90, -⟩ := M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm E N D
  obtain ⟨x, ⟨u, rfl⟩, p, hp, hxp⟩ := Subgroup.mem_sup.mp (hH90 ũ hfix)
  have ha₀u : a₀ = Additive.ofMul (QuotientGroup.mk (Units.map (genuineBaseChange E N).β.toMonoidHom u)) := by
    show Additive.ofMul (Additive.toMul a₀) = _
    congr 1
    refine hũ.symm.trans ?_
    rw [← hxp, QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right]
    exact Subgroup.inv_mem _ hp

  have hnpos : 0 < Module.finrank E F := Module.finrank_pos
  have hmem := NumberField.pow_map_genuineBaseChange_mem_principalIdeles_sup_range_idelicNorm
    E F N L hinj (Module.finrank E F) hexp dvd_rfl u
  rw [Nat.div_self hnpos, pow_one] at hmem
  obtain ⟨q, ⟨α, rfl⟩, y, ⟨v, rfl⟩, hqv⟩ := Subgroup.mem_sup.mp hmem

  let DF : IdeleGaloisDescent (𝓞 N) F N :=
    { act := D.act.comp rS
      compat := fun σ x => D.compat (rS σ) x
      continuous_act := fun σ => D.continuous_act (rS σ) }
  have hDF : ∀ (σ : N ≃ₐ[F] N) (w : (AdeleRing (𝓞 N) N)ˣ), DF.unitsAct σ w = D.unitsAct (rS σ) w := fun _ _ => rfl
  obtain ⟨-, -, -, hprodF⟩ := M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm F N DF
  have htower : Units.map (genuineBaseChange F N).β.toMonoidHom (Units.map (genuineBaseChange E F).β.toMonoidHom u)
      = Units.map (genuineBaseChange E N).β.toMonoidHom u := by
    apply Units.ext
    show (genuineBaseChange F N).β ((genuineBaseChange E F).β (u : AdeleRing (𝓞 E) E)) = (genuineBaseChange E N).β u
    rw [genuineBaseChange_β, genuineBaseChange_β, genuineBaseChange_β, ← RingHom.comp_apply,
      M4aHerbrand.Bridge.genuineBeta_comp_of_tower E F N]
  have hβα : Units.map (genuineBaseChange F N).β.toMonoidHom
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) α) ∈ principalIdeles (𝓞 N) N :=
    ⟨Units.map (algebraMap F N : F →* N) α, Units.ext ((genuineBaseChange F N).β_compat (α : F)).symm⟩
  have hEN : (QuotientGroup.mk (Units.map (genuineBaseChange E N).β.toMonoidHom u) : IdeleClassGroup (𝓞 N) N)
      = QuotientGroup.mk (∏ σ : N ≃ₐ[F] N, DF.unitsAct σ v) := by
    rw [← htower, ← hqv, map_mul, hprodF v, QuotientGroup.eq, mul_inv_rev, mul_comm, ← mul_assoc,
      mul_inv_cancel, one_mul]
    exact Subgroup.inv_mem _ hβα

  have hfinT : IsOfFinOrder t := isOfFinOrder_of_finite t
  have hreidx : ∏ σ : N ≃ₐ[F] N, DF.unitsAct σ v
      = ∏ i ∈ Finset.range (orderOf t), D.unitsAct ((t : N ≃ₐ[E] N) ^ i) v := by
    rw [Fintype.prod_equiv eS (fun σ => DF.unitsAct σ v) (fun g : S => D.unitsAct (g : N ≃ₐ[E] N) v)
      (fun σ => hDF σ v)]

    let e : Fin (orderOf t) ≃ S := (finEquivZPowers hfinT).trans (Equiv.subtypeUnivEquiv ht)
    have he : ∀ i : Fin (orderOf t), ((e i : S) : N ≃ₐ[E] N) = (t : N ≃ₐ[E] N) ^ (i : ℕ) := fun i => by
      simp [e, finEquivZPowers_apply]
    rw [← Fin.prod_univ_eq_prod_range (fun i => D.unitsAct ((t : N ≃ₐ[E] N) ^ i) v) (orderOf t),
      ← Equiv.prod_comp e (fun g : S => D.unitsAct (g : N ≃ₐ[E] N) v)]
    simp_rw [he]

  refine ⟨Additive.ofMul (QuotientGroup.mk v), ?_⟩
  have hsum : ∀ tt : Finset ℕ,
      (∑ i ∈ tt, A.ρ ((t : N ≃ₐ[E] N) ^ i) (Additive.ofMul (QuotientGroup.mk v : IdeleClassGroup (𝓞 N) N)))
      = Additive.ofMul (QuotientGroup.mk (∏ i ∈ tt, D.unitsAct ((t : N ≃ₐ[E] N) ^ i) v)) := by
    intro tt
    induction tt using Finset.induction_on with
    | empty => rfl
    | insert i tt hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, ih, hρ, QuotientGroup.mk_mul]
      rfl
  show (∑ i ∈ Finset.range (orderOf t), A.ρ ((t : N ≃ₐ[E] N) ^ i) (Additive.ofMul (QuotientGroup.mk v))) = a₀
  rw [hsum, ← hreidx, ← hEN, ← ha₀u]

end S_NumberField_IdeleClassGroup_exists_sum_rho_pow_eq_of_forall_rho_eq
end P2MW
export P2MW.S_NumberField_IdeleClassGroup_exists_sum_rho_pow_eq_of_forall_rho_eq (solution)
