-- Prove2me | solution 1 for NumberField.sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d70c2202-f789-5d1d-b047-c9707b8d8dc8

import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.RingTheory.Frobenius
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.NumberField.Basic
import Theorems.Thm_NumberField_exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt.NumberField LanglandsTunnell.RankinSelberg MulAction"
open scoped Pointwise Classical

namespace NumberField
p2m_export "NumberField" "mk RingOfIntegers RingOfIntegers.mapAlgEquiv exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt"
namespace FrobeniusSign
p2m_open "NumberField"

section A_helpers

variable {X : Type*} [Fintype X] [DecidableEq X] (τ : Equiv.Perm X)

omit [Fintype X] [DecidableEq X] in
theorem orbitRel_zpowers_iff {x y : X} :
    orbitRel (Subgroup.zpowers τ) X x y ↔ τ.SameCycle y x := by
  rw [orbitRel_apply, mem_orbit_iff, Subtype.exists]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨τ ^ k, Subgroup.zpow_mem_zpowers τ k, hk⟩

noncomputable def classMap (x : X) :
    Function.fixedPoints τ ⊕ {c // c ∈ τ.cycleFactorsFinset} :=
  if h : τ x = x then Sum.inl ⟨x, h⟩
  else Sum.inr ⟨τ.cycleOf x, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr h)⟩

theorem classMap_congr {x y : X} (h : τ.SameCycle x y) : classMap τ x = classMap τ y := by
  unfold classMap
  by_cases hx : τ x = x
  · have hy : τ y = y := h.apply_eq_self_iff.mp hx
    have : x = y := h.eq_of_left hx
    subst this
    rfl
  · have hy : ¬ τ y = y := fun hy => hx (h.apply_eq_self_iff.mpr hy)
    rw [dif_neg hx, dif_neg hy]
    congr 2
    exact h.cycleOf_eq

noncomputable def classLift :
    orbitRel.Quotient (Subgroup.zpowers τ) X → Function.fixedPoints τ ⊕ {c // c ∈ τ.cycleFactorsFinset} :=
  Quotient.lift (classMap τ) (fun _ _ hxy => (classMap_congr τ ((orbitRel_zpowers_iff τ).mp hxy)).symm)

theorem classLift_bijective : Function.Bijective (classLift τ) := by
  constructor
  · intro a b
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    intro hxy
    change classMap τ x = classMap τ y at hxy
    apply Quotient.sound
    change orbitRel (Subgroup.zpowers τ) X x y
    rw [orbitRel_zpowers_iff]
    unfold classMap at hxy
    by_cases hx : τ x = x
    · by_cases hy : τ y = y
      · rw [dif_pos hx, dif_pos hy] at hxy
        have : x = y := congrArg Subtype.val (Sum.inl_injective hxy)
        subst this; exact Equiv.Perm.SameCycle.refl _ _
      · rw [dif_pos hx, dif_neg hy] at hxy; exact absurd hxy Sum.inl_ne_inr
    · by_cases hy : τ y = y
      · rw [dif_neg hx, dif_pos hy] at hxy; exact absurd hxy Sum.inr_ne_inl
      · rw [dif_neg hx, dif_neg hy] at hxy
        have hc : τ.cycleOf x = τ.cycleOf y := congrArg Subtype.val (Sum.inr_injective hxy)
        have : x ∈ (τ.cycleOf y).support := by
          rw [← hc, Equiv.Perm.mem_support_cycleOf_iff]
          exact ⟨Equiv.Perm.SameCycle.refl _ _, Equiv.Perm.mem_support.mpr hx⟩
        exact (Equiv.Perm.mem_support_cycleOf_iff.mp this).1
  · rintro (⟨x, hx⟩ | ⟨c, hc⟩)
    · refine ⟨Quotient.mk _ x, ?_⟩
      change classMap τ x = _
      unfold classMap
      rw [dif_pos (show τ x = x from hx)]
    · obtain ⟨a, ha⟩ := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1.nonempty_support
      refine ⟨Quotient.mk _ a, ?_⟩
      change classMap τ a = _
      have hτa : τ a ≠ a := Equiv.Perm.mem_support.mp (Equiv.Perm.mem_cycleFactorsFinset_support_le hc ha)
      unfold classMap
      rw [dif_neg hτa]
      congr 1
      exact Subtype.ext (Equiv.Perm.cycle_is_cycleOf ha hc).symm

end A_helpers

theorem card_orbitRel_quotient_zpowers_eq {X : Type*} [Fintype X] [DecidableEq X] (τ : Equiv.Perm X) :
    Nat.card (orbitRel.Quotient (Subgroup.zpowers τ) X) =
      Multiset.card τ.cycleType + Fintype.card (Function.fixedPoints τ) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (classLift_bijective τ)), Nat.card_sum, add_comm,
    Nat.card_eq_fintype_card (α := Function.fixedPoints τ), Nat.card_eq_fintype_card, Fintype.card_coe,
    Equiv.Perm.cycleType_def, Multiset.card_map, Finset.card_def]

theorem sign_eq_neg_one_pow_card_add_card_orbits {X : Type*} [Fintype X] [DecidableEq X] (τ : Equiv.Perm X) :
    ((Equiv.Perm.sign τ : ℤˣ) : ℤ) = (-1) ^ (Fintype.card X + Nat.card (orbitRel.Quotient (Subgroup.zpowers τ) X)) := by
  rw [Equiv.Perm.sign_of_cycleType, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    card_orbitRel_quotient_zpowers_eq, Equiv.Perm.card_fixedPoints]
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le τ.sum_cycleType_le
  rw [hd, Nat.add_sub_cancel_left,
    show τ.cycleType.sum + d + (Multiset.card τ.cycleType + d)
      = (τ.cycleType.sum + Multiset.card τ.cycleType) + 2 * d by ring,
    pow_add _ (_ + _) (2 * d), pow_mul, neg_one_sq, one_pow, mul_one]

theorem card_orbits_toPerm_eq {Γ : Type*} [Group Γ] {X : Type*} [MulAction Γ X] (g : Γ) :
    Nat.card (orbitRel.Quotient (Subgroup.zpowers (MulAction.toPerm g : Equiv.Perm X)) X) =
      Nat.card (orbitRel.Quotient (Subgroup.zpowers g) X) := by
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl X) fun a b => ?_
  change a ∈ orbit (Subgroup.zpowers (MulAction.toPerm g : Equiv.Perm X)) b ↔ a ∈ orbit (Subgroup.zpowers g) b
  constructor
  · rintro ⟨⟨τ, hτ⟩, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    refine ⟨⟨g ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩⟩, ?_⟩
    change g ^ n • b = ((MulAction.toPerm g : Equiv.Perm X) ^ n) b
    rw [← MulAction.toPermHom_apply, ← map_zpow, MulAction.toPermHom_apply, MulAction.toPerm_apply]
  · rintro ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine ⟨⟨(MulAction.toPerm g : Equiv.Perm X) ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩⟩, ?_⟩
    change ((MulAction.toPerm g : Equiv.Perm X) ^ n) b = g ^ n • b
    rw [← MulAction.toPermHom_apply, ← map_zpow, MulAction.toPermHom_apply, MulAction.toPerm_apply]

section B

variable (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
  (K : Type) [Field K] [NumberField K] [Algebra E K] [Algebra K L] [IsScalarTower E K L]

abbrev Kim : IntermediateField E L := (IsScalarTower.toAlgHom E K L).fieldRange

theorem card_quotient_fixingSubgroup_eq_finrank :
    Nat.card ((L ≃ₐ[E] L) ⧸ (Kim E L K).fixingSubgroup) = Module.finrank E K := by
  rw [← Subgroup.index, ← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom E K L)).toLinearEquiv.finrank_eq).symm

def hosCongr {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    (φ : A ≃+* B) : HeightOneSpectrum A ≃ HeightOneSpectrum B where
  toFun v := ⟨v.asIdeal.comap (φ.symm : B →+* A), Ideal.IsPrime.comap _, fun h => v.ne_bot (by
    rw [← Ideal.comap_of_equiv (I := v.asIdeal) φ, h]
    exact Ideal.comap_bot_of_injective _ φ.injective)⟩
  invFun w := ⟨w.asIdeal.comap (φ : A →+* B), Ideal.IsPrime.comap _, fun h => w.ne_bot (by
    have := Ideal.comap_of_equiv (I := w.asIdeal) φ.symm
    rw [RingEquiv.symm_symm] at this
    rw [← this, h]
    exact Ideal.comap_bot_of_injective _ φ.symm.injective)⟩
  left_inv v := by ext1; exact Ideal.comap_of_equiv (I := v.asIdeal) φ
  right_inv w := by
    ext1
    have := Ideal.comap_of_equiv (I := w.asIdeal) φ.symm
    rw [RingEquiv.symm_symm] at this
    exact this

theorem hosCongr_under {R A B : Type*} [CommRing R] [IsDedekindDomain R] [CommRing A]
    [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B] [Algebra R A] [Algebra R B]
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
    (ψ : A ≃ₐ[R] B) (w : HeightOneSpectrum A) :
    (hosCongr (ψ : A ≃+* B) w).under R = w.under R := by
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
  show ((ψ : A ≃+* B).symm : B →+* A) (algebraMap R B x) ∈ w.asIdeal ↔ _
  have : ((ψ : A ≃+* B).symm : B →+* A) (algebraMap R B x) = algebraMap R A x := by simp
  rw [this]

theorem card_primeFibre_eq (v : HeightOneSpectrum (𝓞 E)) :
    Nat.card (primeFibre E K v) = Nat.card (primeFibre E (Kim E L K) v) := by

  let e' : K ≃ₐ[E] Kim E L K := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom E K L)
  let ψ : 𝓞 K ≃ₐ[𝓞 E] 𝓞 (Kim E L K) := RingOfIntegers.mapAlgEquiv e'
  refine Nat.card_congr ((hosCongr (ψ : 𝓞 K ≃+* 𝓞 (Kim E L K))).subtypeEquiv fun P => ?_)
  simp only [mem_primeFibre, hosCongr_under]

end B

end NumberField.FrobeniusSign

open IsDedekindDomain _root_.NumberField _root_.P2MW.S_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt.NumberField LanglandsTunnell.RankinSelberg MulAction NumberField.FrobeniusSign in
open scoped Classical in

theorem solution
    (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    (K : Type) [Field K] [NumberField K] [Algebra E K] [Algebra K L] [IsScalarTower E K L]
    (v : HeightOneSpectrum (𝓞 E)) (hv : Ideal.ramificationIdxIn v.asIdeal (𝓞 L) = 1)
    (Q : HeightOneSpectrum (𝓞 L)) (hQ : Q.under (𝓞 E) = v)
    (σ : L ≃ₐ[E] L) (hσ : IsArithFrobAt (𝓞 E) σ Q.asIdeal) :
    ((Equiv.Perm.sign (MulAction.toPerm σ :
        Equiv.Perm ((L ≃ₐ[E] L) ⧸ (IsScalarTower.toAlgHom E K L).fieldRange.fixingSubgroup)) : ℤˣ) : ℤ) =
      (-1) ^ (Module.finrank E K + Nat.card (primeFibre E K v)) := by
  rw [sign_eq_neg_one_pow_card_add_card_orbits, card_orbits_toPerm_eq, ← Nat.card_eq_fintype_card,
    card_quotient_fixingSubgroup_eq_finrank E L K, card_primeFibre_eq E L K v]
  obtain ⟨e, -⟩ :=
    NumberField.exists_equiv_orbitRel_zpowers_quotient_fixingSubgroup_primeFibre_of_isArithFrobAt E L (Kim E L K)
      v hv Q hQ σ hσ
  congr 2
  exact Nat.card_congr e

end S_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt
end P2MW
export P2MW.S_NumberField_sign_toPerm_quotient_fixingSubgroup_fieldRange_eq_neg_one_pow_of_isArithFrobAt (solution)
