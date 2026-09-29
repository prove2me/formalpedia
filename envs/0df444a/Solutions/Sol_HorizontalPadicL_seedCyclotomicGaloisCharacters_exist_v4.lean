-- Prove2me | solution 1 for HorizontalPadicL.seedCyclotomicGaloisCharacters_exist_v4
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T11:47:28.113531+00:00
-- url     : https://prove2.me/submissions/c6074e07-d461-42d1-97d8-59b1053d5598

import Definitions.Def_KN_SeedCyclotomicGaloisCharactersV3B
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

private def seedCyclotomicFieldV2 (n : ℕ) : IntermediateField ℚ MTT.Qbar :=
  IntermediateField.adjoin ℚ
    {x : MTT.Qbar | ∃ d ∈ ({n} : Set ℕ), d ≠ 0 ∧ x ^ d = 1}

private instance (n : ℕ) [NeZero n] :
    IsCyclotomicExtension {n} ℚ (seedCyclotomicFieldV2 n) := by
  apply IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
  intro d hd hd0
  rw [Set.mem_singleton_iff] at hd
  subst d
  exact HasEnoughRootsOfUnity.exists_primitiveRoot MTT.Qbar n

private instance (n : ℕ) [NeZero n] : NumberField (seedCyclotomicFieldV2 n) :=
  IsCyclotomicExtension.numberField {n} ℚ _

private instance (n : ℕ) [NeZero n] : IsGalois ℚ (seedCyclotomicFieldV2 n) :=
  IsCyclotomicExtension.isGalois {n} ℚ _

private theorem exists_value_orderOf_eq_v2 (n : ℕ)
    (chi : DirichletCharacter MTT.Qbar n) :
    ∃ a : (ZMod n)ˣ, orderOf (chi.toUnitHom a) = orderOf chi := by
  let f : (ZMod n)ˣ →* MTT.Qbarˣ := chi.toUnitHom
  let R : Subgroup MTT.Qbarˣ := f.range
  letI : Finite R := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨g, hgen⟩ := IsCyclic.exists_generator (α := R)
  obtain ⟨a, ha⟩ := g.property
  use a
  have hcoe : orderOf (fun b ↦ f b) = orderOf f :=
    orderOf_injective (MonoidHom.coeFn _ _) DFunLike.coe_injective f
  have hdiv₁ : orderOf (f a) ∣ orderOf f := by
    rw [← hcoe]
    exact orderOf_apply_dvd_orderOf (x := fun b ↦ f b) a
  have hdiv₂ : orderOf f ∣ orderOf (f a) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    ext b
    let xb : R := ⟨f b, ⟨b, rfl⟩⟩
    have hbmem : xb ∈ Subgroup.zpowers g := hgen _
    have hbdiv : orderOf (f b) ∣ orderOf (f a) := by
      calc
        orderOf (f b) = orderOf xb := by
          change orderOf (R.subtype xb) = orderOf xb
          exact orderOf_injective R.subtype Subtype.coe_injective xb
        _ ∣ orderOf g := orderOf_dvd_of_mem_zpowers hbmem
        _ = orderOf (f a) := (orderOf_injective R.subtype Subtype.coe_injective g).symm.trans
          (congrArg orderOf ha.symm)
    exact congrArg Units.val (orderOf_dvd_iff_pow_eq_one.mp hbdiv)
  have hfa : orderOf (f a) = orderOf f := Nat.dvd_antisymm hdiv₁ hdiv₂
  rw [hfa]
  exact MulChar.mulEquivToUnitHom.orderOf_eq chi

theorem _root_.solution
    {N p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive) (m : ℕ) (hm : 0 < m)
    (hηorder : 2 ≤ orderOf η.2)
    (horderCoprime : Nat.Coprime (orderOf η.2) p)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor) :
    Nonempty (SeedCyclotomicGaloisCharacterDataV2 N p m η) := by
  let n := η.1.1
  let q := p ^ m * N
  let t := n * q
  have hq : 0 < q := mul_pos (pow_pos ((Fact.out : p.Prime).pos) _) hN
  have ht : 0 < t := mul_pos η.1.2 hq
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  letI : NeZero t := ⟨Nat.ne_of_gt ht⟩
  let L := seedCyclotomicFieldV2 t
  let gal : (L ≃ₐ[ℚ] L) ≃* (ZMod t)ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod t L
  have hn_dvd : n ∣ t := dvd_mul_right n q
  have hq_dvd : q ∣ t := dvd_mul_left q n
  let toSeed : (ZMod t)ˣ →* (ZMod n)ˣ := ZMod.unitsMap hn_dvd
  let toCyclo : (ZMod t)ˣ →* (ZMod q)ˣ := ZMod.unitsMap hq_dvd
  let seed : (L ≃ₐ[ℚ] L) →* MTT.Qbarˣ :=
    η.2.toUnitHom.comp (toSeed.comp gal.toMonoidHom)
  let cyclo : (L ≃ₐ[ℚ] L) →* (ZMod q)ˣ :=
    toCyclo.comp gal.toMonoidHom
  let zeta := IsCyclotomicExtension.zeta t ℚ L
  let root : L := zeta ^ n
  have hroot : IsPrimitiveRoot root q := by
    exact IsPrimitiveRoot.pow ht (IsCyclotomicExtension.zeta_spec t ℚ L) rfl
  obtain ⟨a, ha⟩ := exists_value_orderOf_eq_v2 n η.2
  obtain ⟨c, hc⟩ := ZMod.unitsMap_surjective hn_dvd a
  let sigma : L ≃ₐ[ℚ] L := gal.symm c
  refine ⟨{
    L := L
    cyclotomicRoot := root
    cyclotomicRoot_primitive := hroot
    cyclotomicCharacter := cyclo
    cyclotomicCharacter_spec := ?_
    seedCharacter := seed
    seed_values_realized := ?_
    only_seed_values := ?_
    seedGenerator := sigma
    seedGenerator_order := ?_ }⟩
  · intro tau
    have hroot_t : root ^ t = 1 := (hroot.pow_eq_one_iff_dvd t).2 hq_dvd
    have hact := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      t L tau hroot_t
    rw [hact]
    apply pow_eq_pow_of_modEq
    rw [← ZMod.natCast_eq_natCast_iff]
    change ((gal tau).val.val : ZMod q) =
      (((toCyclo (gal tau) : ZMod q).val : ℕ) : ZMod q)
    calc
      ((gal tau).val.val : ZMod q) = ((gal tau : ZMod t).cast : ZMod q) := by
        rw [ZMod.cast_eq_val]
      _ = (toCyclo (gal tau) : ZMod q) := (ZMod.unitsMap_val hq_dvd (gal tau)).symm
      _ = ((toCyclo (gal tau) : ZMod q).val : ZMod q) := (ZMod.natCast_zmod_val _).symm
    exact hroot.pow_eq_one
  · intro b
    obtain ⟨d, hd⟩ := ZMod.unitsMap_surjective hn_dvd b
    refine ⟨gal.symm d, ?_⟩
    change ↑(η.2.toUnitHom (toSeed (gal (gal.symm d)))) = η.2 ↑b
    rw [gal.apply_symm_apply, hd]
    exact η.2.coe_toUnitHom b
  · intro tau
    refine ⟨toSeed (gal tau), ?_⟩
    exact η.2.coe_toUnitHom (toSeed (gal tau))
  · change orderOf (η.2.toUnitHom (toSeed (gal (gal.symm c)))) = orderOf η.2
    rw [gal.apply_symm_apply, hc]
    exact ha

end HorizontalPadicL
