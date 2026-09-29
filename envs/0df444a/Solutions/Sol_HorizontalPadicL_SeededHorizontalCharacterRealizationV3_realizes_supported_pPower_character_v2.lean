-- Prove2me | solution 1 for HorizontalPadicL.SeededHorizontalCharacterRealizationV3.realizes_supported_pPower_character_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:55:18.925981+00:00
-- url     : https://prove2.me/submissions/d482bb76-bf57-48b6-b431-878a5a804de4

import Definitions.Def_KN_InverseSeedConventionV2
import Definitions.Def_KN_SeededHorizontalCharacterRealizationV2B
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Group.Pi.Units

set_option autoImplicit false
noncomputable section
open scoped BigOperators

private theorem card_ker_mul_card_of_surjective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (q : G →* H) (hq : Function.Surjective q) :
    Nat.card q.ker * Nat.card H = Nat.card G := by
  rw [← Subgroup.card_mul_index q.ker, Subgroup.index_ker]
  congr 1
  rw [MonoidHom.range_eq_top.mpr hq]
  simp

private theorem local_kernel_coprime
    {p ℓ : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime)
    (q : (ZMod ℓ)ˣ →* Multiplicative (ZMod (p ^ padicValNat p (ℓ - 1))))
    (hq : Function.Surjective q) :
    Nat.Coprime p (Nat.card q.ker) := by
  rw [(Fact.out : p.Prime).coprime_iff_not_dvd]
  intro hpker
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hcardG : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hℓ]
  have hcardH : Nat.card (Multiplicative
      (ZMod (p ^ padicValNat p (ℓ - 1)))) =
      p ^ padicValNat p (ℓ - 1) := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hmul : Nat.card q.ker * p ^ padicValNat p (ℓ - 1) = ℓ - 1 := by
    calc
      Nat.card q.ker * p ^ padicValNat p (ℓ - 1) =
          Nat.card q.ker * Nat.card (Multiplicative
            (ZMod (p ^ padicValNat p (ℓ - 1)))) := by rw [hcardH]
      _ = Nat.card (ZMod ℓ)ˣ := card_ker_mul_card_of_surjective q hq
      _ = ℓ - 1 := hcardG
  have hd : p ^ (padicValNat p (ℓ - 1) + 1) ∣
      Nat.card q.ker * p ^ padicValNat p (ℓ - 1) := by
    convert Nat.mul_dvd_mul hpker
      (dvd_refl (p ^ padicValNat p (ℓ - 1))) using 1
    rw [pow_succ', Nat.mul_comm]
  have hd' : p ^ (padicValNat p (ℓ - 1) + 1) ∣ ℓ - 1 := by
    rwa [hmul] at hd
  exact (pow_succ_padicValNat_not_dvd (p := p) (n := ℓ - 1)
    (Nat.ne_of_gt (Nat.sub_pos_of_lt hℓ.one_lt))) hd'

open HorizontalPadicL

private theorem orderOf_ofUnitHom
    {A K : Type*} [CommMonoid A] [CommGroupWithZero K]
    (f : Aˣ →* Kˣ) :
    orderOf (MulChar.ofUnitHom f) = orderOf f := by
  calc
    orderOf (MulChar.ofUnitHom f) =
        orderOf (MulChar.mulEquivToUnitHom (MulChar.ofUnitHom f)) :=
      (orderOf_injective MulChar.mulEquivToUnitHom.toMonoidHom
        MulChar.mulEquivToUnitHom.injective _).symm
    _ = orderOf f := by simp

private theorem dirichletCharacter_heq_of_int_apply_eq
    {R : Type*} [CommMonoidWithZero R] {m n : ℕ}
    (hmn : m = n) (f : DirichletCharacter R m)
    (g : DirichletCharacter R n)
    (hfg : ∀ z : ℤ, f z = g z) : f ≍ g := by
  subst n
  apply heq_of_eq
  apply MulChar.ext'
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  exact hfg z

private theorem supportProjection_surjective
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (P : SeededHorizontalProjectionSystemV3 L) (A : Finset ℕ) :
    Function.Surjective (P.supportProjection A) := by
  let I := {n : ℕ // n ∈ A}
  have hpair : Pairwise (Function.onFun Nat.Coprime (fun i : I ↦ L.primeAt i.1)) := by
    intro i j hij
    change Nat.Coprime (L.primeAt i.1) (L.primeAt j.1)
    rw [Nat.coprime_primes (L.primeAt_prime i) (L.primeAt_prime j)]
    intro h
    exact hij (Subtype.ext (L.primeAt_injective h))
  have hprod : (∏ i : I, L.primeAt i.1) = L.supportModulus A := by
    exact Finset.prod_attach A L.primeAt
  let eR : ZMod (L.supportModulus A) ≃+* (∀ i : I, ZMod (L.primeAt i.1)) :=
    (ZMod.ringEquivCongr hprod.symm).trans
      (ZMod.prodEquivPi (fun i : I ↦ L.primeAt i.1) hpair)
  let eU : (ZMod (L.supportModulus A))ˣ ≃* (∀ i : I, (ZMod (L.primeAt i.1))ˣ) :=
    (Units.mapEquiv eR.toMulEquiv).trans MulEquiv.piUnits
  intro y
  choose v hv using fun i : I ↦ P.localProjection_surjective i.1 (y i)
  obtain ⟨u, hu⟩ := eU.surjective v
  refine ⟨u, funext fun i ↦ ?_⟩
  change P.localProjection i.1 (ZMod.unitsMap _ u) = y i
  rw [← hv i]
  congr 1
  have hui := congr_fun hu i
  letI : NeZero (L.primeAt i.1) := ⟨(L.primeAt_prime i.1).ne_zero⟩
  apply Units.ext
  apply ZMod.val_injective
  have hd₁ : L.primeAt i.1 ∣ ∏ j : I, L.primeAt j.1 :=
    Finset.dvd_prod_of_mem (fun j : I ↦ L.primeAt j.1) (Finset.mem_univ i)
  have hd₂ : L.primeAt i.1 ∣ L.supportModulus A :=
    Finset.dvd_prod_of_mem L.primeAt i.2
  have he :
      (((ZMod.ringEquivCongr hprod.symm)
        (u : ZMod (L.supportModulus A))).cast : ZMod (L.primeAt i.1)) =
        ((u : ZMod (L.supportModulus A)).cast : ZMod (L.primeAt i.1)) := by
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (u : ZMod (L.supportModulus A))
    rw [← hz]
    simp only [ZMod.ringEquivCongr_intCast]
    calc
      ((z : ZMod (∏ j : I, L.primeAt j.1)).cast : ZMod (L.primeAt i.1)) =
          (z : ZMod (L.primeAt i.1)) := ZMod.cast_intCast hd₁ z
      _ = ((z : ZMod (L.supportModulus A)).cast : ZMod (L.primeAt i.1)) :=
        (ZMod.cast_intCast hd₂ z).symm
  have hui' := congr_arg Units.val hui
  change eR (u : ZMod (L.supportModulus A)) i =
    (v i : ZMod (L.primeAt i.1)) at hui'
  dsimp only [eR, RingEquiv.trans_apply] at hui'
  rw [ZMod.prodEquivPi_apply] at hui'
  change (((ZMod.ringEquivCongr hprod.symm)
    (u : ZMod (L.supportModulus A))).cast : ZMod (L.primeAt i.1)) = _ at hui'
  rw [he] at hui'
  change ((u : ZMod (L.supportModulus A)).cast : ZMod (L.primeAt i.1)).val =
    (v i : ZMod (L.primeAt i.1)).val
  exact congr_arg ZMod.val hui'

private theorem support_kernel_order_coprime
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (P : SeededHorizontalProjectionSystemV3 L) (A : Finset ℕ)
    (u : (ZMod (L.supportModulus A))ˣ)
    (hu : u ∈ (P.supportProjection A).ker) :
    Nat.Coprime p (orderOf u) := by
  let I := {n : ℕ // n ∈ A}
  have hpair : Pairwise (Function.onFun Nat.Coprime (fun i : I ↦ L.primeAt i.1)) := by
    intro i j hij
    change Nat.Coprime (L.primeAt i.1) (L.primeAt j.1)
    rw [Nat.coprime_primes (L.primeAt_prime i) (L.primeAt_prime j)]
    intro h
    exact hij (Subtype.ext (L.primeAt_injective h))
  have hprod : (∏ i : I, L.primeAt i.1) = L.supportModulus A := by
    exact Finset.prod_attach A L.primeAt
  let eR : ZMod (L.supportModulus A) ≃+* (∀ i : I, ZMod (L.primeAt i.1)) :=
    (ZMod.ringEquivCongr hprod.symm).trans
      (ZMod.prodEquivPi (fun i : I ↦ L.primeAt i.1) hpair)
  let eU : (ZMod (L.supportModulus A))ˣ ≃* (∀ i : I, (ZMod (L.primeAt i.1))ˣ) :=
    (Units.mapEquiv eR.toMulEquiv).trans MulEquiv.piUnits
  have heU : ∀ i : I,
      eU u i = ZMod.unitsMap
        (Finset.dvd_prod_of_mem L.primeAt i.2) u := by
    intro i
    letI : NeZero (L.primeAt i.1) := ⟨(L.primeAt_prime i.1).ne_zero⟩
    apply Units.ext
    apply ZMod.val_injective
    have hd₁ : L.primeAt i.1 ∣ ∏ j : I, L.primeAt j.1 :=
      Finset.dvd_prod_of_mem (fun j : I ↦ L.primeAt j.1) (Finset.mem_univ i)
    have hd₂ : L.primeAt i.1 ∣ L.supportModulus A :=
      Finset.dvd_prod_of_mem L.primeAt i.2
    have he :
        (((ZMod.ringEquivCongr hprod.symm)
          (u : ZMod (L.supportModulus A))).cast : ZMod (L.primeAt i.1)) =
          ((u : ZMod (L.supportModulus A)).cast : ZMod (L.primeAt i.1)) := by
      obtain ⟨z, hz⟩ := ZMod.intCast_surjective (u : ZMod (L.supportModulus A))
      rw [← hz]
      simp only [ZMod.ringEquivCongr_intCast]
      calc
        ((z : ZMod (∏ j : I, L.primeAt j.1)).cast : ZMod (L.primeAt i.1)) =
            (z : ZMod (L.primeAt i.1)) := ZMod.cast_intCast hd₁ z
        _ = ((z : ZMod (L.supportModulus A)).cast : ZMod (L.primeAt i.1)) :=
          (ZMod.cast_intCast hd₂ z).symm
    change (eR (u : ZMod (L.supportModulus A)) i).val =
      (((u : ZMod (L.supportModulus A)).cast : ZMod (L.primeAt i.1))).val
    dsimp only [eR, RingEquiv.trans_apply]
    rw [ZMod.prodEquivPi_apply]
    change ((((ZMod.ringEquivCongr hprod.symm)
      (u : ZMod (L.supportModulus A))).cast :
        ZMod (L.primeAt i.1))).val = _
    rw [he]
  let b : ℕ := ∏ i : I, Nat.card (P.localProjection i.1).ker
  have hb_coprime : Nat.Coprime p b := by
    exact (Nat.Coprime.prod_left (t := Finset.univ)
      (s := fun i : I ↦ Nat.card (P.localProjection i.1).ker)
      (x := p) (fun i _ ↦ (local_kernel_coprime
        (L.primeAt_prime i.1) (P.localProjection i.1)
        (P.localProjection_surjective i.1)).symm)).symm
  have hub : u ^ b = 1 := by
    apply eU.injective
    apply funext
    intro i
    rw [map_pow, map_one]
    apply (orderOf_dvd_iff_pow_eq_one).mp
    have hlocal : ZMod.unitsMap
        (Finset.dvd_prod_of_mem L.primeAt i.2) u ∈
        (P.localProjection i.1).ker := by
      change P.localProjection i.1
        (ZMod.unitsMap (Finset.dvd_prod_of_mem L.primeAt i.2) u) = 1
      have hui := congr_fun hu i
      exact hui
    have h₁ : orderOf (eU u i) ∣ Nat.card (P.localProjection i.1).ker := by
      rw [heU i]
      exact Subgroup.orderOf_dvd_natCard _ hlocal
    have h₂ : Nat.card (P.localProjection i.1).ker ∣ b := by
      exact Finset.dvd_prod_of_mem
        (fun j : I ↦ Nat.card (P.localProjection j.1).ker)
        (Finset.mem_univ i)
    exact h₁.trans h₂
  exact hb_coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hub)

theorem _root_.solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (ψ : DirichletCharacterWithLevel)
    (hprimitive : ψ.2.IsPrimitive)
    (horder : ∃ a : ℕ, orderOf ψ.2 = p ^ a)
    (hsupport : ∃ A : Finset ℕ,
      ψ.2.conductor ∣ L.supportModulus A) :
    ∃ χ : HorizontalCharacter p L.exponent,
      R.realized χ = ψ := by
  obtain ⟨a, ha⟩ := horder
  obtain ⟨A, hA⟩ := hsupport
  let M := L.supportModulus A
  letI : NeZero M := ⟨Nat.ne_of_gt (L.supportModulus_pos A)⟩
  have hc : ψ.2.conductor = ψ.1.1 :=
    (DirichletCharacter.isPrimitive_def ψ.2).mp hprimitive
  have hlevel : ψ.1.1 ∣ M := by
    rw [← hc]
    exact hA
  let ψM : DirichletCharacter MTT.Qbar M :=
    DirichletCharacter.changeLevel hlevel ψ.2
  let q := R.projections.supportProjection A
  have hq : Function.Surjective q :=
    supportProjection_surjective R.projections A
  let g : (ZMod M)ˣ →* ℂ_[p]ˣ :=
    (Units.map ιp.toMonoidHom).comp ψM.toUnitHom
  have hψMorder : orderOf ψM = p ^ a := by
    calc
      orderOf ψM = orderOf ψ.2 :=
        orderOf_injective (DirichletCharacter.changeLevel hlevel)
          (DirichletCharacter.changeLevel_injective hlevel) ψ.2
      _ = p ^ a := ha
  have hker : q.ker ≤ g.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    have hcop : Nat.Coprime (p ^ a) (orderOf u) :=
      (support_kernel_order_coprime R.projections A u hu).pow_left a
    apply (pow_eq_one_iff_of_coprime hcop).mp
    constructor
    · have hunitorder : orderOf ψM.toUnitHom = p ^ a := by
        rw [← orderOf_ofUnitHom ψM.toUnitHom]
        simpa using hψMorder
      have hpow : ψM.toUnitHom ^ (p ^ a) = 1 := by
        rw [← hunitorder]
        exact pow_orderOf_eq_one ψM.toUnitHom
      have hu' := DFunLike.congr_fun hpow u
      change (ψM.toUnitHom u) ^ (p ^ a) = 1 at hu'
      simpa [g, map_pow] using
        congr_arg (Units.map ιp.toMonoidHom) hu'
    · rw [← map_pow]
      simp
  let gu : HorizontalFiniteGroup p L.exponent A →* ℂ_[p]ˣ :=
    q.liftOfSurjective hq ⟨g, hker⟩
  let χ : HorizontalCharacter p L.exponent :=
    { support := A
      toMonoidHom := (Units.coeHom ℂ_[p]).comp gu }
  refine ⟨χ, ?_⟩
  have hat : R.atLevel χ = ψM := by
    apply MulChar.ext
    intro u
    apply ιp.injective
    rw [R.atLevel_compatibility]
    change ((gu (q u) : ℂ_[p]ˣ) : ℂ_[p]) = ιp (ψM (u : ZMod M))
    have hgu : gu (q u) = g u := by
      simpa [gu]
    rw [hgu]
    rfl
  unfold SeededHorizontalCharacterRealizationV3.realized
  dsimp only
  apply Sigma.ext
  · apply Subtype.ext
    calc
      (R.atLevel χ).conductor = ψM.conductor := congr_arg _ hat
      _ = ψ.2.conductor := ψ.2.conductor_changeLevel hlevel
      _ = ψ.1.1 := hc
  · have hprimHat : (R.atLevel χ).primitiveCharacter ≍
        ψM.primitiveCharacter :=
      congr_arg_heq (fun φ : DirichletCharacter MTT.Qbar M ↦
        φ.primitiveCharacter) hat
    have hcond : ψM.conductor = ψ.1.1 :=
      (ψ.2.conductor_changeLevel hlevel).trans hc
    have hprimPsi : ψM.primitiveCharacter ≍ ψ.2 :=
      dirichletCharacter_heq_of_int_apply_eq hcond _ _ fun z ↦ by
        calc
          ψM.primitiveCharacter z = ψ.2.primitiveCharacter z :=
            DirichletCharacter.primitiveCharacter_changeLevel_apply
              hlevel ψ.2 z
          _ = ψ.2 z := by
            by_cases hz : IsCoprime z ψ.1.1
            · exact ψ.2.primitiveCharacter_apply_of_isCoprime hz
            · rw [(ψ.2.primitiveCharacter.apply_eq_zero_iff z).2,
                (ψ.2.apply_eq_zero_iff z).2 hz]
              rwa [hc]
    exact hprimHat.trans hprimPsi
