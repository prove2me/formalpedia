-- Prove2me | solution 1 for HorizontalPadicL.seededHorizontalCharacterRealization_exists_v4
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:58:20.664861+00:00
-- url     : https://prove2.me/submissions/32f35eae-ef66-45ea-97d9-eb4e9c25d8a5

import Definitions.Def_KN_InverseSeedConventionV2
import Theorems.Thm_HorizontalPadicL_SeededHorizontalCharacterRealizationV3_realizes_supported_pPower_character_v2
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Group.Pi.Units

set_option autoImplicit false
noncomputable section
open scoped BigOperators

open HorizontalPadicL

private theorem orderOf_eq_of_pow_eq_one_iff
    {G H : Type*} [Monoid G] [Monoid H] (x : G) (y : H)
    (h : ∀ n : ℕ, x ^ n = 1 ↔ y ^ n = 1) :
    orderOf x = orderOf y := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one]
    exact (h _).2 (pow_orderOf_eq_one y)
  · rw [orderOf_dvd_iff_pow_eq_one]
    exact (h _).1 (pow_orderOf_eq_one x)

private theorem orderOf_comp_of_surjective
    {G H K : Type*} [Monoid G] [Monoid H] [CommMonoid K]
    (f : H →* K) (q : G →* H) (hq : Function.Surjective q) :
    orderOf (f.comp q) = orderOf f := by
  apply orderOf_eq_of_pow_eq_one_iff
  intro n
  constructor
  · intro hn
    ext y
    obtain ⟨x, rfl⟩ := hq y
    simpa using DFunLike.congr_fun hn x
  · intro hn
    ext x
    simpa using DFunLike.congr_fun hn (q x)

/-- Lift a character of a finite group through the fixed embedding of the
algebraic closure. -/
private noncomputable def liftFiniteCharacter
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (ιp : MTT.Qbar →+* ℂ_[p]) (f : G →* ℂ_[p]) : G →* MTT.Qbarˣ := by
  let n := Nat.card G
  letI : NeZero n := ⟨Nat.card_pos.ne'⟩
  let fu : G →* ℂ_[p]ˣ := f.toHomUnits
  let fr : G →* rootsOfUnity n ℂ_[p] :=
    fu.codRestrict (rootsOfUnity n ℂ_[p]) fun g => by
      rw [mem_rootsOfUnity, ← map_pow]
      simpa [fu, n] using congr_arg f.toHomUnits (pow_card_eq_one' (x := g))
  let hζ : (primitiveRoots n MTT.Qbar).Nonempty := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot MTT.Qbar n
    exact ⟨ζ, (mem_primitiveRoots (NeZero.pos n)).2 hζ⟩
  let e : rootsOfUnity n MTT.Qbar ≃* rootsOfUnity n ℂ_[p] :=
    rootsOfUnityEquivOfPrimitiveRoots ιp.injective hζ
  exact (rootsOfUnity n MTT.Qbar).subtype.comp (e.symm.toMonoidHom.comp fr)

private theorem liftFiniteCharacter_spec
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (ιp : MTT.Qbar →+* ℂ_[p]) (f : G →* ℂ_[p]) (g : G) :
    ιp ((liftFiniteCharacter ιp f g : MTT.Qbarˣ) : MTT.Qbar) = f g := by
  simp [liftFiniteCharacter, rootsOfUnityEquivOfPrimitiveRoots_symm_apply]

private theorem orderOf_liftFiniteCharacter
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (ιp : MTT.Qbar →+* ℂ_[p]) (f : G →* ℂ_[p]) :
    orderOf (liftFiniteCharacter ιp f) = orderOf f := by
  apply orderOf_eq_of_pow_eq_one_iff
  intro n
  constructor
  · intro hn
    ext g
    have hg := DFunLike.congr_fun hn g
    have hg' := congr_arg (fun z : MTT.Qbarˣ => ιp (z : MTT.Qbar)) hg
    simpa [map_pow, liftFiniteCharacter_spec] using hg'
  · intro hn
    ext g
    apply ιp.injective
    have hg := DFunLike.congr_fun hn g
    simpa [map_pow, liftFiniteCharacter_spec] using hg

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

private noncomputable def localProjection
    {p ℓ : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime) :
    (ZMod ℓ)ˣ →* Multiplicative (ZMod (p ^ padicValNat p (ℓ - 1))) := by
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hc : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hℓ]
  let c : Multiplicative (ZMod (Nat.card (ZMod ℓ)ˣ)) →*
      Multiplicative (ZMod (ℓ - 1)) :=
    AddMonoidHom.toMultiplicative (ZMod.ringEquivCongr hc).toAddMonoidHom
  exact (AddMonoidHom.toMultiplicative
      (ZMod.castHom pow_padicValNat_dvd
        (ZMod (p ^ padicValNat p (ℓ - 1)))).toAddMonoidHom).comp
    (c.comp (zmodCyclicMulEquiv
      (ZMod.isCyclic_units_prime hℓ)).symm.toMonoidHom)

private theorem localProjection_surjective
    {p ℓ : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime) :
    Function.Surjective (localProjection (p := p) hℓ) := by
  letI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hc : Nat.card (ZMod ℓ)ˣ = ℓ - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hℓ]
  unfold localProjection
  dsimp only
  intro y
  obtain ⟨z, hz⟩ := ZMod.castHom_surjective pow_padicValNat_dvd
    (Multiplicative.toAdd y)
  obtain ⟨w, hw⟩ := (ZMod.ringEquivCongr hc).surjective z
  obtain ⟨x, hx⟩ := (zmodCyclicMulEquiv
    (ZMod.isCyclic_units_prime hℓ)).symm.surjective (Multiplicative.ofAdd w)
  refine ⟨x, ?_⟩
  simpa [hx, hw] using congr_arg Multiplicative.ofAdd hz

private theorem supportProjection_surjective
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (P : SeededHorizontalProjectionSystemV3 L) (A : Finset ℕ) :
    Function.Surjective (P.supportProjection A) := by
  let I := {n : ℕ // n ∈ A}
  have hpair : Pairwise (Function.onFun Nat.Coprime (fun i : I => L.primeAt i.1)) := by
    intro i j hij
    change Nat.Coprime (L.primeAt i.1) (L.primeAt j.1)
    rw [Nat.coprime_primes (L.primeAt_prime i) (L.primeAt_prime j)]
    intro h
    exact hij (Subtype.ext (L.primeAt_injective h))
  have hprod : (∏ i : I, L.primeAt i.1) = L.supportModulus A := by
    exact Finset.prod_attach A L.primeAt
  let eR : ZMod (L.supportModulus A) ≃+* (∀ i : I, ZMod (L.primeAt i.1)) :=
    (ZMod.ringEquivCongr hprod.symm).trans
      (ZMod.prodEquivPi (fun i : I => L.primeAt i.1) hpair)
  let eU : (ZMod (L.supportModulus A))ˣ ≃* (∀ i : I, (ZMod (L.primeAt i.1))ˣ) :=
    (Units.mapEquiv eR.toMulEquiv).trans MulEquiv.piUnits
  intro y
  choose v hv using fun i : I => P.localProjection_surjective i.1 (y i)
  obtain ⟨u, hu⟩ := eU.surjective v
  refine ⟨u, funext fun i => ?_⟩
  change P.localProjection i.1 (ZMod.unitsMap _ u) = y i
  rw [← hv i]
  congr 1
  have hui := congr_fun hu i
  letI : NeZero (L.primeAt i.1) := ⟨(L.primeAt_prime i.1).ne_zero⟩
  apply Units.ext
  apply ZMod.val_injective
  letI : NeZero (L.supportModulus A) :=
    ⟨Nat.ne_of_gt (L.supportModulus_pos A)⟩
  have hd₁ : L.primeAt i.1 ∣ ∏ j : I, L.primeAt j.1 :=
    Finset.dvd_prod_of_mem (fun j : I => L.primeAt j.1) (Finset.mem_univ i)
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

private theorem primitivePackage_levelOne_eq_trivial
    (ψ : DirichletCharacter MTT.Qbar 1) :
    (⟨⟨ψ.conductor, Nat.pos_of_ne_zero ψ.conductor_ne_zero⟩,
      ψ.primitiveCharacter⟩ : DirichletCharacterWithLevel) =
      trivialCharacterWithLevelV2 := by
  have hψ : ψ = 1 := DirichletCharacter.level_one ψ
  subst ψ
  have hc : DirichletCharacter.conductor
      (1 : DirichletCharacter MTT.Qbar 1) = 1 :=
    DirichletCharacter.conductor_one
  apply Sigma.ext
  · exact Subtype.ext hc
  · have hp : DirichletCharacter.primitiveCharacter
        (1 : DirichletCharacter MTT.Qbar 1) = 1 :=
      DirichletCharacter.primitiveCharacter_one
    have hOne :
        (1 : DirichletCharacter MTT.Qbar
          (DirichletCharacter.conductor (1 : DirichletCharacter MTT.Qbar 1))) ≍
          (1 : DirichletCharacter MTT.Qbar 1) := by
      have htype :
          DirichletCharacter MTT.Qbar
              (DirichletCharacter.conductor (1 : DirichletCharacter MTT.Qbar 1)) =
            DirichletCharacter MTT.Qbar 1 :=
        congr_arg (DirichletCharacter MTT.Qbar) hc
      have ht : htype ▸
          (1 : DirichletCharacter MTT.Qbar
            (DirichletCharacter.conductor (1 : DirichletCharacter MTT.Qbar 1))) = 1 :=
        DirichletCharacter.level_one _
      exact heq_of_eqRec_eq htype ht
    exact (heq_of_eq hp).trans hOne

theorem solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) :
    ∃ R : SeededHorizontalCharacterRealizationV3 L,
      R.HasExpectedProperties := by
  let P : SeededHorizontalProjectionSystemV3 L := {
    localProjection n := localProjection (p := p) (L.primeAt_prime n)
    localProjection_surjective n :=
      localProjection_surjective (p := p) (L.primeAt_prime n) }
  let R : SeededHorizontalCharacterRealizationV3 L := {
    projections := P
    atLevel χ := MulChar.ofUnitHom
      (liftFiniteCharacter ιp (χ.toMonoidHom.comp
        (P.supportProjection χ.support)))
    atLevel_compatibility χ u := by
      rw [MulChar.ofUnitHom_coe]
      exact liftFiniteCharacter_spec ιp _ u }
  refine ⟨R, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro χ
    let ψ := R.atLevel χ
    letI : NeZero (L.supportModulus χ.support) :=
      ⟨Nat.ne_of_gt (L.supportModulus_pos χ.support)⟩
    have hprimitive : orderOf ψ.primitiveCharacter = orderOf ψ := by
      let cl : DirichletCharacter MTT.Qbar ψ.conductor →*
          DirichletCharacter MTT.Qbar (L.supportModulus χ.support) :=
        DirichletCharacter.changeLevel
          (DirichletCharacter.conductor_dvd_level ψ)
      calc
        orderOf ψ.primitiveCharacter = orderOf (cl ψ.primitiveCharacter) :=
          (orderOf_injective cl
            (DirichletCharacter.changeLevel_injective _) _).symm
        _ = orderOf ψ := congr_arg orderOf
          (DirichletCharacter.changeLevel_primitiveCharacter ψ)
    have hfull : orderOf ψ = orderOf χ.toMonoidHom := by
      calc
        orderOf ψ = orderOf
            (liftFiniteCharacter ιp (χ.toMonoidHom.comp
              (P.supportProjection χ.support))) := by
          exact orderOf_ofUnitHom _
        _ = orderOf (χ.toMonoidHom.comp
              (P.supportProjection χ.support)) :=
          orderOf_liftFiniteCharacter ιp _
        _ = orderOf χ.toMonoidHom :=
          orderOf_comp_of_surjective _ _
            (supportProjection_surjective P χ.support)
    change orderOf ψ.primitiveCharacter = orderOf χ.toMonoidHom
    exact hprimitive.trans hfull
  · let χ₀ := trivialHorizontalCharacterV2 p L.exponent
    let ψ : DirichletCharacter MTT.Qbar 1 := R.atLevel χ₀
    change
      (⟨⟨ψ.conductor, Nat.pos_of_ne_zero ψ.conductor_ne_zero⟩,
        ψ.primitiveCharacter⟩ : DirichletCharacterWithLevel) =
        trivialCharacterWithLevelV2
    exact primitivePackage_levelOne_eq_trivial ψ
  · exact R.realizes_supported_pPower_character_v2
