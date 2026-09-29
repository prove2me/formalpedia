-- Prove2me | solution 1 for HorizontalPadicL.fullSupportCriticalZeroSet_descends_inverseSeed_v3
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T15:07:48.575978+00:00
-- url     : https://prove2.me/submissions/2580a673-6678-454f-8bf1-4d59d92069a4

import Theorems.Thm_HorizontalPadicL_horizontalFiniteGroup_isPGroup_v2
import Definitions.Def_KN_SeededThetaFullSupportInterpolationV3
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

private theorem realizes_on_support
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (ψ : DirichletCharacterWithLevel)
    (hprimitive : ψ.2.IsPrimitive)
    (horder : ∃ a : ℕ, orderOf ψ.2 = p ^ a)
    (A : Finset ℕ) (hA : ψ.2.conductor ∣ L.supportModulus A) :
    ∃ χ : HorizontalCharacter p L.exponent,
      χ.support = A ∧ R.realized χ = ψ := by
  obtain ⟨a, ha⟩ := horder
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
  refine ⟨χ, rfl, ?_⟩
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

private theorem divisor_prime_product (v : ℕ → ℕ) (hv : ∀ n, (v n).Prime)
    (A : Finset ℕ) (d : ℕ) (hd : d ∣ ∏ n ∈ A, v n) :
    ∃ C ⊆ A, d = ∏ n ∈ C, v n := by
  classical
  induction A using Finset.induction_on generalizing d with
  | empty =>
      have : d = 1 := Nat.eq_one_of_dvd_one (by simpa using hd)
      exact ⟨∅, Finset.Subset.refl _, by simpa⟩
  | @insert n A hn ih =>
      rw [Finset.prod_insert hn] at hd
      obtain ⟨d₁, d₂, hd₁, hd₂, heq⟩ := exists_dvd_and_dvd_of_dvd_mul hd
      obtain ⟨C, hCA, hC⟩ := ih d₂ hd₂
      rcases (Nat.dvd_prime (hv n)).mp hd₁ with h | h
      · refine ⟨C, hCA.trans (Finset.subset_insert n A), ?_⟩
        simpa [heq, h] using hC
      · refine ⟨insert n C, Finset.insert_subset_insert n hCA, ?_⟩
        rw [Finset.prod_insert (fun h => hn (hCA h)), ← hC, heq, h]

private theorem realized_lift
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel} {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (χ : HorizontalCharacter p L.exponent) :
    ∃ h : (R.realized χ).1.1 ∣ L.supportModulus χ.support,
      DirichletCharacter.changeLevel h (R.realized χ).2 = R.atLevel χ := by
  exact ⟨(R.atLevel χ).conductor_dvd_level,
    (R.atLevel χ).changeLevel_primitiveCharacter⟩

private theorem atLevel_of_same_realization
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel} {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (χ ψ : HorizontalCharacter p L.exponent)
    (h : L.supportModulus ψ.support ∣ L.supportModulus χ.support)
    (hr : R.realized ψ = R.realized χ) :
    DirichletCharacter.changeLevel h (R.atLevel ψ) = R.atLevel χ := by
  obtain ⟨hψ, eψ⟩ := realized_lift R ψ
  obtain ⟨hχ, eχ⟩ := realized_lift R χ
  have hψ' : ∃ h' : (R.realized χ).1.1 ∣ L.supportModulus ψ.support,
      DirichletCharacter.changeLevel h' (R.realized χ).2 = R.atLevel ψ := by
    rw [← hr]
    exact ⟨hψ, eψ⟩
  obtain ⟨hψ', eψ'⟩ := hψ'
  rw [← eψ', ← DirichletCharacter.changeLevel_trans, eχ]

private theorem supportProjection_restrict
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel} {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (P : SeededHorizontalProjectionSystemV3 L)
    {A C : Finset ℕ} (hCA : C ⊆ A)
    (h : L.supportModulus C ∣ L.supportModulus A)
    (u : (ZMod (L.supportModulus A))ˣ) :
    horizontalRestrictionHom hCA (P.supportProjection A u) =
      P.supportProjection C (ZMod.unitsMap h u) := by
  ext i
  change P.localProjection i.1 (ZMod.unitsMap _ u) =
    P.localProjection i.1 (ZMod.unitsMap _ (ZMod.unitsMap h u))
  congr 1
  exact (DFunLike.congr_fun (ZMod.unitsMap_comp
    (Finset.dvd_prod_of_mem L.primeAt i.2) h) u).symm

private theorem character_of_same_realization
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel} {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (χ ψ : HorizontalCharacter p L.exponent) (hsub : ψ.support ⊆ χ.support)
    (hr : R.realized ψ = R.realized χ) :
    χ.toMonoidHom = ψ.toMonoidHom.comp (horizontalRestrictionHom hsub) := by
  have hd : L.supportModulus ψ.support ∣ L.supportModulus χ.support :=
    Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hat := atLevel_of_same_realization R χ ψ hd hr
  apply MonoidHom.ext
  intro x
  obtain ⟨u, rfl⟩ := supportProjection_surjective R.projections χ.support x
  rw [← R.atLevel_compatibility χ u, ← hat]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  change ιp (R.atLevel ψ _) =
    ψ.toMonoidHom (horizontalRestrictionHom hsub (R.projections.supportProjection χ.support u))
  rw [supportProjection_restrict R.projections hsub hd]
  exact R.atLevel_compatibility ψ (ZMod.unitsMap hd u)

private theorem horizontalGroupAlgebraProjection_comp (R : Type*) [CommRing R]
    {p : ℕ} {m : ℕ → ℕ} {A B C : Finset ℕ}
    (hAB : A ⊆ B) (hBC : B ⊆ C)
    (x : HorizontalGroupAlgebra R p m C) :
    horizontalGroupAlgebraProjection R hAB
        (horizontalGroupAlgebraProjection R hBC x) =
      horizontalGroupAlgebraProjection R (hAB.trans hBC) x := by
  change MonoidAlgebra.mapDomainRingHom R (horizontalRestrictionHom hAB)
      (MonoidAlgebra.mapDomainRingHom R (horizontalRestrictionHom hBC) x) = _
  rw [← RingHom.comp_apply, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 2

private theorem horizontalGroupAlgebraProjection_refl (R : Type*) [CommRing R]
    {p : ℕ} {m : ℕ → ℕ} {A : Finset ℕ} (hAA : A ⊆ A)
    (x : HorizontalGroupAlgebra R p m A) :
    horizontalGroupAlgebraProjection R hAA x = x := by
  change MonoidAlgebra.mapDomainRingHom R (horizontalRestrictionHom hAA) x = x
  have hh : horizontalRestrictionHom hAA = MonoidHom.id (HorizontalFiniteGroup p m A) := by
    apply MonoidHom.ext
    intro g
    rfl
  rw [hh, MonoidAlgebra.mapDomainRingHom_id]
  rfl


private theorem theta_projection_unit_multiple
    {N k p B₀ : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B₀}
    (Θ : SeededFiniteThetaDataV3 L) (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors) (A B : Finset ℕ) (hAB : A ⊆ B) :
    ∃ u : (HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A)ˣ,
      horizontalGroupAlgebraProjection Θ.coefficientRing hAB (Θ.theta B) =
        (u : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) * Θ.theta A := by
  classical
  by_cases hEq : A = B
  · subst B
    refine ⟨1, ?_⟩
    rw [horizontalGroupAlgebraProjection_refl, Units.val_one, one_mul]
  · have hss : A ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hAB, hEq⟩
    obtain ⟨n, hnB, hnA⟩ := Finset.exists_of_ssubset hss
    let C := B.erase n
    have hAC : A ⊆ C := by
      intro a ha
      simp only [C, Finset.mem_erase]
      exact ⟨fun han => hnA (han ▸ ha), hAB ha⟩
    have hCB : C ⊆ B := Finset.erase_subset n B
    obtain ⟨u, hu⟩ := theta_projection_unit_multiple Θ hnorm hunit A C hAC
    let q : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent C →+*
        HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A :=
      horizontalGroupAlgebraProjection Θ.coefficientRing hAC
    let v : (HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A)ˣ :=
      Units.map q.toMonoidHom ((hunit C n).unit)
    refine ⟨v * u, ?_⟩
    calc
      horizontalGroupAlgebraProjection Θ.coefficientRing hAB (Θ.theta B) =
          horizontalGroupAlgebraProjection Θ.coefficientRing hAC
            (horizontalGroupAlgebraProjection Θ.coefficientRing hCB (Θ.theta B)) := by
              rw [horizontalGroupAlgebraProjection_comp]
      _ = horizontalGroupAlgebraProjection Θ.coefficientRing hAC
            (Θ.eulerFactor C n * Θ.theta C) := by
              congr 1
              have hrel := hnorm C n (by simp [C])
              have hins : insert n C = B := by simp [C, hnB]
              let q' : {D : Finset ℕ // C ⊆ D} →
                  HorizontalGroupAlgebra Θ.coefficientRing p L.exponent C :=
                fun D => horizontalGroupAlgebraProjection Θ.coefficientRing D.2 (Θ.theta D.1)
              have hz : (⟨B, hCB⟩ : {D : Finset ℕ // C ⊆ D}) =
                  ⟨insert n C, Finset.subset_insert n C⟩ := by
                apply Subtype.ext
                exact hins.symm
              exact (congrArg q' hz).trans hrel
      _ = q (Θ.eulerFactor C n) * q (Θ.theta C) := map_mul q _ _
      _ = (v : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) *
            ((u : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) * Θ.theta A) := by
              rw [hu]
              rfl
      _ = ((v * u : (HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A)ˣ) :
            HorizontalGroupAlgebra Θ.coefficientRing p L.exponent A) * Θ.theta A := by
              simp only [Units.val_mul]
              rw [mul_assoc]
termination_by (B \ A).card
decreasing_by
  have heq : B.erase n \ A = (B \ A).erase n := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    aesop
  rw [heq]
  exact Finset.card_erase_lt_of_mem (by simp [hnB, hnA])


private def horizontalCharacterEvalRingHom
    {p : ℕ} [Fact p.Prime] {m : ℕ → ℕ} (R : Subring ℂ_[p])
    (χ : HorizontalCharacter p m) :
    HorizontalGroupAlgebra R p m χ.support →+* ℂ_[p] :=
  ((MonoidAlgebra.lift R ℂ_[p] (HorizontalFiniteGroup p m χ.support)) χ.toMonoidHom).toRingHom

private theorem horizontalCharacterEvalRingHom_apply
    {p : ℕ} [Fact p.Prime] {m : ℕ → ℕ} (R : Subring ℂ_[p])
    (χ : HorizontalCharacter p m) (x : HorizontalGroupAlgebra R p m χ.support) :
    horizontalCharacterEvalRingHom R χ x =
      x.coeff.sum fun g a => (a : ℂ_[p]) * χ.toMonoidHom g := by
  unfold horizontalCharacterEvalRingHom
  change ((MonoidAlgebra.lift R ℂ_[p] (HorizontalFiniteGroup p m χ.support))
    χ.toMonoidHom) x = _
  rw [MonoidAlgebra.lift_apply]
  apply Finsupp.sum_congr
  intro g hg
  change (x.coeff g : ℂ_[p]) * χ.toMonoidHom g =
    (x.coeff g : ℂ_[p]) * χ.toMonoidHom g
  rfl


private theorem evaluation_projection
    {p : ℕ} [Fact p.Prime] {m : ℕ → ℕ} (R : Subring ℂ_[p])
    (χ ψ : HorizontalCharacter p m) (hsub : ψ.support ⊆ χ.support)
    (hχ : χ.toMonoidHom = ψ.toMonoidHom.comp (horizontalRestrictionHom hsub))
    (x : HorizontalGroupAlgebra R p m χ.support) :
    horizontalCharacterEvalRingHom R χ x =
      horizontalCharacterEvalRingHom R ψ (horizontalGroupAlgebraProjection R hsub x) := by
  have heq : horizontalCharacterEvalRingHom R χ =
      (horizontalCharacterEvalRingHom R ψ).comp (horizontalGroupAlgebraProjection R hsub) := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      simp [horizontalCharacterEvalRingHom, horizontalGroupAlgebraProjection]
    · intro g
      simp [horizontalCharacterEvalRingHom, horizontalGroupAlgebraProjection, hχ]
  exact DFunLike.congr_fun heq x

private theorem character_order_prime_power
    {p : ℕ} [Fact p.Prime] {m : ℕ → ℕ}
    (χ : HorizontalCharacter p m) :
    ∃ a : ℕ, orderOf χ.toMonoidHom = p ^ a := by
  have hpgroup := horizontalFiniteGroup_isPGroup_v2 (p := p) m χ.support
  obtain ⟨a, ha⟩ := (isPGroup_iff_exists_pow_pow_eq_one).mp hpgroup
  have hpow : χ.toMonoidHom ^ (p ^ a) = 1 := by
    apply MonoidHom.ext
    intro g
    change χ.toMonoidHom g ^ (p ^ a) = 1
    rw [← map_pow, ha g, map_one]
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
    (orderOf_dvd_of_pow_eq_one hpow)
  exact ⟨b, hb⟩

open HorizontalPadicL in
/-- Remove redundant character support using unit Euler transition factors. -/
private theorem descent_of_full_support
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L)
    (hcharacters : Θ.characters.HasExpectedProperties)
    (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors)
    (hfull : ∀ χ,
      (Θ.characters.realized χ).2.conductor = L.supportModulus χ.support →
      (Θ.eval χ ≠ 0 ↔
        let θ := primitiveProductV2 η (Θ.characters.realized χ)
        @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
          (k / 2 - 1) ≠ 0)) :
    Θ.HasSeededCriticalZeroSet := by
  classical
  intro χ
  let R := Θ.characters
  have hd := R.realized_conductor_dvd χ
  obtain ⟨C, hC, hcond⟩ := divisor_prime_product L.primeAt L.primeAt_prime
    χ.support (R.realized χ).2.conductor hd
  have horder : ∃ a, orderOf (R.realized χ).2 = p ^ a := by
    rw [hcharacters.1 χ]
    exact character_order_prime_power χ
  obtain ⟨ψ, hψsupport, hψ⟩ := realizes_on_support R (R.realized χ)
    (R.realized_primitive χ) horder C (by rw [hcond]; exact dvd_refl _)
  have hsub : ψ.support ⊆ χ.support := hψsupport ▸ hC
  have hfullψ : (R.realized ψ).2.conductor = L.supportModulus ψ.support := by
    rw [hψ, hψsupport]
    exact hcond
  have hpull := character_of_same_realization R χ ψ hsub hψ
  obtain ⟨u, hu⟩ := theta_projection_unit_multiple Θ hnorm hunit ψ.support χ.support hsub
  let ev := horizontalCharacterEvalRingHom Θ.coefficientRing ψ
  have heval : Θ.eval χ = ev (u : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent ψ.support) * Θ.eval ψ := by
    change (Θ.theta χ.support).coeff.sum _ = _
    rw [← horizontalCharacterEvalRingHom_apply]
    rw [evaluation_projection Θ.coefficientRing χ ψ hsub hpull, hu, map_mul]
    rw [horizontalCharacterEvalRingHom_apply Θ.coefficientRing ψ (Θ.theta ψ.support)]
    rfl
  have hune : ev (u : HorizontalGroupAlgebra Θ.coefficientRing p L.exponent ψ.support) ≠ 0 :=
    (u.isUnit.map ev).ne_zero
  have hnonzero : Θ.eval χ ≠ 0 ↔ Θ.eval ψ ≠ 0 := by
    rw [heval, mul_ne_zero_iff]
    exact and_iff_right hune
  rw [hnonzero, hfull ψ hfullψ]
  let critical : DirichletCharacterWithLevel → Prop := fun ξ =>
    let θ := primitiveProductV2 η ξ
    @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
      (k / 2 - 1) ≠ 0
  change critical (Θ.characters.realized ψ) ↔ critical (Θ.characters.realized χ)
  exact iff_of_eq (congrArg critical hψ)

/-- Descent from the correctly parenthesized full-support predicate. -/
theorem _root_.solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L)
    (hcharacters : Θ.characters.HasExpectedProperties)
    (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors)
    (hfull : Θ.HasFullSupportCriticalZeroSetV2) :
    Θ.HasSeededCriticalZeroSet := by
  exact descent_of_full_support Θ hcharacters hnorm hunit hfull
