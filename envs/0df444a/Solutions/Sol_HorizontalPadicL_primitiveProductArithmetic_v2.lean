-- Prove2me | solution 1 for HorizontalPadicL.primitiveProductArithmetic_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:11:48.510475+00:00
-- url     : https://prove2.me/submissions/dae0fa76-de30-4840-8d9d-36e066db7b1f

import Definitions.Def_KN_PrimePowerPropagationV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

private theorem conductor_primitive_mul_eq
    {n m : ℕ} [NeZero n] [NeZero m]
    (χ : DirichletCharacter MTT.Qbar n)
    (ψ : DirichletCharacter MTT.Qbar m)
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (hcop : Nat.Coprime n m) :
    (χ.mul ψ).conductor = n * m := by
  let L := Nat.lcm n m
  let χ' : DirichletCharacter MTT.Qbar L :=
    DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ
  let ψ' : DirichletCharacter MTT.Qbar L :=
    DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ
  let φ : DirichletCharacter MTT.Qbar L := χ' * ψ'
  have hL : L = n * m := hcop.lcm_eq_mul
  letI : NeZero L := ⟨hL ▸ Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne m)⟩
  have hχ' : χ'.conductor = n := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact hχ
  have hψ' : ψ'.conductor = m := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact hψ
  have hφ : φ = χ.mul ψ := rfl
  have hn : n ∣ φ.conductor := by
    have heq : χ' = φ * ψ'⁻¹ := by simp [φ]
    have hd := DirichletCharacter.conductor_mul_dvd_lcm_conductor φ ψ'⁻¹
    rw [← heq, DirichletCharacter.conductor_inv, hχ', hψ'] at hd
    apply hcop.dvd_of_dvd_mul_right
    exact hd.trans (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))
  have hm : m ∣ φ.conductor := by
    have heq : ψ' = φ * χ'⁻¹ := by simp [φ, mul_comm]
    have hd := DirichletCharacter.conductor_mul_dvd_lcm_conductor φ χ'⁻¹
    rw [← heq, DirichletCharacter.conductor_inv, hψ', hχ'] at hd
    apply hcop.symm.dvd_of_dvd_mul_right
    exact hd.trans (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _))
  have hlower : n * m ∣ φ.conductor := hcop.mul_dvd_of_dvd_of_dvd hn hm
  have hupper : φ.conductor ∣ n * m := by
    rw [← hL]
    exact DirichletCharacter.conductor_dvd_level φ
  rw [← hφ]
  exact Nat.dvd_antisymm hupper hlower

private theorem orderOf_primitive_mul
    {n m : ℕ} [NeZero n] [NeZero m]
    (χ : DirichletCharacter MTT.Qbar n)
    (ψ : DirichletCharacter MTT.Qbar m)
    (hcop : Nat.Coprime (orderOf χ) (orderOf ψ)) :
    orderOf (χ.mul ψ).primitiveCharacter = orderOf χ * orderOf ψ := by
  let L := Nat.lcm n m
  let χ' : DirichletCharacter MTT.Qbar L :=
    DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ
  let ψ' : DirichletCharacter MTT.Qbar L :=
    DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ
  let φ : DirichletCharacter MTT.Qbar L := χ' * ψ'
  letI : NeZero L := ⟨Nat.lcm_ne_zero (NeZero.ne n) (NeZero.ne m)⟩
  have hχ' : orderOf χ' = orderOf χ :=
    orderOf_injective
      (DirichletCharacter.changeLevel (R := MTT.Qbar) (Nat.dvd_lcm_left n m))
      (DirichletCharacter.changeLevel_injective (Nat.dvd_lcm_left n m)) χ
  have hψ' : orderOf ψ' = orderOf ψ :=
    orderOf_injective
      (DirichletCharacter.changeLevel (R := MTT.Qbar) (Nat.dvd_lcm_right n m))
      (DirichletCharacter.changeLevel_injective (Nat.dvd_lcm_right n m)) ψ
  have hφ : orderOf φ = orderOf χ * orderOf ψ := by
    rw [show φ = χ' * ψ' by rfl,
      (Commute.all χ' ψ').orderOf_mul_eq_mul_orderOf_of_coprime]
    · rw [hχ', hψ']
    · rwa [hχ', hψ']
  have hprim : orderOf (χ.mul ψ).primitiveCharacter = orderOf (χ.mul ψ) := by
    let c := (χ.mul ψ).conductor
    letI : NeZero c := ⟨DirichletCharacter.conductor_ne_zero (χ.mul ψ)⟩
    symm
    simpa only [DirichletCharacter.changeLevel_primitiveCharacter] using
      orderOf_injective
        (DirichletCharacter.changeLevel (R := MTT.Qbar)
          (χ.mul ψ).conductor_dvd_level)
        (DirichletCharacter.changeLevel_injective
          (χ.mul ψ).conductor_dvd_level)
        (χ.mul ψ).primitiveCharacter
  rw [hprim]
  exact hφ

private theorem changeLevel_apply_neg_one
    {n m : ℕ} [NeZero n] [NeZero m] (h : n ∣ m)
    (χ : DirichletCharacter MTT.Qbar n) :
    (DirichletCharacter.changeLevel h χ) (-1) = χ (-1) := by
  have hc := DirichletCharacter.changeLevel_eq_cast_of_dvd'
    χ h (a := (-1 : ℤ)) (IsCoprime.neg_left (isCoprime_one_left :
      IsCoprime (1 : ℤ) (m : ℤ)))
  norm_num at hc ⊢
  exact hc

private theorem primitive_mul_apply_neg_one
    {n m : ℕ} [NeZero n] [NeZero m]
    (χ : DirichletCharacter MTT.Qbar n)
    (ψ : DirichletCharacter MTT.Qbar m)
    (hχ : χ (-1) = 1) (hψ : ψ (-1) = 1) :
    (χ.mul ψ).primitiveCharacter (-1) = 1 := by
  let L := Nat.lcm n m
  let φ := χ.mul ψ
  letI : NeZero L := ⟨Nat.lcm_ne_zero (NeZero.ne n) (NeZero.ne m)⟩
  letI : NeZero φ.conductor := ⟨DirichletCharacter.conductor_ne_zero φ⟩
  rw [← changeLevel_apply_neg_one φ.conductor_dvd_level φ.primitiveCharacter]
  rw [DirichletCharacter.changeLevel_primitiveCharacter]
  change
    (DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ) (-1) *
      (DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ) (-1) = 1
  rw [changeLevel_apply_neg_one, changeLevel_apply_neg_one, hχ, hψ, one_mul]

theorem test_sigma_conductor
    (η ψ : DirichletCharacterWithLevel)
    (hη : η.2.IsPrimitive) (hψ : ψ.2.IsPrimitive)
    (hcop : Nat.Coprime η.2.conductor ψ.2.conductor) :
    (primitiveProductV2 η ψ).2.conductor = η.2.conductor * ψ.2.conductor := by
  rcases η with ⟨⟨n, hn⟩, χ⟩
  rcases ψ with ⟨⟨m, hm⟩, ξ⟩
  dsimp only at hη hψ hcop ⊢
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  change χ.conductor = n at hη
  change ξ.conductor = m at hψ
  have hcop' : Nat.Coprime n m := by simpa [hη, hψ] using hcop
  unfold primitiveProductV2
  dsimp only
  calc
    (χ.mul ξ).primitiveCharacter.conductor = (χ.mul ξ).conductor :=
      DirichletCharacter.primitiveCharacter_isPrimitive (χ.mul ξ)
    _ = n * m := conductor_primitive_mul_eq χ ξ hη hψ hcop'
    _ = χ.conductor * ξ.conductor := by rw [hη, hψ]

theorem test_sigma_primitive (η ψ : DirichletCharacterWithLevel) :
    (primitiveProductV2 η ψ).2.IsPrimitive := by
  rcases η with ⟨⟨n, hn⟩, χ⟩
  rcases ψ with ⟨⟨m, hm⟩, ξ⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  unfold primitiveProductV2
  dsimp only
  exact DirichletCharacter.primitiveCharacter_isPrimitive (χ.mul ξ)

theorem test_sigma_order
    (η ψ : DirichletCharacterWithLevel)
    (_hη : η.2.IsPrimitive) (_hψ : ψ.2.IsPrimitive)
    (_hcond : Nat.Coprime η.2.conductor ψ.2.conductor)
    (horder : Nat.Coprime (orderOf η.2) (orderOf ψ.2)) :
    orderOf (primitiveProductV2 η ψ).2 = orderOf η.2 * orderOf ψ.2 := by
  rcases η with ⟨⟨n, hn⟩, χ⟩
  rcases ψ with ⟨⟨m, hm⟩, ξ⟩
  dsimp only at horder ⊢
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  unfold primitiveProductV2
  dsimp only
  exact orderOf_primitive_mul χ ξ horder

theorem test_sigma_even
    (η ψ : DirichletCharacterWithLevel)
    (hη : η.2 (-1) = 1) (hψ : ψ.2 (-1) = 1) :
    (primitiveProductV2 η ψ).2 (-1) = 1 := by
  rcases η with ⟨⟨n, hn⟩, χ⟩
  rcases ψ with ⟨⟨m, hm⟩, ξ⟩
  dsimp only at hη hψ ⊢
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  unfold primitiveProductV2
  dsimp only
  exact primitive_mul_apply_neg_one χ ξ hη hψ

theorem test_sigma_injective
    (η : DirichletCharacterWithLevel) (hη : η.2.IsPrimitive) :
    Function.Injective (fun ψ : {ψ : DirichletCharacterWithLevel |
      ψ.2.IsPrimitive ∧ Nat.Coprime η.2.conductor ψ.2.conductor} =>
        primitiveProductV2 η ψ.val) := by
  rcases η with ⟨⟨n, hn⟩, χ⟩
  dsimp only at hη ⊢
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rintro ⟨⟨⟨m₁, hm₁⟩, ξ₁⟩, h₁prim, h₁cop⟩
    ⟨⟨⟨m₂, hm₂⟩, ξ₂⟩, h₂prim, h₂cop⟩ hout
  apply Subtype.ext
  letI : NeZero m₁ := ⟨Nat.ne_of_gt hm₁⟩
  letI : NeZero m₂ := ⟨Nat.ne_of_gt hm₂⟩
  have hcop₁ : Nat.Coprime n m₁ := by
    change χ.conductor = n at hη
    change ξ₁.conductor = m₁ at h₁prim
    rw [hη, h₁prim] at h₁cop
    exact h₁cop
  have hcop₂ : Nat.Coprime n m₂ := by
    change ξ₂.conductor = m₂ at h₂prim
    rw [hη, h₂prim] at h₂cop
    exact h₂cop
  have houtfst := congrArg (fun z : DirichletCharacterWithLevel => z.1.1) hout
  dsimp only [primitiveProductV2] at houtfst
  have hm : m₁ = m₂ := by
    apply Nat.eq_of_mul_eq_mul_left hn
    rw [← conductor_primitive_mul_eq χ ξ₁ hη h₁prim hcop₁,
      ← conductor_primitive_mul_eq χ ξ₂ hη h₂prim hcop₂]
    exact houtfst
  subst m₂
  have hhm : hm₂ = hm₁ := Subsingleton.elim _ _
  subst hm₂
  change (⟨⟨m₁, hm₁⟩, ξ₁⟩ : DirichletCharacterWithLevel) =
    ⟨⟨m₁, hm₁⟩, ξ₂⟩
  congr 1
  unfold primitiveProductV2 at hout
  dsimp only at hout
  have hdiv₁ : (χ.mul ξ₁).conductor ∣ n * m₁ := by
    rw [← hcop₁.lcm_eq_mul]
    exact DirichletCharacter.conductor_dvd_level (χ.mul ξ₁)
  have hdiv₂ : (χ.mul ξ₂).conductor ∣ n * m₁ := by
    rw [← hcop₂.lcm_eq_mul]
    exact DirichletCharacter.conductor_dvd_level (χ.mul ξ₂)
  let recover : DirichletCharacterWithLevel →
      DirichletCharacter MTT.Qbar (n * m₁) := fun z =>
    if h : z.1.1 ∣ n * m₁ then z.2.changeLevel h else 1
  have hrecovered := congrArg recover hout
  dsimp only [recover] at hrecovered
  rw [dif_pos hdiv₁, dif_pos hdiv₂] at hrecovered
  have hlcm : Nat.lcm n m₁ ∣ n * m₁ := by rw [hcop₁.lcm_eq_mul]
  have hleft : DirichletCharacter.changeLevel hdiv₁
      (χ.mul ξ₁).primitiveCharacter =
      DirichletCharacter.changeLevel hlcm (χ.mul ξ₁) := by
    have hx := congrArg (DirichletCharacter.changeLevel hlcm)
      (χ.mul ξ₁).changeLevel_primitiveCharacter
    simpa only [← DirichletCharacter.changeLevel_trans] using hx
  have hright : DirichletCharacter.changeLevel hdiv₂
      (χ.mul ξ₂).primitiveCharacter =
      DirichletCharacter.changeLevel hlcm (χ.mul ξ₂) := by
    have hx := congrArg (DirichletCharacter.changeLevel hlcm)
      (χ.mul ξ₂).changeLevel_primitiveCharacter
    simpa only [← DirichletCharacter.changeLevel_trans] using hx
  have hmul : DirichletCharacter.changeLevel hlcm (χ.mul ξ₁) =
      DirichletCharacter.changeLevel hlcm (χ.mul ξ₂) :=
    hleft.symm.trans (hrecovered.trans hright)
  simp only [DirichletCharacter.mul, map_mul,
    ← DirichletCharacter.changeLevel_trans] at hmul
  apply DirichletCharacter.changeLevel_injective (Nat.dvd_mul_left m₁ n)
  exact mul_left_cancel hmul

end HorizontalPadicL

open HorizontalPadicL

theorem solution : HorizontalPadicL.PrimitiveProductArithmetic := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact HorizontalPadicL.test_sigma_primitive
  · exact HorizontalPadicL.test_sigma_conductor
  · exact HorizontalPadicL.test_sigma_order
  · exact HorizontalPadicL.test_sigma_even
  · exact HorizontalPadicL.test_sigma_injective
