-- Prove2me | solution 1 for IsLocalRing.exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4f80dc3c-f901-51ed-85c6-e7203129f341

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle

set_option autoImplicit false

namespace UextAux

private noncomputable def toCircle (n : ℕ) [NeZero n] : ZMod n →+ AddCircle (1 : ℚ) :=
  ZMod.lift n ⟨(QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
      ((AddMonoidHom.mulRight ((n : ℚ)⁻¹)).comp (Int.castAddHom ℚ)), by
    show ((((n : ℤ) : ℚ) * (n : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) = 0
    rw [Int.cast_natCast, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)),
      AddCircle.coe_eq_zero_iff]
    exact ⟨1, one_zsmul _⟩⟩

private theorem toCircle_intCast (n : ℕ) [NeZero n] (z : ℤ) :
    toCircle n (z : ZMod n) = (((z : ℚ) * (n : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) := by
  show ZMod.lift n _ (z : ZMod n) = _
  rw [ZMod.lift_coe]
  rfl

private theorem toCircle_injective (n : ℕ) [NeZero n] : Function.Injective (toCircle n) := by
  apply (ZMod.lift_injective n).mpr
  intro m hm
  change (((m : ℚ) * (n : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) = 0 at hm
  rw [AddCircle.coe_eq_zero_iff] at hm
  obtain ⟨k, hk⟩ := hm
  rw [zsmul_eq_mul, mul_one] at hk
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hmk : (m : ℚ) = n * k := by
    rw [hk, mul_comm (m : ℚ), ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨k, by exact_mod_cast hmk⟩

private theorem exists_toCircle_eq (n : ℕ) [NeZero n] (u : AddCircle (1 : ℚ)) (hu : n • u = 0) :
    ∃ x : ZMod n, toCircle n x = u := by
  induction u using QuotientAddGroup.induction_on with
  | H q =>
    rw [← AddCircle.coe_nsmul (1 : ℚ), AddCircle.coe_eq_zero_iff] at hu
    obtain ⟨k, hk⟩ := hu
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hk
    refine ⟨(k : ZMod n), ?_⟩
    rw [toCircle_intCast, hk, mul_comm, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)), one_mul]

private theorem cast_mod_mul_pow (p N : ℕ) (hN : 1 ≤ N) (m : ℕ) :
    ((m % p : ℕ) : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ (N - 1) =
      (m : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ (N - 1) := by
  have hpN : (p : ZMod (p ^ N)) ^ N = 0 := by exact_mod_cast ZMod.natCast_self (p ^ N)
  have hpp : (p : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ (N - 1) = 0 := by
    rw [← pow_succ', Nat.sub_add_cancel hN, hpN]
  conv_rhs => rw [← Nat.mod_add_div m p]
  rw [Nat.cast_add, add_mul, Nat.cast_mul, mul_right_comm, hpp, zero_mul, add_zero]

end UextAux

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime]
    (hpB : (p : B) ∈ IsLocalRing.maximalIdeal B)
    (t : B) (ht0 : t ≠ 0) (htk : ∀ m ∈ IsLocalRing.maximalIdeal B, t * m = 0) :
    ∃ N : ℕ, 1 ≤ N ∧ (p : B) ^ N = 0 ∧
      ∀ Λ : IsLocalRing.ResidueField B →+ ZMod p, ∃ π : B →+ ZMod (p ^ N),
        ∀ c : B, π (t * c) = ((Λ (IsLocalRing.residue B c)).val : ZMod (p ^ N)) * (p : ZMod (p ^ N)) ^ (N - 1) := by

  have _htk := htk
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨M, hM⟩ : IsNilpotent (IsLocalRing.maximalIdeal B) := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  have hpM : (p : B) ^ M = 0 := by
    have := Ideal.pow_mem_pow hpB M
    rwa [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hpN : (p : B) ^ (M + 1) = 0 := by rw [pow_succ, hpM, zero_mul]
  haveI : NeZero (p ^ (M + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine ⟨M + 1, Nat.le_add_left 1 M, hpN, fun Λ => ?_⟩

  let S : AddSubgroup B := (Ideal.span ({t} : Set B)).toAddSubgroup
  have hmemS : ∀ c : B, t * c ∈ S := fun c => Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hwd : ∀ c c' : B, t * c = t * c' →
      IsLocalRing.residue B c = IsLocalRing.residue B c' := by
    intro c c' h
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    by_contra hu
    have hu' : IsUnit (c - c') := by
      by_contra h'
      exact hu ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h'))
    apply ht0
    have : t * (c - c') = 0 := by rw [mul_sub, h, sub_self]
    exact hu'.mul_left_eq_zero.mp this
  have hS : ∀ x : ↥S, ∃ a : B, a * t = x := fun x => Ideal.mem_span_singleton'.mp x.2
  let cf : ↥S → B := fun x => (hS x).choose
  have hcf : ∀ x : ↥S, cf x * t = x := fun x => (hS x).choose_spec
  have hwd' : ∀ (x : ↥S) (c : B), (x : B) = t * c →
      IsLocalRing.residue B (cf x) = IsLocalRing.residue B c :=
    fun x c h => hwd _ _ (by rw [mul_comm, hcf, h])
  let g : ↥S →+ ZMod p :=
    { toFun := fun x => Λ (IsLocalRing.residue B (cf x))
      map_zero' := by
        show Λ (IsLocalRing.residue B (cf 0)) = 0
        rw [hwd' 0 0 (by rw [mul_zero]; rfl), map_zero, map_zero]
      map_add' := fun x y => by
        show Λ (IsLocalRing.residue B (cf (x + y))) =
          Λ (IsLocalRing.residue B (cf x)) + Λ (IsLocalRing.residue B (cf y))
        rw [← map_add Λ, ← map_add (IsLocalRing.residue B), hwd' (x + y) (cf x + cf y) ?_]
        rw [AddSubgroup.coe_add, mul_add, mul_comm t (cf x), mul_comm t (cf y), hcf, hcf] }
  have hg : ∀ c : B, g ⟨t * c, hmemS c⟩ = Λ (IsLocalRing.residue B c) := fun c =>
    show Λ _ = _ by rw [hwd' ⟨t * c, hmemS c⟩ c rfl]

  let ι : ZMod p →+ ZMod (p ^ (M + 1)) :=
    { toFun := fun x => (x.val : ZMod (p ^ (M + 1))) * (p : ZMod (p ^ (M + 1))) ^ (M + 1 - 1)
      map_zero' := by
        show ((0 : ZMod p).val : ZMod (p ^ (M + 1))) * _ = 0
        rw [ZMod.val_zero, Nat.cast_zero, zero_mul]
      map_add' := fun x y => by
        show ((x + y).val : ZMod (p ^ (M + 1))) * (p : ZMod (p ^ (M + 1))) ^ (M + 1 - 1) =
          (x.val : ZMod (p ^ (M + 1))) * (p : ZMod (p ^ (M + 1))) ^ (M + 1 - 1) +
          (y.val : ZMod (p ^ (M + 1))) * (p : ZMod (p ^ (M + 1))) ^ (M + 1 - 1)
        rw [← add_mul, ZMod.val_add, ← Nat.cast_add,
          UextAux.cast_mod_mul_pow p (M + 1) (Nat.le_add_left 1 M)] }

  let ψ₀ : CharacterModule ↥S := (UextAux.toCircle (p ^ (M + 1))).comp (ι.comp g)
  let f : ↥S →ₗ[ℤ] B := S.subtype.toIntLinearMap
  obtain ⟨χ, hχ⟩ :=
    CharacterModule.dual_surjective_of_injective f (fun a b h => Subtype.ext h) ψ₀
  have h1 : ∀ x : ↥S, χ (x : B) = ψ₀ x := fun x => by
    have := DFunLike.congr_fun hχ x
    rw [CharacterModule.dual_apply] at this
    exact this

  have hχT : ∀ b : B, χ b ∈ (UextAux.toCircle (p ^ (M + 1))).range := by
    intro b
    obtain ⟨x, hx⟩ := UextAux.exists_toCircle_eq (p ^ (M + 1)) (χ b) (by
      rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, hpN, zero_mul, map_zero])
    exact ⟨x, hx⟩
  let eT := AddMonoidHom.ofInjective (UextAux.toCircle_injective (p ^ (M + 1)))
  let π : B →+ ZMod (p ^ (M + 1)) :=
    eT.symm.toAddMonoidHom.comp (χ.codRestrict (UextAux.toCircle (p ^ (M + 1))).range hχT)
  have hπ : ∀ b : B, UextAux.toCircle (p ^ (M + 1)) (π b) = χ b := by
    intro b
    rw [← AddMonoidHom.ofInjective_apply (UextAux.toCircle_injective (p ^ (M + 1)))]
    show ((eT (eT.symm (χ.codRestrict _ hχT b))) : AddCircle (1 : ℚ)) = χ b
    rw [AddEquiv.apply_symm_apply]
    rfl
  refine ⟨π, fun c => UextAux.toCircle_injective (p ^ (M + 1)) ?_⟩
  rw [hπ, h1 ⟨t * c, hmemS c⟩]
  show UextAux.toCircle (p ^ (M + 1)) (ι (g ⟨t * c, hmemS c⟩)) = _
  rw [hg]
  rfl

end S_IsLocalRing_exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle
end P2MW
export P2MW.S_IsLocalRing_exists_addMonoidHom_zmod_pow_apply_mul_eq_of_socle (solution)
