-- Prove2me | solution 1 for Ihara.hasTrivialSchurMultiplier_SL2_ZMod_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/25887966-25ee-516f-a359-2a5881d44d59

import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.Group
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Coset.Card
import Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_step
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.Int.GCD
import Theorems.Thm_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_sq
import Theorems.Thm_Ihara_exists_pow_prime_pow_eq_one_of_sl2_stem
import Theorems.Thm_Ihara_isPerfect_SL2_ZMod_prime_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime_pow

set_option Elab.async false

section Inl_P2B_TransferSubgroup

namespace Ihara
p2m_export "Ihara" "hasTrivialSchurMultiplier_SL2_ZMod_step HasTrivialSchurMultiplier hasTrivialSchurMultiplier_SL2_ZMod_sq exists_pow_prime_pow_eq_one_of_sl2_stem isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open Subgroup

open scoped commutatorElement

variable {E G : Type*} [Group E] [Group G]

theorem pow_index_mem_ker_inf_commutator_comap (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G) [H.FiniteIndex]
    {x : E} (hx : x ∈ π.ker) (hxcomm : x ∈ commutator E) :
    x ^ H.index ∈ π.ker ⊓ ⁅H.comap π, H.comap π⁆ := by
  classical
  set H' := H.comap π with hH'
  have hidx : H'.index = H.index := H.index_comap_of_surjective hπ
  haveI : H'.FiniteIndex := ⟨by rw [hidx]; exact FiniteIndex.index_ne_zero⟩
  refine ⟨pow_mem hx _, ?_⟩

  let ϕ : ↥H' →* Abelianization ↥H' := Abelianization.of
  have hkey : ∀ (k : ℕ) (g₀ : E), g₀⁻¹ * x ^ k * g₀ ∈ H' → g₀⁻¹ * x ^ k * g₀ = x ^ k := by
    intro k g₀ _
    have hxc : x ^ k ∈ center E := pow_mem (hcen hx) k
    rw [mul_assoc, ← mem_center_iff.mp hxc g₀, inv_mul_cancel_left]
  have htr := MonoidHom.transfer_eq_pow ϕ x hkey

  have hker : MonoidHom.transfer ϕ x = 1 :=
    MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker (MonoidHom.transfer ϕ) hxcomm)
  rw [htr] at hker
  have hmem : (⟨x ^ H'.index, MonoidHom.transfer_eq_pow_aux x hkey⟩ : ↥H') ∈ commutator ↥H' := by
    rw [← Abelianization.ker_of]
    exact MonoidHom.mem_ker.mpr hker

  have hmap : (commutator ↥H').map H'.subtype = ⁅H', H'⁆ := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, H'.range_subtype]
  rw [← hidx, ← hmap]
  exact ⟨_, hmem, rfl⟩

theorem commutator_comap_eq_bot_of_isCyclic (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G) [IsCyclic H] :
    ⁅H.comap π, H.comap π⁆ = ⊥ := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := ↥H)
  obtain ⟨c, hc⟩ := hπ γ

  have hsplit : ∀ u ∈ H.comap π, ∃ (k : ℤ) (z : E), z ∈ π.ker ∧ u = c ^ k * z := by
    intro u hu
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hγ ⟨π u, hu⟩)
    have hk' : (γ : G) ^ k = π u := by rw [← coe_zpow, hk]
    refine ⟨k, (c ^ k)⁻¹ * u, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hc, hk', inv_mul_cancel]
  rw [eq_bot_iff, commutator_le]
  intro u hu v hv
  obtain ⟨k, z, hz, rfl⟩ := hsplit u hu
  obtain ⟨l, w, hw, rfl⟩ := hsplit v hv
  have hzc := mem_center_iff.mp (hcen hz)
  have hwc := mem_center_iff.mp (hcen hw)
  rw [mem_bot, commutatorElement_eq_one_iff_commute]
  show c ^ k * z * (c ^ l * w) = c ^ l * w * (c ^ k * z)
  calc c ^ k * z * (c ^ l * w)
      = c ^ k * (z * c ^ l) * w := by group
    _ = c ^ k * (c ^ l * z) * w := by rw [← hzc (c ^ l)]
    _ = c ^ (k + l) * (z * w) := by rw [zpow_add]; group
    _ = c ^ (l + k) * (w * z) := by rw [add_comm k l, hwc z]
    _ = c ^ l * (c ^ k * w) * z := by rw [zpow_add]; group
    _ = c ^ l * (w * c ^ k) * z := by rw [hwc (c ^ k)]
    _ = c ^ l * w * (c ^ k * z) := by group

theorem pow_index_eq_one_of_isCyclic_of_stem (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G) [H.FiniteIndex] [IsCyclic H]
    {x : E} (hx : x ∈ π.ker) (hxcomm : x ∈ commutator E) : x ^ H.index = 1 := by
  have h := pow_index_mem_ker_inf_commutator_comap π hπ hcen H hx hxcomm
  rw [commutator_comap_eq_bot_of_isCyclic π hπ hcen H, inf_bot_eq, mem_bot] at h
  exact h

section LocalTriviality

universe u v

variable {E : Type u} {G : Type v} [Group E] [Group G]

theorem ker_inf_commutator_comap_eq_bot_of_local (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G)
    (hH : ∀ (E' : Type u) [Group E'] (π' : E' →* ↥H), Function.Surjective π' →
      π'.ker ≤ center E' → π'.ker ⊓ commutator E' = ⊥) :
    π.ker ⊓ ⁅H.comap π, H.comap π⁆ = ⊥ := by
  set H' := H.comap π with hH'
  let π' : ↥H' →* ↥H := π.subgroupComap H
  have hsurj' : Function.Surjective π' := π.subgroupComap_surjective_of_surjective H hπ
  have hker' : ∀ y : ↥H', y ∈ π'.ker ↔ (y : E) ∈ π.ker := fun y => by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff]
    rfl
  have hcen' : π'.ker ≤ center ↥H' := fun y hy => by
    rw [mem_center_iff]
    intro z
    apply Subtype.ext
    change (z : E) * y = y * z
    exact mem_center_iff.mp (hcen ((hker' y).mp hy)) z
  have h := hH (↥H') π' hsurj' hcen'
  have hmap : (commutator ↥H').map H'.subtype = ⁅H', H'⁆ := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, H'.range_subtype]
  rw [eq_bot_iff]
  rintro x ⟨hx, hxc⟩
  rw [← hmap] at hxc
  obtain ⟨y, hy, rfl⟩ := hxc
  have hy' : y ∈ π'.ker ⊓ commutator ↥H' := ⟨(hker' y).mpr hx, hy⟩
  rw [h, mem_bot] at hy'
  rw [mem_bot, hy']
  rfl

theorem pow_index_eq_one_of_local (π : E →* G) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center E) (H : Subgroup G) [H.FiniteIndex]
    (hH : ∀ (E' : Type u) [Group E'] (π' : E' →* ↥H), Function.Surjective π' →
      π'.ker ≤ center E' → π'.ker ⊓ commutator E' = ⊥)
    {x : E} (hx : x ∈ π.ker) (hxcomm : x ∈ commutator E) : x ^ H.index = 1 := by
  have h := pow_index_mem_ker_inf_commutator_comap π hπ hcen H hx hxcomm
  rw [ker_inf_commutator_comap_eq_bot_of_local π hπ hcen H hH, mem_bot] at h
  exact h

end LocalTriviality

end Ihara

end Inl_P2B_TransferSubgroup

section Inl_P2A_SL2Card

namespace Ihara
p2m_export "Ihara" "hasTrivialSchurMultiplier_SL2_ZMod_step HasTrivialSchurMultiplier hasTrivialSchurMultiplier_SL2_ZMod_sq exists_pow_prime_pow_eq_one_of_sl2_stem isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open Matrix

open scoped MatrixGroups

variable (F : Type*) [Field F]

private lemma det_GL_two_surjective :
    Function.Surjective (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ) := by
  intro u
  have hmul : ∀ x y : F, !![x, 0; 0, 1] * !![y, 0; 0, 1] = !![x * y, 0; 0, 1] := by
    intro x y
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hone : (1 : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨⟨!![(u : F), 0; 0, 1], !![((u⁻¹ : Fˣ) : F), 0; 0, 1], ?_, ?_⟩, ?_⟩
  · rw [hmul, hone]
    norm_num
  · rw [hmul, hone]
    norm_num
  · apply Units.ext
    rw [GeneralLinearGroup.val_det_apply]
    show Matrix.det !![(u : F), 0; 0, 1] = (u : F)
    rw [Matrix.det_fin_two_of]
    ring

private lemma card_ker_det_GL_two :
    Nat.card (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ)) =
      Nat.card (SpecialLinearGroup (Fin 2) F) := by
  refine (Nat.card_eq_of_bijective
    (fun g : SpecialLinearGroup (Fin 2) F =>
      (⟨SpecialLinearGroup.toGL g, by
        rw [MonoidHom.mem_ker]
        exact SpecialLinearGroup.coeToGL_det g⟩ :
        MonoidHom.ker (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ)))
    ⟨?_, ?_⟩).symm
  · intro g g' hgg'
    exact SpecialLinearGroup.toGL_injective (Subtype.ext_iff.mp hgg')
  · rintro ⟨A, hA⟩
    rw [MonoidHom.mem_ker] at hA
    have hAdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      have := congrArg (Units.val) hA
      rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at this
    refine ⟨⟨(A : Matrix (Fin 2) (Fin 2) F), hAdet⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rfl

theorem card_SL2_zmod (p : ℕ) [Fact p.Prime] :
    Nat.card (SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  have hp : p.Prime := Fact.out
  have key : Nat.card (GL (Fin 2) (ZMod p)) =
      (p - 1) * Nat.card (SpecialLinearGroup (Fin 2) (ZMod p)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ))]
    rw [card_ker_det_GL_two]
    congr 1
    rw [Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective _ (det_GL_two_surjective (ZMod p))).toEquiv]
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_two] at key
  norm_num at key
  have h1 : 1 ≤ p := hp.one_lt.le
  have h2 : p ≤ p ^ 2 := by nlinarith
  have h3 : 1 ≤ p ^ 2 := h1.trans h2
  have harith : (p ^ 2 - 1) * (p ^ 2 - p) = (p - 1) * (p * (p ^ 2 - 1)) := by
    zify [h1, h2, h3]
    ring
  rw [harith] at key
  rw [Nat.card_eq_fintype_card]
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hp.one_lt) key.symm

end Ihara

end Inl_P2A_SL2Card

section Inl_P2B_Induction

set_option autoImplicit false

namespace Ihara
p2m_export "Ihara" "hasTrivialSchurMultiplier_SL2_ZMod_step HasTrivialSchurMultiplier hasTrivialSchurMultiplier_SL2_ZMod_sq exists_pow_prime_pow_eq_one_of_sl2_stem isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open Matrix
open scoped MatrixGroups

section LevelOne

variable (q : ℕ)

def unipU : SL(2, ZMod q) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem unipU_pow_coe (n : ℕ) :
    ((unipU q ^ n : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))
      = !![1, (n : ZMod q); 0, 1] := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero]
    exact Matrix.one_fin_two
  | succ n ih =>
    rw [pow_succ]
    change ((unipU q ^ n : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 1; 0, 1] = _
    rw [ih, Matrix.mul_fin_two, Nat.cast_succ]
    simp [add_comm]

theorem unipU_pow_self [Fact q.Prime] : unipU q ^ q = 1 :=
  Subtype.ext <| by
    rw [unipU_pow_coe, ZMod.natCast_self]
    exact Matrix.one_fin_two.symm

theorem unipU_ne_one [Fact q.Prime] : unipU q ≠ 1 := by
  intro h
  have h01 := congrArg (fun g : SL(2, ZMod q) => (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1) h
  change (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1
    = (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 at h01
  simp at h01

theorem orderOf_unipU [Fact q.Prime] : orderOf (unipU q) = q :=
  orderOf_eq_prime (unipU_pow_self q) (unipU_ne_one q)

theorem index_zpowers_unipU [Fact q.Prime] :
    (Subgroup.zpowers (unipU q)).index = q ^ 2 - 1 := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have h := (Subgroup.zpowers (unipU q)).card_mul_index
  rw [Nat.card_zpowers, orderOf_unipU, card_SL2_zmod q] at h
  exact Nat.eq_of_mul_eq_mul_left hq h

theorem hasTrivialSchurMultiplier_SL2_ZMod_of_kerPowQ (hq : q.Prime)
    (hA : ∀ (E : Type) [Group E] (π : E →* SL(2, ZMod q)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∀ x ∈ π.ker, x ∈ commutator E →
        ∃ k : ℕ, x ^ (q ^ k) = 1) :
    HasTrivialSchurMultiplier SL(2, ZMod q) := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro E _ π hπ hcen hcomm
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxcomm : x ∈ commutator E := hcomm hx
  obtain ⟨k, hk⟩ := hA E π hπ hcen x hx hxcomm
  have htr : x ^ (q ^ 2 - 1) = 1 :=
    index_zpowers_unipU q ▸
      pow_index_eq_one_of_isCyclic_of_stem π hπ hcen (Subgroup.zpowers (unipU q)) hx hxcomm
  have hcop : Nat.Coprime (q ^ k) (q ^ 2 - 1) := by
    refine Nat.Coprime.pow_left k ?_
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
    have h2 : Nat.Coprime (q ^ 2) (q ^ 2 - 1) :=
      (Nat.coprime_self_sub_right h1).mpr (Nat.coprime_one_right _)
    exact (Nat.coprime_pow_left_iff two_pos q (q ^ 2 - 1)).mp h2
  have h : x ^ (q ^ k).gcd (q ^ 2 - 1) = 1 := pow_gcd_eq_one.mpr ⟨hk, htr⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

end LevelOne

theorem hasTrivialSchurMultiplier_SL2_ZMod_prime_pow_of (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hA : ∀ (E : Type) [Group E] (π : E →* SL(2, ZMod q)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∀ x ∈ π.ker, x ∈ commutator E →
        ∃ k : ℕ, x ^ (q ^ k) = 1)
    (hM2 : HasTrivialSchurMultiplier SL(2, ZMod (q ^ 2)))
    (hperf : ∀ m : ℕ, 3 ≤ m → commutator SL(2, ZMod (q ^ m)) = ⊤)
    {n : ℕ} (hn : n ≠ 0) : HasTrivialSchurMultiplier SL(2, ZMod (q ^ n)) := by
  refine Nat.le_induction (m := 1)
    (P := fun n _ => HasTrivialSchurMultiplier SL(2, ZMod (q ^ n))) ?_ ?_ n
    (Nat.one_le_iff_ne_zero.mpr hn)
  · show HasTrivialSchurMultiplier SL(2, ZMod (q ^ 1))
    rw [pow_one]
    exact hasTrivialSchurMultiplier_SL2_ZMod_of_kerPowQ q hq hA
  · intro n hmn ih
    have ih' : HasTrivialSchurMultiplier SL(2, ZMod (q ^ n)) := ih
    show HasTrivialSchurMultiplier SL(2, ZMod (q ^ (n + 1)))
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      exact hM2
    · exact hasTrivialSchurMultiplier_SL2_ZMod_step q (n + 1) hq hq2 (by omega)
        (hperf (n + 1) (by omega)) (by simpa using ih')

end Ihara

end Inl_P2B_Induction

section Inl_P2B_Assembly

namespace Ihara
p2m_export "Ihara" "hasTrivialSchurMultiplier_SL2_ZMod_step HasTrivialSchurMultiplier hasTrivialSchurMultiplier_SL2_ZMod_sq exists_pow_prime_pow_eq_one_of_sl2_stem isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open scoped MatrixGroups

theorem hasTrivialSchurMultiplier_SL2_ZMod_prime_pow_of_slots {q : ℕ} (hq : q.Prime)
    (h5 : 5 ≤ q)
    (hA : ∀ (E : Type) [Group E] (π : E →* SL(2, ZMod q)), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∀ x ∈ π.ker, x ∈ commutator E →
        ∃ k : ℕ, x ^ (q ^ k) = 1)
    (hP1 : ∀ m : ℕ, m ≠ 0 → commutator SL(2, ZMod (q ^ m)) = ⊤)
    {n : ℕ} (hn : n ≠ 0) : HasTrivialSchurMultiplier SL(2, ZMod (q ^ n)) :=
  hasTrivialSchurMultiplier_SL2_ZMod_prime_pow_of q hq (by omega) hA
    (hasTrivialSchurMultiplier_SL2_ZMod_sq q hq h5 (hP1 2 two_ne_zero)
      (by rw [pow_one]; exact hasTrivialSchurMultiplier_SL2_ZMod_of_kerPowQ q hq hA))
    (fun m hm => hP1 m (by omega)) hn

end Ihara

end Inl_P2B_Assembly

section Inl_P2B_Final

namespace Ihara
p2m_export "Ihara" "hasTrivialSchurMultiplier_SL2_ZMod_step HasTrivialSchurMultiplier hasTrivialSchurMultiplier_SL2_ZMod_sq exists_pow_prime_pow_eq_one_of_sl2_stem isPerfect_SL2_ZMod_prime_pow"
p2m_open "Ihara"

open scoped MatrixGroups

theorem sl2_zmod_prime_pow_hasTrivialSchurMultiplier {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    {n : ℕ} (hn : n ≠ 0) : HasTrivialSchurMultiplier SL(2, ZMod (q ^ n)) :=
  haveI : Fact q.Prime := ⟨hq⟩
  hasTrivialSchurMultiplier_SL2_ZMod_prime_pow_of_slots hq h5
    (fun E _ π hπ hcen x hx hxcomm =>
      exists_pow_prime_pow_eq_one_of_sl2_stem q (by omega) π hπ hcen hx hxcomm)
    (fun m hm => Group.isPerfect_def.mp (isPerfect_SL2_ZMod_prime_pow hq h5 hm)) hn

end Ihara

end Inl_P2B_Final

open scoped MatrixGroups in
theorem solution {q : ℕ} (hq : q.Prime) (h5 : 5 ≤ q)
    {n : ℕ} (hn : n ≠ 0) : Ihara.HasTrivialSchurMultiplier (SL(2, ZMod (q ^ n))) :=
  Ihara.sl2_zmod_prime_pow_hasTrivialSchurMultiplier hq h5 hn

end S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime_pow
end P2MW
export P2MW.S_Ihara_hasTrivialSchurMultiplier_SL2_ZMod_prime_pow (solution)
