-- Prove2me | solution 1 for GroundTheory.ProfCoh.AdditiveFunction.g_eq_zero_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:57.671858+00:00
-- url     : https://prove2.me/submissions/4d723284-433d-4494-a884-82bf20db10a0

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_Additive
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_of_torsion_trivial
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_g_add
import Theorems.Thm_GroundTheory_ProfCoh_AdditiveFunction_toFun_eq_zero_of_subsingleton
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
import Theorems.Thm_GroundTheory_ProfCoh_modN_mk_eq_zero_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
open GroundTheory.ProfCoh.AdditiveFunction
variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)
namespace GroundTheory.ProfCoh.AdditiveFunction
theorem _root_.solution (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite A] :
    d.g A = 0 := by
  suffices H : ∀ (N : ℕ) (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite A],
      Nat.card A = N → d.g A = 0 from H _ A rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A _ _ _ hN
  by_cases hA : ∀ a : A, l • a = 0 → a = 0
  · have hs : Function.Surjective (fun a : A => l • a) :=
      Finite.injective_iff_surjective.1 (fun a b hab =>
        sub_eq_zero.1 (hA (a - b) (by rw [smul_sub, sub_eq_zero]; exact hab)))
    have : Subsingleton (ModN A l) := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨a', rfl⟩ := hs a
      obtain ⟨b', rfl⟩ := hs b
      rw [(modN_mk_eq_zero_iff l _).2 ⟨a', rfl⟩, (modN_mk_eq_zero_iff l _).2 ⟨b', rfl⟩]⟩
    rw [d.g_eq_of_torsion_trivial A hA, d.toFun_eq_zero_of_subsingleton (X := ModN A l)]
  · push Not at hA
    obtain ⟨a₀, ha₀, hne⟩ := hA
    let m : A →+ A := (LinearMap.lsmul ℤ A (l : ℤ)).toAddMonoidHom
    have hm : ∀ a, m a = l • a := fun a => by simp [m]
    have hK : ∀ (γ : Γ) (a : A), a ∈ m.ker → γ • a ∈ m.ker := fun γ a ha => by
      rw [AddMonoidHom.mem_ker, hm] at ha ⊢
      rw [← smul_comm γ l a, ha, smul_zero]
    have hH : ∀ (γ : Γ) (a : A), a ∈ m.range → γ • a ∈ m.range := by
      rintro γ _ ⟨b, rfl⟩
      exact ⟨γ • b, by rw [hm, hm, smul_comm]⟩
    let _ := subgroupDistribMulAction m.ker hK
    let _ := subgroupDistribMulAction m.range hH
    have hKl : ∀ x : m.ker, l • x = 0 := fun x =>
      Subtype.ext (by rw [AddSubgroup.coe_nsmul, ← hm]; exact x.2)
    have hcard : Nat.card m.range < N := by
      have h₁ : Nat.card A = Nat.card m.range * Nat.card m.ker := by
        rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.ker,
          Nat.card_congr (QuotientAddGroup.quotientKerEquivRange m).toEquiv]
      have h₂ : 1 < Nat.card m.ker := by
        have : Nontrivial m.ker :=
          ⟨⟨⟨a₀, by rw [AddMonoidHom.mem_ker, hm, ha₀]⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
        exact Finite.one_lt_card
      have h₃ : 0 < Nat.card m.range := Nat.card_pos
      rw [← hN, h₁]
      nlinarith
    have e := d.g_add m.ker.subtype m.rangeRestrict (fun _ _ => rfl)
      (fun γ a => Subtype.ext (show m (γ • a) = γ • m a by rw [hm, hm, smul_comm]))
      (AddSubgroup.subtype_injective _)
      (fun y => ⟨fun hy => ⟨⟨y, congrArg Subtype.val hy⟩, rfl⟩,
        by rintro ⟨x, rfl⟩; exact Subtype.ext (AddMonoidHom.mem_ker.1 x.2)⟩)
      m.rangeRestrict_surjective
    rw [e, d.g_eq_zero_of_nsmul_eq_zero _ hKl, ih _ hcard _ rfl, add_zero]
end GroundTheory.ProfCoh.AdditiveFunction
