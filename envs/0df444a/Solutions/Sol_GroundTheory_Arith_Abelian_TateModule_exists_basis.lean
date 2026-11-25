-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.TateModule.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:36.635895+00:00
-- url     : https://prove2.me/submissions/2e794d89-c1a7-48c2-b1f9-4af35c2313ac

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TorsionGalois
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
import Theorems.Thm_GroundTheory_Arith_Abelian_TateModule_zero_apply
import Theorems.Thm_GroundTheory_Arith_Abelian_zmodMulHom_apply
import Theorems.Thm_GroundTheory_Arith_Abelian_exists_tateModule_apply_eq
import Theorems.Thm_GroundTheory_Arith_Abelian_exists_toZModPow_eq
import Theorems.Thm_GroundTheory_Arith_Abelian_TateModule_dvd_of_nsmul_add_nsmul_eq_zero
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_openNormalSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
import Theorems.Thm_GroundTheory_ProfCoh_openNormalSubgroupEquiv_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] GroundTheory.ProfCoh.coe_openNormalSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer
attribute [local simp] GroundTheory.ProfCoh.openNormalSubgroupEquiv_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]
namespace GroundTheory.Arith.Abelian
namespace TateModule
theorem _root_.solution
    (hcard : ∀ k, Nat.card {P : A // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2)
    (hbase : ∃ P Q : A, ℓ • P = 0 ∧ ℓ • Q = 0 ∧ ∀ a b : ℕ, a • P + b • Q = 0 → ℓ ∣ a ∧ ℓ ∣ b) :
    Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ A)) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := hbase
  obtain ⟨t, ht⟩ := exists_tateModule_apply_eq hcard 1 P (by rwa [pow_one])
  obtain ⟨s, hs⟩ := exists_tateModule_apply_eq hcard 1 Q (by rwa [pow_one])
  have h1 : ∀ a b : ℕ, a • (t : ℕ → A) 1 + b • (s : ℕ → A) 1 = 0 → ℓ ∣ a ∧ ℓ ∣ b := by
    rw [ht, hs]; exact hPQ
  have hind := TateModule.dvd_of_nsmul_add_nsmul_eq_zero t s h1
  let g : ∀ k, ZMod (ℓ ^ k) × ZMod (ℓ ^ k) →+ A := fun k =>
    (zmodMulHom _ _ (TateModule.pow_nsmul t k)).coprod (zmodMulHom _ _ (TateModule.pow_nsmul s k))
  have hg : ∀ k x, g k x = x.1.val • (t : ℕ → A) k + x.2.val • (s : ℕ → A) k := by
    intro k x
    simp [g, zmodMulHom_apply]
  have hginj : ∀ k, Function.Injective (g k) := by
    intro k
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ hxy
    rw [hg] at hxy
    obtain ⟨hx, hy⟩ := hind k _ _ hxy
    have hx0 : x = 0 := by
      rw [← ZMod.val_eq_zero]; exact Nat.eq_zero_of_dvd_of_lt hx (ZMod.val_lt x)
    have hy0 : y = 0 := by
      rw [← ZMod.val_eq_zero]; exact Nat.eq_zero_of_dvd_of_lt hy (ZMod.val_lt y)
    simp [hx0, hy0]
  let Φ : ℤ_[ℓ] × ℤ_[ℓ] →ₗ[ℤ_[ℓ]] TateModule ℓ A :=
    (LinearMap.toSpanSingleton ℤ_[ℓ] _ t).coprod (LinearMap.toSpanSingleton ℤ_[ℓ] _ s)
  have hΦ : ∀ a b k, ((Φ (a, b) : TateModule ℓ A) : ℕ → A) k =
      g k (PadicInt.toZModPow k a, PadicInt.toZModPow k b) := by
    intro a b k
    rw [hg]
    simp [Φ, LinearMap.coprod_apply, TateModule.smul_apply]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hk : ∀ k, PadicInt.toZModPow k a = 0 ∧ PadicInt.toZModPow k b = 0 := by
      intro k
      have h := congrArg (fun u : TateModule ℓ A => (u : ℕ → A) k) hab
      simp only [hΦ, ZeroMemClass.coe_zero, Pi.zero_apply] at h
      have h0 := hginj k (h.trans (map_zero (g k)).symm)
      exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
    have ha : a = 0 := PadicInt.ext_of_toZModPow.mp fun k => by rw [(hk k).1, map_zero]
    have hb : b = 0 := PadicInt.ext_of_toZModPow.mp fun k => by rw [(hk k).2, map_zero]
    simp [ha, hb]
  have hsurj : Function.Surjective Φ := by
    intro u
    have hlev : ∀ k, ∃ x : ZMod (ℓ ^ k) × ZMod (ℓ ^ k), g k x = (u : ℕ → A) k := by
      intro k
      have := finite_torsion_of_card hcard k
      let G : ZMod (ℓ ^ k) × ZMod (ℓ ^ k) → {P : A // ℓ ^ k • P = 0} := fun x => ⟨g k x, by
        rw [hg, nsmul_add, nsmul_swap (ℓ ^ k) x.1.val, nsmul_swap (ℓ ^ k) x.2.val,
          TateModule.pow_nsmul t k, TateModule.pow_nsmul s k]
        simp⟩
      have hG : Function.Injective G := fun x y h => hginj k (congrArg Subtype.val h)
      have hGb := hG.bijective_of_nat_card_le (by rw [hcard, Nat.card_prod, Nat.card_zmod, sq])
      obtain ⟨x, hx⟩ := hGb.2 ⟨(u : ℕ → A) k, TateModule.pow_nsmul u k⟩
      exact ⟨x, congrArg Subtype.val hx⟩
    choose x hx using hlev
    have hcompat : ∀ k, (((x (k + 1)).1.val : ZMod (ℓ ^ k)), ((x (k + 1)).2.val : ZMod (ℓ ^ k)))
        = x k := by
      intro k
      apply hginj k
      rw [hx k, hg]
      dsimp only
      rw [val_nsmul_eq (TateModule.pow_nsmul t k) rfl, val_nsmul_eq (TateModule.pow_nsmul s k) rfl,
        ← TateModule.nsmul_succ t k, ← TateModule.nsmul_succ s k, nsmul_swap _ ℓ,
        nsmul_swap _ ℓ, ← nsmul_add, ← hg (k + 1) (x (k + 1)), hx (k + 1),
        TateModule.nsmul_succ u k]
    obtain ⟨a, ha⟩ := exists_toZModPow_eq (fun k => (x k).1) fun k => congrArg Prod.fst (hcompat k)
    obtain ⟨b, hb⟩ := exists_toZModPow_eq (fun k => (x k).2) fun k => congrArg Prod.snd (hcompat k)
    refine ⟨(a, b), Subtype.ext (funext fun k => ?_)⟩
    rw [hΦ, ha, hb]
    exact hx k
  exact ⟨(Module.Basis.finTwoProd ℤ_[ℓ]).map (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩)⟩
end TateModule
end GroundTheory.Arith.Abelian
