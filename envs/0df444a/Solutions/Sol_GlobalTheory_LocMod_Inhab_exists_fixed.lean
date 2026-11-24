-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.exists_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:47:06.441035+00:00
-- url     : https://prove2.me/submissions/b967605f-46da-4b3d-b040-49a62427e2fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_neg_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] {χ : G → G → ℂ} (h : IsBichar χ)
    (ρ σ : G → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f) (hσ : ∀ y f, σ y f = 0 → f = 0)
    (hc : ∀ x y f, ρ x (σ y f) = χ x y • σ y (ρ x f)) (L K : AddSubgroup G) [Finite (L ⧸ K.addSubgroupOf L)]
    (hsep : ∀ u ∈ L, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (P : Submodule ℂ V)
    (hP : ∀ u ∈ L, ∀ f ∈ P, ρ u f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P) {f : V} (hf : f ∈ P) (f0 : f ≠ 0)
    (hK : ∀ κ ∈ K, ρ κ f = f) : ∃ g ∈ P, g ≠ 0 ∧ ∀ u ∈ L, ρ u g = g := by
  classical
  letI : Fintype (L ⧸ K.addSubgroupOf L) := Fintype.ofFinite _
  let A : AddSubgroup G :=
    { carrier := {y | ∀ κ ∈ K, χ κ y = 1}
      zero_mem' := fun κ _ => h.zero_right κ
      add_mem' := fun {a b} ha hb κ hκ => by rw [h.right, ha κ hκ, hb κ hκ, mul_one]
      neg_mem' := fun {a} ha κ hκ => by
        have := h.right κ a (-a)
        rwa [add_neg_cancel, h.zero_right, ha κ hκ, one_mul, eq_comm] at this }
  have hcl : ∀ g : V, (∀ κ ∈ K, ρ κ g = g) → ∀ a b : L,
      (QuotientAddGroup.mk a : L ⧸ K.addSubgroupOf L) = QuotientAddGroup.mk b → ρ a g = ρ b g := fun g hg a b hab => by
    have : -(a : G) + b ∈ K := (QuotientAddGroup.eq (s := K.addSubgroupOf L)).1 hab
    rw [← hg _ this, hρ, add_neg_cancel_left, hg _ this]
  by_contra hcon
  have hz : ∀ y ∈ A, ∑ q : L ⧸ K.addSubgroupOf L, χ (q.out : L) y • ρ (q.out : L) f = 0 := fun y hy => by
    have hfix : ∀ κ ∈ K, ρ κ (σ y f) = σ y f := fun κ hκ => by rw [hc, hy κ hκ, hK κ hκ, one_smul]
    refine hσ y _ ?_
    simp only [map_sum, map_smul, ← hc]
    by_contra hne
    refine hcon ⟨_, P.sum_mem fun q _ => hP _ (q.out : L).2 _ (hP' y f hf), hne, fun u hu => ?_⟩
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (⟨u, hu⟩ : L))) _ _ fun q => ?_
    rw [hρ]
    refine hcl _ hfix (⟨u, hu⟩ + q.out) _ ?_
    simp
  let ch : (L ⧸ K.addSubgroupOf L) → (Multiplicative A →* ℂ) := fun q =>
    { toFun := fun y => χ (q.out : L) (y.toAdd : A)
      map_one' := h.zero_right _
      map_mul' := fun a b => h.right _ _ _ }
  have hinj : Function.Injective ch := by
    intro q q' hq
    rw [← q.out_eq', ← q'.out_eq', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    by_contra hn
    obtain ⟨y, hy, hne⟩ := hsep _ (-q.out + q'.out : L).2 hn
    have e : χ (q.out : L) y = χ (q'.out : L) y := DFunLike.congr_fun hq (Multiplicative.ofAdd ⟨y, hy⟩)
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, h.left, ← e, h.neg_mul] at hne
    exact hne rfl
  have hli := (linearIndependent_monoidHom (Multiplicative A) ℂ).comp ch hinj
  rw [Fintype.linearIndependent_iff] at hli
  refine f0 ((Module.forall_dual_apply_eq_zero_iff ℂ f).1 fun ℓ => ?_)
  have := hli (fun q => ℓ (ρ (q.out : L) f)) (by
    funext y
    have := congrArg ℓ (hz _ y.toAdd.2)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    rw [Finset.sum_apply]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) this
    simp [ch, mul_comm]) (QuotientAddGroup.mk 0)
  rwa [hcl f hK _ 0 (QuotientAddGroup.out_eq' _), hK ((0 : L) : G) K.zero_mem] at this
end GlobalTheory.LocMod.Inhab
