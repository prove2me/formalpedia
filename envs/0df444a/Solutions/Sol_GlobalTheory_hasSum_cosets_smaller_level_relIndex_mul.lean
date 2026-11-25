-- Prove2me | solution 1 for GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:52.213824+00:00
-- url     : https://prove2.me/submissions/5b2c56a6-b1ef-4ca1-b4f4-18d6937386ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsSmallerLevelRelIndexMul
import Theorems.Thm_GlobalTheory_hasSum_comp_fst_card_mul_of_fintype

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open QuotientGroup
namespace GlobalTheory
theorem _root_.solution : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  intro G _ K J H Γ hKJ hJH hHΓ hidx Ψ z hvan hinv hsum
  classical

  set f : Γ ⧸ J.subgroupOf Γ → ℂ := fun x => Ψ (x.out : Γ) with hf
  have hfmk : ∀ g : Γ, f (mk g) = Ψ (g : G) := by
    intro g
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf Γ) g
    simp only [hf, hj, Subgroup.coe_mul]
    exact hinv _ g.2 _ (Subgroup.mem_subgroupOf.mp j.2)

  let ι : H ⧸ J.subgroupOf H → Γ ⧸ J.subgroupOf Γ := fun y => mk (Subgroup.inclusion hHΓ y.out)
  have hιmk : ∀ a : H, ι (mk a) = mk (Subgroup.inclusion hHΓ a) := by
    intro a
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) a
    show (mk (Subgroup.inclusion hHΓ (mk a : H ⧸ J.subgroupOf H).out) : Γ ⧸ J.subgroupOf Γ) = _
    rw [hj, QuotientGroup.eq]
    simp [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mp j.2
  have hιinj : Function.Injective ι := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [hιmk, hιmk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hxy
  have h1 : HasSum f z := by
    rw [← hιinj.hasSum_iff]
    · convert hsum using 1
      funext y
      show f (mk (Subgroup.inclusion hHΓ y.out)) = _
      rw [hfmk]
      rfl
    · intro x hx
      show Ψ (x.out : G) = 0
      apply hvan _ x.out.2
      intro hH
      apply hx
      refine ⟨mk ⟨(x.out : G), hH⟩, ?_⟩
      rw [hιmk]
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rfl

  have hle : K.subgroupOf Γ ≤ J.subgroupOf Γ := fun x hx => by
    simpa [Subgroup.mem_subgroupOf] using hKJ (Subgroup.mem_subgroupOf.mp hx)
  let e := Subgroup.quotientEquivProdOfLE hle
  have hJΓ : J ≤ Γ := hJH.trans hHΓ
  have hrel : (K.subgroupOf Γ).relIndex (J.subgroupOf Γ) = K.relIndex J :=
    Subgroup.relIndex_subgroupOf hJΓ
  haveI : (((K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))).FiniteIndex := ⟨by
    rw [← Subgroup.relIndex, hrel]; exact hidx⟩
  haveI : Finite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) :=
    Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))
  have hcard : (Fintype.card (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) : ℂ)
      = (K.relIndex J : ℂ) := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index, ← Subgroup.relIndex, hrel]
  have h2 := hasSum_comp_fst_card_mul_of_fintype (β := J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) f z h1
  rw [hcard, ← e.hasSum_iff] at h2
  convert h2 using 1
  funext y
  have he1 : (e y).1 = mk y.out := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  simp only [Function.comp_apply, he1, hfmk]
end GlobalTheory
