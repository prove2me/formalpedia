-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CofinalDual.index_eq_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:27.422853+00:00
-- url     : https://prove2.me/submissions/7fd79177-b31a-406f-89f1-7421f6a6aaf7

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_card_le_of_pairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CofinalDual
namespace GlobalTheory.CompanionTheory.SW.CofinalDual
theorem _root_.solution {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (c : X → Y → ℂ)
    (hn : ∀ x y, ‖c x y‖ = 1)
    (hl : ∀ x x' y, c (x + x') y = c x y * c x' y)
    (hr : ∀ x y y', c x (y + y') = c x y * c x y')
    (N : AddSubgroup X) (M : AddSubgroup Y)
    (hN : ∀ x, x ∈ N ↔ ∀ y, c x y = 1) (hM : ∀ y, y ∈ M ↔ ∀ x, c x y = 1)
    [N.FiniteIndex] [M.FiniteIndex] : N.index = M.index := by
  have hx : ∀ (x x' : X) (y : Y), (x : X ⧸ N) = x' → c x y = c x' y := by
    intro x x' y h
    have hm : -x + x' ∈ N := QuotientAddGroup.eq.1 h
    have := hl x (-x + x') y
    rw [add_neg_cancel_left, (hN _).1 hm y, mul_one] at this
    exact this.symm
  have hy : ∀ (x : X) (y y' : Y), (y : Y ⧸ M) = y' → c x y = c x y' := by
    intro x y y' h
    have hm : -y + y' ∈ M := QuotientAddGroup.eq.1 h
    have := hr x y (-y + y')
    rw [add_neg_cancel_left, (hM _).1 hm x, mul_one] at this
    exact this.symm
  let b : X ⧸ N → Y ⧸ M → ℂ := fun p q => c (Quotient.out p) (Quotient.out q)
  have hb : ∀ (x : X) (y : Y), b (x : X ⧸ N) (y : Y ⧸ M) = c x y := fun x y => by
    change c (Quotient.out (x : X ⧸ N)) (Quotient.out (y : Y ⧸ M)) = c x y
    rw [hx _ x _ (QuotientAddGroup.out_eq' _), hy _ _ y (QuotientAddGroup.out_eq' _)]
  have bn : ∀ p q, ‖b p q‖ = 1 := fun p q => hn _ _
  have bl : ∀ p p' q, b (p + p') q = b p q * b p' q := by
    intro p p' q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective p'
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hl]
  have br : ∀ p q q', b p (q + q') = b p q * b p q' := by
    intro p q q'
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y', rfl⟩ := QuotientAddGroup.mk_surjective q'
    rw [← QuotientAddGroup.mk_add, hb, hb, hb, hr]
  have k1 : ∀ p, (∀ q, b p q = 1) → p = 0 := by
    intro p h
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
    exact (QuotientAddGroup.eq_zero_iff x).2 ((hN x).2 fun y => by rw [← hb, h])
  have k2 : ∀ q, (∀ p, b p q = 1) → q = 0 := by
    intro q h
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (QuotientAddGroup.eq_zero_iff y).2 ((hM y).2 fun x => by rw [← hb, h])
  exact le_antisymm (card_le_of_pairing b bn bl br k1)
    (card_le_of_pairing (fun q p => b p q) (fun q p => bn p q) (fun q q' p => br p q q')
      (fun q p p' => bl p p' q) k2)
end GlobalTheory.CompanionTheory.SW.CofinalDual
