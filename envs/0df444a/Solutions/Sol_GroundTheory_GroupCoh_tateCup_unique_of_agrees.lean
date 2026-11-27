-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCup_unique_of_agrees
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:12.923175+00:00
-- url     : https://prove2.me/submissions/d0a22434-749c-4171-9125-1b92d4e9cac3

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Theorems.Thm_GroundTheory_GroupCoh_augSES_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorLeft_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorRight_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_moduleIso_hom_injective
import Theorems.Thm_GroundTheory_GroupCoh_tateCup_of_nonpos
import Theorems.Thm_GroundTheory_GroupCoh_tateCup_of_pos_of_nonpos
import Theorems.Thm_GroundTheory_GroupCoh_tateIsoH_tateCup
import Theorems.Thm_GroundTheory_GroupCoh_tateLeftIso_cupL
import Theorems.Thm_GroundTheory_GroupCoh_tateLeftIso_hom
import Theorems.Thm_GroundTheory_GroupCoh_tateRightIso_cupR
import Theorems.Thm_GroundTheory_GroupCoh_tateRightIso_hom


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
set_option maxHeartbeats 800000
namespace GroundTheory.GroupCoh
theorem _root_.solution (μ : ∀ p q : ℤ, TateCupFam k G p q)
    (hpos : ∀ (n m l : ℕ) [NeZero n] [NeZero m] [NeZero l] (hl : n + m = l) (A B : Rep.{u} k G)
      (a : tateCohomology A n) (b : tateCohomology B m),
      (tateIsoH (A ⊗ B) l l rfl).hom.hom (μ n m A B l (by omega) a b) =
        cupH hl ((tateIsoH A n n rfl).hom.hom a) ((tateIsoH B m m rfl).hom.hom b))
    (hleft : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        μ (p + 1) q (augIdeal k G ⊗ A) B (r + 1) (by omega)
          ((tδ (augSES_shortExact A) p (p + 1) rfl).hom a) b)
    (hright : ∀ (p q : ℤ) (A B : Rep.{u} k G) (r : ℤ) (h : p + q = r) (a : tateCohomology A p)
      (b : tateCohomology B q),
      (tδ (augSES_tensorLeft_shortExact A B) r (r + 1) rfl).hom (μ p q A B r h a b) =
        tsgn k p • μ p (q + 1) A (augIdeal k G ⊗ B) (r + 1) (by omega) a
          ((tδ (augSES_shortExact B) q (q + 1) rfl).hom b))
    (m : ℕ) : ∀ (p q : ℤ), (1 - p).toNat + (1 - q).toNat = m → ∀ (A B : Rep.{u} k G) (r : ℤ)
      (h : p + q = r) (a : tateCohomology A p) (b : tateCohomology B q),
      μ p q A B r h a b = tateCup p q A B r h a b := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro p q hm A B r h a b
  by_cases hp : p ≤ 0
  · rw [tateCup_of_nonpos q hp]
    apply moduleIso_hom_injective (tateLeftIso A B r)
    rw [tateLeftIso_cupL, tateLeftIso_hom]
    refine (hleft p q A B r h a b).trans ?_
    exact ih _ (by omega) (p + 1) q rfl _ _ _ _ _ _
  by_cases hq : q ≤ 0
  · rw [tateCup_of_pos_of_nonpos (by omega) hq]
    apply moduleIso_hom_injective (tateRightIso A B r)
    rw [tateRightIso_cupR, tateRightIso_hom]
    refine (hright p q A B r h a b).trans ?_
    exact congrArg (tsgn k p • ·) (ih _ (by omega) p (q + 1) rfl _ _ _ _ _ _)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m' : ℕ, q = m' := ⟨q.toNat, by omega⟩
    obtain ⟨l, rfl⟩ : ∃ l : ℕ, r = l := ⟨r.toNat, by omega⟩
    have : NeZero n := ⟨by omega⟩
    have : NeZero m' := ⟨by omega⟩
    have : NeZero l := ⟨by omega⟩
    have hl : n + m' = l := by omega
    apply moduleIso_hom_injective (tateIsoH (A ⊗ B) l l rfl)
    rw [hpos n m' l hl, tateIsoH_tateCup rfl rfl rfl h hl]
end GroundTheory.GroupCoh
