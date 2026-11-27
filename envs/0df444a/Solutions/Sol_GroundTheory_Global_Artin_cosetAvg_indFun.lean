-- Prove2me | solution 1 for GroundTheory.Global.Artin.cosetAvg_indFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:36.961798+00:00
-- url     : https://prove2.me/submissions/2968e3b1-f191-4168-b265-c26ebe395376

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
import Theorems.Thm_GroundTheory_Global_Artin_cosetAvg_indFun_conjFun
import Theorems.Thm_GroundTheory_Global_Artin_indFun_comp_subtype_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G] [Fintype G] {H D I : Subgroup G}
open Classical
namespace GroundTheory.Global.Artin
theorem _root_.solution [Fintype H] [Fintype D] [Fintype I] (hID : I ≤ D)
    [(I.subgroupOf D).Normal] {φ : G} (hφ : φ ∈ D)
    (hgen : Subgroup.zpowers ((⟨φ, hφ⟩ : D) : D ⧸ I.subgroupOf D) = ⊤) {f : H → ℂ}
    (hf : IsClassFun f) (x : DoubleCoset.Quotient (H : Set G) D → G)
    (hx : ∀ q, DoubleCoset.mk H D (x q) = q) (φx : DoubleCoset.Quotient (H : Set G) D → H)
    (hφx : ∀ q, ∃ i ∈ (MulAut.conj (x q) • I : Subgroup G),
      (φx q : G) = x q * φ ^ (frobIndex H D I (x q) : ℤ) * (x q)⁻¹ * i) (m : ℤ) :
    cosetAvg I φ (indFun H.subtype f) m =
      ∑ q, if (frobIndex H D I (x q) : ℤ) ∣ m then
        (frobIndex H D I (x q) : ℂ) *
          cosetAvg ((MulAut.conj (x q) • I : Subgroup G).subgroupOf H) (φx q) f
            (m / frobIndex H D I (x q))
      else 0 := by
  classical
  have hA : ∀ i : I, indFun H.subtype f (φ ^ m * i) = ∑ q,
      indFun ((MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D).subtype (conjFun H D (x q) f)
        ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩ := by
    intro i
    have := congrFun (indFun_comp_subtype_eq_sum H D hf x hx)
      ⟨φ ^ m * i, D.mul_mem (D.zpow_mem hφ m) (hID i.2)⟩
    rw [Finset.sum_apply] at this
    exact this
  rw [cosetAvg]
  simp_rw [hA]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ ↦
    cosetAvg_indFun_conjFun hID hφ hgen f (x q) (φx q) (hφx q) m
end GroundTheory.Global.Artin
