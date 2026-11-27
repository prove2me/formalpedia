-- Prove2me | solution 1 for GlobalTheory.UnitLemma.herm_basis_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:03.762665+00:00
-- url     : https://prove2.me/submissions/e94456a0-b5df-44a5-8076-5c8fb36aa92f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermBasisOrthonormal
import Theorems.Thm_GlobalTheory_UnitLemma_OrthBasis_herm_add_right
import Theorems.Thm_GlobalTheory_UnitLemma_OrthBasis_herm_zero_right
import Theorems.Thm_P2M_GlobalTheory_UnitLemma_OrthBasis_herm_smul_right__c57101fb1dc8
import Theorems.Thm_GlobalTheory_UnitLemma_OrthBasis_herm_sum_smul_left
import Theorems.Thm_GlobalTheory_UnitLemma_OrthBasis_herm_mul_left_of_fixed
import Theorems.Thm_GlobalTheory_UnitLemma_OrthBasis_repr_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open GlobalTheory.UnitLemma.OrthBasis
namespace GlobalTheory.UnitLemma
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (x w : B.A), B.σ B.g = B.g → IsUnit w →
    Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l) = ⊤ → ∀ (n : ℕ) (e : Module.Basis (Fin n) K.E B.A),
    (∀ i j, K.c (e.repr (B.g * e j) i) = e.repr (B.g * e i) j) → (∀ j, B.herm x (e j) w = K.c (e.repr w j)) →
    ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0 := by
  intro K B x w hg hw hspan n e hM hwj

  let P : B.A → Prop := fun z => ∀ i, B.herm x (e i) z = K.c (e.repr z i)
  have hstep : ∀ z, P z → P (B.g * z) := by
    intro z hz i
    rw [← herm_mul_left_of_fixed B x B.g (e i) z hg]
    conv_lhs => rw [← e.sum_repr (B.g * e i)]
    rw [herm_sum_smul_left, repr_mul, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz j, RingEquiv.map_mul K.c, hM, mul_comm]
  have hpow : ∀ l : ℕ, P (B.g ^ l * w) := by
    intro l
    induction l with
    | zero => simpa [P] using hwj
    | succ l ih => rw [pow_succ', mul_assoc]; exact hstep _ ih
  have hspanP : ∀ a ∈ Submodule.span K.E (Set.range fun l : ℕ => B.g ^ l), P (a * w) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy => obtain ⟨l, rfl⟩ := hy; exact hpow l
    | zero => intro i; simp [herm_zero_right]
    | add y z _ _ hy hz =>
      intro i; rw [add_mul, herm_add_right, hy i, hz i, map_add, Finsupp.add_apply, map_add]
    | smul a y _ hy =>
      intro i; rw [smul_mul_assoc, herm_smul_right', hy i, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul,
        RingEquiv.map_mul K.c]
  have hall : ∀ z, P z := by
    intro z
    obtain ⟨u, rfl⟩ := hw
    have := hspanP (z * ((u⁻¹ : B.Aˣ) : B.A)) (by rw [hspan]; exact Submodule.mem_top)
    rwa [mul_assoc, Units.inv_mul, mul_one] at this
  intro i j
  rw [hall (e j) i, e.repr_self, Finsupp.single_apply]
  split_ifs with h1 h2 h2
  · exact map_one _
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · exact map_zero _
end GlobalTheory.UnitLemma
