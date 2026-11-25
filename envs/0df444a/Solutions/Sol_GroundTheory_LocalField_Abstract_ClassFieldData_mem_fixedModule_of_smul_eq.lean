-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.mem_fixedModule_of_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:32.923799+00:00
-- url     : https://prove2.me/submissions/12a324dd-0279-43dd-9d85-35449aa6d4e9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_relDeg_pow
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution [IsDiscreteModule G A] (K : OpenSubgroup G) {φ : G}
    (hφK : φ ∈ (K : Subgroup G)) (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    {w : A} (hw : w ∈ fixedModule A ((K : Subgroup G) ⊓ D.deg.ker)) (hφw : φ • w = w) :
    w ∈ fixedModule A (K : Subgroup G) := by
  let S : OpenSubgroup G := ⟨MulAction.stabilizer G w, IsDiscreteModule.isOpen_stabilizer w⟩
  let M : OpenSubgroup G := S ⊓ K
  have hMK : M ≤ K := inf_le_right
  have hu : (K : Subgroup G) ⊓ D.deg.ker ≤ M := fun g hg => ⟨hw g hg, hg.1⟩
  have hrel : D.relDeg K ⟨φ, hφK⟩ = Multiplicative.ofAdd 1 := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [D.relDeg_pow, ← ofAdd_nsmul, nsmul_one]
    exact hdφ
  intro τ hτ
  obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hMK hu hrel ⟨τ, hτ⟩
  have h1 : ∀ j : ℕ, (φ ^ j) • w = w := by
    intro j
    induction j with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hφw, ih]
  have h2 : ((φ ^ m)⁻¹ * τ) • w = w := by
    have h3 : (φ ^ m)⁻¹ * τ ∈ S := by simpa using hm.1
    exact MulAction.mem_stabilizer_iff.1 h3
  calc τ • w = (φ ^ m * ((φ ^ m)⁻¹ * τ)) • w := by group
    _ = w := by rw [mul_smul, h2, h1]
end GroundTheory.LocalField.Abstract.ClassFieldData
