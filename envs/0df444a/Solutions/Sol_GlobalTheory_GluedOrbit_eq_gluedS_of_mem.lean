-- Prove2me | solution 1 for GlobalTheory.GluedOrbit.eq_gluedS_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:47.348447+00:00
-- url     : https://prove2.me/submissions/eb7c75f2-facd-4961-9534-4b38a8ecb592

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiesOnRamOfInvariant
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmulGluedLatticeFirstPositionCases
import Theorems.Thm_GlobalTheory_LevelUnfold_mem_gluedS
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
noncomputable section
open GlobalTheory GlobalTheory.GluedOrbit
open GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration (interX)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
namespace GlobalTheory.GluedOrbit
theorem _root_.solution (q : Unif k) {M : Submodule 𝒪[k] (n ⊕ Fin 1 → k)}
    (hq : ∀ x ∈ M, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) {m : n ⊕ Fin 1 → k} (hm : m ∈ M)
    (hm1 : m (Sum.inr 0) = q.inv) : M = gluedS q 1 (interX M) (m ∘ Sum.inl) := by
  have hqi : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  ext y
  rw [GlobalTheory.LevelUnfold.mem_gluedS]
  constructor
  · intro hy
    refine ⟨⟨_, hq y hy⟩, ?_, fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    · have e : inX k n 1 (y ∘ Sum.inl - (⟨_, hq y hy⟩ : 𝒪[k]) • (m ∘ Sum.inl)) =
          y - (⟨_, hq y hy⟩ : 𝒪[k]) • m := by
        ext (j | j)
        · rfl
        · have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change (0 : k) = y (Sum.inr 0) - (q.1 : k) * y (Sum.inr 0) * m (Sum.inr 0)
          rw [hm1, mul_right_comm, hqi, one_mul, sub_self]
      change inX k n 1 _ ∈ M
      rw [e]
      exact sub_mem hy (M.smul_mem _ hm)
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      change y (Sum.inr 0) = q.inv * ((q.1 : k) * y (Sum.inr 0))
      rw [← mul_assoc, mul_comm q.inv, hqi, one_mul]
  · rintro ⟨s, hs, h⟩
    have e : y = inX k n 1 (y ∘ Sum.inl - s • (m ∘ Sum.inl)) + s • m := by
      ext (j | j)
      · change y (Sum.inl j) = (y (Sum.inl j) - (s : k) * m (Sum.inl j)) + (s : k) * m (Sum.inl j)
        ring
      · have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        change y (Sum.inr 0) = 0 + (s : k) * m (Sum.inr 0)
        rw [(h 0).1 rfl, hm1, zero_add, mul_comm]
    rw [e]
    exact add_mem hs (M.smul_mem _ hm)
end GlobalTheory.GluedOrbit
