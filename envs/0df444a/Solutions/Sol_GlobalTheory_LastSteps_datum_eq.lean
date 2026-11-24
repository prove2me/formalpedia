-- Prove2me | solution 1 for GlobalTheory.LastSteps.datum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:36:25.864628+00:00
-- url     : https://prove2.me/submissions/edd2f2aa-92b9-4d94-8c1d-498162f91067

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
variable [Fintype n']
namespace GlobalTheory.LastSteps
theorem _root_.solution (q : Unif k) (P : Pair k n') (LY : Submodule 𝒪[k] (n → k)) (x₀ : Matrix n n' k) (y : n → k) :
    datum q P LY x₀ y = latInd (gluedS q 1 P.ker P.vec) LY (withCol x₀ y) := by
  classical
  have hm : ∀ v : n' ⊕ Fin 1 → k, withCol x₀ y *ᵥ v = x₀ *ᵥ (v ∘ Sum.inl) + v (Sum.inr 0) • y := fun v => by
    ext i
    simp [withCol, mulVec, dotProduct, mul_comm]
  refine if_congr ?_ rfl rfl
  simp only [← gluedLat_one, mem_gluedLat, hm, Fin.forall_fin_one]
  constructor
  · rintro ⟨h, h'⟩ v ⟨s, hs, -, hv, -⟩
    have := add_mem (h _ hs) (LY.smul_mem s h')
    convert this using 1
    rw [hv rfl, mulVec_sub, mulVec_smul, smul_add, mul_comm, mul_smul]
    abel
  · intro h
    refine ⟨fun z hz => ?_, ?_⟩
    · simpa using h (Sum.elim z 0) ⟨0, by simpa using hz, by simp⟩
    · simpa [add_comm] using h (Sum.elim P.vec fun _ => q.inv) ⟨1, by simp, by simp⟩
end GlobalTheory.LastSteps
