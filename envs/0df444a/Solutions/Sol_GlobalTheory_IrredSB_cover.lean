-- Prove2me | solution 1 for GlobalTheory.IrredSB.cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:48.812199+00:00
-- url     : https://prove2.me/submissions/2eed3241-dc43-411d-bb40-fcb131c0fe8e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Theorems.Thm_GlobalTheory_matrix_integers_mod_nat_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [Fintype Y']
namespace GlobalTheory.IrredSB
theorem _root_.solution [CharZero k] {a N : ℕ} (ha : 0 < a) (hN : 0 < N) :
    ∃ P : Finset (Matrix Y Y' k), ∀ t : Matrix Y Y' k, (∀ r q, (a • t) r q ∈ 𝒪[k]) →
      ∃ p ∈ P, ∃ u ∈ lat k Y Y' N, t = p + u := by
  classical
  obtain ⟨R, hR, hRc⟩ := GlobalTheory.matrix_integers_mod_nat_finite k Y Y' (a * N) (Nat.mul_pos ha hN)
  refine ⟨(hR.image fun s => ((a : k)⁻¹) • s).toFinset, fun t ht => ?_⟩
  obtain ⟨s, hs, u, hu, he⟩ := hRc _ ht
  have ha' : (a : k) ≠ 0 := by exact_mod_cast ha.ne'
  have hinv : ∀ v : Matrix Y Y' k, (a : k)⁻¹ • (a • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ ha', one_smul]
  refine ⟨(a : k)⁻¹ • s, (Set.Finite.mem_toFinset _).2 ⟨s, hs, rfl⟩, N • u, ⟨u, hu, rfl⟩, ?_⟩
  rw [← hinv t, he, smul_add, mul_smul, hinv]
end GlobalTheory.IrredSB
