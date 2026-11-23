-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.exists_partner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:32.704086+00:00
-- url     : https://prove2.me/submissions/4f31fd1d-ac7a-48c3-a2cb-618c4e844d0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_equivalence
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
namespace GlobalTheory.Ex.RecPeriods
theorem _root_.solution {e : N.X ≃+ N'.X} (hB : μ.B e) (j k : ℕ) (hk : k = n ^ j) (p : N.QT k) :
    ∃ p', μ.r k p p' ∧ p'.1.1.toAdd = e p.1.1.toAdd := by
  subst hk
  obtain ⟨p', h⟩ := μ.tot j p
  obtain ⟨z, hz⟩ := hB j p p' h
  refine ⟨p' * N'.qTriv _ (-z), (μ.eqv _ p p p' _ h ((N.qEq_equivalence _).refl p)).2
    ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩), ?_⟩
  change p'.1.1.toAdd + n ^ j • (-z) = _
  rw [hz, smul_neg, add_neg_cancel_right]
end GlobalTheory.Ex.RecPeriods
