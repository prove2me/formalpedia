-- Prove2me | solution 1 for GlobalTheory.MatchTerm.eq_of_qeq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:08:36.925034+00:00
-- url     : https://prove2.me/submissions/d4733381-13b3-46d6-807b-4cfaffad5788

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_TorsionFourier_add_nsmul_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
namespace GlobalTheory.MatchTerm
theorem _root_.solution {N : NumD C} {k : ℕ} (hk : k ≠ 0) {p q : N.QT k} (h : N.QEq p q) (e : p.1.1 = q.1.1) : p = q := by
  obtain ⟨z, h1, h2⟩ := h
  rw [e, left_eq_add] at h1
  have hz : z = 0 := by
    have := TorsionFourier.add_nsmul_injective (Nat.pos_of_ne_zero hk) (0 : N.X) (a₁ := z) (a₂ := 0) (by simpa using h1)
    exact this
  rw [hz, N.io_zero, mul_one] at h2
  exact Subtype.ext (Prod.ext e h2.symm)
end GlobalTheory.MatchTerm
