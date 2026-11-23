-- Prove2me | solution 1 for GlobalTheory.ResidueDegreeChart.mem_primeIdealOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:06.570779+00:00
-- url     : https://prove2.me/submissions/70232bbc-a410-48c6-ba95-06ad5c286a37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ResidueDegreeChart
namespace GlobalTheory.ResidueDegreeChart
theorem _root_.solution {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔ (X.evaluation U x hx).hom s = 0 := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal s, ← IsLocalRing.residue_eq_zero_iff]
  rfl
end GlobalTheory.ResidueDegreeChart
