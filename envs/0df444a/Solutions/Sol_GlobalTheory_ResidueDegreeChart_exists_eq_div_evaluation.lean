-- Prove2me | solution 1 for GlobalTheory.ResidueDegreeChart.exists_eq_div_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:36.880716+00:00
-- url     : https://prove2.me/submissions/1eed5282-8c40-4e26-8f6c-abaa33af2326

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ResidueDegreeEqInertiaDegAffineChart
import Theorems.Thm_GlobalTheory_ResidueDegreeChart_mem_primeIdealOf_iff

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
    (hx : x ∈ U) (z : X.residueField x) :
    ∃ a b, z = (X.evaluation U x hx).hom a / (X.evaluation U x hx).hom b := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  obtain ⟨t, rfl⟩ := X.residue_surjective x z
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk x) t
  refine ⟨a, b, ?_⟩
  have hb : (X.evaluation U x hx).hom b ≠ 0 := fun h0 =>
    b.2 ((mem_primeIdealOf_iff hU x hx b).2 h0)
  rw [eq_div_iff hb]
  have := congrArg (X.residue x).hom h
  rw [map_mul] at this
  exact this
end GlobalTheory.ResidueDegreeChart
