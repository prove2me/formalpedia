-- Prove2me | solution 1 for MIPStarRE.QPBT.uniformDistribution_map_lineRepMap_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:55:47.219138+00:00
-- url     : https://prove2.me/submissions/d1cdea94-08b2-4a05-9930-c5a38283fe06

-- Generated proof for MIPStarRE.QPBT.uniformDistribution_map_lineRepMap_add_smul.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Questions
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/- Source helpers from QPBT/Combining/Lines/SubLineUniform.lean. -/
/-!
# Uniform points of a line and the blocks of a coordinate direction

This module records the two elementary geometric inputs of the sampling
procedure of the sub-line lemma. First, for independent uniform inputs `u` in
the ambient coordinate space and `t` in the scalar field, the point
`lineRepMap v u + t • v` is uniform. This map on ambient-point--parameter pairs
has fibers of size `q`: for nonzero `v`, `u` varies over a coset of the span of
`v`, while its canonical representative and `t` are fixed; for zero `v`, `u`
is fixed and `t` is free. In averaged form this is the resampling identity used
by the line-point samplers: a quantity of the canonical representative and of
the point may equivalently be averaged over the point and an independent
uniform affine parameter along the direction. Second, the two coordinate
blocks of an elementary coordinate direction of the extended space are the
corresponding elementary direction of the source space in the block that
carries the coordinate, and zero in the other block and at the two scalar
coordinates.

## References

The two statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The canonical representative map is blueprint
`def:line-representative`; the coordinate blocks are those of
blueprint `def:combine-map`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

noncomputable section

/-! ## The canonical representative for the zero direction -/

/-- For the zero direction the canonical representative map of
`def:line-representative` is the identity, since the span of the zero vector
is trivial.  Blueprint `def:line-representative`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:143-174`.
-/
theorem lineRepMap_zero_apply {K : Type*} [Field K] {m : ℕ}
    (u : Fin m → K) : _root_.MIPStarRE.QPBT.lineRepMap (0 : Fin m → K) u = u := by
  have hspan : Submodule.span K ({0} : Set (Fin m → K)) = ⊥ := by simp
  have h := _root_.MIPStarRE.QPBT.sub_lineRepMap_mem_span (0 : Fin m → K) u
  rw [hspan, Submodule.mem_bot, sub_eq_zero] at h
  exact h.symm

/-! ## Uniform points of a line -/



/-! ## Resampling a uniform point along its canonical line -/



/-! ## Injectivity of the two block embeddings -/





/-! ## The blocks of an elementary coordinate direction -/

















/-! ## The coordinates occupied by the two blocks -/









/-! ## The blocks of a point of an extended line -/







/-! ## Incidence of the blocks of an extended line -/







end

end MIPStarRE.QPBT

/-!
# Uniform points of a line and the blocks of a coordinate direction

This module records the two elementary geometric inputs of the sampling
procedure of the sub-line lemma. First, for independent uniform inputs `u` in
the ambient coordinate space and `t` in the scalar field, the point
`lineRepMap v u + t • v` is uniform. This map on ambient-point--parameter pairs
has fibers of size `q`: for nonzero `v`, `u` varies over a coset of the span of
`v`, while its canonical representative and `t` are fixed; for zero `v`, `u`
is fixed and `t` is free. In averaged form this is the resampling identity used
by the line-point samplers: a quantity of the canonical representative and of
the point may equivalently be averaged over the point and an independent
uniform affine parameter along the direction. Second, the two coordinate
blocks of an elementary coordinate direction of the extended space are the
corresponding elementary direction of the source space in the block that
carries the coordinate, and zero in the other block and at the two scalar
coordinates.

## References

The two statements support `lem:qld-sublines` in
blueprint `lem:qld-sublines`, whose source is
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`.
The canonical representative map is blueprint
`def:line-representative`; the coordinate blocks are those of
blueprint `def:combine-map`.
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT



/-! ## The canonical representative for the zero direction -/



/-! ## Uniform points of a line -/

theorem solution {K : Type*} [Field K]
    [Fintype K] [DecidableEq K] {m : ℕ} (v : Fin m → K) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((Fin m → K) × K)).map
        (fun w => _root_.MIPStarRE.QPBT.lineRepMap v w.1 + w.2 • v) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin m → K) := by
  refine _root_.MIPStarRE.QPBT.uniformDistribution_map_of_card_fiber _ (Fintype.card K) fun x => ?_
  by_cases hv : v = 0
  · subst hv
    have hfilter :
        ((Finset.univ : Finset ((Fin m → K) × K)).filter
            fun w => _root_.MIPStarRE.QPBT.lineRepMap (0 : Fin m → K) w.1 + w.2 • (0 : Fin m → K)
              = x)
          = ({x} : Finset (Fin m → K)) ×ˢ (Finset.univ : Finset K) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton, and_true, smul_zero,
        add_zero, _root_.MIPStarRE.QPBT.lineRepMap_zero_apply]
    rw [hfilter, Finset.card_product]
    simp
  · have hinj : Function.Injective
        (fun c : K => (_root_.MIPStarRE.QPBT.lineRepMap v x + c • v, _root_.MIPStarRE.QPBT.directLineRepParameter v x)) := by
      intro c₁ c₂ hc
      have hc' : c₁ • v = c₂ • v := by
        have h := congrArg Prod.fst hc
        simpa using h
      have hsub : (c₁ - c₂) • v = 0 := by
        rw [sub_smul, hc', sub_self]
      rcases smul_eq_zero.mp hsub with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv
    have himg :
        ((Finset.univ : Finset ((Fin m → K) × K)).filter
            fun w => _root_.MIPStarRE.QPBT.lineRepMap v w.1 + w.2 • v = x)
          = (Finset.univ : Finset K).image
              (fun c => (_root_.MIPStarRE.QPBT.lineRepMap v x + c • v,
                _root_.MIPStarRE.QPBT.directLineRepParameter v x)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hw
        have hrep : _root_.MIPStarRE.QPBT.lineRepMap v w.1 = _root_.MIPStarRE.QPBT.lineRepMap v x := by
          rw [← hw, _root_.MIPStarRE.QPBT.lineRepMap_add_smul, _root_.MIPStarRE.QPBT.lineRepMap_apply_self]
        have hx : x = _root_.MIPStarRE.QPBT.lineRepMap v x + w.2 • v := by
          rw [← hrep]
          exact hw.symm
        have ht : _root_.MIPStarRE.QPBT.directLineRepParameter v x = w.2 :=
          _root_.MIPStarRE.QPBT.directLineRepParameter_eq_of_nonzero hv hx
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
          (_root_.MIPStarRE.QPBT.sub_lineRepMap_mem_span v w.1)
        refine ⟨c, ?_⟩
        have hw1 : _root_.MIPStarRE.QPBT.lineRepMap v x + c • v = w.1 := by
          rw [← hrep, hc]
          abel
        rw [Prod.ext_iff]
        exact ⟨hw1, ht⟩
      · rintro ⟨c, rfl⟩
        show _root_.MIPStarRE.QPBT.lineRepMap v (_root_.MIPStarRE.QPBT.lineRepMap v x + c • v) +
          _root_.MIPStarRE.QPBT.directLineRepParameter v x • v = x
        rw [_root_.MIPStarRE.QPBT.lineRepMap_add_smul, _root_.MIPStarRE.QPBT.lineRepMap_apply_self]
        exact (_root_.MIPStarRE.QPBT.directLineRepParameter_spec v x).symm
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
