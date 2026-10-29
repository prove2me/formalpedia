-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.map_bijective_eq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:23:53.92793+00:00
-- url     : https://prove2.me/submissions/09c15f5b-75af-4b92-8937-f4b10d8691ba

-- Generated proof for MIPStarRE.QPBT.Distribution.map_bijective_eq.
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
import Definitions.Def_QPBT_QPBT_Games_DistributionAux

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Products, marginals, and restrictions of finite distributions

The finite-distribution push-forward calculus gives corresponding identities
for probability mass functions and for projections transported across finite
equivalences.  These forms are used by the directly indexed low-degree
line-point laws and by the correspondence between the seed-indexed and directly
indexed question distributions. Products can be expressed as dependent mixtures, and
conditioning on an event of one factor preserves the independence of the other.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/



open scoped BigOperators

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT





/-! ## Nonemptiness of the support of a probability law -/



/-! ## Push-forward of one factor of a product -/



/-! ## The first marginal of a product -/





/-! ## A product as a dependent mixture -/



/-! ## The support and the weight of a product -/





/-! ## Push-forward along a bijection -/

theorem solution {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (ν : _root_.LIDT.MIPStarRE.LDT.Distribution β) (f : α → β)
    (g : β → α) (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b)
    (hs : ∀ a, a ∈ μ.support ↔ f a ∈ ν.support)
    (hw : ∀ a, μ.weight a = ν.weight (f a)) :
    μ.map f = ν := by
  classical
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · rw [_root_.LIDT.MIPStarRE.LDT.Distribution.map_support]
    ext b
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hs a).mp ha
    · intro hb
      refine ⟨g b, (hs (g b)).mpr ?_, hfg b⟩
      rw [hfg b]
      exact hb
  · funext b
    rw [_root_.LIDT.MIPStarRE.LDT.Distribution.map_weight]
    have hfilter : μ.support.filter (fun a => f a = b) =
        μ.support.filter (fun a => a = g b) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha, h⟩
        exact ⟨ha, by rw [← h, hgf]⟩
      · rintro ⟨ha, h⟩
        exact ⟨ha, by rw [h, hfg]⟩
    rw [hfilter, Finset.filter_eq' μ.support (g b)]
    by_cases hmem : g b ∈ μ.support
    · rw [if_pos hmem, Finset.sum_singleton, hw (g b), hfg]
    · rw [if_neg hmem, Finset.sum_empty]
      refine (ν.outsideSupport b ?_).symm
      intro hb
      exact hmem ((hs (g b)).mpr (by rw [hfg b]; exact hb))
