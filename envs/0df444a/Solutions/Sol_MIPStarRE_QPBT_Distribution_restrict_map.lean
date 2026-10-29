-- Prove2me | solution 1 for MIPStarRE.QPBT.Distribution.restrict_map
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:34:37.243084+00:00
-- url     : https://prove2.me/submissions/4a743910-d915-4d8e-a06a-b5c6d7c1d26c

-- Generated proof for MIPStarRE.QPBT.Distribution.restrict_map.
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



/-! ## Push-forward of the second factor of a product -/



/-! ## Uniform laws on products -/





/-! ## Conditioning one factor of a product -/







/-! ## Conditioning the first factor of a product -/







/-! ## Restriction of a push-forward -/

theorem solution {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution α) (f : α → β) (p : β → Prop) [DecidablePred p]
    (q : α → Prop) [DecidablePred q] (hq : ∀ a, q a ↔ p (f a))
    (hpos : 0 < ∑ b ∈ (μ.map f).support.filter p, (μ.map f).weight b)
    (hpos' : 0 < ∑ a ∈ μ.support.filter q, μ.weight a) :
    _root_.MIPStarRE.QPBT.Distribution.restrict (μ.map f) p hpos =
      (_root_.MIPStarRE.QPBT.Distribution.restrict μ q hpos').map f := by
  classical
  have hfiber : ∀ b : β, p b →
      μ.support.filter (fun a => f a = b) =
        (μ.support.filter q).filter (fun a => f a = b) := by
    intro b hb
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hab⟩
      exact ⟨⟨ha, (hq a).mpr (hab ▸ hb)⟩, hab⟩
    · rintro ⟨⟨ha, -⟩, hab⟩
      exact ⟨ha, hab⟩
  have himg : (μ.map f).support.filter p = (μ.support.filter q).image f := by
    ext b
    simp only [_root_.LIDT.MIPStarRE.LDT.Distribution.map_support, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hpb⟩
      exact ⟨a, ⟨ha, (hq a).mpr hpb⟩, rfl⟩
    · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
      exact ⟨⟨a, ha1, rfl⟩, (hq a).mp ha2⟩
  have hmass : (∑ b ∈ (μ.map f).support.filter p, (μ.map f).weight b) =
      ∑ a ∈ μ.support.filter q, μ.weight a := by
    rw [himg]
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := μ.support.filter q) (t := (μ.support.filter q).image f)
      (g := f) (fun a ha => Finset.mem_image_of_mem f ha) μ.weight]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp hb
    rw [_root_.LIDT.MIPStarRE.LDT.Distribution.map_weight,
      hfiber _ ((hq a0).mp (Finset.mem_filter.mp ha0).2)]
  refine _root_.MIPStarRE.QPBT.Distribution.ext_of_support_of_weight ?_ ?_
  · exact himg
  · funext b
    show (if p b then (μ.map f).weight b /
        ∑ c ∈ (μ.map f).support.filter p, (μ.map f).weight c else 0) =
      ∑ a ∈ (μ.support.filter q).filter (fun a => f a = b),
        (if q a then μ.weight a / ∑ c ∈ μ.support.filter q, μ.weight c else 0)
    by_cases hb : p b
    · rw [if_pos hb, hmass, _root_.LIDT.MIPStarRE.LDT.Distribution.map_weight, hfiber b hb,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_pos (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2]
    · rw [if_neg hb]
      refine (Finset.sum_eq_zero fun a ha => ?_).symm
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact absurd (ha2 ▸ (hq a).mp (Finset.mem_filter.mp ha1).2) hb
