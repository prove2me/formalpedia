-- Prove2me | solution 1 for Module.ker_baseChange_field_of_subsingleton_H1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/43bf1da5-04d0-5de6-a7b0-186c915f418e

import Mathlib
import Theorems.Thm_Module_exists_mumfordTruncation_of_flat_complex
import Theorems.Thm_Module_ker_baseChange_field_of_subsingleton_H1_of_projective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_ker_baseChange_field_of_subsingleton_H1
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

universe u

open TensorProduct

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (K : Type u) [Field K] [Algebra R K]
    (hH1 : LinearMap.ker ((d 1).baseChange K) ≤ LinearMap.range ((d 0).baseChange K)) :
    LinearMap.range ((LinearMap.ker (d 0)).subtype.baseChange K) = LinearMap.ker ((d 0).baseChange K) ∧
      Function.Injective ((LinearMap.ker (d 0)).subtype.baseChange K) := by
  obtain ⟨m₀, m₁, P, ε, -, -, hεδ, hA⟩ :=
    Module.exists_mumfordTruncation_of_flat_complex R C d hdd n hbdd hfin0 hfin
  obtain ⟨h1, h2, h3⟩ := hA K
  have hT2 := Module.ker_baseChange_field_of_subsingleton_H1_of_projective R
    (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype) ε hεδ K (h1 hH1)
  exact ⟨h2 hT2.1, h3 hT2.2⟩

end S_Module_ker_baseChange_field_of_subsingleton_H1
end P2MW
export P2MW.S_Module_ker_baseChange_field_of_subsingleton_H1 (solution)
