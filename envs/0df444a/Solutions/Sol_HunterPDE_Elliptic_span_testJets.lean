-- Prove2me | solution 1 for HunterPDE.Elliptic.span_testJets
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T21:15:40.33021+00:00
-- url     : https://prove2.me/submissions/05d25c5e-f87b-4f19-81b4-071ed510fb54

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Definitions.Def_HunterPDE_Elliptic_H10

open MeasureTheory
open scoped ContDiff
open HunterPDE.Elliptic

set_option autoImplicit false

theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    (↑(Submodule.span ℝ (testJets n Ω)) : Set (JetL2 n Ω)) = testJets n Ω := by
  let S : Submodule ℝ (JetL2 n Ω) :=
    { carrier := testJets n Ω
      zero_mem' := by
        refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_, ?_⟩
        · simp
        · filter_upwards [Lp.coeFn_zero (E := Jet n) (p := 2) (μ := volume.restrict Ω)] with x hx
          rw [hx]
          apply WithLp.ofLp_injective 2
          simp [gradient]
          rfl
      add_mem' := by
        rintro F G ⟨f, hf, hfc, hfs, hF⟩ ⟨g, hg, hgc, hgs, hG⟩
        refine ⟨f + g, hf.add hg, hfc.add hgc, ?_, ?_⟩
        · exact (tsupport_add f g).trans (Set.union_subset hfs hgs)
        · filter_upwards [Lp.coeFn_add F G, hF, hG] with x hx hfx hgx
          rw [hx]
          change F x + G x = _
          rw [hfx, hgx]
          apply WithLp.ofLp_injective 2
          simp only [WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply, Prod.mk_add_mk]
          congr 1
          simp [gradient, fderiv_add (hf.differentiable (by simp) x)
            (hg.differentiable (by simp) x)]
      smul_mem' := by
        rintro c F ⟨f, hf, hfc, hfs, hF⟩
        refine ⟨c • f, hf.const_smul c, hfc.smul_left, ?_, ?_⟩
        · exact (tsupport_smul_subset_right (fun _ => c) f).trans hfs
        · filter_upwards [Lp.coeFn_smul c F, hF] with x hx hfx
          rw [hx]
          change c • F x = _
          rw [hfx]
          apply WithLp.ofLp_injective
          simp only [WithLp.ofLp_smul, WithLp.ofLp_toLp, Pi.smul_apply, Prod.smul_mk]
          congr 1
          simp [gradient, fderiv_const_smul (hf.differentiable (by simp) x)] }
  apply Set.Subset.antisymm
  · exact Submodule.span_le.mpr (show testJets n Ω ⊆ S from fun _ h => h)
  · exact Submodule.subset_span
