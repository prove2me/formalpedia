-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothProjectiveVariety.regularLattice_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:12:05.303982+00:00
-- url     : https://prove2.me/submissions/dd27667b-f686-4018-9a25-3adce7762174

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/LogLattice.lean:L136-L157
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.SmoothProjectiveVariety.regularLattice_restriction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange

-- ---- from OAI.AlgebraicGeometry.LogKodaira.LogLattice ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section
namespace ReverseLogKodaira.LocalizationLattice

 

end ReverseLogKodaira.LocalizationLattice

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

lemma regularLattice_restriction (X : SmoothProjectiveVariety)
    (U V : X.scheme.affineOpens) [Nonempty U.1] [Nonempty V.1] (hUV : U.1 ≤ V.1)
    (m : ℕ) {s : X.RationalPluriform m} (hs : s ∈ X.regularPluriformLattice V m) :
    s ∈ X.regularPluriformLattice U m := by
  let res := (X.scheme.presheaf.map (homOfLE hUV).op).hom
  have hres (a : Γ(X.scheme, V.1)) :
      algebraMap Γ(X.scheme, U.1) X.scheme.functionField (res a) =
        algebraMap Γ(X.scheme, V.1) X.scheme.functionField a :=
    X.scheme.presheaf.germ_res_apply (homOfLE hUV) (genericPoint X.scheme) _ a
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun j i => res (a j i), ?_⟩
    simp only [hres]
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    have h := (X.regularPluriformLattice U m).smul_mem (res a) ih
    rw [← IsScalarTower.algebraMap_smul X.scheme.functionField (res a),
      hres, IsScalarTower.algebraMap_smul] at h
    exact h

 
end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary

 

end ReverseLogKodaira.SmoothProjectiveVariety.ReducedSNCBoundary

end
end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution (X : SmoothProjectiveVariety)
    (U V : X.scheme.affineOpens) [Nonempty U.1] [Nonempty V.1] (hUV : U.1 ≤ V.1)
    (m : ℕ) {s : X.RationalPluriform m} (hs : s ∈ X.regularPluriformLattice V m) :
    s ∈ X.regularPluriformLattice U m := by
  first
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.regularLattice_restriction X U V hUV m hs
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.regularLattice_restriction
    | (apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.regularLattice_restriction <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.regularLattice_restriction <;> assumption)
