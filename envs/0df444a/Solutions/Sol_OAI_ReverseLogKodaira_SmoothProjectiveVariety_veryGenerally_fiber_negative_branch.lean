-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:27:50.312549+00:00
-- url     : https://prove2.me/submissions/8ba4bac4-97ea-4648-b01f-d69ed1c5ec97

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/FiberNegative.lean:L53-L74
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_veryGenerally_fiber_negative_branch) verbatim and is proved by it.
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
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_GlobalSpecialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_NonzeroFiber
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_ReducedSNCBoundary_kodaira_eq_bot_iff
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_exists_open_nonzero_fiber_pluriform

-- ---- from OAI.AlgebraicGeometry.LogKodaira.NonzeroFiber ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.CanonicalSpecialization
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

 

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.RelativeCharts

 

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

lemma ReducedSNCBoundary.generic_mem_complement {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) : genericPoint X.scheme ∈ E.complement := by
  change genericPoint X.scheme ∉ E.ideal.support
  intro hg
  have hbot : E.ideal = ⊥ := by
    apply Scheme.IdealSheafData.support_eq_top_iff.mp
    apply eq_top_iff.mpr
    intro z hz
    have hs := closure_minimal (Set.singleton_subset_iff.mpr hg) E.ideal.support.isClosed
    rw [genericPoint_closure] at hs
    exact hs (Set.mem_univ z)
  obtain ⟨V, _, t, ht, hI⟩ := E.union_cartier (genericPoint X.scheme)
  change E.ideal.ideal V = Ideal.span {t} at hI
  rw [hbot] at hI
  change (⊥ : Ideal Γ(X.scheme, V.1)) = Ideal.span {t} at hI
  apply ht
  have hm : t ∈ (⊥ : Ideal Γ(X.scheme, V.1)) := by
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton t)
  exact hm

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.DifferentialBaseChange

end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety
open DifferentialBaseChange CanonicalSpecialization FiberChartSpecialization

 

end ReverseLogKodaira.SmoothProjectiveVariety

end

end OAI

-- ---- from OAI.AlgebraicGeometry.LogKodaira.FiberNegative ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

lemma veryGenerally_of_nonempty_open
    {Y : SmoothProjectiveVariety} {P : Y.ComplexPoint → Prop}
    {U : Y.scheme.Opens} (hne : U ≠ ⊥)
    (hP : ∀ y : Y.ComplexPoint, y.point ∈ U → P y) : VeryGenerally Y P := by
  classical
  refine ⟨fun _ => U.compl, fun _ => ?_, ?_⟩
  · intro htop
    change U.compl = ⊤ at htop
    apply hne
    apply le_bot_iff.mp
    intro x hx
    have hc : x ∈ U.compl := by rw [htop]; trivial
    exact (hc hx).elim
  · intro y hy
    apply hP y
    exact Classical.not_not.mp (hy 0)

 

theorem exists_open_fiber_kodaira_ne_bot
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (hE : E.kodaira ≠ ⊥) :
    ∃ U : Y.scheme.Opens, U ≠ ⊥ ∧ U ≤ D.complement ∧
      ∀ (y : Y.ComplexPoint), y.point ∈ U →
        ∀ F : FiberModel f.toBoundaryFibration y, F.boundary.kodaira ≠ ⊥ := by
  classical
  have hs : ∃ (m : ℕ), 0 < m ∧ ∃ s : X.RationalPluriform m,
      s ∈ E.sections m ∧ s ≠ 0 := by
    by_contra! h
    exact hE (E.kodaira_eq_bot_iff.mpr h)
  obtain ⟨m, hm, s, hs, hn⟩ := hs
  obtain ⟨U, hne, hU, hf⟩ := exists_open_nonzero_fiber_pluriform f m hm s hs hn
  refine ⟨U, hne, hU, ?_⟩
  intro y hy F hF
  obtain ⟨σ, hσ, hnσ⟩ := hf y hy F
  exact hnσ (F.boundary.kodaira_eq_bot_iff.mp hF m hm σ hσ)

 

theorem veryGenerally_fiber_negative_branch
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) :
    VeryGenerally Y fun y => y.point ∈ D.complement ∧
      ∀ F : FiberModel f.toBoundaryFibration y, F.boundary.kodaira = ⊥ →
        E.kodaira = D.kodaira + F.boundary.kodaira ∧
        ∀ (m : ℕ), 0 < m → ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0 := by
  classical
  by_cases hE : E.kodaira = ⊥
  · have hne : D.complement ≠ ⊥ := by
      intro hD
      have hg := D.generic_mem_complement
      rw [hD] at hg
      exact hg
    apply veryGenerally_of_nonempty_open hne
    intro y hy
    refine ⟨hy, fun F hF => ⟨?_, E.kodaira_eq_bot_iff.mp hE⟩⟩
    simpa only [hF, WithBot.add_bot] using hE
  · obtain ⟨U, hne, hU, hf⟩ := exists_open_fiber_kodaira_ne_bot f hE
    apply veryGenerally_of_nonempty_open hne
    intro y hy
    exact ⟨hU hy, fun F hF => ((hf y hy F) hF).elim⟩

end ReverseLogKodaira.SmoothProjectiveVariety

end

end OAI

-- ---- mission target ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) :
    VeryGenerally Y fun y => y.point ∈ D.complement ∧
      ∀ F : FiberModel f.toBoundaryFibration y, F.boundary.kodaira = ⊥ →
        E.kodaira = D.kodaira + F.boundary.kodaira ∧
        ∀ (m : ℕ), 0 < m → ∀ s : X.RationalPluriform m, s ∈ E.sections m → s = 0 := by
  first
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch f
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch
    | (apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.veryGenerally_fiber_negative_branch <;> assumption)
