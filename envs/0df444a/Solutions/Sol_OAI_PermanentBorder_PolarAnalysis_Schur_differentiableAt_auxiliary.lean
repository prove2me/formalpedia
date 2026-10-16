-- Prove2me | solution 1 for OAI.PermanentBorder.PolarAnalysis.Schur.differentiableAt_auxiliary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:48:13.262854+00:00
-- url     : https://prove2.me/submissions/464738d7-713f-4c07-a14e-fb4bdc40d9a8

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SchurDifferentials.lean:L174-L197
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.PolarAnalysis.Schur.differentiableAt_auxiliary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials

-- ---- from OAI.Algebra.Determinantal.SchurDifferentials ----
namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [DecidableEq ι] in
 theorem differentiableAt_auxiliary {β γ : V → ι → ℂ} {E : V → Matrix ι ι ℂ}
    {x : V} {w : (ι → ℂ) × (ι → ℂ)}
    (hβ : ∀ i, DifferentiableAt ℂ (fun y => β y i) x)
    (hγ : ∀ i, DifferentiableAt ℂ (fun y => γ y i) x)
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    DifferentiableAt ℂ (auxiliary β γ E) (x,w) := by
  apply DifferentiableAt.prodMk
  · apply differentiableAt_pi.mpr
    intro i
    change DifferentiableAt ℂ (fun z => γ z.1 i + ∑ j, E z.1 i j * z.2.1 j) (x,w)
    apply DifferentiableAt.add ((hγ i).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    apply DifferentiableAt.fun_sum
    intro j _
    apply DifferentiableAt.mul ((hE i j).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    fun_prop
  · apply differentiableAt_pi.mpr
    intro j
    change DifferentiableAt ℂ (fun z => β z.1 j + ∑ i, z.2.2 i * E z.1 i j) (x,w)
    apply DifferentiableAt.add ((hβ j).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.mul _ ((hE i j).comp (x,w) (ContinuousLinearMap.fst ℂ V ((ι → ℂ) × (ι → ℂ))).differentiableAt)
    fun_prop

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
section Multiplier
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

end Multiplier
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {κ : Type*} [Fintype κ]

end PermanentBorder.PolarAnalysis

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis OAI.PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.PolarAnalysis.Schur.differentiableAt_auxiliary := @_root_.OAI.PermanentBorder.PolarAnalysis.Schur.differentiableAt_auxiliary
