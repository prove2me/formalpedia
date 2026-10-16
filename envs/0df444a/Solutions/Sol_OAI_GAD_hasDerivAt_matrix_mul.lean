-- Prove2me | solution 1 for OAI.GAD.hasDerivAt_matrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:13:16.701421+00:00
-- url     : https://prove2.me/submissions/be8f9c7b-74a0-4123-ad23-2cdbb4620ae1

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean:L46-L62
-- (upload_full_project.md Phase 4): solution for node OAI.GAD.hasDerivAt_matrix_mul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

-- ---- from OAI.InformationTheory.AmplitudeDamping.MatrixDifferentiation ----
namespace OAI

universe u_1 u_2

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace GAD

variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Product differentiation with the entrywise matrix topology. -/
theorem hasDerivAt_matrix_mul {A B : ℝ → Matrix ι ι ℂ}
    {H K : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hB : HasDerivAt B K t) :
    HasDerivAt (fun s ↦ A s * B s) (H * B t + A t * K) t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hh := HasDerivAt.sum (u := Finset.univ) (fun k _ ↦
    ((hasDerivAt_pi.1 (hasDerivAt_pi.1 hA i) k).mul
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB k) j)))
  convert! hh using 1
  · ext s
    simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, Finset.sum_add_distrib]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI

-- ---- platform node ----
open OAI OAI.GAD
open scoped BigOperators
open Matrix


theorem solution : type_of% @_root_.OAI.GAD.hasDerivAt_matrix_mul := @_root_.OAI.GAD.hasDerivAt_matrix_mul
