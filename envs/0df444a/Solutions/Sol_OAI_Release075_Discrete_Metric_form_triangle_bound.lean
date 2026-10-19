-- Prove2me | solution 1 for OAI.Release075.Discrete.Metric.form_triangle_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:59:41.542051+00:00
-- url     : https://prove2.me/submissions/39820623-83bc-467d-ac2f-1c0d65f3a6b4

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/DiscreteMetric.lean:L238-L260
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.Discrete.Metric.form_triangle_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_BasedWords
import Definitions.Def_OAI_GroupTheory_Hyperbolic_DiscreteMetric

-- ---- from OAI.GroupTheory.Hyperbolic.DiscreteMetric ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075.Discrete

variable {V : Type} (M : Metric V)

namespace Path
variable {M} {a b c : V}

end Path

namespace Metric
variable {M}

theorem int_dist_sub_le (x y z : V) : |(M.dist x y : ℤ)-M.dist x z| ≤ M.dist y z := by
  have h₁ := M.triangle x y z
  have h₂ := M.triangle x z y
  rw [M.symm z y] at h₂
  rw [abs_le]
  constructor <;> omega

theorem tent_lipschitz (o : V) (R : ℕ) (x y : V) :
    |M.tent o R x - M.tent o R y| ≤ M.dist x y := by
  have h := M.int_dist_sub_le o x y
  unfold tent
  rw [abs_le] at h ⊢
  omega

theorem form_triangle_bound (o a x y z : V) (R : ℕ)
    (hxy : M.dist x y ≤ 1) (_hyz : M.dist y z ≤ 1) (hzx : M.dist z x ≤ 1) :
    |M.form o a R x y+M.form o a R y z+M.form o a R z x| ≤ 2 := by
  have hF₁ : |M.tent o R y-M.tent o R x| ≤ 1 :=
    (M.tent_lipschitz o R y x).trans (by rw [M.symm y x]; exact_mod_cast hxy)
  have hF₂ : |M.tent o R z-M.tent o R x| ≤ 1 :=
    (M.tent_lipschitz o R z x).trans (by exact_mod_cast hzx)
  have hG₁ : |(M.dist a y:ℤ)-M.dist a x| ≤ 1 :=
    (M.int_dist_sub_le a y x).trans (by rw [M.symm y x]; exact_mod_cast hxy)
  have hG₂ : |(M.dist a z:ℤ)-M.dist a x| ≤ 1 :=
    (M.int_dist_sub_le a z x).trans (by exact_mod_cast hzx)
  have he : M.form o a R x y+M.form o a R y z+M.form o a R z x =
      (M.tent o R y-M.tent o R x)*((M.dist a z:ℤ)-M.dist a x) -
      (M.tent o R z-M.tent o R x)*((M.dist a y:ℤ)-M.dist a x) := by unfold form; ring
  rw [he]
  calc
    _ ≤ |(M.tent o R y-M.tent o R x)*((M.dist a z:ℤ)-M.dist a x)| +
        |(M.tent o R z-M.tent o R x)*((M.dist a y:ℤ)-M.dist a x)| := abs_sub _ _
    _ ≤ 1*1+1*1 := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hF₁ hG₂ (abs_nonneg _) (by omega))
        (mul_le_mul hF₂ hG₁ (abs_nonneg _) (by omega))
    _ = 2 := by norm_num

end Metric
end Release075.Discrete

namespace Release075.Discrete
variable {V : Type} {M : Metric V}

namespace Path
variable {a b c d e f : V}

end Path

end Release075.Discrete

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.Discrete OAI.Release075.Discrete.Metric


theorem solution : type_of% @_root_.OAI.Release075.Discrete.Metric.form_triangle_bound := @_root_.OAI.Release075.Discrete.Metric.form_triangle_bound
