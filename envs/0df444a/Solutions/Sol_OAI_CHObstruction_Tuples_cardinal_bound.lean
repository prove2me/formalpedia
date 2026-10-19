-- Prove2me | solution 1 for OAI.CHObstruction.Tuples.cardinal_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:26:35.704494+00:00
-- url     : https://prove2.me/submissions/97d12689-c2ee-4de1-bcd8-b038ca69f61f

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Arrays.lean:L185-L200
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Tuples.cardinal_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound
import Definitions.Def_OAI_ModelTheory_Categoricity_Arrays

-- ---- from OAI.ModelTheory.Categoricity.Arrays ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Matrix

open scoped symmDiff

variable {B : Type u}

attribute [local instance] OAI.CHObstruction.Matrix.instDecidableEq_oAI
end Matrix

namespace Arrays

open Tuples
open scoped symmDiff

attribute [instance] Data.indexNonempty Data.baseNonempty Data.order Data.dense Data.noMin Data.noMax

variable (M : Data.{u})

attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB
end Arrays

namespace Tuples

variable {I J K : Type u}

theorem cardinal_bound (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hI : #I ≤ κ) : #(Tuple I) ≤ κ := by
  rw [Cardinal.mk_sigma]
  have h : ∀ n : ℕ, #(Fin (n + 1) ↪ I) ≤ κ := by
    intro n
    calc
      #(Fin (n + 1) ↪ I) ≤ #(Fin (n + 1) → I) :=
        Cardinal.mk_le_of_injective DFunLike.coe_injective
      _ = #I ^ ((n + 1 : ℕ) : Cardinal.{u}) := by simp
      _ ≤ κ ^ ((n + 1 : ℕ) : Cardinal.{u}) := Cardinal.power_le_power_right hI
      _ ≤ κ := Cardinal.power_nat_le hκ
  calc
    Cardinal.sum (fun n : ℕ => #(Fin (n + 1) ↪ I)) ≤
        Cardinal.sum (fun _ : ℕ => κ) := Cardinal.sum_le_sum _ _ h
    _ = κ := by
      simp only [Cardinal.sum_const, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
      exact Cardinal.aleph0_mul_eq hκ

end Tuples

namespace FiniteSupports

open scoped symmDiff

variable {A : Type u} {B : Type v} [DecidableEq A] [DecidableEq B]

end FiniteSupports

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_1
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_2
end Arrays

namespace Tuples

end Tuples

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Tuples
open Cardinal Ordinal Order


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Tuples.cardinal_bound.{u} := @_root_.OAI.CHObstruction.Tuples.cardinal_bound.{u}
