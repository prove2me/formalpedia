-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.Data.cardinal_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:35:19.768409+00:00
-- url     : https://prove2.me/submissions/59465c27-c5d1-4073-9b33-679a12e33045

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Subarrays.lean:L134-L155
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.Data.cardinal_le. The node keeps its source
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
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayMaps
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayEmbeddings
import Definitions.Def_OAI_ModelTheory_Categoricity_Subarrays
import Theorems.Thm_OAI_CHObstruction_Tuples_cardinal_bound

-- ---- from OAI.ModelTheory.Categoricity.Subarrays ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace BaseOrders

variable {B : Type u} [LinearOrder B] [DenselyOrdered B] [NoMinOrder B]
  [NoMaxOrder B] [Nonempty B]

end BaseOrders

namespace Arrays

open Tuples
open scoped symmDiff

variable (M : Data.{u})

variable {M}
variable (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
  [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S]

attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_15
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqElemB
theorem Data.cardinal_le (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hI : #M.I ≤ κ) (hB : #M.B ≤ κ) : #M.Carrier ≤ κ := by
  let enc : M.Carrier → M.I ⊕ M.B ⊕ Finset M.B ⊕ Finset ℕ ⊕
      (Tuple M.I × ℕ × Finset M.B) ⊕ (Tuple M.I × M.B × Finset ℕ)
    | .index i => .inl i
    | .base b => .inr (.inl b)
    | .group s => .inr (.inr (.inl s))
    | .star v => .inr (.inr (.inr (.inl v)))
    | .row t n s => .inr (.inr (.inr (.inr (.inl (t, n, s)))))
    | .col t b v => .inr (.inr (.inr (.inr (.inr (t, b, v)))))
  have he : Function.Injective enc := by
    intro a b h
    cases a <;> cases b <;> simp_all [enc]
  apply (Cardinal.mk_le_of_injective he).trans
  simp only [Cardinal.mk_sum, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_uzero,
    Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.mk_finset_of_infinite]
  have ht := Tuples.cardinal_bound κ hκ hI
  calc
    #M.I + (#M.B + (#M.B + (ℵ₀ +
      (#(Tuple M.I) * (ℵ₀ * #M.B) + #(Tuple M.I) * (#M.B * ℵ₀))))) ≤
      κ + (κ + (κ + (κ + (κ * (κ * κ) + κ * (κ * κ))))) := by gcongr
    _ = κ := by simp only [Cardinal.mul_eq_self hκ, Cardinal.add_eq_self hκ]

end Arrays

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_15
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqElemB


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.Data.cardinal_le.{u} := @_root_.OAI.CHObstruction.Arrays.Data.cardinal_le.{u}
