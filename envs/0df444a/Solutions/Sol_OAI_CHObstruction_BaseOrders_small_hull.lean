-- Prove2me | solution 1 for OAI.CHObstruction.BaseOrders.small_hull
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:33:57.025621+00:00
-- url     : https://prove2.me/submissions/9056942f-c14a-497d-85a7-901868ffcdc5

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Subarrays.lean:L18-L65
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.BaseOrders.small_hull. The node keeps its source
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

-- ---- from OAI.ModelTheory.Categoricity.Subarrays ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace BaseOrders

variable {B : Type u} [LinearOrder B] [DenselyOrdered B] [NoMinOrder B]
  [NoMaxOrder B] [Nonempty B]

theorem small_hull (loc : ∀ a b : B, (Set.Icc a b).Countable)
    (A : Set B) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    ∃ S : Set B, A ⊆ S ∧ S.OrdConnected ∧ Nonempty S ∧
      NoMinOrder S ∧ NoMaxOrder S ∧ DenselyOrdered S ∧ #S ≤ κ := by
  classical
  let p : B := Classical.arbitrary B
  let T : Set B := A ∪ {p}
  let lo : B → B := fun x => (exists_lt x).choose
  let hi : B → B := fun x => (exists_gt x).choose
  have hlo (x : B) : lo x < x := (exists_lt x).choose_spec
  have hhi (x : B) : x < hi x := (exists_gt x).choose_spec
  let S : Set B := {x | ∃ a : T, ∃ b : T, lo a < x ∧ x < hi b}
  have hTS : T ⊆ S := fun x hx => ⟨⟨x, hx⟩, ⟨x, hx⟩, hlo x, hhi x⟩
  have hc : S.OrdConnected := by
    constructor
    rintro x ⟨a, b, hax, hxb⟩ y ⟨c, d, hcy, hyd⟩ z ⟨hxz, hzy⟩
    exact ⟨a, d, hax.trans_le hxz, hzy.trans_lt hyd⟩
  have hmin : NoMinOrder S := ⟨by
    rintro ⟨x, a, b, hax, hxb⟩
    obtain ⟨y, hay, hyx⟩ := exists_between hax
    exact ⟨⟨y, a, b, hay, hyx.trans hxb⟩, hyx⟩⟩
  have hmax : NoMaxOrder S := ⟨by
    rintro ⟨x, a, b, hax, hxb⟩
    obtain ⟨y, hxy, hyb⟩ := exists_between hxb
    exact ⟨⟨y, a, b, hax.trans hxy, hyb⟩, hxy⟩⟩
  have hd : DenselyOrdered S := ⟨by
    intro x y hxy
    obtain ⟨z, hxz, hzy⟩ := exists_between hxy
    exact ⟨⟨z, hc.out x.property y.property ⟨hxz.le, hzy.le⟩⟩, hxz, hzy⟩⟩
  refine ⟨S, Set.Subset.trans Set.subset_union_left hTS, hc,
    ⟨⟨p, hTS (Or.inr rfl)⟩⟩, hmin, hmax, hd, ?_⟩
  have hT : #T ≤ κ := by
    apply (Cardinal.mk_union_le A {p}).trans
    simpa only [Cardinal.mk_singleton, Cardinal.add_eq_self hκ] using
      add_le_add hA (Cardinal.one_le_aleph0.trans hκ)
  have he : S = ⋃ ab : T × T, Set.Ioo (lo ab.1) (hi ab.2) := by
    ext x
    simp only [S, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_Ioo]
    exact ⟨fun ⟨a, b, h⟩ => ⟨⟨a, b⟩, h⟩, fun ⟨⟨a, b⟩, h⟩ => ⟨a, b, h⟩⟩
  rw [he]
  apply Cardinal.mk_iUnion_le_sum_mk.trans
  have hb (ab : T × T) : #(Set.Ioo (lo ab.1) (hi ab.2)) ≤ κ :=
    (Cardinal.mk_le_aleph0_iff.2 ((loc _ _).mono Set.Ioo_subset_Icc_self)).trans hκ
  apply (Cardinal.sum_le_sum _ _ hb).trans
  simp only [Cardinal.sum_const, Cardinal.mk_prod, Cardinal.lift_id]
  calc
    (#T * #T) * κ ≤ (κ * κ) * κ := mul_le_mul' (mul_le_mul' hT hT) le_rfl
    _ = κ := by rw [Cardinal.mul_eq_self hκ, Cardinal.mul_eq_self hκ]

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
end Arrays

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.BaseOrders
open Cardinal Ordinal Order


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.BaseOrders.small_hull.{u} := @_root_.OAI.CHObstruction.BaseOrders.small_hull.{u}
