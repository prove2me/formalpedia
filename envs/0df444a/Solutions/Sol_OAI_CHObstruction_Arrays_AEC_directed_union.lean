-- Prove2me | solution 1 for OAI.CHObstruction.Arrays.AEC.directed_union
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:51:50.585007+00:00
-- url     : https://prove2.me/submissions/b229259e-2a69-4e0d-b8ae-24aa6a72aff8

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/AEC.lean:L327-L402
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Arrays.AEC.directed_union. The node keeps its source
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
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayIsomorphisms
import Definitions.Def_OAI_ModelTheory_Categoricity_DirectedLimits
import Definitions.Def_OAI_ModelTheory_Categoricity_AEC
import Theorems.Thm_OAI_CHObstruction_Arrays_Map_Strong_comp
import Theorems.Thm_OAI_CHObstruction_Arrays_System_Data_liftMap_strong
import Theorems.Thm_OAI_CHObstruction_Arrays_System_Data_limit_object
import Theorems.Thm_OAI_CHObstruction_Arrays_System_Data_toLimit_strong

-- ---- from OAI.ModelTheory.Categoricity.ArrayEmbeddings ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Tests

open Tuples

end Tests

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_8
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_9
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_10
end Arrays

namespace Tuples

variable {I J : Type u}

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_11
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_12
theorem Map.strong_of_surjective (f : Map M N) (hCH : CH.{u})
    (hb : Function.Surjective f.base) : f.Strong hCH := by
  constructor
  · rw [Set.range_eq_univ.2 hb]
    exact Set.ordConnected_univ
  · intro t b h
    exact (h (hb b)).elim

end Arrays

namespace Tuples

end Tuples

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_13
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_14
variable (f : RawEmbedding M N)

end Arrays

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.ArrayIsomorphisms ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

open Tuples
open scoped symmDiff

variable {M N P : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_16
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_17
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_18
variable (e : RawIso M N)

theorem RawIso.base_surjective : Function.Surjective e.toMap.base := by
  intro b
  obtain ⟨a, ha⟩ := e.base_surjective_point b
  refine ⟨a, Point.base.inj (I := N.I) ?_⟩
  exact (e.toMap_onPoint (.base a)).trans ha

end Arrays

namespace CardinalTools

end CardinalTools

namespace Arrays

open Tuples
open scoped symmDiff

variable {M : Data.{u}}
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqI
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_19
end Arrays

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.AEC ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace RelModel

variable {L : ℕ → Type} {M N P : RelModel.{u} L}

end RelModel

namespace Arrays

open Tuples

variable {M N : Data.{u}}

namespace Presentation

variable {R T V : RelModel.{u} Language} (P : Presentation R)

theorem comparison_strong (Q : Presentation R) (hCH : CH.{u}) :
    (P.comparison Q).toMap.Strong hCH :=
  (P.comparison Q).toMap.strong_of_surjective hCH (P.comparison Q).base_surjective

theorem inclusion_unique {Q : Presentation T} {f g : Map P.data Q.data}
    (hf : P.Inclusion Q f) (hg : P.Inclusion Q g) : f = g := by
  apply Map.ext_onPoint
  intro x
  apply Q.equiv.injective
  apply Subtype.ext
  exact (hf x).trans (hg x).symm

theorem inclusion_refl : P.Inclusion P (Map.id P.data) := by
  intro x
  rw [Map.id_onPoint]

theorem Inclusion.comp {P : Presentation R} {Q : Presentation T} {O : Presentation V}
    {f : Map P.data Q.data} {g : Map Q.data O.data}
    (hg : Q.Inclusion O g) (hf : P.Inclusion Q f) : P.Inclusion O (g.comp f) := by
  intro x
  rw [Map.comp_onPoint]
  exact (hg (f.onPoint x)).trans (hf x)

theorem inclusion_comparison (Q : Presentation R) : P.Inclusion Q (P.comparison Q).toMap := by
  intro x
  rw [comparison_onPoint, Equiv.apply_symm_apply]

end Presentation

variable (hCH : CH.{u})

namespace AEC

variable {hCH : CH.{u}} {R T V : RelModel.{u} Language}

theorem strong_rebase (h : Strong (hCH := hCH) R T) (P : Presentation R) (Q : Presentation T) :
    ∃ f : Map P.data Q.data, f.Strong hCH ∧ P.Inclusion Q f := by
  obtain ⟨P', Q', hp, hq, f, hf, he⟩ := h
  refine ⟨(Q'.comparison Q).toMap.comp (f.comp (P.comparison P').toMap),
    (Q'.comparison_strong Q hCH).comp hCH (hf.comp hCH (P.comparison_strong P' hCH)), ?_⟩
  exact (Q'.inclusion_comparison Q).comp (he.comp (P.inclusion_comparison P'))

theorem strong_of {P : Presentation R} {Q : Presentation T}
    (hp : P.data.IsObject hCH) (hq : Q.data.IsObject hCH)
    (f : Map P.data Q.data) (hf : f.Strong hCH) (he : P.Inclusion Q f) : Strong (hCH := hCH) R T :=
  ⟨P, Q, hp, hq, f, hf, he⟩

end AEC

namespace Coding

variable {X : Type u} {A : ZFSet.{u}}

end Coding

namespace AEC

section

variable {hCH : CH.{u}} {R : RelModel.{u} Language}

end

variable {hCH : CH.{u}}

theorem directed_union {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (F : J → RelModel.{u} Language) (ho : ∀ i, Object (hCH := hCH) (F i))
    (hs : ∀ i j, i ≤ j → Strong (hCH := hCH) (F i) (F j)) :
    ∃ U, Object (hCH := hCH) U ∧ RelModel.IsUnion F U ∧
      (∀ i, Strong (hCH := hCH) (F i) U) ∧
      (∀ N, Object (hCH := hCH) N → (∀ i, Strong (hCH := hCH) (F i) N) → Strong (hCH := hCH) U N) := by
  classical
  let P (i : J) : Presentation (F i) := (ho i).choose
  have hp (i : J) : (P i).data.IsObject hCH := (ho i).choose_spec
  let maps (i j : J) (h : i ≤ j) : Map (P i).data (P j).data :=
    (strong_rebase (hs i j h) (P i) (P j)).choose
  have hm (i j : J) (h : i ≤ j) : (maps i j h).Strong hCH :=
    (strong_rebase (hs i j h) (P i) (P j)).choose_spec.1
  have hi (i j : J) (h : i ≤ j) : (P i).Inclusion (P j) (maps i j h) :=
    (strong_rebase (hs i j h) (P i) (P j)).choose_spec.2
  let S : System.Data (J := J) := {
    obj := fun i => (P i).data
    map := maps
    map_id := fun i => (P i).inclusion_unique (hi i i le_rfl) (P i).inclusion_refl
    map_comp := fun i j k h h' => (P i).inclusion_unique ((hi j k h').comp (hi i j h)) (hi i k (h.trans h')) }
  have hconv : ∀ i j h, (Set.range (S.map i j h).base).OrdConnected := fun i j h => (hm i j h).convex
  let A : ZFSet.{u} := ZFSet.iUnion (fun i => (F i).carrier)
  let stage (i : J) (x : (S.obj i).Carrier) : A :=
    ⟨((P i).equiv x).val, ZFSet.mem_iUnion.2 ⟨i, ((P i).equiv x).property⟩⟩
  let val : S.X → A := DirectLimit.lift S.pointMap stage (by
    intro i j h x
    apply Subtype.ext
    exact (hi i j h x).symm)
  have hv (i : J) (x : (S.obj i).Carrier) : val (S.point i x) = stage i x := rfl
  have hinj : Function.Injective val := by
    intro x y
    induction x, y using DirectLimit.induction₂ S.pointMap with
    | ih i x y =>
      intro h
      apply congrArg (S.point i)
      apply (P i).equiv.injective
      apply Subtype.ext
      exact congrArg (fun z : A => z.val) h
  have hsurj : Function.Surjective val := by
    intro a
    obtain ⟨i, hai⟩ := ZFSet.mem_iUnion.1 a.property
    refine ⟨S.point i ((P i).equiv.symm ⟨a.val, hai⟩), ?_⟩
    rw [hv]
    apply Subtype.ext
    change ((P i).equiv ((P i).equiv.symm ⟨a.val, hai⟩)).val = a.val
    simp only [Equiv.apply_symm_apply]
  let e : (S.limitData hconv).Carrier ≃ A :=
    (S.equivalence hconv).symm.trans (Equiv.ofBijective val ⟨hinj, hsurj⟩)
  have he (i : J) (x : (S.obj i).Carrier) :
      e ((S.toLimit hconv i).onPoint x) = stage i x := by
    change val ((S.equivalence hconv).symm ((S.toLimit hconv i).onPoint x)) = _
    rw [S.equivalence_symm_stage, hv]
  let U := Coding.model (S.limitData hconv) A e
  let Q := Coding.presentation (S.limitData hconv) A e
  have hu : Q.data.IsObject hCH := S.limit_object hconv hp hm
  have hstage (i : J) : Strong (hCH := hCH) (F i) U :=
    strong_of (P := P i) (Q := Q) (hp i) hu (S.toLimit hconv i)
      (S.toLimit_strong hconv hm i) (fun x => congrArg Subtype.val (he i x))
  refine ⟨U, ⟨Q, hu⟩, ⟨fun i => substructure (hstage i), ?_⟩, hstage, ?_⟩
  · intro x
    exact ZFSet.mem_iUnion.1 x.property
  · intro N hn hc
    obtain ⟨O, ho'⟩ := hn
    let q (i : J) : Map (S.obj i) O.data := (strong_rebase (hc i) (P i) O).choose
    have hq_strong (i : J) : (q i).Strong hCH := (strong_rebase (hc i) (P i) O).choose_spec.1
    have hq_inc (i : J) : (P i).Inclusion O (q i) := (strong_rebase (hc i) (P i) O).choose_spec.2
    have hq (i j : J) (h : i ≤ j) : (q j).comp (S.map i j h) = q i :=
      (P i).inclusion_unique ((hq_inc j).comp (hi i j h)) (hq_inc i)
    let f := S.liftMap hconv q hq
    refine strong_of hu ho' f (S.liftMap_strong hconv q hq hq_strong) ?_
    intro x
    obtain ⟨i, y, rfl⟩ := S.toLimit_covers hconv x
    change (O.equiv ((S.liftMap hconv q hq).onPoint ((S.toLimit hconv i).onPoint y))).val =
      (e ((S.toLimit hconv i).onPoint y)).val
    rw [S.liftMap_stage, he]
    exact hq_inc i y

end AEC
end Arrays

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Arrays OAI.CHObstruction.Arrays.AEC
open Cardinal Ordinal Order
open Tuples


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Arrays.AEC.directed_union.{u} := @_root_.OAI.CHObstruction.Arrays.AEC.directed_union.{u}
