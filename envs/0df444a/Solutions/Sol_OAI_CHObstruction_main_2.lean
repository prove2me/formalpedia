-- Prove2me | solution 2 for OAI.CHObstruction.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:54:08.723313+00:00
-- url     : https://prove2.me/submissions/1779fc81-32af-4332-8fec-a22d5680e493

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Main.lean:L233-L240
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.CHObstruction.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_CHObstruction_main) verbatim and is proved by it.
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
import Definitions.Def_OAI_ModelTheory_Categoricity_Main
import Theorems.Thm_OAI_CHObstruction_Arrays_AEC_directed_union
import Theorems.Thm_OAI_CHObstruction_Arrays_Data_cardinal_le
import Theorems.Thm_OAI_CHObstruction_Arrays_Data_small_subarray
import Theorems.Thm_OAI_CHObstruction_Arrays_Map_Strong_comp
import Theorems.Thm_OAI_CHObstruction_Arrays_Map_Strong_factor
import Theorems.Thm_OAI_CHObstruction_Arrays_Map_factor
import Theorems.Thm_OAI_CHObstruction_Arrays_Map_surjective
import Theorems.Thm_OAI_CHObstruction_BaseOrders_cardinal_le
import Theorems.Thm_OAI_CHObstruction_Domination_countable_exceptions
import Theorems.Thm_OAI_CHObstruction_TailBound_index_lt

-- ---- from OAI.ModelTheory.Categoricity.Collapse ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TaggedCollapse

variable {Q : Type u} (R : Q → Q → Prop) (wf : WellFounded R)

end TaggedCollapse

namespace Domination

end Domination

namespace CountableClosures

variable {A : Type u} (R : A → A → Prop)
  (separates : ∀ a b, a ≠ b → ∃ w, ¬ (R w a ↔ R w b))

theorem witness_distinguishes {a b : A} (h : a ≠ b) :
    ¬ (R (witness R separates a b) a ↔ R (witness R separates a b) b) := by
  simpa only [witness, dite_eq_right h] using Classical.choose_spec (separates a b h)

theorem stage_mono (S : Set A) : Monotone (stage R separates S) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

theorem closure_mono : Monotone (closure R separates) := by
  intro S T hST x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  apply Set.mem_iUnion.2 ⟨n, ?_⟩
  suffices stage R separates S n ⊆ stage R separates T n from this hn
  clear hn
  induction n with
  | zero => exact hST
  | succ n ih =>
    intro y hy
    rcases hy with hy | hy
    · exact Or.inl (ih hy)
    · rcases hy with ⟨a, ha, b, hb, rfl⟩
      exact Or.inr ⟨a, ih ha, b, ih hb, rfl⟩

theorem witness_mem {S : Set A} {a b : A}
    (ha : a ∈ closure R separates S) (hb : b ∈ closure R separates S) :
    witness R separates a b ∈ closure R separates S := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.1 ha
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hb
  apply Set.mem_iUnion.2 ⟨max m n + 1, ?_⟩
  exact Or.inr ⟨a, stage_mono R separates S (le_max_left _ _) hm,
    b, stage_mono R separates S (le_max_right _ _) hn, rfl⟩

theorem extensional {S : Set A} {a b : A}
    (ha : a ∈ closure R separates S) (hb : b ∈ closure R separates S)
    (heq : ∀ w ∈ closure R separates S, R w a ↔ R w b) : a = b := by
  by_contra h
  exact witness_distinguishes R separates h (heq _ (witness_mem R separates ha hb))

theorem entries_mono (X Y : FiniteSeed A) (h : X.val ⊆ Y.val) :
    entries R separates X ⊆ entries R separates Y :=
  closure_mono R separates h

theorem enumeration_surjective (X : FiniteSeed A) :
    Function.Surjective (enumeration R separates X) := by
  intro x
  obtain ⟨n, hn⟩ := Classical.choose_spec
    (Set.Countable.exists_surjective (entries_nonempty R separates X)
      (entries_countable R separates X)) x
  exact ⟨n + 1, hn⟩

theorem enumeration_singleton (x : A) :
    (enumeration R separates ⟨{x}, Finset.singleton_nonempty x⟩ 0).val = x := by
  exact Finset.mem_singleton.1 (Classical.choose_spec (Finset.singleton_nonempty x))

end CountableClosures

namespace TaggedLimit

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι]
  (F : ι → Type u) (f : ∀ i j, i ≤ j → F i ↪ F j)
  [DirectedSystem F (fun i j h => f i j h)]
  (R : ∀ i, F i → F i → Prop)
  (respect : ∀ i j h x y, R i x y ↔ R j (f i j h x) (f i j h y))
  (ρ : ∀ i, F i → Ordinal.{u})
  (tags : ∀ i j h x, ρ i x = ρ j (f i j h x))

end TaggedLimit

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.Partition ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace EndHomogeneous

variable {J X C : Type u} [LinearOrder J] [LinearOrder X]
  (wJ : WellFounded ((· < ·) : J → J → Prop))
  (wX : WellFounded ((· < ·) : X → X → Prop)) (c : Finset X → C)

end EndHomogeneous

namespace FinitePartition

end FinitePartition

namespace ThresholdArithmetic

theorem palette_lt : ξ.{u} < tailThreshold.{u} :=
  (lt_succ ξ).trans_le (Cardinal.le_beth_ord _)

theorem endpoint_eq_hanf (hCH : CH.{u}) : endpoint.{u} = hanf (ℵ₀ : Cardinal.{u}) := by
  unfold endpoint hanf
  rw [hCH, Cardinal.succ_aleph, Cardinal.ord_aleph]
  congr 2
  norm_num

end ThresholdArithmetic

namespace FinitePartition

variable {X J C : Type u}

end FinitePartition

namespace FinitePatterns

open FinitePartition

variable {X C : Type u} (Λ ξ : Cardinal.{u}) (c : ℕ → Finset X → C)

variable (hΛ : Λ.IsStrongLimit) (hξinf : ℵ₀ ≤ ξ) (hξ : ξ < Λ)
  (hcof : ξ < Λ.ord.cof) (hC : #C ≤ ξ)

variable (hX : Λ ≤ #X)

end FinitePatterns

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.Colors ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Colors

theorem representative_color (s : Color) : color (representative s) = s := Quotient.out_eq s

open Diagrams

end Colors

namespace Tuples

end Tuples

namespace Tests

open Diagrams Colors Tuples

variable (hCH : CH.{u})

end Tests

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.EndpointDiagrams ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace EndpointDiagrams

open Diagrams CountableClosures Tuples

theorem entry_mem (t : Tuple D.{u}) (l : Label (Fin (t.1 + 1))) :
    entry t.2 l ∈ entries membership separates (fullSeed t) := by
  exact entries_mono membership separates (seed t.2 l.1) (fullSeed t)
    (Finset.map_subset_map.mpr (Finset.subset_univ _))
    (enumeration membership separates (seed t.2 l.1) l.2).property

theorem entry_surjective (t : Tuple D.{u}) (x : entries membership separates (fullSeed t)) :
    ∃ l, entry t.2 l = x.val := by
  obtain ⟨n, hn⟩ := enumeration_surjective membership separates (fullSeed t) x
  exact ⟨(⟨Finset.univ, Finset.univ_nonempty⟩, n), congrArg Subtype.val hn⟩

theorem entry_root {k : ℕ} (t : Fin k ↪ D.{u}) (i : Fin k) :
    entry t (Label.root i) = t i := by
  have hs : seed t (Label.root i).1 = ⟨{t i}, Finset.singleton_nonempty _⟩ := by
    apply Subtype.ext
    exact Finset.map_singleton _ _
  unfold entry
  rw [hs]
  exact enumeration_singleton membership separates (t i)

theorem entry_comp {k m : ℕ} (t : Fin k ↪ D.{u}) (e : Fin m ↪ Fin k) (l : Label (Fin m)) :
    entry (e.trans t) l = entry t (Label.map e l) := by
  have hs : seed (e.trans t) l.1 = seed t (Label.map e l).1 := by
    apply Subtype.ext
    exact (Finset.map_map e t l.1.val).symm
  unfold entry
  rw [hs]
  rfl

theorem diagram_restrict {k m : ℕ} (t : Fin k ↪ D.{u}) (e : Fin m ↪ Fin k) (b : Tag.{u}) :
    diagram (e.trans t) b = (diagram t b).restrict e := by
  unfold diagram Diagram.restrict
  congr 1 <;> funext l
  · funext l'; rw [entry_comp, entry_comp]
  · funext l'; rw [entry_comp, entry_comp]
  · rw [entry_comp]

theorem countable_bad (X : FiniteSeed D.{u}) : {b | ¬ Good X b}.Countable := by
  classical
  have : Countable (entries membership separates X) :=
    Set.countable_coe_iff.2 (entries_countable membership separates X)
  let bad (a c : entries membership separates X) : Set Tag.{u} :=
    if h : membership a.val c.val then
      {b | (Domination.values (rank c.val) (beta b)).val ≤
        (Domination.values (rank a.val) (beta b)).val} else ∅
  have hb : ∀ a c, (bad a c).Countable := by
    intro a c
    dsimp only [bad]
    split_ifs with h
    · have hr : (rank a.val).val < (rank c.val).val := ZFSet.rank_lt_of_mem h
      exact (Domination.countable_exceptions (rank c.val) ⟨(rank a.val).val, hr⟩).preimage
        Ordinal.ToType.mk.symm.injective
    · exact Set.countable_empty
  apply (Set.countable_iUnion (fun a => Set.countable_iUnion (hb a))).mono
  intro b h
  simp only [Good, not_forall] at h
  obtain ⟨a, c, hm, hlt⟩ := h
  exact Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨c, by
    simpa only [bad, dite_eq_left hm, Set.mem_ofPred_eq, localTag_value, not_lt] using hlt⟩⟩

theorem good_mono {X Y : FiniteSeed D.{u}} (hXY : X.val ⊆ Y.val) {b : Tag.{u}}
    (h : Good Y b) : Good X b := by
  intro a c hac
  exact h ⟨a.val, entries_mono membership separates X Y hXY a.property⟩
    ⟨c.val, entries_mono membership separates X Y hXY c.property⟩ hac

theorem diagram_valid (t : Tuple D.{u}) (b : Tag.{u}) (hb : Good (fullSeed t) b) :
    (diagram t.2 b).Valid := by
  constructor
  · exact ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩
  · intro a a' c c' haa hcc
    change membership _ _ ↔ membership _ _
    rw [show entry t.2 a = entry t.2 a' from haa,
      show entry t.2 c = entry t.2 c' from hcc]
  · intro a a' haa
    exact congrArg (localTag b) haa
  · intro a c hac
    exact hb ⟨entry t.2 a, entry_mem t a⟩ ⟨entry t.2 c, entry_mem t c⟩ hac
  · intro a c h
    apply CountableClosures.extensional membership separates
      (entry_mem t a) (entry_mem t c)
    intro z hz
    obtain ⟨l, hl⟩ := entry_surjective t ⟨z, hz⟩
    simpa only [diagram, hl] using h l
  · intro i j hij
    apply t.2.injective
    simpa only [diagram, entry_root] using hij

theorem sub_seed (t : Tuple D.{u}) {m : ℕ} (e : Fin (m + 1) ↪o Fin (t.1 + 1)) :
    (fullSeed (sub t e)).val ⊆ (fullSeed t).val := by
  change Finset.univ.map (e.toEmbedding.trans t.2) ⊆ Finset.univ.map t.2
  rw [← Finset.map_map]
  exact Finset.map_subset_map.mpr (Finset.subset_univ _)

theorem passes (hCH : CH.{u}) (t : Tuple D.{u}) (b : Tag.{u}) (hb : Good (fullSeed t) b) :
    Tests.Test hCH (fun t => colors hCH t b) t := by
  refine ⟨diagram t.2 b, ?_⟩
  intro m e
  rw [← diagram_restrict]
  exact ⟨diagram_valid (sub t e) b (good_mono (sub_seed t e) hb), rfl⟩

theorem countable_failures (hCH : CH.{u}) (t : Tuple D.{u}) :
    {b | ¬ Tests.Test hCH (fun t => colors hCH t b) t}.Countable :=
  (countable_bad (fullSeed t)).mono (fun b h hb => h (passes hCH t b hb))

end EndpointDiagrams

end CHObstruction

end

end OAI

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
theorem Data.countable_object (hCH : CH.{u}) [Countable M.B] : M.IsObject hCH :=
  fun _ => Set.to_countable _

theorem Data.base_bound : #M.B ≤ (ℵ_ 1 : Cardinal.{u}) :=
  BaseOrders.cardinal_le M.locallyCountable

theorem Data.uncountable_index_bound (hCH : CH.{u}) (hM : M.IsObject hCH)
    (hB : ¬ Countable M.B) : #M.I < tailThreshold.{u} :=
  TailBound.index_lt hCH M.base_bound hB M.colors hM

end Arrays

namespace Tuples

variable {I J K : Type u}

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

-- ---- from OAI.ModelTheory.Categoricity.ArrayEmbeddings ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Tests

open Tuples

theorem congr {I : Type v} (hCH : CH.{u}) {c d : Tuple I → Colors.Palette.{u}}
    (t : Tuple I) (h : ∀ m (e : Fin (m + 1) ↪o Fin (t.1 + 1)), c (sub t e) = d (sub t e)) :
    Test hCH c t ↔ Test hCH d t := by
  have he : (fun m (e : Fin (m + 1) ↪o Fin (t.1 + 1)) => c (sub t e)) =
      (fun m (e : Fin (m + 1) ↪o Fin (t.1 + 1)) => d (sub t e)) := funext (fun m => funext (h m))
  exact iff_of_eq (congrArg (Passes hCH) he)

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
theorem countable_isomorphic [Countable M.B] [Countable N.B] (hI : #M.I = #N.I) :
    ∃ f : Map M N, Function.Surjective f.index ∧ Function.Surjective f.base := by
  obtain ⟨ei⟩ := Cardinal.eq.1 hI
  obtain ⟨eb⟩ := Order.iso_of_countable_dense M.B N.B
  exact ⟨countableMap ei eb, ei.surjective, eb.surjective⟩

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
theorem Data.cardinal_eq : #M.Carrier = max (max #M.I #M.B) ℵ₀ := by
  apply le_antisymm
  · exact M.cardinal_le _ (le_max_right _ _) ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _))
  · apply max_le
    · exact max_le (Cardinal.mk_le_of_injective (fun _ _ h => Point.index.inj h))
        (Cardinal.mk_le_of_injective (fun _ _ h => Point.base.inj h))
    · have h := Cardinal.mk_le_of_injective (f := fun v : ULift.{u} (Finset ℕ) =>
          Point.star (I := M.I) (B := M.B) v.down) (fun a b h => ULift.ext _ _ (Point.star.inj h))
      simpa only [Cardinal.mk_uLift, Cardinal.mk_finset_of_infinite, Cardinal.mk_nat,
        Cardinal.lift_aleph0] using h

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

theorem IsSubstructure.antisymm (h : M.IsSubstructure N) (k : N.IsSubstructure M) : M = N := by
  obtain ⟨A, r⟩ := M
  obtain ⟨B, s⟩ := N
  have he : A = B := ZFSet.ext (fun x => ⟨fun hx => h.subset hx, fun hx => k.subset hx⟩)
  subst B
  congr 1
  funext n c a
  exact propext (h.restrict n c a)

end RelModel

namespace Arrays

open Tuples

variable {M N : Data.{u}}

namespace Presentation

variable {R T V : RelModel.{u} Language} (P : Presentation R)

theorem comparison_strong (Q : Presentation R) (hCH : CH.{u}) :
    (P.comparison Q).toMap.Strong hCH :=
  (P.comparison Q).toMap.strong_of_surjective hCH (P.comparison Q).base_surjective

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

theorem strong_objects (h : Strong (hCH := hCH) R T) : Object (hCH := hCH) R ∧ Object (hCH := hCH) T := by
  obtain ⟨P, Q, hp, hq, f, hf, he⟩ := h
  exact ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩

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

theorem refl (h : Object (hCH := hCH) R) : Strong (hCH := hCH) R R := by
  obtain ⟨P, hp⟩ := h
  exact strong_of hp hp (Map.id P.data) (Map.id_strong hCH _) P.inclusion_refl

theorem antisymm (h : Strong (hCH := hCH) R T) (k : Strong (hCH := hCH) T R) : R = T :=
  (substructure h).antisymm (substructure k)

theorem trans (h : Strong (hCH := hCH) R T) (k : Strong (hCH := hCH) T V) : Strong (hCH := hCH) R V := by
  obtain ⟨P, Q, hp, hq, f, hf, he⟩ := h
  obtain ⟨O, ho⟩ := (strong_objects k).2
  obtain ⟨g, hg, he'⟩ := strong_rebase k Q O
  exact strong_of hp ho (g.comp f) (hg.comp hCH hf) (he'.comp he)

theorem iso_objects (h : Object (hCH := hCH) R) (e : R.Iso T) : Object (hCH := hCH) T := by
  obtain ⟨P, hp⟩ := h
  exact ⟨P.transport e, hp⟩

theorem iso_strong {R' T' : RelModel.{u} Language} (h : Strong (hCH := hCH) R T)
    (e : R.Iso R') (f : T.Iso T')
    (he : ∀ x : R.carrier, (e.toEquiv x).val =
      (f.toEquiv ⟨x.val, (substructure h).subset x.property⟩).val) :
    Strong (hCH := hCH) R' T' := by
  obtain ⟨P, Q, hp, hq, g, hg, hinc⟩ := h
  refine strong_of (P := P.transport e) (Q := Q.transport f) hp hq g hg ?_
  intro x
  change (f.toEquiv (Q.equiv (g.onPoint x))).val = (e.toEquiv (P.equiv x)).val
  rw [he]
  congr 2
  exact Subtype.ext (hinc x)

theorem coherence (hsub : R.IsSubstructure T) (h : Strong (hCH := hCH) R V)
    (k : Strong (hCH := hCH) T V) : Strong (hCH := hCH) R T := by
  obtain ⟨P, O, hp, ho, f, hf, he⟩ := h
  obtain ⟨Q, hq⟩ := (strong_objects k).1
  obtain ⟨g, hg, he'⟩ := strong_rebase k Q O
  have hr : ∀ x : P.data.Carrier, ∃ y, g.onPoint y = f.onPoint x := by
    intro x
    let y : T.carrier := ⟨(P.equiv x).val, hsub.subset (P.equiv x).property⟩
    refine ⟨Q.equiv.symm y, O.equiv.injective (Subtype.ext ?_)⟩
    rw [he', he, Equiv.apply_symm_apply]
  obtain ⟨l, hl⟩ := f.factor g hr
  refine strong_of hp hq l (hf.factor hCH hl) ?_
  intro x
  have hv := congrArg (fun m : Map P.data O.data => (O.equiv (m.onPoint x)).val) hl
  rw [Map.comp_onPoint] at hv
  rw [he', he] at hv
  exact hv

end AEC

namespace Coding

variable {X : Type u} {A : ZFSet.{u}}

theorem cardinal (e : X ≃ A) : #X = A.card := by
  apply Cardinal.lift_injective.{u+1}
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift] using (Cardinal.lift_mk_eq'.2 ⟨e⟩)

theorem coded_cardinal (M : Data.{u}) : (coded M).carrier.card = #M.Carrier :=
  (cardinal (universeEquiv M.Carrier)).symm

end Coding

namespace AEC

section

variable {hCH : CH.{u}} {R : RelModel.{u} Language}

theorem small (h : Object (hCH := hCH) R) (A : ZFSet.{u}) (hA : A ⊆ R.carrier) :
    ∃ T, Object (hCH := hCH) T ∧ Strong (hCH := hCH) T R ∧
      A ⊆ T.carrier ∧ T.carrier.card ≤ A.card + ℵ₀ := by
  obtain ⟨P, hp⟩ := h
  let S : Set P.data.Carrier := {x | (P.equiv x).val ∈ A}
  let e : S ≃ A := Equiv.ofBijective (fun x => ⟨(P.equiv x.val).val, x.property⟩) ⟨by
    intro a b hab
    apply Subtype.ext
    apply P.equiv.injective
    have hh : (P.equiv a.val).val = (P.equiv b.val).val := congrArg (fun z : A => z.val) hab
    exact Subtype.ext hh, by
    rintro ⟨a, ha⟩
    let x := P.equiv.symm ⟨a, hA ha⟩
    have hx : x ∈ S := by change (P.equiv x).val ∈ A; simpa only [x, Equiv.apply_symm_apply] using ha
    exact ⟨⟨x, hx⟩, Subtype.ext (by simp only [x, Equiv.apply_symm_apply])⟩⟩
  obtain ⟨M, f, hm, hf, hs, hc⟩ := P.data.small_subarray hCH hp S
  let z : M.Carrier → ZFSet.{u} := fun x => (P.equiv (f.onPoint x)).val
  have hz : Function.Injective z := Subtype.val_injective.comp (P.equiv.injective.comp f.injective)
  let eqv := Coding.rangeEquiv z hz
  let T := Coding.model M (ZFSet.range z) eqv
  let Q := Coding.presentation M (ZFSet.range z) eqv
  refine ⟨T, ⟨Q, hm⟩, strong_of (P := Q) (Q := P) hm hp f hf (fun x => rfl), ?_, ?_⟩
  · intro a ha
    have hx : P.equiv.symm ⟨a, hA ha⟩ ∈ S := by
      change (P.equiv (P.equiv.symm _)).val ∈ A
      simpa only [Equiv.apply_symm_apply] using ha
    obtain ⟨x, hx⟩ := hs hx
    exact ZFSet.mem_range.2 ⟨x, by change (P.equiv (f.onPoint x)).val = a; rw [hx]; simp⟩
  · change (ZFSet.range z).card ≤ A.card + ℵ₀
    rw [← Coding.cardinal eqv, ← Coding.cardinal e]
    exact hc

end

variable {hCH : CH.{u}}

theorem lsBound : (classData hCH).LSBound ℵ₀ := by
  refine ⟨le_rfl, ?_, ?_⟩
  · simpa only [Cardinal.lift_le_aleph0] using (Cardinal.mk_le_aleph0 (α := Σ n, Language n))
  · exact fun R h A ha => small h A ha

theorem isAEC : (classData hCH).IsAEC where
  strong_objects := strong_objects
  refl := refl
  antisymm := antisymm
  trans := trans
  substructure := substructure
  iso_objects h e := iso_objects h e.some
  iso_strong := iso_strong
  coherence := coherence
  chain_union γ hγ F ho hs := by
    let : Nonempty γ.ToType := Ordinal.nonempty_toType_iff.2 hγ
    exact directed_union F ho hs
  downward := ⟨ℵ₀, lsBound⟩

theorem hasLSNumber : (classData hCH).HasLSNumber ℵ₀ :=
  ⟨lsBound, fun _ h => h.1⟩

end AEC
end Arrays

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.Main ----
namespace OAI

/-!
# A CH obstruction to a prescribed categoricity threshold

Under CH, a countable relational language admits an abstract elementary class
with least Löwenheim–Skolem number `aleph0`, two nonisomorphic models of size
`beth (omega 2) = hanf aleph0`, and categoricity, including existence, at every
cardinal at least `tailThreshold`. Distinct base cardinalities separate the
endpoint models, while finite-support row and column translations establish
the included categoricity tail.
-/

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Arrays

open Tuples

variable (hCH : CH.{u})

namespace Existence

theorem countableData_object (hCH : CH.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    (countableData μ hμ).IsObject hCH := by
  have : Countable (countableData μ hμ).B := by change Countable RationalBase; infer_instance
  exact Data.countable_object _ _

theorem countableData_index (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    #(countableData μ hμ).I = μ := by
  change #μ.ord.ToType = μ
  simp only [Cardinal.mk_toType, Cardinal.card_ord]

theorem countableData_cardinal (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    #(countableData μ hμ).Carrier = μ := by
  rw [Data.cardinal_eq, countableData_index]
  change max (max μ #RationalBase.{u}) ℵ₀ = μ
  rw [max_eq_left ((Cardinal.mk_le_aleph0 (α := RationalBase.{u})).trans hμ), max_eq_left hμ]

theorem models (hCH : CH.{u}) (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) :
    ∃ R, AEC.Object (hCH := hCH) R ∧ R.carrier.card = μ := by
  refine ⟨Coding.coded (countableData μ hμ),
    ⟨Coding.codedPresentation _, countableData_object hCH μ hμ⟩, ?_⟩
  rw [Coding.coded_cardinal, countableData_cardinal]

end Existence

namespace Categoricity

theorem aleph_one_lt : (ℵ_ 1 : Cardinal.{u}) < tailThreshold.{u} :=
  (Cardinal.cantor _).trans ThresholdArithmetic.palette_lt

theorem index_eq (M : Data.{u}) {μ : Cardinal.{u}} (hμ : tailThreshold.{u} ≤ μ)
    (hM : #M.Carrier = μ) : #M.I = μ := by
  have hi : #M.I ≤ μ := (Cardinal.mk_le_of_injective (fun _ _ h => Point.index.inj h)).trans_eq hM
  apply le_antisymm hi
  by_contra! hn
  have hb : #M.B < μ := M.base_bound.trans_lt (aleph_one_lt.trans_le hμ)
  have hz : ℵ₀ < μ := (Cardinal.aleph0_le_aleph 1).trans_lt (aleph_one_lt.trans_le hμ)
  have hc := max_lt (max_lt hn hb) hz
  rw [← M.cardinal_eq, hM] at hc
  exact hc.false

theorem countable (M : Data.{u}) (hCH : CH.{u}) (ho : M.IsObject hCH)
    {μ : Cardinal.{u}} (hμ : tailThreshold.{u} ≤ μ) (hM : #M.Carrier = μ) : Countable M.B := by
  by_contra hn
  have hh := M.uncountable_index_bound hCH ho hn
  rw [index_eq M hμ hM] at hh
  exact hh.not_ge hμ

theorem tail (hCH : CH.{u}) (μ : Cardinal.{u}) (hμ : tailThreshold.{u} ≤ μ) :
    (classData hCH).Categorical μ := by
  refine ⟨Existence.models hCH μ
    ((Cardinal.aleph0_le_aleph 1).trans (aleph_one_lt.le.trans hμ)), ?_⟩
  intro R T hr ht hc hd
  obtain ⟨P, hp⟩ := hr
  obtain ⟨Q, hq⟩ := ht
  have hpc : #P.data.Carrier = μ := (Coding.cardinal P.equiv).trans hc
  have hqc : #Q.data.Carrier = μ := (Coding.cardinal Q.equiv).trans hd
  have := countable P.data hCH hp hμ hpc
  have := countable Q.data hCH hq hμ hqc
  obtain ⟨f, hi, hb⟩ := countable_isomorphic
    ((index_eq P.data hμ hpc).trans (index_eq Q.data hμ hqc).symm)
  exact ⟨P.isoOfMap Q f (f.surjective hi hb)⟩

end Categoricity

namespace EndpointModels

open Diagrams
open Existence

theorem base_le_endpoint : (ℵ_ 1 : Cardinal.{u}) ≤ endpoint.{u} := by
  apply (Cardinal.aleph.monotone (by norm_num : (1 : Ordinal.{u}) ≤ 2)).trans
  change ℵ_ 2 ≤ beth (ω_ 2)
  rw [← Cardinal.ord_aleph]
  exact Cardinal.le_beth_ord _

theorem data_colors (hCH : CH.{u}) (t : Tuples.Tuple EndpointDiagrams.D.{u}) (b : Base.{u}) :
    (data hCH).colors t b = EndpointDiagrams.colors hCH t (baseEquiv b) := by
  apply ULift.ext
  exact Colors.representative_color _

theorem object (hCH : CH.{u}) : (data hCH).IsObject hCH := by
  intro t
  have h := (EndpointDiagrams.countable_failures hCH t).preimage baseEquiv.injective
  apply h.mono
  intro b hb ht
  apply hb
  apply (Tests.congr hCH t (fun _ _ => data_colors hCH _ b)).mpr ht

theorem cardinal (hCH : CH.{u}) : #(data hCH).Carrier = endpoint.{u} := by
  rw [Data.cardinal_eq]
  change max (max #EndpointDiagrams.D.{u} #Base.{u}) ℵ₀ = endpoint.{u}
  rw [EndpointDiagrams.cardinal, base_cardinal, max_eq_left base_le_endpoint,
    max_eq_left endpoint_infinite]

theorem twoModels (hCH : CH.{u}) : (classData hCH).TwoModels endpoint.{u} := by
  let M := countableData endpoint endpoint_infinite
  let N := data hCH
  let P := Coding.codedPresentation M
  let Q := Coding.codedPresentation N
  refine ⟨Coding.coded M, Coding.coded N,
    ⟨P, countableData_object hCH endpoint endpoint_infinite⟩, ⟨Q, object hCH⟩, ?_, ?_, ?_⟩
  · rw [Coding.coded_cardinal]
    exact countableData_cardinal endpoint endpoint_infinite
  · rw [Coding.coded_cardinal]
    exact cardinal hCH
  · rintro ⟨e⟩
    let f := (P.transport e).comparison Q
    have : Countable (P.transport e).data.B := by change Countable RationalBase; infer_instance
    have : Countable N.B := f.base_surjective.countable
    have hc := Cardinal.mk_le_aleph0 (α := N.B)
    change #Base.{u} ≤ ℵ₀ at hc
    rw [base_cardinal] at hc
    exact (Cardinal.aleph0_lt_aleph.2 (by norm_num : (0 : Ordinal.{u}) < 1)).not_ge hc

end EndpointModels

end Arrays

theorem main (hCH : CH.{u}) :
    ∃ (L : ℕ → Type), Countable (Σ n, L n) ∧
      ∃ K : ClassData.{u} L, K.IsAEC ∧ K.HasLSNumber ℵ₀ ∧
        endpoint = hanf (ℵ₀ : Cardinal.{u}) ∧ K.TwoModels endpoint ∧
        ∀ μ, tailThreshold ≤ μ → K.Categorical μ := by
  refine ⟨Arrays.Language, Arrays.language_countable, Arrays.classData hCH,
    Arrays.AEC.isAEC, Arrays.AEC.hasLSNumber, ThresholdArithmetic.endpoint_eq_hanf hCH,
    Arrays.EndpointModels.twoModels hCH, Arrays.Categoricity.tail hCH⟩

end CHObstruction

end

end OAI

-- ---- mission target ----
open OAI OAI.CHObstruction
universe u
open Cardinal Ordinal Order

namespace OAI
namespace CHObstruction
theorem _root_.solution (hCH : CH.{u}) :
    ∃ (L : ℕ → Type), Countable (Σ n, L n) ∧
      ∃ K : ClassData.{u} L, K.IsAEC ∧ K.HasLSNumber ℵ₀ ∧
        endpoint = hanf (ℵ₀ : Cardinal.{u}) ∧ K.TwoModels endpoint ∧
        ∀ μ, tailThreshold ≤ μ → K.Categorical μ := by
  first
    | exact OAI.CHObstruction.main hCH
    | exact OAI.CHObstruction.main
    | (apply OAI.CHObstruction.main <;> assumption)
    | (intros; apply OAI.CHObstruction.main <;> assumption)
end CHObstruction
end OAI
