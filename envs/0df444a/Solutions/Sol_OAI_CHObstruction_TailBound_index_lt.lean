-- Prove2me | solution 1 for OAI.CHObstruction.TailBound.index_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:23:50.764302+00:00
-- url     : https://prove2.me/submissions/6aadd8e0-a5ad-4204-b36e-38e61744f96c

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/TailBound.lean:L93-L125
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.TailBound.index_lt. The node keeps its source
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
import Theorems.Thm_OAI_CHObstruction_Tests_no_pattern

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

theorem palette_infinite : ℵ₀ ≤ ξ.{u} :=
  (aleph0_le_aleph 1).trans (Cardinal.cantor _).le

theorem palette_lt : ξ.{u} < tailThreshold.{u} :=
  (lt_succ ξ).trans_le (Cardinal.le_beth_ord _)

theorem index_limit : IsSuccLimit (succ ξ.{u}).ord :=
  Cardinal.isSuccLimit_ord (palette_infinite.trans (le_succ ξ))

theorem strongLimit : tailThreshold.{u}.IsStrongLimit :=
  Cardinal.isStrongLimit_beth.2 index_limit.isSuccPrelimit

theorem cofinality : tailThreshold.{u}.ord.cof = succ ξ.{u} := by
  change ((Cardinal.ord ∘ Cardinal.beth) (succ ξ).ord).cof = succ ξ
  rw [Ordinal.cof_map_of_isNormal (Cardinal.isNormal_ord.comp Cardinal.isNormal_beth) index_limit]
  exact (Cardinal.isRegular_succ palette_infinite).cof_ord

theorem palette_lt_cofinality : ξ.{u} < tailThreshold.{u}.ord.cof := by
  rw [cofinality]
  exact lt_succ _

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

theorem states_agree (n j : ℕ) (hj : j < n) :
    (states Λ ξ c hΛ hξinf hξ hcof hC hX n).val j =
      colors Λ ξ c hΛ hξinf hξ hcof hC hX j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
    · change Function.update _ n _ j = _
      rw [Function.update_of_ne h.ne]
      exact ih h
    · rfl

theorem colors_unbounded (n : ℕ) :
    Unbounded Λ c n (colors Λ ξ c hΛ hξinf hξ hcof hC hX) := by
  intro χ hχ
  obtain ⟨Y, hY, hp⟩ := (states Λ ξ c hΛ hξinf hξ hcof hC hX n).property χ hχ
  refine ⟨Y, hY, ?_⟩
  intro j hj
  rw [← states_agree Λ ξ c hΛ hξinf hξ hcof hC hX n j hj]
  exact hp j hj

include hΛ hξinf hξ hcof hC hX in

theorem exists_patterns :
    ∃ p : ℕ → C, ∀ k : ℕ, ∃ A : Finset X, A.card = k ∧
      ∀ j ≤ k, ∀ s ⊆ A, s.card = j → c j s = p j := by
  classical
  refine ⟨colors Λ ξ c hΛ hξinf hξ hcof hC hX, ?_⟩
  intro k
  obtain ⟨Y, hY, hp⟩ := colors_unbounded Λ ξ c hΛ hξinf hξ hcof hC hX
    (k + 1) ℵ₀ (hξinf.trans_lt hξ)
  have hi : Infinite Y := Cardinal.aleph0_le_mk_iff.1 hY
  obtain ⟨A, hA, hc⟩ := (Set.infinite_coe_iff.1 hi).exists_subset_card_eq k
  refine ⟨A, hc, ?_⟩
  intro j hj s hs hsc
  exact hp j (Nat.lt_succ_of_le hj) s ((Finset.coe_subset.2 hs).trans hA) hsc

end FinitePatterns

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.TailBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace TuplePatterns

open Tuples

variable {I : Type u} [LinearOrder I]

omit [LinearOrder I] in
theorem sub_support (t : Tuple I) {m : ℕ} (e : Fin (m + 1) ↪o Fin (t.1 + 1)) :
    support (sub t e) ⊆ support t := by
  change Finset.univ.map (e.toEmbedding.trans t.2) ⊆ Finset.univ.map t.2
  rw [← Finset.map_map]
  exact Finset.map_subset_map.mpr (Finset.subset_univ _)

theorem sub_sorted (s : Finset I) {n m : ℕ} (hs : s.card = n + 1)
    (e : Fin (m + 1) ↪o Fin (n + 1)) :
    sub (sorted s hs) e = sorted (support (sub (sorted s hs) e)) (support_card _) := by
  apply congrArg (Sigma.mk m)
  apply Function.Embedding.ext
  have h := Finset.orderEmbOfFin_unique' (support_card (sub (sorted s hs) e))
    (f := e.trans (s.orderEmbOfFin hs)) (fun x => Finset.mem_map.2 ⟨x, Finset.mem_univ _, rfl⟩)
  exact congrFun (congrArg (fun f : Fin (m + 1) ↪o I => (f : Fin (m + 1) → I)) h)

variable {C : Type u}

theorem setColor_sorted (c : Tuple I → C) (p0 : C) (s : Finset I) {n : ℕ}
    (hs : s.card = n + 1) : setColor c p0 s = c (sorted s hs) := by
  have hn : s.card ≠ 0 := by omega
  rw [setColor, dite_eq_left hn]
  have he : s.card - 1 = n := by omega
  subst n
  rfl

theorem sub_color (c : Tuple I → C) (p0 : C) (p : ℕ → C) (s : Finset I)
    {n : ℕ} (hs : s.card = n + 1)
    (hp : ∀ j ≤ n + 1, ∀ r ⊆ s, r.card = j → setColor c p0 r = p j)
    {m : ℕ} (e : Fin (m + 1) ↪o Fin (n + 1)) :
    c (sub (sorted s hs) e) = p (m + 1) := by
  have hm : m + 1 ≤ n + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  have hsub : support (sub (sorted s hs) e) ⊆ s := by
    simpa only [support_sorted] using sub_support (sorted s hs) e
  rw [sub_sorted]
  rw [← setColor_sorted c p0]
  exact hp (m + 1) hm _ hsub (support_card _)

end TuplePatterns

namespace TailBound

open Tuples Diagrams Colors Tests ThresholdArithmetic

variable {I B : Type u} (hCH : CH.{u})

theorem profile_cardinal (hB : #B ≤ (ℵ_ 1 : Cardinal.{u})) : #(B → Palette.{u}) ≤ ξ.{u} := by
  rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id, palette_cardinal, ← Cardinal.two_power_aleph0]
  apply (Cardinal.power_le_power_left (by simpa only [Cardinal.two_power_aleph0] using Cardinal.continuum_ne_zero) hB).trans_eq
  rw [← Cardinal.power_mul, Cardinal.mul_eq_right (Cardinal.aleph0_le_aleph 1)
    (Cardinal.aleph0_le_aleph 1) Cardinal.aleph0_ne_zero]
  rfl

theorem index_lt (hB : #B ≤ (ℵ_ 1 : Cardinal.{u})) (hunc : ¬ Countable B)
    (c : Tuple I → B → Palette.{u})
    (hbad : ∀ t, {b | ¬ Test hCH (fun t => c t b) t}.Countable) :
    #I < tailThreshold.{u} := by
  classical
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  by_contra! hI
  let p0 : B → Palette.{u} := fun _ => ⟨color (fun _ => false)⟩
  obtain ⟨p, hp⟩ := FinitePatterns.exists_patterns tailThreshold ξ
    (fun _ => TuplePatterns.setColor c p0) strongLimit palette_infinite palette_lt
    palette_lt_cofinality (profile_cardinal hB) hI
  choose A hcard hA using (fun n => hp (n + 1))
  let t : ℕ → Tuple I := fun n => TuplePatterns.sorted (A n) (hcard n)
  have hcount : (⋃ n, {b | ¬ Test hCH (fun t => c t b) (t n)}).Countable :=
    Set.countable_iUnion (fun n => hbad (t n))
  obtain ⟨b, hb⟩ : ∃ b : B, b ∉ ⋃ n, {b | ¬ Test hCH (fun t => c t b) (t n)} := by
    by_contra! hn
    apply hunc
    apply Set.countable_univ_iff.1
    exact hcount.mono (fun b _ => hn b)
  have hb' : ∀ n, Test hCH (fun t => c t b) (t n) := by
    intro n
    exact not_not.mp (fun hn => hb (Set.mem_iUnion.2 ⟨n, hn⟩))
  apply Tests.no_pattern hCH (fun n => p (n + 1) b)
  intro n
  have httest := hb' n
  change Passes hCH (n := n) (fun m e => c (sub (t n) e) b) at httest
  obtain ⟨d, hd⟩ := httest
  refine ⟨d, ?_⟩
  intro m e
  refine ⟨(hd m e).1, ?_⟩
  rw [(hd m e).2]
  exact congrFun (TuplePatterns.sub_color c p0 p (A n) (hcard n) (hA n) e) b

end TailBound

namespace BaseOrders

variable {B : Type u} [LinearOrder B]

end BaseOrders

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.TailBound
open Cardinal Ordinal Order
open Tuples Diagrams Colors Tests ThresholdArithmetic


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.TailBound.index_lt.{u} := @_root_.OAI.CHObstruction.TailBound.index_lt.{u}
