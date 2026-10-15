-- Prove2me | solution 1 for OAI.ForestSpace.corrected_test_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:38:10.385804+00:00
-- url     : https://prove2.me/submissions/8c3a51be-66e7-4288-908b-c20aa0b6e8b6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Paired.lean:L160-L177
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.corrected_test_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Theorems.Thm_OAI_ForestSpace_TestBound_add
import Theorems.Thm_OAI_ForestSpace_segment_cut
import Theorems.Thm_OAI_ForestSpace_simultaneous_cut_bound

-- ---- from OAI.Analysis.ForestSpace.Segments ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Basic
variable {V : Type} [PartialOrder V]

 theorem TestBound.smul {u : V → ℝ} {C : ℝ} (h : TestBound u C) (a : ℝ) :
    TestBound (a • u) (a ^ 2 * C) := by
  intro ι inst S hS hd
  have hh := mul_le_mul_of_nonneg_left (h ι inst S hS hd) (sq_nonneg a)
  simpa only [segSum_smul, mul_pow, Finset.mul_sum] using hh

end Basic

section Geometry
variable {V : Type} [PartialOrder V]

 theorem Gate.eq_of_le {H : Set V} {g h : V} (hg : Gate H g) (hh : Gate H h)
    (hgh : g ≤ h) : g = h := by
  by_contra hne
  exact hg.1 (hh.2 g (lt_of_le_of_ne hgh hne))

 theorem IsSegment.gate_unique {H : Set V} {S : Finset V} (hS : IsSegment S)
    {g h : V} (hg : Gate H g) (hh : Gate H h) (hgs : g ∈ S) (hhs : h ∈ S) : g = h := by
  rcases hS.1 g hgs h hhs with hgh | hhg
  · exact hg.eq_of_le hh hgh
  · exact (hh.eq_of_le hg hhg).symm

end Geometry

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.FiniteGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FiniteGeometry
variable {V : Type} [Fintype V] [PartialOrder V]

 theorem isSegment_along (hF : ForestOrder V) (g w : V) : IsSegment (along g w) := by
  constructor
  · intro a ha b hb
    exact hF a b w (mem_along.mp ha).2 (mem_along.mp hb).2
  · intro a ha b hb c hac hcb
    exact mem_along.mpr ⟨(mem_along.mp ha).1.trans hac, hcb.trans (mem_along.mp hb).2⟩

 theorem mass_attained (k : V → ℝ) (g : V) :
    ∃ w, mass k g = |segSum k (along g w)| := by
  obtain ⟨w, hw, he⟩ := exists_mem_eq_sup' (⟨g, mem_univ g⟩ : (univ : Finset V).Nonempty)
    (fun w => |segSum k (along g w)|)
  exact ⟨w, he⟩

 theorem gate_mass_bound (hF : ForestOrder V) {k : V → ℝ} (hk : TestBound k 1)
    (H : Set V) : ∑ g : {g // Gate H g}, mass k g ^ 2 ≤ 1 := by
  choose w hw using (fun g : {g // Gate H g} => mass_attained k g)
  have hd : Pairwise (fun g h : {g // Gate H g} => Disjoint (along (g : V) (w g)) (along (h : V) (w h))) := by
    intro g h hne
    apply disjoint_left.mpr
    intro v hvg hvh
    have hcomp := hF g h v (mem_along.mp hvg).1 (mem_along.mp hvh).1
    apply hne
    apply Subtype.ext
    exact hcomp.elim (g.property.eq_of_le h.property) (fun hle => (h.property.eq_of_le g.property hle).symm)
  have hh := hk {g // Gate H g} inferInstance (fun g => along (g : V) (w g))
    (fun g => isSegment_along hF g (w g)) hd
  simpa only [hw, sq_abs] using hh

 theorem gateWeight_nonneg (H : Set V) (k : V → ℝ) (g : V) : 0 ≤ gateWeight H k g := by
  unfold gateWeight
  split_ifs <;> positivity

 theorem gateWeight_sum_le (hF : ForestOrder V) {k : V → ℝ} (hk : TestBound k 1)
    (H : Set V) : ∑ g, gateWeight H k g ≤ 1 := by
  have he : (∑ g, gateWeight H k g) = ∑ g : {g // Gate H g}, mass k g ^ 2 := by
    rw [← sum_subtype (p := Gate H) (univ.filter (Gate H)) (by simp)
      (fun g => mass k g ^ 2)]
    simp only [gateWeight, sum_filter]
  rw [he]
  exact gate_mass_bound hF hk H

omit [Fintype V] [PartialOrder V] in
 theorem disjoint_sum_le [Fintype V] [PartialOrder V] {ι : Type} [Fintype ι] (S : ι → Finset V)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (q : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
    (∑ i, ∑ v ∈ S i, q v) ≤ ∑ v, q v := by
  rw [← sum_biUnion (s := univ) (t := S) (by intro i hi j hj hij; exact hd hij)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intro v hv hv'; exact hq v)

 theorem gateWeight_family_le (hF : ForestOrder V) {k : V → ℝ} (hk : TestBound k 1)
    (H : Set V) {ι : Type} [Fintype ι] (S : ι → Finset V)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    (∑ i, ∑ v ∈ S i, gateWeight H k v) ≤ 1 :=
  (disjoint_sum_le S hd _ (gateWeight_nonneg H k)).trans (gateWeight_sum_le hF hk H)

omit [Fintype V] [PartialOrder V] in
/-- A segment contains at most one coordinate of a gate-supported vector. -/
 theorem sum_gate_supported [Fintype V] [PartialOrder V] {H : Set V} {c : V → ℝ}
    (hc : ∀ v, ¬ Gate H v → c v = 0) {S : Finset V} (hS : IsSegment S)
    {g : V} (hg : Gate H g) (hgs : g ∈ S) : segSum c S = c g := by
  apply sum_eq_single g
  · intro v hv hvg
    apply hc v
    intro hgate
    exact hvg (hS.gate_unique hgate hg hv hgs)
  · exact fun h => (h hgs).elim

 theorem correction_sum {H : Set V} {k σ : V → ℝ} {S : Finset V} (hS : IsSegment S)
    {g : V} (hg : Gate H g) (hgs : g ∈ S) :
    segSum (correction H k σ) S = σ g * mass k g := by
  rw [sum_gate_supported (c := correction H k σ) (fun v hv => ite_eq_right hv) hS hg hgs]
  exact ite_eq_left hg

 theorem correction_segment_sq {H : Set V} {k σ : V → ℝ} (hσ : ∀ v, σ v ^ 2 = 1)
    {S : Finset V} (hS : IsSegment S) :
    segSum (correction H k σ) S ^ 2 = ∑ v ∈ S, gateWeight H k v := by
  by_cases h : ∃ g ∈ S, Gate H g
  · obtain ⟨g, hgs, hg⟩ := h
    rw [correction_sum hS hg hgs, mul_pow, hσ, one_mul]
    symm
    calc
      (∑ v ∈ S, gateWeight H k v) = gateWeight H k g := by
        apply sum_eq_single g
        · intro v hv hvg
          exact ite_eq_right (fun hgate => hvg (hS.gate_unique hgate hg hv hgs))
        · exact fun hn => (hn hgs).elim
      _ = mass k g ^ 2 := ite_eq_left hg
  · have hz : segSum (correction H k σ) S = 0 := by
      apply sum_eq_zero
      intro v hv
      exact ite_eq_right (fun hg => h ⟨v, hv, hg⟩)
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    symm
    apply sum_eq_zero
    intro v hv
    exact ite_eq_right (fun hg => h ⟨v, hv, hg⟩)

 theorem correction_testBound (hF : ForestOrder V) {k σ : V → ℝ} (hk : TestBound k 1)
    (hσ : ∀ v, σ v ^ 2 = 1) (H : Set V) : TestBound (correction H k σ) 1 := by
  intro ι inst S hS hd
  simp_rw [correction_segment_sq hσ (hS _)]
  exact gateWeight_family_le hF hk H S hd

end FiniteGeometry

section CrossTermAlgebra

 theorem oppositeSign_sq (r : ℝ) : oppositeSign r ^ 2 = 1 := by
  unfold oppositeSign
  split_ifs <;> norm_num

end CrossTermAlgebra

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.Paired ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePaired
variable {V : Type} [Fintype V] [PartialOrder V]

 theorem gateSigns_sq (f k : V → ℝ) (s : ℝ) (g : V) : gateSigns f k s g ^ 2 = 1 :=
  oppositeSign_sq _

 theorem correctedTail_testBound (hF : ForestOrder V) (H : Set V) (f k : V → ℝ)
    (hk : TestBound k 1) (s τ : ℝ) (hτ : |τ| ≤ 1) :
    TestBound (correctedTail H f k s τ) 4 := by
  have ht : τ ^ 2 ≤ 1 := by
    have := abs_le.mp hτ
    nlinarith [sq_abs τ]
  have hk' : TestBound (τ • k) 1 := (hk.smul τ).mono (by simpa using ht)
  have hc := correction_testBound hF hk (gateSigns_sq f k s) H
  have hh := TestBound.add (A := 1) (B := 1) (by simpa using hc) (by simpa using hk')
    zero_le_one zero_le_one
  convert hh using 1 <;> norm_num [correctedTail]

/-- The corrected tests have squared norm at most 1+12s², for either sign. -/
 theorem corrected_test_bound (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {f k : V → ℝ} (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hf₁ : TestBound f 1) (hk₁ : TestBound k 1)
    {s τ : ℝ} (hs : 0 ≤ s) (hτ : |τ| ≤ 1) :
    TestBound (f + s • correctedTail H f k s τ) (1 + 12 * s ^ 2) := by
  intro ι inst S hS hd
  choose L hL hseg hdiff hlocal using (fun i => segment_cut hF hH hf hk hs hτ (hS i))
  have hhead := simultaneous_cut_bound hf hf₁ S L hd hL hseg hdiff
  have hcharge := gateWeight_family_le hF hk₁ H S hd
  have htail := correctedTail_testBound hF H f k hk₁ s τ hτ ι inst S hS hd
  have hnum := sum_le_sum (s := (univ : Finset ι)) (fun i hi => hlocal i)
  simp only [sum_add_distrib, ← mul_sum] at hnum
  have hcharge' := mul_le_mul_of_nonneg_left hcharge (show 0 ≤ 8 * s ^ 2 by positivity)
  have htail' := mul_le_mul_of_nonneg_left htail (sq_nonneg s)
  simp only [sum_add_distrib] at hhead
  simp only [segSum_add, segSum_smul]
  nlinarith

end FinitePaired

section FiniteRestriction
variable {V : Type} [PartialOrder V]

end FiniteRestriction

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.corrected_test_bound := @_root_.OAI.ForestSpace.corrected_test_bound
