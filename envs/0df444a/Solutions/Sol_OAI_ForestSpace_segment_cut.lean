-- Prove2me | solution 1 for OAI.ForestSpace.segment_cut
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:35:21.845161+00:00
-- url     : https://prove2.me/submissions/01653cc1-0977-4709-aa74-d0808eddda2f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Paired.lean:L68-L117
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.segment_cut. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Theorems.Thm_OAI_ForestSpace_IsSegment_head_eq_before
import Theorems.Thm_OAI_ForestSpace_IsSegment_sdiff_before

-- ---- from OAI.Analysis.ForestSpace.Segments ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Basic
variable {V : Type} [PartialOrder V]

end Basic

section Geometry
variable {V : Type} [PartialOrder V]

 theorem IsSegment.endpoints {S : Finset V} (hS : IsSegment S) (hne : S.Nonempty) :
    ∃ a ∈ S, ∃ b ∈ S, ∀ v, v ∈ S ↔ a ≤ v ∧ v ≤ b := by
  obtain ⟨a, ha, hamin⟩ := S.exists_minimal hne
  obtain ⟨b, hb, hbmax⟩ := S.exists_maximal hne
  refine ⟨a, ha, b, hb, ?_⟩
  intro v
  constructor
  · intro hv
    exact ⟨(hS.1 a ha v hv).elim id (hamin hv),
      (hS.1 v hv b hb).elim id (hbmax hv)⟩
  · rintro ⟨hav, hvb⟩
    exact hS.2 a ha b hb v hav hvb

 theorem Gate.eq_of_le {H : Set V} {g h : V} (hg : Gate H g) (hh : Gate H h)
    (hgh : g ≤ h) : g = h := by
  by_contra hne
  exact hg.1 (hh.2 g (lt_of_le_of_ne hgh hne))

 theorem IsSegment.gate_unique {H : Set V} {S : Finset V} (hS : IsSegment S)
    {g h : V} (hg : Gate H g) (hh : Gate H h) (hgs : g ∈ S) (hhs : h ∈ S) : g = h := by
  rcases hS.1 g hgs h hhs with hgh | hhg
  · exact hg.eq_of_le hh hgh
  · exact (hh.eq_of_le hg hhg).symm

 theorem IsSegment.exists_gate (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {S : Finset V} (hS : IsSegment S)
    (hp : ∃ a ∈ S, a ∈ H) (hq : ∃ b ∈ S, b ∉ H) :
    ∃ g ∈ S, Gate H g := by
  classical
  obtain ⟨a, ha, haH⟩ := hp
  let T := S.filter (· ∉ H)
  have hne : T.Nonempty := by
    obtain ⟨b, hb, hbH⟩ := hq
    exact ⟨b, mem_filter.mpr ⟨hb, hbH⟩⟩
  obtain ⟨g, hg, hgmin⟩ := T.exists_minimal hne
  have hgs : g ∈ S := (mem_filter.mp hg).1
  have hgH : g ∉ H := (mem_filter.mp hg).2
  have hag : a ≤ g := (hS.1 a ha g hgs).resolve_right (fun h => hgH (hH h haH))
  refine ⟨g, hgs, hgH, ?_⟩
  intro v hvg
  rcases hF v a g hvg.le hag with hva | hav
  · exact hH hva haH
  · by_contra hvH
    have hvm : v ∈ T := mem_filter.mpr ⟨hS.2 a ha g hgs v hav hvg.le, hvH⟩
    exact (not_le_of_gt hvg) (hgmin hvm hvg.le)

omit [PartialOrder V] in
 theorem SupportedOn.segSum_filter [PartialOrder V] {u : V → ℝ} {H : Set V} (hu : SupportedOn u H)
    (S : Finset V) : segSum u (S.filter (· ∈ H)) = segSum u S := by
  classical
  simp only [segSum, Finset.sum_filter]
  apply sum_congr rfl
  intro v hv
  split_ifs with hh
  · rfl
  · exact (hu v hh).symm

omit [PartialOrder V] in
 theorem SupportedOn.segSum_eq_zero [PartialOrder V] {u : V → ℝ} {H : Set V} (hu : SupportedOn u H)
    {S : Finset V} (hS : ∀ v ∈ S, v ∉ H) : segSum u S = 0 := by
  exact sum_eq_zero fun v hv => hu v (hS v hv)

 theorem cross_zero_of_no_gate (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {f v : V → ℝ} (hf : SupportedOn f H) (hv : SupportedOn v Hᶜ)
    {S : Finset V} (hS : IsSegment S) (hg : ¬∃ g ∈ S, Gate H g) :
    segSum f S * segSum v S = 0 := by
  by_cases hp : ∃ a ∈ S, a ∈ H
  · have hq : ∀ b ∈ S, b ∈ H := by
      intro b hb
      by_contra hbH
      exact hg (hS.exists_gate hF hH hp ⟨b, hb, hbH⟩)
    have hz : segSum v S = 0 := hv.segSum_eq_zero (by simpa using hq)
    rw [hz, mul_zero]
  · have hz : segSum f S = 0 := hf.segSum_eq_zero (by simpa using hp)
    rw [hz, zero_mul]

end Geometry

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.FiniteGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FiniteGeometry
variable {V : Type} [Fintype V] [PartialOrder V]

 theorem isSegment_before (hF : ForestOrder V) (a g : V) : IsSegment (before a g) := by
  constructor
  · intro v hv w hw
    exact hF v w g (mem_before.mp hv).2.le (mem_before.mp hw).2.le
  · intro v hv w hw z hvz hzw
    exact mem_before.mpr ⟨(mem_before.mp hv).1.trans hvz,
      lt_of_le_of_lt hzw (mem_before.mp hw).2⟩

 theorem before_mono {a b g : V} (hab : a ≤ b) : before b g ⊆ before a g := by
  intro v hv
  exact mem_before.mpr ⟨hab.trans (mem_before.mp hv).1, (mem_before.mp hv).2⟩

 theorem IsSegment.tail_eq_along {H : Set V} (hH : IsLowerSet H)
    {S : Finset V} (hS : IsSegment S) {g : V} (hg : Gate H g) (hgs : g ∈ S) :
    ∃ b, S.filter (· ∉ H) = along g b := by
  obtain ⟨a, ha, b, hb, hab⟩ := hS.endpoints ⟨g, hgs⟩
  refine ⟨b, ?_⟩
  ext v
  simp only [mem_filter, mem_along]
  constructor
  · rintro ⟨hv, hvH⟩
    refine ⟨?_, ((hab v).mp hv).2⟩
    rcases hS.1 g hgs v hv with hgv | hvg
    · exact hgv
    · by_contra hngv
      exact hvH (hg.2 v (lt_of_le_not_ge hvg hngv))
  · rintro ⟨hgv, hvb⟩
    exact ⟨hS.2 g hgs b hb v hgv hvb, fun hv => hg.1 (hH hgv hv)⟩

 theorem abs_segSum_along_le (k : V → ℝ) (g w : V) :
    |segSum k (along g w)| ≤ mass k g :=
  le_sup' (fun w => |segSum k (along g w)|) (mem_univ w)

 theorem mass_nonneg (k : V → ℝ) (g : V) : 0 ≤ mass k g :=
  (abs_nonneg _).trans (abs_segSum_along_le k g g)

 theorem gateWeight_nonneg (H : Set V) (k : V → ℝ) (g : V) : 0 ≤ gateWeight H k g := by
  unfold gateWeight
  split_ifs <;> positivity

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

 theorem correction_supported (H : Set V) (k σ : V → ℝ) :
    SupportedOn (correction H k σ) Hᶜ := by
  intro v hv
  simp only [Set.mem_compl_iff, not_not] at hv
  exact ite_eq_right (fun hg => hg.1 hv)

 theorem correction_sum {H : Set V} {k σ : V → ℝ} {S : Finset V} (hS : IsSegment S)
    {g : V} (hg : Gate H g) (hgs : g ∈ S) :
    segSum (correction H k σ) S = σ g * mass k g := by
  rw [sum_gate_supported (c := correction H k σ) (fun v hv => ite_eq_right hv) hS hg hgs]
  exact ite_eq_left hg

 theorem tail_sum_le_mass {H : Set V} (hH : IsLowerSet H) {k : V → ℝ}
    (hk : SupportedOn k Hᶜ) {S : Finset V} (hS : IsSegment S)
    {g : V} (hg : Gate H g) (hgs : g ∈ S) : |segSum k S| ≤ mass k g := by
  obtain ⟨b, hb⟩ := hS.tail_eq_along hH hg hgs
  have he := hk.segSum_filter S
  simp only [Set.mem_compl_iff] at he
  rw [← he, hb]
  exact abs_segSum_along_le k g b

 theorem selectedStart_spec (f k : V → ℝ) (s : ℝ) (g : V)
    (h : (largeStarts f k s g).Nonempty) :
    Maximal (· ∈ largeStarts f k s g) (selectedStart f k s g h) :=
  Classical.choose_spec ((largeStarts f k s g).exists_maximal h)

 theorem selectedHead_segment (hF : ForestOrder V) (f k : V → ℝ) (s : ℝ) (g : V) :
    IsSegment (selectedHead f k s g) := by
  unfold selectedHead
  split_ifs
  · exact isSegment_before hF _ _
  · exact isSegment_empty

 theorem selectedHead_subset (hF : ForestOrder V) {f k : V → ℝ} {s : ℝ} {a g : V}
    (ha : a ∈ largeStarts f k s g) : selectedHead f k s g ⊆ before a g := by
  have hne : (largeStarts f k s g).Nonempty := ⟨a, ha⟩
  rw [selectedHead, dite_eq_left hne]
  apply before_mono
  have hb := selectedStart_spec f k s g hne
  exact (hF a (selectedStart f k s g hne) g
    (mem_largeStarts.mp ha).1.le (mem_largeStarts.mp hb.1).1.le).elim id (hb.2 ha)

 theorem selectedHead_large {f k : V → ℝ} {s : ℝ} {a g : V}
    (ha : a ∈ largeStarts f k s g) :
    2 * s * mass k g ≤ |segSum f (selectedHead f k s g)| := by
  have hne : (largeStarts f k s g).Nonempty := ⟨a, ha⟩
  rw [selectedHead, dite_eq_left hne]
  exact (mem_largeStarts.mp (selectedStart_spec f k s g hne).1).2

 theorem sdiff_selectedHead_segment {f k : V → ℝ} {s : ℝ} {a g : V}
    (hS : IsSegment (before a g)) : IsSegment (before a g \ selectedHead f k s g) := by
  unfold selectedHead
  split_ifs
  · exact hS.sdiff_before rfl
  · simpa using hS

end FiniteGeometry

section CrossTermAlgebra

 theorem abs_oppositeSign (r : ℝ) : |oppositeSign r| = 1 := by
  unfold oppositeSign
  split_ifs <;> norm_num

 theorem oppositeSign_cross {r m d : ℝ} (hd : |d| ≤ m) :
    r * (oppositeSign r * m + d) ≤ 0 := by
  have hd' := abs_le.mp hd
  unfold oppositeSign
  split_ifs with hr
  · exact mul_nonpos_of_nonpos_of_nonneg hr.le (by linarith)
  · exact mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt hr) (by linarith)

 theorem oppositeSign_tail_abs {r m d : ℝ} (hm : 0 ≤ m) (hd : |d| ≤ m) :
    |oppositeSign r * m + d| ≤ 2 * m := by
  calc
    |oppositeSign r * m + d| ≤ |oppositeSign r * m| + |d| := abs_add_le _ _
    _ ≤ m + m := by rw [abs_mul, abs_oppositeSign, abs_of_nonneg hm, one_mul]; linarith
    _ = 2 * m := by ring

 theorem small_cross_bound {a b s m q : ℝ} (hs : 0 ≤ s) (hm : 0 ≤ m)
    (ha : |a| ≤ 2 * s * m) (hb : |b| ≤ 2 * m) (hq : m ^ 2 ≤ q) :
    2 * s * a * b ≤ 8 * s ^ 2 * q := by
  have hab : a * b ≤ (2 * s * m) * (2 * m) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (by positivity))
  have h₁ := mul_le_mul_of_nonneg_left hab (show 0 ≤ 2 * s by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hq (show 0 ≤ 8 * s ^ 2 by positivity)
  nlinarith

 theorem cross_sign {a b r : ℝ} (hab : 0 < a * b) (hrb : r * b ≤ 0) : a * r ≤ 0 := by
  rcases lt_or_ge b 0 with hb | hb
  · have ha : a < 0 := (mul_pos_iff.mp hab).resolve_left (fun hh => not_lt_of_ge hb.le hh.2)
      |>.1
    have hr : 0 ≤ r := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hr
  · have hb' : 0 < b := lt_of_le_of_ne hb (by intro h; subst b; simp at hab)
    have ha : 0 < a := (mul_pos_iff.mp hab).resolve_right (fun hh => not_lt_of_ge hb hh.2)
      |>.1
    have hr : r ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hr

/-- A large positive cross term is paid for by splitting off the selected suffix. -/
 theorem large_cross_bound {a b r s m : ℝ} (hs : 0 ≤ s) (hm : 0 ≤ m)
    (hab : 0 < a * b) (hrb : r * b ≤ 0) (hr : 2 * s * m ≤ |r|)
    (hb : |b| ≤ 2 * m) :
    2 * s * a * b ≤ (a - r) ^ 2 + r ^ 2 - a ^ 2 := by
  have har := cross_sign hab hrb
  have h₁ : a * b ≤ |a| * (2 * m) :=
    (le_abs_self _).trans (by
      rw [abs_mul, mul_comm |a| |b|, mul_comm |a| (2 * m)]
      exact mul_le_mul hb le_rfl (abs_nonneg a) (mul_nonneg (by norm_num) hm))
  have h₂ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 * s by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * |a| by positivity)
  have he : |a| * |r| = -(a * r) := by rw [← abs_mul, abs_of_nonpos har]
  nlinarith [sq_nonneg r]

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

 theorem correctedTail_supported {H : Set V} {f k : V → ℝ}
    (hk : SupportedOn k Hᶜ) (s τ : ℝ) : SupportedOn (correctedTail H f k s τ) Hᶜ := by
  intro v hv
  change correction H k (gateSigns f k s) v + τ * k v = 0
  rw [correction_supported H k (gateSigns f k s) v hv, hk v hv]
  ring

 theorem correctedTail_at_gate {H : Set V} (hH : IsLowerSet H) {f k : V → ℝ}
    (hk : SupportedOn k Hᶜ) {s τ : ℝ} (hτ : |τ| ≤ 1)
    {S : Finset V} (hS : IsSegment S) {g : V} (hg : Gate H g) (hgs : g ∈ S) :
    segSum f (selectedHead f k s g) * segSum (correctedTail H f k s τ) S ≤ 0 ∧
    |segSum (correctedTail H f k s τ) S| ≤ 2 * mass k g := by
  have hd : |τ * segSum k S| ≤ mass k g := by
    rw [abs_mul]
    calc
      |τ| * |segSum k S| ≤ 1 * mass k g :=
        mul_le_mul hτ (tail_sum_le_mass hH hk hS hg hgs) (abs_nonneg _) zero_le_one
      _ = mass k g := one_mul _
  simp only [correctedTail, segSum_add, segSum_smul, correction_sum hS hg hgs, gateSigns]
  exact ⟨oppositeSign_cross hd, oppositeSign_tail_abs (mass_nonneg k g) hd⟩

 theorem gate_charge_le {H : Set V} {k : V → ℝ} {S : Finset V} {g : V}
    (hg : Gate H g) (hgs : g ∈ S) : mass k g ^ 2 ≤ ∑ v ∈ S, gateWeight H k v := by
  have hh := single_le_sum (f := gateWeight H k)
    (fun v hv => gateWeight_nonneg H k v) hgs
  simpa only [gateWeight, ite_eq_left hg] using hh

/-- The local choice of a suffix cut, including empty cuts for inexpensive terms. -/
 theorem segment_cut (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {f k : V → ℝ} (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    {s τ : ℝ} (hs : 0 ≤ s) (hτ : |τ| ≤ 1)
    {S : Finset V} (hS : IsSegment S) :
    ∃ L : Finset V, L ⊆ S.filter (· ∈ H) ∧ IsSegment L ∧
      IsSegment (S.filter (· ∈ H) \ L) ∧
      (segSum f S + s * segSum (correctedTail H f k s τ) S) ^ 2 ≤
        (segSum f S - segSum f L) ^ 2 + segSum f L ^ 2 +
        8 * s ^ 2 * (∑ v ∈ S, gateWeight H k v) +
        s ^ 2 * segSum (correctedTail H f k s τ) S ^ 2 := by
  have hq : 0 ≤ ∑ v ∈ S, gateWeight H k v := sum_nonneg (fun v hv => gateWeight_nonneg H k v)
  have hcost : 0 ≤ 8 * s ^ 2 * (∑ v ∈ S, gateWeight H k v) := by positivity
  by_cases hcross : 0 < segSum f S * segSum (correctedTail H f k s τ) S
  · have hgex : ∃ g ∈ S, Gate H g := by
      by_contra hng
      have hz := cross_zero_of_no_gate hF hH hf (correctedTail_supported (f := f) hk s τ) hS hng
      linarith
    obtain ⟨g, hgs, hg⟩ := hgex
    have hinfo := correctedTail_at_gate (f := f) (s := s) hH hk hτ hS hg hgs
    have hcharge := gate_charge_le (k := k) hg hgs
    by_cases hsmall : |segSum f S| ≤ 2 * s * mass k g
    · refine ⟨∅, empty_subset _, isSegment_empty, by simpa using hS.head H hH, ?_⟩
      have hc := small_cross_bound hs (mass_nonneg k g) hsmall hinfo.2 hcharge
      simp only [segSum_empty, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
      nlinarith
    · have hp : ∃ a ∈ S, a ∈ H := by
        by_contra hn
        have hz := hf.segSum_eq_zero (S := S) (by simpa using hn)
        rw [hz, zero_mul] at hcross
        exact (lt_irrefl 0) hcross
      obtain ⟨a, hag, hhead⟩ := hS.head_eq_before hH hg hgs hp
      have he : segSum f (before a g) = segSum f S := by
        rw [← hhead]
        exact hf.segSum_filter S
      have ha : a ∈ largeStarts f k s g := mem_largeStarts.mpr
        ⟨hag, by rw [he]; exact le_of_lt (lt_of_not_ge hsmall)⟩
      refine ⟨selectedHead f k s g, ?_, selectedHead_segment hF f k s g, ?_, ?_⟩
      · rw [hhead]
        exact selectedHead_subset hF ha
      · rw [hhead]
        exact sdiff_selectedHead_segment (isSegment_before hF a g)
      · have hc := large_cross_bound hs (mass_nonneg k g) hcross hinfo.1
          (selectedHead_large ha) hinfo.2
        nlinarith
  · refine ⟨∅, empty_subset _, isSegment_empty, by simpa using hS.head H hH, ?_⟩
    have hc : 2 * s * (segSum f S * segSum (correctedTail H f k s τ) S) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hcross)
    simp only [segSum_empty, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
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


theorem solution : type_of% @_root_.OAI.ForestSpace.segment_cut := @_root_.OAI.ForestSpace.segment_cut
