-- Prove2me | solution 1 for OAI.LipschitzHilbert.laceyLiInput_proved
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:08:55.271552+00:00
-- url     : https://prove2.me/submissions/8452959e-8572-4840-bb2e-fe5b97dc92b8

import Mathlib
import Definitions.Def_LipschitzHilbert
import Definitions.Def_OAIQ090A002

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BinaryDensityBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite binary subdivision used for the far-group mass estimate.
A bad child is bounded using its good parent; good children are subdivided
until the terminal scale. -/
noncomputable section
open scoped ENNReal
namespace LipschitzHilbert

theorem binary_density_bound (M V : ℝ → ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (good : ℕ → ℝ → ℝ → Prop)
    (hM : ∀ c l, 0 < l → M c l = M (c-l/4) (l/2)+M (c+l/4) (l/2))
    (hV : ∀ c l, 0 < l → V c l = V (c-l/4) (l/2)+V (c+l/4) (l/2))
    (hzero : ∀ c l, 0 < l → good 0 c l → M c l ≤ C*V c l)
    (hbad : ∀ n c l, 0 < l → good (n+1) c l → ∀ b,
      ¬good n (binaryChildCenter c l b) (l/2) →
        M (binaryChildCenter c l b) (l/2) ≤ C*V (binaryChildCenter c l b) (l/2)) :
    ∀ n c l, 0 < l → good n c l → M c l ≤ C*V c l := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    intro c l hl hg
    have hchild (b : Bool) : M (binaryChildCenter c l b) (l/2) ≤
        C*V (binaryChildCenter c l b) (l/2) := by
      by_cases hb : good n (binaryChildCenter c l b) (l/2)
      · exact ih _ _ (half_pos hl) hb
      · exact hbad n c l hl hg b hb
    rw [hM c l hl,hV c l hl,mul_add]
    exact add_le_add (hchild false) (hchild true)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_DyadicLineGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nested alternating one-third grids in the line-counting argument. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

theorem cell_length (q k j : ℤ) : MeasureTheory.volume.real (cell q k j) = scale k := by
  rw [cell, Real.volume_real_Ico_of_le]
  · unfold left
    push_cast
    ring
  · unfold left
    have hs := scale_pos k
    push_cast
    nlinarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LaminarWeakL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weak L1 covering estimate for a ranked laminar family. Applied
below only to squares in the product of two fixed dyadic grids. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

variable {ι X : Type*}

theorem ranked_disjoint_cover (Q : ι → Set X) (rank : ι → ℤ)
    (hnest : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (s : Finset ι) : ∃ t : Finset ι, t ⊆ s ∧ (t : Set ι).PairwiseDisjoint Q ∧
      (⋃ i ∈ s, Q i) = ⋃ i ∈ t, Q i := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s = ∅
    · subst s
      exact ⟨∅,by simp,by simp,by simp⟩
    obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image s rank (Finset.nonempty_iff_ne_empty.mpr hs)
    let r := s.filter (fun j => j ≠ i ∧ Disjoint (Q i) (Q j))
    have hrs : r ⊆ s := Finset.filter_subset _ _
    have hri : i ∉ r := by
      intro hir
      exact (Finset.mem_filter.mp hir).2.1 rfl
    have hstrict : r ⊂ s := (ssubset_iff_subset_ne).mpr ⟨hrs,fun he => hri (he.symm ▸ hi)⟩
    obtain ⟨t,ht,hdisj,hcover⟩ := ih r hstrict
    refine ⟨insert i t,Finset.insert_subset hi (ht.trans hrs),?_,?_⟩
    · intro a ha b hb hab
      by_cases hai : a = i
      · subst a
        have hbt : b ∈ t := (Finset.mem_insert.mp hb).resolve_left (Ne.symm hab)
        exact (Finset.mem_filter.mp (ht hbt)).2.2
      · have hat : a ∈ t := (Finset.mem_insert.mp ha).resolve_left hai
        by_cases hbi : b = i
        · subst b
          exact ((Finset.mem_filter.mp (ht hat)).2.2).symm
        · exact hdisj hat ((Finset.mem_insert.mp hb).resolve_left hbi) hab
    · apply Subset.antisymm
      · intro x hx
        obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx
        by_cases hji : j = i
        · subst j
          exact mem_iUnion₂.mpr ⟨i,Finset.mem_insert_self _ _,hxj⟩
        by_cases hd : Disjoint (Q i) (Q j)
        · have hxr : x ∈ ⋃ j ∈ r, Q j := mem_iUnion₂.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hji,hd⟩,hxj⟩
          obtain ⟨k,hk,hxk⟩ := mem_iUnion₂.mp (hcover ▸ hxr)
          exact mem_iUnion₂.mpr ⟨k,Finset.mem_insert_of_mem hk,hxk⟩
        · have hint : (Q i ∩ Q j).Nonempty := not_disjoint_iff_nonempty_inter.mp hd
          exact mem_iUnion₂.mpr ⟨i,Finset.mem_insert_self _ _,hnest i j (hmax j hj) hint hxj⟩
      · intro x hx
        obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨j,(Finset.insert_subset hi (ht.trans hrs)) hj,hxj⟩

variable [MeasurableSpace X]

theorem ranked_finite_weak_bound (μ : Measure X) (Q : ι → Set X) (rank : ι → ℤ)
    (hm : ∀ i, MeasurableSet (Q i))
    (hnest : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (f : X → ℝ≥0∞) (c : ℝ≥0∞) (s : Finset ι)
    (hgood : ∀ i ∈ s, c * μ (Q i) ≤ ∫⁻ x in Q i, f x ∂μ) :
    c * μ (⋃ i ∈ s, Q i) ≤ ∫⁻ x, f x ∂μ := by
  obtain ⟨t,ht,hd,heq⟩ := ranked_disjoint_cover Q rank hnest s
  rw [heq,measure_biUnion_finset hd (fun i _ => hm i),Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ t, ∫⁻ x in Q i, f x ∂μ := Finset.sum_le_sum (fun i hi => hgood i (ht hi))
    _ = ∫⁻ x in ⋃ i ∈ t, Q i, f x ∂μ :=
      (lintegral_biUnion_finset hd (fun i _ => hm i) f).symm
    _ ≤ ∫⁻ x, f x ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl

theorem ranked_countable_weak_bound [Countable ι] (μ : Measure X) (Q : ι → Set X)
    (rank : ι → ℤ) (hm : ∀ i, MeasurableSet (Q i))
    (hnest : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (f : X → ℝ≥0∞) (c : ℝ≥0∞)
    (hgood : ∀ i, c * μ (Q i) ≤ ∫⁻ x in Q i, f x ∂μ) :
    c * μ (⋃ i, Q i) ≤ ∫⁻ x, f x ∂μ := by
  classical
  have heq : (⋃ i, Q i) = ⋃ s : Finset ι, ⋃ i ∈ s, Q i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨{i},by simpa using hi⟩
    · intro hx
      obtain ⟨s,hs⟩ := mem_iUnion.mp hx
      obtain ⟨i,_,hi⟩ := mem_iUnion₂.mp hs
      exact mem_iUnion.mpr ⟨i,hi⟩
  have hmono : Monotone (fun s : Finset ι => ⋃ i ∈ s, Q i) := by
    intro s t hst x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨i,hst hi,hxi⟩
  rw [heq,hmono.measure_iUnion,ENNReal.mul_iSup]
  exact iSup_le (fun s => ranked_finite_weak_bound μ Q rank hm hnest f c s (fun i _ => hgood i))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SourceThreeGridCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal three-grid covering lemma for the nested alternating
one-third grids. It supplies the interval comparison in the maximal
kernel estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert.DyadicLineGrid

theorem shift_signed_third (k : ℤ) : shift (k.negOnePow:ℤ) k=1/3 := by
  simp only [shift,←Units.val_mul,Int.units_mul_self,Units.val_one,Int.cast_one]

theorem signed_third_in_range (k : ℤ) : (k.negOnePow:ℤ)∈Finset.Icc (-1) 1 := by
  rw [Finset.mem_Icc]
  exact abs_le.mp (le_of_eq (Int.abs_negOnePow k))

/-- A closed interval of radius less than one sixth of a grid cell
fits in a cell of one of the three fixed nested grids. -/
theorem exists_three_grid_cover (k : ℤ) (c r : ℝ) (_hr : 0 ≤ r)
    (hsmall : 6*r < scale k) :
    ∃ q∈Finset.Icc (-1) 1, ∃ j : ℤ, Icc (c-r) (c+r)⊆cell q k j := by
  let m := index 0 k c
  let a := left 0 k m
  have hc := mem_index_cell 0 k c
  have hright : left 0 k (m+1)=a+scale k := by
    dsimp [a,left,shift]
    push_cast
    ring
  change a ≤ c ∧ c<left 0 k (m+1) at hc
  rw [hright] at hc
  by_cases hleft : a ≤ c-r
  · by_cases hend : c+r<a+scale k
    · refine ⟨0,by simp, m,?_⟩
      intro x hx
      exact ⟨hleft.trans hx.1,hx.2.trans_lt (by simpa only [hright] using hend)⟩
    · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m,?_⟩
      intro x hx
      change left (k.negOnePow:ℤ) k m≤x ∧ x<left (k.negOnePow:ℤ) k (m+1)
      have hl : left (k.negOnePow:ℤ) k m=a+scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      have hu : left (k.negOnePow:ℤ) k (m+1)=a+4*scale k/3 := by
        simp only [left,shift_signed_third]
        dsimp [a,left,shift]
        push_cast
        ring
      rw [hl,hu]
      constructor <;> linarith [hx.1,hx.2]
  · refine ⟨(k.negOnePow:ℤ),signed_third_in_range k,m-1,?_⟩
    intro x hx
    change left (k.negOnePow:ℤ) k (m-1)≤x ∧
      x<left (k.negOnePow:ℤ) k (m-1+1)
    have hl : left (k.negOnePow:ℤ) k (m-1)=a-2*scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    have hu : left (k.negOnePow:ℤ) k (m-1+1)=a+scale k/3 := by
      simp only [left,shift_signed_third]
      dsimp [a,left,shift]
      push_cast
      ring
    rw [hl,hu]
    constructor <;> linarith [hx.1,hx.2]

/-- The covering cell has length at most six times the interval length. -/
theorem exists_comparable_three_grid_cover (c r : ℝ) (hr : 0 < r) :
    ∃ q∈Finset.Icc (-1) 1, ∃ k j : ℤ,
      Icc (c-r) (c+r)⊆cell q k j ∧ scale k≤12*r := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow
    (show 0<12*r by positivity) (by norm_num : (1:ℝ)<2)
  change scale k≤12*r at hlo
  change 12*r < scale (k+1) at hhi
  rw [scale_succ] at hhi
  obtain ⟨q,hq,j,hcell⟩ := exists_three_grid_cover k c r hr.le (by linarith)
  exact ⟨q,hq,k,j,hcell,hlo⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_SourceThreeGridMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual interval maximal majorant built from three nested grids.
The exceptional set is independent of the real interval parameters. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem gridChoice_card : Fintype.card GridChoice=3 := by
  simp [GridChoice]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_DyadicSquareWeakL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All-scale square averages in a fixed pair of dyadic grids. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem squareCell_measurable (qx qy : ℤ) (p : SquareIndex) :
    MeasurableSet (squareCell qx qy p) :=
  (cell_measurable _ _ _).prod (cell_measurable _ _ _)

theorem cell_volume (q k j : ℤ) : volume (cell q k j) = ENNReal.ofReal (scale k) := by
  rw [←cell_length q k j]
  exact (ENNReal.ofReal_toReal measure_Ico_lt_top.ne).symm

theorem squareCell_volume (qx qy : ℤ) (p : SquareIndex) :
    (volume.prod volume) (squareCell qx qy p) = ENNReal.ofReal ((scale p.1)^2) := by
  rw [squareCell,Measure.prod_prod,cell_volume,cell_volume,←ENNReal.ofReal_mul (scale_pos _).le]
  congr 1
  ring

theorem squareCell_ranked (qx qy : ℤ) (p q : SquareIndex) (h : q.1 ≤ p.1)
    (hint : (squareCell qx qy p ∩ squareCell qx qy q).Nonempty) :
    squareCell qx qy q ⊆ squareCell qx qy p := by
  obtain ⟨z,hz1,hz2⟩ := hint
  exact Set.prod_mono
    (cell_subset_of_intersect h ⟨z.1,hz2.1,hz1.1⟩)
    (cell_subset_of_intersect h ⟨z.2,hz2.2,hz1.2⟩)

theorem gridSquareSup_measurable (qx qy : ℤ) (f : ℝ × ℝ → ℝ≥0∞) :
    Measurable (gridSquareSup qx qy f) :=
  Measurable.iSup (fun p => measurable_const.indicator (squareCell_measurable qx qy p))

theorem square_average_le_gridSquareSup (qx qy : ℤ) (f : ℝ × ℝ → ℝ≥0∞)
    (p : SquareIndex) {z : ℝ × ℝ} (hz : z ∈ squareCell qx qy p) :
    (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
      (volume.prod volume) (squareCell qx qy p) ≤ gridSquareSup qx qy f z := by
  calc
    _ = (squareCell qx qy p).indicator (fun _ =>
        (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
        (volume.prod volume) (squareCell qx qy p)) z := (indicator_of_mem hz _).symm
    _ ≤ _ := le_iSup (fun p : SquareIndex => (squareCell qx qy p).indicator
      (fun _ => (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
        (volume.prod volume) (squareCell qx qy p)) z) p

theorem gridSquareSup_weak_L1 (qx qy : ℤ) (f : ℝ × ℝ → ℝ≥0∞)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    (volume.prod volume) {z | t < gridSquareSup qx qy f z} ≤
      t⁻¹ * ∫⁻ z, f z ∂volume.prod volume := by
  let G := {p : SquareIndex | t * (volume.prod volume) (squareCell qx qy p) ≤
    ∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume}
  have hsub : {z | t < gridSquareSup qx qy f z} ⊆ ⋃ p : G, squareCell qx qy p.val := by
    intro z hz
    change t < ⨆ p : SquareIndex, (squareCell qx qy p).indicator
      (fun _ => (∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
        (volume.prod volume) (squareCell qx qy p)) z at hz
    obtain ⟨p,hp⟩ := lt_iSup_iff.mp hz
    have hzp : z ∈ squareCell qx qy p := by
      by_contra hn
      simp only [indicator_of_notMem hn, not_lt_zero] at hp
    rw [indicator_of_mem hzp] at hp
    have hpos : (volume.prod volume) (squareCell qx qy p) ≠ 0 := by
      rw [squareCell_volume]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (scale_pos _)))
    have hfinite : (volume.prod volume) (squareCell qx qy p) ≠ ∞ := by
      rw [squareCell_volume]
      exact ENNReal.ofReal_ne_top
    have hg : p ∈ G := by
      change t * (volume.prod volume) (squareCell qx qy p) ≤ _
      calc
        _ ≤ ((∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
            (volume.prod volume) (squareCell qx qy p)) *
            (volume.prod volume) (squareCell qx qy p) := mul_le_mul' hp.le le_rfl
        _ = _ := ENNReal.div_mul_cancel hpos hfinite
    exact mem_iUnion.mpr ⟨⟨p,hg⟩,hzp⟩
  have hmass := ranked_countable_weak_bound (volume.prod volume)
    (fun p : G => squareCell qx qy p.val) (fun p => p.val.1)
    (fun p => squareCell_measurable qx qy p.val)
    (fun p q => squareCell_ranked qx qy p.val q.val) f t (fun p => p.property)
  calc
    _ ≤ (volume.prod volume) (⋃ p : G, squareCell qx qy p.val) := measure_mono hsub
    _ = t⁻¹ * (t * (volume.prod volume) (⋃ p : G, squareCell qx qy p.val)) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel ht htop,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hmass

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RankedMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive integral maximal functions for the line and square grids. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert
variable {ι X : Type*} [MeasurableSpace X]

theorem rankedMaximal_mono (μ : Measure X) (Q : ι → Set X)
    {f g : X → ℝ≥0∞} (h : f ≤ g) : rankedMaximal μ Q f ≤ rankedMaximal μ Q g := by
  intro x
  change (⨆ i, (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x) ≤
    ⨆ i, (Q i).indicator (fun _ => (∫⁻ y in Q i, g y ∂μ) / μ (Q i)) x
  apply iSup_mono
  intro i
  by_cases hx : x ∈ Q i
  · simp only [indicator_of_mem hx]
    exact mul_le_mul' (lintegral_mono h) le_rfl
  · simp only [indicator_of_notMem hx,le_refl]

theorem average_le_rankedMaximal (μ : Measure X) (Q : ι → Set X) (f : X → ℝ≥0∞)
    (i : ι) {x : X} (hx : x ∈ Q i) :
    (∫⁻ y in Q i, f y ∂μ) / μ (Q i) ≤ rankedMaximal μ Q f x := by
  calc
    _ = (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x := (indicator_of_mem hx _).symm
    _ ≤ _ := le_iSup (fun i => (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x) i

theorem rankedMaximal_weak_L1 [Countable ι] (μ : Measure X) (Q : ι → Set X)
    (rank : ι → ℤ) (hm : ∀ i, MeasurableSet (Q i))
    (hpos : ∀ i, μ (Q i) ≠ 0) (hfinite : ∀ i, μ (Q i) ≠ ∞)
    (hnest : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (f : X → ℝ≥0∞) (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    μ {x | t < rankedMaximal μ Q f x} ≤ t⁻¹ * ∫⁻ x, f x ∂μ := by
  let G := {i : ι | t * μ (Q i) ≤ ∫⁻ x in Q i, f x ∂μ}
  have hsub : {x | t < rankedMaximal μ Q f x} ⊆ ⋃ i : G, Q i.val := by
    intro x hx
    change t < ⨆ i, (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x at hx
    obtain ⟨i,hi⟩ := lt_iSup_iff.mp hx
    have hxi : x ∈ Q i := by
      by_contra hn
      simp only [indicator_of_notMem hn,not_lt_zero] at hi
    rw [indicator_of_mem hxi] at hi
    have hg : i ∈ G := by
      calc
        t * μ (Q i) ≤ ((∫⁻ y in Q i, f y ∂μ) / μ (Q i)) * μ (Q i) := mul_le_mul' hi.le le_rfl
        _ = _ := ENNReal.div_mul_cancel (hpos i) (hfinite i)
    exact mem_iUnion.mpr ⟨⟨i,hg⟩,hxi⟩
  have hmass := ranked_countable_weak_bound μ (fun i : G => Q i.val) (fun i => rank i.val)
    (fun i => hm i.val) (fun i j => hnest i.val j.val) f t (fun i => i.property)
  calc
    _ ≤ μ (⋃ i : G, Q i.val) := measure_mono hsub
    _ = t⁻¹ * (t * μ (⋃ i : G, Q i.val)) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel ht htop,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hmass

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_PositiveLineMaximal
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive line maximal functions. Extended integrals give pointwise
monotonicity, including on exceptional lines, which is needed by the
finite rectangle removal algorithm. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem positiveGridLine_weak_L1 (q : ℤ) (f : ℝ → ℝ≥0∞)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    volume {x | t < positiveGridLine q f x} ≤ t⁻¹ * ∫⁻ x, f x := by
  exact rankedMaximal_weak_L1 volume (fun p : LineCellIndex => cell q p.1 p.2)
    (fun p => p.1) (fun p => cell_measurable q p.1 p.2)
    (fun p => by rw [cell_volume]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (scale_pos _)))
    (fun p => by rw [cell_volume]; exact ENNReal.ofReal_ne_top)
    (fun i j hij hint => cell_subset_of_intersect hij (by simpa only [inter_comm] using hint))
    f t ht htop

theorem positiveGridHorizontal_measurable (q : ℤ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (positiveGridHorizontal q f) := by
  change Measurable (fun z : ℝ × ℝ => ⨆ p : LineCellIndex,
    (cell q p.1 p.2).indicator (fun _ =>
      (∫⁻ x in cell q p.1 p.2, f (x,z.2)) / volume (cell q p.1 p.2)) z.1)
  apply Measurable.iSup
  intro p
  have hm : Measurable (fun z : ℝ × ℝ =>
      (∫⁻ x in cell q p.1 p.2, f (x,z.2)) / volume (cell q p.1 p.2)) :=
    (hf.lintegral_prod_left'.comp measurable_snd).div_const _
  convert hm.indicator ((cell_measurable q p.1 p.2).preimage measurable_fst) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  by_cases hz : z.1 ∈ cell q p.1 p.2 <;> simp [hz]

theorem positiveGridHorizontal_weak_L1 (q : ℤ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    (volume.prod volume) {z | t < positiveGridHorizontal q f z} ≤
      t⁻¹ * ∫⁻ z, f z ∂volume.prod volume := by
  rw [Measure.prod_apply_symm (measurableSet_lt measurable_const (positiveGridHorizontal_measurable q hf))]
  calc
    _ ≤ ∫⁻ y, t⁻¹ * ∫⁻ x, f (x,y) := lintegral_mono (fun y => positiveGridLine_weak_L1 q (fun x => f (x,y)) t ht htop)
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr ht),lintegral_prod_symm _ hf.aemeasurable]

theorem positiveHorizontal_measurable {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (positiveHorizontal f) := by
  have h (s : Finset GridChoice) : Measurable (fun z => s.sup (fun q => positiveGridHorizontal q.val f z)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert q s hqs ih => simpa only [Finset.sup_insert] using (positiveGridHorizontal_measurable q.val hf).max ih
  exact h Finset.univ

theorem positiveHorizontal_mono {f g : ℝ × ℝ → ℝ≥0∞} (h : f ≤ g) :
    positiveHorizontal f ≤ positiveHorizontal g := by
  intro z
  apply Finset.sup_mono_fun
  intro q _
  exact rankedMaximal_mono volume _ (fun x => h (x,z.2)) z.1

theorem positiveHorizontal_weak_L1 {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    (volume.prod volume) {z | t < positiveHorizontal f z} ≤
      3 * t⁻¹ * ∫⁻ z, f z ∂volume.prod volume := by
  have hsub : {z | t < positiveHorizontal f z} ⊆
      ⋃ q : GridChoice, {z | t < positiveGridHorizontal q.val f z} := by
    intro z hz
    change t < Finset.univ.sup (fun q : GridChoice => positiveGridHorizontal q.val f z) at hz
    obtain ⟨q,_,hq⟩ := Finset.lt_sup_iff.mp hz
    exact mem_iUnion.mpr ⟨q,hq⟩
  calc
    _ ≤ (volume.prod volume) (⋃ q : GridChoice, {z | t < positiveGridHorizontal q.val f z}) := measure_mono hsub
    _ ≤ ∑ q : GridChoice, (volume.prod volume) {z | t < positiveGridHorizontal q.val f z} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _q : GridChoice, t⁻¹ * ∫⁻ z, f z ∂volume.prod volume :=
      Finset.sum_le_sum (fun q _ => positiveGridHorizontal_weak_L1 q.val hf t ht htop)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,gridChoice_card,nsmul_eq_mul]; norm_num; rw [mul_assoc]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SquareMaximalWeakL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weak L1 square maximal majorant using nine fixed grid pairs. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

theorem squareSup_measurable (f : ℝ × ℝ → ℝ≥0∞) : Measurable (squareSup f) := by
  have h (s : Finset (GridChoice × GridChoice)) : Measurable (fun z =>
      s.sup (fun q => gridSquareSup q.1.val q.2.val f z)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert q s hqs ih => simpa only [Finset.sup_insert] using (gridSquareSup_measurable q.1.val q.2.val f).max ih
  exact h Finset.univ

theorem gridSquareSup_le_squareSup (q : GridChoice × GridChoice)
    (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) :
    gridSquareSup q.1.val q.2.val f z ≤ squareSup f z :=
  Finset.le_sup (f := fun q : GridChoice × GridChoice => gridSquareSup q.1.val q.2.val f z) (Finset.mem_univ q)

theorem squareSup_weak_L1 (f : ℝ × ℝ → ℝ≥0∞) (t : ℝ≥0∞)
    (ht : t ≠ 0) (htop : t ≠ ∞) :
    (volume.prod volume) {z | t < squareSup f z} ≤
      9 * t⁻¹ * ∫⁻ z, f z ∂volume.prod volume := by
  have hsub : {z | t < squareSup f z} ⊆
      ⋃ q : GridChoice × GridChoice, {z | t < gridSquareSup q.1.val q.2.val f z} := by
    intro z hz
    change t < Finset.univ.sup (fun q : GridChoice × GridChoice => gridSquareSup q.1.val q.2.val f z) at hz
    obtain ⟨q,_,hq⟩ := Finset.lt_sup_iff.mp hz
    exact mem_iUnion.mpr ⟨q,hq⟩
  calc
    _ ≤ (volume.prod volume) (⋃ q : GridChoice × GridChoice,
        {z | t < gridSquareSup q.1.val q.2.val f z}) := measure_mono hsub
    _ ≤ ∑ q : GridChoice × GridChoice,
        (volume.prod volume) {z | t < gridSquareSup q.1.val q.2.val f z} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _q : GridChoice × GridChoice, t⁻¹ * ∫⁻ z, f z ∂volume.prod volume :=
      Finset.sum_le_sum (fun q _ => gridSquareSup_weak_L1 q.1.val q.2.val f t ht htop)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,gridChoice_card,nsmul_eq_mul]
      norm_num
      rw [mul_assoc]

theorem centeredSquare_measurable (c : ℝ × ℝ) (r : ℝ) : MeasurableSet (centeredSquare c r) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem centeredSquare_volume (c : ℝ × ℝ) (r : ℝ) :
    (volume.prod volume) (centeredSquare c r) = ENNReal.ofReal (2*r) * ENNReal.ofReal (2*r) := by
  rw [centeredSquare,Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
  congr 2 <;> ring

theorem square_integral_le_squareSup (f : ℝ × ℝ → ℝ≥0∞) (c : ℝ × ℝ)
    (r : ℝ) (hr : 0 < r) {z : ℝ × ℝ} (hz : z ∈ centeredSquare c r) :
    (∫⁻ w in centeredSquare c r, f w ∂volume.prod volume) ≤
      36 * (volume.prod volume) (centeredSquare c r) * squareSup f z := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow
    (show 0 < 12*r by positivity) (by norm_num : (1:ℝ) < 2)
  change scale k ≤ 12*r at hlo
  change 12*r < scale (k+1) at hhi
  rw [scale_succ] at hhi
  have hsmall : 6*r < scale k := by linarith
  obtain ⟨qx,hqx,i,hx⟩ := exists_three_grid_cover k c.1 r hr.le hsmall
  obtain ⟨qy,hqy,j,hy⟩ := exists_three_grid_cover k c.2 r hr.le hsmall
  let p : SquareIndex := (k,i,j)
  let q : GridChoice × GridChoice := (⟨qx,hqx⟩,⟨qy,hqy⟩)
  have hsub : centeredSquare c r ⊆ squareCell qx qy p := Set.prod_mono hx hy
  have hvolpos : (volume.prod volume) (squareCell qx qy p) ≠ 0 := by
    rw [squareCell_volume]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (scale_pos k)))
  have hvolfinite : (volume.prod volume) (squareCell qx qy p) ≠ ∞ := by
    rw [squareCell_volume]
    exact ENNReal.ofReal_ne_top
  have hmean := (square_average_le_gridSquareSup qx qy f p (hsub hz)).trans
    (gridSquareSup_le_squareSup q f z)
  have hvol : (volume.prod volume) (squareCell qx qy p) ≤
      36 * (volume.prod volume) (centeredSquare c r) := by
    rw [squareCell_volume,centeredSquare_volume,←ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)]
    rw [show (36:ℝ≥0∞) = ENNReal.ofReal 36 by norm_num,
      ←ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    change (scale k)^2 ≤ 36*((2*r)*(2*r))
    nlinarith [scale_pos k]
  calc
    _ ≤ ∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume := lintegral_mono_set hsub
    _ = (volume.prod volume) (squareCell qx qy p) *
        ((∫⁻ w in squareCell qx qy p, f w ∂volume.prod volume) /
        (volume.prod volume) (squareCell qx qy p)) := by
      rw [mul_comm,ENNReal.div_mul_cancel hvolpos hvolfinite]
    _ ≤ _ := mul_le_mul' hvol hmean

end LipschitzHilbert.DyadicLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PublishedInputs
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published inputs for the Lipschitz-direction Hilbert transform

The two classical estimates used by the manuscript are stated as propositions.
Their deterministic consequences make the quantifiers needed for the
finite rectangle and martingale applications explicit.

* Lacey--Li, *On a conjecture of E. M. Stein on the Hilbert transform on
  vector fields*, Memoirs AMS 205 (2010), no. 965, result 1.10 and equation
  (1.11); DOI 10.1090/S0065-9266-10-00572-7. In the author version
  arXiv:0704.0808 these occur on printed p. 3, with the finite-family proof
  in Chapter 3. This is the published form of arXiv:math/0601213v2,
  Theorem 1.4. We use the finite admissible-rectangle weak `(2,2)` estimate.
* Zorin-Kranich, *Weighted Lépingle inequality*, Bernoulli 26 (2020),
  2311--2318, Theorem 1.1, with `p = 2`, `r = 3`, and weight one.
  We use only real-valued finite martingales on probability spaces.

The deterministic consequences below make the quantifiers relevant to the
application explicit: a union of high-average rectangles, and a variation
sum whose increasing indices may be chosen separately at each point.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

namespace Rectangle

theorem measurableSet_carrier (R : Rectangle) : MeasurableSet R.carrier := by
  have h (i : Fin 2) : Continuous (fun x : Plane => R.axes.repr (x - R.center) i) :=
    (PiLp.continuous_apply 2 _ i).comp (R.axes.repr.continuous.comp (continuous_id.sub continuous_const))
  exact ((isClosed_le (h 0).abs continuous_const).inter
    (isClosed_le (h 1).abs continuous_const)).measurableSet

end Rectangle

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlaneCoordinates
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure-preserving bridge from the manuscript's real coordinate
pairs to the Euclidean plane used by the published maximal estimate. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem planeCoordinates_symm_apply (z : Plane) :
    planeCoordinates.symm z = (z 0,z 1) := rfl

theorem planeCoordinates_measurePreserving :
    MeasurePreserving planeCoordinates (volume.prod volume) volume := by
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp
    (measurePreserving_finTwoArrow (volume : Measure ℝ)).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleArea
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact area of the orthogonal rectangles in the published input. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

theorem orthogonalCoordinates_apply (R : Rectangle) (z : Plane) :
    R.orthogonalCoordinates z = (R.axes.repr (z-R.center) 0, R.axes.repr (z-R.center) 1) := rfl

theorem orthogonalCoordinates_measurePreserving (R : Rectangle) :
    MeasurePreserving R.orthogonalCoordinates volume (volume.prod volume) := by
  exact planeCoordinates_measurePreserving.symm.comp
    (R.axes.measurePreserving_repr.comp (measurePreserving_sub_right volume R.center))

theorem carrier_eq_coordinate_rectangle (R : Rectangle) :
    R.carrier = R.orthogonalCoordinates ⁻¹'
      (Icc (-R.long/2) (R.long/2) ×ˢ Icc (-R.short/2) (R.short/2)) := by
  ext z
  simp only [carrier, mem_ofPred_eq, mem_preimage, mem_prod, mem_Icc,
    orthogonalCoordinates_apply, abs_le, neg_div]

theorem volume_carrier (R : Rectangle) :
    volume R.carrier = ENNReal.ofReal R.long * ENNReal.ofReal R.short := by
  rw [carrier_eq_coordinate_rectangle,
    R.orthogonalCoordinates_measurePreserving.measure_preimage_equiv,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  congr 2 <;> ring

theorem volume_carrier_ne_top (R : Rectangle) : volume R.carrier ≠ ∞ := by
  rw [volume_carrier]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem volume_carrier_pos (R : Rectangle) : 0 < volume R.carrier := by
  rw [volume_carrier]
  have hl := lt_of_lt_of_le R.short_pos R.short_le_long
  exact bot_lt_iff_ne_bot.mpr (mul_ne_zero
    (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
    (ne_of_gt (ENNReal.ofReal_pos.mpr R.short_pos)))

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LaceyLiGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary geometry for the finite rectangle covering proof of
Lacey--Li, Memoirs AMS 205 (2010), Chapter 3. All rectangles and popularity
sets here are the actual objects from the published input. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert.Rectangle

theorem long_pos (R : Rectangle) : 0<R.long := R.short_pos.trans_le R.short_le_long

theorem aperture_pos (R : Rectangle) : 0<R.short/(2*R.long) := by
  exact div_pos R.short_pos (mul_pos (by norm_num) R.long_pos)

theorem norm_sub_center_le_long (R : Rectangle) {x : Plane} (hx : x∈R.carrier) :
    ‖x-R.center‖ ≤ R.long := by
  have h0 := hx.1
  have h1 := hx.2
  calc
    ‖x-R.center‖ = ‖∑ i : Fin 2, R.axes.repr (x-R.center) i • R.axes i‖ := by
      rw [R.axes.sum_repr]
    _  ≤  ∑ i : Fin 2, ‖R.axes.repr (x-R.center) i • R.axes i‖ := norm_sum_le _ _
    _ = |R.axes.repr (x-R.center) 0|+|R.axes.repr (x-R.center) 1| := by
      simp only [Fin.sum_univ_two,norm_smul,R.axes.norm_eq_one,mul_one,Real.norm_eq_abs]
    _  ≤  R.long := by linarith [R.short_le_long]

theorem dist_le_two_long (R : Rectangle) {x y : Plane} (hx : x∈R.carrier) (hy : y∈R.carrier) :
    dist x y ≤ 2*R.long := by
  have ht := dist_triangle x R.center y
  rw [dist_comm R.center y,dist_eq_norm x R.center,dist_eq_norm y R.center] at ht
  linarith [R.norm_sub_center_le_long hx,R.norm_sub_center_le_long hy]

theorem popular_axis_distance (R : Rectangle) {v : Plane → Plane}
    (hu : ∀ x, ‖v x‖=1) {x : Plane} (hx : x∈R.popularSet v) :
    dist (v x) (R.axes 0) ≤ R.short/(2*R.long) := by
  have hcos := Real.one_sub_sq_div_two_le_cos (x:=R.short/(2*R.long))
  have hinner := hx.2
  have he := norm_sub_sq_real (v x) (R.axes 0)
  rw [hu x,R.axes.norm_eq_one] at he
  rw [dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) R.aperture_pos.le).mp
  nlinarith

theorem popularSet_nonempty (R : Rectangle) {v : Plane → Plane} {K δ : ℝ≥0}
    (hR : R.Admissible v K δ) (hδ : 0<δ) : (R.popularSet v).Nonempty := by
  have hpos : 0<(δ:ℝ≥0∞)*volume R.carrier :=
    ENNReal.mul_pos (by exact_mod_cast hδ.ne') R.volume_carrier_pos.ne'
  have hne : volume (R.popularSet v)≠0 := ne_of_gt (hpos.trans_le hR.2)
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty.mp h,measure_empty] at hne
  contradiction

theorem popular_points_distance (R S : Rectangle) {v : Plane → Plane}
    {x y z : Plane} (hx : x∈R.popularSet v) (hy : y∈S.popularSet v)
    (hzR : z∈R.carrier) (hzS : z∈S.carrier) : dist x y ≤ 2*(R.long+S.long) := by
  have ht := dist_triangle x z y
  have hR := R.dist_le_two_long hx.1 hzR
  have hS := S.dist_le_two_long hzS hy.1
  linarith

theorem intersecting_axes_distance (R S : Rectangle) {v : Plane → Plane} {K δ : ℝ≥0}
    (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖=1) (hδ : 0<δ)
    (hR : R.Admissible v K δ) (hS : S.Admissible v K δ)
    (hint : (R.carrier ∩ S.carrier).Nonempty) :
    dist (R.axes 0) (S.axes 0) ≤ R.short/(2*R.long)+S.short/(2*S.long)+
      2*(K:ℝ)*(R.long+S.long) := by
  obtain ⟨x,hx⟩ := R.popularSet_nonempty hR hδ
  obtain ⟨y,hy⟩ := S.popularSet_nonempty hS hδ
  obtain ⟨z,hzR,hzS⟩ := hint
  have hxy := hv.dist_le_mul x y
  have hxy' := R.popular_points_distance S hx hy hzR hzS
  have hm := mul_le_mul_of_nonneg_left hxy' K.coe_nonneg
  have ht1 := dist_triangle (R.axes 0) (v x) (S.axes 0)
  have ht2 := dist_triangle (v x) (v y) (S.axes 0)
  have hRx := R.popular_axis_distance hu hx
  have hSy := S.popular_axis_distance hu hy
  rw [dist_comm (R.axes 0) (v x)] at ht1
  linarith

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleCountingEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact first and second moments of finite rectangle counts, in the
normalization of Lacey--Li's covering lemma (3.1)--(3.2). -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {ι : Type*}

theorem rectangleCount_measurable (R : ι → Rectangle) (s : Finset ι) :
    Measurable (rectangleCount R s) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.indicator (R i).measurableSet_carrier)

theorem rectangleCount_first_moment (R : ι → Rectangle) (s : Finset ι) :
    (∫⁻ x, rectangleCount R s x)=∑ i∈s, volume (R i).carrier := by
  unfold rectangleCount
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (R i).measurableSet_carrier)]
  simp only [lintegral_indicator_fun_one (Rectangle.measurableSet_carrier _)]

theorem rectangleCount_second_moment (R : ι → Rectangle) (s : Finset ι) :
    (∫⁻ x, rectangleCount R s x^2)=∑ i∈s, ∑ j∈s, volume ((R i).carrier ∩ (R j).carrier) := by
  classical
  have he (x : Plane) : rectangleCount R s x^2=
      ∑ i∈s, ∑ j∈s, ((R i).carrier ∩ (R j).carrier).indicator (fun _ => (1:ℝ≥0∞)) x := by
    unfold rectangleCount
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : x∈(R i).carrier <;> by_cases hj : x∈(R j).carrier <;> simp [hi,hj]
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun j _ =>
    measurable_const.indicator ((R i).measurableSet_carrier.inter (R j).measurableSet_carrier)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_finsetSum _ (fun j _ =>
    measurable_const.indicator ((R i).measurableSet_carrier.inter (R j).measurableSet_carrier))]
  apply Finset.sum_congr rfl
  intro j _
  exact lintegral_indicator_fun_one ((R i).measurableSet_carrier.inter (R j).measurableSet_carrier)

theorem rectangleCount_pairing (R : ι → Rectangle) (s : Finset ι) (h : Plane → ℝ)
    (hh : AEStronglyMeasurable h volume) :
    (∫⁻ x, ‖h x‖ₑ*rectangleCount R s x)=∑ i∈s, ∫⁻ x in (R i).carrier, ‖h x‖ₑ := by
  classical
  have he (x : Plane) : ‖h x‖ₑ*rectangleCount R s x=
      ∑ i∈s, (R i).carrier.indicator (fun y => ‖h y‖ₑ) x := by
    unfold rectangleCount
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x∈(R i).carrier <;> simp [hi]
  simp_rw [he]
  rw [lintegral_finsetSum' _ (fun i _ => hh.enorm.indicator (R i).measurableSet_carrier)]
  simp only [lintegral_indicator (Rectangle.measurableSet_carrier _)]

theorem rectangleCount_pairing_sq_le (R : ι → Rectangle) (s : Finset ι) (h : Plane → ℝ)
    (hh : AEStronglyMeasurable h volume) :
    (∫⁻ x, ‖h x‖ₑ*rectangleCount R s x)^2 ≤
      squareIntegral volume h*(∫⁻ x, rectangleCount R s x^2) := by
  have hc := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hh.enorm (rectangleCount_measurable R s).aemeasurable
  have hroot (a : ℝ≥0∞) : (a^(1/2:ℝ))^2=a := by
    rw [←ENNReal.rpow_mul_natCast]
    norm_num
  have hp := pow_le_pow_left' hc 2
  rw [mul_pow,hroot,hroot] at hp
  simpa only [ENNReal.rpow_two,Pi.mul_apply,squareIntegral] using hp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleDilation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual rectangle dilations and containment of intersecting rectangles
with controlled relative angle, as used in Lacey--Li (3.4). -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.Rectangle

theorem carrier_subset_dilate (R : Rectangle) (a : ℝ) (ha : 1≤a) :
    R.carrier⊆(R.dilate a (lt_of_lt_of_le zero_lt_one ha)).carrier := by
  intro x hx
  constructor
  · change |R.axes.repr (x-R.center) 0| ≤ a*R.long/2
    exact hx.1.trans (by nlinarith [R.long_pos])
  · change |R.axes.repr (x-R.center) 1| ≤ a*R.short/2
    exact hx.2.trans (by nlinarith [R.short_pos])

theorem volume_dilate (R : Rectangle) (a : ℝ) (ha : 0<a) :
    volume (R.dilate a ha).carrier=ENNReal.ofReal (a^2)*volume R.carrier := by
  rw [volume_carrier,volume_carrier]
  simp only [dilate,ENNReal.ofReal_mul ha.le,ENNReal.ofReal_pow ha.le]
  ring

theorem abs_coordinate_le_norm (R : Rectangle) (x : Plane) (i : Fin 2) :
    |R.axes.repr x i|≤‖x‖ := by
  rw [R.axes.repr_apply_apply]
  simpa only [R.axes.norm_eq_one,one_mul] using abs_real_inner_le_norm (R.axes i) x

theorem coordinate_difference_zero (R : Rectangle) {x y : Plane}
    (hx : x∈R.carrier) (hy : y∈R.carrier) : |R.axes.repr (x-y) 0|≤R.long := by
  have he : R.axes.repr (x-y) 0=R.axes.repr (x-R.center) 0-R.axes.repr (y-R.center) 0 := by
    simp only [R.axes.repr_apply_apply,inner_sub_right]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hx.1,hy.1])

theorem coordinate_difference_one (R : Rectangle) {x y : Plane}
    (hx : x∈R.carrier) (hy : y∈R.carrier) : |R.axes.repr (x-y) 1|≤R.short := by
  have he : R.axes.repr (x-y) 1=R.axes.repr (x-R.center) 1-R.axes.repr (y-R.center) 1 := by
    simp only [R.axes.repr_apply_apply,inner_sub_right]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [hx.2,hy.2])

theorem transverse_axis_le (R S : Rectangle) :
    |R.axes.repr (S.axes 0) 1|≤dist (R.axes 0) (S.axes 0) := by
  have hz : R.axes.repr (R.axes 0) 1=0 := by
    simp
  have h := R.abs_coordinate_le_norm (S.axes 0-R.axes 0) 1
  rw [map_sub,PiLp.sub_apply,hz,sub_zero] at h
  simpa only [dist_eq_norm,norm_sub_rev] using h

theorem transverse_difference_le (R S : Rectangle) {x y : Plane}
    (hx : x∈S.carrier) (hy : y∈S.carrier) :
    |R.axes.repr (x-y) 1|≤S.long*dist (R.axes 0) (S.axes 0)+S.short := by
  have he : R.axes.repr (x-y) 1=
      S.axes.repr (x-y) 0*R.axes.repr (S.axes 0) 1+
      S.axes.repr (x-y) 1*R.axes.repr (S.axes 1) 1 := by
    nth_rw 1 [←S.axes.sum_repr (x-y)]
    rw [Fin.sum_univ_two,map_add,PiLp.add_apply,map_smul,map_smul]
    rfl
  have hc := R.abs_coordinate_le_norm (S.axes 1) 1
  rw [S.axes.norm_eq_one] at hc
  rw [he]
  calc
    _ ≤ |S.axes.repr (x-y) 0| *|R.axes.repr (S.axes 0) 1|+
        |S.axes.repr (x-y) 1| *|R.axes.repr (S.axes 1) 1| := by
      simpa only [abs_mul] using abs_add_le
        (S.axes.repr (x-y) 0*R.axes.repr (S.axes 0) 1)
        (S.axes.repr (x-y) 1*R.axes.repr (S.axes 1) 1)
    _ ≤ S.long*dist (R.axes 0) (S.axes 0)+S.short*1 :=
      add_le_add
        (mul_le_mul (S.coordinate_difference_zero hx hy) (R.transverse_axis_le S)
          (abs_nonneg _) S.long_pos.le)
        (mul_le_mul (S.coordinate_difference_one hx hy) hc (abs_nonneg _) S.short_pos.le)
    _ = _ := by ring

theorem controlled_angle_containment (R S : Rectangle) (A : ℝ) (hA : 0≤A)
    (hL : S.long≤R.long) (hW : S.short≤R.short)
    (hangle : S.long*dist (R.axes 0) (S.axes 0)≤A*R.short)
    (hint : (R.carrier ∩ S.carrier).Nonempty) :
    S.carrier⊆(R.dilate (2*A+5) (by positivity)).carrier := by
  obtain ⟨z,hzR,hzS⟩ := hint
  intro x hx
  have he : R.axes.repr (x-R.center)=R.axes.repr (x-z)+R.axes.repr (z-R.center) := by
    rw [←map_add]
    congr 1
    abel
  constructor
  · change |R.axes.repr (x-R.center) 0|≤(2*A+5)*R.long/2
    rw [he,PiLp.add_apply]
    have ht := abs_add_le (R.axes.repr (x-z) 0) (R.axes.repr (z-R.center) 0)
    have hc := R.abs_coordinate_le_norm (x-z) 0
    have hd := S.dist_le_two_long hx hzS
    rw [dist_eq_norm] at hd
    nlinarith [hzR.1,R.long_pos]
  · change |R.axes.repr (x-R.center) 1|≤(2*A+5)*R.short/2
    rw [he,PiLp.add_apply]
    have ht := abs_add_le (R.axes.repr (x-z) 1) (R.axes.repr (z-R.center) 1)
    have hc := R.transverse_difference_le S hx hzS
    nlinarith [hzR.2,R.short_pos]

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PositiveRectangleAuxiliary
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise monotone positive-integral auxiliary maximal functions for
finite rectangle selection. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid

theorem gridSquareSup_mono (qx qy : ℤ) {f g : ℝ × ℝ → ℝ≥0∞} (h : f ≤ g) :
    gridSquareSup qx qy f ≤ gridSquareSup qx qy g :=
  rankedMaximal_mono (volume.prod volume) (squareCell qx qy) h

theorem squareSup_mono {f g : ℝ × ℝ → ℝ≥0∞} (h : f ≤ g) : squareSup f ≤ squareSup g := by
  intro z
  apply Finset.sup_mono_fun
  intro q _
  exact gridSquareSup_mono q.1.val q.2.val h z

theorem positiveChartLine_weak_L1 (e : Plane ≃ᵐ (ℝ × ℝ))
    (he : MeasurePreserving e volume (volume.prod volume)) {f : Plane → ℝ≥0∞}
    (hf : Measurable f) (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    volume {x | t < positiveChartLine e f x} ≤ 3 * t⁻¹ * ∫⁻ x, f x := by
  have hE : MeasurableSet {z | t < positiveHorizontal (f ∘ e.symm) z} :=
    measurableSet_lt measurable_const (positiveHorizontal_measurable (hf.comp e.symm.measurable))
  change volume (e ⁻¹' {z | t < positiveHorizontal (f ∘ e.symm) z}) ≤ _
  rw [he.measure_preimage hE.nullMeasurableSet]
  have h := positiveHorizontal_weak_L1 (hf.comp e.symm.measurable) t ht htop
  refine h.trans_eq ?_
  simp only [Function.comp_apply]
  rw [he.symm.lintegral_comp hf]

theorem positivePlaneSquare_weak_L1 {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    volume {x | t < positivePlaneSquare f x} ≤ 9 * t⁻¹ * ∫⁻ x, f x := by
  have hE : MeasurableSet {z | t < squareSup (f ∘ planeCoordinates) z} :=
    measurableSet_lt measurable_const (squareSup_measurable _)
  change volume (planeCoordinates.symm ⁻¹' {z | t < squareSup (f ∘ planeCoordinates) z}) ≤ _
  rw [planeCoordinates_measurePreserving.symm.measure_preimage hE.nullMeasurableSet]
  refine (squareSup_weak_L1 (f ∘ planeCoordinates) t ht htop).trans_eq ?_
  simp only [Function.comp_apply]
  rw [planeCoordinates_measurePreserving.lintegral_comp hf]

variable {ι : Type*} [Fintype ι]

theorem positiveAuxiliary_mono (e : ι → Plane ≃ᵐ (ℝ × ℝ))
    {f g : Plane → ℝ≥0∞} (h : f ≤ g) : positiveAuxiliary e f ≤ positiveAuxiliary e g := by
  intro x
  apply sup_le_sup
  · exact squareSup_mono (fun z => h (planeCoordinates z)) (planeCoordinates.symm x)
  · apply Finset.sup_mono_fun
    intro i _
    exact positiveHorizontal_mono (fun z => h ((e i).symm z)) (e i x)

theorem positiveAuxiliary_zero (e : ι → Plane ≃ᵐ (ℝ × ℝ)) (x : Plane) :
    positiveAuxiliary e (fun _ => 0) x = 0 := by
  simp [positiveAuxiliary,positivePlaneSquare,squareSup,gridSquareSup,
    positiveChartLine,positiveHorizontal,positiveGridHorizontal,positiveGridLine,rankedMaximal]

theorem positiveAuxiliary_weak_L1 (e : ι → Plane ≃ᵐ (ℝ × ℝ))
    (he : ∀ i, MeasurePreserving (e i) volume (volume.prod volume))
    {f : Plane → ℝ≥0∞} (hf : Measurable f) (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    volume {x | t < positiveAuxiliary e f x} ≤
      (9 + 3 * Fintype.card ι) * t⁻¹ * ∫⁻ x, f x := by
  classical
  have hsub : {x | t < positiveAuxiliary e f x} ⊆
      {x | t < positivePlaneSquare f x} ∪ ⋃ i : ι, {x | t < positiveChartLine (e i) f x} := by
    intro x hx
    change t < positivePlaneSquare f x ⊔ Finset.univ.sup (fun i => positiveChartLine (e i) f x) at hx
    rcases lt_sup_iff.mp hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨i,_,hi⟩ := Finset.lt_sup_iff.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)
  calc
    _ ≤ volume ({x | t < positivePlaneSquare f x} ∪
        ⋃ i : ι, {x | t < positiveChartLine (e i) f x}) := measure_mono hsub
    _ ≤ volume {x | t < positivePlaneSquare f x} +
        ∑ i : ι, volume {x | t < positiveChartLine (e i) f x} :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
    _ ≤ 9 * t⁻¹ * (∫⁻ x, f x) + ∑ _i : ι, 3 * t⁻¹ * ∫⁻ x, f x :=
      add_le_add (positivePlaneSquare_weak_L1 hf t ht htop)
        (Finset.sum_le_sum (fun i _ => positiveChartLine_weak_L1 (e i) (he i) hf t ht htop))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PositiveAuxiliaryAverages
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise domination of the literal line and square integrals used
by the rectangle selection argument. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid

theorem positiveHorizontal_interval (f : ℝ × ℝ → ℝ≥0∞) (c r : ℝ) (hr : 0 < r)
    (z : ℝ × ℝ) (hz : z.1 ∈ Icc (c-r) (c+r)) :
    (∫⁻ x in Icc (c-r) (c+r), f (x,z.2)) ≤
      6 * ENNReal.ofReal (2*r) * positiveHorizontal f z := by
  obtain ⟨q,hq,k,j,hsub,hscale⟩ := exists_comparable_three_grid_cover c r hr
  let Q : GridChoice := ⟨q,hq⟩
  have hv0 : volume (cell q k j) ≠ 0 := by
    rw [cell_volume]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (scale_pos k))
  have hvtop : volume (cell q k j) ≠ ∞ := by rw [cell_volume]; exact ENNReal.ofReal_ne_top
  have hm : (∫⁻ x in cell q k j, f (x,z.2)) / volume (cell q k j) ≤ positiveHorizontal f z := by
    have h : (∫⁻ x in cell q k j, f (x,z.2)) / volume (cell q k j) ≤
        positiveGridHorizontal q f z :=
      average_le_rankedMaximal volume (fun p : LineCellIndex => cell q p.1 p.2)
        (fun x => f (x,z.2)) (k,j) (hsub hz)
    have hle : positiveGridHorizontal q f z ≤ positiveHorizontal f z := by
      change positiveGridHorizontal Q.val f z ≤
        Finset.univ.sup (fun Q : GridChoice => positiveGridHorizontal Q.val f z)
      exact Finset.le_sup (f := fun Q : GridChoice => positiveGridHorizontal Q.val f z) (Finset.mem_univ Q)
    exact h.trans hle
  have hv : volume (cell q k j) ≤ 6 * ENNReal.ofReal (2*r) := by
    rw [cell_volume,show (6:ℝ≥0∞)=ENNReal.ofReal 6 by norm_num,
      ←ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [hscale]
  calc
    _ ≤ ∫⁻ x in cell q k j, f (x,z.2) := lintegral_mono_set hsub
    _ = volume (cell q k j) * ((∫⁻ x in cell q k j, f (x,z.2)) / volume (cell q k j)) := by
      rw [mul_comm,ENNReal.div_mul_cancel hv0 hvtop]
    _ ≤ _ := mul_le_mul' hv hm

variable {ι : Type*} [Fintype ι]

theorem positiveAuxiliary_line_integral (e : ι → Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ≥0∞)
    (i : ι) (c r : ℝ) (hr : 0 < r) (x : Plane) (hx : (e i x).1 ∈ Icc (c-r) (c+r)) :
    (∫⁻ t in Icc (c-r) (c+r), f ((e i).symm (t,(e i x).2))) ≤
      6 * ENNReal.ofReal (2*r) * positiveAuxiliary e f x := by
  have h := positiveHorizontal_interval (f ∘ (e i).symm) c r hr (e i x) hx
  refine h.trans (mul_le_mul' le_rfl ?_)
  exact (Finset.le_sup (f := fun j => positiveChartLine (e j) f x) (Finset.mem_univ i)).trans le_sup_right

theorem positiveAuxiliary_square_integral (e : ι → Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ≥0∞)
    (c : ℝ × ℝ) (r : ℝ) (hr : 0 < r) (x : Plane)
    (hx : planeCoordinates.symm x ∈ centeredSquare c r) :
    (∫⁻ z in centeredSquare c r, f (planeCoordinates z) ∂volume.prod volume) ≤
      36 * (volume.prod volume) (centeredSquare c r) * positiveAuxiliary e f x := by
  have h := square_integral_le_squareSup (f ∘ planeCoordinates) c r hr hx
  exact h.trans (mul_le_mul' le_rfl le_sup_left)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleCoverSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite selection with the exact length/eccentricity priority in the
Lacey--Li covering algorithm. The removal predicate will be instantiated
by containment in the auxiliary maximal-function level set. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert
variable {ι : Type*}

theorem rectangle_priority_exists (R : ι → Rectangle) (s : Finset ι) (hs : s.Nonempty) :
    ∃ i∈s, ∀ j∈s, rectanglePriority R i j := by
  classical
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image s (fun i => (R i).long) hs
  let t := s.filter (fun j => (R j).long=(R i).long)
  have ht : t.Nonempty := ⟨i,by simp [t,hi]⟩
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image t (fun j => (R j).short/(R j).long) ht
  have hjs := (Finset.mem_filter.mp hj).1
  have hji := (Finset.mem_filter.mp hj).2
  refine ⟨j,hjs,?_⟩
  intro k hk
  constructor
  · rw [hji]
    exact hmax k hk
  · intro hkj
    exact hmin k (by simp [t,hk,hkj,hji])

theorem mem_rectangleRemaining [DecidableEq ι] (blocked : Finset ι → ι → Prop)
    (previous stock : Finset ι) (i j : ι) :
    j∈rectangleRemaining blocked previous stock i ↔ j∈stock ∧ j≠i ∧ ¬blocked (insert i previous) j := by
  classical
  simp only [rectangleRemaining,Finset.mem_filter]

theorem rectangleRemaining_subset [DecidableEq ι] (blocked : Finset ι → ι → Prop)
    (previous stock : Finset ι) (i : ι) : rectangleRemaining blocked previous stock i⊆stock := by
  classical
  exact Finset.filter_subset _ _

theorem rectangle_cover_run_exists [DecidableEq ι] (R : ι → Rectangle)
    (blocked : Finset ι → ι → Prop) (stock previous : Finset ι)
    (hallowed : ∀ i∈stock, ¬blocked previous i) :
    ∃ selected, RectangleCoverRun R blocked previous stock selected := by
  classical
  induction stock using Finset.strongInduction generalizing previous with
  | H stock ih =>
    by_cases hs : stock=∅
    · subst stock
      exact ⟨[],RectangleCoverRun.stop previous⟩
    · obtain ⟨i,hi,hp⟩ := rectangle_priority_exists R stock (Finset.nonempty_iff_ne_empty.mpr hs)
      have hsub : rectangleRemaining blocked previous stock i⊂stock := by
        apply (ssubset_iff_subset_ne).2
        refine ⟨rectangleRemaining_subset blocked previous stock i,?_⟩
        intro he
        have hm : i∈rectangleRemaining blocked previous stock i := he.symm ▸ hi
        exact (mem_rectangleRemaining blocked previous stock i i).mp hm |>.2.1 rfl
      obtain ⟨tail,htail⟩ := ih _ hsub (insert i previous) (fun j hj =>
        ((mem_rectangleRemaining blocked previous stock i j).mp hj).2.2)
      exact ⟨i::tail,RectangleCoverRun.step previous stock i tail hi hp (hallowed i hi) htail⟩

namespace RectangleCoverRun
variable [DecidableEq ι] {R : ι → Rectangle} {blocked : Finset ι → ι → Prop}
  {previous stock : Finset ι} {selected : List ι}

theorem selected_subset (h : RectangleCoverRun R blocked previous stock selected) :
    ∀ i∈selected, i∈stock := by
  induction h with
  | stop => simp
  | step previous stock i tail hi _ _ htail ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact rectangleRemaining_subset blocked previous stock i (ih j hj)

theorem selected_nodup (h : RectangleCoverRun R blocked previous stock selected) : selected.Nodup := by
  induction h with
  | stop => simp
  | step previous stock i tail _ _ _ htail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hi
    have hm := htail.selected_subset i hi
    exact (mem_rectangleRemaining blocked previous stock i i).mp hm |>.2.1 rfl


theorem rejected_blocked (h : RectangleCoverRun R blocked previous stock selected)
    (hmono : ∀ s t : Finset ι, s⊆t → ∀ i, blocked s i → blocked t i) :
    ∀ i∈stock, i∉selected → blocked (previous ∪ selected.toFinset) i := by
  classical
  induction h with
  | stop => simp
  | step previous stock r tail hr hp ha htail ih =>
    intro i hi hnot
    have hir : i≠r := by
      intro heq
      subst i
      exact hnot (List.mem_cons_self)
    have hint : i∉tail := fun hit => hnot (List.mem_cons_of_mem r hit)
    by_cases hn : i∈rectangleRemaining blocked previous stock r
    · have hh := ih i hn hint
      have heq : insert r previous ∪ tail.toFinset=previous ∪ (r::tail).toFinset := by
        ext j
        simp
      simpa only [heq] using hh
    · have hb : blocked (insert r previous) i := by
        by_contra hb
        exact hn ((mem_rectangleRemaining blocked previous stock r i).mpr ⟨hi,hir,hb⟩)
      apply hmono (insert r previous) (previous ∪ (r::tail).toFinset) _ i hb
      intro j hj
      simp only [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · simp
      · exact Finset.mem_union_left _ hj

end RectangleCoverRun
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LaceyLiSelectionCover
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual discarded-family covering estimate in the Lacey--Li
selection algorithm. The remaining energy estimate is geometric. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype κ]

theorem rectangleCount_mono (R : ι → Rectangle) {s t : Finset ι} (h : s ⊆ t) :
    rectangleCount R s ≤ rectangleCount R t := by
  intro x
  exact Finset.sum_le_sum_of_subset h

theorem maximalBlocked_mono (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle)
    (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) {s t : Finset ι} (hst : s ⊆ t) (i : ι)
    (hi : maximalBlocked e R a ha η s i) : maximalBlocked e R a ha η t i := by
  intro x hx
  exact (hi hx).trans_le (positiveAuxiliary_mono e (rectangleCount_mono _ hst) x)

theorem not_maximalBlocked_empty (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle)
    (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (i : ι) : ¬maximalBlocked e R a ha η ∅ i := by
  intro h
  have hc : (R i).center ∈ (R i).carrier := by
    constructor <;> simp only [sub_self,map_zero,PiLp.zero_apply,abs_zero] <;>
      linarith [(R i).short_pos,(R i).long_pos]
  have hh := h hc
  change η < positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a ha) ∅) (R i).center at hh
  have hz : rectangleCount (fun j => (R j).dilate a ha) ∅ = fun _ => 0 := by
    funext x
    simp [rectangleCount]
  rw [hz,positiveAuxiliary_zero] at hh
  exact not_lt_zero hh

theorem rectangle_cover_run_maximal_exists [DecidableEq ι]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle)
    (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (stock : Finset ι) :
    ∃ selected, RectangleCoverRun R (maximalBlocked e R a ha η) ∅ stock selected :=
  rectangle_cover_run_exists R (maximalBlocked e R a ha η) stock ∅
    (fun i _ => not_maximalBlocked_empty e R a ha η i)

theorem maximal_selection_cover_bound [DecidableEq ι]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (he : ∀ i, MeasurePreserving (e i) volume (volume.prod volume))
    (R : ι → Rectangle) (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞)
    (hη : η ≠ 0) (hηtop : η ≠ ∞) (stock : Finset ι) (selected : List ι)
    (hrun : RectangleCoverRun R (maximalBlocked e R a ha η) ∅ stock selected) :
    volume (⋃ i ∈ stock, (R i).carrier) ≤
      (1 + (9 + 3 * Fintype.card κ) * η⁻¹ * ENNReal.ofReal (a^2)) *
        ∑ i ∈ selected.toFinset, volume (R i).carrier := by
  let count := rectangleCount (fun i => (R i).dilate a ha) selected.toFinset
  let E := {x | η < positiveAuxiliary e count x}
  have hb : ∀ i ∈ stock, i ∉ selected → (R i).carrier ⊆ E := by
    intro i hi hnot
    have h := hrun.rejected_blocked
      (fun s t hst i hi => maximalBlocked_mono e R a ha η hst i hi) i hi hnot
    simpa only [Finset.empty_union,maximalBlocked] using h
  have hsub : (⋃ i ∈ stock, (R i).carrier) ⊆
      (⋃ i ∈ selected.toFinset, (R i).carrier) ∪ E := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
    by_cases hs : i ∈ selected
    · exact Or.inl (mem_iUnion₂.mpr ⟨i,List.mem_toFinset.mpr hs,hxi⟩)
    · exact Or.inr (hb i hi hs hxi)
  have hmass : (∫⁻ x, count x) = ENNReal.ofReal (a^2) *
      ∑ i ∈ selected.toFinset, volume (R i).carrier := by
    rw [rectangleCount_first_moment]
    simp_rw [Rectangle.volume_dilate]
    rw [Finset.mul_sum]
  have hweak := positiveAuxiliary_weak_L1 e he
    (rectangleCount_measurable (fun i : ι => (R i).dilate a ha) selected.toFinset) η hη hηtop
  change volume E ≤ _ at hweak
  rw [hmass] at hweak
  calc
    _ ≤ volume ((⋃ i ∈ selected.toFinset, (R i).carrier) ∪ E) := measure_mono hsub
    _ ≤ volume (⋃ i ∈ selected.toFinset, (R i).carrier) + volume E := measure_union_le _ _
    _ ≤ (∑ i ∈ selected.toFinset, volume (R i).carrier) +
        (9 + 3 * Fintype.card κ) * η⁻¹ * (ENNReal.ofReal (a^2) *
        ∑ i ∈ selected.toFinset, volume (R i).carrier) :=
      add_le_add (measure_biUnion_finset_le _ _) hweak
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FatRectangleSum
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square averages control overlap with targets of bounded eccentricity. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid
variable {ι κ : Type*} [Fintype κ]

theorem rectangleCount_on_carrier (R : ι → Rectangle) (s : Finset ι) (T : Rectangle) :
    (∫⁻ x in T.carrier, rectangleCount R s x) = ∑ j ∈ s, volume (T.carrier ∩ (R j).carrier) := by
  unfold rectangleCount
  rw [lintegral_finsetSum s (fun j _ => measurable_const.indicator (R j).measurableSet_carrier)]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_indicator (R j).measurableSet_carrier,lintegral_const,
    Measure.restrict_restrict (R j).measurableSet_carrier,Measure.restrict_apply_univ,one_mul,inter_comm]

theorem rectangleCount_dilate_le (R : ι → Rectangle) (s : Finset ι) (a : ℝ) (ha : 1 ≤ a) :
    rectangleCount R s ≤ rectangleCount (fun j => (R j).dilate a (by linarith)) s := by
  intro x
  apply Finset.sum_le_sum
  intro j _
  by_cases hx : x ∈ (R j).carrier
  · have hx' := (R j).carrier_subset_dilate a ha hx
    simp only [indicator_of_mem hx,indicator_of_mem hx',le_refl]
  · simp only [indicator_of_notMem hx]
    exact zero_le

theorem rectangle_in_centeredSquare (T : Rectangle) (x : Plane) (hx : x ∈ T.carrier) :
    planeCoordinates ⁻¹' T.carrier ⊆ centeredSquare (planeCoordinates.symm x) (2*T.long) := by
  intro z hz
  have hd : ‖planeCoordinates z-x‖ ≤ 2*T.long := by
    simpa only [dist_eq_norm] using T.dist_le_two_long hz hx
  have h0 : |z.1-(planeCoordinates.symm x).1| ≤ 2*T.long := by
    have h := PiLp.norm_apply_le (planeCoordinates z-x) (0 : Fin 2)
    have hc : |z.1-(planeCoordinates.symm x).1| ≤ ‖planeCoordinates z-x‖ := by
      simpa [Real.norm_eq_abs,PiLp.sub_apply,planeCoordinates_apply,planeCoordinates_symm_apply] using h
    exact hc.trans hd
  have h1 : |z.2-(planeCoordinates.symm x).2| ≤ 2*T.long := by
    have h := PiLp.norm_apply_le (planeCoordinates z-x) (1 : Fin 2)
    have hc : |z.2-(planeCoordinates.symm x).2| ≤ ‖planeCoordinates z-x‖ := by
      simpa [Real.norm_eq_abs,PiLp.sub_apply,planeCoordinates_apply,planeCoordinates_symm_apply] using h
    exact hc.trans hd
  change (z.1 ∈ Icc _ _) ∧ (z.2 ∈ Icc _ _)
  constructor <;> constructor <;> linarith [abs_le.mp h0,abs_le.mp h1]

theorem fat_intersection_sum_le_auxiliary (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (R : ι → Rectangle) (s : Finset ι) (T : Rectangle) (B : ℝ) (hB : 0 ≤ B)
    (hfat : T.long ≤ B*T.short) (a : ℝ) (ha : 1 ≤ a)
    (x : Plane) (hx : x ∈ T.carrier) :
    (∑ j ∈ s, volume (T.carrier ∩ (R j).carrier)) ≤
      ENNReal.ofReal (576*B) * volume T.carrier *
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a (by linarith)) s) x := by
  let g := rectangleCount (fun j => (R j).dilate a (by linarith)) s
  let c := planeCoordinates.symm x
  let r := 2*T.long
  have hr : 0 < r := mul_pos (by norm_num) T.long_pos
  have hsub := rectangle_in_centeredSquare T x hx
  have hmass : (∫⁻ y in T.carrier, g y) =
      ∫⁻ z in planeCoordinates ⁻¹' T.carrier, g (planeCoordinates z) ∂volume.prod volume :=
    (planeCoordinates_measurePreserving.setLIntegral_comp_preimage T.measurableSet_carrier
      (rectangleCount_measurable _ _)).symm
  have hcenter : planeCoordinates.symm x ∈ centeredSquare c r := by
    change (c.1 ∈ Icc (c.1-r) (c.1+r)) ∧ (c.2 ∈ Icc (c.2-r) (c.2+r))
    constructor <;> constructor <;> linarith
  have haux := positiveAuxiliary_square_integral e g c r hr x hcenter
  have hcoef : (36:ℝ≥0∞)*(volume.prod volume) (centeredSquare c r) ≤
      ENNReal.ofReal (576*B)*volume T.carrier := by
    rw [centeredSquare_volume,Rectangle.volume_carrier]
    have he : (36:ℝ≥0∞)* (ENNReal.ofReal (2*r)*ENNReal.ofReal (2*r)) =
        ENNReal.ofReal (576*T.long^2) := by
      have hr0 : 0 ≤ 2*r := by positivity
      rw [←ENNReal.ofReal_mul hr0,show (36:ℝ≥0∞)=ENNReal.ofReal 36 by norm_num,
        ←ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp [r]
      ring
    rw [he,←mul_assoc,←ENNReal.ofReal_mul (by positivity : 0 ≤ 576*B),
      ←ENNReal.ofReal_mul (mul_nonneg (by positivity : 0 ≤ 576*B) T.long_pos.le)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left hfat T.long_pos.le
    nlinarith
  calc
    _ = ∫⁻ y in T.carrier, rectangleCount R s y := (rectangleCount_on_carrier R s T).symm
    _ ≤ ∫⁻ y in T.carrier, g y := lintegral_mono (rectangleCount_dilate_le R s a ha)
    _ = _ := hmass
    _ ≤ ∫⁻ z in centeredSquare c r, g (planeCoordinates z) ∂volume.prod volume := lintegral_mono_set hsub
    _ ≤ 36*(volume.prod volume) (centeredSquare c r)*positiveAuxiliary e g x := haux
    _ ≤ _ := mul_le_mul' hcoef le_rfl

theorem fat_selected_overlap_bound (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (R : ι → Rectangle) (s previous : Finset ι) (hs : s ⊆ previous) (r : ι)
    (B : ℝ) (hB : 0 ≤ B) (hfat : (R r).long ≤ B*(R r).short)
    (a : ℝ) (ha : 1 ≤ a) (η : ℝ≥0∞) (hη : ENNReal.ofReal (576*B)*η ≤ 1)
    (hnot : ¬maximalBlocked e R a (by linarith) η previous r) :
    (∑ j ∈ s, volume ((R r).carrier ∩ (R j).carrier)) ≤ volume (R r).carrier := by
  classical
  let g := rectangleCount (fun j => (R j).dilate a (by linarith)) previous
  have hpoint : ∃ x ∈ (R r).carrier, positiveAuxiliary e g x ≤ η := by
    by_contra hn
    push Not at hn
    exact hnot hn
  obtain ⟨x,hx,hvalue⟩ := hpoint
  have hlocal := fat_intersection_sum_le_auxiliary e R s (R r) B hB hfat a ha x hx
  have hm := positiveAuxiliary_mono e
    (rectangleCount_mono (fun j => (R j).dilate a (by linarith)) hs) x
  calc
    _ ≤ ENNReal.ofReal (576*B)*volume (R r).carrier *
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a (by linarith)) s) x := hlocal
    _ ≤ ENNReal.ofReal (576*B)*volume (R r).carrier*η := mul_le_mul' le_rfl (hm.trans hvalue)
    _ = (ENNReal.ofReal (576*B)*η)*volume (R r).carrier := by ring
    _ ≤ 1*volume (R r).carrier := mul_le_mul' hη le_rfl
    _ = _ := one_mul _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_NearRectangleSection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A transverse section bound for intersecting rectangles. This is the
area-to-line reduction behind the near-angle part of Lacey--Li (3.5). -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

theorem coordinate_difference (S : Rectangle) (x y : Plane) (i : Fin 2) :
    S.axes.repr (y-S.center) i-S.axes.repr (x-S.center) i = S.axes.repr (y-x) i := by
  simp only [S.axes.repr_apply_apply,inner_sub_right]
  ring

theorem near_intersection_coordinates (R S : Rectangle) (x : Plane) (hx : x ∈ R.carrier)
    (A : ℝ) (hangle : R.long * dist (S.axes 0) (R.axes 0) ≤ A * R.short) :
    S.orthogonalCoordinates '' (R.carrier ∩ S.carrier) ⊆
      Icc ((S.orthogonalCoordinates x).1-2*R.long) ((S.orthogonalCoordinates x).1+2*R.long) ×ˢ
        nearSection R S x (A+1) := by
  rintro z ⟨y,hy,rfl⟩
  have hlong : |S.axes.repr (y-S.center) 0-S.axes.repr (x-S.center) 0| ≤ 2*R.long := by
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (y-x) 0).trans (by simpa only [dist_eq_norm] using R.dist_le_two_long hy.1 hx)
  have hshort : |S.axes.repr (y-S.center) 1-S.axes.repr (x-S.center) 1| ≤ (A+1)*R.short := by
    rw [coordinate_difference]
    exact (S.transverse_difference_le R hy.1 hx).trans (by nlinarith [R.short_pos])
  simp only [orthogonalCoordinates_apply,nearSection,mem_prod,mem_inter_iff,mem_Icc]
  change (_ ∧ _) ∧ (_ ∧ _)
  constructor
  · obtain ⟨hl,hu⟩ := abs_le.mp hlong
    constructor <;> linarith
  · refine ⟨?_,?_⟩
    · simpa only [neg_div] using abs_le.mp hy.2.2
    · obtain ⟨hl,hu⟩ := abs_le.mp hshort
      constructor <;> linarith

theorem near_intersection_area (R S : Rectangle) (x : Plane) (hx : x ∈ R.carrier)
    (A : ℝ) (hangle : R.long * dist (S.axes 0) (R.axes 0) ≤ A * R.short) :
    volume (R.carrier ∩ S.carrier) ≤
      ENNReal.ofReal (4*R.long) * volume (nearSection R S x (A+1)) := by
  have he : (volume.prod volume) (S.orthogonalCoordinates '' (R.carrier ∩ S.carrier)) =
      volume (R.carrier ∩ S.carrier) := by
    have h := S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv
      (S.orthogonalCoordinates '' (R.carrier ∩ S.carrier))
    rw [Set.preimage_image_eq _ S.orthogonalCoordinates.injective] at h
    exact h.symm
  rw [←he]
  refine (measure_mono (near_intersection_coordinates R S x hx A hangle)).trans_eq ?_
  rw [Measure.prod_prod,Real.volume_Icc]
  congr 2
  ring

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_NearRectangleLine
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection of a transverse rectangle section onto an actual line.
The dilation is explicit, and no geometric covering hypothesis is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

theorem line_coordinate (S : Rectangle) (x w : Plane) (t : ℝ) (i : Fin 2) :
    S.axes.repr (x+t • w-S.center) i =
      S.axes.repr (x-S.center) i+t*S.axes.repr w i := by
  have he : x+t • w-S.center = (x-S.center)+t • w := by abel
  rw [he,map_add,PiLp.add_apply,map_smul]
  rfl

theorem projectionTime_bound (R S : Rectangle) (x w : Plane) (B : ℝ)
    (hB : 0 ≤ B) (hw : 1/2 ≤ |S.axes.repr w 1|)
    {u : ℝ} (hu : u ∈ nearSection R S x B) :
    |S.projectionTime x w u| ≤ 2*B*R.short := by
  have hd : 0 < |S.axes.repr w 1| := by linarith
  have hh : |u-(S.orthogonalCoordinates x).2| ≤ B*R.short := by
    apply abs_le.mpr
    constructor <;> linarith [hu.2.1,hu.2.2]
  rw [projectionTime,abs_div]
  apply (div_le_iff₀ hd).mpr
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hB R.short_pos.le))
  nlinarith

theorem projected_point_mem_dilate (R S : Rectangle) (x w : Plane)
    (hx : x ∈ R.carrier) (hint : (R.carrier ∩ S.carrier).Nonempty)
    (hL : R.long ≤ S.long) (B : ℝ) (hB : 0 ≤ B) (hw : ‖w‖ ≤ 1)
    (htrans : 1/2 ≤ |S.axes.repr w 1|) {u : ℝ} (hu : u ∈ nearSection R S x B) :
    x+S.projectionTime x w u • w ∈ (S.dilate (4*B+5) (by linarith)).carrier := by
  obtain ⟨y,hyR,hyS⟩ := hint
  have hdist : |S.axes.repr (x-S.center) 0-S.axes.repr (y-S.center) 0| ≤ 2*R.long := by
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (x-y) 0).trans (by simpa only [dist_eq_norm] using R.dist_le_two_long hx hyR)
  have hxl : |S.axes.repr (x-S.center) 0| ≤ 5*S.long/2 := by
    calc
      _ = |(S.axes.repr (x-S.center) 0-S.axes.repr (y-S.center) 0)+S.axes.repr (y-S.center) 0| := by congr 1; ring
      _ ≤ |S.axes.repr (x-S.center) 0-S.axes.repr (y-S.center) 0|+|S.axes.repr (y-S.center) 0| := abs_add_le _ _
      _ ≤ 5*S.long/2 := by linarith [hyS.1]
  have ht := projectionTime_bound R S x w B hB htrans hu
  have hw0 : |S.axes.repr w 0| ≤ 1 := (S.abs_coordinate_le_norm w 0).trans hw
  have hprod : |S.projectionTime x w u * S.axes.repr w 0| ≤ 2*B*R.short := by
    rw [abs_mul]
    have h := mul_le_mul ht hw0 (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hB) R.short_pos.le)
    simpa only [mul_one] using h
  constructor
  · change |S.axes.repr (x+S.projectionTime x w u • w-S.center) 0| ≤ (4*B+5)*S.long/2
    rw [line_coordinate]
    have hs := mul_le_mul_of_nonneg_left (R.short_le_long.trans hL) (by linarith : 0 ≤ 2*B)
    exact (abs_add_le _ _).trans (by nlinarith)
  · change |S.axes.repr (x+S.projectionTime x w u • w-S.center) 1| ≤ (4*B+5)*S.short/2
    have hd : S.axes.repr w 1 ≠ 0 := by intro hd; norm_num [hd] at htrans
    rw [line_coordinate,projectionTime,div_mul_cancel₀ _ hd]
    have he : S.axes.repr (x-S.center) 1+(u-(S.orthogonalCoordinates x).2)=u := by
      rw [orthogonalCoordinates_apply]
      ring
    rw [he]
    have huabs : |u| ≤ S.short/2 := abs_le.mpr (by simpa only [mem_Icc,neg_div] using hu.1)
    nlinarith [S.short_pos]

theorem nearSection_measurable (R S : Rectangle) (x : Plane) (B : ℝ) :
    MeasurableSet (nearSection R S x B) := measurableSet_Icc.inter measurableSet_Icc

theorem nearLineParameters_subset (R S : Rectangle) (x w : Plane)
    (hx : x ∈ R.carrier) (hint : (R.carrier ∩ S.carrier).Nonempty)
    (hL : R.long ≤ S.long) (B : ℝ) (hB : 0 ≤ B) (hw : ‖w‖ ≤ 1)
    (htrans : 1/2 ≤ |S.axes.repr w 1|) :
    nearLineParameters R S x w B ⊆ Icc (-2*B*R.short) (2*B*R.short) ∩
      {t | x+t • w ∈ (S.dilate (4*B+5) (by linarith)).carrier} := by
  intro t ht
  have hu : (S.orthogonalCoordinates x).2+t*S.axes.repr w 1 ∈ nearSection R S x B := ht
  have hd : S.axes.repr w 1 ≠ 0 := by intro hd; norm_num [hd] at htrans
  have he : S.projectionTime x w ((S.orthogonalCoordinates x).2+t*S.axes.repr w 1)=t := by
    unfold projectionTime
    field_simp [hd]
    ring
  have hb := projectionTime_bound R S x w B hB htrans hu
  have hm := projected_point_mem_dilate R S x w hx hint hL B hB hw htrans hu
  rw [he] at hb hm
  exact ⟨by simpa only [mem_Icc,neg_mul] using abs_le.mp hb,hm⟩

theorem nearSection_le_lineParameters (R S : Rectangle) (x w : Plane) (B : ℝ)
    (hw : ‖w‖ ≤ 1) (htrans : 1/2 ≤ |S.axes.repr w 1|) :
    volume (nearSection R S x B) ≤ volume (nearLineParameters R S x w B) := by
  have hd : S.axes.repr w 1 ≠ 0 := by intro hd; norm_num [hd] at htrans
  have he : nearLineParameters R S x w B =
      (fun t : ℝ => t*S.axes.repr w 1) ⁻¹'
      ((fun u : ℝ => (S.orthogonalCoordinates x).2+u) ⁻¹' nearSection R S x B) := rfl
  rw [he,Real.volume_preimage_mul_right hd,
    (measurePreserving_add_left volume (S.orthogonalCoordinates x).2).measure_preimage
      (nearSection_measurable R S x B).nullMeasurableSet]
  have hcoord : |S.axes.repr w 1| ≤ 1 := (S.abs_coordinate_le_norm w 1).trans hw
  have hi : (1:ℝ) ≤ |(S.axes.repr w 1)⁻¹| := by
    rw [abs_inv]
    exact (one_le_inv₀ (abs_pos.mpr hd)).mpr hcoord
  calc
    _ = 1 * volume (nearSection R S x B) := (one_mul _).symm
    _ ≤ _ := mul_le_mul' (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hi) le_rfl

theorem nearSection_le_line_integral (R S : Rectangle) (x w : Plane)
    (hx : x ∈ R.carrier) (hint : (R.carrier ∩ S.carrier).Nonempty)
    (hL : R.long ≤ S.long) (B : ℝ) (hB : 0 ≤ B) (hw : ‖w‖ ≤ 1)
    (htrans : 1/2 ≤ |S.axes.repr w 1|) :
    volume (nearSection R S x B) ≤
      ∫⁻ t in Icc (-2*B*R.short) (2*B*R.short),
        (S.dilate (4*B+5) (by linarith)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (x+t • w) := by
  have hline : MeasurableSet {t : ℝ | x+t • w ∈ (S.dilate (4*B+5) (by linarith)).carrier} :=
    (S.dilate (4*B+5) (by linarith)).measurableSet_carrier.preimage (by fun_prop)
  have he : (fun t : ℝ => (S.dilate (4*B+5) (by linarith)).carrier.indicator
      (fun _ => (1:ℝ≥0∞)) (x+t • w)) =
      {t : ℝ | x+t • w ∈ (S.dilate (4*B+5) (by linarith)).carrier}.indicator (fun _ => (1:ℝ≥0∞)) := by
    funext t
    by_cases ht : x+t • w ∈ (S.dilate (4*B+5) (by linarith)).carrier <;> simp [ht]
  rw [he,lintegral_indicator hline,lintegral_const,Measure.restrict_restrict hline,
    Measure.restrict_apply_univ,one_mul]
  exact (nearSection_le_lineParameters R S x w B hw htrans).trans
    (measure_mono (by simpa only [inter_comm] using nearLineParameters_subset R S x w hx hint hL B hB hw htrans))

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleLineCoordinates
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact parameter changes for the line averages in the near-angle
rectangle estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

theorem orthogonalCoordinates_symm_line (D : Rectangle) (x : Plane) (t : ℝ) :
    D.orthogonalCoordinates.symm ((D.orthogonalCoordinates x).1+t,(D.orthogonalCoordinates x).2) =
      x+t • D.axes 0 := by
  apply D.orthogonalCoordinates.injective
  rw [D.orthogonalCoordinates.apply_symm_apply]
  apply Prod.ext
  · change D.axes.repr (x-D.center) 0+t = D.axes.repr (x+t • D.axes 0-D.center) 0
    rw [line_coordinate]
    simp
  · change D.axes.repr (x-D.center) 1 = D.axes.repr (x+t • D.axes 0-D.center) 1
    rw [line_coordinate]
    simp

theorem line_integral_change_origin (D : Rectangle) {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (x : Plane) (r : ℝ) :
    (∫⁻ t in Icc (-r) r, f (x+t • D.axes 0)) =
      ∫⁻ u in Icc ((D.orthogonalCoordinates x).1-r) ((D.orthogonalCoordinates x).1+r),
        f (D.orthogonalCoordinates.symm (u,(D.orthogonalCoordinates x).2)) := by
  let c := (D.orthogonalCoordinates x).1
  let b := (D.orthogonalCoordinates x).2
  have hF : Measurable (fun u : ℝ => f (D.orthogonalCoordinates.symm (u,b))) :=
    (hf.comp D.orthogonalCoordinates.symm.measurable).comp (measurable_id.prodMk measurable_const)
  have he : (fun t : ℝ => c+t) ⁻¹' Icc (c-r) (c+r) = Icc (-r) r := by
    ext t
    simp only [mem_preimage,mem_Icc]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hh := (measurePreserving_add_left volume c).setLIntegral_comp_preimage (s := Icc (c-r) (c+r)) measurableSet_Icc hF
  rw [he] at hh
  calc
    _ = ∫⁻ t in Icc (-r) r, f (D.orthogonalCoordinates.symm (c+t,b)) := by
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall (fun t => congrArg f (D.orthogonalCoordinates_symm_line x t).symm)
    _ = _ := hh

theorem near_intersection_line_integral (R S D : Rectangle) (x : Plane)
    (hx : x ∈ R.carrier) (hint : (R.carrier ∩ S.carrier).Nonempty) (hL : R.long ≤ S.long)
    (A : ℝ) (hA : 0 ≤ A)
    (hangle : R.long * dist (S.axes 0) (R.axes 0) ≤ A * R.short)
    (htrans : 1/2 ≤ |S.axes.repr (D.axes 0) 1|) :
    volume (R.carrier ∩ S.carrier) ≤ ENNReal.ofReal (4*R.long) *
      ∫⁻ u in Icc ((D.orthogonalCoordinates x).1-2*(A+1)*R.short)
          ((D.orthogonalCoordinates x).1+2*(A+1)*R.short),
        (S.dilate (4*(A+1)+5) (by linarith)).carrier.indicator (fun _ => (1:ℝ≥0∞))
          (D.orthogonalCoordinates.symm (u,(D.orthogonalCoordinates x).2)) := by
  have hb : 0 ≤ A+1 := by linarith
  have hw : ‖D.axes 0‖ ≤ 1 := by rw [D.axes.norm_eq_one]
  have h := (near_intersection_area R S x hx A hangle).trans
    (mul_le_mul' le_rfl (nearSection_le_line_integral R S x (D.axes 0) hx hint hL (A+1) hb hw htrans))
  have he := line_integral_change_origin D
    (f := (S.dilate (4*(A+1)+5) (by linarith)).carrier.indicator (fun _ => (1:ℝ≥0∞)))
    (measurable_const.indicator (S.dilate (4*(A+1)+5) (by linarith)).measurableSet_carrier)
    x (2*(A+1)*R.short)
  simp only [neg_mul] at h
  rw [he] at h
  exact h

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_StripProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A section-width estimate for projection onto a line. Applied to the
actual popularity sets in orthogonal rectangle coordinates. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem strip_projection_area (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (P : Set ℝ) (hP : MeasurableSet P) (a b c w : ℝ) (hb : b ≠ 0) (_hw : 0 ≤ w)
    (hproj : ∀ z ∈ E, z.1 ∈ P) (hstrip : ∀ z ∈ E, |a*z.1+b*z.2-c| ≤ w) :
    (volume.prod volume) E ≤ ENNReal.ofReal (2*w/|b|)*volume P := by
  have hsection (x : ℝ) : volume ((fun y => (x,y)) ⁻¹' E) ≤
      P.indicator (fun _ => ENNReal.ofReal (2*w/|b|)) x := by
    by_cases hx : x ∈ P
    · rw [indicator_of_mem hx]
      have hs : ((fun y => (x,y)) ⁻¹' E) ⊆
          (fun y : ℝ => b*y) ⁻¹' Icc (c-a*x-w) (c-a*x+w) := by
        intro y hy
        have h := abs_le.mp (hstrip (x,y) hy)
        constructor <;> dsimp at h ⊢ <;> linarith
      calc
        _ ≤ volume ((fun y : ℝ => b*y) ⁻¹' Icc (c-a*x-w) (c-a*x+w)) := measure_mono hs
        _ = ENNReal.ofReal |b⁻¹| * ENNReal.ofReal (2*w) := by
          rw [Real.volume_preimage_mul_left hb,Real.volume_Icc]
          congr 2
          ring
        _ = _ := by
          rw [←ENNReal.ofReal_mul (abs_nonneg _)]
          congr 1
          rw [abs_inv,div_eq_mul_inv]
          ring
    · rw [indicator_of_notMem hx]
      have hs : ((fun y => (x,y)) ⁻¹' E) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hx (hproj (x,y) hy)
      simp only [hs,measure_empty,le_refl]
  rw [Measure.prod_apply hE]
  calc
    _ ≤ ∫⁻ x, P.indicator (fun _ => ENNReal.ofReal (2*w/|b|)) x := lintegral_mono hsection
    _ = _ := by rw [lintegral_indicator hP,lintegral_const,Measure.restrict_apply_univ,mul_comm]

theorem strip_projection_area_half (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (P : Set ℝ) (hP : MeasurableSet P) (a b c w : ℝ) (hb : 1/2 ≤ |b|) (hw : 0 ≤ w)
    (hproj : ∀ z ∈ E, z.1 ∈ P) (hstrip : ∀ z ∈ E, |a*z.1+b*z.2-c| ≤ w) :
    (volume.prod volume) E ≤ ENNReal.ofReal (4*w)*volume P := by
  have hb0 : 0 < |b| := by linarith
  have hbne : b ≠ 0 := by intro he; norm_num [he] at hb
  refine (strip_projection_area E hE P hP a b c w hbne hw hproj hstrip).trans ?_
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_iff₀ hb0).mpr
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_NearRectangleSum
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The near-angle intersection sum is controlled by the actual
auxiliary maximal function, pointwise on the target rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype κ]

theorem near_intersection_sum_le_auxiliary (D : κ → Rectangle) (R : ι → Rectangle)
    (s : Finset ι) (T : Rectangle) (i : κ) (A : ℝ) (hA : 0 ≤ A)
    (hL : ∀ j ∈ s, T.long ≤ (R j).long)
    (hangle : ∀ j ∈ s, T.long * dist ((R j).axes 0) (T.axes 0) ≤ A*T.short)
    (htrans : ∀ j ∈ s, 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1|)
    (x : Plane) (hx : x ∈ T.carrier) :
    (∑ j ∈ s, volume (T.carrier ∩ (R j).carrier)) ≤
      ENNReal.ofReal (96*(A+1)) * volume T.carrier *
        positiveAuxiliary (fun i => (D i).orthogonalCoordinates)
          (rectangleCount (fun j => (R j).dilate (4*(A+1)+5) (by linarith)) s) x := by
  let a := 4*(A+1)+5
  have ha : 0 < a := by dsimp [a]; linarith
  let g := rectangleCount (fun j => (R j).dilate a ha) s
  let e := (D i).orthogonalCoordinates
  let c := (e x).1
  let b := (e x).2
  let r := 2*(A+1)*T.short
  have hr : 0 < r := mul_pos (by linarith) T.short_pos
  let I := Icc (c-r) (c+r)
  let P := fun u : ℝ => e.symm (u,b)
  have hP : Measurable P := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hint (j : ι) : Measurable (fun u => ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u)) :=
    (measurable_const.indicator ((R j).dilate a ha).measurableSet_carrier).comp hP
  have hsum : (∫⁻ u in I, g (P u)) = ∑ j ∈ s,
      ∫⁻ u in I, ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    exact lintegral_finsetSum s (fun j _ => hint j)
  have hterm (j : ι) (hj : j ∈ s) : volume (T.carrier ∩ (R j).carrier) ≤
      ENNReal.ofReal (4*T.long) * ∫⁻ u in I,
        ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    by_cases hn : (T.carrier ∩ (R j).carrier).Nonempty
    · exact Rectangle.near_intersection_line_integral T (R j) (D i) x hx hn (hL j hj)
        A hA (hangle j hj) (htrans j hj)
    · rw [Set.not_nonempty_iff_eq_empty.mp hn,measure_empty]
      exact zero_le
  have haux := positiveAuxiliary_line_integral (fun j => (D j).orthogonalCoordinates)
    g i c r hr x (show (e x).1 ∈ Icc (c-r) (c+r) by constructor <;> dsimp [c] <;> linarith)
  have hc : ENNReal.ofReal (4*T.long)*6*ENNReal.ofReal (2*r) =
      ENNReal.ofReal (96*(A+1))*volume T.carrier := by
    have hp4 : 0 ≤ 4*T.long := mul_nonneg (by norm_num) T.long_pos.le
    have hp96 : 0 ≤ 96*(A+1) := mul_nonneg (by norm_num) (by linarith)
    calc
      _ = ENNReal.ofReal ((4*T.long)*6*(2*r)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hp4 (by norm_num)),ENNReal.ofReal_mul hp4]
        norm_num
      _ = ENNReal.ofReal ((96*(A+1))*T.long*T.short) := by congr 1; dsimp [r]; ring
      _ = _ := by
        rw [Rectangle.volume_carrier,ENNReal.ofReal_mul (mul_nonneg hp96 T.long_pos.le),ENNReal.ofReal_mul hp96]
        ring
  calc
    _ ≤ ∑ j ∈ s, ENNReal.ofReal (4*T.long) * ∫⁻ u in I,
        ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (4*T.long) * ∫⁻ u in I, g (P u) := by rw [hsum,Finset.mul_sum]
    _ ≤ ENNReal.ofReal (4*T.long) * (6*ENNReal.ofReal (2*r)*
        positiveAuxiliary (fun j => (D j).orthogonalCoordinates) g x) := mul_le_mul' le_rfl haux
    _ = _ := by rw [←mul_assoc,←mul_assoc,hc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_NearSelectionBound
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The near-angle selected overlap bound: maximal non-removal supplies
one point, and the explicit section estimate controls every near pair. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype κ]

theorem near_selected_overlap_bound (D : κ → Rectangle) (R : ι → Rectangle)
    (s previous : Finset ι) (r : ι) (i : κ) (A : ℝ) (hA : 0 ≤ A)
    (hs : s ⊆ previous) (η : ℝ≥0∞) (hη : ENNReal.ofReal (96*(A+1))*η ≤ 1)
    (hL : ∀ j ∈ s, (R r).long ≤ (R j).long)
    (hangle : ∀ j ∈ s, (R r).long * dist ((R j).axes 0) ((R r).axes 0) ≤ A*(R r).short)
    (htrans : ∀ j ∈ s, 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1|)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      (4*(A+1)+5) (by linarith) η previous r) :
    (∑ j ∈ s, volume ((R r).carrier ∩ (R j).carrier)) ≤ volume (R r).carrier := by
  classical
  let a := 4*(A+1)+5
  have ha : 0 < a := by dsimp [a]; linarith
  let g := rectangleCount (fun j => (R j).dilate a ha) previous
  let e := fun i => (D i).orthogonalCoordinates
  have hpoint : ∃ x ∈ (R r).carrier, positiveAuxiliary e g x ≤ η := by
    by_contra hn
    push Not at hn
    apply hnot
    exact hn
  obtain ⟨x,hx,hvalue⟩ := hpoint
  have hnear := near_intersection_sum_le_auxiliary D R s (R r) i A hA hL hangle htrans x hx
  have hm := positiveAuxiliary_mono e
    (rectangleCount_mono (fun j => (R j).dilate a ha) hs) x
  calc
    _ ≤ ENNReal.ofReal (96*(A+1))*volume (R r).carrier *
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a ha) s) x := hnear
    _ ≤ ENNReal.ofReal (96*(A+1))*volume (R r).carrier * η :=
      mul_le_mul' le_rfl (hm.trans hvalue)
    _ = (ENNReal.ofReal (96*(A+1))*η)*volume (R r).carrier := by ring
    _ ≤ 1*volume (R r).carrier := mul_le_mul' hη le_rfl
    _ = _ := one_mul _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FiniteTransverseDirections
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite family of transverse directions. Compactness supplies
a universal net, independent of the rectangles later selected. -/
noncomputable section
open Set MeasureTheory Metric
namespace LipschitzHilbert.Rectangle

theorem transverseFrame_axis (R : Rectangle) : (transverseFrame R).axes 0 = R.axes 1 := by
  simp [transverseFrame]

theorem exists_finite_transverse_directions :
    ∃ n : ℕ, ∃ D : Fin n → Rectangle, ∀ R : Rectangle,
      ∃ i : Fin n, dist ((D i).axes 0) (R.axes 1) < 1/4 := by
  classical
  let S : Set Plane := Set.range (fun R : Rectangle => R.axes 0)
  have hS : S ⊆ sphere (0:Plane) 1 := by
    rintro w ⟨R,rfl⟩
    simpa only [mem_sphere,dist_zero_right] using R.axes.norm_eq_one 0
  have hcomp : IsCompact (closure S) :=
    (isCompact_sphere (0:Plane) 1).of_isClosed_subset isClosed_closure (closure_minimal hS isClosed_sphere)
  obtain ⟨C,hCS,hCf,hcover⟩ := exists_finite_cover_balls_of_isCompact_closure hcomp (by norm_num : (0:ℝ) < 1/4)
  let : Fintype C := hCf.fintype
  have hc (y : C) : ∃ R : Rectangle, R.axes 0 = y.val := hCS y.property
  choose D hD using hc
  let e := Fintype.equivFin C
  refine ⟨Fintype.card C,fun i => D (e.symm i),?_⟩
  intro R
  have hr : R.axes 1 ∈ S := ⟨R.transverseFrame,R.transverseFrame_axis⟩
  obtain ⟨w,hwC,hw⟩ := mem_iUnion₂.mp (hcover hr)
  let j : C := ⟨w,hwC⟩
  refine ⟨e j,?_⟩
  simpa only [Equiv.symm_apply_apply,hD,mem_ball,dist_comm] using hw

theorem transverse_coordinate_large (S : Rectangle) (w : Plane) (hw : ‖w‖ = 1)
    (hsmall : |S.axes.repr w 0| ≤ 1/2) : 1/2 ≤ |S.axes.repr w 1| := by
  have he := S.axes.sum_sq_inner_right w
  simp only [Fin.sum_univ_two,←S.axes.repr_apply_apply,hw,one_pow] at he
  have h0 : (S.axes.repr w 0)^2 ≤ (1/2:ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (S.axes.repr w 0)) (by norm_num : (0:ℝ) ≤ 1/2)).mpr hsmall
  by_contra hn
  have h1 : (S.axes.repr w 1)^2 < (1/2:ℝ)^2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg (S.axes.repr w 1)) (by norm_num : (0:ℝ) ≤ 1/2)).mpr (lt_of_not_ge hn)
  nlinarith

theorem nearby_transverse_coordinate (R S D : Rectangle)
    (hangle : dist (S.axes 0) (R.axes 0) ≤ 1/4)
    (hdir : dist (D.axes 0) (R.axes 1) ≤ 1/4) :
    1/2 ≤ |S.axes.repr (D.axes 0) 1| := by
  apply S.transverse_coordinate_large (D.axes 0) (D.axes.norm_eq_one 0)
  have hD : |R.axes.repr (D.axes 0) 0| ≤ dist (D.axes 0) (R.axes 1) := by
    have hz : R.axes.repr (R.axes 1) 0 = 0 := by simp
    have h := R.abs_coordinate_le_norm (D.axes 0-R.axes 1) 0
    rw [map_sub,PiLp.sub_apply,hz,sub_zero] at h
    simpa only [dist_eq_norm] using h
  have hi : |inner ℝ (S.axes 0) (D.axes 0)-inner ℝ (R.axes 0) (D.axes 0)| ≤ dist (S.axes 0) (R.axes 0) := by
    rw [←inner_sub_left]
    simpa only [D.axes.norm_eq_one,mul_one,dist_eq_norm] using abs_real_inner_le_norm (S.axes 0-R.axes 0) (D.axes 0)
  have htri := abs_add_le
    (inner ℝ (S.axes 0) (D.axes 0)-inner ℝ (R.axes 0) (D.axes 0))
    (inner ℝ (R.axes 0) (D.axes 0))
  simp only [sub_add_cancel] at htri
  rw [S.axes.repr_apply_apply]
  rw [R.axes.repr_apply_apply] at hD
  linarith

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleProjection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact coordinate projections and exact change of orthogonal
coordinates for the popularity packing in Lacey--Li (3.11). -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert.Rectangle

theorem isClosed_carrier (R : Rectangle) : IsClosed R.carrier := by
  change IsClosed ({x : Plane | |R.axes.repr (x-R.center) 0| ≤ R.long/2} ∩
    {x : Plane | |R.axes.repr (x-R.center) 1| ≤ R.short/2})
  exact (isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop) continuous_const)

theorem isCompact_carrier (R : Rectangle) : IsCompact R.carrier := by
  apply Metric.isCompact_of_isClosed_isBounded R.isClosed_carrier
  apply (Metric.isBounded_closedBall (x := R.center) (r := R.long)).subset
  intro x hx
  simpa only [Metric.mem_closedBall,dist_eq_norm] using R.norm_sub_center_le_long hx

theorem isCompact_popularSet (R : Rectangle) {v : Plane → Plane} (hv : Continuous v) :
    IsCompact (R.popularSet v) := by
  change IsCompact (R.carrier ∩ {x | Real.cos (R.short/(2*R.long)) ≤ inner ℝ (v x) (R.axes 0)})
  exact R.isCompact_carrier.inter_right (isClosed_le continuous_const (hv.inner continuous_const))

theorem continuous_orthogonalCoordinates (R : Rectangle) : Continuous R.orthogonalCoordinates := by
  change Continuous (fun x : Plane => (R.axes.repr (x-R.center) 0,R.axes.repr (x-R.center) 1))
  fun_prop

theorem isCompact_coordinateProjection (S : Rectangle) {E : Set Plane} (hE : IsCompact E) :
    IsCompact (S.coordinateProjection E) :=
  hE.image (continuous_fst.comp S.continuous_orthogonalCoordinates)

theorem change_transverse_coordinates (R S : Rectangle) (x : Plane) :
    R.axes.repr (x-R.center) 1 =
      R.axes.repr (S.axes 0) 1 * (S.orthogonalCoordinates x).1 +
      R.axes.repr (S.axes 1) 1 * (S.orthogonalCoordinates x).2 +
      R.axes.repr (S.center-R.center) 1 := by
  have he : x-R.center = (x-S.center)+(S.center-R.center) := by abel
  rw [he,map_add,PiLp.add_apply]
  nth_rw 1 [←S.axes.sum_repr (x-S.center)]
  rw [Fin.sum_univ_two,map_add,PiLp.add_apply,map_smul,map_smul]
  change (S.axes.repr (x-S.center) 0)*R.axes.repr (S.axes 0) 1 +
    (S.axes.repr (x-S.center) 1)*R.axes.repr (S.axes 1) 1 + R.axes.repr (S.center-R.center) 1 = _
  rw [orthogonalCoordinates_apply]
  ring

theorem coordinate_projection_area (R S : Rectangle) {E : Set Plane} (hE : IsCompact E)
    (hsub : E ⊆ R.carrier) (hangle : dist (R.axes 0) (S.axes 0) ≤ 1/4) :
    volume E ≤ ENNReal.ofReal (2*R.short)*volume (S.coordinateProjection E) := by
  let E' := S.orthogonalCoordinates '' E
  have hE' : IsCompact E' := hE.image S.continuous_orthogonalCoordinates
  have hP := S.isCompact_coordinateProjection hE
  have hb : 1/2 ≤ |R.axes.repr (S.axes 1) 1| := by
    have h := nearby_transverse_coordinate S R S.transverseFrame hangle
      (show dist (S.transverseFrame.axes 0) (S.axes 1) ≤ 1/4 by rw [transverseFrame_axis]; norm_num)
    simpa only [transverseFrame_axis] using h
  have h := LipschitzHilbert.strip_projection_area_half E' hE'.measurableSet
    (S.coordinateProjection E) hP.measurableSet
    (R.axes.repr (S.axes 0) 1) (R.axes.repr (S.axes 1) 1)
    (-R.axes.repr (S.center-R.center) 1) (R.short/2) hb (half_pos R.short_pos).le
    (fun z hz => by obtain ⟨x,hx,rfl⟩ := hz; exact ⟨x,hx,rfl⟩)
    (fun z hz => by
      obtain ⟨x,hx,rfl⟩ := hz
      have hh := (hsub hx).2
      rw [change_transverse_coordinates R S x] at hh
      simpa only [sub_neg_eq_add] using hh)
  have he : (volume.prod volume) E' = volume E := by
    have he := S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv E'
    rw [Set.preimage_image_eq E S.orthogonalCoordinates.injective] at he
    exact he.symm
  rw [he] at h
  have hc : 4*(R.short/2) = 2*R.short := by ring
  rw [hc] at h
  exact h

theorem popular_projection_density (R S : Rectangle) {v : Plane → Plane} {K δ : ℝ≥0}
    (hv : Continuous v) (hR : R.Admissible v K δ)
    (hangle : dist (R.axes 0) (S.axes 0) ≤ 1/4) :
    (δ : ℝ≥0∞)*ENNReal.ofReal R.long ≤ 2*volume (S.coordinateProjection (R.popularSet v)) := by
  have hp := coordinate_projection_area R S (R.isCompact_popularSet hv)
    (fun _ hx => hx.1) hangle
  have hm := hR.2.trans hp
  rw [volume_carrier] at hm
  have hh : ENNReal.ofReal R.short * ((δ : ℝ≥0∞)*ENNReal.ofReal R.long) ≤
      ENNReal.ofReal R.short * (2*volume (S.coordinateProjection (R.popularSet v))) := by
    calc
      _ = (δ : ℝ≥0∞)*(ENNReal.ofReal R.long*ENNReal.ofReal R.short) := by ring
      _ ≤ ENNReal.ofReal (2*R.short)*volume (S.coordinateProjection (R.popularSet v)) := hm
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num; ring
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr R.short_pos))
    ENNReal.ofReal_ne_top).mp hh

theorem projection_in_long_interval (R S : Rectangle) (hL : R.long ≤ S.long)
    (hint : (R.carrier ∩ S.carrier).Nonempty) {E : Set Plane} (hE : E ⊆ R.carrier) :
    S.coordinateProjection E ⊆ Icc (-3*S.long) (3*S.long) := by
  obtain ⟨y,hyR,hyS⟩ := hint
  rintro u ⟨x,hx,rfl⟩
  have hn : ‖x-S.center‖ ≤ 3*S.long := by
    have hdist := R.dist_le_two_long (hE hx) hyR
    rw [dist_eq_norm] at hdist
    have htri : ‖x-S.center‖ ≤ ‖x-y‖+‖y-S.center‖ := by
      simpa only [dist_eq_norm] using dist_triangle x y S.center
    linarith [S.norm_sub_center_le_long hyS]
  have hc := (S.abs_coordinate_le_norm (x-S.center) 0).trans hn
  simpa only [orthogonalCoordinates_apply,mem_Icc,neg_mul] using abs_le.mp hc

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_DilatedRectangleInterior
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative interior neighborhood of a dilated rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid

theorem centeredSquare_norm_bound (x : Plane) (r : ℝ) {z : ℝ × ℝ}
    (hz : z ∈ centeredSquare (planeCoordinates.symm x) r) : ‖planeCoordinates z-x‖ ≤ 2*r := by
  have h0 : |z.1-(planeCoordinates.symm x).1| ≤ r := by
    apply abs_le.mpr
    constructor <;> linarith [hz.1.1,hz.1.2]
  have h1 : |z.2-(planeCoordinates.symm x).2| ≤ r := by
    apply abs_le.mpr
    constructor <;> linarith [hz.2.1,hz.2.2]
  have hh := plane_norm_le_coordinate_sum (planeCoordinates z-x)
  change ‖planeCoordinates z-x‖ ≤ |z.1-(planeCoordinates.symm x).1|+|z.2-(planeCoordinates.symm x).2| at hh
  linarith

namespace Rectangle

theorem dilate_interior_ball (R : Rectangle) (a : ℝ) (ha : 0 < a) {x y : Plane}
    (hx : x ∈ (R.dilate (a/2) (half_pos ha)).carrier)
    (hy : ‖y-x‖ ≤ a*R.short/4) : y ∈ (R.dilate a ha).carrier := by
  have hdiff (i : Fin 2) : |R.axes.repr (y-R.center) i-R.axes.repr (x-R.center) i| ≤ a*R.short/4 := by
    rw [R.coordinate_difference]
    exact (R.abs_coordinate_le_norm (y-x) i).trans hy
  have hab (i : Fin 2) : |R.axes.repr (y-R.center) i| ≤
      |R.axes.repr (y-R.center) i-R.axes.repr (x-R.center) i|+|R.axes.repr (x-R.center) i| := by
    simpa only [sub_add_cancel] using abs_add_le
      (R.axes.repr (y-R.center) i-R.axes.repr (x-R.center) i) (R.axes.repr (x-R.center) i)
  change |R.axes.repr (y-R.center) 0| ≤ a*R.long/2 ∧ |R.axes.repr (y-R.center) 1| ≤ a*R.short/2
  change |R.axes.repr (x-R.center) 0| ≤ (a/2)*R.long/2 ∧
    |R.axes.repr (x-R.center) 1| ≤ (a/2)*R.short/2 at hx
  constructor
  · have hwidth := mul_le_mul_of_nonneg_left R.short_le_long ha.le
    linarith [hdiff 0,hab 0]
  · linarith [hdiff 1,hab 1]

theorem dilate_interior_square (R : Rectangle) (a : ℝ) (ha : 0 < a) {x : Plane}
    (hx : x ∈ (R.dilate (a/2) (half_pos ha)).carrier) :
    centeredSquare (planeCoordinates.symm x) (a*R.short/8) ⊆ planeCoordinates ⁻¹' (R.dilate a ha).carrier := by
  intro z hz
  apply R.dilate_interior_ball a ha hx
  have h := centeredSquare_norm_bound x (a*R.short/8) hz
  linarith

end Rectangle
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MaximalContainmentExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The maximal selection rule excludes a later rectangle contained in
the interior half of an earlier dilation. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid
variable {ι κ : Type*} [Fintype κ]

theorem interior_indicator_auxiliary_lower (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (S : Rectangle) (a : ℝ) (ha : 0 < a) {x : Plane}
    (hx : x ∈ (S.dilate (a/2) (half_pos ha)).carrier) :
    1 ≤ 36 * positiveAuxiliary e ((S.dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞))) x := by
  let r := a*S.short/8
  have hr : 0 < r := div_pos (mul_pos ha S.short_pos) (by norm_num)
  let Q := centeredSquare (planeCoordinates.symm x) r
  let f := (S.dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞))
  have hsub : Q ⊆ planeCoordinates ⁻¹' (S.dilate a ha).carrier := S.dilate_interior_square a ha hx
  have hQ : MeasurableSet Q := centeredSquare_measurable _ _
  have hint : (∫⁻ z in Q, f (planeCoordinates z) ∂volume.prod volume) = (volume.prod volume) Q := by
    calc
      _ = ∫⁻ _z in Q, (1:ℝ≥0∞) ∂volume.prod volume :=
        setLIntegral_congr_fun hQ (fun z hz => by
          have hz' : planeCoordinates z ∈ (S.dilate a ha).carrier := hsub hz
          exact indicator_of_mem hz' _)
      _ = _ := by simp
  have hc : planeCoordinates.symm x ∈ Q := by
    change (_ ∈ Icc _ _) ∧ (_ ∈ Icc _ _)
    constructor <;> constructor <;> linarith
  have haux := positiveAuxiliary_square_integral e f (planeCoordinates.symm x) r hr x hc
  rw [hint] at haux
  have hpos : (volume.prod volume) Q ≠ 0 := by
    rw [centeredSquare_volume]
    exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  have htop : (volume.prod volume) Q ≠ ∞ := by
    rw [centeredSquare_volume]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hpos htop).mp
  simpa only [mul_one,mul_assoc,mul_left_comm] using haux

theorem contained_in_earlier_dilation_blocked (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (R : ι → Rectangle) (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (hη : 36*η < 1)
    (previous : Finset ι) (s r : ι) (hs : s ∈ previous)
    (hsub : (R r).carrier ⊆ ((R s).dilate (a/2) (half_pos ha)).carrier) :
    maximalBlocked e R a ha η previous r := by
  let f := ((R s).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞))
  have hf : f ≤ rectangleCount (fun j => (R j).dilate a ha) previous := by
    intro x
    exact Finset.single_le_sum
      (f := fun j => ((R j).dilate a ha).carrier.indicator (fun _ => (1:ℝ≥0∞)) x)
      (fun _ _ => zero_le) hs
  intro x hx
  have h := (interior_indicator_auxiliary_lower e (R s) a ha (hsub hx)).trans
    (mul_le_mul' le_rfl (positiveAuxiliary_mono e hf x))
  change η < positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a ha) previous) x
  apply lt_of_not_ge
  intro hn
  exact (not_le_of_gt hη) (h.trans (mul_le_mul' le_rfl hn))

theorem unblocked_not_contained_in_earlier_dilation (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (R : ι → Rectangle) (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (hη : 36*η < 1)
    (previous : Finset ι) (s r : ι) (hs : s ∈ previous)
    (hnot : ¬maximalBlocked e R a ha η previous r) :
    ¬(R r).carrier ⊆ ((R s).dilate (a/2) (half_pos ha)).carrier := by
  intro hsub
  exact hnot (contained_in_earlier_dilation_blocked e R a ha η hη previous s r hs hsub)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_UniformNearSelection
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A universal near-angle selected overlap bound, with all directional
and aspect-ratio choices discharged. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

private theorem selectionThreshold_mul_le (c : ℝ) (hc : 0 ≤ c) (hcle : c ≤ 1048576) :
    ENNReal.ofReal c * selectionThreshold ≤ 1 := by
  change ENNReal.ofReal c * ENNReal.ofReal (1/1048576 : ℝ) ≤ 1
  rw [←ENNReal.ofReal_one,←ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  have h : c/(1048576:ℝ) ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by simpa using hcle)
  simpa only [div_eq_mul_inv,one_div,one_mul] using h

theorem uniform_near_selected_overlap {ι : Type*} {n : ℕ} (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (s previous : Finset ι) (hs : s ⊆ previous) (r : ι)
    (hL : ∀ j ∈ s, (R r).long ≤ (R j).long)
    (hnear : ∀ j ∈ s, (R r).long * dist ((R j).axes 0) ((R r).axes 0) ≤ 64*(R r).short)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ s, volume ((R r).carrier ∩ (R j).carrier)) ≤ volume (R r).carrier := by
  by_cases hfat : (R r).long ≤ 256*(R r).short
  · exact fat_selected_overlap_bound (fun i => (D i).orthogonalCoordinates) R s previous hs r
      256 (by norm_num) hfat selectionDilation (by norm_num) selectionThreshold (selectionThreshold_mul_le _ (by norm_num) (by norm_num)) hnot
  · obtain ⟨i,hi⟩ := hD (R r)
    have htrans (j : ι) (hj : j ∈ s) : 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1| := by
      apply Rectangle.nearby_transverse_coordinate (R r) (R j) (D i) _ hi.le
      have hh := hnear j hj
      have hp := (R r).long_pos
      have hn : 256*(R r).short < (R r).long := lt_of_not_ge hfat
      nlinarith
    have hsmall : ENNReal.ofReal (96*((64:ℝ)+1))*selectionThreshold ≤ 1 := by
      exact selectionThreshold_mul_le _ (by norm_num) (by norm_num)
    have haeq : 4*((64:ℝ)+1)+5 = selectionDilation := by norm_num [selectionDilation]
    have hn : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        (4*((64:ℝ)+1)+5) (by norm_num) selectionThreshold previous r := by
      simpa only [haeq] using hnot
    exact near_selected_overlap_bound D R s previous r i 64 (by norm_num) hs
      selectionThreshold hsmall hL hnear htrans hn

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FarSelectionGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric consequences of actual maximal non-removal for far pairs.
In particular, both widths are small relative to the angle and all
remaining angles satisfy the bound needed for popularity projection. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

namespace Rectangle

theorem dilate_carrier_mono (R : Rectangle) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    (R.dilate a ha).carrier ⊆ (R.dilate b hb).carrier := by
  intro x hx
  change |R.axes.repr (x-R.center) 0| ≤ a*R.long/2 ∧ |R.axes.repr (x-R.center) 1| ≤ a*R.short/2 at hx
  constructor
  · change |R.axes.repr (x-R.center) 0| ≤ b*R.long/2
    have hl := mul_le_mul_of_nonneg_right hab R.long_pos.le
    exact hx.1.trans (by linarith)
  · change |R.axes.repr (x-R.center) 1| ≤ b*R.short/2
    have hl := mul_le_mul_of_nonneg_right hab R.short_pos.le
    exact hx.2.trans (by linarith)

end Rectangle

theorem selectionThreshold_small : 36*selectionThreshold < 1 := by
  change (36:ℝ≥0∞)*ENNReal.ofReal (1/1048576:ℝ) < 1
  rw [show (36:ℝ≥0∞)=ENNReal.ofReal 36 by norm_num,←ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_lt_one]
  norm_num

theorem far_selected_earlier_width {ι κ : Type*} [Fintype κ]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle) (previous : Finset ι)
    (s r : ι) (hs : s ∈ previous) (hL : (R r).long ≤ (R s).long)
    (hinter : ((R s).carrier ∩ (R r).carrier).Nonempty)
    (hfar : 64*(R r).short < (R r).long * dist ((R s).axes 0) ((R r).axes 0))
    (hnot : ¬maximalBlocked e R selectionDilation (by norm_num) selectionThreshold previous r) :
    32*(R s).short < dist ((R s).axes 0) ((R r).axes 0)*(R s).long := by
  by_contra hn
  have hwidth : dist ((R s).axes 0) ((R r).axes 0)*(R s).long ≤ 32*(R s).short := le_of_not_gt hn
  have hangle : (R r).long * dist ((R s).axes 0) ((R r).axes 0) ≤ 32*(R s).short := by
    have h := mul_le_mul_of_nonneg_left hL (dist_nonneg (x := (R s).axes 0) (y := (R r).axes 0))
    nlinarith
  have hshort : (R r).short ≤ (R s).short := by linarith [(R r).short_pos]
  have hc := Rectangle.controlled_angle_containment (R s) (R r) 32 (by norm_num) hL hshort hangle hinter
  have hsub : (R r).carrier ⊆ ((R s).dilate (selectionDilation/2) (by norm_num)).carrier :=
    hc.trans ((R s).dilate_carrier_mono (2*32+5) (selectionDilation/2) (by norm_num) (by norm_num) (by norm_num))
  exact (unblocked_not_contained_in_earlier_dilation e R selectionDilation (by norm_num)
    selectionThreshold selectionThreshold_small previous s r hs hnot) hsub

theorem far_selected_angle_bound (S T : Rectangle) {v : Plane → Plane} {K δ : ℝ≥0}
    (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1) (hδ : 0 < δ)
    (hS : S.Admissible v K δ) (hT : T.Admissible v K δ)
    (hL : T.long ≤ S.long) (hinter : (S.carrier ∩ T.carrier).Nonempty)
    (hfar : 64*T.short < T.long*dist (S.axes 0) (T.axes 0))
    (hwidth : 32*S.short < dist (S.axes 0) (T.axes 0)*S.long) :
    dist (S.axes 0) (T.axes 0) ≤ 5*(K:ℝ)*S.long ∧ dist (S.axes 0) (T.axes 0) ≤ 1/20 := by
  let θ := dist (S.axes 0) (T.axes 0)
  have hST : S.short/(2*S.long) ≤ θ/64 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) S.long_pos)).mpr
    dsimp [θ]
    nlinarith
  have hTT : T.short/(2*T.long) ≤ θ/128 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) T.long_pos)).mpr
    dsimp [θ]
    nlinarith
  have hraw := S.intersecting_axes_distance T hv hu hδ hS hT hinter
  have hK := mul_le_mul_of_nonneg_left hL K.coe_nonneg
  have hKnonneg : 0 ≤ (K:ℝ)*S.long := mul_nonneg K.coe_nonneg S.long_pos.le
  have hbound : θ ≤ 5*(K:ℝ)*S.long := by
    dsimp [θ] at hST hTT ⊢
    nlinarith
  refine ⟨hbound,?_⟩
  have hscale := hS.1
  change 100*(K:ℝ)*S.long ≤ 1 at hscale
  nlinarith

/-- Non-removal controls the reference width by the *later* length as
well. This is the local scale bound used in the strip estimates. -/
theorem far_selected_reference_width {ι κ : Type*} [Fintype κ]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle) (previous : Finset ι)
    (s r : ι) (hs : s ∈ previous) (hL : (R r).long ≤ (R s).long)
    (hinter : ((R s).carrier ∩ (R r).carrier).Nonempty)
    (hfar : 64*(R r).short < (R r).long * dist ((R s).axes 0) ((R r).axes 0))
    (hnot : ¬maximalBlocked e R selectionDilation (by norm_num) selectionThreshold previous r) :
    32*(R s).short < (R r).long*dist ((R s).axes 0) ((R r).axes 0) := by
  by_contra hn
  have hangle : (R r).long*dist ((R s).axes 0) ((R r).axes 0) ≤ 32*(R s).short :=
    le_of_not_gt hn
  have hshort : (R r).short ≤ (R s).short := by linarith [(R r).short_pos]
  have hc := Rectangle.controlled_angle_containment (R s) (R r) 32 (by norm_num)
    hL hshort hangle hinter
  have hsub : (R r).carrier ⊆ ((R s).dilate (selectionDilation/2) (by norm_num)).carrier :=
    hc.trans ((R s).dilate_carrier_mono (2*32+5) (selectionDilation/2)
      (by norm_num) (by norm_num) (by norm_num))
  exact (unblocked_not_contained_in_earlier_dilation e R selectionDilation (by norm_num)
    selectionThreshold selectionThreshold_small previous s r hs hnot) hsub

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LocalSelectedWidths
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Width bounds at the local interval scale, derived from actual
non-removal rather than imposed as extra geometric assumptions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem local_selected_widths {ι κ : Type*} [Fintype κ]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle) (previous : Finset ι)
    (s r : ι) (hs : s ∈ previous) (hL : (R r).long ≤ (R s).long)
    (hinter : ((R s).carrier ∩ (R r).carrier).Nonempty)
    (hfar : 64*(R r).short < (R r).long*dist ((R s).axes 0) ((R r).axes 0))
    (hnot : ¬maximalBlocked e R selectionDilation (by norm_num) selectionThreshold previous r)
    (l θ : ℝ) (hl : 0 ≤ l) (hsize : (R r).long ≤ 16*l)
    (hangle : dist ((R s).axes 0) ((R r).axes 0) ≤ 2*θ) :
    (R s).short ≤ θ*l ∧ (R r).short ≤ θ*l := by
  have href := far_selected_reference_width e R previous s r hs hL hinter hfar hnot
  have hprod := mul_le_mul hsize hangle dist_nonneg (by linarith : 0 ≤ 16*l)
  constructor <;> nlinarith [(R s).short_pos,(R r).short_pos]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ProjectionFiberGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual distances between points with the same projected coordinate,
used to compare directions within one projected-popularity group. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.Rectangle

theorem dist_of_same_long_coordinate (S : Rectangle) (x y : Plane)
    (hxy : (S.orthogonalCoordinates x).1 = (S.orthogonalCoordinates y).1) :
    dist x y = |(S.orthogonalCoordinates y).2-(S.orthogonalCoordinates x).2| := by
  have h0 : S.axes.repr (y-x) 0 = 0 := by
    rw [←S.coordinate_difference x y 0]
    change (S.orthogonalCoordinates y).1-(S.orthogonalCoordinates x).1=0
    rw [hxy,sub_self]
  have he : y-x = S.axes.repr (y-x) 1 • S.axes 1 := by
    have h := S.axes.sum_repr (y-x)
    rw [Fin.sum_univ_two,h0,zero_smul,zero_add] at h
    exact h.symm
  rw [dist_eq_norm,norm_sub_rev,he,norm_smul,S.axes.norm_eq_one,mul_one,Real.norm_eq_abs,
    ←S.coordinate_difference x y 1]
  rfl

theorem transverse_position_bound (S R : Rectangle) (x : Plane) (hx : x ∈ R.carrier)
    (hint : (R.carrier ∩ S.carrier).Nonempty) :
    |(S.orthogonalCoordinates x).2| ≤ S.short/2+R.long*dist (S.axes 0) (R.axes 0)+R.short := by
  obtain ⟨y,hyR,hyS⟩ := hint
  have hd := S.transverse_difference_le R hx hyR
  rw [←S.coordinate_difference y x 1] at hd
  have ht := abs_add_le
    (S.axes.repr (x-S.center) 1-S.axes.repr (y-S.center) 1) (S.axes.repr (y-S.center) 1)
  simp only [sub_add_cancel] at ht
  change |S.axes.repr (x-S.center) 1| ≤ _
  linarith [hyS.2]

theorem shared_projection_distance (S R T : Rectangle) (x y : Plane)
    (hx : x ∈ R.carrier) (hy : y ∈ T.carrier)
    (hR : (R.carrier ∩ S.carrier).Nonempty) (hT : (T.carrier ∩ S.carrier).Nonempty)
    (hxy : (S.orthogonalCoordinates x).1 = (S.orthogonalCoordinates y).1) :
    dist x y ≤ S.short+R.long*dist (S.axes 0) (R.axes 0)+R.short+
      T.long*dist (S.axes 0) (T.axes 0)+T.short := by
  rw [S.dist_of_same_long_coordinate x y hxy]
  have h := abs_sub (S.orthogonalCoordinates y).2 (S.orthogonalCoordinates x).2
  have hx' := S.transverse_position_bound R x hx hR
  have hy' := S.transverse_position_bound T y hy hT
  linarith

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_PopularGroupDirections
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Directions in one overlapping projected-popularity group are close.
This uses actual popularity points with the same long coordinate. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace LipschitzHilbert.Rectangle

theorem popular_group_directions (S R T : Rectangle) {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hscale : 100*(K:ℝ)*S.long ≤ 1) (hRS : R.long ≤ S.long) (hTR : T.long ≤ R.long)
    (hR : (R.carrier ∩ S.carrier).Nonempty) (hT : (T.carrier ∩ S.carrier).Nonempty)
    (hRw : 64*R.short ≤ R.long*dist (S.axes 0) (R.axes 0))
    (hTw : 64*T.short ≤ T.long*dist (S.axes 0) (T.axes 0))
    (hSw : 32*S.short ≤ S.long*dist (S.axes 0) (R.axes 0))
    {x y : Plane} (hx : x ∈ R.popularSet v) (hy : y ∈ T.popularSet v)
    (hxy : (S.orthogonalCoordinates x).1 = (S.orthogonalCoordinates y).1) :
    dist (R.axes 0) (T.axes 0) ≤ dist (S.axes 0) (R.axes 0)/2 := by
  let θ := dist (S.axes 0) (R.axes 0)
  let φ := dist (S.axes 0) (T.axes 0)
  let d := dist (R.axes 0) (T.axes 0)
  have hθ : 0 ≤ θ := dist_nonneg
  have hφ : 0 ≤ φ := dist_nonneg
  have hφd : φ ≤ θ+d := dist_triangle _ _ _
  have hRsmall : R.short ≤ R.long*θ := by dsimp [θ]; nlinarith [R.short_pos]
  have hTsmall : T.short ≤ T.long*φ := by dsimp [φ]; nlinarith [T.short_pos]
  have hφlen : T.long*φ ≤ R.long*φ := mul_le_mul_of_nonneg_right hTR hφ
  have hdist0 := S.shared_projection_distance R T x y hx.1 hy.1 hR hT hxy
  have hdist : dist x y ≤ S.short+2*R.long*(θ+φ) := by
    change dist x y ≤ S.short+R.long*θ+R.short+T.long*φ+T.short at hdist0
    nlinarith
  have hKl : (K:ℝ)*R.long ≤ 1/100 := by
    have h := mul_le_mul_of_nonneg_left hRS K.coe_nonneg
    nlinarith
  have hKθ : (K:ℝ)*S.long*θ ≤ θ/100 := by
    have h := mul_le_mul_of_nonneg_right hscale hθ
    nlinarith
  have hKS : (K:ℝ)*S.short ≤ θ/3200 := by
    have h := mul_le_mul_of_nonneg_left hSw K.coe_nonneg
    change (K:ℝ)*(32*S.short) ≤ (K:ℝ)*(S.long*θ) at h
    nlinarith
  have hKsum : (K:ℝ)*R.long*(θ+φ) ≤ (θ+φ)/100 := by
    have h := mul_le_mul_of_nonneg_right hKl (add_nonneg hθ hφ)
    nlinarith
  have hKdist : (K:ℝ)*dist x y ≤ θ/3200+(θ+φ)/50 := by
    have h := mul_le_mul_of_nonneg_left hdist K.coe_nonneg
    nlinarith
  have hRap : R.short/(2*R.long) ≤ θ/128 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) R.long_pos)).mpr
    change 64*R.short ≤ R.long*θ at hRw
    nlinarith
  have hTap : T.short/(2*T.long) ≤ φ/128 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) T.long_pos)).mpr
    change 64*T.short ≤ T.long*φ at hTw
    nlinarith
  have hvxy := hv.dist_le_mul x y
  have hxv := R.popular_axis_distance hu hx
  have hyv := T.popular_axis_distance hu hy
  have ht1 := dist_triangle (R.axes 0) (v x) (T.axes 0)
  have ht2 := dist_triangle (v x) (v y) (T.axes 0)
  rw [dist_comm (R.axes 0) (v x)] at ht1
  change d ≤ _ at ht1
  change dist (v x) (R.axes 0) ≤ R.short/(2*R.long) at hxv
  nlinarith

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_ProjectedPopularityPacking
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual projected-popularity packing estimate for the far-angle
rectangle groups, in the finite form needed by the application. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert
variable {ι : Type*}

theorem projected_popularity_packing (R : ι → Rectangle) (s : Finset ι) (S : Rectangle)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : Continuous v)
    (hR : ∀ i ∈ s, (R i).Admissible v K δ)
    (hL : ∀ i ∈ s, (R i).long ≤ S.long)
    (hinter : ∀ i ∈ s, ((R i).carrier ∩ S.carrier).Nonempty)
    (hangle : ∀ i ∈ s, dist ((R i).axes 0) (S.axes 0) ≤ 1/4)
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => S.coordinateProjection ((R i).popularSet v))) :
    (δ : ℝ≥0∞) * (∑ i ∈ s, ENNReal.ofReal (R i).long) ≤ 12*ENNReal.ofReal S.long := by
  let P := fun i => S.coordinateProjection ((R i).popularSet v)
  have hPm (i : ι) : MeasurableSet (P i) :=
    (S.isCompact_coordinateProjection ((R i).isCompact_popularSet hv)).measurableSet
  have hsub : (⋃ i ∈ s, P i) ⊆ Icc (-3*S.long) (3*S.long) := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
    exact (Rectangle.projection_in_long_interval (R i) S (hL i hi) (hinter i hi)
      (fun _ hx => hx.1)) hxi
  calc
    _ = ∑ i ∈ s, (δ : ℝ≥0∞)*ENNReal.ofReal (R i).long := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ s, 2*volume (P i) :=
      Finset.sum_le_sum (fun i hi => Rectangle.popular_projection_density (R i) S hv (hR i hi) (hangle i hi))
    _ = 2*volume (⋃ i ∈ s, P i) := by
      rw [measure_biUnion_finset hdisj (fun i _ => hPm i),Finset.mul_sum]
    _ ≤ 2*volume (Icc (-3*S.long) (3*S.long)) := mul_le_mul' le_rfl (measure_mono hsub)
    _ = _ := by
      rw [Real.volume_Icc,show 3*S.long- -3*S.long = 6*S.long by ring,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_ProjectionGroupSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite maximal-length grouping of overlapping projected
popularity sets used in the far-angle estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem projectionBlocked_mono (P : ι → Set ℝ) {s t : Finset ι} (hst : s ⊆ t)
    (j : ι) (h : projectionBlocked P s j) : projectionBlocked P t j := by
  obtain ⟨i,hi,hij⟩ := h
  exact ⟨i,hst hi,hij⟩

theorem projection_group_run_exists (R : ι → Rectangle) (P : ι → Set ℝ) (s : Finset ι) :
    ∃ centers, RectangleCoverRun R (projectionBlocked P) ∅ s centers := by
  apply rectangle_cover_run_exists
  intro i _
  simp [projectionBlocked]

namespace RectangleCoverRun
variable {R : ι → Rectangle} {P : ι → Set ℝ} {previous stock : Finset ι} {centers : List ι}

theorem selected_unblocked_before (h : RectangleCoverRun R (projectionBlocked P) previous stock centers) :
    ∀ j ∈ centers, ¬projectionBlocked P previous j := by
  induction h with
  | stop => simp
  | step previous stock i tail hi hp ha htail ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ha
    · intro hb
      exact ih j hj (projectionBlocked_mono P (Finset.subset_insert _ _) j hb)

theorem projected_centers_disjoint (h : RectangleCoverRun R (projectionBlocked P) previous stock centers) :
    centers.Pairwise (fun i j => Disjoint (P i) (P j)) := by
  induction h with
  | stop => exact List.Pairwise.nil
  | step previous stock i tail hi hp ha htail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro j hj
    apply Set.disjoint_iff_inter_eq_empty.mpr
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    exact htail.selected_unblocked_before j hj ⟨i,Finset.mem_insert_self _ _,hn⟩

theorem projected_center_cover (h : RectangleCoverRun R (projectionBlocked P) previous stock centers)
    (hallowed : ∀ j ∈ stock, ¬projectionBlocked P previous j)
    (hnonempty : ∀ j ∈ stock, (P j).Nonempty) :
    ∀ j ∈ stock, ∃ i ∈ centers, (R j).long ≤ (R i).long ∧ (P i ∩ P j).Nonempty := by
  classical
  induction h with
  | stop => simp
  | step previous stock i tail hi hp ha htail ih =>
    intro j hj
    by_cases hji : j = i
    · subst j
      exact ⟨i,List.mem_cons_self,(hp i hi).1,by simpa only [inter_self] using hnonempty i hi⟩
    by_cases hjr : j ∈ rectangleRemaining (projectionBlocked P) previous stock i
    · obtain ⟨k,hkt,hlen,hint⟩ := ih
        (fun k hk => ((mem_rectangleRemaining (projectionBlocked P) previous stock i k).mp hk).2.2)
        (fun k hk => hnonempty k (rectangleRemaining_subset _ _ _ _ hk)) j hjr
      exact ⟨k,List.mem_cons_of_mem i hkt,hlen,hint⟩
    · have hb : projectionBlocked P (insert i previous) j := by
        by_contra hn
        exact hjr ((mem_rectangleRemaining (projectionBlocked P) previous stock i j).mpr ⟨hj,hji,hn⟩)
      obtain ⟨k,hk,hint⟩ := hb
      rcases Finset.mem_insert.mp hk with hki | hk
      · subst k
        exact ⟨i,List.mem_cons_self,(hp j hj).1,hint⟩
      · exact (hallowed j hj ⟨k,hk,hint⟩).elim

end RectangleCoverRun
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PopularGroups
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite groups from intersecting popularity projections.  Their
representatives have the packing bound, and every group lies in a long
interval of the size of its representative. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

namespace Rectangle

theorem projected_popularity_directions (S R T : Rectangle) {v : Plane → Plane} {K : ℝ≥0}
    (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hscale : 100*(K:ℝ)*S.long ≤ 1) (hRS : R.long ≤ S.long) (hTR : T.long ≤ R.long)
    (hR : (R.carrier ∩ S.carrier).Nonempty) (hT : (T.carrier ∩ S.carrier).Nonempty)
    (hRw : 64*R.short ≤ R.long*dist (S.axes 0) (R.axes 0))
    (hTw : 64*T.short ≤ T.long*dist (S.axes 0) (T.axes 0))
    (hSw : 32*S.short ≤ S.long*dist (S.axes 0) (R.axes 0))
    (hproj : (S.coordinateProjection (R.popularSet v) ∩
      S.coordinateProjection (T.popularSet v)).Nonempty) :
    dist (R.axes 0) (T.axes 0) ≤ dist (S.axes 0) (R.axes 0)/2 := by
  obtain ⟨t,htR,htT⟩ := hproj
  obtain ⟨x,hx,hxt⟩ := htR
  obtain ⟨y,hy,hyt⟩ := htT
  exact popular_group_directions S R T hv hu hscale hRS hTR hR hT hRw hTw hSw
    hx hy (hxt.trans hyt.symm)

theorem projected_group_localization (S R T : Rectangle) {v : Plane → Plane}
    (hTR : T.long ≤ R.long)
    (hproj : (S.coordinateProjection (R.popularSet v) ∩
      S.coordinateProjection (T.popularSet v)).Nonempty) {y : Plane} (hy : y ∈ T.carrier) :
    |(S.orthogonalCoordinates y).1 - (S.orthogonalCoordinates R.center).1| ≤ 3*R.long := by
  obtain ⟨t,htR,htT⟩ := hproj
  obtain ⟨x,hx,hxt⟩ := htR
  obtain ⟨z,hz,hzt⟩ := htT
  have hxR := R.norm_sub_center_le_long hx.1
  have hyz := T.dist_le_two_long hy hz.1
  have hcx : |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates R.center).1| ≤ R.long := by
    change |S.axes.repr (x-S.center) 0-S.axes.repr (R.center-S.center) 0| ≤ R.long
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (x-R.center) 0).trans hxR
  have hcy : |(S.orthogonalCoordinates y).1-(S.orthogonalCoordinates z).1| ≤ 2*T.long := by
    change |S.axes.repr (y-S.center) 0-S.axes.repr (z-S.center) 0| ≤ 2*T.long
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (y-z) 0).trans (by simpa only [dist_eq_norm] using hyz)
  have hzx : (S.orthogonalCoordinates z).1 = (S.orthogonalCoordinates x).1 := hzt.trans hxt.symm
  rw [hzx] at hcy
  exact (abs_sub_le _ _ _).trans (by linarith)

end Rectangle

/-- The representatives are selected by maximal length. No geometric
packing hypothesis is assumed: their projected popularity sets are disjoint
by construction. -/
theorem exists_projected_popularity_groups {ι : Type*} [DecidableEq ι]
    (R : ι → Rectangle) (s : Finset ι) (S : Rectangle)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : Continuous v) (hδ : 0 < δ)
    (hR : ∀ j ∈ s, (R j).Admissible v K δ)
    (hL : ∀ j ∈ s, (R j).long ≤ S.long)
    (hinter : ∀ j ∈ s, ((R j).carrier ∩ S.carrier).Nonempty)
    (hangle : ∀ j ∈ s, dist ((R j).axes 0) (S.axes 0) ≤ 1/4) :
    ∃ centers : Finset ι, centers ⊆ s ∧
      (δ : ℝ≥0∞)*(∑ i ∈ centers, ENNReal.ofReal (R i).long) ≤ 12*ENNReal.ofReal S.long ∧
      ∀ j ∈ s, ∃ i ∈ centers, (R j).long ≤ (R i).long ∧
        (S.coordinateProjection ((R i).popularSet v) ∩
          S.coordinateProjection ((R j).popularSet v)).Nonempty := by
  let P := fun j => S.coordinateProjection ((R j).popularSet v)
  obtain ⟨l,hl⟩ := projection_group_run_exists R P s
  have hsub : l.toFinset ⊆ s := by
    intro j hj
    exact hl.selected_subset j (List.mem_toFinset.mp hj)
  have hdisj : (l.toFinset : Set ι).PairwiseDisjoint P :=
    (List.pairwiseDisjoint_iff_coe_toFinset_pairwise_disjoint hl.selected_nodup).mpr
      hl.projected_centers_disjoint
  refine ⟨l.toFinset,hsub,?_,?_⟩
  · exact projected_popularity_packing R l.toFinset S hv
      (fun i hi => hR i (hsub hi)) (fun i hi => hL i (hsub hi))
      (fun i hi => hinter i (hsub hi)) (fun i hi => hangle i (hsub hi)) hdisj
  · intro j hj
    have hn (k : ι) (hk : k ∈ s) : (P k).Nonempty := by
      obtain ⟨x,hx⟩ := (R k).popularSet_nonempty (hR k hk) hδ
      exact ⟨(S.orthogonalCoordinates x).1,x,hx,rfl⟩
    obtain ⟨i,hi,hij,hp⟩ := hl.projected_center_cover (by simp [projectionBlocked]) hn j hj
    exact ⟨i,List.mem_toFinset.mpr hi,hij,hp⟩

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FarStripGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative transverse coordinates and the actual area bound for
intersections of two thin rectangles. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert.Rectangle

theorem norm_le_coordinate_sum (R : Rectangle) (z : Plane) :
    ‖z‖ ≤ |R.axes.repr z 0|+|R.axes.repr z 1| := by
  calc
    ‖z‖ = ‖∑ i : Fin 2, R.axes.repr z i • R.axes i‖ := by rw [R.axes.sum_repr]
    _ ≤ ∑ i : Fin 2, ‖R.axes.repr z i • R.axes i‖ := norm_sum_le _ _
    _ = _ := by simp only [Fin.sum_univ_two,norm_smul,R.axes.norm_eq_one,mul_one,Real.norm_eq_abs]

theorem transverse_coordinate_comparable (R S : Rectangle)
    (hangle : dist (R.axes 0) (S.axes 0) ≤ 1) :
    dist (R.axes 0) (S.axes 0)/2 ≤ |R.axes.repr (S.axes 0) 1| ∧
      |R.axes.repr (S.axes 0) 1| ≤ dist (R.axes 0) (S.axes 0) := by
  let a := R.axes.repr (S.axes 0) 0
  let b := R.axes.repr (S.axes 0) 1
  have hunit := R.axes.sum_sq_inner_right (S.axes 0)
  simp only [Fin.sum_univ_two,←R.axes.repr_apply_apply,S.axes.norm_eq_one,one_pow] at hunit
  change a^2+b^2=1 at hunit
  have ha : |a| ≤ 1 := by
    exact (R.abs_coordinate_le_norm (S.axes 0) 0).trans_eq (S.axes.norm_eq_one 0)
  have hd := R.abs_coordinate_le_norm (S.axes 0-R.axes 0) 0
  have hb := R.abs_coordinate_le_norm (S.axes 0-R.axes 0) 1
  have ht := R.norm_le_coordinate_sum (S.axes 0-R.axes 0)
  simp only [map_sub,PiLp.sub_apply] at hd hb ht
  have h00 : R.axes.repr (R.axes 0) 0 = 1 := by simp
  have h01 : R.axes.repr (R.axes 0) 1 = 0 := by simp
  rw [h00] at hd ht
  rw [h01] at hb ht
  change |a-1| ≤ ‖S.axes 0-R.axes 0‖ at hd
  change |b-0| ≤ ‖S.axes 0-R.axes 0‖ at hb
  change ‖S.axes 0-R.axes 0‖ ≤ |a-1|+|b-0| at ht
  have hn : ‖S.axes 0-R.axes 0‖ = dist (R.axes 0) (S.axes 0) := by rw [dist_comm,dist_eq_norm]
  rw [hn] at hd hb ht
  have ha0 : 0 ≤ a := by linarith [(abs_le.mp hd).1]
  have ha1 : a ≤ 1 := (abs_le.mp ha).2
  have hsquare : (1-a)^2 ≤ |b|^2 := by rw [sq_abs]; nlinarith
  have hcomp : 1-a ≤ |b| :=
    (sq_le_sq₀ (by linarith : 0 ≤ 1-a) (abs_nonneg b)).mp hsquare
  have habs : |a-1| = 1-a := by rw [abs_of_nonpos (by linarith)]; ring
  rw [habs,sub_zero] at ht
  exact ⟨by linarith,by simpa only [sub_zero] using hb⟩

end LipschitzHilbert.Rectangle

namespace LipschitzHilbert

theorem strip_projection_area_swap (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (P : Set ℝ) (hP : MeasurableSet P) (a b c w : ℝ) (ha : a ≠ 0) (hw : 0 ≤ w)
    (hproj : ∀ z ∈ E, z.2 ∈ P) (hstrip : ∀ z ∈ E, |a*z.1+b*z.2-c| ≤ w) :
    (volume.prod volume) E ≤ ENNReal.ofReal (2*w/|a|)*volume P := by
  have h := strip_projection_area (Prod.swap ⁻¹' E) (hE.preimage measurable_swap)
    P hP b a c w ha hw (fun z hz => hproj z.swap hz)
    (fun z hz => by simpa only [Prod.fst_swap,Prod.snd_swap,add_comm] using hstrip z.swap hz)
  have he : (volume.prod volume) (Prod.swap ⁻¹' E) = (volume.prod volume) E :=
    (MeasureTheory.Measure.measurePreserving_swap (μ := volume) (ν := volume)).measure_preimage hE.nullMeasurableSet
  rwa [he] at h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FarLineLower
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A lower bound for a transverse line average of the actual dilated
rectangle. The constants fit the fixed dilation in the selection rule. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

theorem far_line_lower (R : Rectangle) (x w : Plane) (q : ℝ) (hq : 0 < q)
    (hqL : q ≤ R.long) (hw : ‖w‖ ≤ 1) (htrans : 1/2 ≤ |R.axes.repr w 1|)
    (hxL : |R.axes.repr (x-R.center) 0| ≤ 64*R.long)
    (hxW : |R.axes.repr (x-R.center) 1| ≤ R.short/2+8*q) :
    ENNReal.ofReal (min R.short q) ≤
      ∫⁻ t in Icc (-64*q) (64*q),
        (R.dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (x+t • w) := by
  let F := fun t : ℝ =>
    (R.dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (x+t • w)
  have hF (t : ℝ) (ht : x+t • w ∈ (R.dilate 265 (by norm_num)).carrier) : F t = 1 := by
    exact indicator_of_mem ht _
  have hw0 : |R.axes.repr w 0| ≤ 1 := (R.abs_coordinate_le_norm w 0).trans hw
  have hw1 : |R.axes.repr w 1| ≤ 1 := (R.abs_coordinate_le_norm w 1).trans hw
  have hlong (t : ℝ) (ht : |t| ≤ 64*q) :
      |R.axes.repr (x+t • w-R.center) 0| ≤ 265*R.long/2 := by
    rw [line_coordinate]
    have hm : |t*R.axes.repr w 0| ≤ 64*q := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hw0 (abs_nonneg t)).trans (by simpa using ht)
    exact (abs_add_le _ _).trans (by linarith)
  by_cases hWq : R.short ≤ q
  · let A : Set ℝ := (fun t => R.axes.repr (x-R.center) 1+t*R.axes.repr w 1) ⁻¹'
        Icc (-R.short/2) (R.short/2)
    have hAm : MeasurableSet A := measurableSet_Icc.preimage (by fun_prop)
    have hsub : A ⊆ Icc (-64*q) (64*q) := by
      intro t ht
      have hu : |R.axes.repr (x-R.center) 1+t*R.axes.repr w 1| ≤ R.short/2 := by
        simpa only [A,mem_preimage,mem_Icc,neg_div,←abs_le] using ht
      have hb : |t*R.axes.repr w 1| ≤ R.short+8*q := by
        have h := abs_sub
          (R.axes.repr (x-R.center) 1+t*R.axes.repr w 1) (R.axes.repr (x-R.center) 1)
        simp only [add_sub_cancel_left] at h
        linarith
      have hprod := mul_le_mul_of_nonneg_left htrans (abs_nonneg t)
      rw [←abs_mul] at hprod
      have habs : |t| ≤ 64*q := by linarith
      simpa only [mem_Icc,neg_mul] using abs_le.mp habs
    have hmem (t : ℝ) (ht : t ∈ A) : x+t • w ∈ (R.dilate 265 (by norm_num)).carrier := by
      constructor
      · exact hlong t (by simpa only [mem_Icc,neg_mul,←abs_le] using hsub ht)
      · change |R.axes.repr (x+t • w-R.center) 1| ≤ 265*R.short/2
        rw [line_coordinate]
        have hu : |R.axes.repr (x-R.center) 1+t*R.axes.repr w 1| ≤ R.short/2 := by
          simpa only [A,mem_preimage,mem_Icc,neg_div,←abs_le] using ht
        linarith [R.short_pos]
    have hd : R.axes.repr w 1 ≠ 0 := by
      intro he
      rw [he,abs_zero] at htrans
      norm_num at htrans
    have hvol : ENNReal.ofReal R.short ≤ volume A := by
      have he : A = (fun t : ℝ => t*R.axes.repr w 1) ⁻¹'
          ((fun u : ℝ => R.axes.repr (x-R.center) 1+u) ⁻¹' Icc (-R.short/2) (R.short/2)) := rfl
      rw [he,Real.volume_preimage_mul_right hd,
        (measurePreserving_add_left volume _).measure_preimage measurableSet_Icc.nullMeasurableSet,
        Real.volume_Icc,show R.short/2- -R.short/2=R.short by ring]
      have hi : (1:ℝ) ≤ |(R.axes.repr w 1)⁻¹| := by
        rw [abs_inv]
        exact (one_le_inv₀ (abs_pos.mpr hd)).mpr hw1
      calc
        _ = 1*ENNReal.ofReal R.short := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hi) le_rfl
    rw [min_eq_left hWq]
    calc
      _ ≤ volume A := hvol
      _ = ∫⁻ t in A, F t := by
        rw [setLIntegral_congr_fun hAm (fun t ht => hF t (hmem t ht))]
        simp
      _ ≤ _ := lintegral_mono_set hsub
  · have hqW : q ≤ R.short := le_of_not_ge hWq
    have hsub : Icc (-q/2) (q/2) ⊆ Icc (-64*q) (64*q) := by
      intro t ht
      constructor <;> linarith [ht.1,ht.2]
    have hmem (t : ℝ) (ht : t ∈ Icc (-q/2) (q/2)) :
        x+t • w ∈ (R.dilate 265 (by norm_num)).carrier := by
      have htq : |t| ≤ q/2 := by simpa only [mem_Icc,neg_div,←abs_le] using ht
      constructor
      · exact hlong t (by linarith)
      · change |R.axes.repr (x+t • w-R.center) 1| ≤ 265*R.short/2
        rw [line_coordinate]
        have hm : |t*R.axes.repr w 1| ≤ q/2 := by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_left hw1 (abs_nonneg t)).trans (by simpa using htq)
        exact (abs_add_le _ _).trans (by linarith)
    rw [min_eq_right hqW]
    calc
      _ = volume (Icc (-q/2) (q/2)) := by rw [Real.volume_Icc]; congr 1; ring
      _ = ∫⁻ t in Icc (-q/2) (q/2), F t := by
        rw [setLIntegral_congr_fun measurableSet_Icc (fun t ht => hF t (hmem t ht))]
        simp
      _ ≤ _ := lintegral_mono_set hsub

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FarSlabGeometry
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local strips in the reference coordinates, and the coordinate bounds
needed to compare their overlap with a transverse line through a small
selected rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

theorem mem_stripSlab (S : Rectangle) (c l : ℝ) (x : Plane) :
    x ∈ S.stripSlab c l ↔
      |(S.orthogonalCoordinates x).1-c| ≤ l/2 ∧
      |(S.orthogonalCoordinates x).2| ≤ S.short/2 := by
  simp only [stripSlab,mem_preimage,mem_prod,mem_Icc,abs_le]
  constructor <;> rintro ⟨⟨h1,h2⟩,h3,h4⟩ <;> constructor <;> constructor <;> linarith

theorem isCompact_stripSlab (S : Rectangle) (c l : ℝ) : IsCompact (S.stripSlab c l) := by
  have he : S.stripSlab c l = S.orthogonalCoordinates.symm ''
      (Icc (c-l/2) (c+l/2) ×ˢ Icc (-S.short/2) (S.short/2)) := by
    ext x
    constructor
    · intro hx
      exact ⟨S.orthogonalCoordinates x,hx,S.orthogonalCoordinates.symm_apply_apply x⟩
    · rintro ⟨z,hz,rfl⟩
      simpa only [stripSlab,mem_preimage,S.orthogonalCoordinates.apply_symm_apply] using hz
  rw [he]
  apply (isCompact_Icc.prod isCompact_Icc).image
  change Continuous (fun z : ℝ × ℝ => S.axes.repr.symm (planeCoordinates z)+S.center)
  apply Continuous.add_const
  apply S.axes.repr.symm.continuous.comp
  change Continuous (fun z : ℝ × ℝ => WithLp.toLp 2 ![z.1,z.2])
  fun_prop

theorem volume_stripSlab (S : Rectangle) (c l : ℝ) :
    volume (S.stripSlab c l) = ENNReal.ofReal l*ENNReal.ofReal S.short := by
  rw [stripSlab,S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv,
    Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
  congr 2 <;> ring

theorem transverse_coordinate_change_bound (R S : Rectangle) (z : Plane) :
    |R.axes.repr z 1| ≤ dist (S.axes 0) (R.axes 0)*|S.axes.repr z 0|+|S.axes.repr z 1| := by
  have h0 := R.abs_coordinate_le_norm (S.axes 0-R.axes 0) 1
  have hz : R.axes.repr (R.axes 0) 1 = 0 := by simp
  rw [map_sub,PiLp.sub_apply,hz,sub_zero] at h0
  change |R.axes.repr (S.axes 0) 1| ≤ dist (S.axes 0) (R.axes 0) at h0
  have h1 : |R.axes.repr (S.axes 1) 1| ≤ 1 :=
    (R.abs_coordinate_le_norm (S.axes 1) 1).trans_eq (S.axes.norm_eq_one 1)
  have he := S.axes.sum_repr z
  rw [Fin.sum_univ_two] at he
  nth_rw 1 [←he]
  rw [map_add,PiLp.add_apply,map_smul,map_smul]
  change |S.axes.repr z 0*R.axes.repr (S.axes 0) 1+
    S.axes.repr z 1*R.axes.repr (S.axes 1) 1| ≤ _
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg (S.axes.repr z 0)),
    mul_le_mul_of_nonneg_left h1 (abs_nonneg (S.axes.repr z 1))]

/-- Coordinate bounds at every point of a short rectangle meeting the
fourfold reference interval. The long rectangle meets the original interval. -/
theorem short_to_long_slab_coordinates (S R T : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : 8*l ≤ R.long) (hTlong : T.long ≤ l)
    (hSshort : S.short ≤ θ*l) (hTshort : T.short ≤ θ*l)
    (hRangle : dist (S.axes 0) (R.axes 0) ≤ 2*θ)
    (hTangle : dist (S.axes 0) (T.axes 0) ≤ 2*θ)
    (hR : (R.carrier ∩ S.stripSlab c l).Nonempty)
    (hT : (T.carrier ∩ S.stripSlab c (4*l)).Nonempty)
    {x : Plane} (hx : x ∈ T.carrier) :
    |R.axes.repr (x-R.center) 0| ≤ 32*R.long ∧
      |R.axes.repr (x-R.center) 1| ≤ R.short/2+8*(2*θ*l) := by
  obtain ⟨y,hyR,hy⟩ := hR
  obtain ⟨z,hzT,hz⟩ := hT
  have hy' := (S.mem_stripSlab c l y).mp hy
  have hz' := (S.mem_stripSlab c (4*l) z).mp hz
  have hxz : |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates z).1| ≤ 2*T.long := by
    change |S.axes.repr (x-S.center) 0-S.axes.repr (z-S.center) 0| ≤ 2*T.long
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (x-z) 0).trans
      (by simpa only [dist_eq_norm] using T.dist_le_two_long hx hzT)
  have hxy0 : |S.axes.repr (x-y) 0| ≤ 9*l/2 := by
    rw [←coordinate_difference]
    change |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates y).1| ≤ 9*l/2
    have ht1 := abs_sub_le (S.orthogonalCoordinates x).1 (S.orthogonalCoordinates z).1 c
    have ht2 := abs_sub_le (S.orthogonalCoordinates x).1 c (S.orthogonalCoordinates y).1
    rw [abs_sub_comm c] at ht2
    linarith [hy'.1,hz'.1]
  have hxz1 := S.transverse_difference_le T hx hzT
  have hxy1 : |S.axes.repr (x-y) 1| ≤ 4*θ*l := by
    have ht1 := abs_sub_le (S.orthogonalCoordinates x).2 (S.orthogonalCoordinates z).2
      (S.orthogonalCoordinates y).2
    have ht2 := abs_sub (S.orthogonalCoordinates z).2 (S.orthogonalCoordinates y).2
    rw [←coordinate_difference] at hxz1 ⊢
    change |(S.orthogonalCoordinates x).2-(S.orthogonalCoordinates y).2| ≤ _
    change |(S.orthogonalCoordinates x).2-(S.orthogonalCoordinates z).2| ≤ _ at hxz1
    have hp := mul_le_mul_of_nonneg_left hTangle T.long_pos.le
    have hp' := mul_le_mul_of_nonneg_left hTlong hθ.le
    nlinarith [hy'.2,hz'.2]
  have hnorm : ‖x-y‖ ≤ 9*l/2+4*θ*l :=
    (S.norm_le_coordinate_sum (x-y)).trans (add_le_add hxy0 hxy1)
  have hr0 := R.abs_coordinate_le_norm (x-y) 0
  have hr1 := R.transverse_coordinate_change_bound S (x-y)
  have hprod := mul_le_mul hRangle hxy0 (abs_nonneg _) (by positivity : 0 ≤ 2*θ)
  have hxsub : x-R.center = (x-y)+(y-R.center) := by abel
  constructor
  · rw [hxsub,map_add,PiLp.add_apply]
    refine (abs_add_le _ _).trans ?_
    have hp := mul_le_mul_of_nonneg_right hθsmall hl.le
    nlinarith [hyR.1]
  · rw [hxsub,map_add,PiLp.add_apply]
    refine (abs_add_le _ _).trans ?_
    nlinarith [hyR.2]

/-- Comparable lengths permit the same transverse line argument with a
larger line radius. -/
theorem comparable_slab_coordinates (S R T : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : l ≤ R.long) (hTlong : T.long ≤ 16*l)
    (hSshort : S.short ≤ θ*l) (hTshort : T.short ≤ θ*l)
    (hRangle : dist (S.axes 0) (R.axes 0) ≤ 2*θ)
    (hTangle : dist (S.axes 0) (T.axes 0) ≤ 2*θ)
    (hR : (R.carrier ∩ S.stripSlab c l).Nonempty)
    (hT : (T.carrier ∩ S.stripSlab c (4*l)).Nonempty)
    {x : Plane} (hx : x ∈ T.carrier) :
    |R.axes.repr (x-R.center) 0| ≤ 64*R.long ∧
      |R.axes.repr (x-R.center) 1| ≤ R.short/2+8*(16*θ*l) := by
  obtain ⟨y,hyR,hy⟩ := hR
  obtain ⟨z,hzT,hz⟩ := hT
  have hy' := (S.mem_stripSlab c l y).mp hy
  have hz' := (S.mem_stripSlab c (4*l) z).mp hz
  have hxz : |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates z).1| ≤ 2*T.long := by
    change |S.axes.repr (x-S.center) 0-S.axes.repr (z-S.center) 0| ≤ 2*T.long
    rw [coordinate_difference]
    exact (S.abs_coordinate_le_norm (x-z) 0).trans
      (by simpa only [dist_eq_norm] using T.dist_le_two_long hx hzT)
  have hxy0 : |S.axes.repr (x-y) 0| ≤ 35*l := by
    rw [←coordinate_difference]
    change |(S.orthogonalCoordinates x).1-(S.orthogonalCoordinates y).1| ≤ 35*l
    have ht1 := abs_sub_le (S.orthogonalCoordinates x).1 (S.orthogonalCoordinates z).1 c
    have ht2 := abs_sub_le (S.orthogonalCoordinates x).1 c (S.orthogonalCoordinates y).1
    rw [abs_sub_comm c] at ht2
    linarith [hy'.1,hz'.1]
  have hxz1 := S.transverse_difference_le T hx hzT
  have hxy1 : |S.axes.repr (x-y) 1| ≤ 34*θ*l := by
    have ht1 := abs_sub_le (S.orthogonalCoordinates x).2 (S.orthogonalCoordinates z).2
      (S.orthogonalCoordinates y).2
    have ht2 := abs_sub (S.orthogonalCoordinates z).2 (S.orthogonalCoordinates y).2
    rw [←coordinate_difference] at hxz1 ⊢
    change |(S.orthogonalCoordinates x).2-(S.orthogonalCoordinates y).2| ≤ _
    change |(S.orthogonalCoordinates x).2-(S.orthogonalCoordinates z).2| ≤ _ at hxz1
    have hp := mul_le_mul_of_nonneg_left hTangle T.long_pos.le
    have hp' := mul_le_mul_of_nonneg_left hTlong hθ.le
    nlinarith [hy'.2,hz'.2]
  have hnorm : ‖x-y‖ ≤ 35*l+34*θ*l :=
    (S.norm_le_coordinate_sum (x-y)).trans (add_le_add hxy0 hxy1)
  have hr0 := R.abs_coordinate_le_norm (x-y) 0
  have hr1 := R.transverse_coordinate_change_bound S (x-y)
  have hprod := mul_le_mul hRangle hxy0 (abs_nonneg _) (by positivity : 0 ≤ 2*θ)
  have hxsub : x-R.center = (x-y)+(y-R.center) := by abel
  constructor
  · rw [hxsub,map_add,PiLp.add_apply]
    refine (abs_add_le _ _).trans ?_
    have hp := mul_le_mul_of_nonneg_right hθsmall hl.le
    nlinarith [hyR.1]
  · rw [hxsub,map_add,PiLp.add_apply]
    refine (abs_add_le _ _).trans ?_
    nlinarith [hyR.2]

end LipschitzHilbert.Rectangle

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FarSlabLineSum
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-rectangle contribution over a local reference strip is
bounded by the actual line part of the auxiliary maximal operator. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
namespace Rectangle

theorem slab_intersection_transverse (R S : Rectangle) (c l : ℝ)
    (ha : R.axes.repr (S.axes 0) 1 ≠ 0) :
    volume (R.carrier ∩ S.stripSlab c l) ≤
      ENNReal.ofReal (R.short / |R.axes.repr (S.axes 0) 1|)*ENNReal.ofReal S.short := by
  let E := S.orthogonalCoordinates '' (R.carrier ∩ S.stripSlab c l)
  have hE : IsCompact E := (R.isCompact_carrier.inter (S.isCompact_stripSlab c l)).image
    S.continuous_orthogonalCoordinates
  have h := strip_projection_area_swap E hE.measurableSet
    (Icc (-S.short/2) (S.short/2)) measurableSet_Icc
    (R.axes.repr (S.axes 0) 1) (R.axes.repr (S.axes 1) 1)
    (-R.axes.repr (S.center-R.center) 1) (R.short/2) ha (half_pos R.short_pos).le
    (fun z hz => by
      obtain ⟨x,hx,rfl⟩ := hz
      exact (mem_prod.mp hx.2).2)
    (fun z hz => by
      obtain ⟨x,hx,rfl⟩ := hz
      have hh := hx.1.2
      rw [change_transverse_coordinates R S x] at hh
      simpa only [sub_neg_eq_add] using hh)
  have he : (volume.prod volume) E = volume (R.carrier ∩ S.stripSlab c l) := by
    have he := S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv E
    rw [Set.preimage_image_eq _ S.orthogonalCoordinates.injective] at he
    exact he.symm
  rw [he,Real.volume_Icc,show S.short/2- -S.short/2=S.short by ring,
    show 2*(R.short/2)=R.short by ring] at h
  exact h

theorem slab_intersection_min_area (R S : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ)
    (hangle : dist (R.axes 0) (S.axes 0) ≤ 1)
    (hlower : θ/2 ≤ dist (R.axes 0) (S.axes 0)) :
    volume (R.carrier ∩ S.stripSlab c l) ≤
      ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short*ENNReal.ofReal (min R.short (2*θ*l)) := by
  have hc := R.transverse_coordinate_comparable S hangle
  have hb : θ/4 ≤ |R.axes.repr (S.axes 0) 1| := by linarith
  have hbpos : 0 < |R.axes.repr (S.axes 0) 1| := lt_of_lt_of_le (by positivity) hb
  by_cases hw : R.short ≤ 2*θ*l
  · rw [min_eq_left hw]
    have hreal : R.short/|R.axes.repr (S.axes 0) 1| ≤ (4/θ)*R.short := by
      apply (div_le_iff₀ hbpos).mpr
      have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4/θ by positivity)
      have he : (4/θ)*(θ/4)=1 := by field_simp
      rw [he] at hh
      have hh' := mul_le_mul_of_nonneg_left hh R.short_pos.le
      nlinarith
    calc
      _ ≤ ENNReal.ofReal (R.short/|R.axes.repr (S.axes 0) 1|)*ENNReal.ofReal S.short :=
        R.slab_intersection_transverse S c l (abs_pos.mp hbpos)
      _ ≤ ENNReal.ofReal ((4/θ)*R.short)*ENNReal.ofReal S.short :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; ring
  · rw [min_eq_right (le_of_not_ge hw)]
    calc
      _ ≤ volume (S.stripSlab c l) := measure_mono inter_subset_right
      _ = ENNReal.ofReal l*ENNReal.ofReal S.short := S.volume_stripSlab c l
      _ ≤ ENNReal.ofReal (8*l)*ENNReal.ofReal S.short :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
      _ = _ := by
        have he : (8*l)*S.short=(4/θ)*S.short*(2*θ*l) := by field_simp; ring
        calc
          _ = ENNReal.ofReal ((8*l)*S.short) := (ENNReal.ofReal_mul (by positivity)).symm
          _ = ENNReal.ofReal ((4/θ)*S.short*(2*θ*l)) := congrArg ENNReal.ofReal he
          _ = _ := by
            rw [ENNReal.ofReal_mul (mul_nonneg (div_nonneg (by norm_num) hθ.le) S.short_pos.le),
              ENNReal.ofReal_mul (div_nonneg (by norm_num) hθ.le)]


end Rectangle

variable {ι κ : Type*} [Fintype κ]

theorem far_slab_line_sum (D : κ → Rectangle) (R : ι → Rectangle)
    (s : Finset ι) (S T : Rectangle) (i : κ) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, 8*l ≤ (R j).long) (hTlong : T.long ≤ l)
    (hSshort : S.short ≤ θ*l) (hTshort : T.short ≤ θ*l)
    (hRangle : ∀ j ∈ s, dist (S.axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist (S.axes 0) ((R j).axes 0))
    (hTangle : dist (S.axes 0) (T.axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ S.stripSlab c l).Nonempty)
    (hT : (T.carrier ∩ S.stripSlab c (4*l)).Nonempty)
    (htrans : ∀ j ∈ s, 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1|)
    (x : Plane) (hx : x ∈ T.carrier) :
    (∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)) ≤
      ENNReal.ofReal 6144*volume (S.stripSlab c l)*
        positiveAuxiliary (fun i => (D i).orthogonalCoordinates)
          (rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s) x := by
  let q := 2*θ*l
  have hq : 0 < q := by dsimp [q]; positivity
  let g := rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s
  let e := (D i).orthogonalCoordinates
  let a := (e x).1
  let b := (e x).2
  let I := Icc (a-64*q) (a+64*q)
  let P := fun u : ℝ => e.symm (u,b)
  have hP : Measurable P := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hsum : (∫⁻ u in I, g (P u)) = ∑ j ∈ s,
      ∫⁻ u in I, ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    apply lintegral_finsetSum
    intro j _
    exact (measurable_const.indicator ((R j).dilate 265 (by norm_num)).measurableSet_carrier).comp hP
  have hterm (j : ι) (hj : j ∈ s) :
      volume ((R j).carrier ∩ S.stripSlab c l) ≤
      (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I,
        ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    have hcoord := S.short_to_long_slab_coordinates (R j) T c l θ hl hθ hθsmall
      (hRlong j hj) hTlong hSshort hTshort (hRangle j hj) hTangle (hR j hj) hT hx
    have hqL : q ≤ (R j).long := by
      have hh := mul_le_mul_of_nonneg_right hθsmall hl.le
      dsimp [q]
      linarith [hRlong j hj]
    have hline := (R j).far_line_lower x ((D i).axes 0) q hq hqL
      (by rw [(D i).axes.norm_eq_one]) (htrans j hj)
      (by linarith [hcoord.1,(R j).long_pos]) hcoord.2
    have hchange := Rectangle.line_integral_change_origin (D i)
      (f := ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)))
      (measurable_const.indicator ((R j).dilate 265 (by norm_num)).measurableSet_carrier) x (64*q)
    simp only [neg_mul] at hline
    rw [hchange] at hline
    have hangle : dist ((R j).axes 0) (S.axes 0) ≤ 1 := by
      rw [dist_comm]
      linarith [hRangle j hj]
    have hlower : θ/2 ≤ dist ((R j).axes 0) (S.axes 0) := by simpa only [dist_comm] using hRlower j hj
    exact ((R j).slab_intersection_min_area S c l θ hl hθ hangle hlower).trans
      (mul_le_mul' le_rfl hline)
  have haux := positiveAuxiliary_line_integral (fun j => (D j).orthogonalCoordinates)
    g i a (64*q) (by positivity) x (by constructor <;> dsimp [a] <;> linarith)
  have he : (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*
      (6*ENNReal.ofReal (2*(64*q))) = ENNReal.ofReal 6144*volume (S.stripSlab c l) := by
    rw [S.volume_stripSlab]
    have hreal : (4/θ)*(6*(2*(64*q)))=6144*l := by dsimp [q]; field_simp; ring
    calc
      _ = ENNReal.ofReal ((4/θ)*(6*(2*(64*q))))*ENNReal.ofReal S.short := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4/θ),ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6)]
        norm_num
        ring
      _ = _ := by rw [hreal,ENNReal.ofReal_mul (by norm_num)]; ring
  calc
    _ ≤ ∑ j ∈ s, (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I,
        ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) :=
      Finset.sum_le_sum hterm
    _ = (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I, g (P u) := by
      rw [hsum,Finset.mul_sum]
    _ ≤ (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*
        (6*ENNReal.ofReal (2*(64*q))*positiveAuxiliary (fun j => (D j).orthogonalCoordinates) g x) :=
      mul_le_mul' le_rfl haux
    _ = _ := by rw [←mul_assoc,he]

/-- The comparable-length version uses the same fixed direction net. -/
theorem comparable_slab_line_sum (D : κ → Rectangle) (R : ι → Rectangle)
    (s : Finset ι) (S T : Rectangle) (i : κ) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, l ≤ (R j).long) (hTlong : T.long ≤ 16*l)
    (hSshort : S.short ≤ θ*l) (hTshort : T.short ≤ θ*l)
    (hRangle : ∀ j ∈ s, dist (S.axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist (S.axes 0) ((R j).axes 0))
    (hTangle : dist (S.axes 0) (T.axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ S.stripSlab c l).Nonempty)
    (hT : (T.carrier ∩ S.stripSlab c (4*l)).Nonempty)
    (htrans : ∀ j ∈ s, 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1|)
    (x : Plane) (hx : x ∈ T.carrier) :
    (∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)) ≤
      ENNReal.ofReal 49152*volume (S.stripSlab c l)*
        positiveAuxiliary (fun i => (D i).orthogonalCoordinates)
          (rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s) x := by
  let q := 16*θ*l
  have hq : 0 < q := by dsimp [q]; positivity
  let g := rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s
  let e := (D i).orthogonalCoordinates
  let a := (e x).1
  let b := (e x).2
  let I := Icc (a-64*q) (a+64*q)
  let P := fun u : ℝ => e.symm (u,b)
  have hP : Measurable P := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hsum : (∫⁻ u in I, g (P u)) = ∑ j ∈ s,
      ∫⁻ u in I, ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    apply lintegral_finsetSum
    intro j _
    exact (measurable_const.indicator ((R j).dilate 265 (by norm_num)).measurableSet_carrier).comp hP
  have hterm (j : ι) (hj : j ∈ s) :
      volume ((R j).carrier ∩ S.stripSlab c l) ≤
      (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I,
        ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) := by
    have hcoord := S.comparable_slab_coordinates (R j) T c l θ hl hθ hθsmall
      (hRlong j hj) hTlong hSshort hTshort (hRangle j hj) hTangle (hR j hj) hT hx
    have hqL : q ≤ (R j).long := by
      have hh := mul_le_mul_of_nonneg_right hθsmall hl.le
      dsimp [q]
      linarith [hRlong j hj]
    have hline := (R j).far_line_lower x ((D i).axes 0) q hq hqL
      (by rw [(D i).axes.norm_eq_one]) (htrans j hj)
      hcoord.1 hcoord.2
    have hchange := Rectangle.line_integral_change_origin (D i)
      (f := ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)))
      (measurable_const.indicator ((R j).dilate 265 (by norm_num)).measurableSet_carrier) x (64*q)
    simp only [neg_mul] at hline
    rw [hchange] at hline
    have hangle : dist ((R j).axes 0) (S.axes 0) ≤ 1 := by
      rw [dist_comm]
      linarith [hRangle j hj]
    have hlower : θ/2 ≤ dist ((R j).axes 0) (S.axes 0) := by simpa only [dist_comm] using hRlower j hj
    have hmin : ENNReal.ofReal (min (R j).short (2*θ*l)) ≤
        ENNReal.ofReal (min (R j).short q) := by
      apply ENNReal.ofReal_le_ofReal
      apply min_le_min_left
      dsimp [q]
      nlinarith [mul_pos hθ hl]
    exact ((R j).slab_intersection_min_area S c l θ hl hθ hangle hlower).trans
      (mul_le_mul' le_rfl (hmin.trans hline))
  have haux := positiveAuxiliary_line_integral (fun j => (D j).orthogonalCoordinates)
    g i a (64*q) (by positivity) x (by constructor <;> dsimp [a] <;> linarith)
  have he : (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*
      (6*ENNReal.ofReal (2*(64*q))) = ENNReal.ofReal 49152*volume (S.stripSlab c l) := by
    rw [S.volume_stripSlab]
    have hreal : (4/θ)*(6*(2*(64*q)))=49152*l := by dsimp [q]; field_simp; ring
    calc
      _ = ENNReal.ofReal ((4/θ)*(6*(2*(64*q))))*ENNReal.ofReal S.short := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4/θ),ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 6)]
        norm_num
        ring
      _ = _ := by rw [hreal,ENNReal.ofReal_mul (by norm_num)]; ring
  calc
    _ ≤ ∑ j ∈ s, (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I,
        ((R j).dilate 265 (by norm_num)).carrier.indicator (fun _ => (1:ℝ≥0∞)) (P u) :=
      Finset.sum_le_sum hterm
    _ = (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*∫⁻ u in I, g (P u) := by
      rw [hsum,Finset.mul_sum]
    _ ≤ (ENNReal.ofReal (4/θ)*ENNReal.ofReal S.short)*
        (6*ENNReal.ofReal (2*(64*q))*positiveAuxiliary (fun j => (D j).orthogonalCoordinates) g x) :=
      mul_le_mul' le_rfl haux
    _ = _ := by rw [←mul_assoc,he]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FarSlabExclusion
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-rectangle exclusion estimate (Lacey--Li, Lemma 3.16) from
actual non-removal. The finite direction net is the one already used
in the near-angle selection estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

private theorem long_slab_threshold : ENNReal.ofReal 6144*selectionThreshold < 1 := by
  change ENNReal.ofReal 6144*ENNReal.ofReal (1/1048576:ℝ) < 1
  rw [←ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_lt_one]
  norm_num

theorem far_slab_selected_bound {ι : Type*} {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (s previous : Finset ι) (r : ι) (hs : s ⊆ previous)
    (S : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, 8*l ≤ (R j).long) (hTlong : (R r).long ≤ l)
    (hSshort : S.short ≤ θ*l) (hTshort : (R r).short ≤ θ*l)
    (hRangle : ∀ j ∈ s, dist (S.axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist (S.axes 0) ((R j).axes 0))
    (hTangle : dist (S.axes 0) ((R r).axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ S.stripSlab c l).Nonempty)
    (hT : ((R r).carrier ∩ S.stripSlab c (4*l)).Nonempty)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)) < volume (S.stripSlab c l) := by
  classical
  obtain ⟨i,hi⟩ := hD S
  have htrans (j : ι) (hj : j ∈ s) : 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1| := by
    exact Rectangle.nearby_transverse_coordinate S (R j) (D i)
      (by rw [dist_comm]; linarith [hRangle j hj]) hi.le
  let e := fun i => (D i).orthogonalCoordinates
  let g := rectangleCount (fun j => (R j).dilate 265 (by norm_num)) previous
  have hpoint : ∃ x ∈ (R r).carrier, positiveAuxiliary e g x ≤ selectionThreshold := by
    by_contra hn
    push Not at hn
    exact hnot hn
  obtain ⟨x,hx,hvalue⟩ := hpoint
  have hline := far_slab_line_sum D R s S (R r) i c l θ hl hθ hθsmall hRlong hTlong
    hSshort hTshort hRangle hRlower hTangle hR hT htrans x hx
  have hm := positiveAuxiliary_mono e
    (rectangleCount_mono (fun j => (R j).dilate 265 (by norm_num)) hs) x
  have hpos : volume (S.stripSlab c l) ≠ 0 := by
    rw [S.volume_stripSlab]
    exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
      (ne_of_gt (ENNReal.ofReal_pos.mpr S.short_pos))
  have htop : volume (S.stripSlab c l) ≠ ∞ := by
    rw [S.volume_stripSlab]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal 6144*volume (S.stripSlab c l)*
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s) x := hline
    _ ≤ ENNReal.ofReal 6144*volume (S.stripSlab c l)*selectionThreshold :=
      mul_le_mul' le_rfl (hm.trans hvalue)
    _ = (ENNReal.ofReal 6144*selectionThreshold)*volume (S.stripSlab c l) := by ring
    _ < 1*volume (S.stripSlab c l) :=
      (ENNReal.mul_lt_mul_iff_left hpos htop).mpr long_slab_threshold
    _ = _ := one_mul _

private theorem comparable_slab_threshold : ENNReal.ofReal 49152*selectionThreshold < 1 := by
  change ENNReal.ofReal 49152*ENNReal.ofReal (1/1048576:ℝ) < 1
  rw [←ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_lt_one]
  norm_num

theorem comparable_slab_selected_bound {ι : Type*} {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (s previous : Finset ι) (r : ι) (hs : s ⊆ previous)
    (S : Rectangle) (c l θ : ℝ)
    (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, l ≤ (R j).long) (hTlong : (R r).long ≤ 16*l)
    (hSshort : S.short ≤ θ*l) (hTshort : (R r).short ≤ θ*l)
    (hRangle : ∀ j ∈ s, dist (S.axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist (S.axes 0) ((R j).axes 0))
    (hTangle : dist (S.axes 0) ((R r).axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ S.stripSlab c l).Nonempty)
    (hT : ((R r).carrier ∩ S.stripSlab c (4*l)).Nonempty)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ s, volume ((R j).carrier ∩ S.stripSlab c l)) < volume (S.stripSlab c l) := by
  classical
  obtain ⟨i,hi⟩ := hD S
  have htrans (j : ι) (hj : j ∈ s) : 1/2 ≤ |(R j).axes.repr ((D i).axes 0) 1| := by
    exact Rectangle.nearby_transverse_coordinate S (R j) (D i)
      (by rw [dist_comm]; linarith [hRangle j hj]) hi.le
  let e := fun i => (D i).orthogonalCoordinates
  let g := rectangleCount (fun j => (R j).dilate 265 (by norm_num)) previous
  have hpoint : ∃ x ∈ (R r).carrier, positiveAuxiliary e g x ≤ selectionThreshold := by
    by_contra hn
    push Not at hn
    exact hnot hn
  obtain ⟨x,hx,hvalue⟩ := hpoint
  have hline := comparable_slab_line_sum D R s S (R r) i c l θ hl hθ hθsmall hRlong hTlong
    hSshort hTshort hRangle hRlower hTangle hR hT htrans x hx
  have hm := positiveAuxiliary_mono e
    (rectangleCount_mono (fun j => (R j).dilate 265 (by norm_num)) hs) x
  have hpos : volume (S.stripSlab c l) ≠ 0 := by
    rw [S.volume_stripSlab]
    exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
      (ne_of_gt (ENNReal.ofReal_pos.mpr S.short_pos))
  have htop : volume (S.stripSlab c l) ≠ ∞ := by
    rw [S.volume_stripSlab]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc
    _ ≤ ENNReal.ofReal 49152*volume (S.stripSlab c l)*
        positiveAuxiliary e (rectangleCount (fun j => (R j).dilate 265 (by norm_num)) s) x := hline
    _ ≤ ENNReal.ofReal 49152*volume (S.stripSlab c l)*selectionThreshold :=
      mul_le_mul' le_rfl (hm.trans hvalue)
    _ = (ENNReal.ofReal 49152*selectionThreshold)*volume (S.stripSlab c l) := by ring
    _ < 1*volume (S.stripSlab c l) :=
      (ENNReal.mul_lt_mul_iff_left hpos htop).mpr comparable_slab_threshold
    _ = _ := one_mul _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectangleLastSelected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite subfamily of a selection run has a last member. All the
other members were present in its actual previous set. -/
noncomputable section
open Set
namespace LipschitzHilbert.RectangleCoverRun
variable {ι : Type*} [DecidableEq ι]
variable {R : ι → Rectangle} {blocked : Finset ι → ι → Prop}
  {previous stock : Finset ι} {selected : List ι}

theorem last_selected_witness (h : RectangleCoverRun R blocked previous stock selected)
    (s : Finset ι) (hs : s.Nonempty) (hsub : s ⊆ selected.toFinset) :
    ∃ r ∈ s, ∃ p : Finset ι, previous ⊆ p ∧ s.erase r ⊆ p ∧ ¬blocked p r := by
  induction h generalizing s with
  | stop previous => simpa using hsub hs.choose_spec
  | step previous stock i tail hi hp ha htail ih =>
    have ht : s.erase i ⊆ tail.toFinset := by
      intro j hj
      have hj' := Finset.mem_erase.mp hj
      have hh := hsub hj'.2
      simp only [List.toFinset_cons,Finset.mem_insert] at hh
      exact hh.resolve_left hj'.1
    by_cases hn : (s.erase i).Nonempty
    · obtain ⟨r,hr,p,hp0,hsp,hb⟩ := ih (s.erase i) hn ht
      have hrs := (Finset.mem_erase.mp hr).2
      refine ⟨r,hrs,p,(Finset.subset_insert _ _).trans hp0,?_,hb⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        exact hp0 (Finset.mem_insert_self _ _)
      · exact hsp (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,
          Finset.mem_erase.mpr ⟨hji,(Finset.mem_erase.mp hj).2⟩⟩)
    · have he : s.erase i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have his : i ∈ s := by
        obtain ⟨j,hj⟩ := hs
        by_contra hni
        have hji : j ≠ i := by intro h; subst j; exact hni hj
        have hh := Finset.mem_erase.mpr ⟨hji,hj⟩
        rw [he] at hh
        exact Finset.notMem_empty j hh
      exact ⟨i,his,previous,Subset.rfl,by simp [he],ha⟩

/-- Every strictly longer selected rectangle precedes the specified
member and belongs to the previous set at its selection. -/
theorem selected_previous_witness (h : RectangleCoverRun R blocked previous stock selected)
    (r : ι) (hr : r ∈ selected) :
    ∃ p : Finset ι, previous ⊆ p ∧
      (∀ j ∈ selected, (R r).long < (R j).long → j ∈ p) ∧ ¬blocked p r := by
  induction h with
  | stop => simp at hr
  | step previous stock i tail hi hp ha htail ih =>
    rcases List.mem_cons.mp hr with hri | hrt
    · subst r
      refine ⟨previous,Subset.rfl,?_,ha⟩
      intro j hj hlong
      rcases List.mem_cons.mp hj with rfl | hjt
      · exact (lt_irrefl _ hlong).elim
      · have hjs := rectangleRemaining_subset blocked previous stock i (htail.selected_subset j hjt)
        exact (not_lt_of_ge (hp j hjs).1 hlong).elim
    · obtain ⟨p,hprev,hpLong,hnot⟩ := ih hrt
      refine ⟨p,(Finset.subset_insert _ _).trans hprev,?_,hnot⟩
      intro j hj hjlong
      rcases List.mem_cons.mp hj with rfl | hjt
      · exact hprev (Finset.mem_insert_self _ _)
      · exact hpLong j hjt hjlong

end LipschitzHilbert.RectangleCoverRun

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComparableSelectedSlab
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A comparable-length subfamily of an actual selection run has bounded
mass in a local strip. The required width bounds follow from non-removal. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem comparable_selected_slab {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (previous stock : Finset ι) (selected : List ι)
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    (s : Finset ι) (hsub : s ⊆ selected.toFinset) (ρ : ι) (hρ : ρ ∈ previous)
    (c l θ : ℝ) (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hsize : ∀ j ∈ s, l ≤ (R j).long ∧ (R j).long ≤ 16*l)
    (hLref : ∀ j ∈ s, (R j).long ≤ (R ρ).long)
    (hinter : ∀ j ∈ s, ((R ρ).carrier ∩ (R j).carrier).Nonempty)
    (hfar : ∀ j ∈ s, 64*(R j).short < (R j).long*dist ((R ρ).axes 0) ((R j).axes 0))
    (hangle : ∀ j ∈ s, dist ((R ρ).axes 0) ((R j).axes 0) ≤ 2*θ)
    (hlower : ∀ j ∈ s, θ/2 ≤ dist ((R ρ).axes 0) ((R j).axes 0))
    (hmeet : ∀ j ∈ s, ((R j).carrier ∩ (R ρ).stripSlab c l).Nonempty) :
    (∑ j ∈ s, volume ((R j).carrier ∩ (R ρ).stripSlab c l)) ≤
      2*volume ((R ρ).stripSlab c l) := by
  by_cases hs : s.Nonempty
  · obtain ⟨r,hr,p,hprev,herase,hnot⟩ := hrun.last_selected_witness s hs hsub
    have hwidth := local_selected_widths (fun i => (D i).orthogonalCoordinates) R p ρ r
      (hprev hρ) (hLref r hr) (hinter r hr) (hfar r hr) hnot l θ hl.le (hsize r hr).2 (hangle r hr)
    have hmeet4 : ((R r).carrier ∩ (R ρ).stripSlab c (4*l)).Nonempty := by
      obtain ⟨x,hxr,hxs⟩ := hmeet r hr
      have hh := ((R ρ).mem_stripSlab c l x).mp hxs
      exact ⟨x,hxr,((R ρ).mem_stripSlab c (4*l) x).mpr ⟨by linarith [hh.1],hh.2⟩⟩
    have hbound := comparable_slab_selected_bound D hD R (s.erase r) p r herase (R ρ) c l θ
      hl hθ hθsmall (fun j hj => (hsize j (Finset.mem_of_mem_erase hj)).1) (hsize r hr).2
      hwidth.1 hwidth.2 (fun j hj => hangle j (Finset.mem_of_mem_erase hj))
      (fun j hj => hlower j (Finset.mem_of_mem_erase hj)) (hangle r hr)
      (fun j hj => hmeet j (Finset.mem_of_mem_erase hj)) hmeet4 hnot
    calc
      _ = (∑ j ∈ s.erase r, volume ((R j).carrier ∩ (R ρ).stripSlab c l))+
          volume ((R r).carrier ∩ (R ρ).stripSlab c l) := (Finset.sum_erase_add _ _ hr).symm
      _ ≤ volume ((R ρ).stripSlab c l)+volume ((R ρ).stripSlab c l) :=
        add_le_add hbound.le (measure_mono inter_subset_right)
      _ = _ := by ring
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_StripSubdivision
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact binary subdivision of the reference strips. Shared boundary
fibers have zero planar measure, so closed strip masses add exactly. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.Rectangle

theorem stripSlab_children (S : Rectangle) (c l : ℝ) :
    S.stripSlab c l = S.stripSlab (c-l/4) (l/2) ∪ S.stripSlab (c+l/4) (l/2) := by
  ext x
  simp only [stripSlab,mem_union,mem_preimage,mem_prod,mem_Icc]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hv⟩
    by_cases hm : (S.orthogonalCoordinates x).1 ≤ c
    · exact Or.inl ⟨⟨by linarith,by linarith⟩,hv⟩
    · exact Or.inr ⟨⟨by linarith,by linarith⟩,hv⟩
  · rintro (⟨⟨hlo,hhi⟩,hv⟩ | ⟨⟨hlo,hhi⟩,hv⟩) <;>
      exact ⟨⟨by linarith,by linarith⟩,hv⟩

theorem volume_coordinate_fiber (S : Rectangle) (c : ℝ) :
    volume {x | (S.orthogonalCoordinates x).1 = c} = 0 := by
  have he : {x | (S.orthogonalCoordinates x).1 = c} =
      S.orthogonalCoordinates ⁻¹' (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) := by ext x; simp
  rw [he,S.orthogonalCoordinates_measurePreserving.measure_preimage_equiv,
    Measure.prod_prod,measure_singleton,zero_mul]

theorem stripSlab_children_null_inter (S : Rectangle) (c l : ℝ) :
    volume (S.stripSlab (c-l/4) (l/2) ∩ S.stripSlab (c+l/4) (l/2)) = 0 := by
  apply measure_mono_null _ (S.volume_coordinate_fiber c)
  intro x hx
  have hxL := hx.1
  have hxR := hx.2
  change ((c-l/4)-(l/2)/2 ≤ (S.orthogonalCoordinates x).1 ∧
    (S.orthogonalCoordinates x).1 ≤ (c-l/4)+(l/2)/2) ∧ _ at hxL
  change ((c+l/4)-(l/2)/2 ≤ (S.orthogonalCoordinates x).1 ∧
    (S.orthogonalCoordinates x).1 ≤ (c+l/4)+(l/2)/2) ∧ _ at hxR
  change (S.orthogonalCoordinates x).1 = c
  linarith [hxL.1.2,hxR.1.1]

theorem intersection_stripSlab_children (S : Rectangle) {E : Set Plane}
    (hE : MeasurableSet E) (c l : ℝ) :
    volume (E ∩ S.stripSlab c l) =
      volume (E ∩ S.stripSlab (c-l/4) (l/2))+
        volume (E ∩ S.stripSlab (c+l/4) (l/2)) := by
  have hnull : volume ((E ∩ S.stripSlab (c-l/4) (l/2)) ∩
      (E ∩ S.stripSlab (c+l/4) (l/2))) = 0 := by
    apply measure_mono_null _ (S.stripSlab_children_null_inter c l)
    intro x hx
    exact ⟨hx.1.2,hx.2.2⟩
  have hm := measure_union_add_inter (μ := volume) (E ∩ S.stripSlab (c-l/4) (l/2))
    (hE.inter (S.isCompact_stripSlab (c+l/4) (l/2)).measurableSet)
  rw [hnull,add_zero] at hm
  rw [S.stripSlab_children c l,inter_union_distrib_left]
  exact hm

end LipschitzHilbert.Rectangle

namespace LipschitzHilbert

theorem stripMass_children {ι : Type*} (R : ι → Rectangle) (s : Finset ι)
    (S : Rectangle) (c l : ℝ) :
    stripMass R s S c l = stripMass R s S (c-l/4) (l/2)+stripMass R s S (c+l/4) (l/2) := by
  unfold stripMass
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact S.intersection_stripSlab_children (R j).measurableSet_carrier c l

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LocalFarExclusion
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The long-overlap exclusion with its local width hypotheses discharged
by the actual reference rectangle and maximal non-removal. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert

theorem local_far_exclusion {ι : Type*} {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (s previous : Finset ι) (r ρ : ι) (hs : s ⊆ previous)
    (hρ : ρ ∈ previous) (hLref : (R r).long ≤ (R ρ).long)
    (hinter : ((R ρ).carrier ∩ (R r).carrier).Nonempty)
    (hfar : 64*(R r).short < (R r).long*dist ((R ρ).axes 0) ((R r).axes 0))
    (c l θ : ℝ) (hl : 0 < l) (hθ : 0 < θ) (hθsmall : θ ≤ 1/20)
    (hRlong : ∀ j ∈ s, 8*l ≤ (R j).long) (hTlong : (R r).long ≤ l)
    (hRangle : ∀ j ∈ s, dist ((R ρ).axes 0) ((R j).axes 0) ≤ 2*θ)
    (hRlower : ∀ j ∈ s, θ/2 ≤ dist ((R ρ).axes 0) ((R j).axes 0))
    (hTangle : dist ((R ρ).axes 0) ((R r).axes 0) ≤ 2*θ)
    (hR : ∀ j ∈ s, ((R j).carrier ∩ (R ρ).stripSlab c l).Nonempty)
    (hT : ((R r).carrier ∩ (R ρ).stripSlab c (4*l)).Nonempty)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ s, volume ((R j).carrier ∩ (R ρ).stripSlab c l)) <
      volume ((R ρ).stripSlab c l) := by
  have hw := local_selected_widths (fun i => (D i).orthogonalCoordinates) R previous ρ r
    hρ hLref hinter hfar hnot l θ hl.le (by linarith) hTangle
  exact far_slab_selected_bound D hD R s previous r hs (R ρ) c l θ hl hθ hθsmall
    hRlong hTlong hw.1 hw.2 hRangle hRlower hTangle hR hT hnot

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_StripMassOperations
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mass operations for the strip stopping argument. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert
variable {ι : Type*}

theorem stripSlab_mono_length (S : Rectangle) (c l l' : ℝ) (h : l ≤ l') :
    S.stripSlab c l ⊆ S.stripSlab c l' := by
  intro x hx
  have hx' := (S.mem_stripSlab c l x).mp hx
  exact (S.mem_stripSlab c l' x).mpr ⟨hx'.1.trans (by linarith),hx'.2⟩

theorem stripMass_mono_family (R : ι → Rectangle) (s t : Finset ι) (hst : s ⊆ t)
    (S : Rectangle) (c l : ℝ) : stripMass R s S c l ≤ stripMass R t S c l := by
  unfold stripMass
  exact Finset.sum_le_sum_of_subset hst

theorem stripMass_mono_region (R : ι → Rectangle) (s : Finset ι) (S : Rectangle)
    (c l c' l' : ℝ) (hsub : S.stripSlab c l ⊆ S.stripSlab c' l') :
    stripMass R s S c l ≤ stripMass R s S c' l' := by
  unfold stripMass
  apply Finset.sum_le_sum
  intro j _
  exact measure_mono (inter_subset_inter_right _ hsub)

theorem stripSlab_child_subset (S : Rectangle) (c l : ℝ) (b : Bool) :
    S.stripSlab (binaryChildCenter c l b) (l/2) ⊆ S.stripSlab c l := by
  rw [S.stripSlab_children c l]
  cases b
  · exact subset_union_left
  · exact subset_union_right

theorem stripMass_filter_meets (R : ι → Rectangle) (s : Finset ι) (S : Rectangle) (c l : ℝ) :
    stripMass R (s.filter (fun j => ((R j).carrier ∩ S.stripSlab c l).Nonempty)) S c l =
      stripMass R s S c l := by
  classical
  unfold stripMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · rfl
  · rw [Set.not_nonempty_iff_eq_empty.mp hj,measure_empty]

theorem stripMass_filter_zero (R : ι → Rectangle) (s : Finset ι) (S : Rectangle) (c l : ℝ)
    (p : ι → Prop) [DecidablePred p]
    (hzero : ∀ j ∈ s, ¬p j → volume ((R j).carrier ∩ S.stripSlab c l) = 0) :
    stripMass R (s.filter p) S c l = stripMass R s S c l := by
  unfold stripMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with hp
  · rfl
  · exact (hzero j hj hp).symm

theorem stripMass_filter_partition (R : ι → Rectangle) (s : Finset ι) (S : Rectangle) (c l : ℝ)
    (p : ι → Prop) [DecidablePred p] :
    stripMass R s S c l = stripMass R (s.filter p) S c l+
      stripMass R (s.filter (fun j => ¬p j)) S c l := by
  exact (Finset.sum_filter_add_sum_filter_not s p _).symm

theorem stripSlab_volume_parent (S : Rectangle) (c l c' : ℝ) :
    volume (S.stripSlab c l) = 2*volume (S.stripSlab c' (l/2)) := by
  rw [S.volume_stripSlab,S.volume_stripSlab]
  have he : ENNReal.ofReal l = 2*ENNReal.ofReal (l/2) := by
    rw [show (2:ℝ≥0∞)=ENNReal.ofReal 2 by norm_num,←ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [he,mul_assoc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SelectedFarFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite far family inside an actual selection run. These data will
be obtained from the projected-popularity grouping; the local estimates
below use no further geometric assumptions. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert

namespace SelectedFarFamily
variable {ι : Type*} [DecidableEq ι]

theorem comparable_mass (F : SelectedFarFamily ι) (c l : ℝ) (hl : 0 < l) :
    stripMass F.rectangles (F.comparableMembers l) F.refRect c l ≤
      2*volume (F.refRect.stripSlab c l) := by
  let t := (F.comparableMembers l).filter
    (fun j => ((F.rectangles j).carrier ∩ F.refRect.stripSlab c l).Nonempty)
  have ht (j : ι) (hj : j ∈ t) : j ∈ F.members :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
  have hb := comparable_selected_slab F.directions F.direction_net F.rectangles
    F.previous F.stock F.selected F.run t (fun j hj => F.members_selected (ht j hj))
    F.reference F.reference_previous c l F.angle hl F.angle_pos F.angle_small
    (fun j hj => (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2)
    (fun j hj => F.lengths j (ht j hj)) (fun j hj => F.intersects j (ht j hj))
    (fun j hj => F.far j (ht j hj)) (fun j hj => F.angle_upper j (ht j hj))
    (fun j hj => F.angle_lower j (ht j hj)) (fun j hj => (Finset.mem_filter.mp hj).2)
  change stripMass F.rectangles t F.refRect c l ≤ _ at hb
  simpa only [t,stripMass_filter_meets] using hb

/-- A strip with large long-rectangle mass cannot meet a shorter selected
rectangle, even in its fourfold enlargement. -/
theorem short_absent (F : SelectedFarFamily ι) (c l : ℝ) (hl : 0 < l)
    (hdense : volume (F.refRect.stripSlab c l) ≤
      stripMass F.rectangles (F.longMembers l) F.refRect c l)
    (r : ι) (hr : r ∈ F.members) (hrshort : (F.rectangles r).long < l) :
    ¬((F.rectangles r).carrier ∩ F.refRect.stripSlab c (4*l)).Nonempty := by
  intro hmeet
  obtain ⟨p,hprev,hbefore,hnot⟩ := F.run.selected_previous_witness r
    (List.mem_toFinset.mp (F.members_selected hr))
  let t := (F.longMembers l).filter
    (fun j => ((F.rectangles j).carrier ∩ F.refRect.stripSlab c l).Nonempty)
  have ht (j : ι) (hj : j ∈ t) : j ∈ F.members ∧ 8*l ≤ (F.rectangles j).long :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hj).1
  have htp : t ⊆ p := by
    intro j hj
    exact hbefore j (List.mem_toFinset.mp (F.members_selected (ht j hj).1)) (by linarith [(ht j hj).2])
  have hb := local_far_exclusion F.directions F.direction_net F.rectangles t p r F.reference
    htp (hprev F.reference_previous) (F.lengths r hr) (F.intersects r hr) (F.far r hr)
    c l F.angle hl F.angle_pos F.angle_small (fun j hj => (ht j hj).2) hrshort.le
    (fun j hj => F.angle_upper j (ht j hj).1) (fun j hj => F.angle_lower j (ht j hj).1)
    (F.angle_upper r hr) (fun j hj => (Finset.mem_filter.mp hj).2) hmeet hnot
  change stripMass F.rectangles t F.refRect c l < _ at hb
  rw [show t = (F.longMembers l).filter
      (fun j => ((F.rectangles j).carrier ∩ F.refRect.stripSlab c l).Nonempty) from rfl,
    stripMass_filter_meets] at hb
  exact (not_lt_of_ge hdense) hb

end SelectedFarFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_BadStripMass
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A dense child strip is bounded by its parent's long mass and the
comparable-length estimate. Short members vanish by actual non-removal. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert.SelectedFarFamily
variable {ι : Type*} [DecidableEq ι]

theorem bad_strip_mass (F : SelectedFarFamily ι) (c l p : ℝ) (hl : 0 < l)
    (hsub : F.refRect.stripSlab c l ⊆ F.refRect.stripSlab p (2*l))
    (hdense : volume (F.refRect.stripSlab c l) ≤
      stripMass F.rectangles (F.longMembers l) F.refRect c l)
    (hparent : stripMass F.rectangles (F.longMembers (2*l)) F.refRect p (2*l) ≤
      4*volume (F.refRect.stripSlab p (2*l))) :
    stripMass F.rectangles F.members F.refRect c l ≤ 10*volume (F.refRect.stripSlab c l) := by
  let u := F.members.filter (fun j => l ≤ (F.rectangles j).long)
  have hu : stripMass F.rectangles u F.refRect c l =
      stripMass F.rectangles F.members F.refRect c l := by
    apply stripMass_filter_zero
    intro j hj hshort
    have hn := F.short_absent c l hl hdense j hj (lt_of_not_ge hshort)
    have he : (F.rectangles j).carrier ∩ F.refRect.stripSlab c l = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hx
      apply hn
      obtain ⟨x,hxR,hxS⟩ := hx
      exact ⟨x,hxR,stripSlab_mono_length F.refRect c l (4*l) (by linarith) hxS⟩
    rw [he,measure_empty]
  let v := u.filter (fun j => (F.rectangles j).long ≤ 16*l)
  let w := u.filter (fun j => ¬(F.rectangles j).long ≤ 16*l)
  have hv : v ⊆ F.comparableMembers l := by
    intro j hj
    have hju := Finset.mem_filter.mp hj
    have hjs := Finset.mem_filter.mp hju.1
    exact Finset.mem_filter.mpr ⟨hjs.1,hjs.2,hju.2⟩
  have hw : w ⊆ F.longMembers (2*l) := by
    intro j hj
    have hju := Finset.mem_filter.mp hj
    have hjs := Finset.mem_filter.mp hju.1
    apply Finset.mem_filter.mpr
    refine ⟨hjs.1,?_⟩
    linarith
  have hvbound := (stripMass_mono_family F.rectangles v (F.comparableMembers l) hv F.refRect c l).trans
    (F.comparable_mass c l hl)
  have hwbound : stripMass F.rectangles w F.refRect c l ≤
      8*volume (F.refRect.stripSlab c l) := by
    calc
      _ ≤ stripMass F.rectangles (F.longMembers (2*l)) F.refRect c l :=
        stripMass_mono_family F.rectangles w _ hw F.refRect c l
      _ ≤ stripMass F.rectangles (F.longMembers (2*l)) F.refRect p (2*l) :=
        stripMass_mono_region F.rectangles _ F.refRect c l p (2*l) hsub
      _ ≤ 4*volume (F.refRect.stripSlab p (2*l)) := hparent
      _ = _ := by
        rw [stripSlab_volume_parent F.refRect p (2*l) c,show (2*l)/2=l by ring]
        ring
  calc
    _ = stripMass F.rectangles u F.refRect c l := hu.symm
    _ = stripMass F.rectangles v F.refRect c l+stripMass F.rectangles w F.refRect c l :=
      stripMass_filter_partition F.rectangles u F.refRect c l (fun j => (F.rectangles j).long ≤ 16*l)
    _ ≤ 2*volume (F.refRect.stripSlab c l)+8*volume (F.refRect.stripSlab c l) :=
      add_le_add hvbound hwbound
    _ = _ := by ring

end LipschitzHilbert.SelectedFarFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_BinaryFarMass
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite binary stopping argument for the far-family mass. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert.SelectedFarFamily
variable {ι : Type*} [DecidableEq ι]

theorem binary_mass_bound (F : SelectedFarFamily ι) (leaf : ℝ)
    (hsmall : ∀ j ∈ F.members, 8*leaf ≤ (F.rectangles j).long) :
    ∀ n c l, 0 < l → l ≤ leaf*(2:ℝ)^n →
      stripMass F.rectangles (F.longMembers l) F.refRect c l ≤ 4*volume (F.refRect.stripSlab c l) →
      stripMass F.rectangles F.members F.refRect c l ≤ 10*volume (F.refRect.stripSlab c l) := by
  let good := fun n c l => l ≤ leaf*(2:ℝ)^n ∧
    stripMass F.rectangles (F.longMembers l) F.refRect c l ≤ 4*volume (F.refRect.stripSlab c l)
  have hzero : ∀ c l, 0 < l → good 0 c l →
      stripMass F.rectangles F.members F.refRect c l ≤ 10*volume (F.refRect.stripSlab c l) := by
    intro c l _ hg
    have hl : l ≤ leaf := by simpa only [pow_zero,mul_one] using hg.1
    have he : F.longMembers l = F.members := by
      apply Finset.filter_eq_self.mpr
      intro j hj
      exact le_trans (by linarith) (hsmall j hj)
    calc
      _ = stripMass F.rectangles (F.longMembers l) F.refRect c l := by rw [he]
      _ ≤ 4*volume (F.refRect.stripSlab c l) := hg.2
      _ ≤ _ := mul_le_mul' (by norm_num) le_rfl
  have hbad : ∀ n c l, 0 < l → good (n+1) c l → ∀ b,
      ¬good n (binaryChildCenter c l b) (l/2) →
      stripMass F.rectangles F.members F.refRect (binaryChildCenter c l b) (l/2) ≤
        10*volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) := by
    intro n c l hl hg b hb
    have hlength : l/2 ≤ leaf*(2:ℝ)^n := by
      have hh := hg.1
      rw [pow_succ] at hh
      linarith
    have hstrict : 4*volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) <
        stripMass F.rectangles (F.longMembers (l/2)) F.refRect (binaryChildCenter c l b) (l/2) := by
      apply lt_of_not_ge
      intro hm
      exact hb ⟨hlength,hm⟩
    have hdense : volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) ≤
        stripMass F.rectangles (F.longMembers (l/2)) F.refRect (binaryChildCenter c l b) (l/2) :=
      (show _ ≤ 4*volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) by
        calc
          _ = 1*volume (F.refRect.stripSlab (binaryChildCenter c l b) (l/2)) := (one_mul _).symm
          _ ≤ _ := mul_le_mul' (by norm_num) le_rfl).trans hstrict.le
    apply F.bad_strip_mass (binaryChildCenter c l b) (l/2) c (half_pos hl)
    · simpa only [show 2*(l/2)=l by ring] using stripSlab_child_subset F.refRect c l b
    · exact hdense
    · simpa only [show 2*(l/2)=l by ring] using hg.2
  have hbound := binary_density_bound (stripMass F.rectangles F.members F.refRect)
    (fun c l => volume (F.refRect.stripSlab c l)) 10 good
    (fun c l _ => stripMass_children F.rectangles F.members F.refRect c l)
    (fun c l _ => by
      have hh := F.refRect.intersection_stripSlab_children MeasurableSet.univ c l
      simpa only [univ_inter] using hh) hzero hbad
  intro n c l hl hlen hg
  exact hbound n c l hl ⟨hlen,hg⟩

/-- A finite far family has uniformly bounded mass in every strip whose
length is at least every member's length. -/
theorem strip_mass_bound (F : SelectedFarFamily ι) (c l : ℝ) (hl : 0 < l)
    (hmax : ∀ j ∈ F.members, (F.rectangles j).long ≤ l) :
    stripMass F.rectangles F.members F.refRect c l ≤ 10*volume (F.refRect.stripSlab c l) := by
  by_cases hn : F.members.Nonempty
  · obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image F.members (fun j => (F.rectangles j).long) hn
    let leaf := (F.rectangles j).long/8
    have hleaf : 0 < leaf := div_pos (F.rectangles j).long_pos (by norm_num)
    have hsmall : ∀ k ∈ F.members, 8*leaf ≤ (F.rectangles k).long := by
      intro k hk
      have hh := hmin k hk
      dsimp [leaf]
      linarith
    obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (l/leaf) (by norm_num : (1:ℝ) < 2)
    have hlen : l ≤ leaf*(2:ℝ)^N := by
      have hh := (div_lt_iff₀ hleaf).mp hN
      linarith
    have he : F.longMembers l = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      have hh := Finset.mem_filter.mp hk
      have hm := hmax k hh.1
      linarith
    apply F.binary_mass_bound leaf hsmall N c l hl hlen
    simp only [he,stripMass,Finset.sum_empty]
    exact zero_le
  · have he : F.members = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he,stripMass,Finset.sum_empty]
    exact zero_le

end LipschitzHilbert.SelectedFarFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FarGroupEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The far-group energy estimate: the actual selected family, localized
by its representative's popularity projection, has total overlap at most
80 times representative length times reference width. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.SelectedFarFamily
variable {ι : Type*} [DecidableEq ι]

theorem group_overlap_bound (F : SelectedFarFamily ι) (B : Rectangle) (v : Plane → Plane)
    (hL : ∀ j ∈ F.members, (F.rectangles j).long ≤ B.long)
    (hproj : ∀ j ∈ F.members,
      (F.refRect.coordinateProjection (B.popularSet v) ∩
        F.refRect.coordinateProjection ((F.rectangles j).popularSet v)).Nonempty) :
    (∑ j ∈ F.members, volume ((F.rectangles j).carrier ∩ F.refRect.carrier)) ≤
      ENNReal.ofReal 80*ENNReal.ofReal B.long*ENNReal.ofReal F.refRect.short := by
  have hB := B.long_pos
  let c := (F.refRect.orthogonalCoordinates B.center).1
  have hsub (j : ι) (hj : j ∈ F.members) :
      (F.rectangles j).carrier ∩ F.refRect.carrier ⊆
        (F.rectangles j).carrier ∩ F.refRect.stripSlab c (8*B.long) := by
    intro x hx
    refine ⟨hx.1,(F.refRect.mem_stripSlab c (8*B.long) x).mpr ⟨?_,?_⟩⟩
    · have hh := F.refRect.projected_group_localization B (F.rectangles j) (hL j hj) (hproj j hj) hx.1
      change |(F.refRect.orthogonalCoordinates x).1-c| ≤ _
      exact hh.trans (by linarith [B.long_pos])
    · exact hx.2.2
  have hm := F.strip_mass_bound c (8*B.long) (by positivity : 0 < 8*B.long)
    (fun j hj => (hL j hj).trans (by linarith [B.long_pos]))
  calc
    _ ≤ stripMass F.rectangles F.members F.refRect c (8*B.long) :=
      Finset.sum_le_sum (fun j hj => measure_mono (hsub j hj))
    _ ≤ 10*volume (F.refRect.stripSlab c (8*B.long)) := hm
    _ = _ := by
      rw [F.refRect.volume_stripSlab,ENNReal.ofReal_mul (by norm_num)]
      norm_num
      ring

end LipschitzHilbert.SelectedFarFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SelectedFarOverlap
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The far-pair overlap estimate for an actual rectangle selection,
combining popular-projection packing with the group energy bound. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Classical
namespace LipschitzHilbert

theorem selected_far_overlap {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (previous stock : Finset ι) (selected : List ι)
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    (s : Finset ι) (hsub : s ⊆ selected.toFinset) (ρ : ι) (hρ : ρ ∈ previous)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hδ : 0 < δ) (hRef : (R ρ).Admissible v K δ)
    (hR : ∀ j ∈ s, (R j).Admissible v K δ)
    (hL : ∀ j ∈ s, (R j).long ≤ (R ρ).long)
    (hinter : ∀ j ∈ s, ((R ρ).carrier ∩ (R j).carrier).Nonempty)
    (hfar : ∀ j ∈ s, 64*(R j).short < (R j).long*dist ((R ρ).axes 0) ((R j).axes 0)) :
    (δ : ℝ≥0∞)*(∑ j ∈ s, volume ((R j).carrier ∩ (R ρ).carrier)) ≤
      960*volume (R ρ).carrier := by
  let S := R ρ
  let θ := fun i => dist (S.axes 0) ((R i).axes 0)
  have hgeom (i : ι) (hi : i ∈ s) : 0 < θ i ∧ θ i ≤ 1/20 ∧ 32*S.short < θ i*S.long := by
    obtain ⟨p,hprev,_,hn⟩ := hrun.selected_previous_witness i (List.mem_toFinset.mp (hsub hi))
    have hw := far_selected_earlier_width (fun i => (D i).orthogonalCoordinates) R p ρ i
      (hprev hρ) (hL i hi) (hinter i hi) (hfar i hi) hn
    have ha := far_selected_angle_bound S (R i) hv hu hδ hRef (hR i hi)
      (hL i hi) (hinter i hi) (hfar i hi) hw
    refine ⟨?_,ha.2,hw⟩
    by_contra hnθ
    have hm := mul_nonpos_of_nonneg_of_nonpos (R i).long_pos.le (le_of_not_gt hnθ)
    have hf := hfar i hi
    change 64*(R i).short < (R i).long*θ i at hf
    linarith [(R i).short_pos]
  have ha (j : ι) (hj : j ∈ s) : dist ((R j).axes 0) (S.axes 0) ≤ 1/4 := by
    rw [dist_comm]
    exact (hgeom j hj).2.1.trans (by norm_num)
  obtain ⟨centers,hcenters,hpack,hcover⟩ := exists_projected_popularity_groups R s S
    hv.continuous hδ hR hL (fun j hj => by simpa only [inter_comm] using hinter j hj) ha
  let group := fun i => s.filter (fun j => (R j).long ≤ (R i).long ∧
    (S.coordinateProjection ((R i).popularSet v) ∩ S.coordinateProjection ((R j).popularSet v)).Nonempty)
  have hg (i : ι) (hi : i ∈ centers) :
      (∑ j ∈ group i, volume ((R j).carrier ∩ S.carrier)) ≤
        ENNReal.ofReal 80*ENNReal.ofReal (R i).long*ENNReal.ofReal S.short := by
    have his := hcenters hi
    have hdirs (j : ι) (hj : j ∈ group i) : dist ((R i).axes 0) ((R j).axes 0) ≤ θ i/2 := by
      have hj' := Finset.mem_filter.mp hj
      apply Rectangle.projected_popularity_directions S (R i) (R j) hv hu hRef.1
        (hL i his) hj'.2.1 (by simpa only [inter_comm] using hinter i his) (by simpa only [inter_comm] using hinter j hj'.1)
        (hfar i his).le (hfar j hj'.1).le _ hj'.2.2
      nlinarith [(hgeom i his).2.2]
    have hupper (j : ι) (hj : j ∈ group i) : dist (S.axes 0) ((R j).axes 0) ≤ 2*θ i := by
      have ht := dist_triangle (S.axes 0) ((R i).axes 0) ((R j).axes 0)
      change dist (S.axes 0) ((R j).axes 0) ≤ θ i+_ at ht
      linarith [hdirs j hj,(hgeom i his).1]
    have hlower (j : ι) (hj : j ∈ group i) : θ i/2 ≤ dist (S.axes 0) ((R j).axes 0) := by
      have ht := dist_triangle (S.axes 0) ((R j).axes 0) ((R i).axes 0)
      rw [dist_comm ((R j).axes 0) ((R i).axes 0)] at ht
      change θ i ≤ _ at ht
      linarith [hdirs j hj]
    let F : SelectedFarFamily ι := {
      n := n
      directions := D
      direction_net := hD
      rectangles := R
      previous := previous
      stock := stock
      selected := selected
      run := hrun
      members := group i
      members_selected := fun j hj => hsub (Finset.mem_filter.mp hj).1
      reference := ρ
      reference_previous := hρ
      angle := θ i
      angle_pos := (hgeom i his).1
      angle_small := (hgeom i his).2.1
      lengths := fun j hj => hL j (Finset.mem_filter.mp hj).1
      intersects := fun j hj => hinter j (Finset.mem_filter.mp hj).1
      far := fun j hj => hfar j (Finset.mem_filter.mp hj).1
      angle_upper := hupper
      angle_lower := hlower }
    exact F.group_overlap_bound (R i) v (fun j hj => (Finset.mem_filter.mp hj).2.1)
      (fun j hj => (Finset.mem_filter.mp hj).2.2)
  have hcover' (j : ι) (hj : j ∈ s) : ∃ i ∈ centers, j ∈ group i := by
    obtain ⟨i,hi,hji,hp⟩ := hcover j hj
    exact ⟨i,hi,Finset.mem_filter.mpr ⟨hj,hji,hp⟩⟩
  let f := fun j => volume ((R j).carrier ∩ S.carrier)
  have hsum : (∑ j ∈ s, f j) ≤ ∑ i ∈ centers, ∑ j ∈ group i, f j := by
    calc
      _ ≤ ∑ j ∈ s, ∑ i ∈ centers, if j ∈ group i then f j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨i,hi,hji⟩ := hcover' j hj
        have hh := Finset.single_le_sum (f := fun i => if j ∈ group i then f j else 0)
          (fun _ _ => zero_le) hi
        simpa only [ite_eq_left hji] using hh
      _ = ∑ i ∈ centers, ∑ j ∈ s, if j ∈ group i then f j else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [←Finset.sum_filter]
        congr 1
        ext j
        simp only [Finset.mem_filter,and_iff_right_iff_imp]
        exact fun hj => (Finset.mem_filter.mp hj).1
  have henergy : (∑ j ∈ s, f j) ≤
      (ENNReal.ofReal 80*ENNReal.ofReal S.short)*(∑ i ∈ centers, ENNReal.ofReal (R i).long) := by
    refine hsum.trans ?_
    calc
      _ ≤ ∑ i ∈ centers, ENNReal.ofReal 80*ENNReal.ofReal (R i).long*ENNReal.ofReal S.short :=
        Finset.sum_le_sum hg
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  calc
    _ ≤ (δ : ℝ≥0∞)*((ENNReal.ofReal 80*ENNReal.ofReal S.short)*
        (∑ i ∈ centers, ENNReal.ofReal (R i).long)) := mul_le_mul' le_rfl henergy
    _ = (ENNReal.ofReal 80*ENNReal.ofReal S.short)*
        ((δ : ℝ≥0∞)*(∑ i ∈ centers, ENNReal.ofReal (R i).long)) := by ring
    _ ≤ (ENNReal.ofReal 80*ENNReal.ofReal S.short)*(12*ENNReal.ofReal S.long) :=
      mul_le_mul' le_rfl hpack
    _ = _ := by rw [S.volume_carrier]; norm_num; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_RectanglePairEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered overlap sums for an actual finite selection list. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem overlapPair_split (R : ι → Rectangle) (i j : ι) :
    overlapPair R i j = nearPair R i j+farPair R i j := by
  by_cases h : (R j).long*dist ((R i).axes 0) ((R j).axes 0) ≤ 64*(R j).short
  · simp only [nearPair,farPair,ite_eq_left h,ite_eq_right (not_lt_of_ge h),add_zero]
  · simp only [nearPair,farPair,ite_eq_right h,ite_eq_left (lt_of_not_ge h),zero_add]

theorem orderedPairSum_split (f g : ι → ι → ℝ≥0∞) (l : List ι) :
    orderedPairSum (fun i j => f i j+g i j) l = orderedPairSum f l+orderedPairSum g l := by
  induction l with
  | nil => simp [orderedPairSum]
  | cons i l ih => simp only [orderedPairSum,Finset.sum_add_distrib,ih]; ring

theorem previousPairSum_cons (f : ι → ι → ℝ≥0∞) (p : Finset ι) (i : ι) (l : List ι)
    (hi : i ∉ p) (hil : i ∉ l) :
    previousPairSum f p (i::l)+orderedPairSum f (i::l) =
      (∑ j ∈ p, f j i)+(previousPairSum f (insert i p) l+orderedPairSum f l) := by
  have hit : i ∉ l.toFinset := by simpa using hil
  simp only [previousPairSum,orderedPairSum,List.toFinset_cons,Finset.sum_insert hit,
    Finset.sum_insert hi,Finset.sum_add_distrib]
  ring

theorem list_overlap_energy (R : ι → Rectangle) (l : List ι) (hl : l.Nodup) :
    (∑ i ∈ l.toFinset, ∑ j ∈ l.toFinset, overlapPair R i j) =
      (∑ i ∈ l.toFinset, volume (R i).carrier)+2*orderedPairSum (overlapPair R) l := by
  induction l with
  | nil => simp [orderedPairSum]
  | cons i l ih =>
    have hn := List.nodup_cons.mp hl
    have hit : i ∉ l.toFinset := by simpa using hn.1
    have hsym : (∑ j ∈ l.toFinset, overlapPair R j i) = ∑ j ∈ l.toFinset, overlapPair R i j := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg volume (inter_comm _ _)
    have hdiag : overlapPair R i i = volume (R i).carrier := by simp [overlapPair]
    simp only [List.toFinset_cons,Finset.sum_insert hit,Finset.sum_add_distrib,orderedPairSum]
    rw [hsym,hdiag,ih hn.2]
    ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FarPairEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total far-pair energy, charged to the earlier rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Classical
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

theorem far_outgoing_sum (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) {previous stock : Finset ι} {selected : List ι}
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    (r : ι) (hr : r ∈ previous)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hδ : 0 < δ) (hRef : (R r).Admissible v K δ)
    (hR : ∀ j ∈ stock, (R j).Admissible v K δ)
    (hL : ∀ j ∈ selected, (R j).long ≤ (R r).long) :
    (δ : ℝ≥0∞)*(∑ j ∈ selected.toFinset, farPair R r j) ≤ 960*volume (R r).carrier := by
  let s := selected.toFinset.filter (fun j =>
    64*(R j).short < (R j).long*dist ((R r).axes 0) ((R j).axes 0) ∧
      ((R r).carrier ∩ (R j).carrier).Nonempty)
  have hs (j : ι) (hj : j ∈ s) : j ∈ selected :=
    List.mem_toFinset.mp (Finset.mem_filter.mp hj).1
  have hb := selected_far_overlap D hD R previous stock selected hrun s
    (Finset.filter_subset _ _) r hr hv hu hδ hRef
    (fun j hj => hR j (hrun.selected_subset j (hs j hj)))
    (fun j hj => hL j (hs j hj))
    (fun j hj => (Finset.mem_filter.mp hj).2.2)
    (fun j hj => (Finset.mem_filter.mp hj).2.1)
  have he : (∑ j ∈ selected.toFinset, farPair R r j) =
      ∑ j ∈ s, volume ((R j).carrier ∩ (R r).carrier) := by
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hf : 64*(R j).short < (R j).long*dist ((R r).axes 0) ((R j).axes 0)
    · by_cases hm : ((R r).carrier ∩ (R j).carrier).Nonempty
      · have hboth := And.intro hf hm
        simp only [farPair,ite_eq_left hf,ite_eq_left hboth,overlapPair]
        exact congrArg volume (inter_comm _ _)
      · have hz := Set.not_nonempty_iff_eq_empty.mp hm
        simp [farPair,hf,overlapPair,hz]
    · simp [farPair,hf]
  rwa [←he] at hb

theorem selected_far_energy (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) {previous stock : Finset ι} {selected : List ι}
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hδ : 0 < δ) (hR : ∀ j ∈ stock, (R j).Admissible v K δ) :
    (δ : ℝ≥0∞)*orderedPairSum (farPair R) selected ≤
      960*(∑ j ∈ selected.toFinset, volume (R j).carrier) := by
  induction hrun with
  | stop => simp [orderedPairSum]
  | step previous stock i tail hi hp ha htail ih =>
    have hhead := far_outgoing_sum D hD R htail i (Finset.mem_insert_self _ _) hv hu hδ
      (hR i hi) (fun j hj => hR j (rectangleRemaining_subset _ _ _ _ hj))
      (fun j hj => (hp j (rectangleRemaining_subset _ _ _ _ (htail.selected_subset j hj))).1)
    have hrest := ih (fun j hj => hR j (rectangleRemaining_subset _ _ _ _ hj))
    have hit : i ∉ tail.toFinset := by
      intro hit
      have hm := htail.selected_subset i (List.mem_toFinset.mp hit)
      exact (mem_rectangleRemaining _ previous stock i i).mp hm |>.2.1 rfl
    simp only [orderedPairSum,mul_add,List.toFinset_cons,Finset.sum_insert hit]
    exact add_le_add hhead hrest

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LaceyLiCoveringReduction
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic reduction in Lacey--Li, Chapter 3: the covering and
intersection estimates (3.1)--(3.2) imply the weak estimate for the
selected high-average family. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert
variable {ι : Type*}

namespace Rectangle

theorem average_mul_volume (R : Rectangle) (h : Plane → ℝ) :
    R.average h*volume R.carrier=∫⁻ x in R.carrier, ‖h x‖ₑ := by
  unfold average
  rw [mul_right_comm,ENNReal.inv_mul_cancel R.volume_carrier_pos.ne' R.volume_carrier_ne_top,one_mul]

theorem high_average_integral (R : Rectangle) (h : Plane → ℝ) (t : ℝ≥0∞)
    (ht : t≤R.average h) : t*volume R.carrier≤∫⁻ x in R.carrier, ‖h x‖ₑ := by
  calc
    _ ≤ R.average h*volume R.carrier := mul_le_mul' ht le_rfl
    _ = _ := R.average_mul_volume h

end Rectangle

theorem selected_area_pairing_bound (R : ι → Rectangle) (s : Finset ι)
    (h : Plane → ℝ) (hh : AEStronglyMeasurable h volume) (t : ℝ≥0∞)
    (hhigh : ∀ i∈s, t≤(R i).average h) :
    t*(∑ i∈s,volume (R i).carrier)≤∫⁻ x, ‖h x‖ₑ*rectangleCount R s x := by
  rw [rectangleCount_pairing R s h hh,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => (R i).high_average_integral h t (hhigh i hi))

theorem selected_area_from_overlap (R : ι → Rectangle) (s : Finset ι)
    (h : Plane → ℝ) (hh : AEStronglyMeasurable h volume) (t D : ℝ≥0∞)
    (hhigh : ∀ i∈s, t≤(R i).average h)
    (hoverlap : (∫⁻ x, rectangleCount R s x^2)≤D*(∑ i∈s,volume (R i).carrier)) :
    t^2*(∑ i∈s,volume (R i).carrier)≤D*squareIntegral volume h := by
  let A := ∑ i∈s, volume (R i).carrier
  by_cases hA : A=0
  · change t^2*A≤_
    rw [hA,mul_zero]
    exact zero_le
  have hAtop : A≠∞ := ENNReal.sum_ne_top.mpr (fun i _ => (R i).volume_carrier_ne_top)
  have hpair := selected_area_pairing_bound R s h hh t hhigh
  have hsq := (pow_le_pow_left' hpair 2).trans (rectangleCount_pairing_sq_le R s h hh)
  have hm := mul_le_mul' (le_refl (squareIntegral volume h)) hoverlap
  have hall : A*(t^2*A)≤A*(D*squareIntegral volume h) := by
    calc
      _ = (t*A)^2 := by ring
      _ ≤ squareIntegral volume h*(∫⁻ x, rectangleCount R s x^2) := hsq
      _ ≤ squareIntegral volume h*(D*A) := hm
      _ = _ := by ring
  exact (ENNReal.mul_le_mul_iff_right hA hAtop).mp hall

theorem covering_weak_bound (R : ι → Rectangle) (s : Finset ι) (U : Set Plane)
    (h : Plane → ℝ) (hh : AEStronglyMeasurable h volume) (t B D : ℝ≥0∞)
    (hhigh : ∀ i∈s, t≤(R i).average h)
    (hcover : volume U≤B*(∑ i∈s,volume (R i).carrier))
    (hoverlap : (∫⁻ x, rectangleCount R s x^2)≤D*(∑ i∈s,volume (R i).carrier)) :
    t^2*volume U≤B*D*squareIntegral volume h := by
  calc
    _ ≤ t^2*(B*(∑ i∈s,volume (R i).carrier)) := mul_le_mul' le_rfl hcover
    _ = B*(t^2*(∑ i∈s,volume (R i).carrier)) := by ring
    _ ≤ B*(D*squareIntegral volume h) :=
      mul_le_mul' le_rfl (selected_area_from_overlap R s h hh t D hhigh hoverlap)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_NearPairEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total near-pair energy. The previous set grows during selection, so
all near interactions are charged once to the later rectangle. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

omit [DecidableEq ι] in
theorem near_previous_sum (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (previous : Finset ι) (r : ι)
    (hL : ∀ j ∈ previous, (R r).long ≤ (R j).long)
    (hnot : ¬maximalBlocked (fun i => (D i).orthogonalCoordinates) R
      selectionDilation (by norm_num) selectionThreshold previous r) :
    (∑ j ∈ previous, nearPair R j r) ≤ volume (R r).carrier := by
  let s := previous.filter (fun j => (R r).long*dist ((R j).axes 0) ((R r).axes 0) ≤ 64*(R r).short)
  have hh := uniform_near_selected_overlap D hD R s previous (Finset.filter_subset _ _) r
    (fun j hj => hL j (Finset.mem_filter.mp hj).1)
    (fun j hj => (Finset.mem_filter.mp hj).2) hnot
  have he : (∑ j ∈ previous, nearPair R j r) =
      ∑ j ∈ s, volume ((R r).carrier ∩ (R j).carrier) := by
    dsimp [s]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    unfold nearPair overlapPair
    rw [inter_comm (R j).carrier]
  rwa [←he] at hh

theorem selected_near_energy (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) {previous stock : Finset ι} {selected : List ι}
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) previous stock selected)
    (hdis : Disjoint previous stock)
    (hL : ∀ i ∈ previous, ∀ j ∈ stock, (R j).long ≤ (R i).long) :
    previousPairSum (nearPair R) previous selected+orderedPairSum (nearPair R) selected ≤
      ∑ j ∈ selected.toFinset, volume (R j).carrier := by
  induction hrun with
  | stop previous => simp [previousPairSum,orderedPairSum]
  | step previous stock i tail hi hp ha htail ih =>
    have hip : i ∉ previous := by
      intro hip
      exact Finset.disjoint_left.mp hdis hip hi
    have hit : i ∉ tail := by
      intro hit
      exact (mem_rectangleRemaining _ previous stock i i).mp (htail.selected_subset i hit) |>.2.1 rfl
    have hdn : Disjoint (insert i previous)
        (rectangleRemaining (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
          selectionDilation (by norm_num) selectionThreshold) previous stock i) := by
      apply Finset.disjoint_left.mpr
      intro j hj hjr
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        exact (mem_rectangleRemaining _ previous stock i i).mp hjr |>.2.1 rfl
      · exact Finset.disjoint_left.mp hdis hj (rectangleRemaining_subset _ _ _ _ hjr)
    have hln : ∀ k ∈ insert i previous,
        ∀ j ∈ rectangleRemaining (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
          selectionDilation (by norm_num) selectionThreshold) previous stock i,
        (R j).long ≤ (R k).long := by
      intro k hk j hj
      have hjs := rectangleRemaining_subset _ _ _ _ hj
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (hp j hjs).1
      · exact hL k hk j hjs
    have hhead := near_previous_sum D hD R previous i (fun j hj => hL j hj i hi) ha
    rw [previousPairSum_cons (nearPair R) previous i tail hip hit]
    have ih' := ih hdn hln
    have hit' : i ∉ tail.toFinset := by simpa using hit
    simpa only [List.toFinset_cons,Finset.sum_insert hit'] using add_le_add hhead ih'

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_SelectedCountingEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual selected rectangle count has the Lacey--Li second moment
bound. Both near and far overlaps have been proved from non-removal. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Classical
namespace LipschitzHilbert

theorem selected_counting_energy {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : Fin n → Rectangle)
    (hD : ∀ T : Rectangle, ∃ i, dist ((D i).axes 0) (T.axes 1) < 1/4)
    (R : ι → Rectangle) (stock : Finset ι) (selected : List ι)
    (hrun : RectangleCoverRun R
      (maximalBlocked (fun i => (D i).orthogonalCoordinates) R
        selectionDilation (by norm_num) selectionThreshold) ∅ stock selected)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : LipschitzWith K v) (hu : ∀ x, ‖v x‖ = 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hR : ∀ j ∈ stock, (R j).Admissible v K δ) :
    (δ : ℝ≥0∞)*(∫⁻ x, (rectangleCount R selected.toFinset x)^2) ≤
      1923*(∑ j ∈ selected.toFinset, volume (R j).carrier) := by
  let A := ∑ j ∈ selected.toFinset, volume (R j).carrier
  have hn := selected_near_energy D hD R hrun (by simp) (by simp)
  have hn' : orderedPairSum (nearPair R) selected ≤ A := by
    simpa only [previousPairSum,Finset.sum_empty,Finset.sum_const_zero,zero_add] using hn
  have hf := selected_far_energy D hD R hrun hv hu hδ hR
  have hd : (δ : ℝ≥0∞) ≤ 1 := by exact_mod_cast hδ1.le
  have hdn : (δ : ℝ≥0∞)*orderedPairSum (nearPair R) selected ≤ A := by
    calc
      _ ≤ 1*A := mul_le_mul' hd hn'
      _ = A := one_mul _
  have hda : (δ : ℝ≥0∞)*A ≤ A := by simpa only [one_mul] using mul_le_mul' hd (le_refl A)
  have hsplit : orderedPairSum (overlapPair R) selected =
      orderedPairSum (nearPair R) selected+orderedPairSum (farPair R) selected := by
    have he : overlapPair R = fun i j => nearPair R i j+farPair R i j := by
      funext i j
      exact overlapPair_split R i j
    rw [he,orderedPairSum_split]
  rw [rectangleCount_second_moment]
  change (δ : ℝ≥0∞)*(∑ i ∈ selected.toFinset, ∑ j ∈ selected.toFinset, overlapPair R i j) ≤ 1923*A
  rw [list_overlap_energy R selected hrun.selected_nodup,hsplit]
  calc
    _ = (δ : ℝ≥0∞)*A+2*((δ : ℝ≥0∞)*orderedPairSum (nearPair R) selected)+
        2*((δ : ℝ≥0∞)*orderedPairSum (farPair R) selected) := by ring
    _ ≤ A+2*A+2*(960*A) := add_le_add (add_le_add hda (mul_le_mul' le_rfl hdn))
      (mul_le_mul' le_rfl hf)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_LaceyLiProof
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-family weak-(2,2) Lipschitz Kakeya estimate of Lacey--Li,
Memoirs AMS 205 (2010), no.965, result 1.10 / equation (1.11).
The proof uses the actual maximal-removal selection, the near/far overlap
bounds, and the proved weak-L1 auxiliary operators. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Classical
namespace LipschitzHilbert

theorem laceyLiInput_proved_oai : LaceyLiInput := by
  obtain ⟨m,D,hD⟩ := Rectangle.exists_finite_transverse_directions
  let B : ℝ≥0∞ := 1+(9+3*(m:ℝ≥0∞))*selectionThreshold⁻¹*ENNReal.ofReal (selectionDilation^2)
  have hη0 : selectionThreshold ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))
  have hηtop : selectionThreshold ≠ ∞ := ENNReal.ofReal_ne_top
  have hBtop : B ≠ ∞ := by
    dsimp [B]
    exact ENNReal.add_ne_top.mpr ⟨by simp,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.add_ne_top.mpr ⟨by norm_num,ENNReal.mul_ne_top (by norm_num) (by simp)⟩)
        (ENNReal.inv_ne_top.mpr hη0))
        ENNReal.ofReal_ne_top⟩
  have hBCtop : B*1923 ≠ ∞ := ENNReal.mul_ne_top hBtop (by norm_num)
  let C : ℝ≥0 := max 1 (B*1923).toNNReal
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hBC : B*1923 ≤ (C:ℝ≥0∞) := by
    rw [←ENNReal.coe_toNNReal hBCtop]
    exact_mod_cast (le_max_right (1:ℝ≥0) (B*1923).toNNReal)
  have hCsq : B*1923 ≤ (C:ℝ≥0∞)^2 := by
    refine hBC.trans ?_
    have h1 : (1:ℝ≥0∞) ≤ C := by exact_mod_cast hC1
    simpa only [one_mul,pow_two] using mul_le_mul' h1 (le_refl (C:ℝ≥0∞))
  refine ⟨C,hCpos,?_⟩
  intro v K δ hv hu hδ hδ1 n R hR h hh t ht
  let stock : Finset (Fin n) := Finset.univ.filter (fun i => (t:ℝ≥0∞) < (R i).average h)
  obtain ⟨selected,hrun⟩ := rectangle_cover_run_maximal_exists
    (fun i => (D i).orthogonalCoordinates) R selectionDilation (by norm_num) selectionThreshold stock
  have henergy := selected_counting_energy D hD R stock selected hrun hv hu hδ hδ1
    (fun i _ => hR i)
  have hδ0 : (δ:ℝ≥0∞) ≠ 0 := by exact_mod_cast hδ.ne'
  have hoverlap : (∫⁻ x, (rectangleCount R selected.toFinset x)^2) ≤
      (1923/(δ:ℝ≥0∞))*(∑ i ∈ selected.toFinset, volume (R i).carrier) := by
    calc
      _ = (δ:ℝ≥0∞)⁻¹*((δ:ℝ≥0∞)*(∫⁻ x, (rectangleCount R selected.toFinset x)^2)) := by
        rw [←mul_assoc,ENNReal.inv_mul_cancel hδ0 ENNReal.coe_ne_top,one_mul]
      _ ≤ (δ:ℝ≥0∞)⁻¹*(1923*(∑ i ∈ selected.toFinset, volume (R i).carrier)) :=
        mul_le_mul' le_rfl henergy
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hcover := maximal_selection_cover_bound (fun i => (D i).orthogonalCoordinates)
    (fun i => (D i).orthogonalCoordinates_measurePreserving) R selectionDilation (by norm_num)
    selectionThreshold hη0 hηtop stock selected hrun
  have hlevel : {x | (t:ℝ≥0∞) < rectangleMaximum R h x} ⊆ ⋃ i ∈ stock, (R i).carrier := by
    intro x hx
    change (t:ℝ≥0∞) < Finset.univ.sup (fun i => if x ∈ (R i).carrier then (R i).average h else 0) at hx
    obtain ⟨i,_,hi⟩ := Finset.lt_sup_iff.mp hx
    by_cases hxi : x ∈ (R i).carrier
    · rw [ite_eq_left hxi] at hi
      exact mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩,hxi⟩
    · rw [ite_eq_right hxi] at hi
      exact (not_lt_zero hi).elim
  have hcover' : volume {x | (t:ℝ≥0∞) < rectangleMaximum R h x} ≤
      B*(∑ i ∈ selected.toFinset, volume (R i).carrier) := by
    refine (measure_mono hlevel).trans ?_
    simpa only [Fintype.card_fin] using hcover
  have hhigh : ∀ i ∈ selected.toFinset, (t:ℝ≥0∞) ≤ (R i).average h := by
    intro i hi
    have his := hrun.selected_subset i (List.mem_toFinset.mp hi)
    exact (Finset.mem_filter.mp his).2.le
  have hweak := covering_weak_bound R selected.toFinset
    {x | (t:ℝ≥0∞) < rectangleMaximum R h x} h hh.aestronglyMeasurable
    (t:ℝ≥0∞) B (1923/(δ:ℝ≥0∞)) hhigh hcover' hoverlap
  refine hweak.trans (mul_le_mul' ?_ le_rfl)
  calc
    B*(1923/(δ:ℝ≥0∞)) = (B*1923)*(δ:ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ (C:ℝ≥0∞)^2*(δ:ℝ≥0∞)⁻¹ := mul_le_mul' hCsq le_rfl
    _ = _ := rfl

end LipschitzHilbert

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.laceyLiInput_proved_oai := @OAI.LipschitzHilbert.laceyLiInput_proved_oai
