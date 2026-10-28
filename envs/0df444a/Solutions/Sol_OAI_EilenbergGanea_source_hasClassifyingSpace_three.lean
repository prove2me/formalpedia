-- Prove2me | solution 1 for OAI.EilenbergGanea.source_hasClassifyingSpace_three
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T06:55:16.224847+00:00
-- url     : https://prove2.me/submissions/dac67627-e2f1-4bfb-83ae-95cefdc31a79

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEGC004

section
-- module Solutions.OAIEG.Cubical_Descending
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

open Classical Set Topology

namespace EilenbergGanea.DescendingCube.Data

section
variable {G A : Type*} [Group G] {f : A → G} (D : Data f)

theorem fullCoord_continuous (c : D.Cell) (a : A) : Continuous (fun x => D.fullCoord c x a) := by
  unfold fullCoord
  split
  · exact continuous_subtype_val.comp (continuous_apply _)
  · exact continuous_const

variable [Fintype A] [Nonempty A]

theorem radius_continuous : Continuous (radius (A := A)) :=
  Continuous.finset_sup'_apply Finset.univ_nonempty (fun a _ => continuous_apply a)

theorem radius_eq_one_iff (c : D.Cell) (x : D.Coordinates c) :
    radius (D.fullCoord c x) = 1 ↔ (D.ones c x).Nonempty := by
  constructor
  · intro hr
    obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (D.fullCoord c x)
    have hh : D.fullCoord c x a = 1 := ha.symm.trans hr
    have hm : a ∈ c.directions := by
      by_contra hn
      simp [fullCoord,hn] at hh
    exact ⟨a,(D.mem_ones c x a).mpr ⟨hm,by simpa [fullCoord,hm] using hh⟩⟩
  · rintro ⟨a,ha⟩
    obtain ⟨ha,he⟩ := (D.mem_ones c x a).mp ha
    apply le_antisymm (radius_le (D.fullCoord_le_one c x))
    have hh := le_radius (D.fullCoord c x) a
    simpa [fullCoord,ha,he] using hh

open scoped unitInterval

theorem deformCoordinates_continuous (c : D.Cell) :
    Continuous (fun z : unitInterval × D.Coordinates c => D.deformCoordinates c z.2 z.1) := by
  apply continuous_pi
  intro a
  apply Continuous.subtype_mk
  exact ((D.fullCoord_continuous c a).comp continuous_snd).add
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.sub (radius_continuous.comp
        (continuous_pi (fun a => (D.fullCoord_continuous c a).comp continuous_snd)))))

theorem deformCoordinates_fixed (c : D.Cell) (x : D.Coordinates c) (t : unitInterval)
    (hx : (D.ones c x).Nonempty) :
    D.deformCoordinates c x t = D.extendCoordinates c x := by
  funext a
  apply Subtype.ext
  simp only [deformCoordinates,extendCoordinates,(D.radius_eq_one_iff c x).mpr hx,
    sub_self,mul_zero,add_zero]

theorem cellDeform_continuous (c : D.Cell) :
    Continuous (fun z : unitInterval × D.Coordinates c => D.cellDeform c z.2 z.1) :=
  (D.characteristic_continuous _).comp (D.deformCoordinates_continuous c)

theorem cellDeform_fixed (c : D.Cell) (x : D.Coordinates c) (t : unitInterval)
    (hx : (D.ones c x).Nonempty) : D.cellDeform c x t = D.characteristic c x := by
  simp only [cellDeform,D.deformCoordinates_fixed c x t hx,characteristic_extend]

end

section
variable {G A : Type*} [Group G] {f : A → G} (D : Data f)

theorem farFaceCoordinates_continuous (c : D.Cell) (a : c.directions) :
    Continuous (D.farFaceCoordinates c a) := by
  apply continuous_pi
  intro b
  exact continuous_apply _

theorem characteristic_farFace (c : D.Cell) (a : c.directions) (x : D.Coordinates c)
    (ha : (x a : ℝ) = 1) :
    D.characteristic (D.farFaceCell c a) (D.farFaceCoordinates c a x) =
      D.characteristic c x := by
  have hm : (a : A) ∈ D.ones c x := (D.mem_ones c x a).mpr ⟨a.property,ha⟩
  apply Point.ext
  · change c.top * f a * D.product (c.top * f a)
      (D.ones (D.farFaceCell c a) (D.farFaceCoordinates c a x)) _ =
        c.top * D.product c.top (D.ones c x) _
    simp only [product,ones_farFace]
    rw [mul_assoc]
    congr 1
    have hi : insert (a : A) ((D.ones c x).erase a) = D.ones c x := Finset.insert_erase hm
    have hc : Set.Pairwise (↑(insert (a : A) ((D.ones c x).erase a)) : Set A)
        (fun b d => Commute (f b) (f d)) := by
      intro b hb d hd hne
      rw [hi] at hb hd
      exact D.commute c.top b d (c.subset (D.ones_subset c x hb))
        (c.subset (D.ones_subset c x hd)) hne
    have he := Finset.noncommProd_insert_of_notMem ((D.ones c x).erase a) a f hc
      (Finset.notMem_erase _ _)
    simpa only [hi] using he.symm
  · funext b
    change D.normalizedCoord (D.farFaceCell c a) (D.farFaceCoordinates c a x) b =
      D.normalizedCoord c x b
    by_cases he : b = a
    · subst b
      simp [normalizedCoord,farFaceCell,a.property,ha]
    · by_cases hb : b ∈ c.directions
      · simp [normalizedCoord,farFaceCell,farFaceCoordinates,he,hb]
      · simp [normalizedCoord,farFaceCell,he,hb]

theorem farFaceCell_length (c : D.Cell) (a : c.directions) :
    D.length (D.farFaceCell c a).top + 1 = D.length c.top :=
  D.decrease c.top a (c.subset a.property)

variable [Fintype A]

theorem fullCoord_point (p : D.Point) :
    D.fullCoord (D.pointCell p) (D.pointCoordinates p) = p.coord := by
  funext a
  by_cases h : p.coord a = 0
  · simp [fullCoord,pointCell,h]
  · simp [fullCoord,pointCell,h,pointCoordinates]

omit [Fintype A] in
theorem characteristic_top_of_ones_empty (c : D.Cell) (x : D.Coordinates c)
    (hx : D.ones c x = ∅) : (D.characteristic c x).top = c.top := by
  change c.top * D.product c.top (D.ones c x) _ = c.top
  simp only [product,hx,Finset.noncommProd_empty,mul_one]

omit [Fintype A] in
theorem characteristic_coord_of_ones_empty (c : D.Cell) (x : D.Coordinates c)
    (hx : D.ones c x = ∅) : (D.characteristic c x).coord = D.fullCoord c x := by
  funext a
  change D.normalizedCoord c x a = D.fullCoord c x a
  by_cases ha : a ∈ c.directions
  · have hne : (x ⟨a,ha⟩ : ℝ) ≠ 1 := by
      intro he
      have hh := (D.mem_ones c x a).mpr ⟨ha,he⟩
      rw [hx] at hh
      exact Finset.notMem_empty a hh
    simp [normalizedCoord,fullCoord,ha,hne]
  · simp [normalizedCoord,fullCoord,ha]

variable [Nonempty A]
open scoped unitInterval

theorem cellDeform_congr (c d : D.Cell) (x : D.Coordinates c) (y : D.Coordinates d)
    (t : unitInterval) (ht : c.top = d.top) (hx : D.fullCoord c x = D.fullCoord d y) :
    D.cellDeform c x t = D.cellDeform d y t := by
  rcases c with ⟨g,s,hs⟩
  rcases d with ⟨h,r,hr⟩
  dsimp only at ht
  subst h
  unfold cellDeform
  congr 1
  funext a
  apply Subtype.ext
  change D.fullCoord _ x a + (t : ℝ) * (1 - radius (D.fullCoord _ x)) =
    D.fullCoord _ y a + (t : ℝ) * (1 - radius (D.fullCoord _ y))
  rw [hx]

/-- On the open part of a cube, radial deformation in its full descending
cube is independent of which zero coordinates were omitted. -/
theorem pointDeform_characteristic (c : D.Cell) (x : D.Coordinates c) (t : unitInterval)
    (hx : D.ones c x = ∅) : D.pointDeform (D.characteristic c x) t = D.cellDeform c x t := by
  have ht := D.characteristic_top_of_ones_empty c x hx
  have hc := D.characteristic_coord_of_ones_empty c x hx
  exact D.cellDeform_congr (D.pointCell (D.characteristic c x)) c
    (D.pointCoordinates _) x t ht ((D.fullCoord_point _).trans hc)

end

variable {G A : Type*} [Group G] {f : A → G} (D : Data f)
variable [Fintype A] [Nonempty A]
open scoped unitInterval NNReal

theorem clip_continuous : Continuous clip := continuous_projIcc (h := zero_le_one)

theorem clip_zero {r : ℝ} (h : r ≤ 0) : clip r = 0 := by
  apply Subtype.ext
  simp [clip,h]

theorem clip_one {r : ℝ} (h : 1 ≤ r) : clip r = 1 := by
  apply Subtype.ext
  simp [clip,h]

theorem flow_fixed (r : ℝ≥0) (p : D.Point) (h : (D.length p.top : ℝ) ≤ r) :
    D.flow r p = p := by rw [flow, dite_eq_left h]

theorem flow_partial (r : ℝ≥0) (p : D.Point)
    (h : (D.length p.top : ℝ) - 1 ≤ r) :
    D.flow r p = D.pointDeform p (clip ((D.length p.top : ℝ) - r)) := by
  rw [flow]
  split_ifs with hh
  · rw [clip_zero (by linarith),pointDeform_zero]
  · rfl

theorem flow_lower (r : ℝ≥0) (p : D.Point)
    (h : (r : ℝ) ≤ (D.length p.top : ℝ) - 1) :
    D.flow r p = D.flow r (D.pointDeform p 1) := by
  have hp : 0 < D.length p.top := by
    by_contra hn
    have hz : D.length p.top = 0 := by omega
    have hr := r.property
    simp only [hz,Nat.cast_zero] at h
    linarith
  have hn : ¬ (D.length p.top : ℝ) ≤ r := by linarith
  rw [flow,dite_eq_right hn]
  split_ifs with hh
  · have he : (r : ℝ) = (D.length p.top : ℝ) - 1 := le_antisymm h hh
    rw [clip_one (by linarith)]
    symm
    apply D.flow_fixed
    have hl := D.pointDeform_one_length p hp
    have hy : (D.length (D.pointDeform p 1).top : ℝ) + 1 ≤ (D.length p.top : ℝ) := by
      exact_mod_cast hl
    linarith
  · rfl

theorem flow_characteristic_high (c : D.Cell) (x : D.Coordinates c) (r : ℝ≥0)
    (hr : (D.length c.top : ℝ) - 1 ≤ r) :
    D.flow r (D.characteristic c x) =
      D.cellDeform c x (clip ((D.length c.top : ℝ) - r)) := by
  by_cases hx : D.ones c x = ∅
  · rw [D.flow_partial r _ (by rw [D.characteristic_top_of_ones_empty c x hx]; exact hr)]
    rw [D.characteristic_top_of_ones_empty c x hx]
    exact D.pointDeform_characteristic c x _ hx
  · have hne := Finset.nonempty_iff_ne_empty.mpr hx
    rw [D.cellDeform_fixed c x _ hne]
    apply D.flow_fixed
    have hl := D.characteristic_length c x
    have hc : 0 < (D.ones c x).card := Finset.card_pos.mpr hne
    have hh : D.length (D.characteristic c x).top + 1 ≤ D.length c.top := by omega
    have hh' : (D.length (D.characteristic c x).top : ℝ) + 1 ≤ D.length c.top := by
      exact_mod_cast hh
    linarith

theorem flow_characteristic_low (c : D.Cell) (x : D.Coordinates c) (r : ℝ≥0)
    (hr : (r : ℝ) ≤ (D.length c.top : ℝ) - 1) :
    D.flow r (D.characteristic c x) = D.flow r (D.cellDeform c x 1) := by
  by_cases hx : D.ones c x = ∅
  · rw [D.flow_lower r _ (by rw [D.characteristic_top_of_ones_empty c x hx]; exact hr)]
    rw [D.pointDeform_characteristic c x 1 hx]
  · rw [D.cellDeform_fixed c x 1 (Finset.nonempty_iff_ne_empty.mpr hx)]

theorem flow_cell_zero_continuous (c : D.Cell) (hc : D.length c.top = 0) :
    Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) := by
  have he : (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) =
      fun z => D.characteristic c z.2 := by
    funext z
    apply D.flow_fixed
    have hl := D.characteristic_length c z.2
    have hh : D.length (D.characteristic c z.2).top = 0 := by omega
    rw [hh,Nat.cast_zero]
    exact z.1.property
  rw [he]
  exact (D.characteristic_continuous c).comp continuous_snd

theorem flow_cell_boundary_continuous (c : D.Cell) (hp : 0 < D.length c.top)
    (ih : ∀ d : D.Cell, D.length d.top < D.length c.top →
      Continuous (fun z : ℝ≥0 × D.Coordinates d => D.flow z.1 (D.characteristic d z.2))) :
    Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.cellDeform c z.2 1)) := by
  have hcoord : Continuous (fun z : ℝ≥0 × D.Coordinates c => D.deformCoordinates c z.2 1) :=
    (D.deformCoordinates_continuous c).comp (continuous_const.prodMk continuous_snd)
  let S : D.desc c.top → Set (ℝ≥0 × D.Coordinates c) := fun a =>
    {z | (D.deformCoordinates c z.2 1 a : ℝ) = 1}
  have hs : ∀ a, IsClosed (S a) := by
    intro a
    exact isClosed_eq (continuous_subtype_val.comp ((continuous_apply a).comp hcoord)) continuous_const
  have hcov : ⋃ a, S a = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨a,ha⟩ := D.deformCoordinates_one_ones c z.2 hp
    obtain ⟨ha,he⟩ := (D.mem_ones _ _ _).mp ha
    exact Set.mem_iUnion.mpr ⟨⟨a,ha⟩,he⟩
  apply (locallyFinite_of_finite S).continuous hcov hs
  intro a
  let d := D.farFaceCell (D.fullCell c.top) a
  have hd : D.length d.top < D.length c.top := by
    have he := D.farFaceCell_length (D.fullCell c.top) a
    change D.length d.top + 1 = D.length c.top at he
    omega
  have hh := ih d hd
  have hf : Continuous (fun z : ℝ≥0 × D.Coordinates c =>
      (z.1,D.farFaceCoordinates (D.fullCell c.top) a (D.deformCoordinates c z.2 1))) :=
    continuous_fst.prodMk ((D.farFaceCoordinates_continuous (D.fullCell c.top) a).comp hcoord)
  apply (hh.comp hf).continuousOn.congr
  intro z hz
  exact congrArg (D.flow z.1)
    (D.characteristic_farFace (D.fullCell c.top) a (D.deformCoordinates c z.2 1) hz).symm

theorem flow_cell_glue_continuous (c : D.Cell)
    (hlower : Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.cellDeform c z.2 1))) :
    Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) := by
  have hhigh : Continuous (fun z : ℝ≥0 × D.Coordinates c =>
      D.cellDeform c z.2 (clip ((D.length c.top : ℝ) - z.1))) := by
    have ht : Continuous (fun z : ℝ≥0 × D.Coordinates c =>
        (clip ((D.length c.top : ℝ) - z.1),z.2)) :=
      (clip_continuous.comp (continuous_const.sub
        (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd
    change Continuous ((fun z : unitInterval × D.Coordinates c => D.cellDeform c z.2 z.1) ∘
      (fun z : ℝ≥0 × D.Coordinates c => (clip ((D.length c.top : ℝ) - (z.1 : ℝ)),z.2)))
    exact Continuous.comp (D.cellDeform_continuous c) ht
  let L : Set (ℝ≥0 × D.Coordinates c) := {z | (z.1 : ℝ) ≤ (D.length c.top : ℝ) - 1}
  let U : Set (ℝ≥0 × D.Coordinates c) := {z | (D.length c.top : ℝ) - 1 ≤ z.1}
  have hL : IsClosed L := isClosed_le (continuous_subtype_val.comp continuous_fst) continuous_const
  have hU : IsClosed U := isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst)
  have hcover : L ∪ U = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    change (z.1 : ℝ) ≤ (D.length c.top : ℝ) - 1 ∨ (D.length c.top : ℝ) - 1 ≤ z.1
    exact le_total _ _
  apply continuousOn_univ.mp
  rw [← hcover]
  apply ContinuousOn.union_of_isClosed _ _ hL hU
  · apply hlower.continuousOn.congr
    intro z hz
    exact D.flow_characteristic_low c z.2 z.1 hz
  · apply hhigh.continuousOn.congr
    intro z hz
    exact D.flow_characteristic_high c z.2 z.1 hz

theorem flow_cell_continuous (c : D.Cell) :
    Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) := by
  have H : ∀ n : ℕ, ∀ c : D.Cell, D.length c.top = n →
      Continuous (fun z : ℝ≥0 × D.Coordinates c => D.flow z.1 (D.characteristic c z.2)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hn
      by_cases hz : n = 0
      · exact D.flow_cell_zero_continuous c (hn.trans hz)
      apply D.flow_cell_glue_continuous c
      apply D.flow_cell_boundary_continuous c (by omega)
      intro d hd
      exact ih (D.length d.top) (by omega) d rfl
  exact H (D.length c.top) c rfl

theorem flow_continuous : Continuous (fun z : ℝ≥0 × D.Point => D.flow z.1 z.2) := by
  apply D.evaluation_quotient.continuous_lift_prod_right
  have hc : Continuous (fun z : (c : D.Cell) × (D.Coordinates c × ℝ≥0) =>
      D.flow z.2.2 (D.characteristic z.1 z.2.1)) := by
    apply continuous_sigma
    intro c
    exact (D.flow_cell_continuous c).comp continuous_swap
  exact hc.comp ((Homeomorph.sigmaProdDistrib (X := fun c : D.Cell => D.Coordinates c) (Y := ℝ≥0)).continuous.comp
    continuous_swap)

omit [Fintype A] [Nonempty A] in
theorem point_eq_origin_of_length_zero (p : D.Point) (hp : D.length p.top = 0) :
    p = D.origin := by
  apply Point.ext
  · exact (D.zero p.top).mp hp
  · funext a
    change p.coord a = 0
    by_contra ha
    have hh := D.decrease p.top a (p.support a ha)
    omega

@[simp] theorem flow_zero (p : D.Point) : D.flow 0 p = D.origin := by
  have H : ∀ n : ℕ, ∀ p : D.Point, D.length p.top = n → D.flow 0 p = D.origin := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hz : n = 0
      · have hp : D.length p.top = 0 := hn.trans hz
        rw [D.flow_fixed 0 p (by simp [hp])]
        exact D.point_eq_origin_of_length_zero p hp
      have hp : 0 < D.length p.top := by omega
      have hr : (0 : ℝ) ≤ (D.length p.top : ℝ) - 1 := by
        have hh : (1 : ℝ) ≤ D.length p.top := by exact_mod_cast hp
        linarith
      rw [D.flow_lower 0 p hr]
      have hl := D.pointDeform_one_length p hp
      exact ih (D.length (D.pointDeform p 1).top) (by omega) (D.pointDeform p 1) rfl
  exact H (D.length p.top) p rfl

@[simp] theorem contraction_one (p : D.Point) : D.contraction 1 p = D.origin := by
  simp [contraction]

theorem heightTime_large (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hb : s ≤ 1 / ((n : ℝ) + 1)) :
    (n : ℝ) ≤ (Real.toNNReal ((1 - s) / s) : ℝ) := by
  apply le_trans _ (Real.le_coe_toNNReal _)
  apply (le_div_iff₀ hs).mpr
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hh := (le_div_iff₀ hn).mp hb
  nlinarith

theorem contraction_cell_eventually_zero (c : D.Cell) (z : unitInterval × D.Coordinates c)
    (hz : (z.1 : ℝ) = 0) :
    (fun w : unitInterval × D.Coordinates c => D.contraction w.1 (D.characteristic c w.2))
      =ᶠ[nhds z] (fun w => D.characteristic c w.2) := by
  have he : 0 < 1 / ((D.length c.top : ℝ) + 1) := by positivity
  have hn : {w : unitInterval × D.Coordinates c | (w.1 : ℝ) < 1 / ((D.length c.top : ℝ) + 1)}
      ∈ nhds z :=
    (isOpen_lt (continuous_subtype_val.comp continuous_fst) continuous_const).mem_nhds
      (by change (z.1 : ℝ) < _; rw [hz]; exact he)
  filter_upwards [hn] with w hw
  unfold contraction
  split_ifs with hs
  · rfl
  · apply D.flow_fixed
    have hp : 0 < (w.1 : ℝ) := lt_of_le_of_ne w.1.property.1 (Ne.symm hs)
    have ht := heightTime_large (D.length c.top) hp hw.le
    have hl := D.characteristic_length c w.2
    have hh : D.length (D.characteristic c w.2).top ≤ D.length c.top := by omega
    exact (by exact_mod_cast hh : (D.length (D.characteristic c w.2).top : ℝ) ≤ D.length c.top).trans ht

theorem contraction_cell_continuous (c : D.Cell) :
    Continuous (fun z : unitInterval × D.Coordinates c => D.contraction z.1 (D.characteristic c z.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : (z.1 : ℝ) = 0
  · exact ((D.characteristic_continuous c).comp continuous_snd).continuousAt.congr_of_eventuallyEq
      (D.contraction_cell_eventually_zero c z hz)
  · have hs : ContinuousAt (fun w : unitInterval × D.Coordinates c =>
        Real.toNNReal ((1 - (w.1 : ℝ)) / w.1)) z := by
      apply (continuous_real_toNNReal).continuousAt.comp
      exact (continuousAt_const.sub (continuous_subtype_val.comp continuous_fst).continuousAt).div
        (continuous_subtype_val.comp continuous_fst).continuousAt hz
    have hh : ContinuousAt (fun w : unitInterval × D.Coordinates c =>
        D.flow (Real.toNNReal ((1 - (w.1 : ℝ)) / w.1)) (D.characteristic c w.2)) z :=
      D.flow_continuous.continuousAt.comp (hs.prodMk
        ((D.characteristic_continuous c).comp continuous_snd).continuousAt)
    apply hh.congr_of_eventuallyEq
    have hn : {w : unitInterval × D.Coordinates c | (w.1 : ℝ) ≠ 0} ∈ nhds z :=
      ((continuous_subtype_val.comp continuous_fst).isOpen_preimage _ isOpen_ne).mem_nhds hz
    filter_upwards [hn] with w hw
    simp only [contraction,ite_eq_right hw]

theorem contraction_continuous : Continuous (fun z : unitInterval × D.Point => D.contraction z.1 z.2) := by
  apply D.evaluation_quotient.continuous_lift_prod_right
  have hc : Continuous (fun z : (c : D.Cell) × (D.Coordinates c × unitInterval) =>
      D.contraction z.2.2 (D.characteristic z.1 z.2.1)) := by
    apply continuous_sigma
    intro c
    exact (D.contraction_cell_continuous c).comp continuous_swap
  exact hc.comp ((Homeomorph.sigmaProdDistrib (X := fun c : D.Cell => D.Coordinates c)
    (Y := unitInterval)).continuous.comp continuous_swap)

/-- Direct radial-shell contraction; no cellular homology or Whitehead theorem is used. -/
theorem contractibleSpace : ContractibleSpace D.Point := by
  apply (contractible_iff_id_nullhomotopic D.Point).mpr
  refine ⟨D.origin,⟨?_⟩⟩
  exact { toFun := fun z => D.contraction z.1 z.2
          continuous_toFun := D.contraction_continuous
          map_zero_left := D.contraction_zero
          map_one_left := D.contraction_one }

end EilenbergGanea.DescendingCube.Data

end

end OAI
end

section
-- module Solutions.OAIEG.Cubical_Realization
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea
open Classical TraceWords
variable {V : Type*} [Fintype V] (L : SimpleGraph V)

variable [Nonempty V]

/-- Contractibility of the actual weak descending-cube realization of the
Artin group, proved by an explicit globally continuous radial-shell flow. -/
theorem artinDescending_contractible : ContractibleSpace (ArtinDescendingRealization L) :=
  (artinDescendingData L).contractibleSpace

end EilenbergGanea

open Classical Set Topology

open Classical Set Topology
namespace EilenbergGanea.CubeInterpolation
variable {G V : Type*} [Group G]

variable (f : V → G)

/-- Every cubical interpolation coordinate is a genuine finite polynomial. -/
theorem operator_continuous {Z : Type*} [TopologicalSpace Z]
    (s : Finset V) (hs) (x : Z → V → ℝ) (hx : ∀ v ∈ s, Continuous (fun z => x z v))
    (φ : G → ℝ) (a : G) : Continuous (fun z => operator f s hs (x z) φ a) := by
  induction s using Finset.induction_on generalizing a with
  | empty => simpa using (continuous_const : Continuous (fun _ : Z => φ a))
  | @insert v s hv ih =>
    simp only [operator_insert f s v hv, Module.End.mul_apply,blend_apply]
    exact (((continuous_const.sub (hx v (by simp))).mul
      (ih _ (fun w hw => hx w (by simp [hw])) a)).add
      ((hx v (by simp)).mul (ih _ (fun w hw => hx w (by simp [hw])) (a*f v))))

end EilenbergGanea.CubeInterpolation

namespace EilenbergGanea.CubeRealization

section
open CubeInterpolation
variable {G V : Type*} [Group G] [Fintype V]
variable (L : SimpleGraph V) (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

variable {L}

omit [Group G] [Fintype V] in
theorem fullCoord_continuous (c : Cell (G := G) L) (v : V) :
    Continuous (fun x : Coordinates c => fullCoord c x v) := by
  unfold fullCoord
  split_ifs
  · exact continuous_subtype_val.comp (continuous_apply _)
  · exact continuous_const

variable (L)

/-- These separating coordinates are continuous for the actual weak topology. -/
theorem interpolation_continuous (φ : G → ℝ) :
    Continuous (fun p : Point (G := G) L f comm => interpolation L f comm p φ) := by
  apply (evaluation_quotient f comm).continuous_iff.mpr
  apply continuous_sigma
  intro c
  change Continuous (fun x : Coordinates c => interpolation L f comm (characteristic f comm c x) φ)
  simp only [interpolation_characteristic]
  exact operator_continuous f c.directions _ (fullCoord c)
    (fun v _ => fullCoord_continuous c v) φ c.base

variable (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)

variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)

include h hf exponent hexponent in
/-- Hausdorffness follows from continuous multilinear vertex functions. -/
theorem point_t2 : T2Space (Point (G := G) L f comm) :=
  T2Space.of_injective_continuous
    (interpolation_injective L f comm h hf exponent hexponent)
    (continuous_pi (fun φ => interpolation_continuous L f comm φ))

end

open Metric

end EilenbergGanea.CubeRealization

namespace EilenbergGanea.CubeInterpolation
variable {G V : Type*} [Group G] (f : V → G)

/-- A nonzero interpolation value comes from one of the finitely many corners. -/
theorem operator_support (s : Finset V)
    (hs : (s : Set V).Pairwise (fun v w => Commute (f v) (f w)))
    (x : V → ℝ) (φ : G → ℝ) (a : G) (h : operator f s hs x φ a ≠ 0) :
    ∃ (t : Finset V) (ht : t ⊆ s), φ (a * t.noncommProd f (hs.mono ht)) ≠ 0 := by
  induction s using Finset.induction_on generalizing a with
  | empty => exact ⟨∅,Finset.Subset.refl _,by simpa using h⟩
  | @insert v s hv ih =>
      let hs' : (s : Set V).Pairwise (fun v w => Commute (f v) (f w)) :=
        hs.mono (by simp)
      rw [operator_insert f s v hv] at h
      simp only [Module.End.mul_apply,blend_apply] at h
      by_cases ha : operator f s hs' x φ a = 0
      · have hb : operator f s hs' x φ (a*f v) ≠ 0 := by
          intro hh
          exact h (by rw [ha,hh]; ring)
        obtain ⟨t,ht,hh⟩ := ih hs' (a*f v) hb
        have hvt : v ∉ t := fun hm => hv (ht hm)
        refine ⟨insert v t,Finset.insert_subset_insert _ ht,?_⟩
        rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hvt,← mul_assoc]
        exact hh
      · obtain ⟨t,ht,hh⟩ := ih hs' a ha
        exact ⟨t,ht.trans (Finset.subset_insert _ _),hh⟩

end EilenbergGanea.CubeInterpolation

namespace EilenbergGanea.CubeRealization

section
open CubeInterpolation
variable {G V : Type*} [Group G] [Fintype V]
variable (L : SimpleGraph V) (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

theorem vertexStar_open (b : G) : IsOpen (vertexStar L f comm b) :=
  isOpen_ne.preimage (interpolation_continuous L f comm _)

theorem mem_vertexStar_self (p : Point (G := G) L f comm) :
    p ∈ vertexStar L f comm p.base := (interpolation_vertex_pos L f comm p).ne'

theorem vertexStar_base {b : G} {p : Point (G := G) L f comm}
    (hp : p ∈ vertexStar L f comm b) :
    ∃ s : CliqueIndex L, p.base = b * (cliqueProduct L f comm s)⁻¹ := by
  obtain ⟨s,hs,he⟩ := operator_support f (active p) ((pointCell p).clique.imp
    (fun {_ _} h => comm _ _ h)) p.coord (fun a => if a = b then 1 else 0) p.base hp
  have hh : p.base * product f comm s ((pointCell p).clique.mono hs) = b := by
    by_contra h
    exact he (ite_eq_right h)
  exact ⟨⟨s,(pointCell p).clique.mono hs⟩,eq_mul_inv_of_mul_eq hh⟩

/-- Only finitely many initial vertices occur in an open vertex star. -/
theorem vertexStar_finite_bases (b : G) :
    (Point.base '' vertexStar L f comm b).Finite := by
  apply (Set.finite_range (fun s : CliqueIndex L => b * (cliqueProduct L f comm s)⁻¹)).subset
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨s,hs⟩ := vertexStar_base L f comm hp
  exact ⟨s,hs.symm⟩

/-- Every compact set in the actual realization has finitely many initial
vertices. The initial-vertex function itself need not be continuous. -/
theorem compact_finite_bases {K : Set (Point (G := G) L f comm)} (hK : IsCompact K) :
    (Point.base '' K).Finite := by
  have hcover : K ⊆ ⋃ b : G, vertexStar L f comm b := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p.base,mem_vertexStar_self L f comm p⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (vertexStar L f comm)
    (vertexStar_open L f comm) hcover
  apply (Set.Finite.biUnion s.finite_toSet (fun b _ => vertexStar_finite_bases L f comm b)).subset
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨b,hbs,hpb⟩ := by simpa only [Set.mem_iUnion] using hs hp
  exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨hbs,⟨p,hpb,rfl⟩⟩⟩

theorem vertexStar_compact_neighborhood (p : Point (G := G) L f comm) :
    ∃ K : Set (Point (G := G) L f comm), K ∈ 𝓝 p ∧ IsCompact K := by
  let C (st : CliqueIndex L × CliqueIndex L) : Cell (G := G) L :=
    cliqueCell L (p.base * (cliqueProduct L f comm st.1)⁻¹) st.2
  let K := ⋃ st, Set.range (characteristic f comm (C st))
  refine ⟨K,?_,?_⟩
  · apply Filter.mem_of_superset ((vertexStar_open L f comm p.base).mem_nhds
      (mem_vertexStar_self L f comm p))
    intro q hq
    obtain ⟨s,hs⟩ := vertexStar_base L f comm hq
    refine Set.mem_iUnion.mpr ⟨(s,⟨active q,(pointCell q).clique⟩),?_⟩
    have he : C (s,⟨active q,(pointCell q).clique⟩) = pointCell q := by
      apply Cell.ext
      · exact hs.symm
      · rfl
    rw [he]
    exact ⟨pointCoordinates q,characteristic_point f comm q⟩
  · apply isCompact_iUnion
    intro st
    exact isCompact_range (characteristic_continuous f comm (C st))

/-- Local compactness is proved from finite generator stars and the actual
closed-cube maps, not asserted as a cubical-model input. -/
theorem point_weaklyLocallyCompact : WeaklyLocallyCompactSpace (Point (G := G) L f comm) :=
  ⟨fun p => by
    obtain ⟨K,hK,hcompact⟩ := vertexStar_compact_neighborhood L f comm p
    exact ⟨K,hcompact,hK⟩⟩

end

variable {G V : Type*} [Group G] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))

instance pointProperlyDiscontinuousSMul :
    ProperlyDiscontinuousSMul G (Point (G := G) L f comm) where
  finite_disjoint_inter_image := by
    intro K D hK hD
    apply (((compact_finite_bases L f comm hD).prod
      (compact_finite_bases L f comm hK)).image (fun p : G × G => p.1 * p.2⁻¹)).subset
    intro g hg
    obtain ⟨q,⟨p,hp,hpq⟩,hq⟩ := hg
    refine ⟨(q.base,p.base),⟨⟨q,hq,rfl⟩,⟨p,hp,rfl⟩⟩,?_⟩
    have he : g * p.base = q.base := congrArg Point.base hpq
    change q.base * p.base⁻¹ = g
    rw [← he,mul_inv_cancel_right]

variable (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)
variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)

instance subgroupProperlyDiscontinuousSMul (H : Subgroup G) :
    ProperlyDiscontinuousSMul H (Point (G := G) L f comm) where
  finite_disjoint_inter_image := by
    intro K D hK hD
    exact Set.Finite.preimage (f := fun g : H => (g : G)) Subtype.val_injective.injOn
      (finite_disjoint_inter_image (Γ := G) hK hD)

include h hf exponent hexponent in
/-- The actual quotient by any subgroup is a covering map. No contractibility
or classifying-space identification is assumed in this theorem. -/
theorem subgroup_quotient_covering (H : Subgroup G) :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel H (Point (G := G) L f comm))) H := by
  let := point_t2 L f comm h hf exponent hexponent
  let := point_weaklyLocallyCompact L f comm
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

end EilenbergGanea.CubeRealization

end

end OAI
end

section
-- module Solutions.OAIEG.SeedConnection
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
namespace SeedConnection

theorem properFace_rank {a b : SeedCell} (h : properFace a b) : cellRank a < cellRank b := by
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp only [properFace,cellRank] at * <;> omega

theorem adjacent_rank_ne {a b : SeedCell} (h : seedGraph.Adj a b) : rankFin a ≠ rankFin b := by
  intro he
  have he' := congrArg Fin.val he
  change cellRank a = cellRank b at he'
  rcases h with h | h <;> have hh := properFace_rank h <;> omega

theorem clique_card_le_three (s : Finset SeedCell) (hs : (s : Set SeedCell).Pairwise seedGraph.Adj) :
    s.card ≤ 3 := by
  have hi : Set.InjOn rankFin (s : Set SeedCell) := by
    intro a ha b hb he
    by_contra hn
    exact adjacent_rank_ne (hs ha hb hn) he
  have hc := Finset.card_le_card (Finset.subset_univ (s.image rankFin))
  rwa [Finset.card_image_of_injOn hi,Finset.card_univ,Fintype.card_fin] at hc

end SeedConnection



end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.CubicalCover
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible _root_.OAI.EilenbergGanea.SeedEncoding.properFaceDecidable _root_.OAI.EilenbergGanea.SeedEncoding.seedAdjDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology
open scoped Quaternion

open Classical Topology

namespace EilenbergGanea.ArtinCubicalTopology
open TraceWords CubeInterpolation CubicalChains.Reorientation
variable {V : Type*} [Fintype V] (L : SimpleGraph V)

variable [Nonempty V]

/-- The ordinary positive-cube CW realization is genuinely contractible. -/
theorem positive_contractible : ContractibleSpace (Positive L) := by
  let : ContractibleSpace (Descending L) := artinDescending_contractible L
  exact (reorient L).symm.contractibleSpace

end EilenbergGanea.ArtinCubicalTopology

open Classical Set Topology

namespace EilenbergGanea.CubeRealization

variable {G Q V : Type*} [Group G] [Group Q] [Fintype V]
variable {L : SimpleGraph V} (f : V → G)
variable (comm : ∀ v w, L.Adj v w → Commute (f v) (f w))
variable (q : G →* Q)

variable (h : G →* Multiplicative ℤ) (hf : ∀ v, (h (f v)).toAdd = 1)
variable (exponent : V → G →* Multiplicative ℝ)
variable (hexponent : ∀ v w, (exponent v (f w)).toAdd = if v = w then 1 else 0)

include h hf exponent hexponent in
theorem quotientPoint_t2 (hq : Function.Surjective q) :
    T2Space (Point (G := Q) L (q ∘ f) (mappedComm f comm q)) := by
  let := point_t2 L f comm h hf exponent hexponent
  let := point_weaklyLocallyCompact L f comm
  exact (kernelQuotientHomeomorph f comm q hq).t2Space

include h hf exponent hexponent in
theorem mapPoint_covering (hq : Function.Surjective q) :
    IsQuotientCoveringMap (mapPoint f comm q) q.ker where
  toIsQuotientMap := mapPoint_quotient f comm q hq
  continuous_const_smul := continuous_const_smul
  apply_eq_iff_mem_orbit := mapPoint_eq_iff_orbit f comm q _ _
  disjoint := (subgroup_quotient_covering f comm h hf exponent hexponent q.ker).disjoint

end EilenbergGanea.CubeRealization

namespace EilenbergGanea
universe u
namespace ArtinCubicalTopology
open CubeRealization
variable {V : Type u} [Fintype V] [Nonempty V] (L : SimpleGraph V)

omit [Fintype V] in
theorem height_surjective : Function.Surjective (height L) := by
  intro n
  let v : V := Classical.choice inferInstance
  refine ⟨f L v ^ n.toAdd,?_⟩
  rw [map_zpow]
  apply Multiplicative.toAdd.injective
  change n.toAdd • (height L (f L v)).toAdd = n.toAdd
  simp only [height_generator,zsmul_eq_mul,mul_one,Int.cast_id]

/-- An ordinary cubical classifying space for the height kernel, with one cube
for every integral level and clique. Contractibility above is the explicit
word-length contraction, and the fundamental-group identification reuses
Mathlib's checked covering-monodromy equivalence. -/
theorem height_hasClassifyingSpace (d : ℕ)
    (hd : ∀ s : Finset V, (s : Set V).Pairwise L.Adj → s.card ≤ d) :
    HasClassifyingSpace.{u} (height L).ker d := by
  let X := Point L ((height L) ∘ f L) (mappedComm (f L) (comm L) (height L))
  let E := Positive L
  let : ContractibleSpace E := positive_contractible L
  let : T2Space X := quotientPoint_t2 (f L) (comm L) (height L)
    (height L) (height_generator L) (exponent L) (exponent_generator L) (height_surjective L)
  let : Topology.CWComplex (Set.univ : Set X) :=
    cwComplexOfT2 ((height L) ∘ f L) (mappedComm (f L) (comm L) (height L))
  let p : E → X := mapPoint (f L) (comm L) (height L)
  have hp : IsQuotientCoveringMap p (height L).ker :=
    mapPoint_covering (f L) (comm L) (height L) (height L) (height_generator L)
      (exponent L) (exponent_generator L) (height_surjective L)
  have hs : Function.Surjective p := mapPoint_surjective (f L) (comm L) (height L) (height_surjective L)
  let : PathConnectedSpace X := hs.pathConnectedSpace hp.continuous
  let e : E := Classical.choice (inferInstance : Nonempty E)
  refine ⟨X,inferInstance,inferInstance,inferInstance,?_,inferInstance,p e,?_,
    E,inferInstance,inferInstance,p,hp.isCoveringMap,hs⟩
  · intro k hk
    exact ⟨fun c => Nat.not_lt_of_ge ((c.property.symm ▸ hd c.val.directions c.val.clique)) hk⟩
  · exact ⟨(hp.fundamentalGroupEquiv ⟨e,rfl⟩).trans (MulEquiv.inv' ((height L).ker)).symm⟩

end ArtinCubicalTopology

/-- The fixed source group has an ordinary three-dimensional classifying CW
space, with an actually contractible surjective covering. -/
theorem source_hasClassifyingSpace_three_oai : HasClassifyingSpace.{0} SourceGroup 3 :=
  ArtinCubicalTopology.height_hasClassifyingSpace seedGraph 3 SeedConnection.clique_card_le_three
end EilenbergGanea

end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.source_hasClassifyingSpace_three_oai := @OAI.EilenbergGanea.source_hasClassifyingSpace_three_oai
