-- Prove2me | solution 1 for OAI.FiniteCircle.mask_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:31:21.678593+00:00
-- url     : https://prove2.me/submissions/df6bc745-6cc5-486c-9991-160f5b4b6f48

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/MaskSeparation.lean:L240-L330
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.mask_separation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Theorems.Thm_OAI_FiniteCircle_get_flatMap_uniform
import Theorems.Thm_OAI_FiniteCircle_halfCircle_separation
import Theorems.Thm_OAI_FiniteCircle_lcs_taggedRow_le
import Theorems.Thm_OAI_FiniteCircle_nodup_maskTags
import Theorems.Thm_OAI_FiniteCircle_row_separation
import Theorems.Thm_OAI_FiniteCircle_segment_flatMap_uniform

-- ---- from OAI.Combinatorics.FiniteCircle.TaggedRows ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem filter_map_tag {J β : Type*} [DecidableEq J] (j k : J) (x : List β) :
    ((x.map (fun b => (k,b))).filter (fun z => decide (z.1 = j))) =
      if k = j then x.map (fun b => (j,b)) else [] := by
  by_cases h : k = j
  · subst k
    simp [List.filter_map, Function.comp_def]
  · simp [List.filter_map, Function.comp_def, h]

theorem filter_taggedRow {J β : Type*} [DecidableEq J] (js : List J)
    (hn : js.Nodup) (W : J → List β) (j : J) :
    ((taggedRow js W).filter (fun z => decide (z.1 = j))) =
      if j ∈ js then (W j).map (fun b => (j,b)) else [] := by
  induction js with
  | nil => simp
  | cons k js ih =>
    have hn' := List.nodup_cons.mp hn
    rw [taggedRow_cons, List.filter_append, filter_map_tag, ih hn'.2]
    by_cases h : k = j
    · subst k
      simp [hn'.1]
    · by_cases hj : j ∈ js <;> simp [h, hj, Ne.symm h]

theorem sum_filter_tag_length {J β : Type*} [Fintype J] [DecidableEq J]
    (x : List (J × β)) :
    ∑ j : J, (x.filter (fun z => decide (z.1 = j))).length = x.length := by
  induction x with
  | nil => simp
  | cons a x ih =>
    have he (j : J) : ((a::x).filter (fun z => decide (z.1 = j))).length =
        (if a.1 = j then 1 else 0) + (x.filter (fun z => decide (z.1 = j))).length := by
      by_cases h : a.1 = j <;> simp [h, Nat.add_comm]
    simp_rw [he]
    rw [Finset.sum_add_distrib, ih]
    simp [Nat.add_comm]

theorem length_taggedRow {J β : Type*} [Fintype J] [DecidableEq J]
    (js : List J) (hn : js.Nodup) (hall : ∀ j, j ∈ js) (W : J → List β) :
    (taggedRow js W).length = ∑ j : J, (W j).length := by
  rw [← sum_filter_tag_length (taggedRow js W)]
  congr 1
  funext j
  rw [filter_taggedRow js hn W j, ite_eq_left (hall j), List.length_map]

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

end WordMatching

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

end WordMatching

theorem tag_get_taggedRow {J β : Type*} [DecidableEq J] (js : List J) (hn : js.Nodup)
    (W : J → List β) {L : ℕ} (hL : 0 < L) (hl : ∀ j ∈ js, (W j).length = L)
    (k : Fin (taggedRow js W).length) :
    js.idxOf ((taggedRow js W).get k).1 = k.val/L := by
  obtain ⟨i,b,hi,_,he⟩ := get_flatMap_uniform js (fun j => (W j).map (fun z => (j,z))) hL
    (fun j hj => by simp [hl j hj]) k
  change (taggedRow js W).get k = _ at he
  rw [he]
  simp only [List.get_eq_getElem, List.getElem_map]
  rw [hn.idxOf_getElem]
  exact hi

theorem tag_get_rows {J β : Type*} [DecidableEq J] (js : List J) (hn : js.Nodup)
    (W : ℕ → J → List β) {L N : ℕ} (hL : 0 < L) (ht : 0 < js.length)
    (hl : ∀ a < N, ∀ j ∈ js, (W a j).length = L)
    (k : Fin ((List.range N).flatMap (fun a => taggedRow js (W a))).length) :
    js.idxOf (((List.range N).flatMap (fun a => taggedRow js (W a))).get k).1 =
      (k.val/L)%js.length := by
  have hr (a : ℕ) (ha : a ∈ List.range N) : (taggedRow js (W a)).length = js.length*L := by
    apply length_flatMap_uniform
    intro j hj
    simp [hl a (List.mem_range.mp ha) j hj]
  obtain ⟨i,b,_,hb,he⟩ := get_flatMap_uniform (List.range N) (fun a => taggedRow js (W a))
    (Nat.mul_pos ht hL) hr k
  rw [he, tag_get_taggedRow js hn _ hL (hl _ (by simpa using i.isLt)), hb]
  rw [Nat.mul_comm js.length L, Nat.mod_mul_right_div_self]

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.PhaseCost ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem circleCost_le_half {M : ℕ} [NeZero M] (x : ZMod M) : circleCost x ≤ 1/2 := by
  have hM : 0 < M := NeZero.pos M
  have h := ZMod.natAbs_valMinAbs_le x
  have h' : 2*x.valMinAbs.natAbs ≤ M := by omega
  unfold circleCost
  rw [div_le_iff₀ (by exact_mod_cast hM)]
  have hh : 2*(x.valMinAbs.natAbs : ℝ) ≤ M := by exact_mod_cast h'
  linarith

namespace PhaseCost
variable {G H J : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype H] [Fintype J]

theorem infAverage_le_self [Nonempty J] (f : PhaseCost G) (σ : H →+ (J → G)) (x : G) :
    f.infAverage σ x ≤ f x := by
  simpa using f.infAverage_le σ x 0

end PhaseCost

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem shiftMaskState_add (h : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (v : MaskState h p M l) (a b : ZMod M) :
    shiftMaskState h p M l (shiftMaskState h p M l v a) b =
      shiftMaskState h p M l v (a+b) := by
  induction l with
  | zero => change ZMod M at v; exact add_assoc v a b
  | succ l ih => funext j; exact ih (v j)

theorem segment_maskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M (l+1)) (a : Fin (R*period h p (l+1))) :
    segment (maskWord h p R M (l+1) v)
        (a.val*((maskTags h p (l+1)).length*maskLength h p R M l))
        ((maskTags h p (l+1)).length*maskLength h p R M l) = maskRow h p R M l v a := by
  have he := segment_flatMap_uniform (List.range (R*period h p (l+1)))
    (maskRow h p R M l v) _ (fun a _ => length_maskRow h p R M l v a)
    ⟨a.val, by simp⟩
  change segment ((List.range (R*period h p (l+1))).flatMap (maskRow h p R M l v)) _ _ = _
  simpa only [List.get_eq_getElem, List.getElem_range] using he

theorem tag_get_maskWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : MaskState h p M (l+1)) (hL : 0 < maskLength h p R M l)
    (ht : 0 < (maskTags h p (l+1)).length)
    (k : Fin (maskWord h p R M (l+1) v).length) :
    (maskTags h p (l+1)).idxOf ((maskWord h p R M (l+1) v).get k).1 =
      (k.val/maskLength h p R M l)%(maskTags h p (l+1)).length := by
  classical
  exact tag_get_rows _ (nodup_maskTags h p (l+1)) _ hL ht
    (fun _ _ _ _ => length_maskWord ..) k

 theorem maskWord_zero_eq {h M R : ℕ} {p : ℕ → ℕ → ℕ} (v : ZMod M) :
    maskWord h p R M 0 v = List.ofFn (fun i : Fin M => halfBit v (i.val : ZMod M)) := by
  have he := maskWord.eq_1 h p R M v
  dsimp only [MaskState, MaskAlphabet] at he
  refine he.trans ?_
  simp only [List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap, List.map_map]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [Function.comp_def, halfBit]

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.MaskSeparation ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem maskPhaseHom_natCast (h : ℕ) (p : ℕ → ℕ → ℕ) (M l a : ℕ)
    (hd : ∀ k : Fin h, p l k ∣ M) (hn : ∀ k : Fin h, 0 < p l k) :
    maskPhaseHom h p M l hd (fun k => (a : ZMod (p l k))) = maskGamma h p M l a := by
  funext j
  change (∑ k, subcircle (hd k) (a : ZMod (p l k))) +
    j.2.val • subcircle (hd j.1) (a : ZMod (p l j.1)) = _
  have he (k : Fin h) : subcircle (hd k) (a : ZMod (p l k)) =
    ((M/p l k*(a%p l k) : ℕ) : ZMod M) := by
    let : NeZero (p l k) := ⟨(hn k).ne'⟩
    rw [subcircle_val, ZMod.val_natCast]
  simp_rw [he]
  simp only [maskGamma, nsmul_eq_mul, Nat.cast_mul]
  ring

 theorem maskCost_le_half {h M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hh : 0 < h) (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (l : ℕ) (x : ZMod M) : maskCost h p M hd hn l x ≤ 1/2 := by
  induction l with
  | zero => exact circleCost_le_half x
  | succ l ih =>
    let : ∀ k : Fin h, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    let : Nonempty (MaskTag h p (l+1)) := ⟨⟨⟨0,hh⟩,⟨0,hn _ ⟨0,hh⟩⟩⟩⟩
    exact ((maskCost h p M hd hn l).infAverage_le_self _ x).trans ih

 theorem card_maskTag (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    Fintype.card (MaskTag h p l) = ∑ k : Fin h, p l k := by
  simp only [MaskTag, Fintype.card_sigma, Fintype.card_fin]

 theorem deficit_cast {β : Type*} (x y : List β) : (deficit x y : ℝ) = (x.length:ℝ) - lcs x y := by
  exact Nat.cast_sub (lcs_le_length_left x y)

 theorem deficit_taggedRow_lower {J β : Type*} [Fintype J] [DecidableEq J]
    (js : List J) (hn : js.Nodup) (hall : ∀ j, j ∈ js) (W U : J → List β) :
    (∑ j : J, (deficit (W j) (U j) : ℝ)) ≤
      deficit (taggedRow js W) (taggedRow js U) := by
  have hc := lcs_taggedRow_le js hn hall W U
  have hcr : (lcs (taggedRow js W) (taggedRow js U) : ℝ) ≤ ∑ j : J, (lcs (W j) (U j) : ℝ) := by exact_mod_cast hc
  simp_rw [deficit_cast]
  rw [Finset.sum_sub_distrib, length_taggedRow js hn hall W, Nat.cast_sum]
  linarith

 theorem maskLength_pos {h M R : ℕ} {p : ℕ → ℕ → ℕ}
    (hh : 0 < h) (hM : 0 < M) (hR : 0 < R) (hn : ∀ l (k : Fin h), 0 < p l k)
    (l : ℕ) : 0 < maskLength h p R M l := by
  induction l with
  | zero => exact hM
  | succ l ih =>
    unfold maskLength
    apply Nat.mul_pos (Nat.mul_pos hR (Finset.prod_pos (fun k _ => hn _ k)))
    apply Nat.mul_pos _ ih
    rw [length_maskTags]
    exact Finset.sum_pos (fun k _ => hn _ k) (Finset.univ_nonempty_iff.mpr ⟨⟨0,hh⟩⟩)

theorem mask_separation {h M R : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (he : M = 2*(M/2)) (hh : 0 < h) (hR : 0 < R)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (ht : ∀ l, 4 ≤ (maskTags h p l).length)
    (l : ℕ) (v : MaskState h p M l) (θ : ZMod M) :
    (1/((2:ℝ)^l*4))*(maskLength h p R M l)*maskCost h p M hd hn l θ ≤
      (deficit (maskWord h p R M l v)
        (maskWord h p R M l (shiftMaskState h p M l v θ)) : ℝ) := by
  classical
  induction l generalizing θ with
  | zero =>
    change ZMod M at v
    change (1/((2:ℝ)^0*4))*M*circleCost θ ≤
      (deficit (maskWord h p R M 0 v) (maskWord h p R M 0 (v+θ)) : ℝ)
    rw [maskWord_zero_eq, maskWord_zero_eq]
    calc
      _ = (M:ℝ)*circleCost θ/4 := by norm_num; ring
      _ ≤ _ := halfCircle_separation he v θ
  | succ l ih =>
    let : ∀ k : Fin h, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    let L := maskLength h p R M l
    let t := (maskTags h p (l+1)).length
    let N := R*period h p (l+1)
    let f := maskCost h p M hd hn l
    let σ := maskPhaseHom h p M (l+1) (hd _)
    let ρ := (1/((2:ℝ)^l*4))*maskCost h p M hd hn (l+1) θ
    have hL : 0 < L := maskLength_pos hh (NeZero.pos M) hR hn l
    have hp2 : 1 ≤ (2:ℝ)^l := one_le_pow₀ (by norm_num)
    have hρ : ρ ≤ 1/2 := by
      have hc := maskCost_le_half hh hd hn (l+1) θ
      have hc0 := (maskCost h p M hd hn (l+1)).nonneg θ
      dsimp [ρ]
      have hi : 1/((2:ℝ)^l*4) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
      calc
        _ ≤ 1*maskCost h p M hd hn (l+1) θ := mul_le_mul_of_nonneg_right hi hc0
        _ ≤ _ := by simpa using hc
    have hx : (maskWord h p R M (l+1) v).length = (t*L)*N := by
      rw [length_maskWord]
      change N*(t*L) = (t*L)*N
      exact Nat.mul_comm _ _
    have hy : (maskWord h p R M (l+1) (shiftMaskState h p M (l+1) v θ)).length = (t*L)*N := by
      rw [length_maskWord]
      change N*(t*L) = (t*L)*N
      exact Nat.mul_comm _ _
    have hr := row_separation hL (ht (l+1)) hx hy
      (fun x => (maskTags h p (l+1)).idxOf x.1)
      (tag_get_maskWord h p R M l v hL (by have := ht (l+1); omega))
      (tag_get_maskWord h p R M l _ hL (by have := ht (l+1); omega)) ρ hρ
    have hrows : ∀ i j : Fin N, ρ*(t*L) ≤
        (deficit (segment (maskWord h p R M (l+1) v) (i.val*(t*L)) (t*L))
          (segment (maskWord h p R M (l+1) (shiftMaskState h p M (l+1) v θ))
            (j.val*(t*L)) (t*L)) : ℝ) := by
      intro a b
      rw [segment_maskWord, segment_maskWord]
      let z : MaskResidues h p (l+1) := fun k => (b.val : ZMod (p (l+1) k)) - (a.val : ZMod (p (l+1) k))
      have hz (j : MaskTag h p (l+1)) : σ z j =
          maskGamma h p M (l+1) b j - maskGamma h p M (l+1) a j := by
        change σ ((fun k : Fin h => (b.val : ZMod (p (l+1) k))) - (fun k : Fin h => (a.val : ZMod (p (l+1) k)))) j = _
        rw [map_sub, Pi.sub_apply]
        exact congrArg₂ (·-·) (congrFun (maskPhaseHom_natCast h p M (l+1) b (hd _) (hn _)) j)
          (congrFun (maskPhaseHom_natCast h p M (l+1) a (hd _) (hn _)) j)
      have hind (j : MaskTag h p (l+1)) := ih
        (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)) (θ+σ z j)
      have hstate (j : MaskTag h p (l+1)) :
          shiftMaskState h p M l (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)) (θ+σ z j) =
          shiftMaskState h p M l (shiftMaskState h p M l (v j) θ) (maskGamma h p M (l+1) b j) := by
        rw [shiftMaskState_add, shiftMaskState_add, hz]
        congr 1
        abel
      simp_rw [hstate] at hind
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hind j)
      have hdef := deficit_taggedRow_lower (maskTags h p (l+1)) (nodup_maskTags ..)
        (mem_maskTags h p (l+1))
        (fun j => maskWord h p R M l (shiftMaskState h p M l (v j) (maskGamma h p M (l+1) a j)))
        (fun j => maskWord h p R M l (shiftMaskState h p M l (shiftMaskState h p M l (v j) θ) (maskGamma h p M (l+1) b j)))
      apply le_trans _ (hsum.trans hdef)
      rw [← Finset.mul_sum]
      have hcost : maskCost h p M hd hn (l+1) θ ≤ f.average σ θ z := f.infAverage_le σ θ z
      have htpos : (0:ℝ) < t := by exact_mod_cast (show 0 < t by have := ht (l+1); omega)
      have hcard : (Fintype.card (MaskTag h p (l+1)) : ℝ) = t := by rw [card_maskTag]; exact_mod_cast (length_maskTags h p (l+1)).symm
      rw [PhaseCost.average, hcard, le_div_iff₀ htpos] at hcost
      dsimp only [ρ]
      calc
        _ = ((1/((2:ℝ)^l*4))*(L:ℝ)) * ((maskCost h p M hd hn (l+1) θ)*t) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcost (by positivity)
    have hfinal := hr hrows
    rw [length_maskWord] at hfinal
    dsimp only [ρ] at hfinal
    calc
      _ = ((1/((2:ℝ)^l*4))*maskCost h p M hd hn (l+1) θ)/2 * maskLength h p R M (l+1) := by rw [pow_succ]; ring
      _ ≤ _ := hfinal

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.mask_separation := @_root_.OAI.FiniteCircle.mask_separation
