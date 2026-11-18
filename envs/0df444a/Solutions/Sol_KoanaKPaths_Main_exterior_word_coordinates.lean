-- Prove2me | solution 1 for KoanaKPaths.Main.exterior_word_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:19:15.165347+00:00
-- url     : https://prove2.me/submissions/9f9c0576-a523-4add-afc5-843eddc3456b

import Definitions.Def_KoanaKPaths_ExteriorCoordinates

lemma KoanaKPaths.ExteriorCoordinates.det_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i j, |A i j| ≤ 1) : |A.det| ≤ (n.factorial : ℤ) := by
  have hb := Matrix.det_le (abv := (AbsoluteValue.abs : AbsoluteValue ℤ ℤ)) h
  simpa only [AbsoluteValue.abs_apply,Fintype.card_fin,one_pow,nsmul_eq_mul,mul_one] using hb

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical
namespace KoanaKPaths.ExteriorCoordinates

lemma erase_enum {k d : ℕ} (S : Finset (Fin k)) (hs : S.card = d+1) (j : Fin (d+1)) :
    ∀ t : Fin d,
      (S.erase (S.orderEmbOfFin hs j)).orderEmbOfFin
        (by rw [Finset.card_erase_of_mem (S.orderEmbOfFin_mem hs j),hs]; omega) t =
        S.orderEmbOfFin hs (j.succAbove t) := by
  have hcard : (S.erase (S.orderEmbOfFin hs j)).card = d := by
    rw [Finset.card_erase_of_mem (S.orderEmbOfFin_mem hs j),hs]
    omega
  have h := Finset.orderEmbOfFin_unique hcard
    (f := fun t : Fin d => S.orderEmbOfFin hs (j.succAbove t))
    (fun t => Finset.mem_erase.mpr ⟨(S.orderEmbOfFin hs).injective.ne (Fin.succAbove_ne j t),
      S.orderEmbOfFin_mem hs _⟩)
    ((S.orderEmbOfFin hs).strictMono.comp (Fin.strictMono_succAbove j))
  intro t
  exact (congrFun h t).symm

lemma wedge_sum {k d : ℕ} (S : Finset (Fin k)) (hs : S.card = d)
    (A : Coordinates k) (v : Fin k → ℤ) :
    wedgeRight A v S = ∑ j : Fin d, (-1 : ℤ)^(d-1+j.val) *
      A (S.erase (S.orderEmbOfFin hs j)) * v (S.orderEmbOfFin hs j) := by
  have hrank (j : Fin d) : S.sort.idxOf (S.orderEmbOfFin hs j) = j.val := by
    have h := congrArg Fin.val ((S.orderIsoOfFin hs).symm_apply_apply j)
    exact h
  unfold wedgeRight
  have h := (S.orderIsoOfFin hs).toEquiv.sum_comp
    (fun r : S => (-1 : ℤ)^(S.card-1+S.sort.idxOf r.val) * A (S.erase r.val) * v r.val)
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  change (-1 : ℤ)^(S.card-1+S.sort.idxOf (S.orderEmbOfFin hs j)) *
      A (S.erase (S.orderEmbOfFin hs j)) * v (S.orderEmbOfFin hs j) = _
  rw [hrank,hs]

/-- Semantics of a vector word in a fixed homogeneous coordinate. -/
def minorWord {k : ℕ} (vs : List (Fin k → ℤ)) (S : Finset (Fin k)) : ℤ :=
  if hs : S.card = vs.length then
    Matrix.det (Matrix.of (fun r c : Fin vs.length =>
      (vs.getD c.val (fun _ => 0)) (S.orderEmbOfFin hs r)))
  else 0

lemma minorWord_unit (k : ℕ) : minorWord ([] : List (Fin k → ℤ)) = unit k := by
  funext S
  by_cases hs : S = ∅
  · subst S
    simp [minorWord,unit]
  · have hcard : S.card ≠ 0 := by simpa using hs
    simp [minorWord,unit,hs,hcard]


lemma det_enum_cast {k d e : ℕ} (S : Finset (Fin k)) (h : d = e)
    (hs : S.card = d) (f : ℕ → Fin k → ℤ) :
    Matrix.det (Matrix.of fun r c : Fin d => f c.val (S.orderEmbOfFin hs r)) =
    Matrix.det (Matrix.of fun r c : Fin e => f c.val (S.orderEmbOfFin (hs.trans h) r)) := by
  subst e
  rfl

lemma minorWord_append {k : ℕ} (vs : List (Fin k → ℤ)) (v : Fin k → ℤ) :
    minorWord (vs++[v]) = wedgeRight (minorWord vs) v := by
  funext S
  by_cases hs : S.card = vs.length+1
  · let A : Matrix (Fin (vs.length+1)) (Fin (vs.length+1)) ℤ := Matrix.of
      (fun r c => ((vs++[v]).getD c.val (fun _ => 0)) (S.orderEmbOfFin hs r))
    have hleft : minorWord (vs++[v]) S = A.det := by
      have hlen : (vs++[v]).length = vs.length+1 := by simp only [List.length_append,List.length_singleton]
      rw [minorWord,dif_pos (hs.trans hlen.symm)]
      exact det_enum_cast S hlen (hs.trans hlen.symm) (fun c => (vs++[v]).getD c (fun _ => 0))
    rw [hleft,wedge_sum S hs,Matrix.det_succ_column A (Fin.last vs.length)]
    apply Finset.sum_congr rfl
    intro j _
    have hecard : (S.erase (S.orderEmbOfFin hs j)).card = vs.length := by
      rw [Finset.card_erase_of_mem (S.orderEmbOfFin_mem hs j),hs]
      omega
    have hm : (A.submatrix j.succAbove (Fin.last vs.length).succAbove).det =
        minorWord vs (S.erase (S.orderEmbOfFin hs j)) := by
      rw [minorWord,dif_pos hecard]
      congr 1
      funext r c
      simp only [A,Matrix.submatrix_apply,Matrix.of_apply,Fin.succAbove_last_apply,Fin.val_castSucc]
      rw [List.getD_append _ _ _ _ c.isLt,erase_enum S hs j r]
    have hl : A j (Fin.last vs.length) = v (S.orderEmbOfFin hs j) := by
      simp only [A,Matrix.of_apply,Fin.val_last]
      rw [List.getD_append_right _ _ _ _ le_rfl]
      simp
    rw [hm,hl]
    simp only [Fin.val_last,Nat.add_sub_cancel]
    rw [Nat.add_comm j.val vs.length]
    ring
  · have hleft : minorWord (vs++[v]) S = 0 := by
      simp [minorWord,List.length_append,hs]
    rw [hleft]
    symm
    unfold wedgeRight
    apply Finset.sum_eq_zero
    intro r _
    have hp : 0 < S.card := Finset.card_pos.mpr ⟨r.val,r.property⟩
    have hecard : (S.erase r.val).card = S.card-1 := Finset.card_erase_of_mem r.property
    have hne : (S.erase r.val).card ≠ vs.length := by
      intro he
      apply hs
      omega
    have hz : minorWord vs (S.erase r.val) = 0 := by
      unfold minorWord
      exact dif_neg hne
    rw [hz,mul_zero,zero_mul]

lemma wordCoordinates_eq_minorWord {k : ℕ} (vs : List (Fin k → ℤ)) :
    wordCoordinates vs = minorWord vs := by
  induction vs using List.reverseRecOn with
  | nil => exact (minorWord_unit k).symm
  | append_singleton vs v ih =>
    rw [wordCoordinates,List.foldl_append]
    change wedgeRight (wordCoordinates vs) v = _
    rw [ih,minorWord_append]

lemma univ_enum {k : ℕ} (h : (Finset.univ : Finset (Fin k)).card = k) (r : Fin k) :
    (Finset.univ : Finset (Fin k)).orderEmbOfFin h r = r := by
  have he := Finset.orderEmbOfFin_unique h (f := id)
    (fun _ => Finset.mem_univ _) (strictMono_id)
  exact (congrFun he r).symm

theorem top_coordinate {k : ℕ} (vs : Fin k → Fin k → ℤ) :
    wordCoordinates (List.ofFn vs) Finset.univ =
      Matrix.det (Matrix.of fun r c : Fin k => vs c r) := by
  have hlen : (List.ofFn vs).length = k := List.length_ofFn
  have hs : (Finset.univ : Finset (Fin k)).card = (List.ofFn vs).length := by simp
  rw [wordCoordinates_eq_minorWord,minorWord,dif_pos hs]
  rw [det_enum_cast Finset.univ hlen hs (fun c => (List.ofFn vs).getD c (fun _ => 0))]
  congr 1
  funext r c
  simp only [Matrix.of_apply,univ_enum]
  simp [List.getD_eq_getElem?_getD,c.isLt]

lemma wedgeRight_zero {k : ℕ} (v : Fin k → ℤ) : wedgeRight (0 : Coordinates k) v = 0 := by
  funext S
  simp [wedgeRight]

lemma wedgeRight_add {k : ℕ} (A B : Coordinates k) (v : Fin k → ℤ) :
    wedgeRight (A+B) v = wedgeRight A v + wedgeRight B v := by
  funext S
  simp only [wedgeRight,Pi.add_apply]
  simp_rw [mul_add,add_mul]
  exact Finset.sum_add_distrib

lemma wedgeRight_smul {k : ℕ} (z : ℤ) (A : Coordinates k) (v : Fin k → ℤ) :
    wedgeRight (z • A) v = z • wedgeRight A v := by
  funext S
  simp only [wedgeRight,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma wedgeRight_sum {k : ℕ} {α : Type} (s : Finset α) (A : α → Coordinates k)
    (v : Fin k → ℤ) :
    wedgeRight (∑ a ∈ s, A a) v = ∑ a ∈ s, wedgeRight (A a) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wedgeRight_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,wedgeRight_add,ih]

theorem coordinates_card (k : ℕ) : Fintype.card (Finset (Fin k)) = 2^k := by simp

set_option backward.isDefEq.respectTransparency true in
theorem word_coordinate_abs_bound {k : ℕ} (vs : List (Fin k → ℤ))
    (hv : ∀ v ∈ vs, ∀ r, |v r| ≤ 1) (S : Finset (Fin k)) :
    |wordCoordinates vs S| ≤ (vs.length.factorial : ℤ) := by
  rw [wordCoordinates_eq_minorWord,minorWord]
  split_ifs with hs
  · have hm (r c : Fin vs.length) :
        |(vs.getD c.val (fun _ => 0)) (S.orderEmbOfFin hs r)| ≤ 1 := by
      apply hv _ _ _
      have hget : vs.getD c.val (fun _ => 0) = vs[c.val] := by
        simp [List.getD_eq_getElem?_getD,c.isLt]
      rw [hget]
      exact List.getElem_mem c.isLt
    exact det_bound _ hm
  · simp

theorem word_coordinate_homogeneous {k : ℕ} (vs : List (Fin k → ℤ))
    (S : Finset (Fin k)) (h : S.card ≠ vs.length) : wordCoordinates vs S = 0 := by
  rw [wordCoordinates_eq_minorWord,minorWord,dif_neg h]

end KoanaKPaths.ExteriorCoordinates

theorem solution (k : ℕ) (vs : List (Fin k → ℤ))
    (S : Finset (Fin k)) :
    (KoanaKPaths.ExteriorCoordinates.wordCoordinates vs S =
      if hs : S.card = vs.length then
        Matrix.det (Matrix.of (fun r c : Fin vs.length =>
          (vs.getD c.val (fun _ => 0)) (S.orderEmbOfFin hs r)))
      else 0) ∧
    ((∀ v ∈ vs, ∀ r, |v r| ≤ 1) →
      |KoanaKPaths.ExteriorCoordinates.wordCoordinates vs S| ≤ (vs.length.factorial : ℤ)) := by
  constructor
  · exact congrFun (KoanaKPaths.ExteriorCoordinates.wordCoordinates_eq_minorWord vs) S
  · exact fun hv => KoanaKPaths.ExteriorCoordinates.word_coordinate_abs_bound vs hv S
