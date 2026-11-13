-- Prove2me | solution 1 for OAI.Saxl.Balance.WordPacking.threeRows
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:08:05.403511+00:00
-- url     : https://prove2.me/submissions/ba21933d-9f49-4e6e-81e2-383986e7b721

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_ThreeRow_generator_support
import Theorems.Thm_OAI_Saxl_ThreeRow_sixSquare_columns

section
-- module Solutions.OAIQ259_US.Saxl_CyclicSector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

theorem cyclic_projection_support {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ} [Group G] [Finite G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (v : X)
    (f : Representation.IntertwiningMap τ (cyclic σ (F v)).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap τ (cyclic ρ v).toRepresentation, g ≠ 0 := by
  obtain ⟨g,hg⟩ := intertwining_lift_surjective (cyclicMap F v) (cyclicMap_surjective F v) f
  refine ⟨g, ?_⟩
  intro hz
  apply hf
  rw [← hg,hz]
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact map_zero (cyclicMap F v)



lemma cyclic_smul_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (c : ℂ) (hc : c ≠ 0) :
    cyclic ρ (c • v) = cyclic ρ v := by
  apply le_antisymm
  · apply (cyclic_le _ _ _).mpr
    exact Submodule.smul_mem _ _ (mem_cyclic ρ v)
  · apply (cyclic_le _ _ _).mpr
    have hh := Submodule.smul_mem (cyclic ρ (c • v)).toSubmodule c⁻¹ (mem_cyclic ρ (c • v))
    change v ∈ (cyclic ρ (c • v)).toSubmodule
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_HorizontalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl


lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

lemma row_lt_some_height {rs : List ℕ} (c : Cells rs) :
    ∃ h ∈ rs, row c < h := by
  induction rs with
  | nil => exact isEmptyElim c
  | cons h rs ih =>
    rcases c with c | c
    · exact ⟨h,by simp,c.isLt⟩
    · obtain ⟨h,hh,hc⟩ := ih c
      exact ⟨h,List.mem_cons_of_mem _ hh,hc⟩

lemma placed_height {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (B : ℕ) (hB : ∀ h ∈ rs, h ≤ B) :
    μ.colLen 0 ≤ B := by
  by_contra hh
  let x : μ.cells := ⟨(B,0),YoungDiagram.mem_iff_lt_colLen.mpr (by omega)⟩
  obtain ⟨h,hh,hc⟩ := row_lt_some_height (e.symm x)
  have ha := hr (e.symm x)
  rw [Equiv.apply_symm_apply] at ha
  change B = row (e.symm x) at ha
  have hb := hB h hh
  omega

lemma columnShape_height (rs : List ℕ) (B : ℕ) (hB : ∀ h ∈ rs, h ≤ B) :
    (columnShape rs).colLen 0 ≤ B := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_height e hr B hB

lemma sum_fin_val_ite (r i : ℕ) :
    (∑ j : Fin r, if j.val = i then (1:ℕ) else 0) = if i < r then 1 else 0 := by
  classical
  by_cases hi : i < r
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin r)]
    · simp
    · intro j hj hji
      exact ite_eq_right (fun h => hji (Fin.ext h))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h : (j : ℕ) = i => hi (h ▸ j.isLt))

lemma cells_row_count (rs : List ℕ) (i : ℕ) :
    (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) = rs.countP (fun h => i < h) := by
  classical
  induction rs with
  | nil => simp [Cells]
  | cons h rs ih =>
    rw [show (∑ c : Cells (h :: rs), if row c = i then (1:ℕ) else 0) =
      (∑ c : Fin h, if c.val = i then (1:ℕ) else 0) +
        (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) from
      Fintype.sum_sum_type _]
    rw [sum_fin_val_ite, ih, List.countP_cons]
    split_ifs <;> simp_all <;> omega

lemma placed_rowLen {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (i : ℕ) :
    μ.rowLen i = rs.countP (fun h => i < h) := by
  classical
  let E : {c : Cells rs // row c = i} ≃ {c : μ.cells // c.val.1 = i} :=
    e.subtypeEquiv (fun c => by rw [hr])
  have hc := Fintype.card_congr (E.trans (rowFiberEquiv μ i))
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter, cells_row_count] at hc
  exact hc.symm

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Strip. -/

section

noncomputable section

namespace Saxl.Balance

lemma horizontal_of_interlacing (ν μ : YoungDiagram)
    (hsub : ∀ i, ν.rowLen i ≤ μ.rowLen i)
    (hbtw : ∀ i, μ.rowLen (i+1) ≤ ν.rowLen i) : HorizontalStrip ν μ := by
  constructor
  · intro x hx
    exact YoungDiagram.mem_iff_lt_rowLen.mpr
      ((YoungDiagram.mem_iff_lt_rowLen.mp hx).trans_le (hsub x.1))
  · intro x hx hxν y hy hyν hxy
    apply Prod.ext _ hxy
    have hh : ∀ (p q : ℕ × ℕ), p ∈ μ → p ∉ ν → q ∈ μ → q ∉ ν →
        p.2 = q.2 → ¬ p.1 < q.1 := by
      intro p q _ hp hq _ hpq hlt
      have hp' := mt YoungDiagram.mem_iff_lt_rowLen.mpr hp
      have hq' := YoungDiagram.mem_iff_lt_rowLen.mp hq
      have hb := (μ.rowLen_anti _ _ (show p.1+1 ≤ q.1 by omega)).trans (hbtw p.1)
      omega
    exact Nat.le_antisymm (Nat.le_of_not_gt (hh y x hy hyν hx hxν hxy.symm))
      (Nat.le_of_not_gt (hh x y hx hxν hy hyν hxy))

lemma ofRowLens_height (A : List ℕ) (hA : A.SortedGE) :
    (YoungDiagram.ofRowLens A hA).colLen 0 ≤ A.length := by
  by_contra hh
  have h := YoungDiagram.mem_iff_lt_colLen.mpr
    (show A.length < (YoungDiagram.ofRowLens A hA).colLen 0 by omega)
  obtain ⟨h',_⟩ := YoungDiagram.mem_ofRowLens.mp h
  exact (Nat.lt_irrefl _) h'

lemma ofRowLens_rowLen (A : List ℕ) (hA : A.SortedGE) (i : ℕ) :
    (YoungDiagram.ofRowLens A hA).rowLen i = A[i]?.getD 0 := by
  by_cases hi : i < A.length
  · simpa [hi] using YoungDiagram.rowLen_ofRowLens (hw := hA) ⟨i,hi⟩
  · rw [rowLen_zero_of_height_le _ ((ofRowLens_height A hA).trans (by omega))]
    simp [List.getElem?_eq_none (by omega : A.length ≤ i)]

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma rowPrefix_eq_take (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ k = (μ.rowLens.take k).sum := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ,ih]
    by_cases hk : k < μ.rowLens.length
    · rw [List.take_succ_eq_append_getElem hk, List.sum_append, List.sum_singleton]
      congr 1
      exact YoungDiagram.get_rowLens.symm
    · have hh : μ.colLen 0 ≤ k := by simpa only [YoungDiagram.length_rowLens] using Nat.le_of_not_gt hk
      rw [rowLen_zero_of_height_le μ hh,add_zero]
      rw [List.take_of_length_le (Nat.le_of_not_gt hk),
        List.take_of_length_le (by omega : μ.rowLens.length ≤ k+1)]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_KroneckerSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kronecker Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open Columns FlagColumns

lemma tableau_card_eq {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) : μ.card = n := by
  have h := Fintype.card_congr t
  simpa only [Fintype.card_fin,Fintype.card_coe,YoungDiagram.card] using h.symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SquareSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Columns

lemma columnShape_diagram (μ : YoungDiagram) :
    columnShape μ.transpose.rowLens = μ := by
  obtain ⟨e,hr,_⟩ := columnShape_placement μ.transpose.rowLens
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  obtain ⟨f,hf,_⟩ := place_columns μ (List.Perm.refl _)
  rw [placed_rowLen e hr,placed_rowLen f hf]

lemma columnShape_sorted (rs : List ℕ) (hs : rs.SortedGE) (hp : ∀ a ∈ rs, 0 < a) :
    columnShape rs = (YoungDiagram.ofRowLens rs hs).transpose := by
  conv_lhs => rw [← YoungDiagram.rowLens_ofRowLens_eq_self hp (hw := hs)]
  simpa only [YoungDiagram.transpose_transpose] using
    columnShape_diagram ((YoungDiagram.ofRowLens rs hs).transpose)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_RowCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowDiagram_eq (rs : List ℕ) (h : GoodRows rs) :
    rowDiagram rs = YoungDiagram.ofRowLens rs h.1 := by
  rw [rowDiagram,columnShape_sorted rs h.1 h.2,YoungDiagram.transpose_transpose]

lemma rowDiagram_rows {rs : List ℕ} (h : GoodRows rs) : (rowDiagram rs).rowLens = rs := by
  rw [rowDiagram_eq rs h,YoungDiagram.rowLens_ofRowLens_eq_self h.2]

lemma rowDiagram_rowLen {rs : List ℕ} (h : GoodRows rs) (i : ℕ) :
    (rowDiagram rs).rowLen i = rs[i]?.getD 0 := by
  rw [rowDiagram_eq rs h,ofRowLens_rowLen]

lemma rowDiagram_height {rs : List ℕ} (h : GoodRows rs) :
    (rowDiagram rs).colLen 0 = rs.length := by
  rw [← YoungDiagram.length_rowLens,rowDiagram_rows h]

lemma rowDiagram_rowLens (μ : YoungDiagram) : rowDiagram μ.rowLens = μ := by
  rw [rowDiagram_eq _ ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

lemma rowsStrip_sound {rs ss : List ℕ} (h : RowsStrip rs ss) :
    HorizontalStrip (rowDiagram rs) (rowDiagram ss) := by
  have hb (i : ℕ) : (rowDiagram rs).rowLen i ≤ (rowDiagram ss).rowLen i ∧
      (rowDiagram ss).rowLen (i+1) ≤ (rowDiagram rs).rowLen i := by
    rw [rowDiagram_rowLen h.1,rowDiagram_rowLen h.2.1,rowDiagram_rowLen h.2.1]
    by_cases hi : i < max rs.length ss.length
    · exact h.2.2 i (List.mem_range.mpr hi)
    · have hr : rs.length ≤ i := le_trans (le_max_left _ _) (Nat.le_of_not_gt hi)
      have hs : ss.length ≤ i := le_trans (le_max_right _ _) (Nat.le_of_not_gt hi)
      simp [List.getElem?_eq_none hr,List.getElem?_eq_none hs,
        List.getElem?_eq_none (by omega : ss.length ≤ i+1)]
  exact horizontal_of_interlacing _ _ (fun i => (hb i).1) (fun i => (hb i).2)

lemma rowsDom_of_dominates {μ θ : YoungDiagram} (h : Dominates μ θ) :
    RowsDom μ.rowLens θ.rowLens := by
  intro k _
  simpa only [← rowPrefix_eq_take] using h k

lemma height_le_of_dominates {μ θ : YoungDiagram} (hc : μ.card = θ.card)
    (h : Dominates μ θ) : μ.colLen 0 ≤ θ.colLen 0 := by
  by_contra hn
  have hp : 0 < μ.rowLen (θ.colLen 0) :=
    YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr (by omega))
  have hh := h (θ.colLen 0)
  rw [rowPrefix_eq_card θ le_rfl] at hh
  have hk := rowPrefix_le_card μ (θ.colLen 0+1)
  rw [rowPrefix_succ] at hk
  omega

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPackingCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing Cone. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

theorem WordPacking.of_cone_shape {rs : List ℕ} {μ θ : YoungDiagram} {d : ℕ}
    (hp : rs.Perm μ.transpose.rowLens) (hd : μ.colLen 0 ≤ d) (ht : θ.card = rs.sum)
    (k : ℕ) (I : Set ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : ∀ (u : Tableau rs.sum μ) (ν : YoungDiagram) (t : Tableau rs.sum ν), Dominates ν θ →
      ∃ F : Representation.IntertwiningMap (spechtRep t)
        (projectedSpechtTensor u u (inOutputs I) (inOutputs_invariant I)).toRepresentation, F ≠ 0) :
    Nonempty (WordPacking rs θ.rowLens d A label {k}) := by
  obtain ⟨e,hr,hc⟩ := place_columns μ hp
  exact ⟨WordPacking.cone e hr hc hd ht k I A label he (hs _)⟩

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

lemma pairLetters_output (a : Fin 6) : output (d := 3) (e := 3) (pairLetters a) ∈ Set.Icc 1 3 := by
  fin_cases a <;> decide

lemma restrict_projected {n : ℕ} (v : WordSpace n 9) :
    restrictLetters pairLetters (invariantCoordinateProjection (inOutputs (d := 3) (e := 3) (Set.Icc 1 3))
      (inOutputs_invariant (d := 3) (e := 3) (Set.Icc 1 3)) v) = restrictLetters pairLetters v := by
  classical
  funext w
  change (if inOutputs (d := 3) (e := 3) (Set.Icc 1 3) (pairLetters ∘ w) then v (pairLetters ∘ w) else 0) = _
  exact ite_eq_left (fun i => pairLetters_output (w i))

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowProjected
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Projected. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

lemma columns_height (m s : ℕ) : (columnShape (columns m s)).colLen 0 ≤ 3 := by
  apply columnShape_height
  intro x hx
  simp only [columns,List.mem_append,List.mem_singleton,twos,ones,List.mem_replicate] at hx
  rcases hx with (⟨_,rfl⟩ | ⟨_,rfl⟩) | rfl <;> omega

theorem projected_support (m s : ℕ)
    (a b : Tableau (columns m s).sum (columnShape (columns m s)))
    {ν η μ : YoungDiagram}
    (tν : Tableau (twos m).sum ν) (tη : Tableau (twos m ++ ones s).sum η)
    (tμ : Tableau (columns m s).sum μ)
    (hev : ∀ i, Even (ν.rowLen i)) (hν : ν.colLen 0 ≤ 3) (hμ : μ.colLen 0 ≤ 3)
    (hs : HorizontalStrip ν η) (ht : HorizontalStrip η μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep tμ)
      (projectedSpechtTensor a b (inOutputs (Set.Icc 1 3))
        (inOutputs_invariant (Set.Icc 1 3))).toRepresentation, Function.Injective F := by
  classical
  let rs := columns m s
  obtain ⟨e,hr,hc⟩ := columnShape_placement rs
  let t := (enumerate rs).trans e
  let f := Fin.castLE (columns_height m s)
  have hblocks : letterLift f (polytabloid t) = blocks rs (standard 3) :=
    (standard_placed e hr hc (columns_height m s)).symm
  let P := inOutputs (n := rs.sum) (d := (columnShape rs).colLen 0)
    (e := (columnShape rs).colLen 0) (Set.Icc 1 3)
  let hP := inOutputs_invariant (n := rs.sum) (d := (columnShape rs).colLen 0)
    (e := (columnShape rs).colLen 0) (Set.Icc 1 3)
  let Q := inOutputs (n := rs.sum) (d := 3) (e := 3) (Set.Icc 1 3)
  have hPQ (w : Fin rs.sum → Fin ((columnShape rs).colLen 0 * (columnShape rs).colLen 0)) :
      Q (pairLetterMap f f ∘ w) ↔ P w := by
    change (∀ i, output (pairLetterMap f f (w i)) ∈ Set.Icc 1 3) ↔ _
    simp only [output_pairLetterMap f (fun _ => rfl)]
    rfl
  let W := projectedSpechtTensor a b P hP
  have hma : polytabloid t ∈ spechtSub a := by
    rw [← spechtSub_tableau_independent t a]
    exact mem_cyclic _ _
  have hmb : polytabloid t ∈ spechtSub b := by
    rw [← spechtSub_tableau_independent t b]
    exact mem_cyclic _ _
  let z : W.toSubmodule := projectedTensorQuotient a b P hP
    (⟨polytabloid t,hma⟩ ⊗ₜ[ℂ] ⟨polytabloid t,hmb⟩)
  let D : Representation.IntertwiningMap W.toRepresentation (wordRep rs.sum 6) :=
    (restrictLetters pairLetters).comp
      ((letterLift (pairLetterMap f f)).comp (subrepInclusion W))
  have hz : D z = -generator (pairPositions m) (shortSplit m s) (tripleSplit m s) := by
    change restrictLetters pairLetters (letterLift (pairLetterMap f f)
      (coordinateProjection P (spechtTensorMap a b
        (⟨polytabloid t,hma⟩ ⊗ₜ[ℂ] ⟨polytabloid t,hmb⟩)))) = _
    rw [spechtTensorMap]
    change restrictLetters pairLetters (letterLift (pairLetterMap f f)
      (coordinateProjection P (wordTensor rs.sum _ _ (polytabloid t ⊗ₜ[ℂ] polytabloid t)))) = _
    rw [← coordinateProjection_letterLift _ P Q hPQ,
      letterLift_wordTensor,hblocks]
    change restrictLetters pairLetters (invariantCoordinateProjection Q
      (inOutputs_invariant _) (wordTensor rs.sum 3 3 (blocks rs (standard 3) ⊗ₜ[ℂ]
        blocks rs (standard 3)))) = _
    rw [restrict_projected]
    exact sixSquare_columns m s
  have hsupp := generator_support (pairPositions m) (shortSplit m s) (tripleSplit m s)
    tν tη tμ hev hν hμ hs ht
  have hcy : cyclic (wordRep rs.sum 6) (D z) =
      cyclic (wordRep rs.sum 6) (generator (pairPositions m) (shortSplit m s) (tripleSplit m s)) := by
    rw [hz, ← neg_one_smul ℂ,cyclic_smul_eq _ _ _ (by norm_num)]
  rw [←hcy] at hsupp
  obtain ⟨F,hF⟩ := hsupp
  obtain ⟨G,hG⟩ := cyclic_projection_support D z F hF
  let H := (subrepInclusion (cyclic W.toRepresentation z)).comp G
  have hH : H ≠ 0 := by
    intro hz
    apply hG
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun J => J x) hz
  let := specht_irreducible tμ
  exact ⟨H,(Representation.IsIrreducible.injective_or_eq_zero H).resolve_right hH⟩

end Saxl.ThreeRow
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FiniteDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Diagrams. -/

section

namespace UniversalTensorSquare

lemma mem_partitionLists (k : ℕ) (rs : List ℕ) (n b : ℕ)
    (hsum : rs.sum = n) (hlen : rs.length ≤ k)
    (hpos : ∀ a ∈ rs, 0 < a) (hbound : ∀ a ∈ rs, a ≤ b)
    (hsort : rs.SortedGE) : rs ∈ partitionLists k n b := by
  induction k generalizing rs n b with
  | zero =>
    have hr : rs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst rs
    simp only [List.sum_nil] at hsum
    subst n
    simp [partitionLists]
  | succ k ih =>
    cases rs with
    | nil =>
      simp only [List.sum_nil] at hsum
      subst n
      simp [partitionLists]
    | cons a rs =>
      have ha : 0 < a := hpos a (by simp)
      have han : a ≤ n := by simp only [List.sum_cons] at hsum; omega
      have hab : a ≤ b := hbound a (by simp)
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨a, Finset.mem_Icc.mpr ⟨ha, le_min han hab⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨rs, ih rs (n-a) a ?_ ?_ ?_ ?_ ?_, rfl⟩
      · simp only [List.sum_cons] at hsum
        omega
      · simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
      · intro x hx
        exact hpos x (by simp [hx])
      · intro x hx
        exact (List.pairwise_cons.mp hsort.pairwise).1 x hx
      · exact (List.pairwise_cons.mp hsort.pairwise).2.sortedGE

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ThreeRowMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Row Masks. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

namespace ThreeRowEntry

lemma support {m s : ℕ} {c : ThreeRowEntry} (h : c.Valid m s)
    (a b : Tableau (ThreeRow.columns m s).sum (columnShape (ThreeRow.columns m s)))
    (t : Tableau (ThreeRow.columns m s).sum (rowDiagram c.final)) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a b (inOutputs (Set.Icc 1 3))
        (inOutputs_invariant (Set.Icc 1 3))).toRepresentation, F ≠ 0 := by
  rcases h with ⟨hν,hμ,hc,hm,hf,hev,h1,h2⟩
  let v := canonicalTableau (rowDiagram c.core) (show (rowDiagram c.core).card =
    (ThreeRow.twos m).sum by rw [rowDiagram_card,hc]; simp [ThreeRow.twos,Nat.mul_comm])
  let u := canonicalTableau (rowDiagram c.middle) (show (rowDiagram c.middle).card =
    (ThreeRow.twos m ++ ThreeRow.ones s).sum by
      rw [rowDiagram_card,hm]; simp [ThreeRow.twos,ThreeRow.ones,Nat.mul_comm])
  have heven (i : ℕ) : Even ((rowDiagram c.core).rowLen i) := by
    rw [rowDiagram_rowLen h1.1]
    by_cases hi : i < c.core.length
    · rw [List.getElem?_eq_getElem hi,Option.getD_some]
      exact (Nat.even_iff).mpr (hev _ (List.getElem_mem hi))
    · simp only [List.getElem?_eq_none (Nat.le_of_not_gt hi),Option.getD_none]
      exact ⟨0,rfl⟩
  obtain ⟨F,hF⟩ := ThreeRow.projected_support m s a b v u t heven
    (by rwa [rowDiagram_height h1.1]) (by rwa [rowDiagram_height h2.2.1])
    (rowsStrip_sound h1) (rowsStrip_sound h2)
  refine ⟨F,?_⟩
  intro hz
  exact polytabloid_ne_zero t (congrArg Subtype.val
    (hF (show F ⟨polytabloid t,mem_cyclic _ _⟩ = F 0 by rw [hz]; rfl)))

end ThreeRowEntry

lemma threeRowMask_support {m s : ℕ} {ps : List ℕ} {cs : List ThreeRowEntry}
    (h : ThreeRowMask m s ps cs)
    (a : Tableau (ThreeRow.columns m s).sum (columnShape (ThreeRow.columns m s)))
    (μ : YoungDiagram) (t : Tableau (ThreeRow.columns m s).sum μ)
    (hd : Dominates μ (rowDiagram ps)) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a a (inOutputs (Set.Icc 1 3))
        (inOutputs_invariant (Set.Icc 1 3))).toRepresentation, F ≠ 0 := by
  have hsize : (ThreeRow.columns m s).sum = 2*m+s+3 := by
    simp [ThreeRow.columns,ThreeRow.twos,ThreeRow.ones,Nat.mul_comm,Nat.add_assoc]
  have hcard : μ.card = 2*m+s+3 := (tableau_card_eq t).trans hsize
  have ht : μ.card = (rowDiagram ps).card := by rw [hcard,rowDiagram_card,h.2.2.1]
  have hh : μ.colLen 0 ≤ 3 := (height_le_of_dominates ht hd).trans (by
    rw [rowDiagram_height h.1]; exact h.2.1)
  have hm : μ.rowLens ∈ partitionLists 3 (2*m+s+3) (2*m+s+3) := by
    apply mem_partitionLists
    · exact (card_eq_sum_rowLens μ).symm.trans hcard
    · simpa only [YoungDiagram.length_rowLens] using hh
    · exact μ.pos_of_mem_rowLens
    · intro x hx
      rw [← hcard,card_eq_sum_rowLens]
      exact List.single_le_sum (fun _ _ => Nat.zero_le _) x hx
    · exact μ.rowLens_sorted
  have hd' : RowsDom μ.rowLens ps := by
    simpa only [rowDiagram_rows h.1] using rowsDom_of_dominates hd
  obtain ⟨c,hc,he⟩ := List.mem_map.mp (h.2.2.2.2 _ hm hd')
  have eqμ : rowDiagram c.final = μ := by rw [he,rowDiagram_rowLens]
  subst μ
  exact ThreeRowEntry.support (h.2.2.2.1 c hc) a a t

end UniversalTensorSquare

namespace Saxl.Balance
open FlagColumns Columns UniversalTensorSquare

theorem WordPacking.threeRows_oai {m s d : ℕ} {ps : List ℕ} {cs : List ThreeRowEntry}
    (hd : 3 ≤ d) (h : ThreeRowMask m s ps cs)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = 1) ↔ output a ∈ Set.Icc 1 3) :
    Nonempty (WordPacking (ThreeRow.columns m s) ps d A label {1}) := by
  have hp : ∀ x ∈ ThreeRow.columns m s, 0 < x := by
    simp only [ThreeRow.columns,ThreeRow.twos,ThreeRow.ones,List.mem_append,
      List.mem_replicate,List.mem_singleton]
    intro x hx
    rcases hx with (⟨_,rfl⟩ | ⟨_,rfl⟩) | rfl <;> omega
  have ht : (rowDiagram ps).card = (ThreeRow.columns m s).sum := by
    rw [rowDiagram_card,h.2.2.1]
    simp [ThreeRow.columns,ThreeRow.twos,ThreeRow.ones,Nat.mul_comm,Nat.add_assoc]
  simpa only [rowDiagram_rows h.1] using WordPacking.of_cone_shape
    (columnShape_rows_permutation (ThreeRow.columns m s) hp)
    ((ThreeRow.columns_height m s).trans hd) ht 1 (Set.Icc 1 3) A label he
    (fun a μ t hμ => threeRowMask_support h a μ t hμ)

end Saxl.Balance
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.Balance.WordPacking.threeRows_oai := @OAI.Saxl.Balance.WordPacking.threeRows_oai
