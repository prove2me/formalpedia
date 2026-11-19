-- Prove2me | solution 2 for OAI.Saxl.cyclic_saxl_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:58:25.206192+00:00
-- url     : https://prove2.me/submissions/b881e0a1-fd6d-44c7-b572-b30c30d3d284
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_dominated_support_uts
import Theorems.Thm_OAI_Saxl_pieri_strip_surjective_uts
import Theorems.Thm_OAI_Saxl_twoBand_support_uts

section
-- module Solutions.OAIQ259_US.Saxl_HighProjection
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.Columns.columnTableau_val _root_.OAI.Saxl.coordinateProjection_apply _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.staircase_colLen _root_.OAI.Saxl.staircase_rowLen _root_.OAI.Saxl.staircase_transpose _root_.OAI.Saxl.tableauInclusion_cell _root_.OAI.UniversalTensorSquare.candidate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/

theorem high_positions_rigidity (h s : ℕ)
    (g k : Equiv.Perm (staircase (h+s)).cells)
    (hg : ∀ x, (g x).val.1 = x.val.1)
    (hk : ∀ x, (k x).val.2 = x.val.2)
    (hc : ∀ x, s ≤ (g x).val.2 ↔ s ≤ (k x).val.1) :
    ∀ x, s ≤ (g x).val.2 ↔ x.val.1 + x.val.2 < h := by
  classical
  let A : Finset (staircase (h+s)).cells := Finset.univ.filter (fun x => s ≤ (g x).val.2)
  let B : Finset (staircase (h+s)).cells := Finset.univ.filter (fun x => x.val.1 + x.val.2 < h)
  let eR : A ≃ (staircase h).cells :=
    (Equiv.subtypeEquiv g (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and])).trans
      (highRowEquiv h s)
  let eC : A ≃ (staircase h).cells :=
    (Equiv.subtypeEquiv k (by intro x; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]; exact hc x)).trans
      (highColEquiv h s)
  let eB : B ≃ (staircase h).cells :=
    { toFun := fun x => ⟨x.val.val, mem_staircase.mpr (by simpa [B] using x.property)⟩
      invFun := fun x => ⟨⟨x.val, mem_staircase.mpr (by
        have hx := mem_staircase.mp x.property; omega)⟩, by simp [B, mem_staircase.mp x.property]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : A.card = B.card := by
    have he := Fintype.card_congr (eR.trans eB.symm)
    simpa using he
  have hrow : ∑ x ∈ A, (x.val.1 : ℤ) = ∑ x ∈ B, (x.val.1 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hR := Equiv.sum_comp eR (fun x => (x.val.1 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.1 : ℤ))
    simpa [eR, eB, highRowEquiv, hg] using hR.trans hB.symm
  have hcol : ∑ x ∈ A, (x.val.2 : ℤ) = ∑ x ∈ B, (x.val.2 : ℤ) := by
    rw [← Finset.sum_coe_sort A, ← Finset.sum_coe_sort B]
    have hC := Equiv.sum_comp eC (fun x => (x.val.2 : ℤ))
    have hB := Equiv.sum_comp eB (fun x => (x.val.2 : ℤ))
    simpa [eC, eB, highColEquiv, hk] using hC.trans hB.symm
  let w := fun x : (staircase (h+s)).cells =>
    2 * (h : ℤ) - 1 - 2 * (x.val.1 : ℤ) - 2 * (x.val.2 : ℤ)
  have he : ∑ x ∈ A, w x = ∑ x ∈ B, w x := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    rw [hcard, hrow, hcol]
  have hab := finset_eq_of_signed_sum A B w
    (fun x hx => by
      have hh : x.val.1 + x.val.2 < h := by simpa [B] using hx
      dsimp [w]
      omega)
    (fun x hx => by
      have hh : ¬x.val.1 + x.val.2 < h := by simpa [B] using hx
      dsimp [w]
      omega) he
  intro x
  have := Finset.ext_iff.mp hab x
  simpa [A, B] using this


lemma polytabloid_support {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) (ha : polytabloid t a ≠ 0) :
    ∃ g : columnGroup t, a = rowWord t ∘ (g : Equiv.Perm (Fin n)) := by
  classical
  have hex : ∃ g : columnGroup t, a ∘ (g : Equiv.Perm (Fin n)) = rowWord t := by
    by_contra! hh
    apply ha
    unfold polytabloid
    simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
      OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
    simp [hh]
  obtain ⟨g, hg⟩ := hex
  refine ⟨g⁻¹, ?_⟩
  funext i
  have he := congrFun hg ((g : Equiv.Perm (Fin n))⁻¹ i)
  simpa using he

/- Local same-high projection in the ordinary pair-letter coordinate space. -/

theorem staircase_projected_high_positions (h s : ℕ)
    (w : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0 * (staircase (h+s)).colLen 0))
    (hw : sameHighProjection _ _ _ s (staircaseWord (h+s)) w ≠ 0) :
    ∀ i, s ≤ (splitLeft w i).val ↔
      ((stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h) := by
  classical
  have heq : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val := by
    by_contra hh
    apply hw
    simp [sameHighProjection, hh]
  have hww : staircaseWord (h+s) w ≠ 0 := by
    simpa [sameHighProjection, heq] using hw
  have hp : polytabloid (stairRowTableau (h+s)) (splitLeft w) *
      polytabloid (stairTableau (h+s)) (splitRight w) ≠ 0 := by
    simpa only [staircaseWord, wordTensor_tmul] using hww
  obtain ⟨g, hg⟩ := polytabloid_support (stairRowTableau (h+s)) _ (mul_ne_zero_iff.mp hp).1
  obtain ⟨k, hk⟩ := polytabloid_support (stairTableau (h+s)) _ (mul_ne_zero_iff.mp hp).2
  let t := stairTableau (h+s)
  let gc : Equiv.Perm (staircase (h+s)).cells := (t.symm.trans (g : Equiv.Perm _)).trans t
  let kc : Equiv.Perm (staircase (h+s)).cells := (t.symm.trans (k : Equiv.Perm _)).trans t
  have hgc : ∀ x, (gc x).val.1 = x.val.1 := by
    intro x
    have hh := g.property (t.symm x)
    change (t ((g : Equiv.Perm _) (t.symm x))).val.1 = (t (t.symm x)).val.1 at hh
    simpa [gc] using hh
  have hkc : ∀ x, (kc x).val.2 = x.val.2 := by
    intro x
    have hh := k.property (t.symm x)
    change (t ((k : Equiv.Perm _) (t.symm x))).val.2 = (t (t.symm x)).val.2 at hh
    simpa [kc] using hh
  have hcommon : ∀ x, s ≤ (gc x).val.2 ↔ s ≤ (kc x).val.1 := by
    intro x
    have hh := heq (t.symm x)
    rw [hg, hk] at hh
    exact hh
  have hr := high_positions_rigidity h s gc kc hgc hkc hcommon
  intro i
  have hh := hr (t i)
  rw [hg]
  simpa [gc, t, rowWord, stairRowTableau, staircaseSwap] using hh


lemma columnAlt_left {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    wordRep n d (h : Equiv.Perm (Fin n)) * columnAlt (d := d) t =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((h * g : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((h * g : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, signC_mul_self, one_mul]

lemma polytabloid_alternating {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) : wordRep n (μ.colLen 0) (h : Equiv.Perm (Fin n))
      (polytabloid t) = signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  rw [← columnAlt_row]
  exact congrArg (fun L : Module.End ℂ (WordSpace n (μ.colLen 0)) =>
    L (Pi.single (rowWord t) 1)) (columnAlt_left t h)

/- Move low row letters to the band and high row letters to B_h. -/

lemma rotateRow_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateRow h s x).val.2 ↔ x.val.1 + x.val.2 < h := by
  have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
  change s ≤ (if x.val.2 < h - x.val.1 then x.val.2+s else x.val.2-(h-x.val.1)) ↔ _
  split_ifs <;> omega

lemma rotateColumn_high (h s : ℕ) (x : (staircase (h+s)).cells) :
    s ≤ (rotateColumn h s x).val.1 ↔ x.val.1 + x.val.2 < h := by
  have hh := rotateRow_high h s (staircaseSwap (h+s) x)
  change s ≤ (rotateRow h s (staircaseSwap (h+s) x)).val.2 ↔ _
  simpa [staircaseSwap, Nat.add_comm] using hh

lemma polytabloid_column_coeff {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : columnGroup t) :
    polytabloid t (rowWord t ∘ (g : Equiv.Perm (Fin n))) = signC (g : Equiv.Perm (Fin n)) := by
  have hh := congrFun (polytabloid_alternating t g) (rowWord t)
  change polytabloid t (rowWord t ∘ (g : Equiv.Perm (Fin n))) =
    signC (g : Equiv.Perm (Fin n)) * polytabloid t (rowWord t) at hh
  simpa [polytabloid_rowWord] using hh

/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
theorem staircase_projected_ne_zero (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) ≠ 0 := by
  classical
  let a := rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)
  let b := rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)
  let w := mergeWords a b
  have ha (i) : s ≤ (a i).val ↔ (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h := by
    have hh := rotateRow_high h s (stairTableau (h+s) i)
    simpa [a, rowWord, stairRowTableau, rotateRowPositions, staircaseSwap] using hh
  have hb (i) : s ≤ (b i).val ↔ (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h := by
    have hh := rotateColumn_high h s (stairTableau (h+s) i)
    simpa [b, rowWord, rotateColumnPositions] using hh
  have hp : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val := by
    intro i
    simp only [w, splitLeft_merge, splitRight_merge]
    exact (ha i).trans (hb i).symm
  intro hz
  have he := congrFun hz w
  change sameHighProjection _ _ _ s (staircaseWord (h+s)) w = 0 at he
  simp only [sameHighProjection, Representation.IntertwiningMap.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, staircaseWord, wordTensor_tmul, w, splitLeft_merge, splitRight_merge,
    a, b, polytabloid_column_coeff] at he
  have hn (g : Equiv.Perm (Fin (staircase (h+s)).card)) : signC g ≠ 0 := by
    intro hz
    have hh := signC_mul_self g
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hpab : ∀ i, s ≤ (a i).val ↔ s ≤ (b i).val := fun i => (ha i).trans (hb i).symm
  rw [ite_eq_left hpab] at he
  exact mul_ne_zero (hn _) (hn _) he

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_CoordinateSector
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.Columns.columnTableau_val _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.staircase_colLen _root_.OAI.Saxl.staircase_rowLen _root_.OAI.Saxl.staircase_transpose _root_.OAI.Saxl.tableauInclusion_cell _root_.OAI.UniversalTensorSquare.candidate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/

lemma altWord_move {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (r : G) :
    altWord G (a ∘ (r : Equiv.Perm (Fin n))) =
      signC (r : Equiv.Perm (Fin n)) • altWord G a := by
  classical
  let := Fintype.ofFinite G
  have he : Pi.single (a ∘ (r : Equiv.Perm (Fin n))) (1 : ℂ) =
      wordRep n d (r⁻¹ : G) (Pi.single a 1) := by
    rw [wordRep_single]
    rfl
  unfold altWord
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, Finset.smul_sum]
  apply (Equiv.sum_comp (Equiv.mulRight r) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC ((g*r : G) : Equiv.Perm (Fin n)) •
    wordRep n d (((g*r : G) : Equiv.Perm (Fin n)) * (r : Equiv.Perm (Fin n))⁻¹) (Pi.single a 1) = _
  simp only [Subgroup.coe_mul, map_mul, mul_inv_cancel_right, smul_smul]
  rw [mul_comm (signC (g : Equiv.Perm (Fin n)))]

/- Keeping a prescribed coloring restricts the alternating group to its
sector stabilizer. This is the finite coset calculation behind block-factorization. -/
theorem altWord_sector {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop)
    (ha : ∀ i, Q (a i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      altWord (G ⊓ sectorGroup D) a := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite ↥(G ⊓ sectorGroup D)
  have hh (g : G) :
      (∀ i, Q ((a ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) i) ↔ D i) ↔
        (g : Equiv.Perm (Fin n)) ∈ sectorGroup D := by
    constructor
    · intro h i
      have h' := (ha _).symm.trans (h ((g : Equiv.Perm (Fin n)) i))
      simpa using h'.symm
    · intro h i
      exact (ha _).trans (by simpa using (h (((g : Equiv.Perm (Fin n))⁻¹) i)).symm)
  unfold altWord
  simp only [map_sum, map_smul, wordRep_single, coordinateProjection_single, hh, smul_ite, smul_zero]
  let e : {g : G // (g : Equiv.Perm (Fin n)) ∈ sectorGroup D} ≃ ↥(G ⊓ sectorGroup D) := {
    toFun := fun g => ⟨g.val.val, g.val.property, g.property⟩
    invFun := fun g => ⟨⟨g.val, g.property.1⟩, g.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Finset.sum_filter]
  rw [← Finset.sum_attach]
  apply Fintype.sum_equiv ?_ _ _ ?_
  · exact (Equiv.subtypeEquivRight (fun g => by simp)).trans e
  · intro g
    rfl

end Saxl

namespace Saxl
/- The prescribed high sector in the actual staircase enumeration. -/

lemma staircase_projected_sector (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
    coordinateProjection (fun w => (∀ i, s ≤ (splitLeft w i).val ↔ stairHigh h s i) ∧
      (∀ i, s ≤ (splitRight w i).val ↔ stairHigh h s i)) (staircaseWord (h+s)) := by
  classical
  ext w
  by_cases he : ∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val
  · by_cases hw : sameHighProjection _ _ _ s (staircaseWord (h+s)) w = 0
    · have hw' : staircaseWord (h+s) w = 0 := by simpa [sameHighProjection, he] using hw
      simp [hw, hw']
    · have hD := staircase_projected_high_positions h s w hw
      have hD' : ∀ i, s ≤ (splitRight w i).val ↔ stairHigh h s i :=
        fun i => (he i).symm.trans (hD i)
      simp [sameHighProjection, he, hD', stairHigh]
  · have hn : ¬ ((∀ i, s ≤ (splitLeft w i).val ↔ stairHigh h s i) ∧
        (∀ i, s ≤ (splitRight w i).val ↔ stairHigh h s i)) := by
      rintro ⟨h₁,h₂⟩
      exact he (fun i => (h₁ i).trans (h₂ i).symm)
    simp [sameHighProjection, he, hn]

lemma coordinateProjection_tensor {n d e : ℕ}
    (P : (Fin n → Fin d) → Prop) (Q : (Fin n → Fin e) → Prop)
    (x : WordSpace n d) (y : WordSpace n e) :
    coordinateProjection (fun w => P (splitLeft w) ∧ Q (splitRight w))
      (wordTensor n d e (x ⊗ₜ[ℂ] y)) =
    wordTensor n d e (coordinateProjection P x ⊗ₜ[ℂ] coordinateProjection Q y) := by
  classical
  ext w
  by_cases hp : P (splitLeft w) <;> by_cases hq : Q (splitRight w) <;>
    simp [hp,hq]

lemma altWord_sector_rotated {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (Q : Fin d → Prop) (D : Fin n → Prop) (r : G)
    (ha : ∀ i, Q ((a ∘ (r : Equiv.Perm (Fin n))) i) ↔ D i) :
    coordinateProjection (fun b => ∀ i, Q (b i) ↔ D i) (altWord G a) =
      signC (r : Equiv.Perm (Fin n)) • altWord (G ⊓ sectorGroup D) (a ∘ (r : Equiv.Perm (Fin n))) := by
  have hh := altWord_sector G (a ∘ (r : Equiv.Perm (Fin n))) Q D ha
  rw [altWord_move, map_smul] at hh
  rw [← hh, smul_smul, signC_mul_self, one_smul]

lemma rotatePositions_sign (h s : ℕ) :
    signC (rotateColumnPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) =
      signC (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) := by
  let q : Equiv.Perm (Fin (staircase (h+s)).card) :=
    ((stairTableau (h+s)).trans (staircaseSwap (h+s))).trans (stairTableau (h+s)).symm
  have he : (rotateColumnPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) =
      q * (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) * q := by
    ext i
    simp [q, rotateColumnPositions, rotateRowPositions, rotateColumn]
  rw [he, map_mul, map_mul]
  calc
    signC q * signC (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) * signC q =
      signC (rotateRowPositions h s : Equiv.Perm (Fin (staircase (h+s)).card)) * (signC q * signC q) := by ring
    _ = _ := by rw [signC_mul_self, mul_one]

/- Exact sign cancellation in the two retained layers. -/
theorem staircase_cut_layers (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
      wordTensor _ _ _ (cutRowWord h s ⊗ₜ[ℂ] cutColumnWord h s) := by
  rw [staircase_projected_sector, staircaseWord]
  rw [coordinateProjection_tensor
    (fun a : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0) =>
      ∀ i, s ≤ (a i).val ↔ stairHigh h s i)
    (fun a : Fin (staircase (h+s)).card → Fin ((staircase (h+s)).colLen 0) =>
      ∀ i, s ≤ (a i).val ↔ stairHigh h s i)]
  have hr := altWord_sector_rotated (columnGroup (stairRowTableau (h+s)))
    (rowWord (stairRowTableau (h+s))) (fun a => s ≤ a.val) (stairHigh h s)
    (rotateRowPositions h s) (by
      intro i
      simpa [rowWord, stairRowTableau, rotateRowPositions, stairHigh, staircaseSwap] using
        rotateRow_high h s (stairTableau (h+s) i))
  have hc := altWord_sector_rotated (columnGroup (stairTableau (h+s)))
    (rowWord (stairTableau (h+s))) (fun a => s ≤ a.val) (stairHigh h s)
    (rotateColumnPositions h s) (by
      intro i
      simpa [rowWord, rotateColumnPositions, stairHigh] using
        rotateColumn_high h s (stairTableau (h+s) i))
  rw [polytabloid_eq_altWord, polytabloid_eq_altWord, hr, hc]
  rw [TensorProduct.smul_tmul_smul, rotatePositions_sign, signC_mul_self, one_smul]
  rfl

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PositionSplit
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.joinPositions_parts _root_.OAI.Saxl.leftWord_join _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.rightWord_join _root_.OAI.Saxl.sumPerm_mul _root_.OAI.Saxl.sumPerm_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/

lemma altWord_split_term {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    (signC (sumPerm e g h) • wordRep n d (sumPerm e g h) (Pi.single w 1)) v =
    (signC g • wordRep a d g (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC h • wordRep b d h (Pi.single (rightWord e w) 1)) (rightWord e v) := by
  rw [single_positionProduct e w]
  change signC (sumPerm e g h) *
    ((Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e (v ∘ sumPerm e g h)) *
      (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e (v ∘ sumPerm e g h))) = _
  have h₁ : leftWord e (v ∘ sumPerm e g h) = leftWord e v ∘ g := by
    ext i; simp [leftWord]
  have h₂ : rightWord e (v ∘ sumPerm e g h) = rightWord e v ∘ h := by
    ext i; simp [rightWord]
  rw [h₁,h₂,signC_sumPerm]
  change _ = (signC g * (Pi.single (leftWord e w) (1:ℂ) : WordSpace a d) (leftWord e v ∘ g)) *
    (signC h * (Pi.single (rightWord e w) (1:ℂ) : WordSpace b d) (rightWord e v ∘ h))
  ring

/- Independent block permutations factor with exactly the product sign. -/
theorem altWord_split {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (G : Subgroup (Equiv.Perm (Fin n))) (G₁ : Subgroup (Equiv.Perm (Fin a)))
    (G₂ : Subgroup (Equiv.Perm (Fin b))) (E : G ≃ G₁ × G₂)
    (hE : ∀ g : G, (g : Equiv.Perm (Fin n)) =
      sumPerm e ((E g).1 : Equiv.Perm (Fin a)) ((E g).2 : Equiv.Perm (Fin b)))
    (w : Fin n → Fin d) :
    altWord G w = positionProduct e (altWord G₁ (leftWord e w)) (altWord G₂ (rightWord e w)) := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite G₁
  let := Fintype.ofFinite G₂
  ext v
  unfold altWord
  simp only [Finset.sum_apply, positionProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : G₁ × G₂,
      (signC (p.1 : Equiv.Perm (Fin a)) • wordRep a d p.1 (Pi.single (leftWord e w) 1)) (leftWord e v) *
      (signC (p.2 : Equiv.Perm (Fin b)) • wordRep b d p.2 (Pi.single (rightWord e w) 1)) (rightWord e v) := by
        apply Fintype.sum_equiv E
        intro g
        rw [hE g]
        exact altWord_split_term e w v _ _
    _ = _ := Fintype.sum_prod_type _



theorem altWord_fiber_split {n a b d : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b)
    (f : Fin n → α) (w : Fin n → Fin d) :
    altWord (fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) w =
      positionProduct e
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inl i)))) (leftWord e w))
        (altWord (fiberGroup (fun i => f (e.symm (Sum.inr i)))) (rightWord e w)) := by
  apply altWord_split e _ _ _ (fiberSplit e f).symm
  intro g
  exact (congrArg Subtype.val ((fiberSplit e f).apply_symm_apply g)).symm


end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandFactorization
attribute [-simp] _root_.OAI.Saxl.Columns.columnTableau_val _root_.OAI.Saxl.staircase_rowLen _root_.OAI.Saxl.staircase_transpose _root_.OAI.Saxl.tableauInclusion_cell _root_.OAI.UniversalTensorSquare.candidate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma cutPositions_left (h s : ℕ) (i : Fin (staircase h).card) :
    (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val = (stairTableau h i).val := by
  classical
  simp [cutPositions, Equiv.sumCompl, highPositionsEquiv]

lemma row_cut_group (h s : ℕ) :
    columnGroup (stairRowTableau (h+s)) ⊓ sectorGroup (stairHigh h s) =
      fiberGroup (fun i => (stairTableau (h+s) i).val.1) ⊓
        sectorGroup (fun i => (cutPositions h s i).isLeft = true) := by
  congr 1
  congr 1; funext i; exact propext (cutPositions_high h s i).symm

lemma column_cut_group (h s : ℕ) :
    columnGroup (stairTableau (h+s)) ⊓ sectorGroup (stairHigh h s) =
      fiberGroup (fun i => (stairTableau (h+s) i).val.2) ⊓
        sectorGroup (fun i => (cutPositions h s i).isLeft = true) := by
  congr 1
  congr 1; funext i; exact propext (cutPositions_high h s i).symm

lemma highRow_word (h s : ℕ) :
    leftWord (cutPositions h s) (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)) =
      highLetter h s ∘ rowWord (stairRowTableau h) := by
  funext i
  apply Fin.ext
  have hi : (stairTableau h i).val.1 + (stairTableau h i).val.2 < h :=
    mem_staircase.mp (stairTableau h i).property
  have he := cutPositions_left h s i
  simp only [leftWord, Function.comp_apply, rowWord, stairRowTableau, rotateRowPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, staircaseSwap, highLetter]
  change (rotateRow h s (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i)))).val.2 = _
  change (if _ then _ else _) = (stairTableau h i).val.2+s
  rw [he]
  rw [ite_eq_left (by omega)]

lemma highColumn_word (h s : ℕ) :
    leftWord (cutPositions h s) (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)) =
      highLetter h s ∘ rowWord (stairTableau h) := by
  funext i
  apply Fin.ext
  have hi : (stairTableau h i).val.1 + (stairTableau h i).val.2 < h :=
    mem_staircase.mp (stairTableau h i).property
  have he := cutPositions_left h s i
  simp only [leftWord, Function.comp_apply, rowWord, rotateColumnPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, highLetter]
  change (rotateColumn h s (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i)))).val.1 = _
  change (if (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.1 <
      h - (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.2 then
      (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.1+s else
      (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.1 -
        (h - (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.2)) = _
  simp only [he]
  rw [ite_eq_left (by omega)]

/- The first-layer exact band factorization, including the high-letter shift. -/
theorem cutRowWord_factor (h s : ℕ) : cutRowWord h s =
    positionProduct (cutPositions h s)
      (letterLift (highLetter h s) (polytabloid (stairRowTableau h))) (bandRowWord h s) := by
  unfold cutRowWord
  rw [row_cut_group, altWord_fiber_split]
  congr 1
  rw [highRow_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau h i).val.1)
  congr 1
  funext i
  exact congrArg Prod.fst (cutPositions_left h s i)

/- The second-layer exact band factorization. -/
theorem cutColumnWord_factor (h s : ℕ) : cutColumnWord h s =
    positionProduct (cutPositions h s)
      (letterLift (highLetter h s) (polytabloid (stairTableau h))) (bandColumnWord h s) := by
  unfold cutColumnWord
  rw [column_cut_group, altWord_fiber_split]
  congr 1
  rw [highColumn_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau h i).val.2)
  congr 1
  funext i
  exact congrArg Prod.snd (cutPositions_left h s i)



end Saxl

end

end OAI
end

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

/- Explicit finite-group induction on a linear map. -/

lemma averagedMap_apply {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) (f : X →ₗ[ℂ] Y) (x : X) :
    averagedMap ρ σ f x = ∑ g : G, σ g (f (ρ g⁻¹ x)) := by
  simp only [averagedMap, Representation.IntertwiningMap.coe_mk, LinearMap.sum_apply,
    LinearMap.comp_apply]

/- Coordinate-sector induction, in precisely the nonzero-Hom form used in
the staircase induction. The projector kills translates outside the stabilizer. -/
theorem sector_average_nonzero {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [Fintype G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y)
    (H : Subgroup G) (f : X →ₗ[ℂ] Y) (hf : f ≠ 0)
    (he : ∀ g ∈ H, ∀ x, f (ρ g x) = σ g (f x))
    (P : Y →ₗ[ℂ] Y) (hP : ∀ x, P (f x) = f x)
    (hkill : ∀ g ∉ H, ∀ x, P (σ g (f x)) = 0) :
    averagedMap ρ σ f ≠ 0 := by
  classical
  have hproj (x : X) : P (averagedMap ρ σ f x) =
      ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) • f x := by
    rw [averagedMap_apply, map_sum]
    have hh (g : G) : P (σ g (f (ρ g⁻¹ x))) = if g ∈ H then f x else 0 := by
      by_cases hg : g ∈ H
      · rw [ite_eq_left hg, ← he g hg, ← Module.End.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        exact hP x
      · rw [ite_eq_right hg]
        exact hkill g hg _
    simp only [hh]
    simp [Finset.sum_ite, Nat.cast_smul_eq_nsmul]
  have hc : ((Finset.univ.filter (fun g : G => g ∈ H)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact ne_of_gt (Finset.card_pos.mpr ⟨1, by simp⟩)
  intro hz
  apply hf
  ext x
  have heq := hproj x
  rw [hz] at heq
  change P 0 = _ at heq
  rw [map_zero] at heq
  exact (smul_eq_zero.mp heq.symm).resolve_left hc

open scoped MonoidAlgebra

end Saxl

namespace Saxl

theorem sector_support_transfer {n d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (D : Fin n → Prop) (A : Fin d → Prop) (z : WordSpace n d)
    (f : X →ₗ[ℂ] WordSpace n d) (hf : f ≠ 0)
    (he : ∀ g ∈ sectorGroup D, ∀ x, f (ρ g x) = wordRep n d g (f x))
    (hm : ∀ x, f x ∈ cyclic (wordRep n d) z)
    (hs : ∀ x w, f x w ≠ 0 → wordSector D A w) :
    ∃ F : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation,
      F ≠ 0 := by
  classical
  let P := coordinateProjection (wordSector D A)
  have hP (x) : P (f x) = f x := by
    ext w
    change (if wordSector D A w then f x w else 0) = _
    split_ifs with h
    · rfl
    · exact (not_ne_iff.mp (fun hh => h (hs x w hh))).symm
  have hk (g : Equiv.Perm (Fin n)) (hg : g ∉ sectorGroup D) (x) :
      P (wordRep n d g (f x)) = 0 := by
    ext w
    change (if wordSector D A w then f x (w ∘ g) else 0) = 0
    split_ifs with hw
    · by_contra hn
      have hh := hs x (w ∘ g) hn
      apply hg
      intro i
      exact (hw (g i)).symm.trans (hh i)
    · rfl
  let F := averagedMap ρ (wordRep n d) f
  have hF : F ≠ 0 := sector_average_nonzero ρ (wordRep n d) (sectorGroup D) f hf he P hP hk
  have hmem (x) : F x ∈ cyclic (wordRep n d) z := by
    rw [show F x = _ from averagedMap_apply ρ (wordRep n d) f x]
    apply Submodule.sum_mem
    intro g hg
    exact (cyclic (wordRep n d) z).apply_mem_toSubmodule g (hm _)
  let G : Representation.IntertwiningMap ρ (cyclic (wordRep n d) z).toRepresentation :=
    { toLinearMap := F.toLinearMap.codRestrict _ hmem
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact LinearMap.congr_fun (F.isIntertwining' g) x }
  refine ⟨G, ?_⟩
  intro hz
  apply hF
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val (congrArg (fun l => l x) hz)

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



end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.joinPositions_parts _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.rightWord_join _root_.OAI.Saxl.staircase_rowLen _root_.OAI.Saxl.staircase_transpose _root_.OAI.Saxl.tableauInclusion_cell _root_.OAI.UniversalTensorSquare.candidate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Coordinate subrepresentation using only letters with property A. -/

lemma alphabetSub_iff {n d : ℕ} (A : Fin d → Prop) (x : WordSpace n d) :
    x ∈ alphabetSub n d A ↔ ∀ w, x w ≠ 0 → ∀ i, A (w i) := by
  change (∀ w, (∃ i, ¬ A (w i)) → x w = 0) ↔ _
  constructor
  · intro h w hw i
    by_contra hn
    exact hw (h w ⟨i,hn⟩)
  · intro h w hw
    by_contra hn
    obtain ⟨i,hi⟩ := hw
    exact hi (h w hn i)

lemma cyclic_alphabet {n d : ℕ} (A : Fin d → Prop) (v : WordSpace n d)
    (hv : v ∈ alphabetSub n d A) (x : WordSpace n d) (hx : x ∈ cyclic (wordRep n d) v) :
    x ∈ alphabetSub n d A := (cyclic_le _ _ _).mpr hv hx

lemma single_mem_alphabet {n d : ℕ} (A : Fin d → Prop) (a : Fin n → Fin d) (ha : ∀ i, A (a i)) :
    (Pi.single a (1:ℂ) : WordSpace n d) ∈ alphabetSub n d A := by
  classical
  intro w hw
  apply Pi.single_eq_of_ne
  intro he
  subst w
  obtain ⟨i,hi⟩ := hw
  exact hi (ha i)

lemma altWord_mem_alphabet {n d : ℕ} (A : Fin d → Prop)
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) (ha : ∀ i, A (a i)) :
    altWord G a ∈ alphabetSub n d A := by
  classical
  unfold altWord
  apply Submodule.sum_mem
  intro g hg
  apply Submodule.smul_mem
  exact (alphabetSub n d A).apply_mem_toSubmodule g.val (single_mem_alphabet A a ha)

lemma pairLift_wordTensor {n d D : ℕ} (φ : Fin d → Fin D) (x y : WordSpace n d) :
    pairLift φ (wordTensor n d d (x ⊗ₜ[ℂ] y)) =
      wordTensor n D D (letterLift φ x ⊗ₜ[ℂ] letterLift φ y) := by
  let E := (wordTensorIntertwiner n d d).ofBijective (wordTensor n d d).bijective
  change wordTensor n D D (((letterLift φ).tensor (letterLift φ)) (E.symm (E (x ⊗ₜ[ℂ] y)))) = _
  rw [E.symm_apply_apply]
  rfl

lemma pairLift_injective {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ) :
    Function.Injective (pairLift (n := n) φ) := by
  apply (wordTensor n D D).injective.comp
  apply (TensorProduct.map_injective_of_flat_flat _ _ (letterLift_injective φ hφ) (letterLift_injective φ hφ)).comp
  exact ((wordTensorIntertwiner n d d).ofBijective (wordTensor n d d).bijective).symm.injective

lemma pairWord_mem_alphabetLeft {n d : ℕ} (A : Fin d → Prop)
    (x y : WordSpace n d) (hx : x ∈ alphabetSub n d A) :
    wordTensor n d d (x ⊗ₜ[ℂ] y) ∈
      alphabetSub n (d*d) (fun a => A (finProdFinEquiv.symm a).1) := by
  apply (alphabetSub_iff _ _).mpr
  intro w hw i
  rw [wordTensor_tmul] at hw
  exact (alphabetSub_iff A x).mp hx (splitLeft w) ((mul_ne_zero_iff.mp hw).1) i



lemma highLetter_injective (h s : ℕ) : Function.Injective (highLetter h s) := by
  intro a b hab
  apply Fin.ext
  have := congrArg Fin.val hab
  dsimp [highLetter] at this
  omega

lemma shiftedStairWord_support (h s : ℕ) (μ : YoungDiagram) (t : Tableau (staircase h).card μ)
    (f : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic h).toRepresentation)
    (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (shiftedStairWord h s)).toRepresentation, F ≠ 0 := by
  let F := (cyclicMap (pairLift (highLetter h s)) (staircaseWord h)).comp f
  refine ⟨F, ?_⟩
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply pairLift_injective (highLetter h s) (highLetter_injective h s)
  have hh := congrArg (fun l => (l x).val) hz
  exact hh.trans (map_zero _).symm

lemma shiftedStairWord_alphabet (h s : ℕ) :
    shiftedStairWord h s ∈ alphabetSub _ _ (fun a => s ≤ ((finProdFinEquiv.symm a).1).val) := by
  unfold shiftedStairWord staircaseWord
  rw [pairLift_wordTensor]
  apply pairWord_mem_alphabetLeft (fun a => s ≤ a.val)
  apply letterLift_mem_alphabet
  intro i
  dsimp [highLetter]
  omega

lemma bandRowWord_alphabet (h s : ℕ) :
    bandRowWord h s ∈ alphabetSub _ _ (fun a => ¬s ≤ a.val) := by
  apply altWord_mem_alphabet
  intro j
  have hb := (bandTableau_bounds h s j).1
  have hr := rotateRow_high h s (bandTableau h s j)
  have hh : ¬ s ≤ (rotateRow h s (bandTableau h s j)).val.2 :=
    fun hh => (Nat.not_lt.mpr hb) (hr.mp hh)
  simpa [rightWord,rowWord,stairRowTableau,rotateRowPositions,bandTableau,staircaseSwap] using hh

lemma stairBandWord_alphabet (h s : ℕ) :
    stairBandWord h s ∈ alphabetSub _ _ (fun a => ¬ s ≤ ((finProdFinEquiv.symm a).1).val) := by
  apply pairWord_mem_alphabetLeft (fun a => ¬s ≤ a.val)
  exact bandRowWord_alphabet h s

/- The actual same-high image factors as the smaller Specht tensor cyclic
vector and the exact retained band vector on independent position blocks. -/
theorem staircase_cut_factor (h s : ℕ) :
    sameHighProjection _ _ _ s (staircaseWord (h+s)) =
      positionProduct (cutPositions h s) (shiftedStairWord h s) (stairBandWord h s) := by
  rw [staircase_cut_layers,cutRowWord_factor,cutColumnWord_factor]
  unfold shiftedStairWord staircaseWord
  rw [pairLift_wordTensor]
  ext w
  simp only [wordTensor_tmul, stairBandWord, positionProduct]
  exact mul_mul_mul_comm _ _ _ _



lemma bandColumnWord_alphabet (h s : ℕ) :
    bandColumnWord h s ∈ alphabetSub _ _ (fun a => ¬s ≤ a.val) := by
  apply altWord_mem_alphabet
  intro j
  have hb := (bandTableau_bounds h s j).1
  have hr := rotateColumn_high h s (bandTableau h s j)
  have hh : ¬ s ≤ (rotateColumn h s (bandTableau h s j)).val.1 :=
    fun hh => (Nat.not_lt.mpr hb) (hr.mp hh)
  simpa [rightWord,rowWord,rotateColumnPositions,bandTableau] using hh

lemma alphabet_small_invariant {n d : ℕ} (A : Fin d → Prop)
    (hA : ∀ a b, A a → A b → a = b) (x : WordSpace n d)
    (hx : x ∈ alphabetSub n d A) (g : Equiv.Perm (Fin n)) : wordRep n d g x = x := by
  ext w
  change x (w ∘ g) = x w
  have he : (∀ i, A (w i)) → w ∘ g = w := by
    intro h
    funext i
    exact hA _ _ (h (g i)) (h i)
  by_cases h : ∀ i, A (w i)
  · rw [he h]
  · have hz : x w = 0 := by
      by_contra hn
      exact h ((alphabetSub_iff A x).mp hx w hn)
    rw [hz]
    by_contra hn
    have hh := (alphabetSub_iff A x).mp hx (w ∘ g) hn
    apply h
    intro i
    simpa using hh (g⁻¹ i)

lemma oneBand_invariant (h : ℕ) (g : Equiv.Perm (Fin (bandSize h 1))) :
    wordRep _ _ g (stairBandWord h 1) = stairBandWord h 1 := by
  have ha (a b : Fin ((staircase (h+1)).colLen 0)) (ha : ¬1 ≤ a.val) (hb : ¬1 ≤ b.val) : a = b := by
    apply Fin.ext; omega
  have hr := alphabet_small_invariant (fun a => ¬1 ≤ a.val) ha _ (bandRowWord_alphabet h 1) g
  have hc := alphabet_small_invariant (fun a => ¬1 ≤ a.val) ha _ (bandColumnWord_alphabet h 1) g
  ext w
  change stairBandWord h 1 (w ∘ g) = stairBandWord h 1 w
  simp only [stairBandWord,wordTensor_tmul]
  exact congrArg₂ (fun x y : ℂ => x*y) (congrFun hr (splitLeft w)) (congrFun hc (splitRight w))

lemma stairBandWord_ne_zero (h s : ℕ) : stairBandWord h s ≠ 0 := by
  intro hz
  apply staircase_projected_ne_zero h s
  rw [staircase_cut_factor,hz]
  ext w
  change _ * 0 = 0
  exact mul_zero _

lemma oneRow_support_invariant {n d : ℕ} (μ : YoungDiagram) (t : Tableau n μ)
    (hμ : μ.colLen 0 ≤ 1) (u : WordSpace n d) (hu : u ≠ 0)
    (he : ∀ g, wordRep n d g u = u) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0 := by
  have hw (g : Equiv.Perm (Fin n)) : rowWord t ∘ g = rowWord t := by
    funext i
    apply Fin.ext
    have h₁ := (rowWord t (g i)).isLt
    have h₂ := (rowWord t i).isLt
    omega
  let F : Specht t →ₗ[ℂ] (cyclic (wordRep n d) u).toSubmodule :=
    { toFun := fun x => ⟨x.val (rowWord t) • u, Submodule.smul_mem _ _ (mem_cyclic _ _)⟩
      map_add' := by intro x y; apply Subtype.ext; exact add_smul _ _ _
      map_smul' := by intro c x; apply Subtype.ext; exact mul_smul _ _ _ }
  let f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep n d) u).toRepresentation :=
    { toLinearMap := F
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change x.val (rowWord t ∘ g) • u = wordRep n d g (x.val (rowWord t) • u)
        rw [hw,map_smul,he] }
  refine ⟨f, ?_⟩
  intro hz
  have hh := congrArg (fun f => (f ⟨polytabloid t,mem_cyclic _ _⟩).val) hz
  change polytabloid t (rowWord t) • u = 0 at hh
  rw [polytabloid_rowWord,one_smul] at hh
  exact hu hh

/- The width-one band is the genuine trivial constituent required by Pieri. -/
theorem oneBand_support (h : ℕ) (μ : YoungDiagram) (t : Tableau (bandSize h 1) μ)
    (hμ : μ.colLen 0 ≤ 1) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (stairBandWord h 1)).toRepresentation, f ≠ 0 :=
  oneRow_support_invariant μ t hμ _ (stairBandWord_ne_zero h 1) (oneBand_invariant h)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SpechtClassification
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.tableauInclusion_cell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV uG

namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/



lemma columnAlt_eq_zero_of_rows {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (hd : d < μ.colLen 0) : columnAlt (d := d) t = 0 := by
  classical
  have hz : ∀ a : Fin n → Fin d, columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
    intro a
    let j : Fin (μ.colLen 0) → Fin n := fun i => t.symm
      ⟨(i.val, 0), YoungDiagram.mem_iff_lt_colLen.mpr i.isLt⟩
    have hnot : ¬ Function.Injective (a ∘ j) := by
      intro hi
      have hh := Fintype.card_le_of_injective _ hi
      simp only [Fintype.card_fin] at hh
      omega
    simp only [Function.Injective] at hnot
    push Not at hnot
    obtain ⟨i, k, ha, hik⟩ := hnot
    have hj : j i ≠ j k := by
      intro he
      apply hik
      apply Fin.ext
      have hh := congrArg (fun l => (t l).val.1) he
      simpa [j] using hh
    exact columnAlt_collision t a (j i) (j k) hj (by simp [j]) ha
  apply LinearMap.ext
  intro x
  have he : x = ∑ a, x a • Pi.single a (1 : ℂ) := by
    ext b
    simp [Pi.single_apply]
  rw [he, map_sum]
  simp only [map_smul, hz, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

/- A Specht constituent of a `d`-letter position representation has at most
`d` rows, proved by the genuine first-column antisymmetrizer. -/
theorem specht_rows_of_hom {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep t) (wordRep n d)) (hf : f ≠ 0) :
    μ.colLen 0 ≤ d := by
  classical
  let := specht_irreducible t
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  by_contra h
  have hd : d < μ.colLen 0 := lt_of_not_ge h
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  have he := columnOperator_intertwining t f p
  change f (columnOperator t (spechtRep t) p) = columnAlt t (f p) at he
  rw [columnAlt_eq_zero_of_rows t hd, LinearMap.zero_apply] at he
  have hz : columnOperator t (spechtRep t) p = 0 := hi (he.trans (map_zero f).symm)
  exact columnAlt_polytabloid_ne_zero t
    ((columnOperator_subtype t (spechtSub t) p).symm.trans (congrArg Subtype.val hz))

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SupportSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uR uX uY uG uV

namespace Saxl

theorem word_support_separates {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0)
    (x : WordSpace n d) (hx : x ≠ 0) :
    ∃ f : Representation.IntertwiningMap (wordRep n d) σ, f x ≠ 0 := by
  apply intertwining_separates_of_simple_support (wordRep n d) σ ?_ x hx
  intro S hS
  let := hS
  obtain ⟨p, ⟨e⟩⟩ := irreducible_equiv_specht S.toRepresentation
  let t := partitionTableau p
  let i : Representation.IntertwiningMap (spechtRep t) (wordRep n d) :=
    (subrepInclusion S).comp e.symm.toIntertwiningMap
  have hi : i ≠ 0 := by
    intro he
    have hz := congrArg (fun F : Representation.IntertwiningMap (spechtRep t) (wordRep n d) =>
      F ⟨polytabloid t, mem_cyclic _ _⟩) he
    have h0 : e.symm ⟨polytabloid t, mem_cyclic _ _⟩ = 0 := Subtype.ext hz
    have h1 := e.symm.injective (h0.trans (map_zero _).symm)
    exact polytabloid_ne_zero t (congrArg Subtype.val h1)
  obtain ⟨f, hf⟩ := h _ t (specht_rows_of_hom t i hi)
  refine ⟨f.comp e.toIntertwiningMap, ?_⟩
  intro he
  apply hf
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  exact congrArg (fun F : Representation.IntertwiningMap S.toRepresentation σ => F z) he

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandOrbit
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma bandOrbitMap_base {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y)
    (hF : ∀ g : Equiv.Perm (Fin b), c ∘ g = c → ∀ x, F (ρ (sumPerm e 1 g) x) = F x)
    (x : X) : bandOrbitMap e ρ c F x c =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin b) => c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c)).card : ℂ) • F x := by
  classical
  change (∑ g : Equiv.Perm (Fin b), _) = _
  have hh (g : Equiv.Perm (Fin b)) :
      ((Pi.single (c ∘ (g⁻¹ : Equiv.Perm (Fin b))) (1:ℂ) : WordSpace b k) c) • F (ρ (sumPerm e 1 g⁻¹) x) =
      if c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c then F x else 0 := by
    by_cases h : c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c
    · rw [ite_eq_left h, h, Pi.single_eq_same, one_smul, hF g⁻¹ h]
    · rw [ite_eq_right h, Pi.single_eq_of_ne (Ne.symm h), zero_smul]
  simp only [hh]
  simp [Finset.sum_ite,Nat.cast_smul_eq_nsmul]

lemma bandOrbitMap_nonzero {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) (hF0 : F ≠ 0)
    (hF : ∀ g : Equiv.Perm (Fin b), c ∘ g = c → ∀ x, F (ρ (sumPerm e 1 g) x) = F x) :
    bandOrbitMap e ρ c F ≠ 0 := by
  classical
  intro hz
  apply hF0
  ext x
  have hh := bandOrbitMap_base e ρ c F hF x
  rw [hz] at hh
  change 0 = _ at hh
  have hc : ((Finset.univ.filter (fun g : Equiv.Perm (Fin b) =>
      c ∘ (g⁻¹ : Equiv.Perm (Fin b)) = c)).card : ℂ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    exact Finset.card_ne_zero.mpr ⟨1,Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  exact (smul_eq_zero.mp hh.symm).resolve_left hc

lemma bandOrbitMap_equivariant {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (τ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y)
    (hF : ∀ h : Equiv.Perm (Fin a), ∀ x, F (ρ (sumPerm e h 1) x) = τ h (F x))
    (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : X) (w : Fin b → Fin k) :
    bandOrbitMap e ρ c F (ρ (sumPerm e h q) x) w =
      τ h (bandOrbitMap e ρ c F x (w ∘ q)) := by
  classical
  change (∑ g : Equiv.Perm (Fin b), _) = τ h (∑ g : Equiv.Perm (Fin b), _)
  rw [map_sum]
  apply (Equiv.sum_comp (Equiv.mulLeft q) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  have he : sumPerm e 1 (q*g)⁻¹ * sumPerm e h q = sumPerm e h 1 * sumPerm e 1 g⁻¹ := by
    rw [← sumPerm_mul, ← sumPerm_mul]
    simp only [one_mul,mul_one,mul_inv_rev,mul_assoc,inv_mul_cancel,mul_one]
  change _ • F (ρ (sumPerm e 1 (q*g)⁻¹) (ρ (sumPerm e h q) x)) = _
  rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hF, map_smul]
  congr 1
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro hh
    funext i
    have hi := congrFun hh (q i)
    simpa using hi
  · intro hh
    funext i
    have hi := congrFun hh (q⁻¹ i)
    simpa using hi

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandGlue
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl

/- Apply a band intertwiner to every scalar high-coordinate of a colored
strip orbit map. This is the concrete tensor product of the two maps. -/

lemma bandGlue_sum {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d) (x : X) :
    bandGlue e T L x = ∑ c : Fin b → Fin k, positionProduct e (T x c) (L (Pi.single c 1)) := by
  classical
  ext w
  change L (fun cb => T x cb (leftWord e w)) (rightWord e w) = _
  have he : (fun cb => T x cb (leftWord e w)) =
      ∑ c : Fin b → Fin k, T x c (leftWord e w) • (Pi.single c (1:ℂ) : WordSpace b k) := by
    ext c
    simp [Pi.single_apply]
  rw [he, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, positionProduct]

lemma bandGlue_equivariant {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (L : Representation.IntertwiningMap (wordRep b k) (wordRep b d))
    (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : X) :
    bandGlue e T L.toLinearMap (ρ (sumPerm e h q) x) =
      wordRep n d (sumPerm e h q) (bandGlue e T L.toLinearMap x) := by
  ext w
  change L (fun cb => T (ρ (sumPerm e h q) x) cb (leftWord e w)) (rightWord e w) = _
  simp only [hT]
  have he : (fun cb => (wordRep a d h (T x (cb ∘ q))) (leftWord e w)) =
      wordRep b k q (fun cb => T x cb ((leftWord e w) ∘ h)) := rfl
  rw [he]
  have hL : L (wordRep b k q (fun cb => T x cb ((leftWord e w) ∘ h))) =
      wordRep b d q (L (fun cb => T x cb ((leftWord e w) ∘ h))) :=
    LinearMap.congr_fun (L.isIntertwining' q) _
  rw [hL]
  change L (fun cb => T x cb ((leftWord e w) ∘ h)) ((rightWord e w) ∘ q) =
    L (fun cb => T x cb (leftWord e (w ∘ sumPerm e h q))) (rightWord e (w ∘ sumPerm e h q))
  have hl : leftWord e (w ∘ sumPerm e h q) = (leftWord e w) ∘ h := by
    funext i
    simp [leftWord,sumPerm_left]
  have hr : rightWord e (w ∘ sumPerm e h q) = (rightWord e w) ∘ q := by
    funext i
    simp [rightWord,sumPerm_right]
  rw [hl,hr]

lemma bandGlue_mem {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ x c, T x c ∈ cyclic (wordRep a d) v)
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d)
    (hL : ∀ y, L y ∈ cyclic (wordRep b d) u) (x : X) :
    bandGlue e T L x ∈ cyclic (wordRep n d) (positionProduct e v u) := by
  rw [bandGlue_sum]
  apply Submodule.sum_mem
  intro c hc
  exact product_mem_cyclic e v u _ _ (hT x c) (hL _)

/- A module containing every band Specht type of the relevant height detects
any nonzero high-valued colored-band vector. No multiplicity hypothesis is needed. -/

lemma positionProduct_sector {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (A : Fin d → Prop) (x : WordSpace a d) (y : WordSpace b d)
    (hx : x ∈ alphabetSub a d A) (hy : y ∈ alphabetSub b d (fun z => ¬A z)) :
    positionProduct e x y ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
  intro w hw
  by_contra hn
  apply hw
  have hxy : x (leftWord e w) ≠ 0 ∧ y (rightWord e w) ≠ 0 := mul_ne_zero_iff.mp hn
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inl, iff_true,leftWord] using
      (alphabetSub_iff A x).mp hx _ hxy.1 j
  | inr j =>
    simpa only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, iff_false,rightWord] using
      (alphabetSub_iff (fun z => ¬A z) y).mp hy _ hxy.2 j

lemma bandGlue_sector {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (A : Fin d → Prop)
    (v : WordSpace a d) (u : WordSpace b d)
    (hv : v ∈ alphabetSub a d A) (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d))
    (hT : ∀ x c, T x c ∈ cyclic (wordRep a d) v)
    (L : WordSpace b k →ₗ[ℂ] WordSpace b d)
    (hL : ∀ y, L y ∈ cyclic (wordRep b d) u) (x : X) :
    bandGlue e T L x ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A) := by
  rw [bandGlue_sum]
  apply Submodule.sum_mem
  intro c hc
  apply positionProduct_sector
  · exact cyclic_alphabet A v hv _ (hT x c)
  · exact cyclic_alphabet (fun z => ¬A z) u hu _ (hL _)

theorem bandGlue_sector_exists {n a b k d : ℕ} {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hvA : v ∈ alphabetSub a d A)
    (huA : u ∈ alphabetSub b d (fun z => ¬A z))
    (hband : ∀ (μ : YoungDiagram) (t : Tableau b μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep b d) u).toRepresentation, f ≠ 0)
    (T : X →ₗ[ℂ] ((Fin b → Fin k) → WordSpace a d)) (hT0 : T ≠ 0)
    (hT : ∀ h q x w, T (ρ (sumPerm e h q) x) w = wordRep a d h (T x (w ∘ q)))
    (hTm : ∀ x c, T x c ∈ cyclic (wordRep a d) v) :
    ∃ f : X →ₗ[ℂ] WordSpace n d, f ≠ 0 ∧
      (∀ h q x, f (ρ (sumPerm e h q) x) = wordRep n d (sumPerm e h q) (f x)) ∧
      (∀ x, f x ∈ cyclic (wordRep n d) (positionProduct e v u)) ∧
      (∀ x, f x ∈ coordinateSub n d (wordSector (fun i => (e i).isLeft = true) A)) := by
  classical
  obtain ⟨x,c,w,hxc⟩ : ∃ x c w, T x c w ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hT0
    ext x c w
    exact hh x c w
  have hv : (fun cb => T x cb w) ≠ (0 : WordSpace b k) := by
    intro hz
    exact hxc (congrFun hz c)
  obtain ⟨L,hL⟩ := word_support_separates (cyclic (wordRep b d) u).toRepresentation hband _ hv
  let L' := (subrepInclusion (cyclic (wordRep b d) u)).comp L
  have hL' : L' (fun cb => T x cb w) ≠ 0 := by
    intro hz
    apply hL
    exact Subtype.ext hz
  obtain ⟨z,hz⟩ : ∃ z, L' (fun cb => T x cb w) z ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hL' (funext hh)
  refine ⟨bandGlue e T L'.toLinearMap, ?_, bandGlue_equivariant e ρ T hT L', ?_, ?_⟩
  · intro he
    apply hz
    have hh := congrArg (fun f : X →ₗ[ℂ] WordSpace n d => f x (joinPositions e w z)) he
    change L' (fun cb => T x cb (leftWord e (joinPositions e w z))) (rightWord e (joinPositions e w z)) = 0 at hh
    simpa only [leftWord_join, rightWord_join] using hh
  · exact bandGlue_mem e v u T hTm L'.toLinearMap (fun y => (L y).property)

  · exact bandGlue_sector e A v u hvA huA T hTm L'.toLinearMap (fun y => (L y).property)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StripExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma restrictPerm_apply {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin n))
    (hg : ∀ x, g x ∈ Set.range i ↔ x ∈ Set.range i) (k : Fin a) :
    i (restrictPerm i g hg k) = g (i k) := by
  change ((Equiv.ofInjective i i.injective)
    ((Equiv.ofInjective i i.injective).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

lemma tableauInclusion_trans {a b n : ℕ} {ν η μ : YoungDiagram}
    (s : Tableau a ν) (u : Tableau b η) (t : Tableau n μ)
    (h₁ : ν ≤ η) (h₂ : η ≤ μ) (k : Fin a) :
    tableauInclusion u t h₂ (tableauInclusion s u h₁ k) =
      tableauInclusion s t (h₁.trans h₂) k := by
  change t.symm ⟨(u (u.symm ⟨(s k).val, _⟩)).val, _⟩ = t.symm ⟨(s k).val, _⟩
  simp only [Equiv.apply_symm_apply]

lemma extendColor_apply {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (x : Fin a) : extendColor i c q (i x) = c x := by
  classical
  unfold extendColor
  rw [dite_eq_left ⟨x,rfl⟩]
  congr 1
  exact (Equiv.ofInjective i i.injective).symm_apply_apply x

lemma extendColor_mem {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) :
    extendColor i c (q+1) x ≤ q ↔ x ∈ Set.range i := by
  classical
  unfold extendColor
  split_ifs with h
  · exact iff_of_true (hc _) h
  · simp [h]

lemma extendColor_le {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) : extendColor i c (q+1) x ≤ q+1 := by
  classical
  unfold extendColor
  split_ifs
  · exact (hc _).trans (Nat.le_succ q)
  · exact le_rfl

lemma extendColor_count_old {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q j : ℕ)
    (hj : j ≠ q) :
    (Finset.univ.filter (fun x => extendColor i c q x = j)).card =
      (Finset.univ.filter (fun x => c x = j)).card := by
  classical
  symm
  apply Finset.card_bij (fun x _ => i x)
  · intro x hx
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hx
  · intro x hx y hy hxy
    exact i.injective hxy
  · intro y hy
    have hyj := (Finset.mem_filter.mp hy).2
    have hym : y ∈ Set.range i := by
      by_contra hn
      simp only [extendColor, dite_eq_right hn] at hyj
      exact hj hyj.symm
    obtain ⟨x,rfl⟩ := hym
    refine ⟨x, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, extendColor_apply] using hyj

lemma extendColor_count_new {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) :
    (Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1)).card = n-a := by
  classical
  have he : Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1) =
      Finset.univ \ Finset.univ.map i := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_map]
    change extendColor i c (q+1) x = q+1 ↔ ¬ x ∈ Set.range i
    rw [← extendColor_mem i c q hc x]
    have hl := extendColor_le i c q hc x
    omega
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SizedStrips
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl



theorem stripChain_restriction_any {bs ν μ} (hs : SizedStripChain bs ν μ)
    {a n : ℕ} (s : Tableau a ν) (t : Tableau n μ) :
    ∃ (c : Fin n → ℕ) (F : Specht t →ₗ[ℂ] Specht s),
      Function.Surjective F ∧
      (∀ i, c i ≤ bs.length) ∧
      (∀ i, c i = 0 ↔ i ∈ Set.range (tableauInclusion s t hs.le)) ∧
      (∀ j (hj : j < bs.length), (Finset.univ.filter (fun i => c i = j+1)).card = bs[j]) ∧
      (∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ i, c (g i) = c i) →
        (∀ k, g (tableauInclusion s t hs.le k) =
          tableauInclusion s t hs.le (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x)) := by
  classical
  induction hs generalizing a n with
  | nil ν =>
    obtain ⟨F,hF,hFe⟩ := pieri_strip_surjective_uts s t
      (show HorizontalStrip ν ν from ⟨le_rfl, by intros x hx hn; exact False.elim (hn hx)⟩)
    refine ⟨fun _ => 0, F, hF, by simp, ?_, ?_, ?_⟩
    · intro i
      constructor
      · intro _
        refine ⟨s.symm (t i), ?_⟩
        change t.symm ⟨(s (s.symm (t i))).val, _⟩ = i
        simp only [Equiv.apply_symm_apply]
        exact t.symm_apply_apply i
      · intro _; rfl
    · intro j hj; simp at hj
    · intro g h hc he x
      exact hFe g h he x
  | @snoc bs ν η μ b hs hh hcard ih =>
    obtain ⟨c,F,hF,hc,hzero,hcount,he⟩ := ih s (shapeTableau η)
    obtain ⟨P,hP,hPe⟩ := pieri_strip_surjective_uts (shapeTableau η) t hh
    let i := tableauInclusion (shapeTableau η) t hh.1
    let c' := extendColor i c (bs.length+1)
    refine ⟨c', F.comp P, hF.comp hP, ?_, ?_, ?_, ?_⟩
    · intro k
      simpa only [List.length_append, List.length_singleton] using extendColor_le i c bs.length hc k
    · intro k
      constructor
      · intro hk
        change extendColor i c (bs.length+1) k = 0 at hk
        have hr : k ∈ Set.range i := (extendColor_mem i c bs.length hc k).mp (by omega)
        obtain ⟨l,rfl⟩ := hr
        have hl : c l = 0 := (extendColor_apply i c _ l).symm.trans hk
        obtain ⟨j,hj⟩ := (hzero l).mp hl
        refine ⟨j, ?_⟩
        rw [← tableauInclusion_trans s (shapeTableau η) t hs.le hh.1]
        exact congrArg i hj
      · rintro ⟨j,rfl⟩
        rw [← tableauInclusion_trans s (shapeTableau η) t hs.le hh.1]
        change extendColor i c _ (i _) = 0
        rw [extendColor_apply]
        exact (hzero _).mpr ⟨j,rfl⟩
    · intro j hj
      have hjle : j ≤ bs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      rcases lt_or_eq_of_le hjle with hjlt | rfl
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = j+1)).card = _
        rw [extendColor_count_old i c (bs.length+1) (j+1) (by omega), hcount j hjlt,
          List.getElem_append_left hjlt]
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = bs.length+1)).card = _
        rw [extendColor_count_new i c bs.length hc]
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        have ht : n = μ.card := by
          have := Fintype.card_congr t
          simpa only [Fintype.card_fin, Fintype.card_coe] using this
        omega
    · intro g h hg hgi x
      have hgmem : ∀ k, g k ∈ Set.range i ↔ k ∈ Set.range i := by
        intro k
        rw [← extendColor_mem i c bs.length hc, ← extendColor_mem i c bs.length hc]
        exact (congrArg (fun c => c ≤ bs.length) (hg k)).to_iff
      let k := restrictPerm i g hgmem
      have hik (l) : i (k l) = g (i l) := restrictPerm_apply i g hgmem l
      have hkcolor (l) : c (k l) = c l := by
        rw [← extendColor_apply i c (bs.length+1) (k l), hik, ← extendColor_apply i c (bs.length+1) l]
        exact hg (i l)
      have hkbase (l) : k (tableauInclusion s (shapeTableau η) hs.le l) =
          tableauInclusion s (shapeTableau η) hs.le (h l) := by
        apply i.injective
        rw [hik]
        change g (tableauInclusion (shapeTableau η) t hh.1 _) =
          tableauInclusion (shapeTableau η) t hh.1 _
        rw [tableauInclusion_trans, tableauInclusion_trans]
        exact hgi l
      change F (P (spechtRep t g x)) = _
      rw [hPe g k (fun l => (hik l).symm), he k h hkcolor hkbase]
      rfl

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StripSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Place the smaller tableau on any chosen block, with the remaining strip
colors on its complement. No transitivity or induction rule is assumed. -/
theorem placed_strip_restriction {n a b : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ (c : Fin b → Fin bs.length) (F : Specht t →ₗ[ℂ] Specht s), Function.Surjective F ∧
      ∀ (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)), c ∘ q = c →
        ∀ x, F (spechtRep t (sumPerm e h q) x) = spechtRep s h (F x) := by
  classical
  obtain ⟨c,F,hF,hcb,hcz,hcount,hFe⟩ := stripChain_restriction_any hs s t
  let i := tableauInclusion s t hs.le
  let l : Fin a → Fin n := fun j => e.symm (Sum.inl j)
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair l i
    (fun x y h => Sum.inl.inj (e.symm.injective h)) i.injective
  have hcL (j : Fin a) : c (p (e.symm (Sum.inl j))) = 0 := by
    rw [show p (e.symm (Sum.inl j)) = i j from hp j]
    exact (hcz _).mpr ⟨j,rfl⟩
  have hcRpos (j : Fin b) : 0 < c (p (e.symm (Sum.inr j))) := by
    by_contra hn
    have hz : c (p (e.symm (Sum.inr j))) = 0 := by omega
    obtain ⟨k,hk⟩ := (hcz _).mp hz
    have hh : e.symm (Sum.inl k) = e.symm (Sum.inr j) := p.injective ((hp k).trans hk)
    have := e.symm.injective hh
    cases this
  let cb : Fin b → Fin bs.length := fun j => ⟨c (p (e.symm (Sum.inr j)))-1, by
    have := hcRpos j
    have := hcb (p (e.symm (Sum.inr j)))
    omega⟩
  have hcR (j : Fin b) : c (p (e.symm (Sum.inr j))) = (cb j).val+1 := by
    have := hcRpos j
    change _ = (c (p (e.symm (Sum.inr j)))-1)+1
    omega
  let F' := F.comp (spechtRep t p)
  have hP : Function.Surjective (spechtRep t p) := by
    intro x
    refine ⟨spechtRep t p⁻¹ x, ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨cb,F',hF.comp hP, ?_⟩
  intro h q hq x
  let g := p * sumPerm e h q * p⁻¹
  have hgL (j : Fin a) : g (p (e.symm (Sum.inl j))) = p (e.symm (Sum.inl (h j))) := by
    simp [g]
  have hgR (j : Fin b) : g (p (e.symm (Sum.inr j))) = p (e.symm (Sum.inr (q j))) := by
    simp [g]
  have hgc (j : Fin n) : c (g j) = c j := by
    obtain ⟨z,rfl⟩ := p.surjective j
    obtain ⟨z,rfl⟩ := e.symm.surjective z
    cases z with
    | inl j => rw [hgL,hcL,hcL]
    | inr j =>
      rw [hgR,hcR,hcR]
      exact congrArg (fun x : Fin bs.length => x.val+1) (congrFun hq j)
  have hgi (j : Fin a) : g (i j) = i (h j) := by rw [← hp j,← hp (h j)]; exact hgL j
  change F (spechtRep t p (spechtRep t (sumPerm e h q) x)) = spechtRep s h (F (spechtRep t p x))
  have hmul : p * sumPerm e h q = g * p := by simp [g,mul_assoc]
  rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]
  exact hFe g h hgc hgi _

end Saxl

namespace Saxl

/- Required support transfer from a genuine iterated horizontal-strip
restriction and genuine independent high/band cyclic factors. -/
theorem strip_product_support {n a b d : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (f : Representation.IntertwiningMap (spechtRep s) (cyclic (wordRep a d) v).toRepresentation)
    (hf : f ≠ 0)
    (hband : ∀ (η : YoungDiagram) (r : Tableau b η), η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r) (cyclic (wordRep b d) u).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, F ≠ 0 := by
  classical
  obtain ⟨c,F,hF,hFe⟩ := placed_strip_restriction hs s t e
  let G := (subrepInclusion (cyclic (wordRep a d) v)).comp f
  let F₀ : Specht t →ₗ[ℂ] WordSpace a d := G.toLinearMap.comp F
  have hF₀ : F₀ ≠ 0 := by
    intro hz
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := hF y
    apply Subtype.ext
    exact LinearMap.congr_fun hz x
  have hFb (q : Equiv.Perm (Fin b)) (hq : c ∘ q = c) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e 1 q) x) = F₀ x := by
    change G (F (spechtRep t (sumPerm e 1 q) x)) = G (F x)
    rw [hFe 1 q hq, map_one]
    rfl
  have hFa (h : Equiv.Perm (Fin a)) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e h 1) x) = wordRep a d h (F₀ x) := by
    change G (F (spechtRep t (sumPerm e h 1) x)) = wordRep a d h (G (F x))
    rw [hFe h 1 rfl]
    exact LinearMap.congr_fun (G.isIntertwining' h) (F x)
  let T := bandOrbitMap e (spechtRep t) c F₀
  have hTm (x : Specht t) (w : Fin b → Fin bs.length) : T x w ∈ cyclic (wordRep a d) v := by
    change (∑ g : Equiv.Perm (Fin b), _) ∈ (cyclic (wordRep a d) v).toSubmodule
    apply Submodule.sum_mem
    intro g hg
    apply Submodule.smul_mem
    exact (f (F (spechtRep t (sumPerm e 1 g⁻¹) x))).property
  obtain ⟨L,hL,hLe,hLm,hLs⟩ := bandGlue_sector_exists e (spechtRep t) v u A hv hu hband T
    (bandOrbitMap_nonzero e (spechtRep t) c F₀ hF₀ hFb)
    (bandOrbitMap_equivariant e (spechtRep t) (wordRep a d) c F₀ hFa) hTm
  apply sector_support_transfer (spechtRep t) (fun i => (e i).isLeft = true) A
    (positionProduct e v u) L hL _ hLm
  · intro x w hw
    by_contra hn
    exact hw (hLs x w hn)
  · intro g hg x
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g,hg⟩
    have heq : sumPerm e (leftRestriction e g') (rightRestriction e g') = g := sumPerm_restrictions e g'
    rw [← heq]
    exact hLe _ _ x

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

lemma stripRow_bounds (μ : YoungDiagram) (t i : ℕ) :
    μ.rowLen (i+1) ≤ stripRow μ t i ∧ stripRow μ t i ≤ μ.rowLen i := by
  have h := μ.rowLen_anti i (i+1) (by omega)
  dsimp [stripRow]
  omega

@[simp] lemma mem_stripRemove {μ : YoungDiagram} {t i j : ℕ} :
    (i,j) ∈ stripRemove μ t ↔ j < stripRow μ t i := by
  change (i,j) ∈ μ.cells.filter _ ↔ _
  simp only [Finset.mem_filter, YoungDiagram.mem_cells]
  exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_rowLen.mpr
    (lt_of_lt_of_le h (stripRow_bounds μ t i).2), h⟩⟩

@[simp] lemma stripRemove_rowLen (μ : YoungDiagram) (t i : ℕ) :
    (stripRemove μ t).rowLen i = stripRow μ t i := by
  have hh : ∀ j, j < (stripRemove μ t).rowLen i ↔ j < stripRow μ t i := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_stripRemove]
  have h₁ := hh ((stripRemove μ t).rowLen i)
  have h₂ := hh (stripRow μ t i)
  omega

lemma stripRemove_le (μ : YoungDiagram) (t : ℕ) : stripRemove μ t ≤ μ := by
  intro x hx
  exact (Finset.mem_filter.mp hx).1

lemma stripRemove_horizontal (μ : YoungDiagram) (t : ℕ) : HorizontalStrip (stripRemove μ t) μ := by
  refine ⟨stripRemove_le μ t, ?_⟩
  intro x hx hxn y hy hyn hcol
  have hhx := YoungDiagram.mem_iff_lt_rowLen.mp hx
  have hhy := YoungDiagram.mem_iff_lt_rowLen.mp hy
  have hnx : stripRow μ t x.1 ≤ x.2 := le_of_not_gt (fun h => hxn (mem_stripRemove.mpr h))
  have hny : stripRow μ t y.1 ≤ y.2 := le_of_not_gt (fun h => hyn (mem_stripRemove.mpr h))
  have hr : x.1 = y.1 := by
    rcases lt_trichotomy x.1 y.1 with hr | hr | hr
    · have hh := μ.rowLen_anti (x.1+1) y.1 (by omega)
      have hb := (stripRow_bounds μ t x.1).1
      omega
    · exact hr
    · have hh := μ.rowLen_anti (y.1+1) x.1 (by omega)
      have hb := (stripRow_bounds μ t y.1).1
      omega
  exact Prod.ext hr hcol

lemma stripRemove_prefix (μ : YoungDiagram) (t k : ℕ) :
    rowPrefix (stripRemove μ t) k + min t (μ.rowLen 0) =
      rowPrefix μ k + min t (μ.rowLen k) := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    have hr : (stripRemove μ t).rowLen k + min t (μ.rowLen k) =
        μ.rowLen k + min t (μ.rowLen (k+1)) := by
      rw [stripRemove_rowLen]
      dsimp [stripRow]
      omega
    simp only [rowPrefix, Finset.sum_range_succ] at ih ⊢
    omega

lemma stripRemove_card (μ : YoungDiagram) (t : ℕ) :
    (stripRemove μ t).card + min t (μ.rowLen 0) = μ.card := by
  have hh := stripRemove_prefix μ t (μ.colLen 0)
  rw [rowPrefix_eq_card μ le_rfl, rowLen_zero_of_height_le μ le_rfl, min_zero, add_zero] at hh
  have ht : (stripRemove μ t).colLen 0 ≤ μ.colLen 0 := by
    by_contra h
    have hm : (μ.colLen 0, 0) ∈ stripRemove μ t := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    have hh := YoungDiagram.mem_iff_lt_colLen.mp (stripRemove_le μ t hm)
    omega
  rwa [rowPrefix_eq_card _ ht] at hh


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
-- module Solutions.OAIQ259_US.Saxl_StripReduction
attribute [-simp] _root_.OAI.UniversalTensorSquare.candidate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl


lemma stripRemove_full_prefix (μ : YoungDiagram) (q : ℕ) :
    rowPrefix (stripRemove μ (μ.rowLen 0)) q + μ.rowLen 0 = rowPrefix μ (q+1) := by
  have hh := stripRemove_prefix μ (μ.rowLen 0) q
  rw [min_self, min_eq_right (μ.rowLen_anti 0 q (Nat.zero_le _))] at hh
  exact hh.trans (rowPrefix_succ μ q).symm

/- Sweeps remove any prescribed number within the first q-row capacity. -/
theorem stripChain_of_capacity (q t : ℕ) (μ : YoungDiagram)
    (ht : t ≤ rowPrefix μ q) :
    ∃ k ≤ q, ∃ ν, ν.card + t = μ.card ∧ StripChain k ν μ := by
  induction q generalizing t μ with
  | zero =>
    have hz : t = 0 := by simpa [rowPrefix] using ht
    exact ⟨0, le_rfl, μ, by omega, StripChain.nil μ⟩
  | succ q ih =>
    by_cases hz : t = 0
    · exact ⟨0, Nat.zero_le _, μ, by omega, StripChain.nil μ⟩
    by_cases hb : t ≤ μ.rowLen 0
    · let ν := stripRemove μ t
      have hc : ν.card + t = μ.card := by
        simpa only [ν, min_eq_left hb] using stripRemove_card μ t
      have hn : ν ≠ μ := by intro he; rw [he] at hc; omega
      exact ⟨1, by omega, ν, hc,
        StripChain.snoc (StripChain.nil ν) (stripRemove_horizontal μ t) hn⟩
    · let η := stripRemove μ (μ.rowLen 0)
      have hp : rowPrefix η q + μ.rowLen 0 = rowPrefix μ (q+1) :=
        stripRemove_full_prefix μ q
      have hcap : t - μ.rowLen 0 ≤ rowPrefix η q := by omega
      obtain ⟨k, hk, ν, hc, hchain⟩ := ih (t-μ.rowLen 0) η hcap
      have hec : η.card + μ.rowLen 0 = μ.card := by
        simpa only [η, min_self] using stripRemove_card μ (μ.rowLen 0)
      have hpos : 0 < μ.rowLen 0 := by
        by_contra h
        have hz0 : μ.rowLen 0 = 0 := by omega
        have hp0 : rowPrefix μ (q+1) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hh := μ.rowLen_anti 0 i (Nat.zero_le _)
          omega
        omega
      have hn : η ≠ μ := by intro he; rw [he] at hec; omega
      refine ⟨k+1, by omega, ν, ?_, StripChain.snoc hchain (stripRemove_horizontal μ _) hn⟩
      omega

lemma rowPrefix_mean (μ : YoungDiagram) {q k : ℕ} (hqk : q ≤ k) :
    q * rowPrefix μ k ≤ k * rowPrefix μ q := by
  have hlow : q * μ.rowLen q ≤ rowPrefix μ q := by
    calc
      q * μ.rowLen q = ∑ i ∈ Finset.range q, μ.rowLen q := by simp
      _ ≤ rowPrefix μ q := Finset.sum_le_sum (fun i hi =>
        μ.rowLen_anti i q (Nat.le_of_lt (Finset.mem_range.mp hi)))
  have he : rowPrefix μ k = rowPrefix μ q +
      ∑ i ∈ Finset.range (k-q), μ.rowLen (q+i) := by
    simp only [rowPrefix]
    rw [← Finset.sum_range_add]
    congr 2
    omega
  have htail : (∑ i ∈ Finset.range (k-q), μ.rowLen (q+i)) ≤ (k-q)*μ.rowLen q := by
    calc
      _ ≤ ∑ i ∈ Finset.range (k-q), μ.rowLen q :=
        Finset.sum_le_sum (fun i hi => μ.rowLen_anti q (q+i) (by omega))
      _ = _ := by simp
  have hm := Nat.mul_le_mul_left (k-q) hlow
  have hs := Nat.mul_le_mul_left q htail
  rw [he]
  have hsum : q + (k-q) = k := by omega
  nlinarith

lemma staircase_prefix_double (m k : ℕ) (hk : k ≤ m) :
    2 * rowPrefix (staircase m) k = k * (2*m+1-k) := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ, staircase_rowLen]
    have hi := ih (by omega)
    have hs : k + (m-k) = m := by omega
    have ht : k + (2*m+1-k) = 2*m+1 := by omega
    have ht' : (k+1) + (2*m+1-(k+1)) = 2*m+1 := by omega
    nlinarith

/- The exact capacity alternative used by the main induction. -/
lemma strip_reduction_capacity (m : ℕ) (hm : 2 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) (hdom : ¬ Dominates (staircase m) μ)
    (hfirst : μ.rowLen 0 < m) : 5 ≤ m ∧ 2*m-1 ≤ rowPrefix μ 4 := by
  obtain ⟨k, hk⟩ : ∃ k, rowPrefix (staircase m) k < rowPrefix μ k := by
    simpa only [Dominates, not_forall, not_le] using hdom
  have hkm : k < m := by
    by_contra hh
    have hc : (staircase m).colLen 0 ≤ k := by simp; omega
    rw [rowPrefix_eq_card _ hc] at hk
    have hle := rowPrefix_le_card μ k
    omega
  have hbound : rowPrefix μ k ≤ k * (m-1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range k, (m-1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := μ.rowLen_anti 0 i (Nat.zero_le _)
        omega
      _ = _ := by simp
  have hstair := staircase_prefix_double m k (by omega)
  have hk4 : 4 ≤ k := by
    have hm1 : m = (m-1)+1 := by omega
    by_contra hh
    interval_cases k <;> omega
  have hmean := rowPrefix_mean μ hk4
  have hpos : 0 < k := by omega
  have hsum : k + (2*m+1-k) = 2*m+1 := by omega
  constructor
  · omega
  · have ha : 4*(2*m+1-k) < 2*rowPrefix μ 4 := by
      nlinarith
    have hb : 2*m-1 ≤ 2*(2*m+1-k) := by omega
    omega

theorem strip_reduction (m : ℕ) (hm : 2 ≤ m) (μ : YoungDiagram)
    (hμ : μ.card = (staircase m).card) (hdom : ¬ Dominates (staircase m) μ) :
    (∃ ν, ν.card = (staircase (m-1)).card ∧ HorizontalStrip ν μ) ∨
    (5 ≤ m ∧ ∃ q ≤ 4, ∃ ν, ν.card = (staircase (m-2)).card ∧ StripChain q ν μ) := by
  by_cases hfirst : m ≤ μ.rowLen 0
  · left
    let ν := stripRemove μ m
    have hc : ν.card + m = μ.card := by
      simpa only [ν, min_eq_left hfirst] using stripRemove_card μ m
    have hs : (staircase m).card = (staircase (m-1)).card + m := by
      have hh := staircase_card_succ (m-1)
      have he : m-1+1 = m := by omega
      simpa only [he] using hh
    exact ⟨ν, by omega, stripRemove_horizontal μ m⟩
  · right
    obtain ⟨hm5, hcap⟩ := strip_reduction_capacity m hm μ hμ hdom (by omega)
    obtain ⟨q, hq, ν, hc, hs⟩ := stripChain_of_capacity 4 (2*m-1) μ hcap
    refine ⟨hm5, q, hq, ν, ?_, hs⟩
    have hc₁ := staircase_card_double m
    have hc₂ := staircase_card_double (m-2)
    have hh : m = (m-2)+2 := by omega
    have ht : 2*m-1+1 = 2*m := by omega
    nlinarith

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_Main
attribute [-simp] _root_.OAI.UniversalTensorSquare.candidate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

lemma SizedStripChain.of_horizontal {ν μ : YoungDiagram} (hs : HorizontalStrip ν μ) :
    SizedStripChain [μ.card-ν.card] ν μ := by
  have hc : ν.card ≤ μ.card := Finset.card_le_card hs.1
  exact SizedStripChain.snoc (SizedStripChain.nil ν) hs (Nat.add_sub_of_le hc)

lemma StripChain.sized {q ν μ} (hs : StripChain q ν μ) :
    ∃ bs : List ℕ, bs.length = q ∧ SizedStripChain bs ν μ := by
  induction hs with
  | nil μ => exact ⟨[],rfl,SizedStripChain.nil μ⟩
  | @snoc q ν η μ hs hh hn ih =>
    obtain ⟨bs,hbs,hS⟩ := ih
    have hc : η.card ≤ μ.card := Finset.card_le_card hh.1
    exact ⟨bs++[μ.card-η.card], by simp [hbs], SizedStripChain.snoc hS hh (Nat.add_sub_of_le hc)⟩

/- Lift the factor support through the exact same-high quotient. -/
theorem band_cut_support (h s m : ℕ) (he : h+s=m)
    (ν μ : YoungDiagram) (hν : ν.card = (staircase h).card)
    (t : Tableau (staircase m).card μ) (bs : List ℕ) (hs : SizedStripChain bs ν μ)
    (fh : Representation.IntertwiningMap (spechtRep (canonicalTableau ν hν))
      (staircaseCyclic h).toRepresentation) (hfh : fh ≠ 0)
    (hband : ∀ (η : YoungDiagram) (r : Tableau (bandSize h s) η), η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r)
        (cyclic (wordRep _ _) (stairBandWord h s)).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic m).toRepresentation, F ≠ 0 := by
  subst m
  obtain ⟨f,hf⟩ := shiftedStairWord_support h s ν (canonicalTableau ν hν) fh hfh
  have H := strip_product_support hs (canonicalTableau ν hν) t (cutPositions h s)
    (shiftedStairWord h s) (stairBandWord h s)
    (fun a => s ≤ ((finProdFinEquiv.symm a).1).val)
    (shiftedStairWord_alphabet h s) (stairBandWord_alphabet h s) f hf hband
  rw [← staircase_cut_factor] at H
  obtain ⟨F,hF⟩ := H
  exact cyclic_projection_support (sameHighProjection _ _ _ s) (staircaseWord (h+s)) F hF

lemma staircase_one_dominates (μ : YoungDiagram) (hμ : μ.card = (staircase 1).card) :
    Dominates (staircase 1) μ := by
  intro k
  by_cases hk : k=0
  · subst k; simp [rowPrefix]
  · have hh : (staircase 1).colLen 0 ≤ k := by simp only [staircase_colLen]; omega
    rw [rowPrefix_eq_card _ hh,← hμ]
    exact rowPrefix_le_card μ k

/- Strong induction, including m=1 and every
partition of the exact triangular size. -/
theorem full_cyclic_support (m : ℕ) (hm : 1 ≤ m) (μ : YoungDiagram)
    (t : Tableau (staircase m).card μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep t) (staircaseCyclic m).toRepresentation, F ≠ 0 := by
  induction m using Nat.strong_induction_on generalizing μ with
  | h m ih =>
    have hμ : μ.card = (staircase m).card := by
      simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr t).symm
    by_cases hd : Dominates (staircase m) μ
    · exact dominated_support_uts m hm μ t hd
    have hm2 : 2 ≤ m := by
      by_contra hn
      have he : m=1 := by omega
      subst m
      exact hd (staircase_one_dominates μ hμ)
    rcases strip_reduction m hm2 μ hμ hd with ⟨ν,hν,hs⟩ | ⟨hm5,q,hq,ν,hν,hs⟩
    · obtain ⟨f,hf⟩ := ih (m-1) (by omega) (by omega) ν (canonicalTableau ν hν)
      exact band_cut_support (m-1) 1 m (by omega) ν μ hν t [μ.card-ν.card]
        (SizedStripChain.of_horizontal hs) f hf (fun η r hη => oneBand_support (m-1) η r hη)
    · obtain ⟨f,hf⟩ := ih (m-2) (by omega) (by omega) ν (canonicalTableau ν hν)
      obtain ⟨bs,hbs,hS⟩ := hs.sized
      exact band_cut_support (m-2) 2 m (by omega) ν μ hν t bs hS f hf
        (fun η r hη => twoBand_support_uts (m-2) (by omega) η r (by omega))

/- The strengthened cyclic form of Saxl’s conjecture. -/
theorem cyclic_saxl_conjecture_oai : CyclicSaxlConjecture := by
  intro m hm μ hμ
  exact full_cyclic_support m hm μ (canonicalTableau μ hμ)

/- Every complex staircase tensor square contains
all Specht irreducibles of its symmetric group. -/

end Saxl

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.cyclic_saxl_conjecture_oai := @OAI.Saxl.cyclic_saxl_conjecture_oai
