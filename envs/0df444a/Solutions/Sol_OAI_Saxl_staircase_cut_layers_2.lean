-- Prove2me | solution 2 for OAI.Saxl.staircase_cut_layers
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:10:24.705086+00:00
-- url     : https://prove2.me/submissions/606715d2-7526-4450-a6af-d5151a437284

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/CoordinateSector.lean:L180-L203
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.staircase_cut_layers. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Theorems.Thm_OAI_Saxl_staircase_projected_high_positions

-- ---- from OAI.RepresentationTheory.Saxl.HighProjection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
/- Local same-high projection in the ordinary pair-letter coordinate space. -/
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

/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.CoordinateSector ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/
lemma coordinateProjection_single {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (a : Fin n → Fin d) [Decidable (P a)] :
    coordinateProjection P (Pi.single a 1) = if P a then Pi.single a 1 else 0 := by
  classical
  ext b
  by_cases he : b = a
  · subst b; by_cases h : P a <;> simp [h]
  · by_cases h : P a <;> simp [he, h]

/- Permutations preserving a position sector. -/
/- The genuine unnormalized signed block alternation. -/
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

lemma polytabloid_eq_altWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t = altWord (columnGroup t) (rowWord t) := rfl

/- The cut's two layers, with their exact retained row and column permutations. -/
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

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.staircase_cut_layers := @_root_.OAI.Saxl.staircase_cut_layers
