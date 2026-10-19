-- Prove2me | solution 1 for OAI.Saxl.twoBand_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:24:57.727144+00:00
-- url     : https://prove2.me/submissions/663edab1-c63f-4632-a18b-6ee4cedb2dc6

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/BandSupport.lean:L48-L64
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.twoBand_support. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Theorems.Thm_OAI_Saxl_Path_fourRow_support
import Theorems.Thm_OAI_Saxl_altWord_fiber_relabel
import Theorems.Thm_OAI_Saxl_altWord_letter_eval

-- ---- from OAI.RepresentationTheory.Saxl.PositionSplit ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/
lemma signC_sumPerm {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) :
    signC (sumPerm e g h) = signC g * signC h := by
  simp [signC_def, sumPerm, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

lemma word_eq_iff_parts {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w v : Fin n → Fin d) : w = v ↔ leftWord e w = leftWord e v ∧ rightWord e w = rightWord e v := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl⟩
  · rintro ⟨h₁,h₂⟩
    funext i
    obtain ⟨k, rfl⟩ := e.symm.surjective i
    cases k with
    | inl k => exact congrFun h₁ k
    | inr k => exact congrFun h₂ k

lemma single_positionProduct {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (w : Fin n → Fin d) :
    (Pi.single w (1:ℂ) : WordSpace n d) =
      positionProduct e (Pi.single (leftWord e w) 1) (Pi.single (rightWord e w) 1) := by
  classical
  ext v
  simp only [positionProduct, Pi.single_apply]
  simp only [word_eq_iff_parts e]
  split_ifs <;> simp_all

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

/- Exact independent-block factorization for arbitrary row/column labels. -/
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

-- ---- from OAI.RepresentationTheory.Saxl.BandFactorization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The first-layer exact band factorization, including the high-letter shift. -/
/- The second-layer exact band factorization. -/
/- The exact path order, starting at the bottom row singleton and ending
at the rightmost column singleton. -/
lemma bandPath_coordinates (h : ℕ) (k : Fin (2*(h+1)+1)) :
    (bandTableau h 2 (bandPathEquiv h k)).val = (h+1-(k.val+1)/2,k.val/2) := by
  have hh := (bandCellsEquiv h 2).apply_symm_apply (pathCellsEquiv h k)
  exact congrArg Subtype.val hh

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.PathAlternation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl.PathLayer

lemma tag_left (r : ℕ) (i : Fin (2*r+1)) :
    tag ((appendPair r).symm (Sum.inl i)) = tag i := rfl
lemma tag_right (r : ℕ) (i : Fin 2) :
    tag ((appendPair r).symm (Sum.inr i)) = r+1 := by
  unfold tag
  rw [appendPair_right]
  omega

lemma tag_side (r : ℕ) (i : Fin (2*(r+1)+1)) :
    (appendPair r i).isLeft = true ↔ tag i < r+1 := by
  obtain ⟨j,rfl⟩ := (appendPair r).symm.surjective i
  cases j with
  | inl j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, true_iff, tag_left]; unfold tag; omega
  | inr j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, tag_right, lt_self_iff_false]

lemma rowGroup_sector (r : ℕ) :
    Saxl.fiberGroup (@tag (r+1)) = Saxl.fiberGroup (@tag (r+1)) ⊓
      Saxl.sectorGroup (fun i => (appendPair r i).isLeft = true) := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg, ?_⟩
    intro i
    change (appendPair r (g i)).isLeft = true ↔ (appendPair r i).isLeft = true
    rw [tag_side,tag_side]
    change ∀ i, tag (g i) = tag i at hg
    rw [hg]
  · exact inf_le_left

lemma rowAlt_step (r : ℕ) :
    rowAlt (r+1) = Saxl.positionProduct (appendPair r) (rowAlt r)
      (Saxl.altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i)) := by
  unfold rowAlt
  rw [rowGroup_sector, Saxl.altWord_fiber_split]
  have hl : Saxl.fiberGroup (fun i => tag ((appendPair r).symm (Sum.inl i))) =
      Saxl.fiberGroup (@tag r) := rfl
  have hr : Saxl.fiberGroup (fun i => tag ((appendPair r).symm (Sum.inr i))) = ⊤ := by
    apply Subgroup.ext
    intro g
    change (∀ i, tag ((appendPair r).symm (Sum.inr (g i))) = tag ((appendPair r).symm (Sum.inr i))) ↔ True
    simp only [tag_right, implies_true]
  rw [hl,hr]
  congr 2
  funext i
  apply Fin.ext
  change (base ((appendPair r).symm (Sum.inr i))).val = i.val
  have hn : ((appendPair r).symm (Sum.inr i)).val ≠ 0 := by rw [appendPair_right]; omega
  unfold base
  rw [ite_eq_right hn]
  change (2*r+1+i.val+1)%2 = i.val
  omega

lemma pair_alt (w : Fin 2 → Fin 2) :
    Saxl.altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i) w = J (w 0) (w 1) := by
  classical
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin 2)))
  unfold Saxl.altWord
  rw [Finset.sum_apply]
  change (∑ g : (⊤ : Subgroup (Equiv.Perm (Fin 2))), Saxl.signC (g : Equiv.Perm (Fin 2)) *
    ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ (g : Equiv.Perm (Fin 2))))) = _
  calc
    _ = ∑ g : Equiv.Perm (Fin 2), Saxl.signC g *
        ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ g)) :=
      Fintype.sum_equiv (Subgroup.topEquiv (G := Equiv.Perm (Fin 2))).toEquiv _ _ (by intro g; rfl)
    _ = _ := by
      have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1,Equiv.swap 0 1} := by decide
      rw [hu]
      have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
      simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton]
      have hw : w = ![w 0,w 1] := by ext i; fin_cases i <;> rfl
      rw [hw]
      generalize h0 : w 0 = a
      generalize h1 : w 1 = b
      fin_cases a <;> fin_cases b <;>
        norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]

lemma rowAlt_zero (w : Fin 1 → Fin 2) :
    rowAlt 0 w = if w 0 = 0 then 1 else 0 := by
  classical
  change Saxl.altWord (Saxl.fiberGroup (@tag 0)) (@base 0) w = _
  let := Fintype.ofFinite (Saxl.fiberGroup (@tag 0))
  unfold Saxl.altWord
  have hu : (Finset.univ : Finset (Saxl.fiberGroup (@tag 0))) = {1} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Fin.ext
    have := ((g : Equiv.Perm (Fin (2*0+1))) i).isLt
    have := i.isLt
    omega
  rw [hu,Finset.sum_singleton]
  simp only [OneMemClass.coe_one, map_one, one_smul]
  change (Pi.single (@base 0) (1:ℂ) : Saxl.WordSpace 1 2) w = _
  rw [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; have := congrFun h 0; simpa [base] using this
  · intro h; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; simpa [base] using h

lemma rowAlt_formula (r : ℕ) (w : Fin (2*r+1) → Fin 2) :
    rowAlt r w = (if w 0 = 0 then 1 else 0) *
      ∏ i : Fin r, J (w ⟨2*i.val+1,by omega⟩) (w ⟨2*i.val+2,by omega⟩) := by
  induction r with
  | zero => simpa using rowAlt_zero w
  | succ r ih =>
    rw [rowAlt_step]
    change rowAlt r (Saxl.leftWord (appendPair r) w) *
      Saxl.altWord ⊤ (fun i : Fin 2 => i) (Saxl.rightWord (appendPair r) w) = _
    rw [ih, pair_alt, Fin.prod_univ_castSucc]
    exact mul_assoc _ _ _

end Saxl.PathLayer

namespace Saxl

lemma lowLetter_injective (h : ℕ) : Function.Injective (lowLetter h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin ((staircase (h+2)).colLen 0) => x.val) hij)

lemma bandColumnPath_coordinates (h : ℕ) (k : Fin (2*(h+1)+1)) :
    (bandTableau h 2 (bandColumnPathEquiv h k)).val = (k.val/2,h+1-(k.val+1)/2) := by
  change (bandTableau h 2 (bandPathEquiv h k.rev)).val = _
  rw [bandPath_coordinates]
  apply Prod.ext <;> simp only [Fin.val_rev] <;> have := k.isLt <;> omega

lemma bandRow_path_group (h : ℕ) :
    fiberGroup ((fun j => (bandTableau h 2 j).val.1) ∘ bandPathEquiv h) =
      fiberGroup (@PathLayer.tag (h+1)) := by
  apply Subgroup.ext
  intro g
  change (∀ i, _ = _) ↔ (∀ i, _ = _)
  simp only [Function.comp_apply, bandPath_coordinates, PathLayer.tag]
  constructor <;> intro hg i <;> have hh := hg i <;>
    have := i.isLt <;> have := (g i).isLt <;> omega

lemma bandColumn_path_group (h : ℕ) :
    fiberGroup ((fun j => (bandTableau h 2 j).val.2) ∘ bandColumnPathEquiv h) =
      fiberGroup (@PathLayer.tag (h+1)) := by
  apply Subgroup.ext
  intro g
  change (∀ i, _ = _) ↔ (∀ i, _ = _)
  simp only [Function.comp_apply, bandColumnPath_coordinates, PathLayer.tag]
  constructor <;> intro hg i <;> have hh := hg i <;>
    have := i.isLt <;> have := (g i).isLt <;> omega

lemma bandRow_path_base (h : ℕ) :
    (rightWord (cutPositions h 2)
      (rowWord (stairRowTableau (h+2)) ∘ (rotateRowPositions h 2 : Equiv.Perm _))) ∘ bandPathEquiv h =
      lowLetter h ∘ (@PathLayer.base (h+1)) := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, rightWord, rowWord, stairRowTableau, rotateRowPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, staircaseSwap]
  change (rotateRow h 2 (bandTableau h 2 (bandPathEquiv h k))).val.2 = _
  change (if (bandTableau h 2 (bandPathEquiv h k)).val.2 < h-(bandTableau h 2 (bandPathEquiv h k)).val.1 then
    (bandTableau h 2 (bandPathEquiv h k)).val.2+2 else
    (bandTableau h 2 (bandPathEquiv h k)).val.2-(h-(bandTableau h 2 (bandPathEquiv h k)).val.1)) = _
  rw [bandPath_coordinates]
  simp only [lowLetter, PathLayer.base]
  split_ifs <;> have := k.isLt <;> simp only [Fin.val_zero] <;> omega

lemma bandColumn_path_base (h : ℕ) :
    (rightWord (cutPositions h 2)
      (rowWord (stairTableau (h+2)) ∘ (rotateColumnPositions h 2 : Equiv.Perm _))) ∘ bandColumnPathEquiv h =
      lowLetter h ∘ (@PathLayer.base (h+1)) := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, rightWord, rowWord, rotateColumnPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  change (rotateColumn h 2 (bandTableau h 2 (bandColumnPathEquiv h k))).val.1 = _
  change (if (bandTableau h 2 (bandColumnPathEquiv h k)).val.1 < h-(bandTableau h 2 (bandColumnPathEquiv h k)).val.2 then
    (bandTableau h 2 (bandColumnPathEquiv h k)).val.1+2 else
    (bandTableau h 2 (bandColumnPathEquiv h k)).val.1-(h-(bandTableau h 2 (bandColumnPathEquiv h k)).val.2)) = _
  rw [bandColumnPath_coordinates]
  simp only [lowLetter, PathLayer.base]
  split_ifs <;> have := k.isLt <;> simp only [Fin.val_zero] <;> omega

lemma bandRow_path_eval (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 2) :
    bandRowWord h 2 ((lowLetter h ∘ w) ∘ (bandPathEquiv h).symm) = PathLayer.rowAlt (h+1) w := by
  unfold bandRowWord bandRowGroup
  rw [altWord_fiber_relabel, bandRow_path_group, bandRow_path_base,
    altWord_letter_eval _ (lowLetter_injective h)]
  rfl

lemma bandColumn_path_eval (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 2) :
    bandColumnWord h 2 ((lowLetter h ∘ w) ∘ (bandColumnPathEquiv h).symm) = PathLayer.rowAlt (h+1) w := by
  unfold bandColumnWord bandColumnGroup
  rw [altWord_fiber_relabel, bandColumn_path_group, bandColumn_path_base,
    altWord_letter_eval _ (lowLetter_injective h)]
  rfl

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.BandPairing ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Band

end Saxl.Band
namespace Saxl.Path

/- The actual complex Specht modules with at most four rows occur in the
specified two-layer alternating path cyclic module. -/
end Saxl.Path

namespace Saxl.PathLayer

lemma J_flip (a b : Fin 2) : J a b = - J b a := by
  fin_cases a <;> fin_cases b <;> norm_num [J]

lemma rowAlt_rev_formula (r : ℕ) (w : Fin (2*r+1) → Fin 2) :
    rowAlt r (w ∘ Fin.rev) = (if w (Fin.last (2*r)) = 0 then 1 else 0) *
      ((-1 : ℂ)^r * ∏ i : Fin r, J (w ⟨2*i.val,by omega⟩) (w ⟨2*i.val+1,by omega⟩)) := by
  rw [rowAlt_formula]
  have hzero : (0 : Fin (2*r+1)).rev = Fin.last (2*r) := by apply Fin.ext; simp
  simp only [Function.comp_apply, hzero]
  congr 1
  calc
    (∏ i : Fin r, J (w (⟨2*i.val+1,by omega⟩ : Fin (2*r+1)).rev)
      (w (⟨2*i.val+2,by omega⟩ : Fin (2*r+1)).rev)) =
      ∏ i : Fin r, (-1 : ℂ) * J (w ⟨2*i.val,by omega⟩) (w ⟨2*i.val+1,by omega⟩) := by
        apply Fintype.prod_equiv Fin.revPerm
        intro i
        have h₁ : (⟨2*i.val+1,by omega⟩ : Fin (2*r+1)).rev = ⟨2*i.rev.val+1,by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_rev]; have := i.isLt; omega
        have h₂ : (⟨2*i.val+2,by omega⟩ : Fin (2*r+1)).rev = ⟨2*i.rev.val,by omega⟩ := by
          apply Fin.ext; simp only [Fin.val_rev]; have := i.isLt; omega
        rw [h₁,h₂,J_flip]
        simp
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

theorem paired_rowAlt (r : ℕ) (w : Fin (2*r+1) → Saxl.Path.Letter) :
    rowAlt r (fun i => (Saxl.Path.parts (w i)).1) *
      rowAlt r ((fun i => (Saxl.Path.parts (w i)).2) ∘ Fin.rev) =
      (-1 : ℂ)^r * Saxl.Path.bandWord r w := by
  rw [rowAlt_formula,rowAlt_rev_formula]
  unfold Saxl.Path.bandWord
  rw [Finset.prod_mul_distrib]
  change _ = (-1:ℂ)^r * (_ * _ *
    ((∏ i : Fin r, J (Saxl.Path.parts (w ⟨2*i.val,by omega⟩)).2 (Saxl.Path.parts (w ⟨2*i.val+1,by omega⟩)).2) *
     (∏ i : Fin r, J (Saxl.Path.parts (w ⟨2*i.val+1,by omega⟩)).1 (Saxl.Path.parts (w ⟨2*i.val+2,by omega⟩)).1)))
  ring

end Saxl.PathLayer

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.CyclicSector ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uX uY uZ uV

namespace Saxl

/- Explicit finite-group induction on a linear map. -/
/- Coordinate-sector induction, in precisely the nonzero-Hom form used in
the staircase induction. The projector kills translates outside the stabilizer. -/
open scoped MonoidAlgebra

theorem intertwining_lift_surjective {G : Type uG} {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Surjective F)
    (f : Representation.IntertwiningMap τ σ) :
    ∃ h : Representation.IntertwiningMap τ ρ, F.comp h = f := by
  let EF := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
  let EH := Representation.IntertwiningMap.equivLinearMapAsModule τ ρ
  let Ef := Representation.IntertwiningMap.equivLinearMapAsModule τ σ
  obtain ⟨h, hh⟩ := IsSemisimpleModule.lifting_property (EF F) hF (Ef f)
  refine ⟨EH.symm h, ?_⟩
  ext z
  exact LinearMap.congr_fun hh z

end Saxl

namespace Saxl

/- Concrete sector averaging produces a constituent of the full cyclic
module from an equivariant map on its coordinate sector. -/
lemma cyclicMap_surjective {G : Type uG} {X : Type uX} {Y : Type uY} [Group G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (v : X) : Function.Surjective (cyclicMap F v) := by
  intro y
  have hy := y.property
  change y.val ∈ Submodule.span ℂ _ at hy
  suffices ∃ x : (cyclic ρ v).toSubmodule, (cyclicMap F v x).val = y.val by
    obtain ⟨x,hx⟩ := this
    exact ⟨x,Subtype.ext hx⟩
  generalize hz : y.val = z at hy ⊢
  clear y hz
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g,rfl⟩ := hz
    refine ⟨(cyclic ρ v).toRepresentation g ⟨v,mem_cyclic _ _⟩, ?_⟩
    change F (ρ g v) = σ g (F v)
    exact LinearMap.congr_fun (F.isIntertwining' g) v
  | zero => exact ⟨0,map_zero F⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨u,hu⟩ := ihx
    obtain ⟨w,hw⟩ := ihy
    refine ⟨u+w, ?_⟩
    change F (u.val+w.val) = _
    rw [map_add,show F u.val = x from hu,show F w.val = y from hw]
  | smul c x hx ih =>
    obtain ⟨u,hu⟩ := ih
    refine ⟨c • u, ?_⟩
    change F (c • u.val) = _
    rw [map_smul,show F u.val = x from hu]

/- A genuine equivariant projection of a cyclic generator transfers every
nonzero constituent map back to the original cyclic module by Maschke. -/
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

lemma cyclic_action_eq {G : Type uG} {V : Type uV} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (g : G) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic ρ v))
  · apply (cyclic_le _ _ _).mpr
    have hh := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic ρ (ρ g v))
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at hh
    exact hh

lemma support_relabel {n m d k : ℕ} (e : Fin n ≃ Fin m) (v : WordSpace n d)
    (hv : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t) (cyclic (wordRep n d) v).toRepresentation, f ≠ 0) :
    ∀ (μ : YoungDiagram) (t : Tableau m μ), μ.colLen 0 ≤ k →
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        (cyclic (wordRep m d) (fun w => v (w ∘ e))).toRepresentation, f ≠ 0 := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  intro μ t hμ
  change ∃ f : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (wordRep n d e v)).toRepresentation, f ≠ 0
  rw [cyclic_action_eq]
  exact hv μ t hμ

end Saxl

end

end OAI

-- ---- from OAI.RepresentationTheory.Saxl.BandSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma bandColumn_path_eval' (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 2) :
    bandColumnWord h 2 ((lowLetter h ∘ w) ∘ (bandPathEquiv h).symm) =
      PathLayer.rowAlt (h+1) (w ∘ Fin.rev) := by
  have he : (lowLetter h ∘ (w ∘ Fin.rev)) ∘ (bandColumnPathEquiv h).symm =
      (lowLetter h ∘ w) ∘ (bandPathEquiv h).symm := by
    funext i
    simp [bandColumnPathEquiv, Function.comp_def, Fin.revPerm]
  rw [← he, bandColumn_path_eval]

lemma stairBandWord_path_eval (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 4) :
    restrictLetters (lowPairLetter h) (stairBandWord h 2) (w ∘ (bandPathEquiv h).symm) =
      (-1 : ℂ)^(h+1) * Path.bandWord (h+1) w := by
  change wordTensor _ _ _ (bandRowWord h 2 ⊗ₜ[ℂ] bandColumnWord h 2)
    (lowPairLetter h ∘ (w ∘ (bandPathEquiv h).symm)) = _
  rw [wordTensor_tmul]
  have hl : splitLeft (lowPairLetter h ∘ (w ∘ (bandPathEquiv h).symm)) =
      (lowLetter h ∘ (fun i => (Path.parts (w i)).1)) ∘ (bandPathEquiv h).symm := by
    funext i; simp [splitLeft, lowPairLetter]
  have hr : splitRight (lowPairLetter h ∘ (w ∘ (bandPathEquiv h).symm)) =
      (lowLetter h ∘ (fun i => (Path.parts (w i)).2)) ∘ (bandPathEquiv h).symm := by
    funext i; simp [splitRight, lowPairLetter]
  rw [hl,hr,bandRow_path_eval,bandColumn_path_eval']
  exact PathLayer.paired_rowAlt _ w

/- Every Specht shape with at most four rows occurs in the cyclic module
generated by the prescribed two-band vector. -/
theorem twoBand_support (h : ℕ) (hh : 1 ≤ h) (μ : YoungDiagram)
    (t : Tableau (bandSize h 2) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (stairBandWord h 2)).toRepresentation, f ≠ 0 := by
  have he : restrictLetters (lowPairLetter h) (stairBandWord h 2) =
      (-1 : ℂ)^(h+1) • (fun w => Path.bandWord (h+1) (w ∘ bandPathEquiv h)) := by
    funext w
    have hw : (w ∘ bandPathEquiv h) ∘ (bandPathEquiv h).symm = w := by funext i; simp
    simpa only [hw,Pi.smul_apply,smul_eq_mul] using stairBandWord_path_eval h (w ∘ bandPathEquiv h)
  have hs := support_relabel (bandPathEquiv h) (Path.bandWord (h+1))
    (fun ν s hν => Path.fourRow_support (h+1) (by omega) ν s hν) μ t hμ
  have hc : cyclic (wordRep (bandSize h 2) 4) (restrictLetters (lowPairLetter h) (stairBandWord h 2)) =
      cyclic (wordRep (bandSize h 2) 4) (fun w => Path.bandWord (h+1) (w ∘ bandPathEquiv h)) := by
    rw [he,cyclic_smul_eq _ _ _ (pow_ne_zero _ (by norm_num))]
  rw [← hc] at hs
  obtain ⟨f,hf⟩ := hs
  exact cyclic_projection_support (restrictLetters (lowPairLetter h)) (stairBandWord h 2) f hf

end Saxl

namespace Saxl

/- Coordinate subrepresentation using only letters with property A. -/
/- The actual same-high image factors as the smaller Specht tensor cyclic
vector and the exact retained band vector on independent position blocks. -/
/- The width-one band is the genuine trivial constituent required by Pieri. -/
end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.twoBand_support := @_root_.OAI.Saxl.twoBand_support
