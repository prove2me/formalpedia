-- Prove2me | solution 1 for OAI.Saxl.twoBand_support_uts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:36:32.985373+00:00
-- url     : https://prove2.me/submissions/79da9213-36e2-4453-a529-69ad2315cf8a

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021

section
-- module Solutions.OAIQ259_US.Saxl_SpechtDuality
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/

lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/
theorem hom_to_cyclic_of_pair {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule)
    (u : WordSpace n e) (hu : star u = u)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ f : Representation.IntertwiningMap S.toRepresentation
      (cyclic (wordRep n e) u).toRepresentation, f ≠ 0 := by
  let inc : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun g => rfl }
  let f := (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)).comp ((wordMap L).comp inc)
  refine ⟨f, ?_⟩
  intro hf
  have hp := subrepProject_pair (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx) (wordMap L x.val) ⟨u, mem_cyclic _ _⟩
  have he : f x = 0 := by rw [hf]; rfl
  change (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)) (wordMap L x.val) = 0 at he
  rw [he] at hp
  exact h (hp.symm.trans (zero_dotProduct _))

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma bandPath_coordinates (h : ℕ) (k : Fin (2*(h+1)+1)) :
    (bandTableau h 2 (bandPathEquiv h k)).val = (h+1-(k.val+1)/2,k.val/2) := by
  have hh := (bandCellsEquiv h 2).apply_symm_apply (pathCellsEquiv h k)
  exact congrArg Subtype.val hh

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PathAlternation
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.joinPositions_parts _root_.OAI.Saxl.leftWord_join _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.rightWord_join
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
        (first | (simp [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]; all_goals first | (norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]; done) | rfl | decide) | (norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]; done) | norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J])

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

lemma altWord_fiber_relabel {n m d : ℕ} {α : Type uAlpha}
    (e : Fin n ≃ Fin m) (c : Fin m → α) (a : Fin m → Fin d) (w : Fin n → Fin d) :
    altWord (fiberGroup c) a (w ∘ e.symm) =
      altWord (fiberGroup (c ∘ e)) (a ∘ e) w := by
  classical
  let := Fintype.ofFinite (fiberGroup c)
  let := Fintype.ofFinite (fiberGroup (c ∘ e))
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv (fiberRelabel e c)
  intro g
  have hs : signC ((fiberRelabel e c g).val) = signC g.val := by
    change signC (e.permCongr g.val) = _
    simp only [signC_def, Equiv.Perm.sign_permCongr]
  rw [hs]
  congr 1
  change (Pi.single (a ∘ e) (1:ℂ) : WordSpace n d) (w ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace m d) ((w ∘ e.symm) ∘ (e.permCongr g.val))
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    simpa [Equiv.permCongr] using congrFun h j
  · intro h
    funext i
    simpa [Equiv.permCongr] using congrFun h (e i)

lemma altWord_letter_eval {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (G : Subgroup (Equiv.Perm (Fin n))) (a w : Fin n → Fin d) :
    altWord G (φ ∘ a) (φ ∘ w) = altWord G a w := by
  classical
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  change (Pi.single (φ ∘ a) (1:ℂ) : WordSpace n D) ((φ ∘ w) ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace n d) (w ∘ g.val)
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; funext i; exact hφ (congrFun h i)
  · intro h; funext i; exact congrArg φ (congrFun h i)



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
end

section
-- module Solutions.OAIQ259_US.Saxl_BandMatrices
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uA

namespace Saxl.Band
lemma sum_perm_succ {A : Type uA} [AddCommMonoid A] (n : ℕ)
    (f : Equiv.Perm (Fin (n + 1)) → A) :
    (∑ π, f π) = ∑ i : Fin (n + 1), ∑ σ : Equiv.Perm (Fin n),
      f (Equiv.Perm.decomposeFin.symm (i, σ)) := by
  calc
    (∑ π, f π) = ∑ x : Fin (n + 1) × Equiv.Perm (Fin n),
        f (Equiv.Perm.decomposeFin.symm x) :=
      Fintype.sum_equiv Equiv.Perm.decomposeFin _ _ (by intro π; simp)
    _ = _ := Fintype.sum_prod_type _

lemma decompose_apply_two {n : ℕ} (e : Equiv.Perm (Fin (n + 2))) (p : Fin (n + 3)) :
    Equiv.Perm.decomposeFin.symm (p, e) 2 = Equiv.swap 0 p (e 1).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (1 : Fin (n + 2)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 1

lemma decompose_apply_three {n : ℕ} (e : Equiv.Perm (Fin (n + 3))) (p : Fin (n + 4)) :
    Equiv.Perm.decomposeFin.symm (p, e) 3 = Equiv.swap 0 p (e 2).succ := by
  change Equiv.Perm.decomposeFin.symm (p, e) (2 : Fin (n + 3)).succ = _
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 2

lemma segment_one_even : segment 1 0 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_one_odd : segment 1 1 = 1 := by
  simp [segment, List.ofFn_succ, basis, D]

lemma segment_two_even : segment 2 0 = (2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_two_odd : segment 2 1 = (-2 : ℂ) • basis 1 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_three_even : segment 3 0 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_three_odd : segment 3 1 = (-6 : ℂ) • basis 3 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_four_even : segment 4 0 = (24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

lemma segment_four_odd : segment 4 1 = (-24 : ℂ) • basis 0 := by
  unfold segment
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique,
    List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
  norm_num only [Equiv.Perm.decomposeFin.symm_sign,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, decompose_apply_two, decompose_apply_three,
    Equiv.Perm.decomposeFin_symm_of_one, Equiv.swap_self, Equiv.swap_apply_def,
    Equiv.Perm.sign_one, Equiv.Perm.sign_swap, Equiv.Perm.one_apply,
    Fin.ext_iff, Fin.isValue, Fin.reduceFinMk, Fin.succ_mk, Fin.val_mk, Fin.zero_eta,
    Fin.succ_zero_eq_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [D, basis, decompose_apply_two, decompose_apply_three, Fin.ext_iff, Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two])

/- Only the original global parity matters. -/
lemma segment_mod (r p : ℕ) : segment r p = segment r (p % 2) := by
  simp [segment, D, Nat.add_mod]

lemma scaledBasis_smul (c : ℂ) (hc : c ≠ 0) (i : Fin 4) :
    ScaledBasis (c • basis i.val) := ⟨c, hc, i, rfl⟩

lemma scaledBasis_one : ScaledBasis 1 := by
  exact ⟨1, one_ne_zero, 0, by simp [basis]⟩

lemma basis_mul (i j : Fin 4) : ScaledBasis (basis i.val * basis j.val) := by
  fin_cases i <;> fin_cases j
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])

lemma ScaledBasis.mul {X Y : Mat} (hX : ScaledBasis X) (hY : ScaledBasis Y) :
    ScaledBasis (X * Y) := by
  obtain ⟨c, hc, i, rfl⟩ := hX
  obtain ⟨d, hd, j, rfl⟩ := hY
  obtain ⟨e, he, k, hk⟩ := basis_mul i j
  refine ⟨c * d * e, mul_ne_zero (mul_ne_zero hc hd) he, k, ?_⟩
  rw [smul_mul_smul_comm, hk, smul_smul]

lemma segment_scaled (r p : ℕ) (hr : 1 ≤ r ∧ r ≤ 4) : ScaledBasis (segment r p) := by
  rw [segment_mod]
  have hp := Nat.mod_two_eq_zero_or_one p
  obtain ⟨hr1, hr4⟩ := hr
  interval_cases r <;> rcases hp with hp | hp <;> rw [hp]
  all_goals simp only [segment_one_even, segment_one_odd,
    segment_two_even, segment_two_odd, segment_three_even, segment_three_odd,
    segment_four_even, segment_four_odd]
  all_goals first
    | exact scaledBasis_one
    | exact scaledBasis_smul _ (by norm_num) 0
    | exact scaledBasis_smul _ (by norm_num) 1
    | exact scaledBasis_smul _ (by norm_num) 3

lemma blocks_scaled (rs : List ℕ) (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) (p : ℕ) :
    ScaledBasis (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact scaledBasis_one
  | cons r rs ih =>
    exact (segment_scaled r p (hrs r (by simp))).mul
      (ih (fun a ha => hrs a (by simp [ha])) (p + r))

lemma Q_inverse : Q⁻¹ = Qinv := by
  exact Matrix.inv_eq_left_inv Qinv_mul_Q

lemma Q_basis_ne_zero (i : Fin 4) : (Q * basis i.val * Q⁻¹) 0 0 ≠ 0 := by
  rw [Q_inverse]
  fin_cases i <;> (first | (simp [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [Q, Qinv, basis, Matrix.mul_apply, Fin.sum_univ_two])

/- Endpoint noncancellation for arbitrary consecutive columns of lengths at most four. -/

end Saxl.Band

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_PathContraction
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Path

lemma chainML_apply (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = (List.ofFn fun i => Band.D (p + i.val) (X i)).prod := rfl

lemma entry_sum (X : Mat) :
    (∑ a : Letter, X (parts a).1 (parts a).2 • entry a) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (first | (simp [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; all_goals first | (norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | rfl | decide) | (norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | norm_num [Fin.sum_univ_succ, parts, entry, Matrix.single, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff])

lemma chain_expand (n p : ℕ) (X : Fin n → Mat) :
    chainML n p X = ∑ w : Fin n → Letter, pureWord X w •
      chainML n p (fun i => entry (w i)) := by
  calc
    chainML n p X = chainML n p (fun i => ∑ a : Letter,
      X i (parts a).1 (parts a).2 • entry a) := by
        congr 1; funext i; exact (entry_sum (X i)).symm
    _ = _ := ?_
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [MultilinearMap.map_smul_univ]
  rfl

lemma adj_entry (a : Letter) (i j : Fin 2) :
    (entry a).adjugate i j = -(J i (parts a).2 * J (parts a).1 j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    (first | (simp [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; all_goals first | (norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | rfl | decide) | (norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff]; done) | norm_num [entry, parts, J, Matrix.single, Matrix.adjugate_fin_two, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.ext_iff])

lemma D_shift (q : ℕ) (X : Mat) : Band.D (q + 2) X = Band.D q X := by
  simp [Band.D]

lemma chain_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    chainML (2 * (r+1) + 1) 1 (fun i => entry (w i)) =
      entry (w 0) * (entry (w 1)).adjugate *
      chainML (2 * r + 1) 1 (fun i => entry (w i.succ.succ)) := by
  rw [chainML_apply, List.ofFn_succ, List.prod_cons, List.ofFn_succ,
    List.prod_cons, chainML_apply]
  simp only [Fin.val_zero, Fin.val_succ, add_zero]
  rw [show Band.D 1 = id from by funext X; simp [Band.D],
    show Band.D 2 = Matrix.adjugate from by funext X; simp [Band.D]]
  simp only [id_eq]
  rw [mul_assoc]
  apply congrArg (fun A : Mat => entry (w 0) * ((entry (w 1)).adjugate * A))
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  rw [show 1 + (i.val + 1 + 1) = (1 + i.val) + 2 by omega, D_shift]

lemma pair_product_step (r : ℕ) (w : Fin (2 * (r+1) + 1) → Letter) :
    (∏ i : Fin (r+1), J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) =
    (J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1) *
    ∏ i : Fin r, J (parts (w (leftPos i).succ.succ)).2
      (parts (w (midPos i).succ.succ)).2 *
      J (parts (w (midPos i).succ.succ)).1 (parts (w (rightPos i).succ.succ)).1 := by
  rw [Fin.prod_univ_succ]
  rfl

lemma chain_entries (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) =
    ((-1 : ℂ)^r * ∏ i : Fin r,
      J (parts (w (leftPos i))).2 (parts (w (midPos i))).2 *
      J (parts (w (midPos i))).1 (parts (w (rightPos i))).1) •
    Matrix.single (parts (w 0)).1 (parts (w (Fin.last (2*r)))).2 1 := by
  induction r with
  | zero => simp [chainML_apply, List.ofFn_succ, Band.D, entry]
  | succ r ih =>
    rw [chain_step, ih, Matrix.mul_smul, pair_product_step]
    rw [show (0 : Fin (2*r+1)).succ.succ = 2 from Fin.ext rfl]
    change _ = _ • Matrix.single _ (parts (w (Fin.last (2*r)).succ.succ)).2 1
    unfold entry at *
    rw [Matrix.single_mul_mul_single, one_mul, mul_one]
    rw [show (Matrix.single (parts (w 1)).1 (parts (w 1)).2 (1 : ℂ)).adjugate
      (parts (w 0)).2 (parts (w 2)).1 =
      -(J (parts (w 0)).2 (parts (w 1)).2 * J (parts (w 1)).1 (parts (w 2)).1)
      from adj_entry (w 1) _ _]
    rw [show ∀ (c : ℂ) (i j : Fin 2), Matrix.single i j c = c • Matrix.single i j 1
      from fun c i j => by ext a b; simp [Matrix.single, smul_eq_mul]]
    rw [smul_smul]
    congr 1
    rw [pow_succ]
    ring

lemma chain_entries_endpoint (r : ℕ) (w : Fin (2*r+1) → Letter) :
    chainML (2*r+1) 1 (fun i => entry (w i)) 0 0 =
      (-1 : ℂ)^r * bandWord r w := by
  rw [chain_entries]
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, Matrix.single, h₁, h₂]

lemma J_real (i j : Fin 2) : star (J i j) = J i j := by
  fin_cases i <;> fin_cases j <;> simp [J]

lemma bandWord_real (r : ℕ) : star (bandWord r) = bandWord r := by
  funext w
  change star (bandWord r w) = bandWord r w
  by_cases h₁ : (parts (w 0)).1 = 0 <;>
    by_cases h₂ : (parts (w (Fin.last (2*r)))).2 = 0 <;>
    simp [bandWord, h₁, h₂, star_mul, star_prod, J_real, mul_comm]
end Saxl.Path

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ColumnContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/

lemma chain_cons (r : ℕ) (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat)
    (π : Equiv.Perm (Fin r)) (σ : Perms rs) :
    chain (r :: rs) p N (π, σ) =
      (List.ofFn fun j : Fin r => Band.D (p + j.val) (N (π j).val)).prod *
      chain rs (p + r) N σ := by
  unfold chain
  erw [List.ofFn_add, List.prod_append]
  congr 2
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + j.val) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.castAdd rs.sum j))))) = _
    rw [enumerate_left]
    rfl
  · apply congrArg List.ofFn
    funext j
    change Band.D (p + (r + j.val)) (N (row (@perm (r :: rs) (π, σ) (enumerate (r :: rs) (Fin.natAdd r j))))) = _
    erw [enumerate_right r rs (show Fin rs.sum from j)]
    simp only [perm, Equiv.sumCongr_apply, Sum.map_inr, row, Nat.add_assoc]

/- Ordered product of independent alternating column segments. -/
lemma sum_chain (rs : List ℕ) (p : ℕ) (N : ℕ → Band.Mat) :
    (∑ π : Perms rs, sg π • chain rs p N π) = segments p rs N := by
  induction rs generalizing p with
  | nil => simp [Perms, chain, sg, segments]
  | cons r rs ih =>
    simp only [Perms, Fintype.sum_prod_type, sg, chain_cons, segments]
    simp_rw [← smul_mul_smul_comm, ← Finset.mul_sum, ← Finset.sum_mul, ih]

lemma columnPerm_sign (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    signC (columnPerm μ π).val = sg π := by
  change (((Equiv.Perm.sign ((enumerate μ.transpose.rowLens).symm.permCongr (perm π)) : ℤ) : ℂ)) = sg π
  rw [Equiv.Perm.sign_permCongr]
  exact sign_perm π

lemma mapped_columnTableau (μ : YoungDiagram) (N : ℕ → Band.Mat) :
    wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
      N i.val (Path.parts a).1 (Path.parts a).2) (polytabloid (columnTableau μ)) =
    ∑ π : Perms μ.transpose.rowLens, sg π • Path.pureWord
      (fun q => N (row (perm π (enumerate μ.transpose.rowLens q)))) := by
  classical
  let := Fintype.ofFinite (columnGroup (columnTableau μ))
  unfold polytabloid
  rw [map_sum]
  let e : Perms μ.transpose.rowLens ≃ columnGroup (columnTableau μ) :=
    (columnEquiv μ).trans (Equiv.inv _)
  symm
  apply Fintype.sum_equiv e
  intro π
  rw [map_smul, wordRep_single]
  have hs : signC (e π).val = sg π := by
    change signC (columnPerm μ π).val⁻¹ = sg π
    rw [signC_inv, columnPerm_sign]
  change sg π • _ = signC (e π).val • _
  rw [hs]
  congr 1
  funext w
  rw [wordMap_single]
  unfold Path.pureWord
  apply Finset.prod_congr rfl
  intro q hq
  have hr : row (perm π (enumerate μ.transpose.rowLens q)) =
      ((columnTableau μ) ((e π).val⁻¹ q)).val.1 := by
    change _ = ((columnTableau μ) (((columnPerm μ π).val⁻¹)⁻¹ q)).val.1
    rw [inv_inv, columnTableau_val]
    dsimp only [columnPerm, Equiv.permCongr_apply]
    rw [Equiv.apply_symm_apply, Equiv.symm_symm]
  exact congrArg (fun j => N j (Path.parts (w q)).1 (Path.parts (w q)).2) hr

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_BandPairing
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Band

lemma conjugation_one : conjugation 1 = 1 := by
  change Q * 1 * Qinv = 1
  rw [mul_one, Q_mul_Qinv]

lemma conjugation_mul (X Y : Mat) : conjugation (X * Y) = conjugation X * conjugation Y := by
  change Q * (X * Y) * Qinv = (Q * X * Qinv) * (Q * Y * Qinv)
  simp only [mul_assoc, ← mul_assoc Qinv Q, Qinv_mul_Q, one_mul]

lemma conjugation_D (q : ℕ) (X : Mat) : D q (conjugation X) = conjugation (D q X) := by
  by_cases h : q % 2 = 0
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D, h, conjugation, Q, Qinv, Matrix.adjugate_fin_two, Matrix.mul_apply,
        Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  · simp [D, h]

lemma conjugation_prod (l : List Mat) : (l.map conjugation).prod = conjugation l.prod := by
  induction l with
  | nil => simp [conjugation_one]
  | cons a l ih => simp [ih, conjugation_mul]

lemma segments_conjugation (rs : List ℕ) (p : ℕ) :
    Columns.segments p rs (fun i => conjugation (basis i)) = conjugation (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact conjugation_one.symm
  | cons r rs ih =>
    simp only [Columns.segments, blocks, ih, conjugation_mul]
    congr 1
    unfold segment
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro π hπ
    rw [map_smul]
    congr 1
    simp_rw [conjugation_D]
    have he := conjugation_prod (List.ofFn fun j : Fin r => D (p + j.val) (basis (π j).val))
    rw [List.map_ofFn] at he
    exact he

lemma conjugation_blocks_ne_zero (rs : List ℕ)
    (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) : conjugation (blocks 1 rs) 0 0 ≠ 0 := by
  obtain ⟨c, hc, i, hi⟩ := blocks_scaled rs hrs 1
  rw [hi, map_smul]
  apply mul_ne_zero hc
  simpa only [conjugation, LinearMap.coe_mk, AddHom.coe_mk, Q_inverse] using Q_basis_ne_zero i

end Saxl.Band
namespace Saxl.Path

lemma chainFunctional_pure (n p : ℕ) (X : Fin n → Mat) :
    chainFunctional n p (pureWord X) = chainML n p X := (chain_expand n p X).symm

lemma chainFunctional_column (μ : YoungDiagram) (p : ℕ) (N : ℕ → Mat) :
    chainFunctional μ.transpose.rowLens.sum p
      (wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
        N i.val (parts a).1 (parts a).2) (polytabloid (Columns.columnTableau μ))) =
      Columns.segments p μ.transpose.rowLens N := by
  rw [Columns.mapped_columnTableau, map_sum]
  simp_rw [map_smul, chainFunctional_pure]
  exact Columns.sum_chain μ.transpose.rowLens p N

lemma chainFunctional_endpoint (r : ℕ) (x : WordSpace (2*r+1) 4) :
    chainFunctional (2*r+1) 1 x 0 0 = (-1 : ℂ)^r * dotProduct x (bandWord r) := by
  change (∑ w : Fin (2*r+1) → Fin 4,
    x w • chainML (2*r+1) 1 (fun i => entry (w i))) 0 0 = _
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, chain_entries_endpoint]
  simp [dotProduct, Finset.mul_sum, mul_left_comm]


lemma fourRow_column_lengths (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 4) :
    ∀ r ∈ μ.transpose.rowLens, 1 ≤ r ∧ r ≤ 4 := by
  intro r hr
  refine ⟨μ.transpose.pos_of_mem_rowLens r hr, ?_⟩
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hr
  rw [← he, YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose]
  exact (μ.colLen_anti 0 j (Nat.zero_le _)).trans hμ

lemma fourRow_tableau_noncancellation (n : ℕ) (μ : YoungDiagram)
    (hn : μ.transpose.rowLens.sum = n) (hμ : μ.colLen 0 ≤ 4) :
    ∃ s : Tableau n μ, chainFunctional n 1
      (wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
        Band.conjugation (Band.basis i.val) (parts a).1 (parts a).2) (polytabloid s)) 0 0 ≠ 0 := by
  subst n
  refine ⟨Columns.columnTableau μ, ?_⟩
  rw [chainFunctional_column μ 1 (fun i => Band.conjugation (Band.basis i)),
    Band.segments_conjugation]
  exact Band.conjugation_blocks_ne_zero _ (fourRow_column_lengths μ hμ)

/- The actual complex Specht modules with at most four rows occur in the
specified two-layer alternating path cyclic module. -/
theorem fourRow_support (r : ℕ) (_hr : 2 ≤ r) (μ : YoungDiagram)
    (t : Tableau (2*r+1) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r+1) 4) (bandWord r)).toRepresentation, f ≠ 0 := by
  have hn : μ.transpose.rowLens.sum = 2*r+1 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr ((Columns.columnTableau μ).trans t.symm)
  obtain ⟨s, hs⟩ := fourRow_tableau_noncancellation (2*r+1) μ hn hμ
  let L : Fin (μ.colLen 0) → Fin 4 → ℂ := fun i a =>
    Band.conjugation (Band.basis i.val) (parts a).1 (parts a).2
  apply hom_to_cyclic_of_pair L (spechtSub t)
    ⟨polytabloid s, polytabloid_mem_all t s⟩ (bandWord r) (bandWord_real r)
  intro h
  rw [chainFunctional_endpoint] at hs
  exact hs (by change (-1 : ℂ)^r * dotProduct (wordMap L (polytabloid s)) (bandWord r) = 0
               rw [h, mul_zero])

end Saxl.Path

namespace Saxl.PathLayer

lemma J_flip (a b : Fin 2) : J a b = - J b a := by
  fin_cases a <;> fin_cases b <;> (first | (simp [J]; all_goals first | (norm_num [J]; done) | rfl | decide) | (norm_num [J]; done) | norm_num [J])

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
end

section
-- module Solutions.OAIQ259_US.Saxl_BandSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply _root_.OAI.Saxl.staircase_rowLen _root_.OAI.Saxl.staircase_transpose _root_.OAI.Saxl.tableauInclusion_cell _root_.OAI.UniversalTensorSquare.candidate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
theorem twoBand_support_uts_oai (h : ℕ) (hh : 1 ≤ h) (μ : YoungDiagram)
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

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.twoBand_support_uts_oai := @OAI.Saxl.twoBand_support_uts_oai
