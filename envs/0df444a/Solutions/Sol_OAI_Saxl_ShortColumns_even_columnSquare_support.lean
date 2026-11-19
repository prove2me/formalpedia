-- Prove2me | solution 1 for OAI.Saxl.ShortColumns.even_columnSquare_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T22:15:39.170852+00:00
-- url     : https://prove2.me/submissions/f0c7afc1-7fc3-46cc-ac92-43fc32081032

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_even_rows_shortPair_support

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
-- module Solutions.OAIQ259_US.Saxl_PathAlternation
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl.PathLayer

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



end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ShortColumns
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short Columns. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.ShortColumns

lemma shortPairForm_eq (i j : Fin 4) :
    shortPairForm i j = PathLayer.J ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).1 ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm j).1 *
      PathLayer.J ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).2 ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm j).2 := by
  fin_cases i <;> fin_cases j <;>
    (first | (simp [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]; all_goals first | (norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]; done) | rfl | decide) | (norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]; done) | norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat])

lemma evenTableau_polytabloid (b : ℕ) :
    letterLift (Fin.castLE (height_le b 0)) (polytabloid (evenTableau b)) = evenAlt b := by
  rw [polytabloid_eq_altWord, letterLift_altWord]
  rfl

lemma evenAlt_step (b : ℕ) :
    evenAlt (b+1) = positionProduct (appendEven b) (evenAlt b)
      (altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i)) := by
  have hs (i : Fin (2*(b+1))) :
      (appendEven b i).isLeft = true ↔ i.val/2 < b := by
    obtain ⟨j,rfl⟩ := (appendEven b).symm.surjective i
    cases j with
    | inl j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, true_iff,
        appendEven_left]; omega
    | inr j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true,
        appendEven_right, false_iff]; omega
  have hg : fiberGroup (fun i : Fin (2*(b+1)) => i.val/2) =
      fiberGroup (fun i : Fin (2*(b+1)) => i.val/2) ⊓
        sectorGroup (fun i => (appendEven b i).isLeft = true) := by
    apply le_antisymm
    · intro g hg
      refine ⟨hg, ?_⟩
      intro i
      change (appendEven b (g i)).isLeft = true ↔ (appendEven b i).isLeft = true
      rw [hs,hs]
      exact congrArg (fun k => k < b) (hg i) |>.to_iff
    · exact inf_le_left
  have hr : fiberGroup (fun i : Fin 2 => ((appendEven b).symm (Sum.inr i)).val/2) = ⊤ := by
    apply Subgroup.ext
    intro g
    change (∀ i, _ = _) ↔ True
    simp only [appendEven_right]
    constructor
    · intro _; trivial
    · intro _ i; have hi := i.isLt; have hgi := (g i).isLt; omega
  unfold evenAlt
  rw [hg, altWord_fiber_split, hr]
  congr 2
  funext i
  apply Fin.ext
  change (2*b+i.val)%2 = i.val
  omega

lemma evenAlt_zero (w : Fin 0 → Fin 2) : evenAlt 0 w = 1 := by
  classical
  let := Fintype.ofFinite (fiberGroup (fun i : Fin (2*0) => i.val/2))
  have hu : (Finset.univ : Finset (fiberGroup (fun i : Fin (2*0) => i.val/2))) = {1} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  unfold evenAlt altWord
  rw [hu, Finset.sum_singleton]
  simp only [OneMemClass.coe_one, map_one, one_smul]
  change (Pi.single (fun i : Fin 0 => (⟨i.val%2, _⟩ : Fin 2)) (1 : ℂ) : WordSpace 0 2) w = 1
  rw [Pi.single_apply, ite_eq_left (Subsingleton.elim _ _)]

lemma evenAlt_formula (b : ℕ) (w : Fin (2*b) → Fin 2) :
    evenAlt b w = ∏ i : Fin b,
      PathLayer.J (w ⟨2*i.val,by omega⟩) (w ⟨2*i.val+1,by omega⟩) := by
  induction b with
  | zero => simpa using evenAlt_zero w
  | succ b ih =>
    rw [evenAlt_step]
    change evenAlt b (leftWord (appendEven b) w) *
      altWord ⊤ (fun i : Fin 2 => i) (rightWord (appendEven b) w) = _
    rw [ih, PathLayer.pair_alt, Fin.prod_univ_castSucc]
    rfl

lemma even_square (b : ℕ) :
    wordTensor (2*b) 2 2 (evenAlt b ⊗ₜ[ℂ] evenAlt b) =
      pairFormTensor (pairSplit b) shortPairForm := by
  funext w
  rw [wordTensor_tmul, evenAlt_formula, evenAlt_formula]
  change (∏ i : Fin b, _) * (∏ i : Fin b, _) =
    ∏ i, shortPairForm (leftWord (pairSplit b) w i) (rightWord (pairSplit b) w i)
  simp only [shortPairForm_eq, leftWord, rightWord, Finset.prod_mul_distrib,
    splitLeft, splitRight]
  rfl

end Saxl.ShortColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OneExtra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One Extra. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

namespace ShortColumns

theorem even_columnSquare_support_oai (b : ℕ) (μ : YoungDiagram) (t : Tableau (2*b) μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (columnSquareCyclic (evenTableau b)).toRepresentation, F ≠ 0 := by
  let F := pairWordMap (n := 2*b) (letterLift (Fin.castLE (height_le b 0)))
    (letterLift (Fin.castLE (height_le b 0)))
  have hF : F (columnSquareWord (evenTableau b)) =
      pairFormTensor (pairSplit b) shortPairForm := by
    change pairWordMap _ _ (wordTensor _ _ _ (_ ⊗ₜ[ℂ] _)) = _
    rw [pairWordMap_tensor, evenTableau_polytabloid, even_square]
  have hs := even_rows_shortPair_support (pairSplit b) μ t he hd
  rw [← hF] at hs
  obtain ⟨g,hg⟩ := hs
  exact cyclic_projection_support F (columnSquareWord (evenTableau b)) g hg

end ShortColumns
end Saxl
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.ShortColumns.even_columnSquare_support_oai := @OAI.Saxl.ShortColumns.even_columnSquare_support_oai
