-- Prove2me | solution 1 for OAI.Saxl.Balance.short_pair_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:08:10.383166+00:00
-- url     : https://prove2.me/submissions/b594115b-8686-42a5-8bba-f177052ae580

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_Columns_two_path_cyclic_support_placed

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
-- module Solutions.OAIQ259_US.Saxl_HighProjection
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/


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

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SignEquivalence
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

lemma signTwist_irreducible {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (signTwist ρ) := by
  let cv : Subrepresentation (signTwist ρ) ≃o Subrepresentation ρ :=
    { toFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            have h := S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx)
            change signC g • (signC g • (ρ g x)) ∈ S.toSubmodule at h
            simpa only [smul_smul, signC_mul_self, one_smul] using h }
      invFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            exact S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx) }
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl
      map_rel_iff' := by intros; rfl }
  exact cv.isSimpleOrder_iff.mpr inferInstance

lemma orbitAverage_base {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (a : Fin n → Fin d) (y : V)
    (hy : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ρ g y = y) :
    orbitAverage ρ a y (Pi.single a 1) =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => a ∘ g = a)).card : ℂ) • y := by
  classical
  change (∑ g : Equiv.Perm (Fin n), (Pi.single a (1 : ℂ) : WordSpace n d) (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y) = _
  have hi (g : Equiv.Perm (Fin n)) : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a ↔ a ∘ g = a := by
    constructor <;> intro hh <;> funext i
    · have he := congrFun hh (g i); simpa using he.symm
    · have he := congrFun hh (g⁻¹ i); simpa using he.symm
  simp only [Pi.single_apply, hi]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_congr rfl (fun g hg => hy g (Finset.mem_filter.mp hg).2)]
  simp [Nat.cast_smul_eq_nsmul]

end Saxl

namespace Saxl
/- Sign-conjugacy proved using the column-antisymmetrized row tabloids. -/
theorem specht_sign_transpose {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) := by
  classical
  let tt := transposeTableau t
  let y : Specht tt := ⟨polytabloid tt, mem_cyclic _ _⟩
  let R := signTwist (spechtRep tt)
  let F := orbitAverage R (rowWord t) y
  let c : ℂ := ((Finset.univ.filter
    (fun g : Equiv.Perm (Fin n) => rowWord t ∘ g = rowWord t)).card : ℂ)
  have hy : ∀ g : Equiv.Perm (Fin n), rowWord t ∘ g = rowWord t → R g y = y := by
    intro g hg
    have hc : g ∈ columnGroup tt := by
      intro i
      exact congrArg Fin.val (congrFun hg i)
    apply Subtype.ext
    change signC g • wordRep n (μ.transpose.colLen 0) g (polytabloid tt) = polytabloid tt
    rw [polytabloid_alternating tt ⟨g, hc⟩, smul_smul, signC_mul_self, one_smul]
  have hF : F (Pi.single (rowWord t) 1) = c • y := orbitAverage_base R _ y hy
  have hc0 : c ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rfl
  have hm (g : columnGroup t) :
      (F (wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n))
        (Pi.single (rowWord t) 1))).val (rowWord tt) = signC (g : Equiv.Perm (Fin n)) * c := by
    rw [F.isIntertwining, hF]
    change signC (g : Equiv.Perm (Fin n)) * (c *
      polytabloid tt (rowWord tt ∘ (g : Equiv.Perm (Fin n)))) = _
    have he : rowWord tt ∘ (g : Equiv.Perm (Fin n)) = rowWord tt := by
      funext i
      apply Fin.ext
      exact g.property i
    rw [he, polytabloid_rowWord, mul_one]
  let inc : Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) :=
    { toLinearMap := (spechtSub t).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let f := F.comp inc
  have hf : f ≠ 0 := by
    intro hz
    have he : (F (polytabloid t)).val (rowWord tt) = 0 := by
      have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) R =>
        (l ⟨polytabloid t, mem_cyclic _ _⟩).val (rowWord tt)) hz
      exact he
    let := Fintype.ofFinite (columnGroup t)
    have hp : (F (polytabloid t)).val (rowWord tt) =
        (Fintype.card (columnGroup t) : ℂ) * c := by
      change (F (∑ g : columnGroup t, signC (g : Equiv.Perm (Fin n)) •
        wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1))).val _ = _
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]
      simp only [← mul_assoc, signC_mul_self, one_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_ne_zero hn hc0) (hp.symm.trans he)
  let := specht_irreducible t
  let := specht_irreducible tt
  let := signTwist_irreducible (spechtRep tt)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_StaircaseSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY uZ

namespace Saxl

lemma alternating_specht_line {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (y : Specht t) (hy : ∀ g : columnGroup t,
      spechtRep t g.val y = signC g.val • y) :
    ∃ c : ℂ, y.val = c • polytabloid t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  have he : columnAlt t y.val = (Fintype.card (columnGroup t) : ℂ) • y.val := by
    change (∑ g : columnGroup t, signC g.val • wordRep n (μ.colLen 0) g.val) y.val = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    have hh (g : columnGroup t) : wordRep n (μ.colLen 0) g.val y.val = signC g.val • y.val :=
      congrArg Subtype.val (hy g)
    simp only [hh, smul_smul, signC_mul_self, one_smul, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hm := columnAlt_tabloid t (spechtSub_le_tabloidSub t y.property)
  rw [he] at hm
  have hc : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hx : y.val ∈ Submodule.span ℂ {polytabloid t} :=
    (Submodule.smul_mem_iff _ hc).mp hm
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hx
  exact ⟨c,hc.symm⟩

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ShortColumns
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

lemma oddTableau_row (b : ℕ) (i : Fin (2*b+1)) :
    ((oddTableau b) i).val.1 = (PathLayer.base i).val := by
  simp only [oddTableau, Equiv.coe_fn_mk, PathLayer.base]
  split_ifs <;> rfl

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

lemma intertwining_comp_ne_zero {G X Y Z : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap σ τ) (hF : Function.Injective F)
    (f : Representation.IntertwiningMap ρ σ) (hf : f ≠ 0) : F.comp f ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hh := congrArg (fun H => H x) hz
  exact hh.trans (map_zero F).symm

lemma transposeTableau_move {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    tableauMove (transposeTableau s) (transposeTableau t) = tableauMove s t := by
  ext i
  rfl

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CoordinateLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate Line. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma projectedCoordinate_pair {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) (x : Specht t) :
    dotProduct (projectedCoordinate t a).val x.val = x.val a := by
  exact congrArg (fun f : Module.Dual ℂ (Specht t) => f x)
    ((spechtSelfDual t).apply_symm_apply (coordinateRestriction t a))

lemma projectedCoordinate_nonzero {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ) :
    projectedCoordinate t (rowWord s) ≠ 0 := by
  intro hz
  have h := projectedCoordinate_pair t (rowWord s)
    ⟨polytabloid s, polytabloid_mem_all t s⟩
  rw [hz] at h
  have h0 : (0 : ℂ) = 1 := by
    simpa only [ZeroMemClass.coe_zero, zero_dotProduct, polytabloid_rowWord] using h
  exact zero_ne_one h0

lemma coordinateRestriction_fixed {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ)
    (g : columnGroup (transposeTableau s)) :
    (spechtRep t).dual g.val (coordinateRestriction t (rowWord s)) =
      coordinateRestriction t (rowWord s) := by
  ext x
  change x.val (rowWord s ∘ ((g.val)⁻¹ : Equiv.Perm (Fin n))) = x.val (rowWord s)
  apply congrArg x.val
  funext i
  apply Fin.ext
  exact g⁻¹.property i

lemma projectedCoordinate_fixed {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ)
    (g : columnGroup (transposeTableau s)) :
    spechtRep t g.val (projectedCoordinate t (rowWord s)) =
      projectedCoordinate t (rowWord s) := by
  have h := LinearMap.congr_fun ((spechtSelfDual t).symm.isIntertwining' g.val)
    (coordinateRestriction t (rowWord s))
  simp only [LinearMap.comp_apply] at h
  rw [coordinateRestriction_fixed] at h
  exact h.symm

theorem signEquiv_coordinate_line {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (projectedCoordinate t (rowWord s))).val =
      c • polytabloid (transposeTableau s) := by
  let y : Specht (transposeTableau s) :=
    ⟨(φ (projectedCoordinate t (rowWord s))).val,
      by change _ ∈ (spechtSub (transposeTableau s)).toSubmodule
         rw [← spechtSub_tableau_independent (transposeTableau t) (transposeTableau s)]
         exact (φ (projectedCoordinate t (rowWord s))).property⟩
  have ha (g : columnGroup (transposeTableau s)) :
      spechtRep (transposeTableau s) g.val y = signC g.val • y := by
    have he := LinearMap.congr_fun (φ.isIntertwining' g.val)
      (projectedCoordinate t (rowWord s))
    change φ (spechtRep t g.val (projectedCoordinate t (rowWord s))) =
      signC g.val • spechtRep (transposeTableau t) g.val
        (φ (projectedCoordinate t (rowWord s))) at he
    rw [projectedCoordinate_fixed] at he
    have hh := congrArg (fun x => signC g.val • x.val) he
    change signC g.val • (φ (projectedCoordinate t (rowWord s))).val =
      signC g.val • (signC g.val • wordRep _ _ g.val
        (φ (projectedCoordinate t (rowWord s))).val) at hh
    apply Subtype.ext
    change wordRep _ _ g.val (φ (projectedCoordinate t (rowWord s))).val =
      signC g.val • (φ (projectedCoordinate t (rowWord s))).val
    simpa only [Submodule.coe_smul_of_tower, smul_smul, signC_mul_self, one_smul]
      using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (transposeTableau s) y ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply projectedCoordinate_nonzero t s
  apply φ.injective
  exact (Subtype.ext hc).trans (map_zero φ).symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_DualTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual Transfer. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma intertwiningFlip_ne_zero {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (f : Representation.IntertwiningMap ρ σ.dual) (hf : f ≠ 0) :
    intertwiningFlip f ≠ 0 := by
  intro hz
  apply hf
  ext x y
  exact congrArg (fun F => F y x) hz

theorem specht_support_of_dual {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) Y)
    (f : Representation.IntertwiningMap (spechtRep t) σ.dual) (hf : f ≠ 0) :
    ∃ h : Representation.IntertwiningMap (spechtRep t) σ, Function.Injective h := by
  let F := (spechtSelfDual t).symm.toIntertwiningMap.comp (intertwiningFlip f)
  have hF : F ≠ 0 := intertwining_comp_ne_zero
    (spechtSelfDual t).symm.toIntertwiningMap (spechtSelfDual t).symm.injective
    (intertwiningFlip f) (intertwiningFlip_ne_zero f hf)
  let := specht_irreducible t
  have hs : Function.Surjective F :=
    (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  obtain ⟨h, hh⟩ := intertwining_lift_surjective F hs
    (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨h, ?_⟩
  intro x y he
  have hx := congrArg (fun H => H x) hh
  have hy := congrArg (fun H => H y) hh
  exact hx.symm.trans ((congrArg F he).trans hy)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ProjectedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projected Tensor. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma projectedTensorEvaluation_pullback {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w)
    (v : Fin n → Fin (α.colLen 0)) (w : Fin n → Fin (β.colLen 0))
    (hp : P (mergeWords v w)) :
    intertwiningDual (X := Specht a ⊗[ℂ] Specht b) (projectedTensorQuotient a b P hP)
      (projectedTensorEvaluation a b P hP (mergeWords v w)) =
      tensorDualEquiv (spechtRep a) (spechtRep b)
        (coordinateRestriction a v ⊗ₜ[ℂ] coordinateRestriction b w) := by
  classical
  ext x y
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.coe_restrictScalars, TensorProduct.curry_apply]
  have hR : (tensorDualEquiv (spechtRep a) (spechtRep b)) (coordinateRestriction a v ⊗ₜ[ℂ] coordinateRestriction b w) (x ⊗ₜ[ℂ] y) = y.val w * x.val v := by
    change TensorProduct.dualDistrib ℂ _ _ (_ ⊗ₜ[ℂ] _) (x ⊗ₜ[ℂ] y) = _
    rw [TensorProduct.dualDistrib_apply]
    exact mul_comm _ _
  rw [hR]
  change coordinateProjection P (spechtTensorMap a b (x ⊗ₜ[ℂ] y)) (mergeWords v w) = y.val w * x.val v
  rw [coordinateProjection_apply, ite_eq_left hp]
  rw [spechtTensorMap]
  change wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val) (mergeWords v w) = _
  simp only [wordTensor_tmul, splitLeft_merge, splitRight_merge, mul_comm]

lemma dualTensorSignMap_coordinates {n : ℕ} {α β : YoungDiagram}
    (a s : Tableau n α) (b t : Tableau n β)
    (φ : (spechtRep a).Equiv (signTwist (spechtRep (transposeTableau a))))
    (ψ : (spechtRep b).Equiv (signTwist (spechtRep (transposeTableau b)))) :
    ∃ c : ℂ, c ≠ 0 ∧
      dualTensorSignMap a b φ ψ
        (tensorDualEquiv (spechtRep a) (spechtRep b)
          (coordinateRestriction a (rowWord s) ⊗ₜ[ℂ] coordinateRestriction b (rowWord t))) =
        c • wordTensor _ _ _
          (polytabloid (transposeTableau s) ⊗ₜ[ℂ] polytabloid (transposeTableau t)) := by
  obtain ⟨c,hc,hφ⟩ := signEquiv_coordinate_line a s φ
  obtain ⟨d,hd,hψ⟩ := signEquiv_coordinate_line b t ψ
  refine ⟨c*d, mul_ne_zero hc hd, ?_⟩
  change spechtTensorMap (transposeTableau a) (transposeTableau b)
    (TensorProduct.map (dualSignMap a φ).toLinearMap (dualSignMap b ψ).toLinearMap
      ((tensorDualEquiv (spechtRep a) (spechtRep b)).symm
        (tensorDualEquiv (spechtRep a) (spechtRep b)
          (coordinateRestriction a (rowWord s) ⊗ₜ[ℂ] coordinateRestriction b (rowWord t))))) = _
  rw [Representation.Equiv.symm_apply_apply, TensorProduct.map_tmul]
  rw [spechtTensorMap]
  change wordTensor _ _ _
    ((φ (projectedCoordinate a (rowWord s))).val ⊗ₜ[ℂ]
      (ψ (projectedCoordinate b (rowWord t))).val) = _
  rw [hφ,hψ,TensorProduct.smul_tmul_smul,map_smul]

theorem pair_coordinate_in_projected_dual_image {n : ℕ} {α β : YoungDiagram}
    (a s : Tableau n α) (b t : Tableau n β)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w)
    (hp : P (mergeWords (rowWord s) (rowWord t)))
    (φ : (spechtRep a).Equiv (signTwist (spechtRep (transposeTableau a))))
    (ψ : (spechtRep b).Equiv (signTwist (spechtRep (transposeTableau b)))) :
    wordTensor _ _ _ (polytabloid (transposeTableau s) ⊗ₜ[ℂ]
      polytabloid (transposeTableau t)) ∈
      ((dualTensorSignMap a b φ ψ).comp
        (intertwiningDual (X := Specht a ⊗[ℂ] Specht b) (projectedTensorQuotient a b P hP))).range := by
  obtain ⟨c,hc,he⟩ := dualTensorSignMap_coordinates a s b t φ ψ
  apply (Submodule.smul_mem_iff _ hc).mp
  refine ⟨projectedTensorEvaluation a b P hP (mergeWords (rowWord s) (rowWord t)), ?_⟩
  change dualTensorSignMap a b φ ψ (intertwiningDual (X := Specht a ⊗[ℂ] Specht b) (projectedTensorQuotient a b P hP)
    (projectedTensorEvaluation a b P hP (mergeWords (rowWord s) (rowWord t)))) = _
  rw [projectedTensorEvaluation_pullback a b P hP _ _ hp]
  exact he

theorem projectedTensor_support_of_coordinate {n : ℕ} {α β μ : YoungDiagram}
    (a s : Tableau n α) (b t : Tableau n β) (u : Tableau n μ)
    (P : (Fin n → Fin (α.colLen 0 * β.colLen 0)) → Prop)
    (hP : ∀ (g : Equiv.Perm (Fin n)) w, P (w ∘ g) ↔ P w)
    (hp : P (mergeWords (rowWord s) (rowWord t)))
    (f : Representation.IntertwiningMap (spechtRep u)
      (cyclic (wordRep n (α.transpose.colLen 0 * β.transpose.colLen 0))
        (wordTensor _ _ _ (polytabloid (transposeTableau s) ⊗ₜ[ℂ]
          polytabloid (transposeTableau t)))).toRepresentation) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep u)
      (projectedSpechtTensor a b P hP).toRepresentation, Function.Injective F := by
  obtain ⟨φ⟩ := specht_sign_transpose a
  obtain ⟨ψ⟩ := specht_sign_transpose b
  let Q := (dualTensorSignMap a b φ ψ).comp
    (intertwiningDual (X := Specht a ⊗[ℂ] Specht b) (projectedTensorQuotient a b P hP))
  have hm := pair_coordinate_in_projected_dual_image a s b t P hP hp φ ψ
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range Q
    (cyclic (wordRep n (α.transpose.colLen 0 * β.transpose.colLen 0))
      (wordTensor _ _ _ (polytabloid (transposeTableau s) ⊗ₜ[ℂ]
        polytabloid (transposeTableau t)))) ((cyclic_le _ _ _).mpr hm)
  exact specht_support_of_dual u _ (i.comp f) (intertwining_comp_ne_zero i hi f hf)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Extensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extensions. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.Path

theorem odd_path_support (r : ℕ) (μ : YoungDiagram)
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
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Neighboring
attribute [-simp] _root_.OAI.Saxl.Balance.appendShortCells_left _root_.OAI.Saxl.Balance.appendShortCells_right _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Neighboring. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl
namespace Balance

lemma neighborLayer_row (r : ℕ) (i : Fin (2*r+1)) :
    ((neighborLayer r) i).val.1 = (PathLayer.base i).val :=
  ShortColumns.oddTableau_row r i

lemma neighborLayer_col (r : ℕ) (i : Fin (2*r+1)) :
    ((neighborLayer r) i).val.2 = if i.val = 0 then r else r-1-(i.val-1)/2 := by
  have hi := i.isLt
  simp only [neighborLayer, Equiv.trans_apply, reverseShortColumns, Equiv.coe_fn_mk,
    ShortColumns.oddTableau, reverseShortColumn]
  split_ifs <;> dsimp only at * <;> omega

lemma neighborLayer_col_iff (r : ℕ) (i j : Fin (2*r+1)) :
    ((neighborLayer r) i).val.2 = ((neighborLayer r) j).val.2 ↔
      PathLayer.tag i = PathLayer.tag j := by
  have hi := i.isLt
  have hj := j.isLt
  rw [neighborLayer_col, neighborLayer_col]
  simp only [PathLayer.tag]
  split_ifs <;> omega

lemma neighborLayer_group (r : ℕ) :
    columnGroup (neighborLayer r) = fiberGroup (@PathLayer.tag r) := by
  apply Subgroup.ext
  intro g
  change (∀ i, ((neighborLayer r) (g i)).val.2 = ((neighborLayer r) i).val.2) ↔ _
  simp only [neighborLayer_col_iff]
  rfl

lemma neighborLayer_polytabloid (r : ℕ) :
    letterLift (Fin.castLE (ShortColumns.height_le r 1)) (polytabloid (neighborLayer r)) =
      PathLayer.rowAlt r := by
  rw [polytabloid_eq_altWord, letterLift_altWord, neighborLayer_group]
  congr 1
  funext i
  apply Fin.ext
  exact neighborLayer_row r i

lemma neighbor_outputs (r : ℕ) :
    inOutputs (Set.Icc r (r+1))
      (mergeWords (rowWord (neighborTableau r)) (rowWord (neighborRight r))) := by
  intro i
  simp only [output, mergeWords, Equiv.symm_apply_apply]
  change ((neighborLayer r i).val.2 + (neighborLayer r i.rev).val.2 + 1) ∈ Set.Icc r (r+1)
  rw [neighborLayer_col, neighborLayer_col]
  simp only [Set.mem_Icc, Fin.val_rev]
  have hi := i.isLt
  split_ifs <;> omega

lemma letterLift_comp {n a b c : ℕ} (f : Fin a → Fin b) (g : Fin b → Fin c) :
    letterLift (n := n) (g ∘ f) = (letterLift g).comp (letterLift f) := by
  classical
  apply Representation.IntertwiningMap.ext
  apply LinearMap.pi_ext
  intro w c
  have he : (Pi.single w c : WordSpace n a) = c • Pi.single w 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [he, map_smul, map_smul]
  congr 1
  change letterLift (g ∘ f) (Pi.single w 1) = letterLift g (letterLift f (Pi.single w 1))
  rw [letterLift_single, letterLift_single, letterLift_single]
  rfl

lemma neighbor_left_word (r : ℕ) :
    letterLift (neighborLetter r) (polytabloid (transposeTableau (neighborTableau r))) =
      PathLayer.rowAlt r := by
  rw [neighborLetter, letterLift_comp]
  change letterLift _ (letterLift _
    (polytabloid (transposeTableau (transposeTableau (neighborLayer r))))) = _
  rw [polytabloid_doubleTranspose, neighborLayer_polytabloid]

lemma neighbor_move (r : ℕ) :
    tableauMove (transposeTableau (neighborTableau r))
      (transposeTableau (neighborRight r)) = Fin.revPerm := by
  rw [transposeTableau_move]
  apply Equiv.ext
  intro i
  simp only [tableauMove, Equiv.trans_apply, neighborRight,
    Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rfl

lemma neighbor_right_word (r : ℕ) :
    letterLift (neighborLetter r) (polytabloid (transposeTableau (neighborRight r))) =
      wordRep (2*r+1) 2 Fin.revPerm (PathLayer.rowAlt r) := by
  rw [polytabloid_move (transposeTableau (neighborTableau r))
    (transposeTableau (neighborRight r)), neighbor_move]
  rw [Representation.IntertwiningMap.isIntertwining]
  rw [neighbor_left_word]

lemma neighbor_pair_word (r : ℕ) :
    pairWordMap (letterLift (neighborLetter r)) (letterLift (neighborLetter r))
      (wordTensor _ _ _ (polytabloid (transposeTableau (neighborTableau r)) ⊗ₜ[ℂ]
        polytabloid (transposeTableau (neighborRight r)))) =
      (-1 : ℂ)^r • Path.bandWord r := by
  rw [pairWordMap_tensor, neighbor_left_word, neighbor_right_word]
  funext w
  rw [wordTensor_tmul]
  exact PathLayer.paired_rowAlt r w

theorem neighboring (r : ℕ)
    (a b : Tableau (2*r+1) (ShortColumns.shape r 1).transpose)
    (μ : YoungDiagram) (t : Tableau (2*r+1) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a b (inOutputs (Set.Icc r (r+1)))
        (inOutputs_invariant (Set.Icc r (r+1)))).toRepresentation, Function.Injective F := by
  let D := pairWordMap (n := 2*r+1)
    (letterLift (neighborLetter r)) (letterLift (neighborLetter r))
  let v := wordTensor _ _ _
    (polytabloid (transposeTableau (neighborTableau r)) ⊗ₜ[ℂ]
      polytabloid (transposeTableau (neighborRight r)))
  have hs : ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r+1) 4) (D v)).toRepresentation, f ≠ 0 := by
    dsimp only [D, v]
    rw [neighbor_pair_word, cyclic_smul_eq _ _ _ (pow_ne_zero r (by norm_num))]
    exact Path.odd_path_support r μ t hμ
  obtain ⟨f,hf⟩ := hs
  obtain ⟨g,hg⟩ := cyclic_projection_support D v f hf
  exact projectedTensor_support_of_coordinate a (neighborTableau r)
    b (neighborRight r) t _ _ (neighbor_outputs r) g hg

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_TwoPathContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Path Contraction. -/

section

noncomputable section
namespace Saxl.Columns

theorem odd_column_split (q : ℕ) (μ : YoungDiagram)
    (hn : μ.card = 2*q+2) (hμ : μ.colLen 0 ≤ 4)
    (ho : ∃ j, μ.colLen j % 2 = 1) :
    ∃ p rs, p ≤ q ∧ 2*p+1 ≤ 4 ∧
      (∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) ∧ rs.sum = 2*(q-p)+1 ∧
      ((2*p+1)::rs).Perm μ.transpose.rowLens := by
  classical
  obtain ⟨j,hj⟩ := ho
  have hp : 0 < μ.colLen j := by omega
  have hjlt : j < μ.transpose.colLen 0 := by
    rw [YoungDiagram.colLen_transpose]
    exact YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr hp)
  have hmem : μ.colLen j ∈ μ.transpose.rowLens := by
    have hjl : j < μ.transpose.rowLens.length := by simpa using hjlt
    have he := List.getElem_mem hjl
    simpa only [YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose] using he
  let rs := μ.transpose.rowLens.erase (μ.colLen j)
  have hperm : ((μ.colLen j)::rs).Perm μ.transpose.rowLens :=
    (List.perm_cons_erase hmem).symm
  have hs : μ.colLen j + rs.sum = 2*q+2 := by
    have h := hperm.sum_eq
    rw [List.sum_cons, ← card_eq_sum_rowLens, transpose_card, hn] at h
    exact h
  have hu := (μ.colLen_anti 0 j (Nat.zero_le _)).trans hμ
  refine ⟨(μ.colLen j)/2, rs, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro a ha
    have ha' := List.mem_of_mem_erase ha
    exact Path.fourRow_column_lengths μ hμ a ha'
  · omega
  · have he : 2*(μ.colLen j/2)+1 = μ.colLen j := by omega
    simpa only [he] using hperm

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoPathGeometry
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Path Geometry. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

lemma appendShortCells_column_same (p r q : ℕ) (hq : p+r=q)
    (x y : (ShortColumns.shape p 1).cells ⊕ (ShortColumns.shape r 1).cells)
    (h : (appendShortCells p r q hq x).val.2 =
      (appendShortCells p r q hq y).val.2) : x.isLeft = y.isLeft := by
  cases x with
  | inl x =>
    cases y with
    | inl y => rfl
    | inr y =>
      have hx := (ShortColumns.mem_shape p 1 x.val.1 x.val.2).mp x.property
      have hy := (ShortColumns.mem_shape r 1 y.val.1 y.val.2).mp y.property
      simp only [appendShortCells_left, appendShortCells_right] at h
      split_ifs at h <;> omega
  | inr x =>
    cases y with
    | inr y => rfl
    | inl y =>
      have hx := (ShortColumns.mem_shape r 1 x.val.1 x.val.2).mp x.property
      have hy := (ShortColumns.mem_shape p 1 y.val.1 y.val.2).mp y.property
      simp only [appendShortCells_left, appendShortCells_right] at h
      split_ifs at h <;> omega

lemma appendShortCells_left_col (p r q : ℕ) (hq : p+r=q)
    (x y : (ShortColumns.shape p 1).cells) :
    (appendShortCells p r q hq (Sum.inl x)).val.2 =
      (appendShortCells p r q hq (Sum.inl y)).val.2 ↔ x.val.2 = y.val.2 := by
  have hx := (ShortColumns.mem_shape p 1 x.val.1 x.val.2).mp x.property
  have hy := (ShortColumns.mem_shape p 1 y.val.1 y.val.2).mp y.property
  simp only [appendShortCells_left]
  split_ifs <;> omega

lemma appendShortCells_right_col (p r q : ℕ) (hq : p+r=q)
    (x y : (ShortColumns.shape r 1).cells) :
    (appendShortCells p r q hq (Sum.inr x)).val.2 =
      (appendShortCells p r q hq (Sum.inr y)).val.2 ↔ x.val.2 = y.val.2 := by
  have hx := (ShortColumns.mem_shape r 1 x.val.1 x.val.2).mp x.property
  have hy := (ShortColumns.mem_shape r 1 y.val.1 y.val.2).mp y.property
  simp only [appendShortCells_right]
  split_ifs <;> omega

lemma appendShort_polytabloid {n a b : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ShortColumns.shape p 1))
    (t : Tableau b (ShortColumns.shape r 1)) :
    letterLift (Fin.castLE (ShortColumns.height_le q 2))
      (polytabloid (appendShortTableau p r q hq e s t)) =
      positionProduct e
        (letterLift (Fin.castLE (ShortColumns.height_le p 1)) (polytabloid s))
        (letterLift (Fin.castLE (ShortColumns.height_le r 1)) (polytabloid t)) := by
  let T := appendShortTableau p r q hq e s t
  let f := fun i => (T i).val.2
  have hs (i : Fin a) : T (e.symm (Sum.inl i)) =
      appendShortCells p r q hq (Sum.inl (s i)) := by simp [T, appendShortTableau]
  have ht (i : Fin b) : T (e.symm (Sum.inr i)) =
      appendShortCells p r q hq (Sum.inr (t i)) := by simp [T, appendShortTableau]
  have hf : fiberGroup f = fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true) := by
    apply le_antisymm
    · intro g hg
      refine ⟨hg, ?_⟩
      intro i
      have hh := appendShortCells_column_same p r q hq
        ((s.sumCongr t) (e (g i))) ((s.sumCongr t) (e i)) (hg i)
      have he (i : Fin n) : ((s.sumCongr t) (e i)).isLeft = (e i).isLeft := by
        cases e i <;> rfl
      rw [he, he] at hh
      change (e (g i)).isLeft = true ↔ (e i).isLeft = true
      rw [hh]
    · exact inf_le_left
  have hl : fiberGroup (fun i => f (e.symm (Sum.inl i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (T (e.symm (Sum.inl (g i)))).val.2 =
      (T (e.symm (Sum.inl i))).val.2) ↔ (∀ i, (s (g i)).val.2 = (s i).val.2)
    simp only [hs, appendShortCells_left_col]
  have hr : fiberGroup (fun i => f (e.symm (Sum.inr i))) = columnGroup t := by
    apply Subgroup.ext
    intro g
    change (∀ i, (T (e.symm (Sum.inr (g i)))).val.2 =
      (T (e.symm (Sum.inr i))).val.2) ↔ (∀ i, (t (g i)).val.2 = (t i).val.2)
    simp only [ht, appendShortCells_right_col]
  rw [polytabloid_eq_altWord, letterLift_altWord]
  change altWord (fiberGroup f) _ = _
  rw [hf, altWord_fiber_split, hl, hr,
    polytabloid_eq_altWord, polytabloid_eq_altWord, letterLift_altWord, letterLift_altWord]
  congr 2
  · funext i
    apply Fin.ext
    change (T (e.symm (Sum.inl i))).val.1 = (s i).val.1
    rw [hs]
    rfl
  · funext i
    apply Fin.ext
    change (T (e.symm (Sum.inr i))).val.1 = (t i).val.1
    rw [ht]
    rfl

lemma appendShortCells_left_neighbor (p r q : ℕ) (hq : p+r=q)
    (i : Fin (2*p+1)) :
    (appendShortCells p r q hq (Sum.inl (neighborLayer p i))).val.2 =
      if i.val = 0 then q else p-1-(i.val-1)/2 := by
  rw [appendShortCells_left, neighborLayer_col]
  have hi := i.isLt
  split_ifs <;> omega

lemma appendShortCells_right_neighbor (p r q : ℕ) (hq : p+r=q)
    (i : Fin (2*r+1)) :
    (appendShortCells p r q hq (Sum.inr (neighborLayer r i))).val.2 =
      if i.val = 0 then q+1 else p+(r-1-(i.val-1)/2) := by
  rw [appendShortCells_right, neighborLayer_col]
  have hi := i.isLt
  split_ifs <;> omega

lemma twoPathLeft_col_left {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) (i : Fin (2*p+1)) :
    (twoPathLeft p r q hq e (e.symm (Sum.inl i))).val.2 =
      if i.val = 0 then q else p-1-(i.val-1)/2 := by
  simp only [twoPathLeft, appendShortTableau, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl]
  exact appendShortCells_left_neighbor p r q hq i

lemma twoPathLeft_col_right {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) (i : Fin (2*r+1)) :
    (twoPathLeft p r q hq e (e.symm (Sum.inr i))).val.2 =
      if i.val = 0 then q+1 else p+(r-1-(i.val-1)/2) := by
  simp only [twoPathLeft, appendShortTableau, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inr]
  exact appendShortCells_right_neighbor p r q hq i

lemma twoPathRight_col_left {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) (i : Fin (2*p+1)) :
    (twoPathRight p r q hq e (e.symm (Sum.inl i))).val.2 =
      if i.rev.val = 0 then q+1 else r+(p-1-(i.rev.val-1)/2) := by
  simp only [twoPathRight, appendShortTableau, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumComm_apply, Sum.swap_inl,
    Equiv.sumCongr_apply, Sum.map_inr]
  exact appendShortCells_right_neighbor r p q (by omega) i.rev

lemma twoPathRight_col_right {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) (i : Fin (2*r+1)) :
    (twoPathRight p r q hq e (e.symm (Sum.inr i))).val.2 =
      if i.rev.val = 0 then q else r-1-(i.rev.val-1)/2 := by
  simp only [twoPathRight, appendShortTableau, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumComm_apply, Sum.swap_inr,
    Equiv.sumCongr_apply, Sum.map_inl]
  exact appendShortCells_left_neighbor r p q (by omega) i.rev

theorem twoPath_outputs {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    inOutputs (Set.Icc q (2*q+3))
      (mergeWords (rowWord (transposeTableau (twoPathLeft p r q hq e)))
        (rowWord (transposeTableau (twoPathRight p r q hq e)))) := by
  intro i
  simp only [output, mergeWords, Equiv.symm_apply_apply]
  change (twoPathLeft p r q hq e i).val.2 +
    (twoPathRight p r q hq e i).val.2 + 1 ∈ Set.Icc q (2*q+3)
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    rw [twoPathLeft_col_left, twoPathRight_col_left]
    simp only [Set.mem_Icc, Fin.val_rev]
    have hj := j.isLt
    split_ifs <;> omega
  | inr j =>
    rw [twoPathLeft_col_right, twoPathRight_col_right]
    simp only [Set.mem_Icc, Fin.val_rev]
    have hj := j.isLt
    split_ifs <;> omega

lemma positionProduct_swap {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) :
    positionProduct (e.trans (Equiv.sumComm _ _)) y x = positionProduct e x y := by
  funext w
  exact mul_comm _ _

lemma neighborLayer_reverse_word (r : ℕ) :
    letterLift (Fin.castLE (ShortColumns.height_le r 1))
      (polytabloid (Fin.revPerm.trans (neighborLayer r))) =
        wordRep (2*r+1) 2 Fin.revPerm (PathLayer.rowAlt r) := by
  rw [polytabloid_move (neighborLayer r) (Fin.revPerm.trans (neighborLayer r))]
  have he : tableauMove (neighborLayer r) (Fin.revPerm.trans (neighborLayer r)) =
      Fin.revPerm := by
    apply Equiv.ext
    intro i
    simp only [tableauMove, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_apply_apply]
    rfl
  rw [he, Representation.IntertwiningMap.isIntertwining, neighborLayer_polytabloid]

lemma twoPathLeft_word {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    letterLift (Fin.castLE (ShortColumns.height_le q 2))
      (polytabloid (twoPathLeft p r q hq e)) =
        positionProduct e (PathLayer.rowAlt p) (PathLayer.rowAlt r) := by
  rw [twoPathLeft, appendShort_polytabloid,
    neighborLayer_polytabloid, neighborLayer_polytabloid]

lemma twoPathRight_word {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    letterLift (Fin.castLE (ShortColumns.height_le q 2))
      (polytabloid (twoPathRight p r q hq e)) =
        positionProduct e (wordRep (2*p+1) 2 Fin.revPerm (PathLayer.rowAlt p))
          (wordRep (2*r+1) 2 Fin.revPerm (PathLayer.rowAlt r)) := by
  rw [twoPathRight, appendShort_polytabloid,
    neighborLayer_reverse_word, neighborLayer_reverse_word, positionProduct_swap]

lemma twoPath_doubleTranspose_word {n : ℕ} (q : ℕ)
    (t : Tableau n (ShortColumns.shape q 2)) :
    letterLift (twoPathLetter q) (polytabloid (transposeTableau (transposeTableau t))) =
      letterLift (Fin.castLE (ShortColumns.height_le q 2)) (polytabloid t) := by
  rw [twoPathLetter, letterLift_comp]
  change letterLift _ (letterLift _ (polytabloid (transposeTableau (transposeTableau t)))) = _
  rw [polytabloid_doubleTranspose]

lemma twoPath_pair_word {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    pairWordMap (letterLift (twoPathLetter q)) (letterLift (twoPathLetter q))
      (wordTensor _ _ _
        (polytabloid (transposeTableau (transposeTableau (twoPathLeft p r q hq e))) ⊗ₜ[ℂ]
          polytabloid (transposeTableau (transposeTableau (twoPathRight p r q hq e))))) =
      (-1 : ℂ)^q • positionProduct e (Path.bandWord p) (Path.bandWord r) := by
  rw [pairWordMap_tensor, twoPath_doubleTranspose_word, twoPath_doubleTranspose_word,
    twoPathLeft_word, twoPathRight_word]
  funext w
  rw [wordTensor_tmul]
  change (PathLayer.rowAlt p (leftWord e (splitLeft w)) *
      PathLayer.rowAlt r (rightWord e (splitLeft w))) *
    (PathLayer.rowAlt p (leftWord e (splitRight w) ∘ Fin.rev) *
      PathLayer.rowAlt r (rightWord e (splitRight w) ∘ Fin.rev)) =
    (-1 : ℂ)^q * (Path.bandWord p (leftWord e w) * Path.bandWord r (rightWord e w))
  have hp := PathLayer.paired_rowAlt p (leftWord e w)
  have hr := PathLayer.paired_rowAlt r (rightWord e w)
  change PathLayer.rowAlt p (leftWord e (splitLeft w)) *
    PathLayer.rowAlt p (leftWord e (splitRight w) ∘ Fin.rev) = _ at hp
  change PathLayer.rowAlt r (rightWord e (splitLeft w)) *
    PathLayer.rowAlt r (rightWord e (splitRight w) ∘ Fin.rev) = _ at hr
  calc
    _ = (PathLayer.rowAlt p (leftWord e (splitLeft w)) *
        PathLayer.rowAlt p (leftWord e (splitRight w) ∘ Fin.rev)) *
      (PathLayer.rowAlt r (rightWord e (splitLeft w)) *
        PathLayer.rowAlt r (rightWord e (splitRight w) ∘ Fin.rev)) := by ring
    _ = _ := by rw [hp, hr, ← hq, pow_add]; ring

theorem two_paths (q : ℕ)
    (a b : Tableau (2*q+2) (ShortColumns.shape q 2).transpose)
    (μ : YoungDiagram) (t : Tableau (2*q+2) μ) (hμ : μ.colLen 0 ≤ 4)
    (ho : ∃ j, μ.colLen j % 2 = 1) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a b (inOutputs (Set.Icc q (2*q+3)))
        (inOutputs_invariant (Set.Icc q (2*q+3)))).toRepresentation,
      Function.Injective F := by
  have hn : μ.card = 2*q+2 := by
    have h := Fintype.card_congr t
    simpa only [Fintype.card_fin, Fintype.card_coe] using h.symm
  obtain ⟨p,rs,hpq,hp,hrs,hr,hc⟩ := Columns.odd_column_split q μ hn hμ ho
  let r := q-p
  have hrq : p+r=q := by omega
  have heq : 2*q+2 = (2*p+1)+(2*r+1) := by omega
  let e : Fin (2*q+2) ≃ Fin (2*p+1) ⊕ Fin (2*r+1) :=
    (finCongr heq).trans finSumFinEquiv.symm
  let s := transposeTableau (twoPathLeft p r q hrq e)
  let u := transposeTableau (twoPathRight p r q hrq e)
  let D := pairWordMap (n := 2*q+2)
    (letterLift (twoPathLetter q)) (letterLift (twoPathLetter q))
  let v := wordTensor _ _ _
    (polytabloid (transposeTableau s) ⊗ₜ[ℂ] polytabloid (transposeTableau u))
  have hs : ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*q+2) 4) (D v)).toRepresentation, f ≠ 0 := by
    dsimp only [D, v, s, u]
    rw [twoPath_pair_word, cyclic_smul_eq _ _ _ (pow_ne_zero q (by norm_num))]
    exact Columns.two_path_cyclic_support_placed p r rs hp hrs hr μ hc t e
  obtain ⟨f,hf⟩ := hs
  obtain ⟨g,hg⟩ := cyclic_projection_support D v f hf
  exact projectedTensor_support_of_coordinate a s b u t _ _
    (twoPath_outputs p r q hrq e) g hg

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_FinitePieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Pieri. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.Balance
open FlagColumns Columns

lemma short_pair_support_oai {n : ℕ} (q δ : ℕ) (hn : n = 2*q+δ)
    (hδ : δ = 1 ∨ δ = 2)
    (a : Tableau n (ShortColumns.shape q δ).transpose)
    (μ : YoungDiagram) (t : Tableau n μ) (hμ : μ.colLen 0 ≤ 4)
    (ho : δ = 2 → ∃ j, μ.colLen j % 2 = 1) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a a (inOutputs (Set.Icc q (pairUpper q δ)))
        (inOutputs_invariant (Set.Icc q (pairUpper q δ)))).toRepresentation, F ≠ 0 := by
  subst n
  have hh : ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a a (inOutputs (Set.Icc q (pairUpper q δ)))
        (inOutputs_invariant (Set.Icc q (pairUpper q δ)))).toRepresentation,
      Function.Injective F := by
    rcases hδ with rfl | rfl
    · exact neighboring q a a μ t hμ
    · exact two_paths q a a μ t hμ (ho rfl)
  obtain ⟨F,hF⟩ := hh
  refine ⟨F,?_⟩
  intro hz
  exact polytabloid_ne_zero t (congrArg Subtype.val
    (hF (show F ⟨polytabloid t,mem_cyclic _ _⟩ = F 0 by rw [hz]; rfl)))

end Saxl.Balance

end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.Balance.short_pair_support_oai := @OAI.Saxl.Balance.short_pair_support_oai
