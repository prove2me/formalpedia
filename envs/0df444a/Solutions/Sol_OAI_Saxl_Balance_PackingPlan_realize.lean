-- Prove2me | solution 1 for OAI.Saxl.Balance.PackingPlan.realize
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T23:07:09.744879+00:00
-- url     : https://prove2.me/submissions/e656cd19-ac9c-4cc7-9188-34f5caff0273

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_Balance_WordPacking_neighbor
import Theorems.Thm_OAI_Saxl_Balance_WordPacking_threeRows
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
-- module Solutions.OAIQ259_US.Saxl_BandPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Path


lemma fourRow_column_lengths (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 4) :
    ∀ r ∈ μ.transpose.rowLens, 1 ≤ r ∧ r ≤ 4 := by
  intro r hr
  refine ⟨μ.transpose.pos_of_mem_rowLens r hr, ?_⟩
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hr
  rw [← he, YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose]
  exact (μ.colLen_anti 0 j (Nat.zero_le _)).trans hμ

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
-- module Solutions.OAIQ259_US.Saxl_PieriRestriction
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/

lemma wordRestrict_single {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (c : Fin n → Fin e) (b : Fin a → Fin d) :
    wordRestrict i j (Pi.single c 1) b = if c ∘ i = j ∘ b then 1 else 0 := by
  classical
  change (∑ z : Fin n → Fin e, if z ∘ i = j ∘ b then (Pi.single c (1 : ℂ) : WordSpace n e) z else 0) = _
  rw [Finset.sum_eq_single c]
  · simp
  · intro z hz hzc
    simp [hzc]
  · simp

lemma wordRestrict_equivariant {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)) (hi : ∀ k, g (i k) = i (h k))
    (x : WordSpace n e) :
    wordRestrict i j (wordRep n e g x) = wordRep a d h (wordRestrict i j x) := by
  classical
  ext b
  change (∑ c : Fin n → Fin e, if c ∘ i = j ∘ b then x (c ∘ g) else 0) =
    ∑ c : Fin n → Fin e, if c ∘ i = j ∘ (b ∘ h) then x c else 0
  apply Eq.trans ?_ (Equiv.sum_comp (wordPerm n e g)
    (fun c => if c ∘ i = j ∘ (b ∘ h) then x c else 0))
  apply Finset.sum_congr rfl
  intro c hc
  change (if c ∘ i = j ∘ b then x (c ∘ g) else 0) =
    if (c ∘ g) ∘ i = j ∘ (b ∘ h) then x (c ∘ g) else 0
  congr 1
  apply propext
  constructor
  · intro hh
    funext k
    simpa only [Function.comp_apply, hi] using congrFun hh (h k)
  · intro hh
    funext k
    have he := congrFun hh (h⁻¹ k)
    simpa [Function.comp_apply, hi] using he


lemma column_fixed_of_strip {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ)
    (g : columnGroup t) (hg : ∀ i, (g : Equiv.Perm (Fin n)) (tableauInclusion s t hs.1 i) =
      tableauInclusion s t hs.1 i) : g = 1 := by
  have hin (k : Fin n) (hk : (t k).val ∈ ν) : (g : Equiv.Perm (Fin n)) k = k := by
    let i := s.symm ⟨(t k).val, hk⟩
    have he : tableauInclusion s t hs.1 i = k := by
      apply t.injective
      apply Subtype.ext
      rw [tableauInclusion_cell]
      simp [i]
    simpa only [he] using hg i
  apply Subtype.ext
  apply Equiv.ext
  intro k
  by_cases hk : (t k).val ∈ ν
  · exact hin k hk
  · have ho : (t ((g : Equiv.Perm (Fin n)) k)).val ∉ ν := by
      intro hh
      have he := hin ((g : Equiv.Perm (Fin n)) k) hh
      have he' := (g : Equiv.Perm (Fin n)).injective he
      exact hk (he' ▸ hh)
    apply t.injective
    apply Subtype.ext
    exact hs.2 _ (t _).property ho _ (t _).property hk (g.property k)

lemma strip_contraction_coefficient {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t) (rowWord s) = 1 := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  have he (g : columnGroup t) :
      (rowWord t ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) ∘ i = j ∘ rowWord s ↔ g = 1 := by
    constructor
    · intro hh
      have hf : ∀ k, ((g : Equiv.Perm (Fin n))⁻¹) (i k) = i k := by
        intro k
        apply t.injective
        apply Subtype.ext
        apply Prod.ext
        · have hh' := congrArg Fin.val (congrFun hh k)
          simpa [rowWord, j, rowLetterInclusion, i] using hh'
        · exact (g⁻¹).property (i k)
      have hh' : (g⁻¹ : columnGroup t) = 1 := column_fixed_of_strip s t hs (g⁻¹) hf
      simpa using congrArg Inv.inv hh'
    · rintro rfl
      funext k
      apply Fin.ext
      exact congrArg Prod.fst (tableauInclusion_cell s t hs.1 k)
  let := Fintype.ofFinite (columnGroup t)
  change wordRestrict i j (∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0)
      (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1)) (rowWord s) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    wordRep_single, wordRestrict_single, he]
  simp

lemma column_viaEmbedding {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (g : columnGroup s) :
    (g : Equiv.Perm (Fin a)).viaEmbedding (tableauInclusion s t h) ∈ columnGroup t := by
  intro k
  by_cases hk : k ∈ Set.range (tableauInclusion s t h)
  · obtain ⟨l, rfl⟩ := hk
    rw [Equiv.Perm.viaEmbedding_apply]
    simpa only [tableauInclusion_cell] using g.property l
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk]

lemma signC_viaEmbedding {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin a)) :
    signC (g.viaEmbedding i) = signC g := by
  classical
  simp [signC_def, Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]

lemma strip_contraction_pair {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    dotProduct (wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t)) (polytabloid s) ≠ 0 := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  let x := wordRestrict i j (polytabloid t)
  have hx (g : columnGroup s) : wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a)) x =
      signC (g : Equiv.Perm (Fin a)) • x := by
    rw [← wordRestrict_equivariant i j ((g : Equiv.Perm (Fin a)).viaEmbedding i)
      (g : Equiv.Perm (Fin a)) (Equiv.Perm.viaEmbedding_apply _ _) (polytabloid t)]
    rw [polytabloid_alternating t ⟨_, column_viaEmbedding s t hs.1 g⟩]
    rw [map_smul, signC_viaEmbedding]
  rw [← columnAlt_coefficient]
  let := Fintype.ofFinite (columnGroup s)
  have he : columnAlt s x = (Fintype.card (columnGroup s) : ℂ) • x := by
    change (∑ g : columnGroup s, signC (g : Equiv.Perm (Fin a)) •
      wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a))) x = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul,
      signC_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  change columnAlt s x (rowWord s) ≠ 0
  rw [he]
  change (Fintype.card (columnGroup s) : ℂ) *
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1) (polytabloid t) (rowWord s) ≠ 0
  rw [strip_contraction_coefficient s t hs, mul_one]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/- Positive horizontal-strip Pieri map, equivariant for the full Young subgroup. -/
theorem pieri_strip_restriction {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, F ≠ 0 ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  let pr := subrepProject (spechtSub s) (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
  let T := wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
  let F := pr.toLinearMap.comp (T.comp (spechtSub t).toSubmodule.subtype)
  refine ⟨F, ?_, ?_⟩
  · intro hF
    have hp := subrepProject_pair (spechtSub s)
      (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
      (T (polytabloid t)) ⟨polytabloid s, mem_cyclic _ _⟩
    have he : pr (T (polytabloid t)) = 0 := by
      exact congrArg (fun L : Specht t →ₗ[ℂ] Specht s => L ⟨polytabloid t, mem_cyclic _ _⟩) hF
    rw [he] at hp
    exact strip_contraction_pair s t hs (hp.symm.trans (zero_dotProduct _))
  · intro g h hh x
    change pr (T (wordRep n (μ.colLen 0) g x.val)) = spechtRep s h (pr (T x.val))
    rw [wordRestrict_equivariant _ _ g h hh x.val]
    exact LinearMap.congr_fun (pr.isIntertwining' h) (T x.val)

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

lemma pieri_strip_surjective {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, Function.Surjective F ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  obtain ⟨F,hF,he⟩ := pieri_strip_restriction s t hs
  let E : Representation.IntertwiningMap
      ((spechtRep t).comp (Equiv.Perm.viaEmbeddingHom (tableauInclusion s t hs.1)))
      (spechtRep s) :=
    { toLinearMap := F
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro x
        exact he _ h (fun k => Equiv.Perm.viaEmbedding_apply _ _ k) x }
  have hE : E ≠ 0 := by
    intro hz
    exact hF (congrArg Representation.IntertwiningMap.toLinearMap hz)
  have := specht_irreducible s
  exact ⟨F, (Representation.IsIrreducible.surjective_or_eq_zero E).resolve_right hE, he⟩

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
    obtain ⟨F,hF,hFe⟩ := pieri_strip_surjective s t
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
    obtain ⟨P,hP,hPe⟩ := pieri_strip_surjective (shapeTableau η) t hh
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
-- module Solutions.OAIQ259_US.Saxl_Main
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

end Saxl

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
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SymmetricPairs
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma symmetricPairs_real {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    star (symmetricPairs e d) = symmetricPairs e d := by
  ext w
  simp only [Pi.star_apply, symmetricPairs]
  split_ifs <;> simp

lemma symmetricPairs_contraction {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (x y : WordSpace m d) :
    dotProduct (positionProduct e x y) (symmetricPairs e d) = dotProduct x y := by
  classical
  unfold dotProduct
  calc
    _ = ∑ p : (Fin m → Fin d) × (Fin m → Fin d),
        x p.1 * y p.2 * (if p.1 = p.2 then 1 else 0) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro w
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp

lemma real_self_pair_ne_zero {n d : ℕ} (x : WordSpace n d)
    (hr : star x = x) (hx : x ≠ 0) : dotProduct x x ≠ 0 := by
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  intro he
  apply hx
  exact dotProduct_self_star_eq_zero.mp (by simpa only [hr] using he)

lemma pairedTableau_left {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) (i : Fin m) :
    (pairedTableau μ he e s (e.symm (Sum.inl i))).val =
      ((s i).val.1, 2*(s i).val.2) := by
  simp [pairedTableau, pairedCells]

lemma pairedTableau_right {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) (i : Fin m) :
    (pairedTableau μ he e s (e.symm (Sum.inr i))).val =
      ((s i).val.1, 2*(s i).val.2+1) := by
  simp [pairedTableau, pairedCells]

lemma pairedTableau_group_sector {n m : ℕ} (μ : YoungDiagram)
    (he : ∀ i, Even (μ.rowLen i)) (e : Fin n ≃ Fin m ⊕ Fin m)
    (s : Tableau m (halfRows μ)) :
    columnGroup (pairedTableau μ he e s) ≤ sectorGroup (fun i => (e i).isLeft = true) := by
  intro g hg i
  have hc := hg i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  obtain ⟨k,hk⟩ := e.symm.surjective (g (e.symm j))
  rw [← hk] at hc ⊢
  cases j <;> cases k <;>
    simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, Sum.isLeft_inr] at *
  · rw [pairedTableau_left, pairedTableau_right] at hc
    dsimp only at hc
    omega
  · rw [pairedTableau_left, pairedTableau_right] at hc
    dsimp only at hc
    omega

lemma pairedTableau_factor {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) :
    polytabloid (pairedTableau μ he e s) = positionProduct e
      (letterLift (Fin.cast (halfRows_height μ he)) (polytabloid s))
      (letterLift (Fin.cast (halfRows_height μ he)) (polytabloid s)) := by
  let t := pairedTableau μ he e s
  let f : Fin n → ℕ := fun i => (t i).val.2
  have hn : columnGroup t = fiberGroup f := rfl
  have hg : columnGroup t = fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true) := by
    rw [← hn]
    exact (inf_eq_left.mpr (pairedTableau_group_sector μ he e s)).symm
  have hl : fiberGroup (fun i => f (e.symm (Sum.inl i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (t (e.symm (Sum.inl (g i)))).val.2 =
      (t (e.symm (Sum.inl i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [t, pairedTableau_left, Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hr : fiberGroup (fun i => f (e.symm (Sum.inr i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (t (e.symm (Sum.inr (g i)))).val.2 =
      (t (e.symm (Sum.inr i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [t, pairedTableau_right, Nat.add_right_cancel_iff,
      Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hw₁ : leftWord e (rowWord t) = Fin.cast (halfRows_height μ he) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (t (e.symm (Sum.inl i))).val.1 = (s i).val.1
    rw [pairedTableau_left]
  have hw₂ : rightWord e (rowWord t) = Fin.cast (halfRows_height μ he) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (t (e.symm (Sum.inr i))).val.1 = (s i).val.1
    rw [pairedTableau_right]
  change polytabloid t = _
  rw [polytabloid_eq_altWord, hg, altWord_fiber_split, hl, hr, hw₁, hw₂,
    ← letterLift_altWord, ← polytabloid_eq_altWord]

lemma letterLift_real {n a b : ℕ} (φ : Fin a → Fin b) (x : WordSpace n a)
    (hr : star x = x) : star (letterLift φ x) = letterLift φ x := by
  classical
  funext w
  change star (∑ c, x c * ∏ i, if φ (c i) = w i then (1 : ℂ) else 0) = _
  simp only [star_sum, star_mul, star_prod, apply_ite, star_one, star_zero]
  have hx (c) : star (x c) = x c := congrFun hr c
  simp_rw [hx]
  simp only [letterLift, wordMap, mul_comm]
  rfl

lemma letterLift_pair {n a b : ℕ} (φ : Fin a → Fin b)
    (x : WordSpace n a) (y : WordSpace n b) :
    dotProduct (letterLift φ x) y = dotProduct x (fun w => y (φ ∘ w)) := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_smul, letterLift_single]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext w
  simp [Pi.single_apply]

lemma letterLift_symmetricPairs_pair {n m a b : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (φ : Fin a → Fin b)
    (hφ : Function.Injective φ) (x : WordSpace n a) :
    dotProduct (letterLift φ x) (symmetricPairs e b) =
      dotProduct x (symmetricPairs e a) := by
  rw [letterLift_pair]
  congr 1
  funext w
  have hh : leftWord e (φ ∘ w) = rightWord e (φ ∘ w) ↔
      leftWord e w = rightWord e w := by
    constructor
    · intro h
      funext i
      exact hφ (congrFun h i)
    · intro h
      funext i
      exact congrArg φ (congrFun h i)
  simp only [symmetricPairs, hh]

lemma pairedTableau_contraction {n m : ℕ} (μ : YoungDiagram)
    (he : ∀ i, Even (μ.rowLen i)) (e : Fin n ≃ Fin m ⊕ Fin m)
    (s : Tableau m (halfRows μ)) :
    dotProduct (polytabloid (pairedTableau μ he e s))
      (symmetricPairs e (μ.colLen 0)) ≠ 0 := by
  rw [pairedTableau_factor, symmetricPairs_contraction]
  apply real_self_pair_ne_zero
  · exact letterLift_real _ _ (polytabloid_real s)
  · intro hz
    apply polytabloid_ne_zero s
    exact letterLift_injective _ (Fin.cast_injective _) (hz.trans (map_zero _).symm)

lemma halfRows_card (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    2 * (halfRows μ).card = μ.card := by
  have hc := Fintype.card_congr (pairedCells μ he)
  simpa only [Fintype.card_sum, Fintype.card_coe, ← two_mul] using hc

theorem even_rows_symmetricPairs_support {n m d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (symmetricPairs e d)).toRepresentation, F ≠ 0 := by
  have hn : μ.card = n := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have hnm : n = 2*m := by
    simpa only [Fintype.card_fin, Fintype.card_sum, ← two_mul] using Fintype.card_congr e
  have hm : (halfRows μ).card = m := by
    have hc := halfRows_card μ he
    omega
  let s := canonicalTableau (halfRows μ) hm
  let es : Fin n ≃ Fin m ⊕ Fin m := t.trans ((pairedCells μ he).symm.trans
    (Equiv.sumCongr s.symm s.symm))
  have ht : pairedTableau μ he es s = t := by
    apply Equiv.ext
    intro i
    change pairedCells μ he ((Equiv.sumCongr s s)
      ((Equiv.sumCongr s s).symm ((pairedCells μ he).symm (t i)))) = t i
    simp only [Equiv.apply_symm_apply]
  let φ : Fin (μ.colLen 0) → Fin d := Fin.castLE hd
  have hh : dotProduct (letterLift φ (polytabloid t)) (symmetricPairs es d) ≠ 0 := by
    rw [letterLift_symmetricPairs_pair _ φ (Fin.castLE_injective hd), ← ht]
    exact pairedTableau_contraction μ he es s
  have hsupp := hom_to_cyclic_of_pair
    (fun a b => if φ a = b then 1 else 0) (spechtSub t)
    ⟨polytabloid t, mem_cyclic _ _⟩ (symmetricPairs es d) (symmetricPairs_real es) hh
  let g : Equiv.Perm (Fin n) := e.trans es.symm
  have hg : wordRep n d g (symmetricPairs e d) = symmetricPairs es d := by
    funext w
    have hl : leftWord e (w ∘ g) = leftWord es w := by
      funext i
      simp [leftWord, g]
    have hr : rightWord e (w ∘ g) = rightWord es w := by
      funext i
      simp [rightWord, g]
    change (if leftWord e (w ∘ g) = rightWord e (w ∘ g) then 1 else 0) = _
    simp only [hl, hr, symmetricPairs]
  have hc : cyclic (wordRep n d) (symmetricPairs es d) =
      cyclic (wordRep n d) (symmetricPairs e d) := by
    rw [← hg, cyclic_action_eq]
  change ∃ f : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (symmetricPairs es d)).toRepresentation, f ≠ 0 at hsupp
  rw [hc] at hsupp
  exact hsupp

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_PairForms
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Forms. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma pairFormTensor_one {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    pairFormTensor e (1 : Matrix (Fin d) (Fin d) ℂ) = symmetricPairs e d := by
  classical
  funext w
  change (∏ i, if leftWord e w i = rightWord e w i then (1 : ℂ) else 0) = _
  by_cases hw : leftWord e w = rightWord e w
  · simp [hw, symmetricPairs]
  · have hi : ∃ i, leftWord e w i ≠ rightWord e w i := by
      exact not_forall.mp (fun he => hw (funext he))
    obtain ⟨i, hi⟩ := hi
    rw [symmetricPairs, ite_eq_right hw]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma pairFormTensor_smul {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (c : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    pairFormTensor e (c • B) = c^m • pairFormTensor e B := by
  funext w
  simp [pairFormTensor, Finset.prod_mul_distrib]

lemma wordMap_pairFormTensor {n m a b : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (L : Fin a → Fin b → ℂ) (B : Matrix (Fin a) (Fin a) ℂ) :
    wordMap L (pairFormTensor e B) = pairFormTensor e
      (fun j k => ∑ p : Fin a × Fin a, B p.1 p.2 * L p.1 j * L p.2 k) := by
  classical
  funext w
  change (∑ c, pairFormTensor e B c * ∏ i, L (c i) (w i)) = _
  calc
    _ = ∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i) := by
      apply Fintype.sum_equiv (pairWordsEquiv e)
      intro c
      simp only [pairWordsEquiv_apply, pairFormTensor, Finset.prod_mul_distrib]
      have he : (∏ i, L (c i) (w i)) =
          (∏ i, L (leftWord e c i) (leftWord e w i)) *
            ∏ i, L (rightWord e c i) (rightWord e w i) := by
        calc
          _ = ∏ x : Fin m ⊕ Fin m, L (c (e.symm x)) (w (e.symm x)) :=
            (Equiv.prod_comp e.symm (fun i => L (c i) (w i))).symm
          _ = _ := by
            rw [Fintype.prod_sum_type]
            rfl
      rw [he, mul_assoc]
    _ = _ := by
      change (∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i)) =
        ∏ i, ∑ p : Fin a × Fin a,
          B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i)
      exact (Fintype.prod_sum (fun (i : Fin m) (p : Fin a × Fin a) =>
        B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i))).symm

theorem even_rows_pairFormTensor_support {n m a d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (B : Matrix (Fin a) (Fin a) ℂ)
    (L : Fin a → Fin d → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hL : (fun j k => ∑ p : Fin a × Fin a, B p.1 p.2 * L p.1 j * L p.2 k) =
      c • (1 : Matrix (Fin d) (Fin d) ℂ))
    (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n a) (pairFormTensor e B)).toRepresentation, F ≠ 0 := by
  have hmap : wordMap L (pairFormTensor e B) = c^m • symmetricPairs e d := by
    rw [wordMap_pairFormTensor, hL, pairFormTensor_smul, pairFormTensor_one]
  have hs := even_rows_symmetricPairs_support e μ t he hd
  have hcyc : cyclic (wordRep n d) (wordMap L (pairFormTensor e B)) =
      cyclic (wordRep n d) (symmetricPairs e d) := by
    rw [hmap, cyclic_smul_eq _ _ _ (pow_ne_zero m hc)]
  rw [← hcyc] at hs
  obtain ⟨F,hF⟩ := hs
  exact cyclic_projection_support (wordMap L) (pairFormTensor e B) F hF

lemma outputTwoCongruence_gram :
    (fun j k => ∑ p : Fin 2 × Fin 2,
      outputTwoForm p.1 p.2 * outputTwoCongruence p.1 j * outputTwoCongruence p.2 k) =
      (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    (first | (simp [Fintype.sum_prod_type, Fin.sum_univ_succ, outputTwoForm, outputTwoCongruence, Matrix.one_apply]; all_goals first | (norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, outputTwoForm, outputTwoCongruence, Matrix.one_apply]; done) | rfl | decide) | (norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, outputTwoForm, outputTwoCongruence, Matrix.one_apply]; done) | norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, outputTwoForm, outputTwoCongruence, Matrix.one_apply])

theorem even_rows_outputTwo_support {n m : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 2) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 2) (pairFormTensor e outputTwoForm)).toRepresentation, F ≠ 0 :=
  even_rows_pairFormTensor_support e outputTwoForm outputTwoCongruence 2 (by norm_num)
    outputTwoCongruence_gram μ t he hd

end Saxl
end
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

lemma oddTableau_row (b : ℕ) (i : Fin (2*b+1)) :
    ((oddTableau b) i).val.1 = (PathLayer.base i).val := by
  simp only [oddTableau, Equiv.coe_fn_mk, PathLayer.base]
  split_ifs <;> rfl

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
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Neighboring
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

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SupportTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support Transport. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

namespace SupportLE
variable {G H X Y Z : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    [AddCommMonoid Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}

lemma refl (ρ : Representation ℂ G X) : SupportLE ρ ρ := by
  intro x hx
  exact ⟨Representation.IntertwiningMap.id ρ, hx⟩

end SupportLE

end Saxl

namespace Saxl

theorem word_supportLE {n d : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0) :
    SupportLE (wordRep n d) σ := word_support_separates σ h

theorem word_coind_supportLE {n d : ℕ} {H V : Type*} [Group H]
    [AddCommGroup V] [Module ℂ V] (φ : H →* Equiv.Perm (Fin n))
    (σ : Representation ℂ H V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap ((spechtRep t).comp φ) σ, f ≠ 0) :
    SupportLE (wordRep n d) (Representation.coind φ σ) := by
  apply word_supportLE
  intro μ t ht
  obtain ⟨f,hf⟩ := h μ t ht
  exact ⟨coindLift φ f,coindLift_ne_zero φ f hf⟩

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalancedPairs
attribute [-simp] _root_.OAI.Saxl.Balance.appendShortCells_left _root_.OAI.Saxl.Balance.appendShortCells_right _root_.OAI.Saxl.orbitTensorEval_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balanced Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

lemma pairAtOutputTwo_output (m : ℕ) (hm : 1 ≤ m) (i : Fin 2) :
    output (pairAtOutputTwo m hm i) = 2 := by
  simp only [output, pairAtOutputTwo, Equiv.symm_apply_apply, Fin.val_castLE, Fin.val_rev]
  have hi := i.isLt
  omega

lemma evenTableau_eval (m : ℕ) (w : Fin (2*m) → Fin ((ShortColumns.shape m 0).colLen 0)) :
    polytabloid (ShortColumns.evenTableau m) w =
      ShortColumns.evenAlt m (Fin.castLE (ShortColumns.height_le m 0) ∘ w) := by
  have he := congrFun (ShortColumns.evenTableau_polytabloid m)
    (Fin.castLE (ShortColumns.height_le m 0) ∘ w)
  rw [letterLift_eval _ (Fin.castLE_injective _) _ w] at he
  exact he

lemma outputTwo_pair_entry (i j : Fin 2) :
    PathLayer.J i j * PathLayer.J (Fin.rev i) (Fin.rev j) =
      (-1 : ℂ) * outputTwoForm i j := by
  fin_cases i <;> fin_cases j <;> (first | (simp [PathLayer.J, outputTwoForm, Fin.rev]; all_goals first | (norm_num [PathLayer.J, outputTwoForm, Fin.rev]; done) | rfl | decide) | (norm_num [PathLayer.J, outputTwoForm, Fin.rev]; done) | norm_num [PathLayer.J, outputTwoForm, Fin.rev])

lemma outputTwo_squared_polytabloid (m : ℕ) (hm : 1 ≤ m)
    (w : Fin (2*m) → Fin 2) :
    wordTensor (2*m) _ _ (polytabloid (ShortColumns.evenTableau m) ⊗ₜ[ℂ]
      polytabloid (ShortColumns.evenTableau m)) (pairAtOutputTwo m hm ∘ w) =
      ((-1 : ℂ)^m • pairFormTensor (ShortColumns.pairSplit m) outputTwoForm) w := by
  rw [wordTensor_tmul, evenTableau_eval, evenTableau_eval]
  have hl : Fin.castLE (ShortColumns.height_le m 0) ∘
      splitLeft (pairAtOutputTwo m hm ∘ w) = w := by
    funext i
    apply Fin.ext
    simp [splitLeft, pairAtOutputTwo]
  have hr : Fin.castLE (ShortColumns.height_le m 0) ∘
      splitRight (pairAtOutputTwo m hm ∘ w) = Fin.rev ∘ w := by
    funext i
    apply Fin.ext
    simp [splitRight, pairAtOutputTwo]
  rw [hl,hr, ShortColumns.evenAlt_formula, ShortColumns.evenAlt_formula,
    ← Finset.prod_mul_distrib]
  simp only [Function.comp_apply, outputTwo_pair_entry, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

theorem repeated_twos (m : ℕ) (hm : 1 ≤ m)
    (a b : Tableau (2*m) (ShortColumns.shape m 0))
    (μ : YoungDiagram) (t : Tableau (2*m) μ)
    (he : ∀ i, Even (μ.rowLen i)) (hμ : μ.colLen 0 ≤ 2) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a b (inOutputs ({2} : Set ℕ))
        (inOutputs_invariant ({2} : Set ℕ))).toRepresentation, Function.Injective F := by
  classical
  let P := inOutputs (n := 2*m) (d := (ShortColumns.shape m 0).colLen 0)
    (e := (ShortColumns.shape m 0).colLen 0) ({2} : Set ℕ)
  let hP := inOutputs_invariant (n := 2*m) (d := (ShortColumns.shape m 0).colLen 0)
    (e := (ShortColumns.shape m 0).colLen 0) ({2} : Set ℕ)
  let W := projectedSpechtTensor a b P hP
  have hma : polytabloid (ShortColumns.evenTableau m) ∈ spechtSub a := by
    rw [← spechtSub_tableau_independent (ShortColumns.evenTableau m) a]
    exact mem_cyclic _ _
  have hmb : polytabloid (ShortColumns.evenTableau m) ∈ spechtSub b := by
    rw [← spechtSub_tableau_independent (ShortColumns.evenTableau m) b]
    exact mem_cyclic _ _
  let z : W.toSubmodule := projectedTensorQuotient a b P hP
    (⟨polytabloid (ShortColumns.evenTableau m),hma⟩ ⊗ₜ[ℂ]
      ⟨polytabloid (ShortColumns.evenTableau m),hmb⟩)
  let D : Representation.IntertwiningMap W.toRepresentation (wordRep (2*m) 2) :=
    (restrictLetters (pairAtOutputTwo m hm)).comp (subrepInclusion W)
  have hz : D z = (-1 : ℂ)^m • pairFormTensor (ShortColumns.pairSplit m) outputTwoForm := by
    funext w
    change coordinateProjection P (spechtTensorMap a b
      (⟨polytabloid (ShortColumns.evenTableau m),hma⟩ ⊗ₜ[ℂ]
        ⟨polytabloid (ShortColumns.evenTableau m),hmb⟩))
          (pairAtOutputTwo m hm ∘ w) = _
    rw [spechtTensorMap, coordinateProjection_apply, ite_eq_left]
    · exact outputTwo_squared_polytabloid m hm w
    · intro i
      exact pairAtOutputTwo_output m hm (w i)
  have hs := even_rows_outputTwo_support (ShortColumns.pairSplit m) μ t he hμ
  have hc : cyclic (wordRep (2*m) 2) (D z) =
      cyclic (wordRep (2*m) 2) (pairFormTensor (ShortColumns.pairSplit m) outputTwoForm) := by
    rw [hz, cyclic_smul_eq _ _ _ (pow_ne_zero m (by norm_num))]
  rw [← hc] at hs
  obtain ⟨f,hf⟩ := hs
  obtain ⟨g,hg⟩ := cyclic_projection_support D z f hf
  let F := (subrepInclusion (cyclic W.toRepresentation z)).comp g
  have hF : F ≠ 0 := by
    intro hz
    apply hg
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun H => H x) hz
  let := specht_irreducible t
  exact ⟨F, (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPackingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing Geometry. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

theorem WordPacking.of_bounded_shape {rs ps : List ℕ} {μ : YoungDiagram} {d E : ℕ}
    (hp : rs.Perm μ.transpose.rowLens) (hd : μ.colLen 0 ≤ d)
    (hsum : ps.sum = rs.sum) (hlen : ps.length ≤ E)
    (k : ℕ) (I : Set ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : ∀ t : Tableau rs.sum μ, SupportLE (wordRep rs.sum E)
      (projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)).toRepresentation) :
    Nonempty (WordPacking rs ps d A label {k}) := by
  obtain ⟨e,hr,hc⟩ := place_columns μ hp
  exact ⟨WordPacking.bounded e hr hc hd hsum hlen k I A label he (hs _)⟩

lemma repeated_column_length {m k n : ℕ} (hk : 0 < k)
    (t : Tableau n (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose)
    (i : Fin n) : (columnLengthWord t i).val+1 = k := by
  have hm := YoungDiagram.mem_transpose.mp (t i).property
  obtain ⟨hj,hi⟩ := YoungDiagram.mem_ofRowLens.mp hm
  have he := YoungDiagram.rowLen_ofRowLens (hw := replicate_sorted m k)
    (show Fin (List.replicate m k).length from ⟨(t i).val.2,hj⟩)
  simp only [Fin.getElem_fin, List.getElem_replicate] at he
  change (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose.colLen
    (t i).val.2 - 1 + 1 = k
  rw [YoungDiagram.colLen_transpose,he]
  omega

theorem WordPacking.repeated {m k d : ℕ} (hm : 0 < m) (hk : 0 < k) (hd : k ≤ d)
    (j : ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = j) ↔ output a = k) :
    Nonempty (WordPacking (List.replicate m k) [m*k] d A label {j}) := by
  let μ := (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose
  have hrow : μ.transpose.rowLens = List.replicate m k := by
    rw [YoungDiagram.transpose_transpose]
    apply YoungDiagram.rowLens_ofRowLens_eq_self
    intro x hx
    rw [(List.mem_replicate.mp hx).2]
    exact hk
  have hD : μ.colLen 0 ≤ d := by
    rw [YoungDiagram.colLen_transpose]
    have hh := YoungDiagram.rowLen_ofRowLens (hw := replicate_sorted m k)
      (show Fin (List.replicate m k).length from ⟨0,by simpa⟩)
    simp only [Fin.getElem_fin, List.getElem_replicate] at hh
    rw [hh]
    exact hd
  apply WordPacking.of_bounded_shape (μ := μ) (E := 1) (by rw [hrow]) hD
    (by simp) (by simp) j {k} A label he
  intro t
  exact constant_output_support t k (repeated_column_length hk t)

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPackingPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance
open FlagColumns Columns

theorem WordPacking.of_binary_shapes {rs ss ps : List ℕ} {μ ν : YoungDiagram} {d E : ℕ}
    (hp : rs.Perm μ.transpose.rowLens) (hp' : ss.Perm ν.transpose.rowLens)
    (hd : μ.colLen 0 ≤ d) (hd' : ν.colLen 0 ≤ d)
    (hsum : ps.sum = (rs++ss).sum) (hlen : ps.length ≤ E)
    (k l : ℕ) (hne : k ≠ l) (I J : Set ℕ)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (he' : ∀ a, (A a ∧ label a = l) ↔ output a ∈ J)
    (hs : ∀ (t : Tableau rs.sum μ) (u : Tableau ss.sum ν),
      SupportLE (wordRep (rs++ss).sum E)
        (Representation.coind (sumPermHom (appendPositions rs ss))
          (outer (projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)).toRepresentation
            (projectedSpechtTensor u u (inOutputs J) (inOutputs_invariant J)).toRepresentation))) :
    Nonempty (WordPacking (rs++ss) ps d A label {k,l}) := by
  obtain ⟨e,hr,hc⟩ := place_columns μ hp
  obtain ⟨f,hr',hc'⟩ := place_columns ν hp'
  exact ⟨WordPacking.binaryBounded e f hr hc hr' hc' hd hd' hsum hlen
    k l hne I J A label he he' (hs _ _)⟩

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OddStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Odd Strip. -/

section

noncomputable section

namespace Saxl.Balance

lemma horizontal_two_rows (ν μ : YoungDiagram)
    (hν : ν.colLen 0 ≤ 2) (hμ : μ.colLen 0 ≤ 2)
    (h0 : ν.rowLen 0 ≤ μ.rowLen 0) (h1 : ν.rowLen 1 ≤ μ.rowLen 1)
    (hm : μ.rowLen 1 ≤ ν.rowLen 0) : HorizontalStrip ν μ := by
  have row_lt (η : YoungDiagram) (hη : η.colLen 0 ≤ 2) (x : ℕ × ℕ)
      (hx : x ∈ η) : x.1 = 0 ∨ x.1 = 1 := by
    have hh := YoungDiagram.mem_iff_lt_colLen.mp
      (η.up_left_mem (le_refl x.1) (Nat.zero_le x.2) hx)
    omega
  constructor
  · intro x hx
    rw [YoungDiagram.mem_iff_lt_rowLen] at hx ⊢
    rcases row_lt ν hν x (YoungDiagram.mem_iff_lt_rowLen.mpr hx) with h | h
    · simpa only [h] using lt_of_lt_of_le (by simpa only [h] using hx) h0
    · simpa only [h] using lt_of_lt_of_le (by simpa only [h] using hx) h1
  · intro x hx hxn y hy hyn hxy
    apply Prod.ext _ hxy
    have hxr := row_lt μ hμ x hx
    have hyr := row_lt μ hμ y hy
    rw [YoungDiagram.mem_iff_lt_rowLen] at hx hy hxn hyn
    rcases hxr with hxr | hxr <;> rcases hyr with hyr | hyr
    · omega
    · simp only [hxr, hyr] at hx hy hxn hyn
      omega
    · simp only [hxr, hyr] at hx hy hxn hyn
      omega
    · omega

theorem odd_strip_precursor (c x : ℕ) (hc : Even c) (hx : Odd x)
    (hxc : x ≤ c) (μ : YoungDiagram) (hsize : μ.card = c+x)
    (hμ : μ.colLen 0 ≤ 2) :
    ∃ ν : YoungDiagram, ν.card = c ∧ ν.colLen 0 ≤ 2 ∧
      (∀ i, Even (ν.rowLen i)) ∧ HorizontalStrip ν μ := by
  let β := μ.rowLen 1
  let U := min β (c-β)
  let y := 2*(U/2)
  have hm := μ.rowLen_anti 0 1 (by omega)
  have hcard := card_of_height_two μ hμ
  have hcp := Nat.even_iff.mp hc
  have hxp := Nat.odd_iff.mp hx
  have hβ : β ≤ c := by dsimp only [β]; omega
  have huβ : U ≤ β := min_le_left _ _
  have huc : U ≤ c-β := min_le_right _ _
  have hyu : y ≤ U := by dsimp only [y]; omega
  have hyc : 2*y ≤ c := by omega
  have hyβ : β ≤ y+x := by
    dsimp only [β, U, y] at *
    omega
  have hyp : y % 2 = 0 := by dsimp only [y]; omega
  refine ⟨ShortColumns.shape y (c-2*y), ?_, ShortColumns.height_le _ _, ?_, ?_⟩
  · rw [short_card]
    omega
  · intro i
    rw [short_rowLen, Nat.even_iff]
    split_ifs <;> omega
  · apply horizontal_two_rows _ _ (ShortColumns.height_le _ _) hμ
    · simp only [short_rowLen, ite_true, if_true]
      dsimp only [β] at *
      omega
    · simpa only [short_rowLen, Nat.one_ne_zero, ite_false, if_false, ite_true, if_true] using
        hyu.trans huβ
    · simp only [short_rowLen, ite_true, if_true]
      dsimp only [β] at *
      omega

end Saxl.Balance
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

lemma four_interlacing_exists (a b c d : ℕ) (hab : b ≤ a) (hbc : c ≤ b)
    (hcd : d ≤ c) (ha : 3 ≤ a) :
    ∃ x y z w, FourInterlacing a b c d x y z w := by
  by_cases hd2 : 2 ≤ d
  · exact ⟨a,b,c,d-2,by unfold FourInterlacing; omega⟩
  by_cases hd1 : d = 1
  · by_cases hab' : b < a
    · exact ⟨a-1,b,c,d-1,by unfold FourInterlacing; omega⟩
    · by_cases hbc' : c < b
      · exact ⟨a,b-1,c,d-1,by unfold FourInterlacing; omega⟩
      · exact ⟨a,b,c-1,d-1,by unfold FourInterlacing; omega⟩
  have hd0 : d = 0 := by omega
  by_cases hc3 : 3 ≤ c
  · exact ⟨a,b,c-2,d,by unfold FourInterlacing; omega⟩
  by_cases hc2 : c = 2
  · by_cases hab' : b < a
    · exact ⟨a,b,c-2,d,by unfold FourInterlacing; omega⟩
    · exact ⟨a,b-1,c-1,d,by unfold FourInterlacing; omega⟩
  by_cases hc1 : c = 1
  · by_cases hb2 : 2 ≤ b
    · exact ⟨a,b-1,c-1,d,by unfold FourInterlacing; omega⟩
    · exact ⟨a-1,b,c-1,d,by unfold FourInterlacing; omega⟩
  by_cases hb2 : 2 ≤ b
  · exact ⟨a,b-2,c,d,by unfold FourInterlacing; omega⟩
  by_cases hb1 : b = 1
  · exact ⟨a-1,b-1,c,d,by unfold FourInterlacing; omega⟩
  · exact ⟨a-2,b,c,d,by unfold FourInterlacing; omega⟩

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

lemma sorted_four (x y z w : ℕ) (hxy : y ≤ x) (hyz : z ≤ y) (hzw : w ≤ z) :
    [x,y,z,w].SortedGE := by
  simp [List.sortedGE_iff_pairwise, List.pairwise_cons]
  omega

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

lemma card_of_height_four (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 4) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 + μ.rowLen 2 + μ.rowLen 3 := by
  rw [← rowPrefix_eq_card μ hμ]
  simp [rowPrefix, Finset.sum_range_succ, add_assoc]

lemma odd_column_of_row_gap (μ : YoungDiagram) (i : ℕ) (hi : Even i)
    (hgap : μ.rowLen (i+1) < μ.rowLen i) : ∃ j, Odd (μ.colLen j) := by
  let j := μ.rowLen (i+1)
  have h₁ : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp
    (YoungDiagram.mem_iff_lt_rowLen.mpr hgap)
  have h₂ : ¬ i+1 < μ.colLen j := by
    intro h
    have hh := YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr h)
    exact Nat.lt_irrefl j hh
  refine ⟨j, ?_⟩
  have hlen : μ.colLen j = i+1 := by omega
  rw [hlen, Nat.odd_iff]
  have := Nat.even_iff.mp hi
  omega

theorem horizontal_two_odd_precursor (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 4)
    (hw : 3 ≤ μ.rowLen 0) :
    ∃ ν : YoungDiagram, ν.card+2 = μ.card ∧ ν.colLen 0 ≤ 4 ∧
      (∃ j, Odd (ν.colLen j)) ∧ HorizontalStrip ν μ := by
  obtain ⟨x,y,z,w,hh⟩ := four_interlacing_exists
    (μ.rowLen 0) (μ.rowLen 1) (μ.rowLen 2) (μ.rowLen 3)
    (μ.rowLen_anti _ _ (by omega)) (μ.rowLen_anti _ _ (by omega))
    (μ.rowLen_anti _ _ (by omega)) hw
  have hs := sorted_four x y z w (hh.2.2.1.trans hh.2.1)
    (hh.2.2.2.2.1.trans hh.2.2.2.1) (hh.2.2.2.2.2.2.1.trans hh.2.2.2.2.2.1)
  let ν := YoungDiagram.ofRowLens [x,y,z,w] hs
  have hheight : ν.colLen 0 ≤ 4 := ofRowLens_height [x,y,z,w] hs
  have hrows (i : ℕ) : ν.rowLen i = [x,y,z,w][i]?.getD 0 := ofRowLens_rowLen _ _ _
  have h0 : ν.rowLen 0 = x := by simp [hrows]
  have h1 : ν.rowLen 1 = y := by simp [hrows]
  have h2 : ν.rowLen 2 = z := by simp [hrows]
  have h3 : ν.rowLen 3 = w := by simp [hrows]
  refine ⟨ν, ?_, hheight, ?_, ?_⟩
  · rw [card_of_height_four _ hheight, card_of_height_four μ hμ, h0, h1, h2, h3]
    exact hh.2.2.2.2.2.2.2.1
  · rcases hh.2.2.2.2.2.2.2.2 with h | h
    · exact odd_column_of_row_gap ν 0 (by decide) (by simpa only [h0,h1] using h)
    · exact odd_column_of_row_gap ν 2 (by decide) (by simpa only [h2,h3] using h)
  · apply horizontal_of_interlacing
    · intro i
      by_cases hi : i < 4
      · interval_cases i <;> simp only [h0,h1,h2,h3] <;> unfold FourInterlacing at hh <;> omega
      · rw [rowLen_zero_of_height_le _ (hheight.trans (by omega))]
        exact Nat.zero_le _
    · intro i
      by_cases hi : i < 3
      · interval_cases i <;> simp only [Nat.reduceAdd, h0,h1,h2] <;> unfold FourInterlacing at hh <;> omega
      · rw [rowLen_zero_of_height_le _ (hμ.trans (by omega))]
        exact Nat.zero_le _

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_PieriInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pieri Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem horizontal_placed_restriction {n a b : ℕ} {ν μ : YoungDiagram}
    (hs : HorizontalStrip ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, Function.Surjective F ∧
      ∀ (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : Specht t),
        F (spechtRep t (sumPerm e h q) x) = spechtRep s h (F x) := by
  obtain ⟨c,F,hF,he⟩ := placed_strip_restriction
    (SizedStripChain.of_horizontal hs) s t e
  exact ⟨F,hF,fun h q => he h q (by funext i; apply Fin.ext; change (c (q i)).val = (c i).val; have h₁ := (c (q i)).isLt; have h₂ := (c i).isLt; simp only [List.length_singleton] at h₁ h₂; omega)⟩

lemma tensorTrivial_injective {V : Type*} [AddCommGroup V] [Module ℂ V] (b : ℕ) :
    Function.Injective (tensorTrivial (V := V) b) := by
  intro x y h
  have he := congrArg (rightSlice (LinearMap.proj (fun _ : Fin b => (0 : Fin 1)))) h
  simpa only [tensorTrivial,LinearMap.flip_apply,TensorProduct.mk_apply,
    rightSlice_tmul,LinearMap.proj_apply,one_smul] using he

theorem horizontal_coind_map {n a b : ℕ} {ν μ : YoungDiagram}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (hs : HorizontalStrip ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (σ : Representation ℂ (Equiv.Perm (Fin a)) V)
    (K : Representation.IntertwiningMap (spechtRep s) σ) (hK : K ≠ 0) :
    ∃ F : Representation.IntertwiningMap ((spechtRep t).comp (sumPermHom e))
      (outer σ (wordRep b 1)), F ≠ 0 := by
  obtain ⟨F,hF,hFe⟩ := horizontal_placed_restriction hs s t e
  let L : Representation.IntertwiningMap ((spechtRep t).comp (sumPermHom e))
      (outer σ (wordRep b 1)) := {
    toLinearMap := (tensorTrivial b).comp (K.toLinearMap.comp F)
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      change K (F (spechtRep t (sumPerm e g.1 g.2) x)) ⊗ₜ[ℂ] (fun _ => 1) =
        (σ g.1 (K (F x))) ⊗ₜ[ℂ] wordRep b 1 g.2 (fun _ => 1)
      rw [hFe,K.isIntertwining]
      rfl }
  refine ⟨L,?_⟩
  intro hz
  apply hK
  ext x
  obtain ⟨y,rfl⟩ := hF x
  apply tensorTrivial_injective b
  have he := congrArg (fun Q : Representation.IntertwiningMap
    ((spechtRep t).comp (sumPermHom e)) (outer σ (wordRep b 1)) => Q y) hz
  change tensorTrivial b (K (F y)) = 0 at he
  change tensorTrivial b (K (F y)) = tensorTrivial b 0
  simpa only [map_zero] using he

namespace Balance

theorem even_twos_odd_coind (m x : ℕ) (hm : 1 ≤ m) (hx : Odd x)
    (hxc : x ≤ 2*m) (a : Tableau (2*m) (ShortColumns.shape m 0))
    (e : Fin (2*m+x) ≃ Fin (2*m) ⊕ Fin x) :
    SupportLE (wordRep (2*m+x) 2)
      (Representation.coind (sumPermHom e)
        (outer (projectedSpechtTensor a a (inOutputs {2})
          (inOutputs_invariant {2})).toRepresentation (wordRep x 1))) := by
  let W := projectedSpechtTensor a a (inOutputs {2}) (inOutputs_invariant {2})
  let : AddCommGroup (W.toSubmodule ⊗[ℂ] WordSpace x 1) :=
    Module.addCommMonoidToAddCommGroup ℂ
  apply word_coind_supportLE
  intro μ t hμ
  have hsize : μ.card = 2*m+x := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr t).symm
  obtain ⟨ν,hν,hheight,hev,hs⟩ := odd_strip_precursor (2*m) x
    (by exact even_two_mul m) hx hxc μ hsize hμ
  let s := canonicalTableau ν hν
  obtain ⟨K,hK⟩ := repeated_twos m hm a a ν s hev hheight
  have hn : K ≠ 0 := by
    intro hz
    have hp := hK (show K ⟨polytabloid s,mem_cyclic _ _⟩ = K 0 by rw [hz]; rfl)
    exact polytabloid_ne_zero s (congrArg Subtype.val hp)
  exact horizontal_coind_map hs s t e _ K hn

theorem two_paths_two_coind (q : ℕ) (hq : 3 ≤ q)
    (a : Tableau (2*q+2) (ShortColumns.shape q 2).transpose)
    (e : Fin (2*q+4) ≃ Fin (2*q+2) ⊕ Fin 2) :
    SupportLE (wordRep (2*q+4) 4)
      (Representation.coind (sumPermHom e)
        (outer (projectedSpechtTensor a a (inOutputs (Set.Icc q (2*q+3)))
          (inOutputs_invariant (Set.Icc q (2*q+3)))).toRepresentation (wordRep 2 1))) := by
  let W := projectedSpechtTensor a a (inOutputs (Set.Icc q (2*q+3)))
    (inOutputs_invariant (Set.Icc q (2*q+3)))
  let : AddCommGroup (W.toSubmodule ⊗[ℂ] WordSpace 2 1) :=
    Module.addCommMonoidToAddCommGroup ℂ
  apply word_coind_supportLE
  intro μ t hμ
  have hsize : μ.card = 2*q+4 := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr t).symm
  have hw : 3 ≤ μ.rowLen 0 := by
    have hc := card_of_height_four μ hμ
    have h1 := μ.rowLen_anti 0 1 (by omega)
    have h2 := μ.rowLen_anti 0 2 (by omega)
    have h3 := μ.rowLen_anti 0 3 (by omega)
    omega
  obtain ⟨ν,hcard,hheight,hodd,hs⟩ := horizontal_two_odd_precursor μ hμ hw
  have hν : ν.card = 2*q+2 := by omega
  let s := canonicalTableau ν hν
  obtain ⟨K,hK⟩ := two_paths q a a ν s hheight (by
    obtain ⟨j,hj⟩ := hodd
    exact ⟨j,Nat.odd_iff.mp hj⟩)
  have hn : K ≠ 0 := by
    intro hz
    have hp := hK (show K ⟨polytabloid s,mem_cyclic _ _⟩ = K 0 by rw [hz]; rfl)
    exact polytabloid_ne_zero s (congrArg Subtype.val hp)
  exact horizontal_coind_map hs s t e _ K hn

end Balance
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_WordPackingPieri
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word Packing Pieri. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance
open FlagColumns Columns

lemma short_transpose_height (r δ : ℕ) : (ShortColumns.shape r δ).transpose.colLen 0 = r+δ := by
  rw [YoungDiagram.colLen_transpose]
  exact YoungDiagram.rowLen_ofRowLens (hw := by apply List.Pairwise.sortedGE; simp)
    (show Fin [r+δ,r].length from ⟨0,by simp⟩)

lemma repeat_transpose_height {m k : ℕ} (hm : 0 < m) :
    (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose.colLen 0 = k := by
  rw [YoungDiagram.colLen_transpose]
  simpa only [Fin.getElem_fin,List.getElem_replicate] using
    YoungDiagram.rowLen_ofRowLens (hw := replicate_sorted m k)
      (show Fin (List.replicate m k).length from ⟨0,by simpa⟩)

lemma repeat_transpose_rows {m k : ℕ} (hk : 0 < k) :
    (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose.transpose.rowLens =
      List.replicate m k := by
  rw [YoungDiagram.transpose_transpose]
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  rw [(List.mem_replicate.mp hx).2]
  exact hk

lemma repeated_twos_shape (m : ℕ) :
    (YoungDiagram.ofRowLens (List.replicate m 2) (replicate_sorted m 2)).transpose =
      ShortColumns.shape m 0 := by
  apply YoungDiagram.ext
  apply Finset.ext
  intro x
  rcases x with ⟨i,j⟩
  change (i,j) ∈ (YoungDiagram.ofRowLens (List.replicate m 2) (replicate_sorted m 2)).transpose ↔
    (i,j) ∈ ShortColumns.shape m 0
  simp only [YoungDiagram.mem_transpose,YoungDiagram.mem_ofRowLens,
    List.length_replicate,List.getElem_replicate,ShortColumns.mem_shape,Prod.swap_prod_mk]
  simp only [exists_prop,Nat.add_zero]
  omega

lemma two_paths_two_support_sizes {n a b q : ℕ} {ν : YoungDiagram}
    (hn : n = 2*q+4) (ha : a = 2*q+2) (hb : b = 2) (hq : 3 ≤ q)
    (t : Tableau a (ShortColumns.shape q 2).transpose) (u : Tableau b ν)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (hu : ∀ i, (columnLengthWord u i).val+1 = 1) :
    SupportLE (wordRep n 4)
      (Representation.coind (sumPermHom e)
        (outer (projectedSpechtTensor t t (inOutputs (Set.Icc q (2*q+3)))
          (inOutputs_invariant (Set.Icc q (2*q+3)))).toRepresentation
          (projectedSpechtTensor u u (inOutputs {1}) (inOutputs_invariant {1})).toRepresentation)) := by
  subst n a b
  exact (two_paths_two_coind q hq t e).trans
    (SupportLE.coind _ ((SupportLE.refl _).outer (constant_output_support u 1 hu)))

theorem WordPacking.twoPaths {q d : ℕ} (hq : 3 ≤ q) (hd : q+2 ≤ d)
    {ps : List ℕ} (hsum : ps.sum = 2*q+4) (hlen : ps.length ≤ 4)
    (k l : ℕ) (hne : k ≠ l) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ Set.Icc q (2*q+3))
    (he' : ∀ a, (A a ∧ label a = l) ↔ output a = 1) :
    Nonempty (WordPacking ([q+2,q] ++ List.replicate 2 1) ps d A label {k,l}) := by
  have hrow : (ShortColumns.shape q 2).rowLens = [q+2,q] :=
    YoungDiagram.rowLens_ofRowLens_eq_self (by simp; omega)
  let ν := (YoungDiagram.ofRowLens (List.replicate 2 1) (replicate_sorted 2 1)).transpose
  apply WordPacking.of_binary_shapes (μ := (ShortColumns.shape q 2).transpose) (ν := ν)
    (by rw [YoungDiagram.transpose_transpose,hrow]) (by rw [repeat_transpose_rows (by decide)])
    (by rw [short_transpose_height]; exact hd)
    (by rw [repeat_transpose_height (by decide)]; omega)
    (by simp; omega) hlen k l hne _ {1} A label he he'
  intro t u
  exact two_paths_two_support_sizes (by simp; omega) (by simp; omega) (by simp)
    hq t u (appendPositions _ _) (repeated_column_length (by decide) u)

lemma even_twos_odd_support_sizes {n a b m x : ℕ} {ν : YoungDiagram}
    (hn : n = 2*m+x) (ha : a = 2*m) (hb : b = x)
    (hm : 1 ≤ m) (hx : Odd x) (hxc : x ≤ 2*m)
    (t : Tableau a (ShortColumns.shape m 0)) (u : Tableau b ν)
    (e : Fin n ≃ Fin a ⊕ Fin b) (hu : ∀ i, (columnLengthWord u i).val+1 = x) :
    SupportLE (wordRep n 2)
      (Representation.coind (sumPermHom e)
        (outer (projectedSpechtTensor t t (inOutputs {2}) (inOutputs_invariant {2})).toRepresentation
          (projectedSpechtTensor u u (inOutputs {x}) (inOutputs_invariant {x})).toRepresentation)) := by
  subst n a b
  exact (even_twos_odd_coind m x hm hx hxc t e).trans
    (SupportLE.coind _ ((SupportLE.refl _).outer (constant_output_support u x hu)))

theorem WordPacking.twosOdd {m x d : ℕ} (hm : 1 ≤ m) (hx : Odd x) (hxc : x ≤ 2*m)
    (hd : 2 ≤ d) (hd' : x ≤ d)
    {ps : List ℕ} (hsum : ps.sum = 2*m+x) (hlen : ps.length ≤ 2)
    (k l : ℕ) (hne : k ≠ l) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a = 2)
    (he' : ∀ a, (A a ∧ label a = l) ↔ output a = x) :
    Nonempty (WordPacking (List.replicate m 2 ++ [x]) ps d A label {k,l}) := by
  let ν := (YoungDiagram.ofRowLens (List.replicate 1 x) (replicate_sorted 1 x)).transpose
  have hxpos : 0 < x := hx.pos
  have hp : (List.replicate m 2).Perm (ShortColumns.shape m 0).transpose.rowLens := by
    rw [← repeated_twos_shape,repeat_transpose_rows (by decide)]
  apply WordPacking.of_binary_shapes (μ := ShortColumns.shape m 0) (ν := ν) hp
    (by rw [repeat_transpose_rows hxpos]; rfl)
    ((ShortColumns.height_le m 0).trans hd)
    (by rw [repeat_transpose_height (by decide)]; exact hd')
    (by simp only [List.sum_append,List.sum_replicate,List.sum_singleton,smul_eq_mul]; omega)
    hlen k l hne {2} {x} A label he he'
  intro t u
  exact even_twos_odd_support_sizes (by simp; omega) (by simp; omega) (by simp)
    hm hx hxc t u (appendPositions _ _) (repeated_column_length hxpos u)

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_PackingPlans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packing Plans. -/

section

noncomputable section
namespace Saxl.Balance
open Columns FlagColumns

namespace PackingPlan

theorem realize_oai (p : PackingPlan) {d : ℕ} (h : p.Valid d)
    (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ e ∈ p.bands, ∀ z, (A z ∧ label z = e.1) ↔ output z ∈ Set.Icc e.1 e.2) :
    Nonempty (WordPacking p.columns p.parts d A label p.marks) := by
  induction p with
  | empty => simpa [columns,parts,marks,bands,bandStarts] using
      Nonempty.intro (WordPacking.empty d A label)
  | neighbor r ps =>
    rcases h with ⟨hr,hd,hs,hl⟩
    simpa [columns,parts,marks,bands,bandStarts] using
      WordPacking.neighbor hr hd hs hl r A label (he (r,r+1) (by simp [bands]))
  | repeated m k =>
    rcases h with ⟨hm,hk,hd⟩
    have hei : ∀ z, (A z ∧ label z = k) ↔ output z = k := by
      intro z
      rw [he (k,k) (by simp [bands]) z]
      simp only [Set.mem_Icc]; omega
    simpa [columns,parts,marks,bands,bandStarts] using WordPacking.repeated hm hk hd k A label hei
  | twosOdd m x ps =>
    rcases h with ⟨hm,hx,hxc,hd,hd',hs,hl⟩
    have hne : 2 ≠ x := by intro heq; rw [← heq] at hx; norm_num at hx
    have hei : ∀ k, (k,k) ∈ (PackingPlan.twosOdd m x ps).bands →
        ∀ z, (A z ∧ label z = k) ↔ output z = k := by
      intro k hk z
      rw [he (k,k) hk z]
      simp only [Set.mem_Icc]; omega
    simpa [columns,parts,marks,bands,bandStarts] using WordPacking.twosOdd hm hx hxc hd hd' hs hl
      2 x hne A label (hei 2 (by simp [bands])) (hei x (by simp [bands]))
  | twoPaths q ps =>
    rcases h with ⟨hq,hd,hs,hl⟩
    have he1 : ∀ z, (A z ∧ label z = 1) ↔ output z = 1 := by
      intro z
      rw [he (1,1) (by simp [bands]) z]
      simp only [Set.mem_Icc]; omega
    simpa [columns,parts,marks,bands,bandStarts] using WordPacking.twoPaths hq hd hs hl
      q 1 (by omega) A label (he (q,2*q+3) (by simp [bands])) he1
  | threeRows m s ps cs =>
    simpa [columns,parts,marks,bands,bandStarts] using
      WordPacking.threeRows h.1 h.2 A label (he (1,3) (by simp [bands]))
  | join p q ip iq =>
    obtain ⟨P⟩ := ip h.1 (by intro e he' z; exact he e (List.mem_append_left _ he') z)
    obtain ⟨Q⟩ := iq h.2.1 (by intro e he' z; exact he e (List.mem_append_right _ he') z)
    simpa only [columns,parts,marks,bands,bandStarts,List.map_append,List.toFinset_append] using
      Nonempty.intro (P.join Q h.2.2)

end PackingPlan
end Saxl.Balance

end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.Balance.PackingPlan.realize_oai := @OAI.Saxl.Balance.PackingPlan.realize_oai
