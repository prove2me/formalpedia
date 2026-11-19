-- Prove2me | solution 1 for OAI.Saxl.ShortColumns.one_extra_odd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:36:09.244432+00:00
-- url     : https://prove2.me/submissions/2d9116c4-fe60-4be2-8206-4844528904da

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US023
import Theorems.Thm_OAI_Saxl_one_odd_row_symmetricPartialPairs_support
import Theorems.Thm_OAI_Saxl_specht_sign_transpose_uts

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
-- module Solutions.OAIQ259_US.Saxl_DominatedQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma subrepProject_subtype {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule) (x : S) :
    subrepProject S hS x.val = x := by
  change (subrepSelfDual S hS).symm (subrepSelfDual S hS x) = x
  exact (subrepSelfDual S hS).symm_apply_apply x

end Saxl

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

lemma shortPairCongruence_gram :
    (fun j k => ∑ p : Fin 4 × Fin 4,
      shortPairForm p.1 p.2 * shortPairCongruence p.1 j * shortPairCongruence p.2 k) =
      (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    (first | (simp [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply]; all_goals first | (norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply]; done) | rfl | decide) | (norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply]; done) | norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm, shortPairCongruence, Matrix.one_apply])

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SingletonPairs
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.pairWordsEquiv_apply _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton Pairs. -/

section

noncomputable section
namespace Saxl

lemma wordMap_positionProduct {n a b d D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (L : Fin d → Fin D → ℂ) (x : WordSpace a d) (y : WordSpace b d) :
    wordMap L (positionProduct e x y) =
      positionProduct e (wordMap L x) (wordMap L y) := by
  classical
  funext w
  change (∑ c, (x (leftWord e c) * y (rightWord e c)) * ∏ i, L (c i) (w i)) = _
  calc
    _ = ∑ p : (Fin a → Fin d) × (Fin b → Fin d),
        (x p.1 * ∏ i, L (p.1 i) (leftWord e w i)) *
          (y p.2 * ∏ i, L (p.2 i) (rightWord e w i)) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro c
      have he : (∏ i, L (c i) (w i)) =
          (∏ i, L (leftWord e c i) (leftWord e w i)) *
            ∏ i, L (rightWord e c i) (rightWord e w i) := by
        calc
          _ = ∏ z : Fin a ⊕ Fin b, L (c (e.symm z)) (w (e.symm z)) :=
            (Equiv.prod_comp e.symm (fun i => L (c i) (w i))).symm
          _ = _ := by rw [Fintype.prod_sum_type]; rfl
      rw [he]
      change _ = (x (leftWord e c) * _) * (y (rightWord e c) * _)
      dsimp [positionWordsEquiv]
      ring
    _ = _ := by
      change _ = (∑ c, x c * ∏ i, L (c i) (leftWord e w i)) *
        (∑ c, y c * ∏ i, L (c i) (rightWord e w i))
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      simp only [Finset.mul_sum]

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SingletonForms
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Singleton Forms. -/

section

noncomputable section
namespace Saxl

lemma wordMap_singleWord {a b : ℕ} (L : Fin a → Fin b → ℂ) (v : Fin a → ℂ) :
    wordMap L (singleWord v) = singleWord (fun j => ∑ i, v i * L i j) := by
  classical
  funext w
  change (∑ c : Fin 1 → Fin a, v (c 0) * ∏ i, L (c i) (w i)) = _
  simpa only [Fintype.prod_unique, show (default : Fin 1) = 0 from rfl, singleWord] using
    (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin a))
      (fun c => v (c 0) * L (c 0) (w 0))
      (fun i => v i * L i (w 0)) (fun _ => rfl))

lemma wordMap_pairSingletonTensor {n a m d D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m)
    (L : Fin d → Fin D → ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    wordMap L (pairSingletonTensor e p B v) = pairSingletonTensor e p
      (fun j k => ∑ q : Fin d × Fin d, B q.1 q.2 * L q.1 j * L q.2 k)
      (fun j => ∑ i, v i * L i j) := by
  rw [pairSingletonTensor, wordMap_positionProduct, wordMap_pairFormTensor,
    wordMap_singleWord]
  rfl

lemma pairSingletonTensor_one {n a m d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m) (v : Fin d → ℂ) :
    pairSingletonTensor e p (1 : Matrix (Fin d) (Fin d) ℂ) v =
      symmetricPartialPairs (pairSingletonEquiv e p) Fin.castSuccEmb v := by
  classical
  funext w
  have ht : leftWord (pairSingletonEquiv e p) w ∘ Fin.castSuccEmb =
      leftWord p (leftWord e w) := by
    funext k
    simp [leftWord]
  have hb : rightWord (pairSingletonEquiv e p) w = rightWord p (leftWord e w) := by
    funext k
    simp [rightWord,leftWord]
  have hlast : Fin.last m ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m+1)) := by
    rintro ⟨k,hk⟩
    have hh := congrArg Fin.val hk
    have hh' := k.isLt
    change k.val = m at hh
    omega
  have hcast (k : Fin m) : k.castSucc ∈ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m+1)) :=
    ⟨k,rfl⟩
  have hprod : (∏ k ∈ Finset.univ.filter
        (fun k => k ∉ Set.range (Fin.castSuccEmb : Fin m ↪ Fin (m+1))),
        v (leftWord (pairSingletonEquiv e p) w k)) = v (rightWord e w 0) := by
    rw [Finset.prod_filter, Fin.prod_univ_castSucc]
    simp [leftWord,rightWord]
  unfold symmetricPartialPairs
  rw [ht,hb,hprod]
  unfold pairSingletonTensor
  rw [pairFormTensor_one]
  change (if leftWord p (leftWord e w) = rightWord p (leftWord e w) then 1 else 0) *
    v (rightWord e w 0) = _
  split_ifs <;> simp

lemma pairSingletonTensor_smul {n a m d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m)
    (B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (c : ℂ) :
    pairSingletonTensor e p (c • B) v = c^m • pairSingletonTensor e p B v := by
  unfold pairSingletonTensor
  rw [pairFormTensor_smul]
  funext w
  change c^m * pairFormTensor p B (leftWord e w) * singleWord v (rightWord e w) = _
  exact mul_assoc _ _ _

theorem one_odd_row_pairSingleton_support {n a m d D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m)
    (B : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ)
    (L : Fin d → Fin D → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hL : (fun j k => ∑ q : Fin d × Fin d, B q.1 q.2 * L q.1 j * L q.2 k) =
      c • (1 : Matrix (Fin D) (Fin D) ℂ))
    (hv : (fun j => ∑ i, v i * L i j) ≠ 0)
    (μ : YoungDiagram) (t : Tableau n μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ D) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (pairSingletonTensor e p B v)).toRepresentation, F ≠ 0 := by
  let v' := fun j => ∑ i, v i * L i j
  have hmap : wordMap L (pairSingletonTensor e p B v) =
      c^m • symmetricPartialPairs (pairSingletonEquiv e p) Fin.castSuccEmb v' := by
    rw [wordMap_pairSingletonTensor, hL, pairSingletonTensor_smul, pairSingletonTensor_one]
  have hcyc : cyclic (wordRep n D) (wordMap L (pairSingletonTensor e p B v)) =
      cyclic (wordRep n D) (symmetricPartialPairs (pairSingletonEquiv e p) Fin.castSuccEmb v') := by
    rw [hmap, cyclic_smul_eq _ _ _ (pow_ne_zero m hc)]
  have hs := one_odd_row_symmetricPartialPairs_support (pairSingletonEquiv e p) Fin.castSuccEmb
    v' hv μ t k hk he hd
  rw [← hcyc] at hs
  obtain ⟨F,hF⟩ := hs
  exact cyclic_projection_support (wordMap L) (pairSingletonTensor e p B v) F hF

lemma shortPair_singleton_nonzero :
    (fun j => ∑ i : Fin 4, (Pi.single 0 (1 : ℂ) : Fin 4 → ℂ) i * shortPairCongruence i j) ≠ 0 := by
  intro h
  have hh := congrFun h (0 : Fin 4)
  first | (simp [shortPairCongruence, Pi.single_apply, Fin.sum_univ_succ] at hh; all_goals first | (norm_num [shortPairCongruence, Pi.single_apply, Fin.sum_univ_succ] at hh; done) | rfl | decide) | (norm_num [shortPairCongruence, Pi.single_apply, Fin.sum_univ_succ] at hh; done) | norm_num [shortPairCongruence, Pi.single_apply, Fin.sum_univ_succ] at hh

theorem one_odd_row_shortPair_support {n a m : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin 1) (p : Fin a ≃ Fin m ⊕ Fin m)
    (μ : YoungDiagram) (t : Tableau n μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 4) (pairSingletonTensor e p shortPairForm (Pi.single 0 1))).toRepresentation,
      F ≠ 0 :=
  one_odd_row_pairSingleton_support e p shortPairForm (Pi.single 0 1)
    shortPairCongruence 2 (by norm_num) shortPairCongruence_gram
      shortPair_singleton_nonzero μ t k hk he hd

end Saxl
end
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

lemma oddTableau_col_iff (b : ℕ) (i j : Fin (2*b+1)) :
    ((oddTableau b) i).val.2 = ((oddTableau b) j).val.2 ↔
      PathLayer.tag i = PathLayer.tag j := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [oddTableau, Equiv.coe_fn_mk, PathLayer.tag]
  split_ifs <;> dsimp only <;> omega

lemma oddTableau_group (b : ℕ) :
    columnGroup (oddTableau b) = fiberGroup (@PathLayer.tag b) := by
  apply Subgroup.ext
  intro g
  change (∀ i, ((oddTableau b) (g i)).val.2 = ((oddTableau b) i).val.2) ↔ _
  simp only [oddTableau_col_iff]
  rfl

lemma oddTableau_polytabloid (b : ℕ) :
    letterLift (Fin.castLE (height_le b 1)) (polytabloid (oddTableau b)) =
      PathLayer.rowAlt b := by
  rw [polytabloid_eq_altWord, letterLift_altWord, oddTableau_group]
  congr 1
  funext i
  apply Fin.ext
  exact oddTableau_row b i

lemma shortPairForm_eq (i j : Fin 4) :
    shortPairForm i j = PathLayer.J ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).1 ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm j).1 *
      PathLayer.J ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).2 ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm j).2 := by
  fin_cases i <;> fin_cases j <;>
    (first | (simp [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]; all_goals first | (norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]; done) | rfl | decide) | (norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]; done) | norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat])

lemma singleton_square (i : Fin 4) :
    (if ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).1 = (0 : Fin 2) then (1 : ℂ) else 0) *
      (if ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).2 = 0 then 1 else 0) =
      (Pi.single 0 1 : Fin 4 → ℂ) i := by
  fin_cases i <;>
    (first | (simp [finProdFinEquiv, Fin.divNat, Fin.modNat, Pi.single_apply, Fin.ext_iff]; all_goals first | (norm_num [finProdFinEquiv, Fin.divNat, Fin.modNat, Pi.single_apply, Fin.ext_iff]; done) | rfl | decide) | (norm_num [finProdFinEquiv, Fin.divNat, Fin.modNat, Pi.single_apply, Fin.ext_iff]; done) | norm_num [finProdFinEquiv, Fin.divNat, Fin.modNat, Pi.single_apply, Fin.ext_iff])

lemma odd_square (b : ℕ) :
    wordTensor (2*b+1) 2 2 (PathLayer.rowAlt b ⊗ₜ[ℂ] PathLayer.rowAlt b) =
      pairSingletonTensor (oddSplit b) (pairSplit b) shortPairForm (Pi.single 0 1) := by
  funext w
  rw [wordTensor_tmul, PathLayer.rowAlt_formula, PathLayer.rowAlt_formula]
  have hp (i : Fin b) :
      leftWord (pairSplit b) (leftWord (oddSplit b) w) i =
        w ⟨2*i.val+1,by omega⟩ ∧
      rightWord (pairSplit b) (leftWord (oddSplit b) w) i =
        w ⟨2*i.val+2,by omega⟩ := by
    constructor <;> apply congrArg w <;> apply Fin.ext <;>
      simp only [oddSplit_left, pairSplit_left, pairSplit_right]
  change (if splitLeft w 0 = 0 then (1 : ℂ) else 0) * _ *
    ((if splitRight w 0 = 0 then 1 else 0) * _) =
    (∏ i, shortPairForm (leftWord (pairSplit b) (leftWord (oddSplit b) w) i)
      (rightWord (pairSplit b) (leftWord (oddSplit b) w) i)) *
      (Pi.single 0 1 : Fin 4 → ℂ) (rightWord (oddSplit b) w 0)
  simp_rw [(hp _).1, (hp _).2, shortPairForm_eq]
  simp only [Finset.prod_mul_distrib, rightWord, oddSplit_right, splitLeft, splitRight]
  rw [← singleton_square]
  ac_rfl

end Saxl.ShortColumns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_AttachmentTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Attachment Transfer. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl

lemma transposeColumnAverage_nonzero {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    transposeColumnAverage t ≠ 0 := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  intro he
  have hh := congrArg (fun y : Specht t => y.val (rowWord t)) he
  have hg (g : columnGroup (transposeTableau t)) : rowWord t ∘ g.val = rowWord t := by
    funext i
    apply Fin.ext
    exact g.property i
  simp only [transposeColumnAverage, Submodule.coe_sum, Finset.sum_apply] at hh
  change (∑ g : columnGroup (transposeTableau t),
    polytabloid t (rowWord t ∘ g.val)) = 0 at hh
  simp only [hg, polytabloid_rowWord, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hh
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hh

lemma transposeColumnAverage_fixed {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (g : columnGroup (transposeTableau t)) :
    spechtRep t g.val (transposeColumnAverage t) = transposeColumnAverage t := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  unfold transposeColumnAverage
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : columnGroup (transposeTableau t) =>
    spechtRep t h.val ⟨polytabloid t, mem_cyclic _ _⟩)

lemma signEquiv_transposeColumnAverage {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (transposeColumnAverage t)).val =
      c • polytabloid (transposeTableau t) := by
  have ha (g : columnGroup (transposeTableau t)) :
      spechtRep (transposeTableau t) g.val (φ (transposeColumnAverage t)) =
        signC g.val • φ (transposeColumnAverage t) := by
    have he := LinearMap.congr_fun (φ.isIntertwining' g.val) (transposeColumnAverage t)
    change φ (spechtRep t g.val (transposeColumnAverage t)) =
      signC g.val • spechtRep (transposeTableau t) g.val (φ (transposeColumnAverage t)) at he
    rw [transposeColumnAverage_fixed] at he
    have hh := congrArg (fun x => signC g.val • x) he
    simpa only [smul_smul, signC_mul_self, one_smul] using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (transposeTableau t)
    (φ (transposeColumnAverage t)) ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply transposeColumnAverage_nonzero t
  apply φ.injective
  exact (Subtype.ext hc).trans (map_zero φ).symm

lemma columnAmbientSignMap_subtype {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t))))
    (x : Specht t) : columnAmbientSignMap t φ x.val = (φ x).val := by
  change (φ (subrepProject (spechtSub t) _ x.val)).val = _
  exact congrArg (fun y : Specht t => (φ y).val) (subrepProject_subtype (spechtSub t) _ x)

lemma columnPairAntiMap_tensor {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t))))
    (x : WordSpace n (α.transpose.colLen 0)) (y : WordSpace n (α.colLen 0)) :
    columnPairAntiMap t φ (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) =
      wordTensor _ _ _ (x ⊗ₜ[ℂ] columnAmbientSignMap t φ y) := by
  change wordTensor _ _ _ (TensorProduct.map LinearMap.id
    (columnAmbientSignMap t φ).toLinearMap
    ((wordTensor _ _ _).symm (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

lemma signed_average_rowColumn {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    letI := Fintype.ofFinite (columnGroup (transposeTableau t))
    ∑ g : columnGroup (transposeTableau t), signC g.val •
      wordRep n (α.transpose.colLen 0 * α.colLen 0) g.val (rowColumnWord t) =
      wordTensor _ _ _
        (polytabloid (transposeTableau t) ⊗ₜ[ℂ] (transposeColumnAverage t).val) := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  change _ = wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
    (∑ g : columnGroup (transposeTableau t),
      spechtRep t g.val ⟨polytabloid t, mem_cyclic _ _⟩).val)
  rw [Submodule.coe_sum, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change signC g.val • wordRep _ _ g.val (wordTensor _ _ _
    (polytabloid (transposeTableau t) ⊗ₜ[ℂ] polytabloid t)) = _
  rw [← wordTensor_equivariant]
  change signC g.val • wordTensor _ _ _
    (wordRep _ _ g.val (polytabloid (transposeTableau t)) ⊗ₜ[ℂ]
      wordRep _ _ g.val (polytabloid t)) = _
  rw [polytabloid_alternating _ g, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    map_smul, smul_smul, signC_mul_self, one_smul]
  rfl

theorem polytabloid_square_in_rowColumn_image {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
      polytabloid (transposeTableau t)) ∈ (rowColumnToSquare t φ).range := by
  classical
  let := Fintype.ofFinite (columnGroup (transposeTableau t))
  obtain ⟨c,hc,hφ⟩ := signEquiv_transposeColumnAverage t φ
  let x : (rowColumnCyclic t).toSubmodule :=
    ∑ g : columnGroup (transposeTableau t), signC g.val •
      (rowColumnCyclic t).toRepresentation g.val ⟨rowColumnWord t, mem_cyclic _ _⟩
  have hx : x.val = wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
      (transposeColumnAverage t).val) := by
    change (∑ g : columnGroup (transposeTableau t), signC g.val •
      (rowColumnCyclic t).toRepresentation g.val ⟨rowColumnWord t, mem_cyclic _ _⟩).val = _
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact signed_average_rowColumn t
  have hF : rowColumnToSquare t φ x = c • wordTensor _ _ _
      (polytabloid (transposeTableau t) ⊗ₜ[ℂ] polytabloid (transposeTableau t)) := by
    change columnPairAntiMap t φ x.val = _
    rw [hx, columnPairAntiMap_tensor, columnAmbientSignMap_subtype, hφ,
      TensorProduct.tmul_smul, map_smul]
  exact (Submodule.smul_mem_iff _ hc).mp ⟨x,hF⟩

theorem square_cyclic_embeds_sign_rowColumn {n : ℕ} {α : YoungDiagram} (t : Tableau n α) :
    ∃ f : Representation.IntertwiningMap
      (cyclic (wordRep n (α.transpose.colLen 0 * α.transpose.colLen 0))
        (wordTensor _ _ _ (polytabloid (transposeTableau t) ⊗ₜ[ℂ]
          polytabloid (transposeTableau t)))).toRepresentation
      (signTwist (rowColumnCyclic t).toRepresentation), Function.Injective f := by
  obtain ⟨φ⟩ := specht_sign_transpose_uts t
  apply subrepresentation_embeds_of_le_range (rowColumnToSquare t φ)
  exact (cyclic_le _ _ _).mpr (polytabloid_square_in_rowColumn_image t φ)

end Saxl
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

theorem sign_rowColumn_support_of_columnSquare {n : ℕ} {α : YoungDiagram} (t : Tableau n α)
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (f : Representation.IntertwiningMap ρ (columnSquareCyclic t).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap ρ (signTwist (rowColumnCyclic t).toRepresentation),
      g ≠ 0 := by
  let T := transposeTableau (transposeTableau t)
  let F := pairWordMap (n := n) (letterLift (Fin.cast (congrArg (fun ν : YoungDiagram => ν.colLen 0)
    (YoungDiagram.transpose_transpose α))))
    (letterLift (Fin.cast (congrArg (fun ν : YoungDiagram => ν.colLen 0)
    (YoungDiagram.transpose_transpose α))))
  have hF : F (columnSquareWord T) = columnSquareWord t := by
    change pairWordMap _ _ (wordTensor _ _ _ (_ ⊗ₜ[ℂ] _)) = _
    rw [pairWordMap_tensor, polytabloid_doubleTranspose]
    rfl
  have hs : ∃ g : Representation.IntertwiningMap ρ
      (cyclic (wordRep n (α.colLen 0 * α.colLen 0)) (F (columnSquareWord T))).toRepresentation,
        g ≠ 0 := by
    rw [hF]
    exact ⟨f,hf⟩
  obtain ⟨f',hf'⟩ := hs
  obtain ⟨f'',hf''⟩ := cyclic_projection_support F (columnSquareWord T) f' hf'
  obtain ⟨A,hA⟩ := square_cyclic_embeds_sign_rowColumn (transposeTableau t)
  let B := signTwistMap (rowColumnTransposeCyclicMap t)
  refine ⟨B.comp (A.comp f''), intertwining_comp_ne_zero B ?_ _
    (intertwining_comp_ne_zero A hA f'' hf'')⟩
  exact rowColumnTransposeCyclicMap_injective t

lemma transposeTableau_move {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    tableauMove (transposeTableau s) (transposeTableau t) = tableauMove s t := by
  ext i
  rfl

lemma rowColumnWord_move {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    wordRep n _ (tableauMove s t) (rowColumnWord s) = rowColumnWord t := by
  unfold rowColumnWord
  rw [← wordTensor_equivariant]
  change wordTensor _ _ _ (wordRep _ _ (tableauMove s t) (polytabloid (transposeTableau s))
    ⊗ₜ[ℂ] wordRep _ _ (tableauMove s t) (polytabloid s)) = _
  rw [← polytabloid_move s t, ← transposeTableau_move s t,
    ← polytabloid_move (transposeTableau s) (transposeTableau t)]

lemma cyclic_translate_eq {G X : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (g : G) (v : X) : cyclic ρ (ρ g v) = cyclic ρ v := by
  apply le_antisymm
  · exact (cyclic_le _ _ _).mpr ((cyclic ρ v).apply_mem_toSubmodule g (mem_cyclic _ _))
  · apply (cyclic_le _ _ _).mpr
    have h := (cyclic ρ (ρ g v)).apply_mem_toSubmodule g⁻¹ (mem_cyclic _ _)
    change v ∈ (cyclic ρ (ρ g v)).toSubmodule
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h

lemma rowColumnCyclic_tableau_independent {n : ℕ} {α : YoungDiagram} (s t : Tableau n α) :
    rowColumnCyclic s = rowColumnCyclic t := by
  unfold rowColumnCyclic
  rw [← rowColumnWord_move s t, cyclic_translate_eq]

theorem rowColumn_support_change_tableau {n : ℕ} {α : YoungDiagram} (s t : Tableau n α)
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (f : Representation.IntertwiningMap ρ (signTwist (rowColumnCyclic s).toRepresentation))
    (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap ρ (signTwist (rowColumnCyclic t).toRepresentation),
      g ≠ 0 := by
  rw [← rowColumnCyclic_tableau_independent s t]
  exact ⟨f,hf⟩

namespace ShortColumns

theorem odd_columnSquare_support (b : ℕ) (μ : YoungDiagram) (t : Tableau (2*b+1) μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (columnSquareCyclic (oddTableau b)).toRepresentation, F ≠ 0 := by
  let F := pairWordMap (n := 2*b+1) (letterLift (Fin.castLE (height_le b 1)))
    (letterLift (Fin.castLE (height_le b 1)))
  have hF : F (columnSquareWord (oddTableau b)) =
      pairSingletonTensor (oddSplit b) (pairSplit b) shortPairForm (Pi.single 0 1) := by
    change pairWordMap _ _ (wordTensor _ _ _ (_ ⊗ₜ[ℂ] _)) = _
    rw [pairWordMap_tensor, oddTableau_polytabloid, odd_square]
  have hs := one_odd_row_shortPair_support (oddSplit b) (pairSplit b) μ t k hk he hd
  rw [← hF] at hs
  obtain ⟨g,hg⟩ := hs
  exact cyclic_projection_support F (columnSquareWord (oddTableau b)) g hg

theorem one_extra_odd_oai (b : ℕ) (s : Tableau (2*b+1) (shape b 1))
    (μ : YoungDiagram) (t : Tableau (2*b+1) μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (signTwist (rowColumnCyclic s).toRepresentation), F ≠ 0 := by
  obtain ⟨f,hf⟩ := odd_columnSquare_support b μ t k hk he hd
  obtain ⟨g,hg⟩ := sign_rowColumn_support_of_columnSquare (oddTableau b) (spechtRep t) f hf
  exact rowColumn_support_change_tableau (oddTableau b) s (spechtRep t) g hg

end ShortColumns
end Saxl
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.ShortColumns.one_extra_odd_oai := @OAI.Saxl.ShortColumns.one_extra_odd_oai
