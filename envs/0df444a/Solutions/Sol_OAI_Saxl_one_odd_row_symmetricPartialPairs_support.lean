-- Prove2me | solution 1 for OAI.Saxl.one_odd_row_symmetricPartialPairs_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:12:26.760194+00:00
-- url     : https://prove2.me/submissions/30a6b56a-49aa-4553-b558-07c82ca184f7

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
-- module Solutions.OAIQ259_US.Saxl_PieriRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/

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

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_RepeatedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem specht_map_back_of_nonzero {n : ℕ} {μ : YoungDiagram}
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X) (t : Tableau n μ)
    (F : Representation.IntertwiningMap ρ (spechtRep t)) (hF : F ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep t) ρ, f ≠ 0 := by
  let := specht_irreducible t
  have hs : Function.Surjective F :=
    (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  obtain ⟨f, hf⟩ := intertwining_lift_surjective F hs
    (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have he := congrArg (fun H : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    H ⟨polytabloid t, mem_cyclic _ _⟩) hf
  change F (f _) = _ at he
  rw [hz] at he
  change F 0 = _ at he
  rw [map_zero] at he
  exact polytabloid_ne_zero t (congrArg Subtype.val he.symm)

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_GeneralDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! General Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordMap_pair_transpose {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (x : WordSpace n d) (y : WordSpace n e) :
    dotProduct (wordMap L x) y = dotProduct x (wordMap (fun b a => L a b) y) := by
  classical
  change (∑ b, (∑ a, x a * ∏ i, L (a i) (b i)) * y b) =
    ∑ a, x a * ∑ b, y b * ∏ i, L (a i) (b i)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem specht_to_cyclic_of_pair {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (L : Fin (μ.colLen 0) → Fin d → ℂ)
    (u : WordSpace n d)
    (h : dotProduct (wordMap L (polytabloid t)) u ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, F ≠ 0 := by
  let pr := subrepProject (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
  let F : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) :=
    pr.comp ((wordMap (fun b a => L a b)).comp (subrepInclusion _))
  apply specht_map_back_of_nonzero _ t F
  intro hz
  have hp := subrepProject_pair (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
    (wordMap (fun b a => L a b) u) ⟨polytabloid t, mem_cyclic _ _⟩
  have he : pr (wordMap (fun b a => L a b) u) = 0 :=
    congrArg (fun H : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) =>
      H ⟨u, mem_cyclic _ _⟩) hz
  rw [he] at hp
  change dotProduct (0 : WordSpace n (μ.colLen 0)) (polytabloid t) =
    dotProduct (wordMap (fun b a => L a b) u) (polytabloid t) at hp
  rw [zero_dotProduct] at hp
  rw [wordMap_pair_transpose, dotProduct_comm]
    at h
  exact h hp.symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_SymmetricPairs
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
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

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_AlternateColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Alternate Columns. -/

section

noncomputable section
namespace Saxl

lemma alternateCells_card (μ : YoungDiagram) :
    (ceilRows μ).card + (halfRows μ).card = μ.card := by
  simpa only [Fintype.card_sum, Fintype.card_coe] using Fintype.card_congr (alternateCells μ)

lemma alternateTableau_left {n a b : ℕ} (μ : YoungDiagram) (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) (i : Fin a) :
    (alternateTableau μ e s t (e.symm (Sum.inl i))).val = ((s i).val.1,2*(s i).val.2) := by
  simp [alternateTableau, alternateCells]

lemma alternateTableau_right {n a b : ℕ} (μ : YoungDiagram) (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) (i : Fin b) :
    (alternateTableau μ e s t (e.symm (Sum.inr i))).val = ((t i).val.1,2*(t i).val.2+1) := by
  simp [alternateTableau, alternateCells]

lemma alternateTableau_group_sector {n a b : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin a ⊕ Fin b) (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) :
    columnGroup (alternateTableau μ e s t) ≤ sectorGroup (fun i => (e i).isLeft = true) := by
  intro g hg i
  have hc := hg i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  obtain ⟨k,hk⟩ := e.symm.surjective (g (e.symm j))
  rw [← hk] at hc ⊢
  cases j <;> cases k <;>
    simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, Sum.isLeft_inr] at *
  · rw [alternateTableau_left, alternateTableau_right] at hc
    dsimp only at hc
    omega
  · rw [alternateTableau_left, alternateTableau_right] at hc
    dsimp only at hc
    omega

lemma alternateTableau_factor {n a b : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin a ⊕ Fin b) (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ)) :
    polytabloid (alternateTableau μ e s t) = positionProduct e
      (letterLift (Fin.cast (ceilRows_height μ)) (polytabloid s))
      (letterLift (Fin.cast (ceilRows_height μ) ∘ rowLetterInclusion (halfRows_le_ceilRows μ))
        (polytabloid t)) := by
  let u := alternateTableau μ e s t
  let f : Fin n → ℕ := fun i => (u i).val.2
  have hn : columnGroup u = fiberGroup f := rfl
  have hg : columnGroup u = fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true) := by
    rw [← hn]
    exact (inf_eq_left.mpr (alternateTableau_group_sector μ e s t)).symm
  have hl : fiberGroup (fun i => f (e.symm (Sum.inl i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (u (e.symm (Sum.inl (g i)))).val.2 =
      (u (e.symm (Sum.inl i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [u, alternateTableau_left, Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hr : fiberGroup (fun i => f (e.symm (Sum.inr i))) = columnGroup t := by
    apply Subgroup.ext
    intro g
    change (∀ i, (u (e.symm (Sum.inr (g i)))).val.2 =
      (u (e.symm (Sum.inr i))).val.2) ↔ ∀ i, (t (g i)).val.2 = (t i).val.2
    simp only [u, alternateTableau_right, Nat.add_right_cancel_iff,
      Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hw₁ : leftWord e (rowWord u) = Fin.cast (ceilRows_height μ) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (u (e.symm (Sum.inl i))).val.1 = (s i).val.1
    rw [alternateTableau_left]
  have hw₂ : rightWord e (rowWord u) =
      (Fin.cast (ceilRows_height μ) ∘ rowLetterInclusion (halfRows_le_ceilRows μ)) ∘ rowWord t := by
    funext i
    apply Fin.ext
    change (u (e.symm (Sum.inr i))).val.1 = (t i).val.1
    rw [alternateTableau_right]
  change polytabloid u = _
  rw [polytabloid_eq_altWord, hg, altWord_fiber_split, hl, hr, hw₁, hw₂,
    ← letterLift_altWord, ← letterLift_altWord, ← polytabloid_eq_altWord,
    ← polytabloid_eq_altWord]

lemma alternateRows_difference (μ : YoungDiagram) (k : ℕ)
    (hk : Odd (μ.rowLen k)) (he : ∀ i, i ≠ k → Even (μ.rowLen i)) (c : ℕ × ℕ) :
    c ∈ ceilRows μ ∧ c ∉ halfRows μ ↔ c = (k, μ.rowLen k / 2) := by
  rw [mem_ceilRows, mem_halfRows]
  constructor
  · rintro ⟨hc,hc'⟩
    have hck : c.1 = k := by
      by_contra hn
      obtain ⟨q,hq⟩ := he c.1 hn
      omega
    obtain ⟨q,hq⟩ := hk
    apply Prod.ext
    · exact hck
    · dsimp
      simp only [hck] at hc hc'
      omega
  · rintro rfl
    obtain ⟨q,hq⟩ := hk
    dsimp
    omega

lemma alternateRows_strip (μ : YoungDiagram) (k : ℕ)
    (hk : Odd (μ.rowLen k)) (he : ∀ i, i ≠ k → Even (μ.rowLen i)) :
    HorizontalStrip (halfRows μ) (ceilRows μ) := by
  refine ⟨halfRows_le_ceilRows μ, ?_⟩
  intro x hx hx' y hy hy' hxy
  exact ((alternateRows_difference μ k hk he x).mp ⟨hx,hx'⟩).trans
    ((alternateRows_difference μ k hk he y).mp ⟨hy,hy'⟩).symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_WeightedRestriction
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Restriction. -/

section

noncomputable section
namespace Saxl

lemma weightedRestrict_single {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (v : Fin e → ℂ) (c : Fin n → Fin e) (b : Fin a → Fin d) :
    weightedRestrict i j v (Pi.single c 1) b =
      if c ∘ i = j ∘ b then ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k)
      else 0 := by
  classical
  simp only [weightedRestrict, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' hc' hne
    rw [Pi.single_eq_of_ne hne]
    split_ifs <;> simp
  · simp

lemma weightedRestrict_equivariant {a n d e : ℕ} (i : Fin a ↪ Fin n)
    (j : Fin d ↪ Fin e) (v : Fin e → ℂ) (h : Equiv.Perm (Fin a)) (x : WordSpace n e) :
    weightedRestrict i j v (wordRep n e (h.viaEmbedding i) x) =
      wordRep a d h (weightedRestrict i j v x) := by
  classical
  let g := h.viaEmbedding i
  funext b
  change (∑ c : Fin n → Fin e,
    if c ∘ i = j ∘ b then x (c ∘ g) *
      ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k) else 0) =
    ∑ c : Fin n → Fin e,
      if c ∘ i = j ∘ (b ∘ h) then x c *
        ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k) else 0
  apply Eq.trans ?_ (Equiv.sum_comp (wordPerm n e g)
    (fun c => if c ∘ i = j ∘ (b ∘ h) then x c *
      ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k) else 0))
  apply Finset.sum_congr rfl
  intro c hc
  have he : c ∘ i = j ∘ b ↔ (c ∘ g) ∘ i = j ∘ (b ∘ h) := by
    constructor
    · intro hh
      funext k
      simpa only [Function.comp_apply, g, Equiv.Perm.viaEmbedding_apply] using congrFun hh (h k)
    · intro hh
      funext k
      have hh' := congrFun hh (h⁻¹ k)
      simpa [Function.comp_apply, g, Equiv.Perm.viaEmbedding_apply] using hh'
  change (if c ∘ i = j ∘ b then x (c ∘ g) *
    ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k) else 0) =
      if (c ∘ g) ∘ i = j ∘ (b ∘ h) then x (c ∘ g) *
        ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c (g k)) else 0
  by_cases hh : c ∘ i = j ∘ b
  · simp only [ite_eq_left hh, ite_eq_left (he.mp hh)]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem h i k (Finset.mem_filter.mp hk).2]
  · simp only [ite_eq_right hh, ite_eq_right (mt he.mpr hh)]

lemma weighted_strip_coefficient {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ)
    (v : Fin (μ.colLen 0) → ℂ) :
    weightedRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1) v
      (polytabloid t) (rowWord s) =
      ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range (tableauInclusion s t hs.1)),
        v (rowWord t k) := by
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
  change weightedRestrict i j v (∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0)
      (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1)) (rowWord s) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    wordRep_single, weightedRestrict_single, he]
  simp [i]
  rfl

lemma weighted_strip_pair {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ)
    (v : Fin (μ.colLen 0) → ℂ) :
    dotProduct (weightedRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1) v
      (polytabloid t)) (polytabloid s) =
      (Nat.card (columnGroup s) : ℂ) *
        ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range (tableauInclusion s t hs.1)),
          v (rowWord t k) := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  let x := weightedRestrict i j v (polytabloid t)
  have hx (g : columnGroup s) : wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a)) x =
      signC (g : Equiv.Perm (Fin a)) • x := by
    rw [← weightedRestrict_equivariant i j v (g : Equiv.Perm (Fin a)) (polytabloid t)]
    rw [polytabloid_alternating t ⟨_, column_viaEmbedding s t hs.1 g⟩]
    rw [map_smul, signC_viaEmbedding]
  rw [← columnAlt_coefficient]
  let := Fintype.ofFinite (columnGroup s)
  have he : columnAlt s x = (Fintype.card (columnGroup s) : ℂ) • x := by
    change (∑ g : columnGroup s, signC (g : Equiv.Perm (Fin a)) •
      wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a))) x = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul,
      signC_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  change columnAlt s x (rowWord s) = _
  rw [he]
  change (Fintype.card (columnGroup s) : ℂ) *
    weightedRestrict i j v (polytabloid t) (rowWord s) = _
  rw [weighted_strip_coefficient s t hs v, Fintype.card_eq_nat_card]

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

lemma letterLift_positionProduct {n a b d D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : Fin d → Fin D) (x : WordSpace a d) (y : WordSpace b d) :
    letterLift φ (positionProduct e x y) =
      positionProduct e (letterLift φ x) (letterLift φ y) :=
  wordMap_positionProduct e _ x y

lemma letterLift_comp {n a b c : ℕ} (φ : Fin a → Fin b) (ψ : Fin b → Fin c)
    (x : WordSpace n a) : letterLift ψ (letterLift φ x) = letterLift (ψ ∘ φ) x := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  rw [hx, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [map_smul, map_smul, map_smul, letterLift_single,
    letterLift_single, letterLift_single]
  rfl

lemma symmetricPartialPairs_lift_pair {n a b d D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i : Fin b ↪ Fin a)
    (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (v : Fin D → ℂ) (x : WordSpace n d) :
    dotProduct (letterLift φ x) (symmetricPartialPairs e i v) =
      dotProduct x (symmetricPartialPairs e i (v ∘ φ)) := by
  rw [letterLift_pair]
  congr 1
  funext w
  have hh : leftWord e (φ ∘ w) ∘ i = rightWord e (φ ∘ w) ↔
      leftWord e w ∘ i = rightWord e w := by
    constructor
    · intro h
      funext k
      exact hφ (congrFun h k)
    · intro h
      funext k
      exact congrArg φ (congrFun h k)
  simp only [symmetricPartialPairs, hh]
  rfl

lemma symmetricPartialPairs_contraction {n a b d D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i : Fin b ↪ Fin a)
    (j : Fin d ↪ Fin D) (v : Fin D → ℂ)
    (x : WordSpace a D) (y : WordSpace b d) :
    dotProduct (positionProduct e x (letterLift j y)) (symmetricPartialPairs e i v) =
      dotProduct (weightedRestrict i j v x) y := by
  classical
  calc
    _ = ∑ p : (Fin a → Fin D) × (Fin b → Fin D),
        x p.1 * letterLift j y p.2 *
          (if p.1 ∘ i = p.2 then
            ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (p.1 k) else 0) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro w
      rfl
    _ = dotProduct (letterLift j y) (fun r => ∑ l : Fin a → Fin D,
        if l ∘ i = r then x l *
          ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (l k) else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      split_ifs <;> ring
    _ = _ := by
      rw [letterLift_pair, dotProduct_comm]
      rfl

lemma alternateTableau_partialPair {n a b : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin a ⊕ Fin b) (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ))
    (hs : HorizontalStrip (halfRows μ) (ceilRows μ)) (v : Fin (μ.colLen 0) → ℂ) :
    dotProduct (polytabloid (alternateTableau μ e s t))
      (symmetricPartialPairs e (tableauInclusion t s hs.1) v) =
      (Nat.card (columnGroup t) : ℂ) *
        ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range (tableauInclusion t s hs.1)),
          v (Fin.cast (ceilRows_height μ) (rowWord s k)) := by
  rw [alternateTableau_factor, ← letterLift_comp, ← letterLift_positionProduct,
    symmetricPartialPairs_lift_pair _ _ _ (Fin.cast_injective _),
    symmetricPartialPairs_contraction, weighted_strip_pair t s hs]
  rfl

lemma tableauInclusion_range {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (k : Fin n) :
    k ∈ Set.range (tableauInclusion s t h) ↔ (t k).val ∈ ν := by
  constructor
  · rintro ⟨l,rfl⟩
    rw [tableauInclusion_cell]
    exact (s l).property
  · intro hk
    refine ⟨s.symm ⟨(t k).val,hk⟩, ?_⟩
    apply t.injective
    apply Subtype.ext
    rw [tableauInclusion_cell]
    simp

lemma alternateRows_card (μ : YoungDiagram) (k : ℕ)
    (hk : Odd (μ.rowLen k)) (he : ∀ i, i ≠ k → Even (μ.rowLen i)) :
    (ceilRows μ).card = (halfRows μ).card + 1 := by
  have hs : (halfRows μ).cells ⊆ (ceilRows μ).cells := halfRows_le_ceilRows μ
  have hd : (ceilRows μ).cells \ (halfRows μ).cells = {(k, μ.rowLen k / 2)} := by
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact alternateRows_difference μ k hk he c
  have hh := Finset.card_sdiff_add_card_eq_card hs
  rw [hd, Finset.card_singleton] at hh
  change 1 + (halfRows μ).card = (ceilRows μ).card at hh
  omega

lemma alternateTableau_partialPair_ne_zero {n a b : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin a ⊕ Fin b) (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ))
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ i, i ≠ k → Even (μ.rowLen i))
    (v : Fin (μ.colLen 0) → ℂ) (hv : v ⟨k, odd_row_lt_height hk⟩ ≠ 0) :
    dotProduct (polytabloid (alternateTableau μ e s t))
      (symmetricPartialPairs e (tableauInclusion t s (halfRows_le_ceilRows μ)) v) ≠ 0 := by
  rw [alternateTableau_partialPair μ e s t (alternateRows_strip μ k hk he)]
  apply mul_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  have hln : (s l).val ∉ halfRows μ :=
    mt (tableauInclusion_range t s (halfRows_le_ceilRows μ) l).mpr (Finset.mem_filter.mp hl).2
  have hcell := (alternateRows_difference μ k hk he (s l).val).mp ⟨(s l).property,hln⟩
  have hh : Fin.cast (ceilRows_height μ) (rowWord s l) = ⟨k, odd_row_lt_height hk⟩ :=
    Fin.ext (congrArg Prod.fst hcell)
  rwa [hh]

lemma symmetricPartialPairs_action {n a b d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i j : Fin b ↪ Fin a)
    (q : Equiv.Perm (Fin a)) (hq : ∀ k, q (i k) = j k) (v : Fin d → ℂ) :
    wordRep n d (sumPerm e q 1) (symmetricPartialPairs e i v) =
      symmetricPartialPairs e j v := by
  classical
  have hrange (k : Fin a) : q k ∈ Set.range j ↔ k ∈ Set.range i := by
    constructor
    · rintro ⟨l,hl⟩
      exact ⟨l, q.injective ((hq l).trans hl)⟩
    · rintro ⟨l,rfl⟩
      exact ⟨l,(hq l).symm⟩
  funext w
  have hl : leftWord e (w ∘ sumPerm e q 1) = leftWord e w ∘ q := by
    funext k
    simp [leftWord]
  have hr : rightWord e (w ∘ sumPerm e q 1) = rightWord e w := by
    funext k
    simp [rightWord]
  have hi : (leftWord e w ∘ q) ∘ i = leftWord e w ∘ j := by
    funext k
    simp only [Function.comp_apply, hq]
  change (if leftWord e (w ∘ sumPerm e q 1) ∘ i = rightWord e (w ∘ sumPerm e q 1)
    then _ else 0) = _
  simp only [hl,hr,hi,symmetricPartialPairs]
  congr 1
  simp only [Finset.prod_filter]
  apply Fintype.prod_equiv q
  intro k
  simp only [hrange, Function.comp_apply]

theorem one_odd_row_symmetricPartialPairs_support_oai {n m d : ℕ}
    (e : Fin n ≃ Fin (m+1) ⊕ Fin m) (i : Fin m ↪ Fin (m+1))
    (v : Fin d → ℂ) (hv : v ≠ 0)
    (μ : YoungDiagram) (t : Tableau n μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (symmetricPartialPairs e i v)).toRepresentation, F ≠ 0 := by
  classical
  have hn : μ.card = n := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have hnm : n = (m+1)+m := by
    simpa only [Fintype.card_fin, Fintype.card_sum] using Fintype.card_congr e
  have hc := alternateCells_card μ
  have hdif := alternateRows_card μ k hk he
  have hm : (halfRows μ).card = m := by omega
  have hM : (ceilRows μ).card = m+1 := by omega
  let s := canonicalTableau (ceilRows μ) hM
  let r := canonicalTableau (halfRows μ) hm
  let j := tableauInclusion r s (halfRows_le_ceilRows μ)
  let tt := alternateTableau μ e s r
  obtain ⟨a,ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra! hh
    exact hv (funext hh)
  let kk : Fin (μ.colLen 0) := ⟨k, odd_row_lt_height hk⟩
  let φ : Fin (μ.colLen 0) → Fin d :=
    (Equiv.swap (Fin.castLE hd kk) a) ∘ Fin.castLE hd
  have hφ : Function.Injective φ :=
    (Equiv.swap _ _).injective.comp (Fin.castLE_injective hd)
  have hφk : (v ∘ φ) kk ≠ 0 := by simpa [φ] using ha
  have hh : dotProduct (letterLift φ (polytabloid tt))
      (symmetricPartialPairs e j v) ≠ 0 := by
    rw [symmetricPartialPairs_lift_pair _ _ _ hφ]
    exact alternateTableau_partialPair_ne_zero μ e s r k hk he (v ∘ φ) hφk
  have hs := specht_to_cyclic_of_pair tt
    (fun a b => if φ a = b then 1 else 0) (symmetricPartialPairs e j v) hh
  obtain ⟨q,hq⟩ := Equiv.Perm.exists_extending_pair i j i.injective j.injective
  have hcyc : cyclic (wordRep n d) (symmetricPartialPairs e j v) =
      cyclic (wordRep n d) (symmetricPartialPairs e i v) := by
    rw [← symmetricPartialPairs_action e i j q hq v, cyclic_action_eq]
  change ∃ F : Representation.IntertwiningMap (spechtSub tt).toRepresentation
    (cyclic (wordRep n d) (symmetricPartialPairs e j v)).toRepresentation, F ≠ 0 at hs
  rw [spechtSub_tableau_independent tt t, hcyc] at hs
  exact hs

end Saxl
end
end

end OAI
end

theorem solution : type_of% @OAI.Saxl.one_odd_row_symmetricPartialPairs_support_oai := @OAI.Saxl.one_odd_row_symmetricPartialPairs_support_oai
