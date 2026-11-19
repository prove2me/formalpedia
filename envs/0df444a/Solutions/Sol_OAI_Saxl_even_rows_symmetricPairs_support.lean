-- Prove2me | solution 1 for OAI.Saxl.even_rows_symmetricPairs_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:07:28.953713+00:00
-- url     : https://prove2.me/submissions/b00f33ec-f883-435e-a916-2f8b300f3cfc

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

theorem even_rows_symmetricPairs_support_oai {n m d : ℕ}
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

theorem solution : type_of% @OAI.Saxl.even_rows_symmetricPairs_support_oai := @OAI.Saxl.even_rows_symmetricPairs_support_oai
