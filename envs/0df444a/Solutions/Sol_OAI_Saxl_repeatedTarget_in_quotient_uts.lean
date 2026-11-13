-- Prove2me | solution 1 for OAI.Saxl.repeatedTarget_in_quotient_uts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:11:08.66263+00:00
-- url     : https://prove2.me/submissions/f6511fd1-5cc5-4b00-af32-ebe626570f62

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007

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
-- module Solutions.OAIQ259_US.Saxl_RepeatedProjection
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/


lemma paired_relation_iff {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    (∀ i, (a (g.val i)).val + (a (h.val i)).val = (t i).val) ↔ h = ω*g := by
  constructor
  · intro hh
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply ha
    apply Prod.ext
    · exact (ht h i).trans ((ht ω (g.val i)).trans (ht g i)).symm
    · apply Fin.ext
      have he := hω (g.val i)
      rw [ht g i] at he
      exact Nat.add_left_cancel ((hh i).trans he.symm)
  · rintro rfl i
    have he := hω (g.val i)
    rw [ht g i] at he
    exact he

lemma paired_term_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) (g h : H) :
    orbitProjection t (pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1)) =
      if h = ω*g then Pi.single t 1 else 0 := by
  classical
  ext c
  change (if wordOrbit t c then pairSumMap n d e (Pi.single
      (mergeWords (a ∘ g.val) (a ∘ h.val)) 1) c else 0) = _
  rw [pairSumMap_single]
  simp only [Function.comp_apply]
  by_cases he : h = ω*g
  · rw [ite_eq_left he]
    have hr := (paired_relation_iff H a t ω ht ha hω g h).mpr he
    by_cases hc : c = t
    · subst c
      rw [ite_eq_left ⟨1, rfl⟩, ite_eq_left hr]
      simp
    · rw [Pi.single_eq_of_ne hc]
      have hn : ¬ ∀ i, (a (g.val i)).val + (a (h.val i)).val = (c i).val := by
        intro hh
        apply hc
        funext i
        exact Fin.ext ((hh i).symm.trans (hr i))
      simp only [hn, ite_false, if_false, ite_self]
  · rw [ite_eq_right he]
    change (if wordOrbit t c then _ else _) = (0:ℂ)
    by_cases ho : wordOrbit t c
    · rw [ite_eq_left ho]
      apply ite_eq_right
      intro hh
      obtain ⟨k,hk⟩ := ho
      have heq : (fun i => ((c i).val : ℝ)) = fun i => ((t i).val : ℝ) := by
        apply pair_sum_rigidity (fun i => ((a i).val : ℝ)) (fun i => ((t i).val : ℝ))
          (fun i => ((c i).val : ℝ)) ω.val g.val h.val k
        · intro i; rw [ht ω i]
        · intro i; exact_mod_cast hω i
        · intro i; rw [ht g i]
        · intro i; rw [ht h i]
        · intro i; exact_mod_cast (hh i).symm
        · intro i; rw [hk]; rfl
      have hct : c = t := by
        funext i
        apply Fin.ext
        exact_mod_cast congrFun heq i
      rw [hct] at hh
      exact he ((paired_relation_iff H a t ω ht ha hω g h).mp hh)
    · rw [ite_eq_right ho]

theorem repeated_alt_projection {n d e : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (a : Fin n → Fin d) (t : Fin n → Fin e) (ω : H)
    (ht : ∀ g : H, ∀ i, t (g.val i) = t i)
    (ha : Function.Injective (fun i => (t i, a i)))
    (hω : ∀ i, (a i).val + (a (ω.val i)).val = (t i).val) :
    orbitProjection t (pairSumMap n d e (wordTensor n d d
      (altWord H a ⊗ₜ[ℂ] altWord H a))) =
      ((Nat.card H : ℂ) * signC ω.val) • Pi.single t 1 := by
  classical
  let := Fintype.ofFinite H
  rw [altWord_inverse_sum, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum, TensorProduct.smul_tmul_smul, map_smul,
    wordTensor_single, paired_term_projection H a t ω ht ha hω]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  have hs (g : H) : signC g.val * signC (ω*g).val = signC ω.val := by
    simp only [Subgroup.coe_mul, map_mul]
    calc
      signC g.val * (signC ω.val * signC g.val) = signC ω.val * (signC g.val * signC g.val) := by ring
      _ = signC ω.val := by rw [signC_mul_self, mul_one]
  simp only [hs, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Fintype.card_eq_nat_card]

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

lemma repeatedTarget_fixed (m : ℕ) (g : columnGroup (stairRowTableau m)) (i) :
    repeatedTarget m (g.val i) = repeatedTarget m i := by
  apply congrArg Fin.rev
  apply Fin.ext
  exact g.property i

lemma repeated_letters_injective (m : ℕ) :
    Function.Injective (fun i => (repeatedTarget m i, rowWord (stairRowTableau m) i)) := by
  intro i j he
  apply (stairTableau m).injective
  apply Subtype.ext
  apply Prod.ext
  · have hh : Fin.rev (rowWord (stairTableau m) i) = Fin.rev (rowWord (stairTableau m) j) :=
      congrArg Prod.fst he
    exact congrArg Fin.val (Fin.rev_injective hh)
  · exact congrArg Fin.val (congrArg Prod.snd he)

lemma repeated_complement (m : ℕ) (i) :
    (rowWord (stairRowTableau m) i).val +
      (rowWord (stairRowTableau m) ((rowReversal m).val i)).val =
      (repeatedTarget m i).val := by
  have hi : (stairTableau m i).val.1 + (stairTableau m i).val.2 < m :=
    mem_staircase.mp (stairTableau m i).property
  simp only [rowWord, stairRowTableau, rowReversal, Equiv.trans_apply,
    Equiv.apply_symm_apply, repeatedTarget, Fin.val_rev, staircase_colLen, Nat.sub_zero]
  change (stairTableau m i).val.2 + (m-1-(stairTableau m i).val.1-(stairTableau m i).val.2) =
    m-((stairTableau m i).val.1+1)
  omega

theorem staircase_repeated_projection (m : ℕ) :
    orbitProjection (repeatedTarget m)
      (pairSumMap (staircase m).card ((staircase m).colLen 0) ((staircase m).colLen 0)
        (wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairRowTableau m)))) =
      ((Nat.card (columnGroup (stairRowTableau m)) : ℂ) * signC (rowReversal m).val) •
        Pi.single (repeatedTarget m) 1 := by
  exact repeated_alt_projection (columnGroup (stairRowTableau m))
    (rowWord (stairRowTableau m)) (repeatedTarget m) (rowReversal m)
    (repeatedTarget_fixed m) (repeated_letters_injective m) (repeated_complement m)

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

lemma rowAverage_nonzero (m : ℕ) : rowAverage m ≠ 0 := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  intro he
  have hh := congrArg (fun y : Specht (stairTableau m) => y.val (rowWord (stairTableau m))) he
  have hg (g : columnGroup (stairRowTableau m)) :
      rowWord (stairTableau m) ∘ g.val = rowWord (stairTableau m) := by
    funext i
    apply Fin.ext
    exact g.property i
  simp only [rowAverage, Submodule.coe_sum, Finset.sum_apply] at hh
  change (∑ g : columnGroup (stairRowTableau m),
    polytabloid (stairTableau m) (rowWord (stairTableau m) ∘ g.val)) = 0 at hh
  simp only [hg, polytabloid_rowWord, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero hh

lemma rowAverage_fixed (m : ℕ) (g : columnGroup (stairRowTableau m)) :
    spechtRep (stairTableau m) g.val (rowAverage m) = rowAverage m := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  unfold rowAverage
  rw [map_sum]
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : columnGroup (stairRowTableau m) =>
    spechtRep (stairTableau m) h.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩)

lemma signEquiv_rowAverage (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (rowAverage m)).val = c • polytabloid (stairRowTableau m) := by
  have ha (g : columnGroup (stairRowTableau m)) :
      spechtRep (stairRowTableau m) g.val (φ (rowAverage m)) = signC g.val • φ (rowAverage m) := by
    have he := LinearMap.congr_fun (φ.isIntertwining' g.val) (rowAverage m)
    change φ (spechtRep (stairTableau m) g.val (rowAverage m)) =
      signC g.val • spechtRep (stairRowTableau m) g.val (φ (rowAverage m)) at he
    rw [rowAverage_fixed] at he
    have hh := congrArg (fun x => signC g.val • x) he
    simpa only [smul_smul, signC_mul_self, one_smul] using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (stairRowTableau m) (φ (rowAverage m)) ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply rowAverage_nonzero m
  apply φ.injective
  exact (Subtype.ext hc).trans (map_zero φ).symm

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

lemma ambientSignMap_subtype (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m))))
    (x : Specht (stairTableau m)) : ambientSignMap m φ x.val = (φ x).val := by
  change (φ (subrepProject (spechtSub (stairTableau m)) _ x.val)).val = _
  exact congrArg (fun y : Specht (stairTableau m) => (φ y).val)
    (subrepProject_subtype (spechtSub (stairTableau m)) _ x)

lemma pairAntiMap_tensor (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m))))
    (x y : WordSpace (staircase m).card ((staircase m).colLen 0)) :
    pairAntiMap m φ (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) =
      wordTensor _ _ _ (x ⊗ₜ[ℂ] ambientSignMap m φ y) := by
  change wordTensor _ _ _ (TensorProduct.map LinearMap.id (ambientSignMap m φ).toLinearMap
    ((wordTensor _ _ _).symm (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rfl

lemma signed_average_staircase (m : ℕ) :
    letI := Fintype.ofFinite (columnGroup (stairRowTableau m))
    ∑ g : columnGroup (stairRowTableau m), signC g.val •
      wordRep (staircase m).card ((staircase m).colLen 0 * (staircase m).colLen 0) g.val (staircaseWord m) =
    wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] (rowAverage m).val) := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  change _ = wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ]
    (∑ g : columnGroup (stairRowTableau m),
      spechtRep (stairTableau m) g.val ⟨polytabloid (stairTableau m), mem_cyclic _ _⟩).val)
  rw [Submodule.coe_sum, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  change signC g.val • wordRep _ _ g.val (wordTensor _ _ _
    (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] polytabloid (stairTableau m))) = _
  rw [← wordTensor_equivariant]
  change signC g.val • wordTensor _ _ _
    (wordRep _ _ g.val (polytabloid (stairRowTableau m)) ⊗ₜ[ℂ]
      wordRep _ _ g.val (polytabloid (stairTableau m))) = _
  rw [polytabloid_alternating _ g, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
    smul_smul, signC_mul_self, one_smul]
  rfl

theorem repeatedTarget_in_quotient_uts_oai (m : ℕ)
    (φ : (spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) :
    Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range := by
  classical
  let := Fintype.ofFinite (columnGroup (stairRowTableau m))
  obtain ⟨c,hc,hφ⟩ := signEquiv_rowAverage m φ
  let x : (staircaseCyclic m).toSubmodule := ∑ g : columnGroup (stairRowTableau m), signC g.val •
    (staircaseCyclic m).toRepresentation g.val ⟨staircaseWord m, mem_cyclic _ _⟩
  have hx : x.val = wordTensor _ _ _ (polytabloid (stairRowTableau m) ⊗ₜ[ℂ] (rowAverage m).val) := by
    change (∑ g : columnGroup (stairRowTableau m), signC g.val •
      (staircaseCyclic m).toRepresentation g.val ⟨staircaseWord m, mem_cyclic _ _⟩).val = _
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
    exact signed_average_staircase m
  let q : ℂ := (Nat.card (columnGroup (stairRowTableau m)) : ℂ) * signC (rowReversal m).val
  have hq : q ≠ 0 := by
    apply mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := columnGroup (stairRowTableau m))).ne')
    intro hz
    have hh := signC_mul_self (rowReversal m).val
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hF : dominatedQuotient m φ x = (c*q) • Pi.single (repeatedTarget m) (1:ℂ) := by
    change orbitProjection (repeatedTarget m) (pairSumMap _ _ _ (pairAntiMap m φ x.val)) = _
    rw [hx, pairAntiMap_tensor, ambientSignMap_subtype, hφ,
      TensorProduct.tmul_smul, map_smul, map_smul, map_smul, staircase_repeated_projection, smul_smul]
  have hm : (c*q) • Pi.single (repeatedTarget m) (1:ℂ) ∈ (dominatedQuotient m φ).range :=
    ⟨x,hF⟩
  exact (Submodule.smul_mem_iff _ (mul_ne_zero hc hq)).mp hm

end Saxl

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.repeatedTarget_in_quotient_uts_oai := @OAI.Saxl.repeatedTarget_in_quotient_uts_oai
