-- Prove2me | solution 1 for OAI.Saxl.dominated_support_uts
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:13:26.656173+00:00
-- url     : https://prove2.me/submissions/7145ad8a-65c6-47d3-9ca6-4e2ed8275c1a

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_orbitAverage_base
import Theorems.Thm_OAI_Saxl_repeatedTarget_in_quotient_uts
import Theorems.Thm_OAI_Saxl_young_orbit_map_uts

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
-- module Solutions.OAIQ259_US.Saxl_SignEquivalence
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


theorem staircase_sign_equiv (m : ℕ) :
    Nonempty ((spechtRep (stairTableau m)).Equiv (signTwist (spechtRep (stairRowTableau m)))) := by
  classical
  let t := stairTableau m
  let tt := stairRowTableau m
  let y : Specht tt := ⟨polytabloid tt, mem_cyclic _ _⟩
  let R := signTwist (spechtRep tt)
  let F := orbitAverage R (rowWord t) y
  let c : ℂ := ((Finset.univ.filter
    (fun g : Equiv.Perm (Fin (staircase m).card) => rowWord t ∘ g = rowWord t)).card : ℂ)
  have hy : ∀ g : Equiv.Perm (Fin (staircase m).card), rowWord t ∘ g = rowWord t → R g y = y := by
    intro g hg
    have hc : g ∈ columnGroup tt := by
      intro i
      exact congrArg Fin.val (congrFun hg i)
    apply Subtype.ext
    change signC g • wordRep (staircase m).card ((staircase m).colLen 0) g (polytabloid tt) = polytabloid tt
    rw [polytabloid_alternating tt ⟨g, hc⟩, smul_smul, signC_mul_self, one_smul]
  have hF : F (Pi.single (rowWord t) 1) = c • y := orbitAverage_base R _ y hy
  have hc0 : c ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rfl
  have hm (g : columnGroup t) :
      (F (wordRep (staircase m).card ((staircase m).colLen 0) (g : Equiv.Perm (Fin (staircase m).card))
        (Pi.single (rowWord t) 1))).val (rowWord tt) = signC (g : Equiv.Perm (Fin (staircase m).card)) * c := by
    rw [F.isIntertwining, hF]
    change signC (g : Equiv.Perm (Fin (staircase m).card)) * (c *
      polytabloid tt (rowWord tt ∘ (g : Equiv.Perm (Fin (staircase m).card)))) = _
    have he : rowWord tt ∘ (g : Equiv.Perm (Fin (staircase m).card)) = rowWord tt := by
      funext i
      apply Fin.ext
      exact g.property i
    rw [he, polytabloid_rowWord, mul_one]
  let inc : Representation.IntertwiningMap (spechtRep t) (wordRep (staircase m).card ((staircase m).colLen 0)) :=
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
      change (F (∑ g : columnGroup t, signC (g : Equiv.Perm (Fin (staircase m).card)) •
        wordRep (staircase m).card ((staircase m).colLen 0) (g : Equiv.Perm (Fin (staircase m).card)) (Pi.single (rowWord t) 1))).val _ = _
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
-- module Solutions.OAIQ259_US.Saxl_DominatedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma colTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (colTruncate μ k).rowLen i = min k (μ.rowLen i) := by
  have hh : ∀ j, j < (colTruncate μ k).rowLen i ↔ j < min k (μ.rowLen i) := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i,j) ∈ (rowTruncate μ.transpose k).transpose ↔ _
    rw [YoungDiagram.mem_transpose]
    change (j,i) ∈ rowTruncate μ.transpose k ↔ _
    rw [mem_rowTruncate, YoungDiagram.mem_transpose]
    simp only [Prod.swap_prod_mk, YoungDiagram.mem_iff_lt_rowLen, lt_min_iff]
    omega
  have h₁ := hh ((colTruncate μ k).rowLen i)
  have h₂ := hh (min k (μ.rowLen i))
  omega

lemma colTruncate_height (μ : YoungDiagram) (k : ℕ) :
    (colTruncate μ k).colLen 0 ≤ μ.colLen 0 := by
  by_contra h
  have hm : (μ.colLen 0,0) ∈ colTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hm
  rw [colTruncate_rowLen, rowLen_zero_of_height_le μ le_rfl] at hr
  simp at hr

lemma sum_range_if_lt (f : ℕ → ℕ) {r H : ℕ} (hr : r ≤ H) :
    (∑ i ∈ Finset.range H, if i < r then f i else 0) = ∑ i ∈ Finset.range r, f i := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma corner_inequality (μ : YoungDiagram) (k r : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ r ≤ μ.card + r*k := by
  let H := max (μ.colLen 0) r
  have hh : μ.colLen 0 ≤ H := Nat.le_max_left _ _
  have hr : r ≤ H := Nat.le_max_right _ _
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ ((colTruncate_height μ k).trans hh)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  rw [hm, ← rowPrefix_eq_card μ hh]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) ≤ (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> omega

lemma corner_equality (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ (μ.colLen k) = μ.card + μ.colLen k*k := by
  let r := μ.colLen k
  let H := μ.colLen 0
  have hr : r ≤ H := μ.colLen_anti 0 k (Nat.zero_le _)
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ (colTruncate_height μ k)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  change rowPrefix μ.transpose k + rowPrefix μ r = μ.card + r*k
  rw [hm, ← rowPrefix_eq_card μ (le_refl H)]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) = (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have he : i < r ↔ k < μ.rowLen i := by
    exact YoungDiagram.mem_iff_lt_colLen.symm.trans YoungDiagram.mem_iff_lt_rowLen
  split_ifs with h
  · have hh := he.mp h
    omega
  · have hh := not_congr he |>.mp h
    omega

/- Ordinary conjugation reverses dominance, including empty diagrams. -/
theorem dominates_transpose {μ ν : YoungDiagram} (hc : μ.card = ν.card)
    (h : Dominates μ ν) : Dominates ν.transpose μ.transpose := by
  intro k
  have h₁ := corner_inequality μ k (ν.colLen k)
  have h₂ := corner_equality ν k
  have h₃ := h (ν.colLen k)
  omega

open scoped MonoidAlgebra

end Saxl

namespace Saxl

theorem dominated_support_uts_oai (m : ℕ) (_hm : 1 ≤ m) (μ : YoungDiagram)
    (t : Tableau (staircase m).card μ) (hμ : Dominates (staircase m) μ) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic m).toRepresentation, f ≠ 0 := by
  classical
  have hc : μ.card = (staircase m).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have ht : μ.transpose.card = (staircase m).card := by rw [transpose_card, hc]
  have hd : Dominates μ.transpose (staircase m) := by
    simpa only [staircase_transpose] using dominates_transpose hc.symm hμ
  have hw (j : Fin ((staircase m).colLen 0)) :
      (Finset.univ.filter (fun i => repeatedTarget m i = Fin.rev j)).card = (staircase m).rowLen j := by
    simpa only [repeatedTarget, Fin.rev_inj] using rowWord_content (stairTableau m) j
  obtain ⟨F,hF⟩ := young_orbit_map_uts (staircase m) μ.transpose (transposeTableau t)
    ht hd (repeatedTarget m) Fin.revPerm hw
  obtain ⟨φ⟩ := staircase_sign_equiv m
  let Q := F.comp (dominatedQuotient m φ)
  have hQ : Q ≠ 0 := by
    obtain ⟨x,hx⟩ := repeatedTarget_in_quotient_uts m φ
    intro hz
    apply hF
    have hh := congrArg (fun l => l x) hz
    change F (dominatedQuotient m φ x) = 0 at hh
    change dominatedQuotient m φ x = Pi.single (repeatedTarget m) 1 at hx
    rwa [hx] at hh
  obtain ⟨E⟩ := specht_sign_transpose t
  let R := E.symm.toIntertwiningMap.comp (signCancelMap Q)
  have hR : R ≠ 0 := by
    intro hz
    apply hQ
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun l => l x) hz
    change E.symm (Q x) = 0 at hh
    exact E.symm.injective (hh.trans (map_zero _).symm)
  let := specht_irreducible t
  have hRs : Function.Surjective R :=
    (Representation.IsIrreducible.surjective_or_eq_zero R).resolve_right hR
  obtain ⟨f,hf⟩ := intertwining_lift_surjective R hRs (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have hzero : (Representation.IntertwiningMap.id (spechtRep t)) = 0 := by
    rw [← hf, hz]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact map_zero R
  have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    l ⟨polytabloid t, mem_cyclic _ _⟩) hzero
  exact polytabloid_ne_zero t (congrArg Subtype.val he)

end Saxl

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.dominated_support_uts_oai := @OAI.Saxl.dominated_support_uts_oai
