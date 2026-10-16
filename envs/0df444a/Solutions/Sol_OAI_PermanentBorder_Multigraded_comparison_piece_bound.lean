-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.comparison_piece_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:28:48.252411+00:00
-- url     : https://prove2.me/submissions/b586a5a1-c3a0-44c5-b96d-77e61f8cc6a8

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/LinearForms.lean:L285-L324
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.comparison_piece_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Theorems.Thm_OAI_PermanentBorder_Multigraded_component_finrank_le_one_of_linear_relations
import Theorems.Thm_OAI_PermanentBorder_Multigraded_component_finrank_zero_of_block_killed
import Theorems.Thm_OAI_PermanentBorder_Multigraded_finrank_le_splitBound

-- ---- from OAI.Algebra.Determinantal.Multigraded ----
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

lemma componentClosed_bot : ComponentClosed (K := K) w ⊥ := by
  intro p hp d
  have hp0 : p = 0 := hp
  simp [hp0]

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section Blocks
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

end Blocks
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearLeaves
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

end LinearLeaves
end PermanentBorder.Multigraded

end OAI

-- ---- from OAI.Algebra.Determinantal.LinearForms ----
namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearCoefficients
variable {K σ τ : Type*} [Field K] [Fintype τ]

lemma linearFormMap_single [DecidableEq τ] (v : τ → σ) (t : τ) :
    linearFormMap v (Pi.single t (1 : K)) = X (v t) := by
  classical
  simp [linearFormMap_apply, Pi.single_apply]

theorem linear_relations_of_codimension_le_one (v : τ → σ) (I : Ideal (MvPolynomial σ K))
    (h : Module.finrank K ((τ → K) ⧸ linearCoefficientSubspace v I) ≤ 1) :
    ∃ z : MvPolynomial σ K, ∃ c : τ → K, ∀ t, X (v t) - C (c t) * z ∈ I := by
  classical
  obtain ⟨a,ha⟩ := finrank_le_one_iff.mp h
  obtain ⟨b,rfl⟩ := Submodule.Quotient.mk_surjective (linearCoefficientSubspace v I) a
  choose c hc using fun t => ha (Submodule.Quotient.mk (Pi.single t (1 : K)))
  refine ⟨linearFormMap v b,c,fun t => ?_⟩
  have hmem : Pi.single t (1 : K) - c t • b ∈ linearCoefficientSubspace v I := by
    apply (Submodule.Quotient.eq (linearCoefficientSubspace v I)).mp
    simpa only [Submodule.Quotient.mk_smul] using (hc t).symm
  change linearFormMap v (Pi.single t 1 - c t • b) ∈ I at hmem
  simpa only [map_sub, map_smul, linearFormMap_single, smul_eq_C_mul] using hmem

theorem variables_mem_of_codimension_zero (v : τ → σ) (I : Ideal (MvPolynomial σ K))
    (h : Module.finrank K ((τ → K) ⧸ linearCoefficientSubspace v I) = 0) :
    ∀ t, X (v t) ∈ I := by
  classical
  intro t
  have hz : Submodule.Quotient.mk (Pi.single t (1 : K)) =
      (0 : (τ → K) ⧸ linearCoefficientSubspace v I) := by
    obtain ⟨c,hc,hq⟩ := Module.finrank_eq_zero_iff.mp h
      (Submodule.Quotient.mk (Pi.single t (1 : K)))
    exact (smul_eq_zero.mp hq).resolve_left hc
  have hm := (Submodule.Quotient.mk_eq_zero (linearCoefficientSubspace v I)).mp hz
  change linearFormMap v (Pi.single t (1 : K)) ∈ I at hm
  simpa only [linearFormMap_single] using hm

end LinearCoefficients

section Vandermonde
variable {K : Type*} [Field K]

lemma linearIndependent_rect_vandermonde {n N : ℕ} (hn : n ≤ N)
    (t : Fin n → K) (ht : Function.Injective t) :
    LinearIndependent K (fun i : Fin n => fun j : Fin N => t i ^ j.val) := by
  let f : (Fin N → K) →ₗ[K] Fin n → K :=
    LinearMap.funLeft K K (Fin.castLE hn)
  apply LinearIndependent.of_comp f
  exact Matrix.linearIndependent_rows_of_det_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr ht)

lemma linear_block_codimension_le {σ : Type*} {n N : ℕ} (hn : n ≤ N)
    (v : Fin N → σ) (I : Ideal (MvPolynomial σ K))
    (t : Fin n → K) (ht : Function.Injective t)
    (hforms : ∀ i, linearFormMap v (fun j => t i ^ j.val) ∈ I) :
    Module.finrank K ((Fin N → K) ⧸ linearCoefficientSubspace v I) + n ≤ N := by
  have hi := linearIndependent_rect_vandermonde hn t ht
  have hspan : Submodule.span K (Set.range (fun i : Fin n => fun j : Fin N => t i ^ j.val)) ≤
      linearCoefficientSubspace v I := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hforms i
  have hr := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hi, Fintype.card_fin] at hr
  have he := Submodule.finrank_quotient_add_finrank (linearCoefficientSubspace v I)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
  omega

end Vandermonde
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section VandermondeLeaves
variable {K ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype L]

omit [Fintype ι] in
lemma labeled_codimension (a : ι → ℕ) (g : L → ι) (t : L → K)
    (ht : Function.Injective t) (I : Ideal (MvPolynomial (BlockVariables a) K))
    (hforms : ∀ l, blockLinearForm a (g l) (t l) ∈ I)
    (j : ι) (n : ℕ) (hn : n ≤ a j+1) (hj : n ≤ Fintype.card {l // g l = j}) :
    Module.finrank K ((Fin (a j+1) → K) ⧸ linearCoefficientSubspace (blockVar a j) I) + n ≤ a j+1 := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin n)
    (β := {l // g l = j}) (by simpa using hj)
  apply linear_block_codimension_le hn (blockVar a j) I (fun i => t (e i).val)
    (ht.comp (Subtype.val_injective.comp e.injective))
  intro i
  have h := hforms (e i).val
  have hij : g (e i).val = j := (e i).property
  rw [hij] at h
  exact h

theorem labeled_leaf_bound (a : ι → ℕ) (g : L → ι) (t : L → K)
    (ht : Function.Injective t) (hcard : Fintype.card L = ∑ j, a j)
    (I : Ideal (MvPolynomial (BlockVariables a) K))
    (hforms : ∀ l, blockLinearForm a (g l) (t l) ∈ I)
    (d : ι → ℤ) (hd : ∀ j, 0 < d j) :
    Module.finrank K (componentQuotient (blockWeight (fun v : BlockVariables a => v.1)) I d) ≤
      if ∀ j, Fintype.card {l // g l = j} = a j then 1 else 0 := by
  classical
  split_ifs with hbalanced
  · have hj (j : ι) :
        Module.finrank K ((Fin (a j+1) → K) ⧸ linearCoefficientSubspace (blockVar a j) I) ≤ 1 := by
      have h := labeled_codimension a g t ht I hforms j (a j) (by omega) (by rw [hbalanced])
      omega
    choose z c hc using fun j => linear_relations_of_codimension_le_one (blockVar a j) I (hj j)
    exact component_finrank_le_one_of_linear_relations (fun v : BlockVariables a => v.1) I z
      (fun v => c v.1 v.2) (fun v => hc v.1 v.2) d
  · have hs : (∑ j, Fintype.card {l // g l = j}) = ∑ j, a j := by
      rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv g), hcard]
    have hex : ∃ j, a j < Fintype.card {l // g l = j} := by
      by_contra! hn
      apply hbalanced
      exact fun j => (Finset.sum_eq_sum_iff_of_le (fun j _ => hn j)).mp hs j (Finset.mem_univ j)
    obtain ⟨j,hj⟩ := hex
    have hdim := labeled_codimension a g t ht I hforms j (a j+1) le_rfl hj
    have hz := variables_mem_of_codimension_zero (blockVar a j) I (by omega)
    have hb : ∀ v : BlockVariables a, v.1 = j → X v ∈ I := by
      rintro ⟨i,v⟩ hv
      change i = j at hv
      subst i
      exact hz v
    exact (component_finrank_zero_of_block_killed (fun v : BlockVariables a => v.1) I j hb d (hd j)).le

end VandermondeLeaves
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BinaryChoices
variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

lemma splitBound_eq_choiceSum (qs : List (FactorPair (K := K) w))
    (I : Ideal (MvPolynomial σ K)) (d : G) :
    splitBound w I d qs = ∑ c : Fin qs.length → Bool,
      pieceDim w (I ⊔ choiceIdeal w qs c) (d-choiceShift w qs c) := by
  classical
  induction qs generalizing I d with
  | nil =>
    change pieceDim w I d = ∑ c : Fin 0 → Bool,
      pieceDim w (I ⊔ choiceIdeal w [] c) (d-choiceShift w [] c)
    simp only [choiceIdeal, choiceShift, sup_bot_eq, sub_zero]
    simp
  | cons q qs ih =>
    rw [splitBound, ih, ih]
    let f : (Fin (qs.length+1) → Bool) → ℕ := fun c =>
      pieceDim w (I ⊔ choiceIdeal w (q::qs) c) (d-choiceShift w (q::qs) c)
    have hs := (Fin.consEquiv (fun _ : Fin (qs.length+1) => Bool)).sum_comp f
    apply Eq.trans (b := ∑ p : Bool × (Fin qs.length → Bool), f (Fin.cons p.1 p.2)) _ hs
    simp only [f, Fintype.sum_prod_type, Fintype.sum_bool,
      choiceIdeal, choiceShift, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true,
      ite_false, ite_true, zero_add, ← sup_assoc]
    simp_rw [sub_add_eq_sub_sub]
    exact add_comm _ _

lemma choice_mem_choiceIdeal (qs : List (FactorPair (K := K) w))
    (c : Fin qs.length → Bool) (i : Fin qs.length) :
    (if c i then (qs.get i).right else (qs.get i).left) ∈ choiceIdeal w qs c := by
  induction qs with
  | nil => exact Fin.elim0 i
  | cons q qs ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    · exact Submodule.mem_sup_right (ih (fun j => c j.succ) i)

end BinaryChoices
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section MixedCoefficient
variable {ι E : Type*} [Fintype E] [DecidableEq ι]

lemma choiceCount_apply (g : E → ι) (j : ι) :
    choiceCount g j = Fintype.card {e // g e = j} := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter]
  simp only [choiceCount, Finsupp.finsetSum_apply, Finsupp.single_apply]

omit [DecidableEq ι] in
lemma mixedPolynomial_eq_choices [DecidableEq E] (u v : E → ι) :
    mixedPolynomial u v = ∑ c : E → Bool,
      monomial (choiceCount (fun e => if c e then v e else u e)) (1 : ℕ) := by
  classical
  have h := Fintype.prod_sum (fun e (b : Bool) =>
    if b then X (v e) else X (u e) : E → Bool → MvPolynomial ι ℕ)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false] at h
  rw [mixedPolynomial]
  simp_rw [add_comm] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  rw [choiceCount, monomial_sum_one]
  apply Finset.prod_congr rfl
  intro e _
  cases c e <;> rfl

lemma mixed_coefficient_eq_count [Fintype ι] [DecidableEq E] (u v : E → ι) (a : ι →₀ ℕ) :
    (mixedPolynomial u v).coeff a =
      ∑ c : E → Bool, if ∀ j,
        Fintype.card {e // (if c e then v e else u e) = j} = a j then 1 else 0 := by
  classical
  rw [mixedPolynomial_eq_choices, coeff_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [coeff_monomial]
  congr 1
  rw [Finsupp.ext_iff]
  simp only [choiceCount_apply]

end MixedCoefficient
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section ComparisonPieceBound
variable {K ι σ : Type*} [Field K] [DecidableEq ι]

omit [DecidableEq ι] in
lemma choiceShift_le_length (w : σ → (ι → ℤ))
    (qs : List (FactorPair (K := K) w)) (c : Fin qs.length → Bool)
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1) (j : ι) :
    choiceShift w qs c j ≤ (qs.length : ℤ) := by
  induction qs with
  | nil => simp [choiceShift]
  | cons q qs ih =>
    have hq := hdeg q (List.mem_cons_self) j
    have hs := ih (fun i => c i.succ) (fun q h => hdeg q (List.mem_cons_of_mem _ h))
    by_cases hc : c 0 = true
    · simpa [choiceShift, hc, add_comm] using add_le_add hq hs
    · simpa [choiceShift, hc] using hs.trans (show (qs.length : ℤ) ≤ qs.length + 1 by omega)

variable [Fintype ι]

theorem comparison_piece_bound (a : ι →₀ ℕ)
    (qs : List (FactorPair (K := K) (blockWeight (fun v : BlockVariables a => v.1))))
    (u v : Fin qs.length → ι) (t : (Fin qs.length × Bool) → K)
    (ht : Function.Injective t)
    (hleft : ∀ i, (qs.get i).left = blockLinearForm a (u i) (t (i,false)))
    (hright : ∀ i, (qs.get i).right = blockLinearForm a (v i) (t (i,true)))
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1)
    (hlen : qs.length = ∑ j, a j) (d : ι → ℤ) (hd : ∀ j, (qs.length : ℤ) < d j) :
    pieceDim (blockWeight (fun v : BlockVariables a => v.1))
      (productIdeal (blockWeight (fun v : BlockVariables a => v.1)) qs) d ≤
      (mixedPolynomial u v).coeff a := by
  classical
  let w := blockWeight (fun v : BlockVariables a => v.1)
  have hf := finrank_le_splitBound w qs ⊥ (componentClosed_bot w) d
  change pieceDim w (⊥ ⊔ productIdeal w qs) d ≤ splitBound w ⊥ d qs at hf
  rw [bot_sup_eq] at hf
  apply hf.trans
  rw [splitBound_eq_choiceSum, mixed_coefficient_eq_count]
  apply Finset.sum_le_sum
  intro c _
  simp only [bot_sup_eq]
  let g : Fin qs.length → ι := fun i => if c i then v i else u i
  let t' : Fin qs.length → K := fun i => t (i,c i)
  have ht' : Function.Injective t' := by
    intro i j hij
    exact congrArg Prod.fst (ht hij)
  have hforms (i : Fin qs.length) :
      blockLinearForm a (g i) (t' i) ∈ choiceIdeal w qs c := by
    have h := choice_mem_choiceIdeal w qs c i
    dsimp only [g,t']
    cases hc : c i
    · simpa only [hc, Bool.false_eq_true, ite_false, hleft i] using h
    · simpa only [hc, ite_true, hright i] using h
  have hp (j : ι) : 0 < (d-choiceShift w qs c) j := by
    have hb := choiceShift_le_length w qs c hdeg j
    have hh := hd j
    simp only [Pi.sub_apply]
    omega
  exact labeled_leaf_bound a g t' ht' (by simpa using hlen)
    (choiceIdeal w qs c) hforms (d-choiceShift w qs c) hp

end ComparisonPieceBound
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section HomogeneousIdealMap
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]
variable (w : σ → G) (e : E → G) (F : E → MvPolynomial σ K)
  (hF : ∀ i, (F i).IsWeightedHomogeneous w (e i))

end HomogeneousIdealMap

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
section AffineIndependent
variable {K E V : Type*} [Field K] [Fintype E]
  [AddCommGroup V] [Module K V]

end AffineIndependent
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.comparison_piece_bound := @_root_.OAI.PermanentBorder.Multigraded.comparison_piece_bound
