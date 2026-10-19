-- Prove2me | solution 1 for OAI.MatchingSmoothing.matching_table_trace_square
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:12:24.679993+00:00
-- url     : https://prove2.me/submissions/3a5c86b2-4c19-404b-a4a3-9398ded43834

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatchingIncidence.lean:L119-L144
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.matching_table_trace_square. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Theorems.Thm_OAI_MatchingSmoothing_standardPairing_table
import Theorems.Thm_OAI_MatchingSmoothing_threeTable_histogram_eq
import Theorems.Thm_OAI_MatchingSmoothing_three_table_kernel_moment

-- ---- from OAI.Combinatorics.MatchingPSD.Pairings ----
namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
namespace Pairing
variable {α : Type u_2}

lemma cycleType_eq [Fintype α] [DecidableEq α] (M N : Pairing α) :
    M.1.cycleType = N.1.cycleType := by
  have hm := Equiv.Perm.cycleType_of_pow_prime_eq_one M.partner_sq
  have hn := Equiv.Perm.cycleType_of_pow_prime_eq_one N.partner_sq
  have hsum (P : Pairing α) : P.1.cycleType.sum = Fintype.card α := by
    rw [Equiv.Perm.sum_cycleType]
    have hs : P.1.support = Finset.univ := by
      ext a
      simp [Equiv.Perm.mem_support, P.partner_ne]
    rw [hs, Finset.card_univ]
  have hc : M.1.cycleType.card = N.1.cycleType.card := by
    have he := (hsum M).trans (hsum N).symm
    rw [hm, hn] at he
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at he
    omega
  rw [hm, hn, hc]

lemma exists_relabel [Fintype α] [DecidableEq α] (M N : Pairing α) :
    ∃ p : Equiv.Perm α, relabel p M = N := by
  have h := Equiv.Perm.isConj_iff_cycleType_eq.mpr (cycleType_eq M N)
  rcases isConj_iff.mp h with ⟨p, hp⟩
  refine ⟨p, Subtype.ext ?_⟩
  exact hp

end Pairing
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.IncidenceKernels ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open Matrix

section FiniteSums
variable {G : Type u_1} {X : Type u_2} [Fintype G] [Group G] [Fintype X] [MulAction G X]

omit [Fintype G] in
lemma sum_smul_eq (g : G) (f : X → ℝ) : ∑ x, f (g • x) = ∑ x, f x :=
  Equiv.sum_comp (MulAction.toPerm g) f

omit [Fintype X] in
lemma sum_group_smul_eq (x₀ : X) (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (f : X → ℝ) (x : X) : ∑ g : G, f (g • x) = ∑ g : G, f (g • x₀) := by
  obtain ⟨h, rfl⟩ := ht x
  simp_rw [← mul_smul]
  exact Equiv.sum_comp (Equiv.mulRight h) (fun g => f (g • x₀))

lemma group_smul_sum_card (x₀ : X) (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (f : X → ℝ) :
    (Fintype.card G : ℝ) * ∑ x, f x =
      (Fintype.card X : ℝ) * ∑ g : G, f (g • x₀) := by
  calc
    _ = ∑ g : G, ∑ x, f (g • x) := by simp only [sum_smul_eq, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    _ = ∑ x, ∑ g : G, f (g • x) := Finset.sum_comm
    _ = _ := by simp_rw [sum_group_smul_eq x₀ ht, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]

omit [Fintype G] in
lemma invariant_kernel_sum (x₀ : X) (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (K : X → X → ℝ) (hK : ∀ (g : G) x y, K (g • x) (g • y) = K x y) :
    (∑ x, ∑ y, K x y) = (Fintype.card X : ℝ) * ∑ y, K x₀ y := by
  have he (x : X) : ∑ y, K x y = ∑ y, K x₀ y := by
    obtain ⟨g, rfl⟩ := ht x
    rw [← sum_smul_eq g (fun y => K (g • x₀) y)]
    simp_rw [hK]
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma invariant_kernel_double_sum_group (x₀ : X)
    (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (K : X → X → ℝ) (hK : ∀ (g : G) x y, K (g • x) (g • y) = K x y) :
    (Fintype.card G : ℝ) * (∑ x, ∑ y, K x y) =
      (Fintype.card X : ℝ) ^ 2 * ∑ g : G, K x₀ (g • x₀) := by
  rw [invariant_kernel_sum x₀ ht K hK]
  have h := group_smul_sum_card x₀ ht (K x₀)
  nlinarith [h]

end FiniteSums

section KernelTrace
variable {G : Type u_3} {X : Type u_4} [Fintype G] [Group G] [Fintype X] [DecidableEq X]
  [MulAction G X]

omit [DecidableEq X] in
lemma trace_normalized_kernel_sq (K : Matrix X X ℝ) (hs : ∀ x y, K x y = K y x) :
    Matrix.trace ((Matrix.of fun x y => K x y / Fintype.card X) *
      (Matrix.of fun x y => K x y / Fintype.card X)) =
      (∑ x, ∑ y, K x y ^ 2) / (Fintype.card X : ℝ) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [hs y x]
  ring

omit [DecidableEq X] in
lemma trace_normalized_invariant_kernel_sq (x₀ : X)
    (ht : ∀ x, ∃ g : G, g • x₀ = x)
    (K : Matrix X X ℝ) (hs : ∀ x y, K x y = K y x)
    (hi : ∀ (g : G) x y, K (g • x) (g • y) = K x y) :
    Matrix.trace ((Matrix.of fun x y => K x y / Fintype.card X) *
      (Matrix.of fun x y => K x y / Fintype.card X)) =
      (∑ g : G, K x₀ (g • x₀) ^ 2) / (Fintype.card G : ℝ) := by
  have : Nonempty X := ⟨x₀⟩
  rw [trace_normalized_kernel_sq K hs]
  have h := invariant_kernel_double_sum_group x₀ ht
    (fun x y => K x y ^ 2) (fun g x y => congrArg (fun a : ℝ => a ^ 2) (hi g x y))
  have hx : (Fintype.card X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hg : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  apply (div_eq_div_iff (pow_ne_zero _ hx) hg).mpr
  nlinarith [h]

end KernelTrace

section Incidence
variable {X : Type u_5} {Z : Type u_6} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma commonIncidence_eq (P : X → Z → Prop) (x y : X) :
    commonIncidence P x y = ∑ z, incidence P z x * incidence P z y := by
  classical
  simp only [commonIncidence, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hx : P x z <;> by_cases hy : P y z <;> simp [incidence, hx, hy]

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma commonIncidence_symm (P : X → Z → Prop) (x y : X) :
    commonIncidence P x y = commonIncidence P y x := by
  simp only [commonIncidence_eq, mul_comm]

omit [Fintype X] [DecidableEq X] [DecidableEq Z] in
lemma incidenceKernel_symm (P : X → Z → Prop) (D : ℝ) (x y : X) :
    incidenceKernel P D x y = incidenceKernel P D y x := by
  unfold incidenceKernel
  rw [commonIncidence_symm P x y]

end Incidence
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingIncidence ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing
variable {V : Type u_1} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma smul_eq_relabel (p : Equiv.Perm V) (M : Pairing V) : p • M = relabel p M := rfl

omit [DecidableEq V] in
lemma table_relabel (p : Equiv.Perm V) (M : Pairing V) (f : V → Fin 3) :
    (relabel p M).table f = M.table (f ∘ p) := by
  funext t
  unfold table
  congr 1
  have he : (fun v => threeEdgeType (f v, f ((relabel p M).1 v))) ∘ p =
      (fun v => threeEdgeType ((f ∘ p) v, (f ∘ p) (M.1 v))) := by
    funext v
    simp only [Function.comp_apply, relabel_apply]
    rw [Equiv.Perm.inv_def, p.symm_apply_apply]
  rw [← he, histogram_comp_perm]

end Pairing

section StandardTable
variable {H : Type u_2} [Fintype H] [DecidableEq H]

end StandardTable

section MatchingIncidence
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma commonIncidence_table_relabel (f₀ : H × Bool → Fin 3)
    (p : Equiv.Perm (H × Bool)) (M N : Pairing (H × Bool)) :
    commonIncidence (tableRelation f₀) (Pairing.relabel p M) (Pairing.relabel p N) =
      commonIncidence (tableRelation f₀) M N := by
  classical
  unfold commonIncidence
  congr 1
  apply Fintype.card_congr
  apply (coloringPerm (histogram f₀) p).subtypeEquiv
  intro z
  change ((Pairing.relabel p M).table z.1 = _ ∧ (Pairing.relabel p N).table z.1 = _) ↔
    (M.table (z.1 ∘ p) = _ ∧ N.table (z.1 ∘ p) = _)
  simp only [Pairing.table_relabel]

lemma commonIncidence_standard (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (p : Equiv.Perm (H × Bool)) :
    commonIncidence (tableRelation f₀) standardPairing (Pairing.relabel p standardPairing) =
      (Fintype.card {f : H × Bool → Fin 3 //
        threeTable f = threeTable f₀ ∧ threeTable (f ∘ p) = threeTable f₀} : ℝ) := by
  classical
  unfold commonIncidence
  congr 1
  apply Fintype.card_congr
  refine { toFun := fun z => ⟨z.1.1, ?_⟩
           invFun := fun f => ⟨⟨f.1, threeTable_histogram_eq hH f.2.1⟩, ?_⟩
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl }
  · simpa only [tableRelation, Pairing.table_relabel, standardPairing_table] using z.2
  · simpa only [tableRelation, Pairing.table_relabel, standardPairing_table] using f.2

lemma matching_table_trace_square (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf₀ : ∀ i, 0 < histogram f₀ i) :
    let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
    Matrix.trace (incidenceOperator (tableRelation f₀) D *
      incidenceOperator (tableRelation f₀) D) ≤ (Fintype.card H + 1 : ℝ) ^ 33 := by
  classical
  dsimp only
  let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
  change Matrix.trace (incidenceOperator (tableRelation f₀) D *
    incidenceOperator (tableRelation f₀) D) ≤ _
  have he := trace_normalized_invariant_kernel_sq (G := Equiv.Perm (H × Bool))
    (standardPairing (H := H)) (fun M => Pairing.exists_relabel _ M)
    (incidenceKernel (tableRelation f₀) D)
    (incidenceKernel_symm (tableRelation f₀) D)
    (fun p M N => by
      change (Fintype.card _ : ℝ) / D ^ 2 * commonIncidence _ (Pairing.relabel p M)
        (Pairing.relabel p N) = (Fintype.card _ : ℝ) / D ^ 2 * commonIncidence _ M N
      rw [commonIncidence_table_relabel])
  change Matrix.trace (incidenceOperator (tableRelation f₀) D *
    incidenceOperator (tableRelation f₀) D) = _ at he
  rw [he]
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (H × Bool)) := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hp).mpr
  simp only [incidenceKernel, Pairing.smul_eq_relabel,
    commonIncidence_standard f₀ hH]
  exact (three_table_kernel_moment f₀ hH hf₀).trans_eq (mul_comm _ _)

end MatchingIncidence
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.matching_table_trace_square := @_root_.OAI.MatchingSmoothing.matching_table_trace_square
