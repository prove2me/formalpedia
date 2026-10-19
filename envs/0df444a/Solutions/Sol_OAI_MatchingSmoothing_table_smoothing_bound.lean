-- Prove2me | solution 1 for OAI.MatchingSmoothing.table_smoothing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:19:59.401981+00:00
-- url     : https://prove2.me/submissions/20e89ef1-6ffa-449f-9f4c-eac3c97ff299

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/FiberAverages.lean:L87-L121
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.table_smoothing_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Theorems.Thm_OAI_MatchingSmoothing_conditionalAverage_energy
import Theorems.Thm_OAI_MatchingSmoothing_matching_table_trace_square
import Theorems.Thm_OAI_MatchingSmoothing_standardPairing_table
import Theorems.Thm_OAI_MatchingSmoothing_symmetric_matching_smoothing
import Theorems.Thm_OAI_MatchingSmoothing_threeTable_histogram_eq

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

-- ---- from OAI.Combinatorics.MatchingPSD.ColoringCounts ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace MatchingSmoothing

variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]

lemma permOfHistogram_spec {f g : α → β} (h : histogram f = histogram g)
    (a : α) : g (permOfHistogram h a) = f a := by
  exact (fiberEquivOfHistogram h (f a) ⟨a, rfl⟩).property

variable {H : Type u_5} [Fintype H] [DecidableEq H]

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.IncidenceKernels ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace MatchingSmoothing
open Matrix

section FiniteSums
variable {G : Type u_1} {X : Type u_2} [Fintype G] [Group G] [Fintype X] [MulAction G X]

end FiniteSums

section KernelTrace
variable {G : Type u_3} {X : Type u_4} [Fintype G] [Group G] [Fintype X] [DecidableEq X]
  [MulAction G X]

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

omit [DecidableEq X] [DecidableEq Z] in
lemma incidenceOperator_eq (P : X → Z → Prop) (D : ℝ) :
    incidenceOperator P D =
      ((Fintype.card Z : ℝ) / (D ^ 2 * Fintype.card X)) •
        ((incidence P).transpose * incidence P) := by
  ext x y
  simp only [incidenceOperator, incidenceKernel, commonIncidence_eq, Matrix.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply]
  ring

omit [DecidableEq X] [DecidableEq Z] in
lemma incidenceOperator_posSemidef (P : X → Z → Prop) (D : ℝ) :
    (incidenceOperator P D).PosSemidef := by
  rw [incidenceOperator_eq]
  apply Matrix.PosSemidef.smul
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (incidence P)
  · positivity

end Incidence
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingIncidence ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing
variable {V : Type u_1} [Fintype V] [DecidableEq V]

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

end MatchingIncidence
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.FiberAverages ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix
attribute [local instance] Classical.propDecidable
section FiberAverages
variable {X : Type u_1} {Z : Type u_2} [Fintype X] [Fintype Z]

lemma cardinal_fibers_balance (P : X → Z → Prop) (D E : ℕ)
    (hD : ∀ x, Fintype.card {z // P x z} = D)
    (hE : ∀ z, Fintype.card {x // P x z} = E) :
    Fintype.card X * D = Fintype.card Z * E := by
  classical
  calc
    _ = ∑ x : X, Fintype.card {z // P x z} := by simp [hD]
    _ = ∑ z : Z, Fintype.card {x // P x z} := by
      simp only [Fintype.card_subtype, Finset.card_filter]
      exact Finset.sum_comm
    _ = _ := by simp [hE]

end FiberAverages

section TableFibers
variable {H : Type u_3} [Fintype H] [DecidableEq H]

lemma table_row_card (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (M : Pairing (H × Bool)) :
    Fintype.card {z // tableRelation f₀ M z} =
      Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} := by
  classical
  obtain ⟨p, rfl⟩ := Pairing.exists_relabel (standardPairing (H := H)) M
  apply Fintype.card_congr
  refine ((coloringPerm (histogram f₀) p).subtypeEquiv
    (q := tableRelation f₀ standardPairing) (fun z => ?_)).trans ?_
  · change ((Pairing.relabel p standardPairing).table z.1 = _) ↔
      (standardPairing.table (z.1 ∘ p) = _)
    rw [Pairing.table_relabel]
  · refine { toFun := fun z => ⟨z.1.1, ?_⟩
             invFun := fun f => ⟨⟨f.1, threeTable_histogram_eq hH f.2⟩, ?_⟩
             left_inv := fun _ => rfl
             right_inv := fun _ => rfl }
    · simpa only [tableRelation, standardPairing_table] using z.2
    · simpa only [tableRelation, standardPairing_table] using f.2

omit [DecidableEq H] in
lemma table_col_card (f₀ : H × Bool → Fin 3)
    (z w : Colorings (H × Bool) (Fin 3) (histogram f₀)) :
    Fintype.card {M // tableRelation f₀ M z} =
      Fintype.card {M // tableRelation f₀ M w} := by
  classical
  let p := permOfHistogram (z.2.trans w.2.symm)
  have hp : w.1 ∘ p = z.1 := funext (permOfHistogram_spec _)
  apply Fintype.card_congr
  apply (Pairing.relabelEquiv p).subtypeEquiv
  intro M
  change (M.table z.1 = _) ↔ ((Pairing.relabel p M).table w.1 = _)
  rw [Pairing.table_relabel, hp]

lemma table_fiber_size (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (z : Colorings (H × Bool) (Fin 3) (histogram f₀)) :
    (Fintype.card {M // tableRelation f₀ M z} : ℝ) =
      (Fintype.card (Pairing (H × Bool)) : ℝ) *
        Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} /
        Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) := by
  classical
  have : Nonempty (Colorings (H × Bool) (Fin 3) (histogram f₀)) := ⟨⟨f₀, rfl⟩⟩
  have he := cardinal_fibers_balance (tableRelation f₀) _ _
    (table_row_card f₀ hH) (fun w => table_col_card f₀ w z)
  apply (eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  have hr : (Fintype.card (Pairing (H × Bool)) : ℝ) *
      Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} =
      Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) *
        Fintype.card {M // tableRelation f₀ M z} := by exact_mod_cast he
  rw [mul_comm]
  exact hr.symm

end TableFibers

open scoped RealInnerProductSpace
lemma table_smoothing_bound {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (f₀ : Vertices h → Fin 3) (hf₀ : ∀ i, 0 < histogram f₀ i)
    (a : ℝ) (ha : 0 ≤ a) (hHa : (h+1 : ℝ)^33 ≤ (h.choose k : ℝ) * a^2)
    (f : MatchingSpace h) (hf : f ∈ (polynomialSpace h ((4*k)*(4*k)))ᗮ) :
    (∑ z, fiberAverage (tableRelation f₀) (matchingEquiv h f) z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) ≤
    a * ((∑ M, (f M)^2) / Fintype.card (Pairing (Vertices h))) := by
  classical
  have hH : 0 < Fintype.card (Fin h) := by simpa using (show 0 < h by omega)
  have : Nonempty (Pairing (Vertices h)) := ⟨standardPairing⟩
  have : Nonempty (Colorings (Vertices h) (Fin 3) (histogram f₀)) := ⟨⟨f₀, rfl⟩⟩
  let D : ℝ := Fintype.card {f : Vertices h → Fin 3 // threeTable f = threeTable f₀}
  have hD : D ≠ 0 := by
    have : Nonempty {f : Vertices h → Fin 3 // threeTable f = threeTable f₀} := ⟨⟨f₀, rfl⟩⟩
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : (∑ z, fiberAverage (tableRelation f₀) (matchingEquiv h f) z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) =
      (∑ M, f M * (incidenceOperator (tableRelation f₀) D *ᵥ (matchingEquiv h f)) M) /
        Fintype.card (Pairing (Vertices h)) := by
    simp only [fiberAverage, table_fiber_size f₀ hH]
    exact conditionalAverage_energy _ D hD _
  rw [he]
  have hb := symmetric_matching_smoothing k hk (incidenceOperator (tableRelation f₀) D)
    (incidenceOperator_posSemidef _ _).isHermitian
    (fun p M N => by
      simp only [incidenceOperator, incidenceKernel, commonIncidence_table_relabel])
    ((h+1)^33) a ha (by simpa using matching_table_trace_square f₀ hH hf₀) hHa f hf
  rw [EuclideanSpace.real_norm_sq_eq] at hb
  have hinner : ⟪f, (incidenceOperator (tableRelation f₀) D).toEuclideanLin f⟫ =
      ∑ M, f M * (incidenceOperator (tableRelation f₀) D *ᵥ (matchingEquiv h f)) M := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact dotProduct_comm _ _
  rw [hinner] at hb
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb
    (show (0 : ℝ) ≤ Fintype.card (Pairing (Vertices h)) by positivity)

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open Matrix
attribute [local instance] Classical.propDecidable
open scoped RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.table_smoothing_bound := @_root_.OAI.MatchingSmoothing.table_smoothing_bound
