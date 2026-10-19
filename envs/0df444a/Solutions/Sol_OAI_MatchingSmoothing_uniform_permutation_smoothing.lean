-- Prove2me | solution 1 for OAI.MatchingSmoothing.uniform_permutation_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:34:35.731978+00:00
-- url     : https://prove2.me/submissions/995cccaf-53d6-40ee-947a-46a15c51b60a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PermutationSmoothing.lean:L102-L125
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.uniform_permutation_smoothing. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Theorems.Thm_OAI_MatchingSmoothing_card_colorings_mul_factorials
import Theorems.Thm_OAI_MatchingSmoothing_standardPairing_table
import Theorems.Thm_OAI_MatchingSmoothing_uniform_table_smoothing

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

lemma card_perm_color_fiber [DecidableEq α] [Fintype β] (f : α → β) (g : Colorings α β (histogram f)) :
    Fintype.card {σ : Equiv.Perm α // f ∘ σ = g.1} =
      ∏ b, (histogram f b).factorial := by
  classical
  rw [Fintype.card_congr (fiberPermEquiv f g.1), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro b _
  rw [Fintype.card_equiv (fiberEquivOfHistogram g.2 b)]
  exact congrArg Nat.factorial (congrFun g.2 b)

lemma sum_perm_comp [DecidableEq α] [Fintype β] (f : α → β) (φ : (α → β) → ℝ) :
    ∑ σ : Equiv.Perm α, φ (f ∘ σ) =
      (∏ b, ((histogram f b).factorial : ℝ)) *
        ∑ g : Colorings α β (histogram f), φ g.1 := by
  classical
  let F : Equiv.Perm α → Colorings α β (histogram f) :=
    fun σ => ⟨f ∘ σ, histogram_comp_perm f σ⟩
  rw [← Fintype.sum_fiberwise F (fun σ => φ (f ∘ σ)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  have he : ∀ σ : {σ // F σ = g}, φ (f ∘ σ.1) = φ g.1 := by
    intro σ
    exact congrArg φ (congrArg Subtype.val σ.2)
  simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  let e : {σ // F σ = g} ≃ {σ : Equiv.Perm α // f ∘ σ = g.1} :=
    Equiv.subtypeEquivRight (fun σ => Subtype.ext_iff)
  rw [Fintype.card_congr e, card_perm_color_fiber]
  simp

lemma mean_perm_comp [DecidableEq α] [Fintype β] (f : α → β) (φ : (α → β) → ℝ) :
    (Fintype.card (Colorings α β (histogram f)) : ℝ) *
      (∑ σ : Equiv.Perm α, φ (f ∘ σ)) =
    (Fintype.card (Equiv.Perm α) : ℝ) *
      ∑ g : Colorings α β (histogram f), φ g.1 := by
  rw [sum_perm_comp, ← mul_assoc]
  congr 1
  have h := card_colorings_mul_factorials f
  rw [Fintype.card_perm]
  exact_mod_cast h

variable {H : Type u_5} [Fintype H] [DecidableEq H]

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

end MatchingIncidence
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TablePolynomials ----
namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section PredicateAverage
variable {X : Type u_1} [Fintype X]

lemma predicateAverage_apply (P : X → Prop) (f : X → ℝ) :
    predicateAverage P f = (∑ x, if P x then f x else 0) / Fintype.card {x // P x} := by
  simp only [predicateAverage, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul,
    div_eq_mul_inv]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x <;> simp [hx]

end PredicateAverage
end MatchingSmoothing

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section ReynoldsAverage
variable {V : Type u_2} {C : Type u_3} [Fintype V]

end ReynoldsAverage

section TablePolynomial
variable {H : Type u_4} [Fintype H] [DecidableEq H]

end TablePolynomial
end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.PermutationSmoothing ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section Averages
variable {X : Type u_1} {Y : Type u_2} [Fintype X] [Fintype Y]
lemma predicateAverage_equiv (e : X ≃ Y) (P : X → Prop) (Q : Y → Prop)
    (he : ∀ x, P x ↔ Q (e x)) (f : Y → ℝ) :
    predicateAverage P (f ∘ e) = predicateAverage Q f := by
  classical
  have hc : Fintype.card {x // P x} = Fintype.card {y // Q y} :=
    Fintype.card_congr (e.subtypeEquiv he)
  rw [predicateAverage_apply, predicateAverage_apply, hc]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun x => by simp only [Function.comp_apply, he])

end Averages

lemma predicateAverage_relabel {V : Type u_3} [Fintype V] [DecidableEq V]
    (z : V → Fin 3) (t : Fin 6 → ℕ) (p : Equiv.Perm V) (f : Pairing V → ℝ) :
    predicateAverage (fun M => M.table z = t) (fun M => f (Pairing.relabel p M)) =
      predicateAverage (fun M => M.table (z ∘ p.symm) = t) f := by
  apply predicateAverage_equiv (Pairing.relabelEquiv p)
  intro M
  change M.table z = t ↔ (Pairing.relabel p M).table (z ∘ p.symm) = t
  rw [Pairing.table_relabel]
  have hz : (z ∘ p.symm) ∘ p = z := by funext a; simp
  rw [hz]

lemma expect_perm_colorings {V : Type u_4} {C : Type u_5} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (z : V → C) (φ : (V → C) → ℝ) :
    (𝔼 p : Equiv.Perm V, φ (z ∘ p)) =
      𝔼 w : Colorings V C (histogram z), φ w.1 := by
  have : Nonempty (Colorings V C (histogram z)) := ⟨⟨z,rfl⟩⟩
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  simpa only [mul_comm] using mean_perm_comp z φ

lemma fiberAverage_eq_predicateAverage {X : Type u_7} {Z : Type u_8} [Fintype X] [Fintype Z]
    (P : X → Z → Prop) (f : X → ℝ) (z : Z) :
    fiberAverage P f z = predicateAverage (fun x => P x z) f := by
  simp only [fiberAverage, conditionalAverage, incidence, predicateAverage_apply,
    ite_mul, one_mul, zero_mul]

lemma fiberEnergy_eq {h : ℕ} (f₀ : Vertices h → Fin 3)
    (f : Pairing (Vertices h) → ℝ) :
    (∑ z, fiberAverage (tableRelation f₀) f z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) =
    tableEnergy (histogram f₀) (threeTable f₀) f := by
  simp_rw [fiberAverage_eq_predicateAverage]
  rw [tableEnergy, Fintype.expect_eq_sum_div_card]
  rfl

lemma permutation_energy_eq {V : Type u_9} [Fintype V] [DecidableEq V]
    (z : V → Fin 3) (t : Fin 6 → ℕ) (f : Pairing V → ℝ) :
    (𝔼 p : Equiv.Perm V, (predicateAverage (fun M => M.table z = t)
      (fun M => f (Pairing.relabel p M)))^2) = tableEnergy (histogram z) t f := by
  simp_rw [predicateAverage_relabel]
  calc
    _ = 𝔼 p : Equiv.Perm V,
        (predicateAverage (fun M => M.table (z ∘ p) = t) f)^2 := by
      apply Fintype.expect_equiv (Equiv.inv (Equiv.Perm V))
      intro p
      rfl
    _ = _ := expect_perm_colorings z (fun w =>
      (predicateAverage (fun M => M.table w = t) f)^2)

lemma uniform_permutation_smoothing (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (z : Vertices h → Fin 3), (∀ i, 0 < histogram z i) →
      ∀ (M₀ : Pairing (Vertices h)) (f : Pairing (Vertices h) → ℝ),
      (𝔼 p : Equiv.Perm (Vertices h),
        (predicateAverage (fun M => M.table z = M₀.table z)
          (fun M => (f - lowProjection h d f) (Pairing.relabel p M)))^2) ≤
      ((2*h : ℝ)^(2*K))⁻¹ * (𝔼 M, (f M)^2) := by
  obtain ⟨d,H,hd,hbound⟩ := uniform_table_smoothing K
  refine ⟨d,H,hd,?_⟩
  intro h hh z hz M₀ f
  obtain ⟨p₀, hp₀⟩ := Pairing.exists_relabel (standardPairing (H := Fin h)) M₀
  let f₀ := z ∘ p₀
  have hhist : histogram f₀ = histogram z := histogram_comp_perm z p₀
  have ht : threeTable f₀ = M₀.table z := by
    rw [← hp₀, Pairing.table_relabel, standardPairing_table]
  have hb := hbound h hh f₀ (by simpa only [hhist] using hz) ((matchingEquiv h).symm f)
  have heg : matchingEquiv h ((matchingEquiv h).symm f -
      polynomialProjection h d ((matchingEquiv h).symm f)) = f - lowProjection h d f := by
    simp only [map_sub, LinearEquiv.apply_symm_apply]
    rfl
  rw [fiberEnergy_eq, heg, ht, hhist] at hb
  rw [permutation_energy_eq, Fintype.expect_eq_sum_div_card]
  exact hb

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.uniform_permutation_smoothing := @_root_.OAI.MatchingSmoothing.uniform_permutation_smoothing
