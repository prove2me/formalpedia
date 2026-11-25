-- Prove2me | solution 1 for GlobalTheory.SW.Model.expo_ofQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:16:36.631293+00:00
-- url     : https://prove2.me/submissions/ee5e2ac4-27ae-46f8-ac89-9dea49ca9455

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) {n N : ℕ} (m : Matrix (Fin n) (QI E N) ℚ) (Z : CM Ψ N N)
    (z z' : CM Ψ n N) :
    ∑ k, (qv (m k) ⬝ᵥ tauOf Ψ Z *ᵥ qv (m k) + 2 * (qv (m k) ⬝ᵥ zetaOf Ψ z z' k)) =
      2 * expo Ψ (ofQ m) Z z z' := by
  unfold expo
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set e : Ψ → Fin (Module.finrank ℚ E) → ℂ := fun τ j => τ.1 (Module.finBasis ℚ E j) with he
  have hx : ∀ (τ : Ψ) a, τ.1 (ofQ m k a) = ∑ j, (m k (a, j) : ℂ) * e τ j := fun τ a => by
    simp [ofQ, he, Rat.smul_def]
  have hq : ∀ τ : Ψ, (fun a => τ.1 (ofQ m k a)) ⬝ᵥ Z τ *ᵥ (fun a => conj (τ.1 (ofQ m k a))) =
      ∑ p : QI E N, ∑ q : QI E N, (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) := by
    intro τ
    simp only [hx, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum, map_ratCast]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring
  have hl : ∀ τ : Ψ, (fun a => τ.1 (ofQ m k a)) ⬝ᵥ z τ k + z' τ k ⬝ᵥ (fun a => conj (τ.1 (ofQ m k a))) =
      ∑ p : QI E N, (m k p : ℂ) * (e τ p.2 * z τ k p.1 + z' τ k p.1 * conj (e τ p.2)) := by
    intro τ
    simp only [hx, dotProduct, Fintype.sum_prod_type, map_sum, map_mul,
      Finset.sum_mul, Finset.mul_sum, map_ratCast, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [add_assoc, hq, hl]
  have h1 : qv (m k) ⬝ᵥ tauOf Ψ Z *ᵥ qv (m k) = 2 * ∑ τ : Ψ, ∑ p : QI E N, ∑ q : QI E N,
      (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) := by
    have s1 : ∑ τ : Ψ, ∑ p : QI E N, ∑ q : QI E N,
        (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) =
        ∑ p : QI E N, ∑ q : QI E N, ∑ τ : Ψ,
        (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    have s2 : ∑ p : QI E N, ∑ q : QI E N, ∑ τ : Ψ,
        (m k p : ℂ) * (e τ p.2 * Z τ p.1 q.1 * conj (e τ q.2) * m k q) =
        ∑ p : QI E N, ∑ q : QI E N, ∑ τ : Ψ,
        (m k p : ℂ) * (e τ q.2 * Z τ q.1 p.1 * conj (e τ p.2) * m k q) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring
    rw [two_mul, s1]
    nth_rewrite 2 [s2]
    simp only [dotProduct, Matrix.mulVec, tauOf, qv, Matrix.of_apply, Finset.sum_mul,
      Finset.mul_sum, add_mul, mul_add, Finset.sum_add_distrib, he]
  have h2 : qv (m k) ⬝ᵥ zetaOf Ψ z z' k = ∑ τ : Ψ, ∑ p : QI E N,
      (m k p : ℂ) * (e τ p.2 * z τ k p.1 + z' τ k p.1 * conj (e τ p.2)) := by
    simp only [dotProduct, zetaOf, qv, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [h1, h2, Finset.sum_add_distrib]
  ring
end GlobalTheory.SW.Model
