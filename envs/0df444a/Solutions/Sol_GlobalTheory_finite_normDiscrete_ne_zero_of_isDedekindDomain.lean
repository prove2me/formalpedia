-- Prove2me | solution 1 for GlobalTheory.finite_normDiscrete_ne_zero_of_isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:48.601719+00:00
-- url     : https://prove2.me/submissions/765f86fc-6011-408b-bdf2-838535a94bf4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteNormDiscreteNeZeroOfIsDedekindDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_eq_addv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S L : Type*} [CommRing S]
    [IsDedekindDomain S] [Field L] [Algebra S L] [IsFractionRing S L] (g : L) (hg : g ≠ 0) :
    {w : AddValuation L (WithTop ℤ) |
      IsNormDiscrete w ∧ (∀ s : S, 0 ≤ w (algebraMap S L s)) ∧ w g ≠ 0}.Finite := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap S L b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective S L (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hg
  have hI : Ideal.span {a * b} ≠ (⊥ : Ideal S) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero ha0 hb0
  refine ((Ideal.finite_factors hI).image (ValPl.addv L)).subset ?_
  rintro w ⟨hw, h0, hwg⟩
  let Q : Ideal S :=
    { carrier := {b | 0 < w (algebraMap S L b)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        exact lt_of_lt_of_le (lt_min ha hb) (w.map_add _ _)
      zero_mem' := by simp
      smul_mem' := fun c b hb => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢
        exact lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 c)) }
  have hz : ∀ s : S, s ∉ Q → w (algebraMap S L s) = 0 := fun s hs =>
    le_antisymm (not_lt.1 (hs : ¬ 0 < w (algebraMap S L s))) (h0 s)
  have hprime : Q.IsPrime := by
    refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : S) ∈ Q := htop ▸ Submodule.mem_top
      simp [Q] at h1
    · change 0 < w (algebraMap _ L (a * b)) at hab
      rw [map_mul, AddValuation.map_mul] at hab
      by_contra hno
      rw [not_or] at hno
      rw [hz a hno.1, hz b hno.2, add_zero] at hab
      exact lt_irrefl _ hab
  have hab : a * b ∈ Q := by
    by_contra hno
    have ha := hz a fun h => hno (Q.mul_mem_right _ h)
    have hb := hz b fun h => hno (Q.mul_mem_left _ h)
    have h := w.map_mul (algebraMap S L a / algebraMap S L b) (algebraMap S L b)
    rw [div_mul_cancel₀ _ hb1, ha, hb, add_zero] at h
    exact hwg h.symm
  have hne : Q ≠ ⊥ := fun h => mul_ne_zero ha0 hb0 (by rwa [h, Ideal.mem_bot] at hab)
  refine ⟨⟨Q, hprime, hne⟩, ?_, (ValPl.eq_addv _ w hw h0 (fun s => Iff.rfl)).symm⟩
  exact Ideal.dvd_span_singleton.mpr hab
end GlobalTheory
