-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.exists_wall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:28.180323+00:00
-- url     : https://prove2.me/submissions/d7d63337-6cec-4b3a-a520-6fbd1ee4dfe3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {n : Type}
namespace GlobalTheory.IwahoriInj
theorem _root_.solution [Fintype n] {f F : n → n → ℤ} (hf : Chamber f) (hF : Chamber F) (hne : f ≠ F) :
    ∃ i j, i ≠ j ∧ f j i < F j i ∧ ∀ l, l ≠ i → l ≠ j → f j i < f j l + f l i := by
  classical
  let ht : n × n → ℤ := fun p => ∑ l, (f p.1 p.2 + f p.2 l - f p.1 l)
  have hpos : ∀ a b, a ≠ b → 0 < ht (a, b) := fun a b hab =>
    Finset.sum_pos' (fun l _ => by have := hf.1.2 a l b; simp only; omega)
      ⟨a, Finset.mem_univ _, by have := hf.2 a b hab; have := hf.1.1 a; simp only; omega⟩
  have hdiag : ∀ a b, f a b < F a b → a ≠ b := by
    rintro a _ h rfl
    rw [hf.1.1, hF.1.1] at h
    exact lt_irrefl _ h
  have hex : (Finset.univ.filter fun p : n × n => f p.1 p.2 < F p.1 p.2).Nonempty := by
    by_contra hc
    apply hne
    have hle : ∀ a b, F a b ≤ f a b := fun a b => by
      by_contra h
      exact hc ⟨(a, b), by simpa using h⟩
    funext a b
    by_cases hab : a = b
    · rw [hab, hf.1.1, hF.1.1]
    · have := hle a b; have := hle b a; have := hf.2 a b hab; have := hF.2 a b hab; omega
  obtain ⟨⟨j, i⟩, hp, hmin⟩ := Finset.exists_min_image _ ht hex
  have hp' : f j i < F j i := by simpa using hp
  refine ⟨i, j, (hdiag _ _ hp').symm, hp', fun l hli hlj => ?_⟩
  by_contra hc
  have he : f j i = f j l + f l i := le_antisymm (hf.1.2 _ _ _) (not_lt.1 hc)
  have hadd : ht (j, i) = ht (j, l) + ht (l, i) := by
    simp only [ht, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by omega
  have h1 := hpos j l hlj.symm
  have h2 := hpos l i hli
  have h3 := hF.1.2 j i l
  by_cases h : f j l < F j l
  · have := hmin (j, l) (by simpa using h); omega
  · have := hmin (l, i) (by simp; omega); omega
end GlobalTheory.IwahoriInj
