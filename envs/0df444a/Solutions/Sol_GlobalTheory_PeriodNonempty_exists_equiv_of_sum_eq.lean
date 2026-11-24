-- Prove2me | solution 1 for GlobalTheory.PeriodNonempty.exists_equiv_of_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:29:47.305242+00:00
-- url     : https://prove2.me/submissions/6d67299d-8927-4c03-9955-485b7cd5471e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_complex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField Matrix
open scoped TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodNonempty
noncomputable section
namespace GlobalTheory.PeriodNonempty
theorem _root_.solution {E : Type} [Field E] [NumberField E] {ι κ : Type} [Fintype ι] [Fintype κ]
    (s : ι → (E →+* ℂ)) (t : κ → (E →+* ℂ)) (h : ∀ a : 𝓞 E, ∑ i, s i (a : E) = ∑ k, t k (a : E)) :
    ∃ e : ι ≃ κ, ∀ i, t (e i) = s i := by
  classical
  let f : (E →+* ℂ) → (𝓞 E →* ℂ) := fun φ => (φ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hf : Function.Injective f := by
    intro φ ψ hφ
    apply (EigenSplit.isSplitting_complex E).injective
    ext a
    exact DFunLike.congr_fun hφ a
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp f hf
  have hs : ∀ {μ : Type} [Fintype μ] (u : μ → (E →+* ℂ)) (a : 𝓞 E),
      ∑ i, u i (a : E) = ∑ φ : E →+* ℂ, (Fintype.card {i // u i = φ} : ℂ) * φ (a : E) := by
    intro μ _ u a
    rw [← Finset.sum_fiberwise Finset.univ u]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => φ (a : E)) (fun i hi => by rw [(Finset.mem_filter.1 hi).2]),
      Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
  have hc := Fintype.linearIndependent_iff.1 hli
    (fun φ => (Fintype.card {i // s i = φ} : ℂ) - (Fintype.card {k // t k = φ} : ℂ)) (by
      funext a
      have := h a
      rw [hs s, hs t, ← sub_eq_zero, ← Finset.sum_sub_distrib] at this
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply, sub_mul]
      exact this)
  have hc' : ∀ φ, Fintype.card {i // s i = φ} = Fintype.card {k // t k = φ} := fun φ => by
    exact_mod_cast sub_eq_zero.1 (hc φ)
  exact ⟨Equiv.ofFiberEquiv fun φ => Fintype.equivOfCardEq (hc' φ), fun i => Equiv.ofFiberEquiv_map _ i⟩
end GlobalTheory.PeriodNonempty
