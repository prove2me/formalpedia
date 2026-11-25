-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.PolyFn.vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:21:08.506255+00:00
-- url     : https://prove2.me/submissions/471491b3-da6b-413d-8a6b-b750b433c5c0

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_PolF_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet qminor Tm)
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
namespace PolyFn
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] {F : ℂ → Module.End ℂ V}
    (hF : PolyFn F) (u₀ : ℂ) (h : ∀ u, u ≠ u₀ → F u = 0) : F u₀ = 0 := by
  obtain ⟨p, hp⟩ := hF
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  have key : ∀ p : Polynomial (Module.End ℂ V), ∃ q : Polynomial ℂ,
      ∀ u, φ ((p.eval (algebraMap ℂ _ u)) v) = q.eval u := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, fun u => by simp [ha, hb]⟩
    | monomial k T =>
      refine ⟨Polynomial.monomial k (φ (T v)), fun u => ?_⟩
      simp only [Polynomial.eval_monomial, ← map_pow, Module.End.mul_apply,
        Module.algebraMap_end_apply, map_smul, smul_eq_mul]
      ring
  obtain ⟨q, hq⟩ := key p
  have hq0 : q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot q
      (((Set.finite_singleton u₀).infinite_compl).mono fun u hu => ?_)
    have e := hq u
    rw [← hp, h u hu] at e
    simpa [Polynomial.IsRoot.def] using e.symm
  rw [hp, hq, hq0]
  simp
end PolyFn
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
