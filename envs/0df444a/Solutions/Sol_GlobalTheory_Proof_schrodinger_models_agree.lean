-- Prove2me | solution 1 for GlobalTheory.Proof.schrodinger_models_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:08.648841+00:00
-- url     : https://prove2.me/submissions/de9017f3-fb09-4d3a-a5a0-079bc70072f7

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerProductEuclideanModelsAgree
import Theorems.Thm_GlobalTheory_Published_Metaplectic_rho_apply
import Theorems.Thm_GlobalTheory_RealWeil_coeFn_rho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
namespace GlobalTheory.Proof
theorem _root_.solution : ∀ (l : Type) [Fintype l] [DecidableEq l] (w : (l → ℝ) × (l → ℝ)) (φ : 𝓢(l → ℝ, ℂ)) (f f₁ : Sch l), (∀ x : EuclideanSpace ℝ l, f x = φ x.ofLp) → (∀ x : EuclideanSpace ℝ l, f₁ x = GlobalTheory.Published.Metaplectic.rho w φ x.ofLp) → f₁.toLp 2 = rho (Sum.elim w.1 w.2) (f.toLp 2) := by
  intro l _ _ w φ f f₁ hf hf₁
  obtain ⟨p, q⟩ := w
  have h : ⇑f₁ = rhoFun (Sum.elim p q) ⇑f := by
    funext x
    rw [hf₁, GlobalTheory.Published.Metaplectic.rho_apply, rhoFun, hf]
    simp only [phase, pPart, qPart, Sum.elim_inl, Sum.elim_inr, PiLp.inner_apply, WithLp.ofLp_add]
    congr 1
    · congr 1
      push_cast
      simp only [dotProduct, RCLike.inner_apply, conj_trivial, Finset.sum_div]
      push_cast
      ring_nf
      rw [Finset.sum_congr rfl fun i _ => mul_comm ((q i : ℝ) : ℂ) ((p i : ℝ) : ℂ)]
      ring
  refine Lp.ext ((f₁.coeFn_toLp 2 volume).trans ?_)
  rw [h]
  exact ((coeFn_rho _ _).trans (rhoFun_congr _ (f.coeFn_toLp 2 volume))).symm
end GlobalTheory.Proof
