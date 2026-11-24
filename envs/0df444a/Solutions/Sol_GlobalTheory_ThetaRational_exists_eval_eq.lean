-- Prove2me | solution 1 for GlobalTheory.ThetaRational.exists_eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:33:06.307494+00:00
-- url     : https://prove2.me/submissions/b51f4ed2-f3da-44d2-a4bf-ee0966cddd9c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]
omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]
namespace GlobalTheory.ThetaRational
theorem _root_.solution {u : ι → E → ℂ}
    (hcl : ∀ y : ι → ℂ, (∀ F : MvPolynomial ι ℂ, (∀ e, MvPolynomial.eval (fun c => u c e) F = 0) →
      MvPolynomial.eval y F = 0) → ∃ e, y = fun c => u c e)
    (χ : Algebra.adjoin ℂ (Set.range u) →ₐ[ℂ] ℂ) : ∃ e, ∀ b, χ b = b.1 e := by
  set g : ι → Algebra.adjoin ℂ (Set.range u) := fun c => ⟨u c, Algebra.subset_adjoin ⟨c, rfl⟩⟩
    with hg
  obtain ⟨e, he⟩ := hcl (fun c => χ (g c)) fun F hF => by
    have h1 : MvPolynomial.aeval g F = 0 := by
      refine Subtype.ext (funext fun e => ?_)
      have := (fun φ g F => (MvPolynomial.comp_aeval_apply (R := ℂ) g φ F).symm)
        ((Pi.evalAlgHom ℂ (fun _ : E => ℂ) e).comp (Algebra.adjoin ℂ (Set.range u)).val) g F
      exact this.symm.trans (hF e)
    have := (fun φ g F => (MvPolynomial.comp_aeval_apply (R := ℂ) g φ F).symm) χ g F
    rw [h1, map_zero] at this
    exact this
  refine ⟨e, fun ⟨b, hb⟩ => ?_⟩
  induction hb using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨c, rfl⟩ := hx; exact congrFun he c
  | algebraMap r => exact χ.commutes r
  | add x y hx' hy' hx hy => exact (map_add χ ⟨x, hx'⟩ ⟨y, hy'⟩).trans (by rw [hx, hy])
  | mul x y hx' hy' hx hy => exact (map_mul χ ⟨x, hx'⟩ ⟨y, hy'⟩).trans (by rw [hx, hy])
end GlobalTheory.ThetaRational
