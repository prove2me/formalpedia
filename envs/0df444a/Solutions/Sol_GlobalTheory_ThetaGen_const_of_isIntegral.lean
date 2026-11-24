-- Prove2me | solution 1 for GlobalTheory.ThetaGen.const_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:25.266864+00:00
-- url     : https://prove2.me/submissions/aca952cf-d4f3-4cc9-a5e2-93970b405866

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaGen
theorem _root_.solution {ι : Type} (θ : ι → E → ℂ) {f : E → ℂ} (hf : Differentiable ℂ f)
    (hint : IsIntegral (Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2))
      (fun p : ℂ × E => p.1 ^ 0 * f p.2)) (z : E) : f z = f 0 := by
  set A := Algebra.adjoin ℂ (Set.range fun (c : ι) (p : ℂ × E) => p.1 * θ c p.2) with hA
  have hc : ∀ a ∈ A, ∀ x, a (0, x) = a (0, 0) := by
    intro a ha x
    induction ha using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; simp
    | algebraMap c => rfl
    | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]
    | mul x y _ _ hx hy => simp only [Pi.mul_apply, hx, hy]
  obtain ⟨P, hP, hP0⟩ := hint
  let φ : A →+* ℂ := (Pi.evalRingHom (fun _ : ℂ × E => ℂ) (0, 0)).comp (algebraMap A _)
  have hroot : ∀ x, (P.map φ).IsRoot (f x) := by
    intro x
    have h1 : (Pi.evalRingHom (fun _ : ℂ × E => ℂ) (0, x)).comp (algebraMap A _) = φ :=
      RingHom.ext fun a => hc a a.2 x
    have h2 := congrArg (Pi.evalRingHom (fun _ : ℂ × E => ℂ) (0, x)) hP0
    rw [Polynomial.hom_eval₂, h1] at h2
    rw [Polynomial.IsRoot, Polynomial.eval_map]
    simpa using h2
  refine hf.apply_eq_apply_of_bounded (Set.Finite.isBounded ?_) z 0
  refine (Polynomial.finite_setOf_isRoot (hP.map φ).ne_zero).subset ?_
  rintro _ ⟨x, rfl⟩
  exact hroot x
end GlobalTheory.ThetaGen
