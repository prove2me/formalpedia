-- Prove2me | solution 1 for GlobalTheory.HermSign.realMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:03:04.625171+00:00
-- url     : https://prove2.me/submissions/888bcf07-f726-433a-aede-5c1cd2c83ad1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum
import Theorems.Thm_GlobalTheory_HermSign_induction_integers
import Theorems.Thm_GlobalTheory_HermSign_realMap_tmul
import Theorems.Thm_GlobalTheory_HermSign_realMap_realAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {r : ℕ}
  (Φ : CMType E) (φ : D.La →ₗ[𝓞 E] (Fin r → E))
namespace GlobalTheory.HermSign
theorem _root_.solution (hspan : Submodule.span E (Set.range φ) = ⊤) :
    Function.Surjective (realMap D Φ φ) := by
  classical
  have hst : ∀ c : Φ → ℂ, ∀ w ∈ LinearMap.range (realMap D Φ φ),
      c • w ∈ LinearMap.range (realMap D Φ φ) := by
    refine induction_integers Φ _ ?_ ?_ ?_
    · rintro a _ ⟨x, rfl⟩
      exact ⟨_, realMap_realAct D Φ φ a x⟩
    · intro c c' h h' w hw
      rw [add_smul]
      exact add_mem (h w hw) (h' w hw)
    · intro t c h w hw
      rw [smul_assoc]
      exact Submodule.smul_mem _ _ (h w hw)
  have hv : ∀ v : Fin r → E,
      (fun (τ : Φ) i => τ.1 (v i)) ∈ LinearMap.range (realMap D Φ φ) := by
    intro v
    have hv : v ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      exact ⟨1 ⊗ₜ x, by funext τ i; simp [realMap_tmul]⟩
    | zero => convert zero_mem (LinearMap.range (realMap D Φ φ)) using 1; funext τ i; simp
    | add x y _ _ hx hy => convert add_mem hx hy using 1; funext τ i; simp
    | smul b x _ hx => convert hst (fun τ => τ.1 b) _ hx using 1; funext τ i; simp
  intro u
  have : u = ∑ i, (fun τ => u τ i) • (fun (τ : Φ) j => τ.1 ((Pi.single i 1 : Fin r → E) j)) := by
    funext τ j
    simp [Finset.sum_apply, Pi.single_apply, apply_ite τ.1]
  rw [this]
  exact (LinearMap.range (realMap D Φ φ)).sum_mem fun i _ => hst _ _ (hv _)
end GlobalTheory.HermSign
