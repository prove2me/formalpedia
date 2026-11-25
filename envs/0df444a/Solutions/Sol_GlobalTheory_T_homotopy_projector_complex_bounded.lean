-- Prove2me | solution 1 for GlobalTheory.T.homotopy_projector_complex_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:20.323847+00:00
-- url     : https://prove2.me/submissions/0df9f3c3-34d0-44cc-be88-84fde2de5275

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBoundedStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_PerfRetract_exists_finite_projective_model


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] (E : ℕ → Type) [∀ n, AddCommGroup (E n)]
    [∀ n, Module R (E n)] [∀ n, Module.Flat R (E n)] (d : ∀ n, E n →ₗ[R] E (n + 1))
    (_ : ∀ n, d (n + 1) ∘ₗ d n = 0) (e : ∀ n, E n →ₗ[R] E n) (h : ∀ n, E (n + 1) →ₗ[R] E n) (B : ℕ)
    (_ : ∀ n, e n ∘ₗ e n = e n) (_ : ∀ n, e (n + 1) ∘ₗ d n = d n ∘ₗ e n)
    (_ : e 0 = LinearMap.id + h 0 ∘ₗ d 0)
    (_ : ∀ n, e (n + 1) = LinearMap.id + d n ∘ₗ h n + h (n + 1) ∘ₗ d (n + 1))
    (_ : ∀ n, B < n → e n = 0)
    (_ : Module.Finite R (LinearMap.ker (d 0)))
    (_ : ∀ n, Module.Finite R (LinearMap.ker (d (n + 1)) ⧸
      (LinearMap.range (d n)).comap (LinearMap.ker (d (n + 1))).subtype)),
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℕ) (ψ : ∀ n, Q.X n →ₗ[R] E n),
      (∀ n, Module.Finite R (Q.X n)) ∧ (∀ n, Module.Projective R (Q.X n)) ∧
      (∀ n, ψ (n + 1) ∘ₗ (Q.d n (n + 1)).hom = d n ∘ₗ ψ n) ∧
      ∀ M : ModuleCat.{0} R,
        QIsoAt (0 : R →ₗ[R] M ⊗[R] Q.X 0) ((Q.d 0 1).hom.lTensor M) (0 : R →ₗ[R] M ⊗[R] E 0)
          ((d 0).lTensor M) ((ψ 0).lTensor M) ∧
        ∀ n, QIsoAt ((Q.d n (n + 1)).hom.lTensor M) ((Q.d (n + 1) (n + 2)).hom.lTensor M)
          ((d n).lTensor M) ((d (n + 1)).lTensor M) ((ψ (n + 1)).lTensor M) := by
  first | exact @GlobalTheory.CompanionTheory.PerfRetract.exists_finite_projective_model | exact GlobalTheory.CompanionTheory.PerfRetract.exists_finite_projective_model | (intros; apply GlobalTheory.CompanionTheory.PerfRetract.exists_finite_projective_model <;> assumption)
end _root_.GlobalTheory.T
