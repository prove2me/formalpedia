-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Red.prod_sq_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:52.497276+00:00
-- url     : https://prove2.me/submissions/58dc808d-8d6b-4d02-8bca-465b883904f0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsCuspReductionBoundStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MobiusActionUpperHalfPlaneStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFiniteStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitBalancingImaginaryPartsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ReductionToSiegelDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Red
namespace GlobalTheory.CompanionTheory.SW.Red
theorem _root_.solution {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F)
    (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (x : F) :
    ∏ w, (ρ w x) ^ 2 = ((Algebra.norm ℚ x : ℚ) : ℝ) ^ 2 := by
  have h1 := InfinitePlace.prod_eq_abs_norm x
  have h2 : ∀ w : InfinitePlace F, w x ^ w.mult = |ρ w x| := by
    intro w
    have hm : w.mult = 1 := by
      simp [InfinitePlace.mult, hF.isReal w]
    rw [hm, pow_one, ← InfinitePlace.norm_embedding_eq, ← hρ]
    simp
  have h3 : ∏ w : InfinitePlace F, |ρ w x| = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    rw [← Finset.prod_congr rfl (fun w _ => h2 w), h1]
    simp
  calc ∏ w, (ρ w x) ^ 2 = ∏ w, |ρ w x| ^ 2 := by simp
    _ = (∏ w, |ρ w x|) ^ 2 := by rw [Finset.prod_pow]
    _ = _ := by rw [h3, sq_abs]
end GlobalTheory.CompanionTheory.SW.Red
