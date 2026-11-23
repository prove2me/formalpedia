-- Prove2me | solution 1 for GlobalTheory.SW.Hyper.finrank_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:16.429257+00:00
-- url     : https://prove2.me/submissions/449ae396-5668-4fc8-9720-95dce80e879c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Hyper
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
namespace GlobalTheory.SW.Hyper
theorem _root_.solution (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have hlc := Module.isLocallyConstant_rankAtStalk (R := O) (M := M)
  let q0 : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  let p0 : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 : Module.finrank k (k ⊗[O] M) = Module.rankAtStalk (R := k) (k ⊗[O] M) q0 := by
    rw [Module.rankAtStalk_eq_finrank_of_free]; rfl
  have hp : p0.asIdeal.primeCompl ≤ nonZeroDivisors O := by
    intro x hx
    have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ Ideal.zero_mem _)
    exact mem_nonZeroDivisors_of_ne_zero hx0
  have h2 : Module.rankAtStalk (R := O) M p0 = Module.finrank O M := by
    rw [Module.rankAtStalk,
      IsLocalization.finrank_eq (Localization.AtPrime p0.asIdeal) p0.asIdeal.primeCompl hp,
      IsLocalizedModule.finrank_eq p0.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p0.asIdeal.primeCompl M) hp]
  rw [h1, Module.rankAtStalk_baseChange, hlc.apply_eq_of_preconnectedSpace _ p0, h2]
end GlobalTheory.SW.Hyper
