-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.inclHat_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:33.542874+00:00
-- url     : https://prove2.me/submissions/2787d1fb-10cb-4180-937c-a0f2ef340746

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution : (inclHat F E).IsIntegral := by
  letI := (inclHat F E).toAlgebra
  rintro ⟨z, hz⟩
  change IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (⟨z, hz⟩ : intHat F E)
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, _, ⟨s, rfl⟩, rfl⟩ := hx
    have h1 : IsIntegral ℤ (ratHat F E s) :=
      (RingOfIntegers.isIntegral s).map (ratHat F E).toIntAlgHom
    have h2 : IsIntegral (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (ratHat F E s) :=
      h1.tower_top
    have h3 := (isIntegral_algebraMap (A := intHat F E)
      (x := (fun v => ⟨a v, ha v⟩ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F))).mul h2
    refine Eq.mpr (congrArg (IsIntegral _) (Subtype.ext ?_)) h3
    change _ = (a ⊗ₜ[F] (1 : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E s))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | zero => exact isIntegral_zero
  | add x y _ _ h1 h2 => exact h1.add h2
  | neg x _ h => exact h.neg
end GlobalTheory.AdLat.RootNear
