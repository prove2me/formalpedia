-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.moved_of_not_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:45:02.48098+00:00
-- url     : https://prove2.me/submissions/d0c5a17a-f3ab-4f5e-90b1-d7219a7ffc77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_aut_eq
import Theorems.Thm_GlobalTheory_UnRep_Compare_conj_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    {P Q : Ideal (𝓞 E)} (hQ : Q.IsPrime)
    (h : P.comap (algebraMap (𝓞 F) (𝓞 E)) = Q.comap (algebraMap (𝓞 F) (𝓞 E))) (hPQ : ¬ P ≤ Q) :
    Moved c Q := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨a, haP, haQ⟩ := Set.not_subset.1 hPQ
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv c.toRingEquiv
  have hσ : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = c x := fun _ => rfl
  obtain ⟨m, hm⟩ : ((a * σ a : 𝓞 E) : E) ∈ Set.range (algebraMap F E) := by
    rw [IsGalois.mem_range_algebraMap_iff_fixed]
    intro f
    rcases aut_eq c h2 hc f with rfl | rfl
    · rfl
    · change f ((a : E) * f a) = (a : E) * f a
      rw [map_mul, conj_conj f h2 hc, mul_comm]
  have hint : IsIntegral ℤ m := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap F E).injective, hm]
    exact (a * σ a).2
  obtain ⟨m', hm'⟩ : ∃ m' : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) m' = a * σ a := ⟨⟨m, hint⟩, Subtype.ext hm⟩
  have h1 : a * σ a ∈ Q := by
    rw [← hm', ← Ideal.mem_comap, ← h, Ideal.mem_comap, hm']
    exact P.mul_mem_right _ haP
  exact ⟨σ a, (hQ.mem_or_mem h1).resolve_left haQ, a, (conj_conj c h2 hc _).symm, haQ⟩
end GlobalTheory.UnRep.Compare
