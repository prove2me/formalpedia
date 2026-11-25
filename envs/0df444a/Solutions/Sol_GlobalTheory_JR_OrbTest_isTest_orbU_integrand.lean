-- Prove2me | solution 1 for GlobalTheory.JR.OrbTest.isTest_orbU_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:03:28.422288+00:00
-- url     : https://prove2.me/submissions/fa9ee0e4-20cc-420e-9da7-91cb3e2e8ac8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProperStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCo
import Theorems.Thm_GlobalTheory_JR_OrbTest_actU_mul
import Theorems.Thm_GlobalTheory_JR_OrbTest_continuous_actU
import Theorems.Thm_GlobalTheory_JR_OrbProper_continuous_actU
import Theorems.Thm_GlobalTheory_T_invariant_image_openClosed_local_sections
import Theorems.Thm_GlobalTheory_T_unitary_action_hermitian_invariants_transitive


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbTest
namespace GlobalTheory.JR.OrbTest
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (f : Hn r F E → ℂ) (hf : IsTest f) (a : Inv r F)
    (X : Hn r F E) (ha : Delta a ≠ 0) (hX : HasInv X a) :
    IsTest (fun g : Matrix.unitaryGroup (Fin r) E => f (actU g X)) := by
  haveI : ContinuousStar E := ⟨by
    have : Continuous (starAddEquiv : E ≃+ E) :=
      AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1
        (fun x => by rw [starAddEquiv_apply, Unram.norm_star (F := F), one_mul])
    exact this⟩
  obtain ⟨-, -, hL5c, -⟩ := GlobalTheory.T.unitary_action_hermitian_invariants_transitive F E r
  obtain ⟨-, hL5iv⟩ := GlobalTheory.T.invariant_image_openClosed_local_sections F E r a ha
  obtain ⟨Ω, s, -, -, haΩ, -, hs, hprop⟩ := hL5iv ⟨X, hX⟩
  obtain ⟨g₀, hg₀, -⟩ := hL5c (s a) X a ha (hs a haΩ).2 hX
  refine ⟨hf.1.comp_continuous (continuous_actU X), ?_⟩
  have hS : IsCompact {h : Matrix.unitaryGroup (Fin r) E | actU h (s a) ∈ tsupport f} := by
    have h1 := (hprop (tsupport f) hf.2).inter_right (isClosed_univ.prod (isClosed_singleton (x := a)))
    convert h1.image continuous_fst using 1
    ext h; constructor
    · intro hh; exact ⟨(h, a), ⟨⟨haΩ, hh⟩, Set.mem_univ _, rfl⟩, rfl⟩
    · rintro ⟨⟨h', a'⟩, ⟨⟨-, hc⟩, -, ha'⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at ha'; subst ha'; exact hc
  have hK : IsCompact {g : Matrix.unitaryGroup (Fin r) E | actU g X ∈ tsupport f} := by
    have := (Homeomorph.mulRight g₀).isCompact_preimage.mpr hS
    convert this using 1
    ext g; simp [Homeomorph.coe_mulRight, actU_mul, hg₀]
  refine HasCompactSupport.intro' hK ((isClosed_tsupport f).preimage (continuous_actU X)) ?_
  intro g hg
  simp only [Set.mem_setOf_eq] at hg
  exact image_eq_zero_of_notMem_tsupport hg
end GlobalTheory.JR.OrbTest
