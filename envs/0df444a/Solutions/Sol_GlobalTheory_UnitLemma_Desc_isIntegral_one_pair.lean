-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.isIntegral_one_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:59:06.570452+00:00
-- url     : https://prove2.me/submissions/492d4286-8c89-4308-a433-d71aeebbd2ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProductLatticePositionsAndTerms
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_aeval_prod_fst
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_aeval_prod_snd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
variable {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {r : A₂} (hr : IsIntegral R r) : IsIntegral R ((1, r) : A₁ × A₂) := by
  obtain ⟨f, hf, hfr⟩ := hr
  refine ⟨f * (X - C 1), hf.mul (monic_X_sub_C 1), ?_⟩
  rw [← aeval_def, map_mul]
  rw [← aeval_def] at hfr
  ext
  · rw [Prod.fst_mul, aeval_prod_fst (f := X - C 1)]; simp
  · rw [Prod.snd_mul, aeval_prod_snd, hfr, zero_mul]; rfl
end GlobalTheory.UnitLemma.Desc
