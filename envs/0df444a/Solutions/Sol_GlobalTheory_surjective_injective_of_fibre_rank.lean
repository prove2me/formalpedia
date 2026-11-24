-- Prove2me | solution 1 for GlobalTheory.surjective_injective_of_fibre_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:17:30.334669+00:00
-- url     : https://prove2.me/submissions/7a2eddaf-c72f-4908-a53b-fc017fed086c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Theorems.Thm_GlobalTheory_surjective_of_fibre_rank
import Theorems.Thm_GlobalTheory_injective_of_fibre_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N), ((∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Surjective f) ∧ (Module.Finite O M → Module.Projective O N → Function.Surjective f → (∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField M) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Injective f) := by
  intro O M N _ _ _ _ _ _ f
  exact ⟨surjective_of_fibre_rank O M N f,
    fun _ _ hf h => injective_of_fibre_rank O M N f hf h⟩
end GlobalTheory
