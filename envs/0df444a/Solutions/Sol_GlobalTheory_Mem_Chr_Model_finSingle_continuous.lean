-- Prove2me | solution 1 for GlobalTheory.Mem.Chr.Model.finSingle_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:40.835692+00:00
-- url     : https://prove2.me/submissions/7d4eb11b-43aa-4fd5-bb18-3e3de4b6796f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]
namespace GlobalTheory.Mem.Chr.Model
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) : Continuous (finSingle L v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 L))) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal {v}ᶜ) :=
    fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.mulSingle_eq_of_ne (Set.mem_compl_singleton_iff.mp hw)]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle v)
  have hfg : (finSingle L v : v.adicCompletion L → FiniteAdeleRing (𝓞 L) L) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    funext x
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg
end GlobalTheory.Mem.Chr.Model
