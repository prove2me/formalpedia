-- Prove2me | solution 1 for GlobalTheory.CMVal.Fibre.tendsto_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:33.552377+00:00
-- url     : https://prove2.me/submissions/490cd712-843c-404e-9d36-685bda438714

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Fibre
variable {E : Type} [Field E] [NumberField E]
open Classical
namespace GlobalTheory.CMVal.Fibre
theorem _root_.solution (a : Af E) (g : Finset (HeightOneSpectrum (𝓞 E)) → Af E)
    (hg : ∀ T v, g T v = if v ∈ T then a v else 1) : Tendsto g atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 E)) := {v | a v ∈ v.adicCompletionIntegers E}
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal S)
  let f : Finset (HeightOneSpectrum (𝓞 E)) → P := fun T => ⟨fun v => if v ∈ T then a v else 1, by
    rw [Filter.eventually_principal]
    intro w hw
    by_cases h : w ∈ T
    · simp only [h, if_true]; exact hw
    · simp only [h, if_false]; exact one_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [Filter.eventually_principal]; exact fun w hw => hw⟩
  have hf : Filter.Tendsto f Filter.atTop (nhds a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = if v ∈ T then a v else 1
    rw [if_pos this]
  have h2 := ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf
  have h3 : g = (RestrictedProduct.inclusion _ _ hle) ∘ f :=
    funext fun T => Subtype.ext (funext fun v => hg T v)
  rw [h3]
  exact h2
end GlobalTheory.CMVal.Fibre
