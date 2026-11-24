-- Prove2me | solution 1 for GlobalTheory.HeckeGal.norm_lt_one_of_contEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:45.457811+00:00
-- url     : https://prove2.me/submissions/d648dd54-a0e3-4907-8ee3-2fe13410b695

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PlaceEqOfContEmbCompEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory GlobalTheory.HeckeGal
open NumberField IsDedekindDomain
namespace GlobalTheory.HeckeGal
namespace _root_.GlobalTheory.HeckeGal
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    {l : ℕ} [Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 E)) (j : v.adicCompletion E →+* _root_.Formalism.ConjugateSelfDual.Qbar l) (hj : Continuous j)
    (a : 𝓞 E) (ha : a ∈ v.asIdeal) :
    ‖j (algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a))‖ < 1 := by
  set x := algebraMap E (v.adicCompletion E) (algebraMap (𝓞 E) E a) with hx
  have hx1 : ‖x‖ < 1 := by
    rw [hx, Valued.toNormedField.norm_lt_one_iff]
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) v a
    erw [h]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact ha
  have hlim : Filter.Tendsto (fun n : ℕ => j x ^ n) Filter.atTop (nhds 0) := by
    have h0 := (hj.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx1)
    simpa [Function.comp_def, map_pow] using h0
  by_contra hge
  push_neg at hge
  have hball : ∀ᶠ n : ℕ in Filter.atTop, ‖j x ^ n‖ < 1 :=
    (tendsto_norm_zero.comp hlim).eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n, hn⟩ := hball.exists
  rw [norm_pow] at hn
  exact absurd hn (not_lt.mpr (one_le_pow₀ hge))
end _root_.GlobalTheory.HeckeGal
end GlobalTheory.HeckeGal
