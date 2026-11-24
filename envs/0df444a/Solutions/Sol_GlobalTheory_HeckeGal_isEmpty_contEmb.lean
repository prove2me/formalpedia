-- Prove2me | solution 1 for GlobalTheory.HeckeGal.isEmpty_contEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:41.35039+00:00
-- url     : https://prove2.me/submissions/bf4a9df8-7e74-4ee8-8c89-bee3424054d2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.HeckeGal
theorem _root_.solution {v : HeightOneSpectrum (𝓞 E)} (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    IsEmpty {j : v.adicCompletion E →+* Qbar l // Continuous j} := by
  refine ⟨fun j => ?_⟩
  have hl : l.Prime := Fact.out
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  obtain ⟨a, M, hM, hNM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.ne_one
  have hmem : ((M : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    have h := Ideal.absNorm_mem v.asIdeal
    rw [hNM, Nat.cast_mul, Nat.cast_pow] at h
    exact (v.isPrime.mem_or_mem h).resolve_left fun h' => hv (v.isPrime.mem_of_pow_mem a h')
  have hlt : Valued.v ((M : ℕ) : v.adicCompletion E) < 1 := by
    have h : Valued.v (((algebraMap (𝓞 E) E (M : 𝓞 E) : E)) : v.adicCompletion E) =
        v.valuation E (algebraMap (𝓞 E) E (M : 𝓞 E)) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
    have h2 : v.valuation E (algebraMap (𝓞 E) E (M : 𝓞 E)) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hmem
    rw [← h] at h2
    have e : (((algebraMap (𝓞 E) E (M : 𝓞 E) : E)) : v.adicCompletion E) = ((M : ℕ) : v.adicCompletion E) := by
      rw [map_natCast]
      exact map_natCast (algebraMap E (v.adicCompletion E)) M
    rwa [e] at h2
  have ht : Filter.Tendsto (fun k : ℕ => ((M : ℕ) : v.adicCompletion E) ^ k) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one hlt
  have ht2 := ((j.2.tendsto 0).comp ht).norm
  have hn : ‖((M : ℕ) : Qbar l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hl).mpr hM)
  have e : (fun k : ℕ => ‖((j.1 : _ → _) ∘ fun k : ℕ => ((M : ℕ) : v.adicCompletion E) ^ k) k‖) = fun _ => (1 : ℝ) := by
    funext k
    simp [hn]
  rw [e, map_zero, norm_zero] at ht2
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds ht2)
end GlobalTheory.HeckeGal
