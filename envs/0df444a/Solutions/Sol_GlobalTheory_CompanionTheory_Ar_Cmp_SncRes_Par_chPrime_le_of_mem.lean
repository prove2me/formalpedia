-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.chPrime_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:21:07.28659+00:00
-- url     : https://prove2.me/submissions/d15fcc97-ffdc-4adb-a7e8-b746ba831ef8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_PrimesBelowParams
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_exists_mul_mem_of_algebraMap_locRing_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_mk_locRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages GlobalTheory.CompanionTheory.Ar.Cmp
variable {m : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
theorem _root_.solution {I 𝔮 : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    {f : MvPolynomial (Fin m) ℂ} (h𝔮 : 𝔮.IsPrime) (hI𝔮 : I ≤ 𝔮) (h𝔮t : 𝔮 ≤ ptIdeal t)
    (hf : f ∈ 𝔮) : chPrime I t f ≤ 𝔮 := by
  intro g hg
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hg)
  obtain ⟨a₀, b₀, hb₀, hab⟩ := exists_mk_locRing I t a
  have hz : algebraMap _ (locRing I t) (b₀ * g - a₀ * f) = 0 := by
    rw [map_sub, map_mul, map_mul, ← ha, ← hab]
    ring
  obtain ⟨s, hs, hsI⟩ := exists_mul_mem_of_algebraMap_locRing_eq_zero I t hz
  have hmem : (s * b₀) * g ∈ 𝔮 := by
    have h1 := 𝔮.add_mem (hI𝔮 hsI) (𝔮.mul_mem_left (s * a₀) hf)
    have h2 : s * (b₀ * g - a₀ * f) + s * a₀ * f = (s * b₀) * g := by ring
    rwa [h2] at h1
  refine (h𝔮.mem_or_mem hmem).resolve_left fun hc => ?_
  have := RingHom.mem_ker.mp (h𝔮t hc)
  rw [map_mul] at this
  exact mul_ne_zero hs hb₀ this
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
