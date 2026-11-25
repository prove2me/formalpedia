-- Prove2me | solution 1 for GlobalTheory.PlaceSum.sum_ram_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:22.433346+00:00
-- url     : https://prove2.me/submissions/46386e58-28b2-4f9a-ace7-0e0c0efca47d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumFinitePlacesLeSumOverPrimes
import Theorems.Thm_GlobalTheory_PlaceSum_liesOver_resChar
import Theorems.Thm_GlobalTheory_PlaceSum_span_ne_bot
import Theorems.Thm_GlobalTheory_PlaceSum_span_isMaximal
import Theorems.Thm_GlobalTheory_PlaceSum_mem_primesOverFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.PlaceSum
variable {K : Type} [Field K] [NumberField K]
set_option linter.deprecated false
namespace GlobalTheory.PlaceSum
theorem _root_.solution {p : ℕ} (hp : p.Prime) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ la ∈ T, resCharOf la = p) :
    ∑ la ∈ T, (ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal) ≤
      (Module.finrank ℚ K : ℝ) * Real.log p := by
  classical
  haveI := span_isMaximal hp
  have hs := Ideal.sum_ramification_inertia (R := ℤ) (𝓞 K) ℚ K (span_ne_bot hp)
  have h1 : ∀ la ∈ T, (ramOverZ la : ℝ) * Real.log (Ideal.absNorm la.asIdeal) =
      ((Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) la.asIdeal *
        Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) la.asIdeal : ℕ) : ℝ) * Real.log p := by
    intro la hla
    have h := hT la hla
    haveI : la.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by rw [← h]; exact liesOver_resChar la
    rw [Ideal.absNorm_eq_pow_inertiaDeg' la.asIdeal hp, ramOverZ, h]
    push_cast
    rw [Real.log_pow]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
  rw [← Nat.cast_sum, Nat.cast_le, ← hs]
  rw [← Finset.sum_image (s := T) (g := fun la => la.asIdeal)
    (f := fun P : Ideal (𝓞 K) => Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) P *
        Ideal.inertiaDeg' (Ideal.span {(p : ℤ)}) P) (fun a _ b _ h => HeightOneSpectrum.ext h)]
  refine Finset.sum_le_sum_of_subset ?_
  intro P hP
  obtain ⟨la, hla, rfl⟩ := Finset.mem_image.1 hP
  exact mem_primesOverFinset hp la (hT la hla)
end GlobalTheory.PlaceSum
