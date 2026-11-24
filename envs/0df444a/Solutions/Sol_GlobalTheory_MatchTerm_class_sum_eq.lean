-- Prove2me | solution 1 for GlobalTheory.MatchTerm.class_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:54:33.971994+00:00
-- url     : https://prove2.me/submissions/de018104-f118-441e-b1cf-bce79476ccf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TendstoTsumZeroOfEventuallyNotMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueAddEquivOfCompatibleCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Theorems.Thm_GlobalTheory_TorsionFourier_natCard_torsionChars
import Theorems.Thm_GlobalTheory_fourier_extraction_tsum_class


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Module Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
variable {K X X' : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X']
namespace GlobalTheory.MatchTerm
theorem _root_.solution [IsAlgClosed K] {M : ℕ} (hM : ‖(M : K)‖ = 1) (σ : X → K) (σ' : X' → K)
    (hσ : Tendsto σ cofinite (𝓝 0)) (hσ' : Tendsto σ' cofinite (𝓝 0)) (c : K) (α : X) (α' : X')
    (E : {t : Multiplicative X →* Kˣ // t ^ M = 1} → {t : Multiplicative X' →* Kˣ // t ^ M = 1})
    (hE : Function.Bijective E)
    (hα : ∀ t, (E t).1 (Multiplicative.ofAdd α') = t.1 (Multiplicative.ofAdd α))
    (hs : ∀ t, ∑' β, σ' β * ((E t).1 (Multiplicative.ofAdd β) : K) =
      c * ∑' β, σ β * (t.1 (Multiplicative.ofAdd β) : K)) :
    ∑' μ, σ' (α' + M • μ) = c * ∑' μ, σ (α + M • μ) := by
  have h0 : (M : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hM
    exact zero_ne_one hM
  have hp : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at h0)
  haveI : NeZero (M : K) := ⟨h0⟩
  haveI : NeZero M := ⟨hp.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
  obtain ⟨hf, h1, -⟩ := fourier_extraction_tsum_class K X M ζ hp hM hζ σ hσ α
  obtain ⟨-, h2, -⟩ := fourier_extraction_tsum_class K X' M ζ hp hM hζ σ' hσ' α'
  have hc : M ^ finrank ℤ X = M ^ finrank ℤ X' := by
    rw [← TorsionFourier.natCard_torsionChars (K := K) hp hζ, ← TorsionFourier.natCard_torsionChars (K := K) hp hζ]
    exact Nat.card_eq_of_bijective E hE
  have hc' : (M : K) ^ finrank ℤ X = (M : K) ^ finrank ℤ X' := by exact_mod_cast congrArg (Nat.cast : ℕ → K) hc
  rw [← finsum_comp E hE] at h2
  simp only [hα, hs] at h2
  haveI := Fintype.ofFinite {t : Multiplicative X →* Kˣ // t ^ M = 1}
  rw [finsum_eq_sum_of_fintype] at h1 h2
  apply mul_left_cancel₀ (pow_ne_zero (finrank ℤ X') h0)
  rw [← h2, ← hc', mul_left_comm, ← h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => mul_left_comm _ _ _
end GlobalTheory.MatchTerm
