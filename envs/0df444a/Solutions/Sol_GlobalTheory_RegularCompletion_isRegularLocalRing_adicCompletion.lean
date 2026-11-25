-- Prove2me | solution 1 for GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:04.21159+00:00
-- url     : https://prove2.me/submissions/8414f0e9-24c2-4898-b500-3bd088e66748

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsNoetherianRingAdicCompletionOfNoetherian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletion
import Theorems.Thm_GlobalTheory_AdicNoeth_isNoetherianRing_adicCompletion
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_flat
import Theorems.Thm_GlobalTheory_isRegular_of_length_eq_spanFinrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.RegularCompletion
namespace GlobalTheory.RegularCompletion
theorem _root_.solution :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T],
      IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by
  intro T _ _
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal T) T) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)
  set S := AdicCompletion (maximalIdeal T) T

  obtain ⟨s, hcard, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal T).fg_of_isNoetherianRing
  set xs := s.toList
  have hofl : Ideal.ofList xs = maximalIdeal T := by
    rw [← hs]; unfold Ideal.ofList; congr 1; ext x; simp [xs]
  have hlen : xs.length = (maximalIdeal T).spanFinrank := by simp [xs, hcard]
  have hreg : RingTheory.Sequence.IsRegular T xs := GlobalTheory.isRegular_of_length_eq_spanFinrank hofl hlen
  have hmem : ∀ r ∈ xs.map (algebraMap T S), r ∈ maximalIdeal S := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ (hofl ▸ Ideal.subset_span hx)
  have hregS : RingTheory.Sequence.IsRegular S (xs.map (algebraMap T S)) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
      (hreg.toIsWeaklyRegular.of_flat)
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hregS
  have hnt : Nontrivial (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    apply hregS.2
    simp [htop]
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq, ← hdim]
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [List.length_map, hlen]
  calc ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞)
      = 0 + ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞) := (zero_add _).symm
    _ ≤ _ := add_le_add_left h0 _
end GlobalTheory.RegularCompletion
