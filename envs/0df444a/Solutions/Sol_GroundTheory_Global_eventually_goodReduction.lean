-- Prove2me | solution 1 for GroundTheory.Global.eventually_goodReduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:45:43.58141+00:00
-- url     : https://prove2.me/submissions/80fd26d9-d5bf-42b9-998d-897c9efef6d2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_GoodReductionAlmostAll
import Theorems.Thm_GroundTheory_Global_eventually_exists_model
import Theorems.Thm_GroundTheory_Global_algebraMap_j_of_map_eq
import Theorems.Thm_GroundTheory_Global_eventually_residue_j_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [NumberField L]
namespace GroundTheory.Global
theorem _root_.solution {ι : Type*} [Finite ι] (E : ι → WeierstrassCurve L)
    [∀ i, (E i).IsElliptic] (hE : Pairwise fun i k => (E i).j ≠ (E k).j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ (W : ι → WeierstrassCurve (localizationAt L v)) (_ : ∀ i, (W i).IsElliptic),
        (∀ i, (W i).map (algebraMap (localizationAt L v) L) = E i) ∧
        (∀ i, algebraMap (localizationAt L v) L (W i).j = (E i).j) ∧
        Pairwise fun i k => residue (localizationAt L v) (W i).j ≠
          residue (localizationAt L v) (W k).j := by
  have hd : ∀ i k, ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, i ≠ k →
      ∀ (W W' : WeierstrassCurve (localizationAt L v)) [W.IsElliptic] [W'.IsElliptic],
        W.map (algebraMap (localizationAt L v) L) = E i →
          W'.map (algebraMap (localizationAt L v) L) = E k →
            residue (localizationAt L v) W.j ≠ residue (localizationAt L v) W'.j := by
    intro i k
    by_cases hik : i = k
    · exact Filter.Eventually.of_forall fun _ h => (h hik).elim
    · exact (eventually_residue_j_ne (hE hik)).mono fun _ h _ => h
  filter_upwards [Filter.eventually_all.mpr fun i => eventually_exists_model (E i),
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hd i)] with v hm hdv
  choose W hWe hWm using hm
  exact ⟨W, hWe, hWm, fun i => algebraMap_j_of_map_eq (hWm i),
    fun i k hik => hdv i k hik (W i) (W k) (hWm i) (hWm k)⟩
end GroundTheory.Global
