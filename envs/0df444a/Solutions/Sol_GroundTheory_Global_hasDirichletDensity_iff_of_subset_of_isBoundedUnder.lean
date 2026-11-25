-- Prove2me | solution 1 for GroundTheory.Global.hasDirichletDensity_iff_of_subset_of_isBoundedUnder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:50.385797+00:00
-- url     : https://prove2.me/submissions/618715e6-3d53-47c6-b5d2-f4cb05c63b8f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_union
import Theorems.Thm_GroundTheory_Global_hasDirichletDensity_zero_of_isBoundedUnder

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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {S T : Set (HeightOneSpectrum (𝓞 K))}
    (hTS : T ⊆ S) (hb : IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s => (S \ T).primeIdealZetaSum s)
    (δ : ℝ) : T.HasDirichletDensity δ ↔ S.HasDirichletDensity δ := by
  have h0 := hasDirichletDensity_zero_of_isBoundedUnder hb
  unfold Set.HasDirichletDensity at h0 ⊢
  have heq : ∀ᶠ s in 𝓝[>] (1 : ℝ),
      S.primeIdealZetaSum s / (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
        T.primeIdealZetaSum s / (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s +
        (S \ T).primeIdealZetaSum s /
          (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← add_div, ← primeIdealZetaSum_union disjoint_sdiff_right hs, union_sdiff_cancel hTS]
  constructor
  · intro hT
    have := hT.add h0
    rw [add_zero] at this
    exact this.congr' (heq.mono fun s hs => hs.symm)
  · intro hS
    have := hS.sub h0
    rw [sub_zero] at this
    refine this.congr' (heq.mono fun s hs => ?_)
    rw [hs]
    ring
end GroundTheory.Global
