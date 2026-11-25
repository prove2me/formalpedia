-- Prove2me | solution 1 for GlobalTheory.DegCnt.DatCount.genBy_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:02:15.478632+00:00
-- url     : https://prove2.me/submissions/c3a23014-68e8-4bc6-8329-a008122fa762

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEmbeddedDataWithGivenFixedLattice
import Theorems.Thm_GlobalTheory_DegCnt_DatCount_exists_gens_of_map
import Theorems.Thm_GlobalTheory_DegCnt_DatCount_GenBy_trans
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DatCount
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.DatCount
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule (𝓞 K) V} {e : ℕ} (hg : GenBy Y X e)
    {m : ℕ} (hm : m ≠ 0) (hmY : ∀ y ∈ Y, (m : 𝓞 K) • y ∈ X) :
    GenBy (Formalism.HermitianLatticesTheory.dual h X) (Formalism.HermitianLatticesTheory.dual h Y) e := by
  obtain ⟨t, hc, hY⟩ := hg
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm
  have htY : ∀ s : t, (s : V) ∈ Y := fun s => by
    rw [hY]; exact Submodule.mem_sup_right (Submodule.subset_span s.2)
  let f : V →ₗ[𝓞 K] (t → K) := LinearMap.pi fun s => (h (s : V)).restrictScalars (𝓞 K)
  let A : Submodule (𝓞 K) (t → K) := Submodule.pi Set.univ fun _ => 1
  let T : Finset (t → K) := Finset.univ.image fun s : t => Pi.single s (m : K)⁻¹
  have hsm : ∀ (c : 𝓞 K) (a : K), c • a = (c : K) * a := fun c a => Algebra.smul_def c a
  obtain ⟨t', hc', ht'⟩ := exists_gens_of_map f (Formalism.HermitianLatticesTheory.dual h X) A (m : 𝓞 K) (Nat.cast_ne_zero.2 hm) T
    (by
      intro x hx
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hx
      intro i _
      by_cases hi : i = s
      · subst hi
        refine Submodule.mem_one.2 ⟨1, ?_⟩
        simp [hsm, hmK]
      · simp [hi])
    (by
      rintro _ ⟨v, hv, rfl⟩
      refine Submodule.mem_sup_right ?_
      rw [← Finset.univ_sum_single (f v)]
      refine Submodule.sum_mem _ fun s _ => ?_
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 ((Formalism.HermitianLatticesTheory.dualBasic_mem_dual h X v).1 hv _ (hmY _ (htY s)))
      have e1 : (Pi.single s (f v s) : t → K) = c • (Pi.single s (m : K)⁻¹ : t → K) := by
        rw [← Pi.single_smul, hsm]
        congr 1
        have e2 : h ((m : 𝓞 K) • (s : V)) v = (m : K) * h s v := by
          rw [Nat.cast_smul_eq_nsmul, map_nsmul]; simp
        change h s v = algebraMap (𝓞 K) K c * _
        rw [hc, e2]; field_simp
      rw [e1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ s)))))
  refine ⟨t', hc'.trans (Finset.card_image_le.trans (by simpa using hc)), ?_⟩
  have : Formalism.HermitianLatticesTheory.dual h X ⊓ A.comap f = Formalism.HermitianLatticesTheory.dual h Y := by
    ext v
    constructor
    · rintro ⟨hv, hv'⟩
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      rw [hY] at hy
      obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, LinearMap.add_apply]
      refine add_mem ((Formalism.HermitianLatticesTheory.dualBasic_mem_dual h X v).1 hv a ha) ?_
      clear hy
      induction hs using Submodule.span_induction with
      | mem s hs => exact hv' ⟨s, hs⟩ trivial
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [Formalism.HermitianLatticesTheory.genusBasic_hsmul_left Formalism.HermitianLatticesTheory.genusCovol_hinj Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range]
        rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ ha
    · intro hv
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hv
      refine ⟨(Formalism.HermitianLatticesTheory.dualBasic_mem_dual h X v).2 fun y hy => hv y ?_, fun s _ => hv _ (htY s)⟩
      rw [hY]; exact Submodule.mem_sup_left hy
  rw [← this]
  exact ht'
end GlobalTheory.DegCnt.DatCount
