-- Prove2me | solution 1 for GlobalTheory.Mass.Witt.exists_isom_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:14.159265+00:00
-- url     : https://prove2.me/submissions/44382e96-9f1f-4334-b19b-d7cadbde04dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Theorems.Thm_GlobalTheory_Mass_Witt_exists_isom_move

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Witt
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.Witt
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) {ι : Type} (a b : ι → V)
    (hab : ∀ i j, h (b i) (b j) = h (a i) (a j)) (t : Finset ι) :
    ∃ g ∈ isom h, ∀ i ∈ t, g (a i) = b i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, (isom h).one_mem, by simp⟩
  | insert j s hj ih =>
    obtain ⟨g, hg, hgs⟩ := ih
    have hg' : ∀ u v, h (g u) (g v) = h u v := hg
    have hgx : h (g (a j)) (g (a j)) = h (b j) (b j) := by rw [hg', hab]
    obtain ⟨k, hk, hkx, hkfix⟩ := exists_isom_move h hs ha (g (a j)) (b j) hgx
    refine ⟨k * g, (isom h).mul_mem hk hg, fun i hi => ?_⟩
    show k (g (a i)) = b i
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hkx
    · rw [hgs i hi]
      apply hkfix
      have e1 : h (g (a j)) (b i) = h (b j) (b i) :=
        calc h (g (a j)) (b i) = h (g (a j)) (g (a i)) := by rw [hgs i hi]
          _ = h (a j) (a i) := hg' _ _
          _ = h (b j) (b i) := (hab j i).symm
      rw [map_sub, LinearMap.sub_apply, e1, sub_self]
end GlobalTheory.Mass.Witt
