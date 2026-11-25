-- Prove2me | solution 1 for GlobalTheory.Mass.DiscOrder.idxN_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:06.181574+00:00
-- url     : https://prove2.me/submissions/268e7496-20ad-41c9-a4d6-e1b7beb3297b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_mul
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_eq_one
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_exists_covBy
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_ne_zero
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_lattice_between
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_dual_of_covBy
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic


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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn
namespace GlobalTheory.Mass.DiscOrder
theorem _root_.solution {X : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X) : ∀ (n : ℕ)
    (Y : Submodule (𝓞 K) V), Submodule.IsLattice K Y → X ≤ Y → idxN Y X = n →
    idxN (dual h X) (dual h Y) = n := by
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hY hle hi
  rcases hle.eq_or_lt with rfl | hlt
  · rw [← hi, idxN_eq_one.2 le_rfl, idxN_eq_one.2 le_rfl]
  obtain ⟨Z, hXZ, hc⟩ := exists_covBy hY.fg hlt
  have hZ := lattice_between hX hY hXZ hc.le
  have m1 := idxN_mul hXZ hc.le
  have n1 := idxN_ne_zero hX hZ.fg
  have n2 := idxN_ne_zero hZ hY.fg
  have n3 : idxN Y Z ≠ 1 := fun e => hc.lt.not_ge (idxN_eq_one.1 e)
  have hlt' : idxN Z X < n := by
    rw [← hi, ← m1]
    exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero n1) (by omega)
  rw [← idxN_mul (an _ _ hc.le) (an _ _ hXZ), ih _ hlt' Z hZ hXZ rfl, idxN_dual_of_covBy h hs hn hZ hY hc,
    ← hi, ← m1, mul_comm]
end GlobalTheory.Mass.DiscOrder
