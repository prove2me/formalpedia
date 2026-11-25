-- Prove2me | solution 1 for GlobalTheory.Mass.DiscOrder.idxN_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:12:15.929874+00:00
-- url     : https://prove2.me/submissions/2f733d43-50a6-40d1-ba03-b513e5484fc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_eq_card
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top


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
omit [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.Mass.DiscOrder
theorem _root_.solution {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsLattice K X) (hY : Y.FG) :
    idxN Y X ≠ 0 := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom (nonZeroDivisors (𝓞 K)) Y X hY
    (by rw [indexBasic_locS_top (K := K) X hX.span_eq_top]; exact le_top)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
  have : Module.Finite (𝓞 K) Y := Module.Finite.iff_fg.mpr hY
  have : Module.Finite ℤ (Y ⧸ X.comap Y.subtype) := Module.Finite.trans (𝓞 K) _
  have : Finite (Y ⧸ X.comap Y.subtype) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (X.comap Y.subtype) q
    refine ⟨⟨(Ideal.absNorm (Ideal.span {d}) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • Submodule.mkQ (X.comap Y.subtype) y = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • (y : V) ∈ X
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← hc, mul_smul]
    exact X.smul_mem c (hdY y y.2)
  rw [idxN_eq_card]
  exact Nat.card_pos.ne'
end GlobalTheory.Mass.DiscOrder
