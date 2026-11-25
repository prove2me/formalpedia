-- Prove2me | solution 1 for GlobalTheory.DegCnt.FixDisc.exists_rat_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:38.508318+00:00
-- url     : https://prove2.me/submissions/248f7321-860c-483d-b8f4-77c8231c7e8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_ne_zero
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.FixDisc
theorem _root_.solution [Module ℚ V] [Module.Finite ℚ V] {A : Submodule (𝓞 K) V}
    (hA : Submodule.IsLattice K A) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ V)) ℚ V, A.toAddSubgroup = AddSubgroup.closure (Set.range b) := by
  have hfin : Module.Finite (𝓞 K) A := Module.Finite.iff_fg.mpr hA.fg
  have hfinZ : Module.Finite ℤ A := Module.Finite.trans (𝓞 K) _
  have hL : Submodule.IsLattice ℚ (A.restrictScalars ℤ) := by
    refine ⟨Module.Finite.iff_fg.mp hfinZ, ?_⟩
    rw [eq_top_iff]
    intro x _
    have h := idxN_ne_zero hA (Submodule.fg_span_singleton (R := 𝓞 K) x)
    set n := idxN (Submodule.span (𝓞 K) {x}) A with hn
    have h1 : n • x ∈ A := AddSubgroup.nsmul_relIndex_mem A.toAddSubgroup
      (K := (Submodule.span (𝓞 K) {x}).toAddSubgroup) (Submodule.mem_span_singleton_self x)
    have h2 : (n : ℚ) ≠ 0 := by exact_mod_cast h
    have h3 : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hr : Module.finrank ℤ (A.restrictScalars ℤ) = Module.finrank ℚ V := by
    unfold Module.finrank
    rw [Submodule.IsLattice.rank' ℚ]
  let b₀ := Module.finBasisOfFinrankEq ℤ (A.restrictScalars ℤ) hr
  refine ⟨b₀.extendOfIsLattice ℚ, ?_⟩
  rw [← Submodule.span_int_eq_addSubgroupClosure]
  have e : Set.range (b₀.extendOfIsLattice ℚ) = (A.restrictScalars ℤ).subtype '' Set.range b₀ := by
    rw [← Set.range_comp]
    congr 1
    funext i
    simp
  rw [e, ← Submodule.map_span, b₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  rfl
end GlobalTheory.DegCnt.FixDisc
