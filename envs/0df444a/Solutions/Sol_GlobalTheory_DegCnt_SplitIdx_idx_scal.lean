-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.idx_scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:08:47.243598+00:00
-- url     : https://prove2.me/submissions/727050da-518d-41d5-a2d4-2c01213fd9df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_idx_of_bij
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_gidx_eq_idx
import Theorems.Thm_GlobalTheory_DegCnt_SplitIdx_isLattice_field
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_GoodMap_comp
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_gidx_mul
import Theorems.Thm_GlobalTheory_DegCnt_DelScale_gidx_pos
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitIdx
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution {c : K} (hc : c * star c = 1) {A M M' : Submodule (𝓞 K) K} (hA : Submodule.IsLattice K A)
    (hM : Submodule.IsLattice K M) (hM' : Submodule.IsLattice K M') (h : ∀ t, t ∈ M' ↔ t * c ∈ M)
    (h1 : M ≤ A) (h2 : M' ≤ A) : idx A M' = idx A M := by
  have hc0 : c ≠ 0 := fun e => by simp [e] at hc
  have hone : (1 : Submodule (𝓞 K) K).FG := by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  have o1 : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have L1 := isLattice_field hone o1 one_ne_zero
  set C : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {c} with hC
  have LC : Submodule.IsLattice K C :=
    isLattice_field (Submodule.fg_span_singleton _) (Submodule.mem_span_singleton_self c) hc0
  have mC : ∀ x : K, x * c ∈ C ↔ x ∈ (1 : Submodule (𝓞 K) K) := fun x => by
    rw [hC, Submodule.mem_span_singleton, Submodule.mem_one]
    refine exists_congr fun a => ?_
    rw [Algebra.smul_def, mul_left_inj' hc0]
  have ms : ∀ x : K, star x ∈ (1 : Submodule (𝓞 K) K) ↔ x ∈ (1 : Submodule (𝓞 K) K) := by
    have : ∀ x : K, x ∈ (1 : Submodule (𝓞 K) K) → star x ∈ (1 : Submodule (𝓞 K) K) := fun x hx => by
      obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hx
      exact Submodule.mem_one.2 (Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range a)
    exact fun x => ⟨fun hx => by simpa using this _ hx, this x⟩
  have bm : Function.Bijective (AddMonoidHom.mulRight c) := (Equiv.mulRight₀ c hc0).bijective
  set f : K →+ K := (AddMonoidHom.mulRight c).comp (starAddEquiv : K ≃+ K).toAddMonoidHom with hf
  have fx : ∀ x, f x = star x * c := fun _ => rfl
  have bf : Function.Bijective f := bm.comp (starAddEquiv : K ≃+ K).bijective
  have e1 : idx C 1 = idx 1 C := by
    refine idx_of_bij f bf (fun x => by rw [fx, mC, ms]) fun x => ?_
    rw [fx, ← ms, star_mul, star_star, ← mC]
    have : star c * x * c = x := by rw [mul_right_comm, mul_comm (star c), hc, one_mul]
    rw [this]
  have g1 : gidx C 1 = 1 := by
    rw [gidx, e1]
    exact div_self (Nat.cast_ne_zero.2 (idxN_ne_zero LC hone))
  have g2 : gidx M C = gidx M' 1 := by
    rw [gidx, gidx, idx_of_bij _ bm (A := M') (B := 1) (fun x => (h x).symm) mC,
      idx_of_bij _ bm (A := 1) (B := M') mC (fun x => (h x).symm)]
  have g3 : gidx M 1 = gidx M' 1 := by rw [← gidx_mul hM LC L1, g1, mul_one, g2]
  have a := gidx_mul hA hM L1
  have b := gidx_mul hA hM' L1
  rw [g3, ← b, mul_left_inj' (gidx_pos hM' L1).ne', gidx_eq_idx h1, gidx_eq_idx h2] at a
  exact_mod_cast a.symm
end GlobalTheory.DegCnt.SplitIdx
