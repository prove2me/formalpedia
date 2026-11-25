-- Prove2me | solution 1 for GlobalTheory.DegAsm.FrameMove.exists_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:16.833155+00:00
-- url     : https://prove2.me/submissions/f2eb7cb7-c72b-4651-a3e3-eac2c2957197

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_swap_zero
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_exists_dual
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_smul_dual_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_exists_integer_add_star_eq_one_of_isCMUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.FrameMove
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.FrameMove
theorem _root_.solution [FiniteDimensional K V] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (G : FlagD H r) {Λ : Submodule (𝓞 K) V}
    (hU : IsUnimod H Λ) {aa : Fin r → Submodule (𝓞 K) K}
    (h1 : ∀ (a : Fin r) (t : K), ∀ x ∈ Λ, x - t • G.e a.castSucc ∈ G.Xa a.val → t ∈ aa a)
    (h2 : ∀ a, ∀ t ∈ aa a, t • G.e a.castSucc ∈ Λ)
    (h3 : ∀ (t : K), ∀ x ∈ Λ, x - t • G.z ∈ G.X → t ∈ (1 : Submodule (𝓞 K) K)) (h4 : G.z ∈ Λ) :
    ∃ y : Fin r → V, Hyp H (fun a => G.e a.castSucc) y ∧ (∀ b, H.B G.z (y b) = 0) ∧
      ∀ x ∈ Λ, ∀ b, H.B x (y b) ∈ aa b := by
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_dual G hU h1 h2 h3 h4
  obtain ⟨w, hw⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram K hK
  have hw' : star (w : K) = ((1 - w : 𝓞 K) : K) := by
    have : ((1 - w : 𝓞 K) : K) = 1 - (w : K) := by simp
    rw [this, ← hw]; ring
  have hye : ∀ a b, H.B (y a) (G.e b.castSucc) = if a = b then 1 else 0 := by
    intro a b
    rw [← H.herm, hy1]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hz : ∀ a : Fin r, H.B G.z (G.e a.castSucc) = 0 := fun a => swap_zero (G.zperp a)
  refine ⟨fun a => y a - ∑ b, ((w : K) * H.B (y a) (y b)) • G.e b.castSucc, ⟨G.iso, fun a b => ?_, fun a b => ?_⟩,
    fun b => ?_, fun x hx a => ?_⟩
  · have hh : (starRingEnd K) (H.B (y b) (y a)) = H.B (y a) (y b) := H.herm _ _
    have hw2 : (w : K) + (starRingEnd K) (w : K) = 1 := hw
    simp [G.iso, hye, hy1, hh]
    linear_combination (-H.B (y a) (y b)) * hw2
  · simp [G.iso, hy1]
  · simp [hy2, hz]
  · rw [map_sub, map_sum]
    refine Submodule.sub_mem _ (hy3 x hx a) (Submodule.sum_mem _ fun b _ => ?_)
    have e1 := hy3 _ (smul_dual_mem hU (fun x' hx' => h2 b _ (hy3 x' hx' b)) hx) a
    have e2 := (aa a).smul_mem (1 - w) e1
    convert e2 using 1
    have hh : (starRingEnd K) (H.B (y a) (y b)) = H.B (y b) (y a) := H.herm _ _
    have hw2 : (starRingEnd K) (w : K) = ((1 - w : 𝓞 K) : K) := hw'
    rw [LinearMap.map_smulₛₗ, map_mul, hh, hw2, smul_eq_mul, Algebra.smul_def, map_smul]
    simp only [smul_eq_mul, LinearMap.smul_apply]
    change _ = ((1 - w : 𝓞 K) : K) * _
    ring
end GlobalTheory.DegAsm.FrameMove
