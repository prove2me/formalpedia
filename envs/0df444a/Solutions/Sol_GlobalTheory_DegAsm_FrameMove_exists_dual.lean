-- Prove2me | solution 1 for GlobalTheory.DegAsm.FrameMove.exists_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:20.931105+00:00
-- url     : https://prove2.me/submissions/1c045ef4-909d-4a5d-8e6e-fa95749e8fea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_exists_proj
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_exists_rep
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_sum_mem_xa
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_coeff_mem
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_smul_mem_of_one
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_isLatMod_top_bot_iff
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
theorem _root_.solution [FiniteDimensional K V] (G : FlagD H r) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    {aa : Fin r → Submodule (𝓞 K) K}
    (h1 : ∀ (a : Fin r) (t : K), ∀ x ∈ Λ, x - t • G.e a.castSucc ∈ G.Xa a.val → t ∈ aa a)
    (h2 : ∀ a, ∀ t ∈ aa a, t • G.e a.castSucc ∈ Λ)
    (h3 : ∀ (t : K), ∀ x ∈ Λ, x - t • G.z ∈ G.X → t ∈ (1 : Submodule (𝓞 K) K)) (h4 : G.z ∈ Λ) :
    ∃ y : Fin r → V, (∀ a b, H.B (G.e a.castSucc) (y b) = if a = b then 1 else 0) ∧ (∀ b, H.B G.z (y b) = 0) ∧
      ∀ x ∈ Λ, ∀ b, H.B x (y b) ∈ aa b := by
  have hL := (isLatMod_top_bot_iff Λ).1 hU.1
  let L : ((Fin r → K) × K) →ₗ[K] V :=
    (Fintype.linearCombination K fun a : Fin r => G.e a.castSucc).coprod (LinearMap.toSpanSingleton K V G.z)
  have hLa : ∀ p, L p = ∑ b, p.1 b • G.e b.castSucc + p.2 • G.z := fun p => by
    simp [L, Fintype.linearCombination_apply]
  have hinj : LinearMap.ker L = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨c, t⟩ hp
    rw [LinearMap.mem_ker, hLa] at hp
    have h5 := congrArg (fun v => H.B v G.z) hp
    have h6 : ∀ a : Fin r, H.B (G.e a.castSucc) G.z = 0 := G.zperp
    have h7 : H.B G.z G.z = -G.T := G.zz
    simp [h6, h7, G.hT] at h5
    subst h5
    simp only [zero_smul, add_zero] at hp
    have := Fintype.linearIndependent_iff.1 G.indep c hp
    have hc : c = 0 := funext this
    simp [hc]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective L hinj
  have hg' : ∀ p, g (L p) = p := fun p => LinearMap.congr_fun hg p
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_proj Λ hL.fg hL.span_eq_top (LinearMap.range L)
  choose y hy using fun b : Fin r => exists_rep H (LinearMap.proj b ∘ₗ LinearMap.fst K _ K ∘ₗ g ∘ₗ P)
  have hy' : ∀ b p, H.B (L p) (y b) = p.1 b := fun b p => by
    rw [hy]; simp [hP2 _ ⟨p, rfl⟩, hg']
  refine ⟨y, fun a b => ?_, fun b => ?_, fun x hx b => ?_⟩
  · have := hy' b (Pi.single a 1, 0)
    rw [hLa] at this
    simpa [Pi.single_apply, eq_comm] using this
  · have := hy' b (0, 1)
    rw [hLa] at this
    simpa using this
  · obtain ⟨p, hp⟩ := hP1 x
    have e1 : H.B x (y b) = p.1 b := by rw [hy]; simp [← hp, hg']
    have e2 : L p ∈ Λ := hp ▸ hP3 x hx
    rw [hLa] at e2
    have e3 : p.2 ∈ (1 : Submodule (𝓞 K) K) := h3 _ _ e2 (by
      rw [add_sub_cancel_right]
      exact sum_mem_xa G r _ fun b hb => absurd b.2 (not_lt.2 hb))
    have e4 := Λ.sub_mem e2 (smul_mem_of_one e3 h4)
    rw [add_sub_cancel_right] at e4
    rw [e1]
    exact coeff_mem G h1 h2 r _ (fun b hb => absurd b.2 (not_lt.2 hb)) e4 b
end GlobalTheory.DegAsm.FrameMove
