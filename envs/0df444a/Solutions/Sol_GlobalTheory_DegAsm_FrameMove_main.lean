-- Prove2me | solution 1 for GlobalTheory.DegAsm.FrameMove.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:01:21.119358+00:00
-- url     : https://prove2.me/submissions/ce0343a5-1c59-4738-84e9-09aa81741a76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIntegerAddStarEqOneOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SmulMemOfOne
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_swap_zero
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_mid_apply
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_Hyp_mid_e
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_move_apply
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_perp_of_span
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_move_isom
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_Hyp_mid_span
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_x_eq_span
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_mem_iff_pair
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_mem_lead
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_smul_dual_mem
import Theorems.Thm_GlobalTheory_DegAsm_FrameMove_exists_hyp
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_DegAsm_AdaptInv_x_eq
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
namespace GlobalTheory.DegAsm.FrameMove
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G : FlagD H r) (aa : Fin r → Submodule (𝓞 K) K) (Λ : Submodule (𝓞 K) V), IsUnimod H Λ → IsFrame F Λ aa → SameGr F G → F.T = G.T → (∀ a, ∀ t ∈ aa a, t • F.e a.castSucc ∈ Λ ∧ t • G.e a.castSucc ∈ Λ) → F.z ∈ Λ → G.z ∈ Λ → ∃ m : V ≃ₗ[K] V, F.InN (m : V →ₗ[K] V) ∧ m • Λ = Λ ∧ ∀ a, m (F.e a) = G.e a := by
  intro K V _ _ _ _ _ _ _ _ H hK r F G aa Λ hU hF hS _ haa hz hz'
  have hFF : SameGr F F := fun a => by simp
  obtain ⟨y, hy, hyz, hyΛ⟩ := exists_hyp hK F hU (aa := aa)
    (fun a t x hx h => hF.1 a ▸ mem_lead hFF a.castSucc hx h) (fun a t ht => (haa a t ht).1)
    (fun t x hx h => hF.2 ▸ mem_lead hFF (Fin.last r) hx h) hz
  obtain ⟨y', hy', hyz', hyΛ'⟩ := exists_hyp hK G hU (aa := aa)
    (fun a t x hx h => hF.1 a ▸ mem_lead hS a.castSucc hx h) (fun a t ht => (haa a t ht).2)
    (fun t x hx h => hF.2 ▸ mem_lead hS (Fin.last r) hx h) hz'
  set e : Fin r → V := fun a => F.e a.castSucc with he
  set e' : Fin r → V := fun a => G.e a.castSucc with he'
  have hX : F.X = Submodule.span K (Set.range e) := x_eq_span F
  have hX' : F.X = Submodule.span K (Set.range e') := (AdaptInv.x_eq hS).symm.trans (x_eq_span G)
  have heX : ∀ a, e a ∈ F.X := fun a => hX ▸ Submodule.subset_span ⟨a, rfl⟩
  have heX' : ∀ a, e' a ∈ F.X := fun a => hX' ▸ Submodule.subset_span ⟨a, rfl⟩
  set M := move H e y e' y' with hM
  have hiso : ∀ v w, H.B (M v) (M w) = H.B v w := move_isom hy hy' fun a => hX ▸ heX' a
  have hinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact H.nondeg v fun w => by rw [← hiso, hv]; simp
  have hbij : Function.Bijective M := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  have hee : ∀ x ∈ Λ, ∀ a, H.B x (y a) • e a ∈ Λ := fun x hx a => (haa a _ (hyΛ x hx a)).1
  have hee' : ∀ x ∈ Λ, ∀ a, H.B x (y a) • e' a ∈ Λ := fun x hx a => (haa a _ (hyΛ x hx a)).2
  have he'e : ∀ x ∈ Λ, ∀ a, H.B x (y' a) • e a ∈ Λ := fun x hx a => (haa a _ (hyΛ' x hx a)).1
  have he'e' : ∀ x ∈ Λ, ∀ a, H.B x (y' a) • e' a ∈ Λ := fun x hx a => (haa a _ (hyΛ' x hx a)).2
  have hmid : ∀ e y : Fin r → V, (∀ x ∈ Λ, ∀ a, H.B x (y a) • e a ∈ Λ) → ∀ x ∈ Λ, mid H e y x ∈ Λ := by
    intro e y h x hx
    rw [mid_apply]
    exact Λ.sub_mem (Λ.sub_mem hx (Λ.sum_mem fun a _ => h x hx a))
      (Λ.sum_mem fun a _ => smul_dual_mem hU (fun x' hx' => h x' hx' a) hx)
  have hMΛ : ∀ x ∈ Λ, M x ∈ Λ := by
    intro x hx
    rw [hM, move_apply]
    exact Λ.add_mem (Λ.add_mem (Λ.sum_mem fun a _ => hee' x hx a)
      (Λ.sum_mem fun a _ => smul_dual_mem hU (fun x' hx' => he'e x' hx' a) hx)) (hmid _ _ he'e' _ (hmid _ _ hee x hx))
  have hMe : ∀ a, M (e a) = e' a := by
    intro a
    rw [hM, move_apply, hy.mid_span (Submodule.subset_span ⟨a, rfl⟩)]
    simp [hy.1, hy.2.2]
  have hMz : M F.z = G.z := by
    have h1 : ∀ a, H.B F.z (e a) = 0 := fun a => swap_zero (F.zperp a)
    have h2 : ∀ a, H.B G.z (e' a) = 0 := fun a => swap_zero (G.zperp a)
    have h3 : mid H e y F.z = F.z := by simp [mid_apply, h1, hyz]
    have h4 : mid H e' y' G.z = G.z := by simp [mid_apply, h2, hyz']
    have h5 : mid H e' y' (G.z - F.z) = 0 := hy'.mid_span (hX' ▸ hS (Fin.last r))
    rw [map_sub, h4, sub_eq_zero] at h5
    rw [hM, move_apply, h3, ← h5]
    simp [h1, hyz]
  refine ⟨LinearEquiv.ofBijective M hbij, ⟨hiso, hbij, fun a => ?_, fun v hv => ?_⟩, ?_, fun a => ?_⟩
  · change M (e a) - e a ∈ _
    rw [hMe]
    exact hS a.castSucc
  · change M v - v ∈ _
    have hv' : ∀ a, H.B v (e a) = 0 := fun a => swap_zero (hv a)
    have hp : ∀ a, H.B (mid H e y v) (e' a) = 0 := fun a => perp_of_span (hy.mid_e v) (hX ▸ heX' a)
    have : M v - v = ∑ a, H.B v (y a) • e' a - ∑ a, H.B v (y a) • e a - ∑ a, H.B (mid H e y v) (y' a) • e' a := by
      rw [hM, move_apply, mid_apply e' y']
      simp only [hp, hv', zero_smul, Finset.sum_const_zero]
      nth_rewrite 1 [mid_apply e y v]
      simp only [hv', zero_smul, Finset.sum_const_zero]
      abel
    rw [this]
    exact F.X.sub_mem (F.X.sub_mem (F.X.sum_mem fun a _ => F.X.smul_mem _ (heX' a))
      (F.X.sum_mem fun a _ => F.X.smul_mem _ (heX a))) (F.X.sum_mem fun a _ => F.X.smul_mem _ (heX' a))
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hMΛ x hx
    · intro x hx
      obtain ⟨v, rfl⟩ := hbij.2 x
      refine ⟨v, ?_, rfl⟩
      refine (mem_iff_pair hU v).2 fun x' hx' => ?_
      rw [← hiso]
      exact (mem_iff_pair hU _).1 hx _ (hMΛ x' hx')
  · change M (F.e a) = _
    induction a using Fin.lastCases with
    | last => exact hMz
    | cast a => exact hMe a
end GlobalTheory.DegAsm.FrameMove
