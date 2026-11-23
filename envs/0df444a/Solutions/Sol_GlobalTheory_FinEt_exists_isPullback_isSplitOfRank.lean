-- Prove2me | solution 1 for GlobalTheory.FinEt.exists_isPullback_isSplitOfRank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:31.981218+00:00
-- url     : https://prove2.me/submissions/7eeeafc4-e3b6-41f8-8f56-00db501df5f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_range_of_isPullback
import Theorems.Thm_GlobalTheory_FinEt_finrank_eq_add
import Theorems.Thm_GlobalTheory_FinEt_isPullback_section
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_of_isPullback
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_of_isPullback_of_isPullback
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_zero_iff
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}
namespace GlobalTheory.FinEt
theorem _root_.solution (n : ℕ) {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p]
    [Etale p] (hn : ∀ s, p.finrank s = n) :
    ∃ (S' X' : Scheme.{u}) (t : S' ⟶ S) (a : X' ⟶ X) (q : X' ⟶ S'),
      IsFinite t ∧ Etale t ∧ Surjective t ∧ IsPullback a q p t ∧ IsSplitOfRank q n := by
  induction n generalizing X S with
  | zero =>
    refine ⟨S, X, 𝟙 S, 𝟙 X, p, inferInstance, inferInstance, inferInstance,
      IsPullback.of_horiz_isIso ⟨by simp⟩, (isSplitOfRank_zero_iff p).mpr ⟨fun x ↦ ?_⟩⟩
    have := p.one_le_finrank_map x
    rw [hn] at this
    omega
  | succ n ih =>
    have hp : Surjective p := p.one_le_finrank_iff_surjective.mp fun s ↦ by simp [hn]
    let σ := pullback.diagonal p
    have hσ : σ ≫ pullback.snd p p = 𝟙 X := pullback.diagonal_snd p
    obtain ⟨S', X', t, a, q, h1, h2, h3, H, hq⟩ := ih ((complOpen σ).ι ≫ pullback.snd p p)
      fun x ↦ by
        have := finrank_eq_add σ (complOpen σ).ι (range_complOpen_ι σ) (pullback.snd p p) x
        rw [hσ, Scheme.Hom.finrank_eq_one_of_isIso (𝟙 X), Scheme.Hom.finrank_pullback_snd, hn,
          Pi.one_apply] at this
        omega
    have G := IsPullback.of_hasPullback (pullback.snd p p) t
    have Gσ := isPullback_section G σ hσ
    have Gj := IsPullback.of_hasPullback (complOpen σ).ι (pullback.fst (pullback.snd p p) t)
    refine ⟨S', _, t ≫ p, _, _, inferInstance, inferInstance, inferInstance,
      G.paste_horiz (IsPullback.of_hasPullback p p), ?_⟩
    have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) Gσ.flip inferInstance
    refine IsSplitOfRank.succ (G.lift (t ≫ σ) (𝟙 _) _) (G.lift_snd _ _ _)
      (pullback.snd (complOpen σ).ι _) ?_
      (hq.of_isPullback_of_isPullback H (Gj.paste_vert G))
    rw [Scheme.Pullback.range_snd, range_of_isPullback Gσ, range_complOpen_ι, Set.preimage_compl]
end GlobalTheory.FinEt
