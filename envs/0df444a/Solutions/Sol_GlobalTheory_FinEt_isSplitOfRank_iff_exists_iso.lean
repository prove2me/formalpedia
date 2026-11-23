-- Prove2me | solution 1 for GlobalTheory.FinEt.isSplitOfRank_iff_exists_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:07.280352+00:00
-- url     : https://prove2.me/submissions/025d6ef8-666b-4bf6-91f2-b13b13f17717

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed

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
theorem _root_.solution {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ) :
    IsSplitOfRank p n ↔
      ∃ e : (∐ fun _ : Fin n ↦ S) ≅ X, e.hom ≫ p = Sigma.desc fun _ : Fin n ↦ 𝟙 S := by
  constructor
  · rintro ⟨s, hs, hc⟩
    have : IsIso (Sigma.desc s) := (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hc
    exact ⟨asIso (Sigma.desc s), Sigma.hom_ext _ _ fun i ↦ by simp [hs]⟩
  · rintro ⟨e, he⟩
    refine ⟨fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom, fun i ↦ by simp [he], ?_⟩
    rw [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc]
    have : Sigma.desc (fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom) = e.hom :=
      Sigma.hom_ext _ _ fun i ↦ by simp
    change IsIso (Sigma.desc fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom)
    rw [this]
    infer_instance
end GlobalTheory.FinEt
