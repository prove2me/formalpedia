-- Prove2me | solution 1 for GlobalTheory.FinEt.finiteEtale_open_closed_conditions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:44.776457+00:00
-- url     : https://prove2.me/submissions/6eefe6eb-97df-4d2f-9ecc-d91c5d5ad297

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_GlobalTheory_FinEt_isIso_iff_bijective_algClosed
import Theorems.Thm_GlobalTheory_FinEt_IsSplitOfRank_of_isPullback
import Theorems.Thm_GlobalTheory_FinEt_exists_isSplitOfRank_pullback
import Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_of_isSepClosed
import Theorems.Thm_GlobalTheory_FinEt_isIso_pullback_map_iff_factors
import Theorems.Thm_GlobalTheory_FinEt_pullback_map_eq_iff_factors

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
theorem _root_.solution {S : Scheme.{u}} (X Y : Over S)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    (∀ f : X ⟶ Y, (IsFinite f.left ∧ Etale f.left) ∧ IsClopen (isoLocus f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ S), IsIso ((Over.pullback t).map f) ↔
        ∃ t' : T ⟶ isoLocusOpen f, t' ≫ (isoLocusOpen f).ι = t) ∧
      (IsIso f ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k],
        Function.Bijective fun x : Spec (.of k) ⟶ X.left ↦ x ≫ f.left)) ∧
    (∀ f g : X ⟶ Y, IsClopen (eqLocus f g) ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ S), (Over.pullback t).map f = (Over.pullback t).map g ↔
        ∃ t' : T ⟶ eqLocusOpen f g, t' ≫ (eqLocusOpen f g).ι = t) ∧
    (∀ (k : Type u) [Field k] [IsSepClosed k], Nonempty (S ≅ Spec (.of k)) →
      ∃ n, IsSplitOfRank X.hom n) ∧
    (∀ n : ℕ, (∀ s, X.hom.finrank s = n) → ∃ (S' : Scheme.{u}) (t : S' ⟶ S),
      IsFinite t ∧ Etale t ∧ Surjective t ∧ IsSplitOfRank (pullback.snd X.hom t) n) := by
  refine ⟨fun f ↦ ⟨⟨isFinite_left f, etale_left f⟩, isClopen_isoLocus f,
    fun t ↦ isIso_pullback_map_iff_factors t f, ?_⟩,
    fun f g ↦ ⟨isClopen_eqLocus f g, fun t ↦ pullback_map_eq_iff_factors t f g⟩, ?_,
    fun n hn ↦ exists_isSplitOfRank_pullback X.hom hn⟩
  · have := isFinite_left f
    have := etale_left f
    rw [isIso_iff_isIso_left, isIso_iff_bijective_algClosed]
  · rintro k _ _ ⟨e⟩
    obtain ⟨s⟩ : Nonempty (Spec (.of k)) := inferInstance
    exact ⟨_, (isSplitOfRank_of_isSepClosed (X.hom ≫ e.hom) s).of_isPullback (a := 𝟙 _)
      (t := e.hom) (IsPullback.of_horiz_isIso ⟨by simp⟩)⟩
end GlobalTheory.FinEt
