-- Prove2me | solution 1 for GlobalTheory.FinEt.isIso_coprodDesc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:11.181798+00:00
-- url     : https://prove2.me/submissions/6376a7ac-2c86-483d-9494-e7da4c95b9fc

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
theorem _root_.solution {U V X : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i]
    [IsOpenImmersion j] (h : Set.range j = (Set.range i)ᶜ) : IsIso (coprod.desc i j) := by
  obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl i j (by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor <;> ext1 <;> simp [h])
  have : coprod.desc i j = ((coprodIsCoprod _ _).coconePointUniqueUpToIso hc).hom := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc]
      exact ((coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom hc ⟨.left⟩).symm
    · rw [coprod.inr_desc]
      exact ((coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom hc ⟨.right⟩).symm
  rw [this]
  exact Iso.isIso_hom _
end GlobalTheory.FinEt
