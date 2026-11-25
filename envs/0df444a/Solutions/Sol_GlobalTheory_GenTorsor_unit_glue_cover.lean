-- Prove2me | solution 1 for GlobalTheory.GenTorsor.unit_glue_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:19.427088+00:00
-- url     : https://prove2.me/submissions/90d82995-469f-4ce6-a185-ebbf96def67e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover
import Theorems.Thm_GlobalTheory_GenTorsor_pb_pb
import Theorems.Thm_GlobalTheory_GenTorsor_pb_congr
import Theorems.Thm_GlobalTheory_GenTorsor_pb_res
import Theorems.Thm_GlobalTheory_GenTorsor_pb_bijective
import Theorems.Thm_GlobalTheory_GenTorsor_unit_glue_opens
import Theorems.Thm_GlobalTheory_GenTorsor_le_iSup_range
import Theorems.Thm_GlobalTheory_GenTorsor_preimage_inf_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]
namespace GlobalTheory.GenTorsor
theorem _root_.solution (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens)
    (u : ∀ i, Γ(T i, a i ⁻¹ᵁ V)ˣ)
    (h : ∀ i j (S : Scheme.{0}) (b : S ⟶ T i) (c : S ⟶ T j), b ≫ a i = c ≫ a j →
      ∀ (hb : ⊤ ≤ b ⁻¹ᵁ a i ⁻¹ᵁ V) (hc : ⊤ ≤ c ⁻¹ᵁ a j ⁻¹ᵁ V),
        pb b _ ⊤ hb (u i) = pb c _ ⊤ hc (u j)) :
    ∃ s : Γ(X, V)ˣ, ∀ i, pb (a i) V _ le_rfl s = u i := by
  choose w hw using fun i => (pb_bijective (a i) inf_le_right (preimage_inf_range a i V)).2 (u i)
  obtain ⟨s, hs⟩ := unit_glue_opens V _ (fun i => inf_le_left) (le_iSup_range a hc V) w (by
    intro i j
    set W := V ⊓ (a i).opensRange ⊓ (V ⊓ (a j).opensRange) with hW
    have hi : Set.range W.ι ⊆ Set.range (a i) := by
      rw [Scheme.Opens.range_ι]; exact fun x hx => hx.1.2
    have hj : Set.range W.ι ⊆ Set.range (a j) := by
      rw [Scheme.Opens.range_ι]; exact fun x hx => hx.2.2
    have ei := IsOpenImmersion.lift_fac (a i) W.ι hi
    have ej := IsOpenImmersion.lift_fac (a j) W.ι hj
    have hT : (⊤ : W.toScheme.Opens) = W.ι ⁻¹ᵁ W := by simp
    have hV : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ V :=
      hT.le.trans (W.ι.preimage_mono (inf_le_left.trans inf_le_left))
    apply (pb_bijective W.ι (U := W) (by simp) hT).1
    have := h i j W _ _ (ei.trans ej.symm)
      (by rw [← Scheme.Hom.comp_preimage, ei]; exact hV)
      (by rw [← Scheme.Hom.comp_preimage, ej]; exact hV)
    rw [← hw, ← hw, pb_pb, pb_pb] at this
    rw [pb_res, pb_res]
    exact (pb_congr ei.symm _ _ _).trans (this.trans (pb_congr ej _ _ _)))
  refine ⟨s, fun i => ?_⟩
  rw [← hw, ← hs, pb_res]
end GlobalTheory.GenTorsor
