-- Prove2me | solution 1 for GlobalTheory.UnitVectorStabEq.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:14:38.679692+00:00
-- url     : https://prove2.me/submissions/5ae804e7-4c8f-4ec8-be74-bf994f171bfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_hform_sub_smul
import Theorems.Thm_GlobalTheory_UnitVectorStabEq_mem_perpLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
open GlobalTheory GlobalTheory.UnitVectorStabEq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.UnitVectorStabEq
theorem _root_.solution (L : Submodule (OEv F E v) (Fin M → Ev F E v)) (hL : IsSDLat σ J v L)
    (x : Fin M → Ev F E v) (hx : x ∈ L) (b : Ev F E v) (hb : b ∈ OEv F E v)
    (hb1 : hR (Fv F v) σ J x x * b = 1) (y : Fin M → Ev F E v) :
    y ∈ L ↔ (b * hR (Fv F v) σ J x y ∈ OEv F E v ∧
      y - (b * hR (Fv F v) σ J x y) • x ∈ perpLat σ J v L x) := by
  have hs : ∀ a ∈ OEv F E v, a • x ∈ L := fun a ha => L.smul_mem (⟨a, ha⟩ : OEv F E v) hx
  constructor
  · intro hy
    have ha : b * hR (Fv F v) σ J x y ∈ OEv F E v := mul_mem hb (((hL.2.2 y).1 hy).2 x hx)
    refine ⟨ha, (mem_perpLat σ J v L x _).2 ⟨?_, L.sub_mem hy (hs _ ha)⟩⟩
    have h : hR (Fv F v) σ J x (y - (b * hR (Fv F v) σ J x y) • x) =
        hR (Fv F v) σ J x y - (b * hR (Fv F v) σ J x y) * hR (Fv F v) σ J x x :=
      hform_sub_smul _ _ _ _ _
    rw [h]
    linear_combination (- hR (Fv F v) σ J x y) * hb1
  · rintro ⟨ha, hy⟩
    have := L.add_mem ((mem_perpLat σ J v L x _).1 hy).2 (hs _ ha)
    rwa [sub_add_cancel] at this
end GlobalTheory.UnitVectorStabEq
