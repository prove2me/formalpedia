-- Prove2me | solution 1 for GlobalTheory.VectorInclusion.lamAf_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:22:20.302796+00:00
-- url     : https://prove2.me/submissions/d58092bd-43b3-4392-886c-26a35388351c

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InclEIntMem
import Theorems.Thm_GlobalTheory_VectorInclusion_vecIncl_add
import Theorems.Thm_GlobalTheory_VectorInclusion_vecIncl_zero
import Theorems.Thm_GlobalTheory_VectorInclusion_vecIncl_smul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField
open scoped TensorProduct
noncomputable section
open Classical
open GlobalTheory GlobalTheory.VectorInclusion
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace GlobalTheory.VectorInclusion
theorem _root_.solution (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) := by
  obtain ⟨s, hs⟩ := hL
  refine ⟨s.image (vecIncl (F := F)), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    have hxL : x ∈ L := hs ▸ Submodule.subset_span hx
    exact ⟨⟨x, hxL⟩, rfl⟩
  · unfold Formalism.MainNotions.S.lamAf
    rw [Submodule.span_le]
    rintro y ⟨⟨x, hx⟩, rfl⟩
    have key : ∀ z ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)),
        vecIncl (F := F) z ∈ Submodule.span (Formalism.MainNotions.S.IntAf F E)
          ((s.image (vecIncl (F := F)) : Finset _) : Set (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        apply Submodule.subset_span
        simp only [Finset.coe_image]
        exact ⟨z, hz, rfl⟩
      | zero => rw [vecIncl_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [vecIncl_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [vecIncl_smul]; exact Submodule.smul_mem _ _ ha
    rw [← hs] at hx
    exact key x hx
end GlobalTheory.VectorInclusion
