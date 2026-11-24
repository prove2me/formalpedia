-- Prove2me | solution 1 for GlobalTheory.AffineThickening.exists_lifts_top_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:35:08.618962+00:00
-- url     : https://prove2.me/submissions/0ef244d1-3aad-4a7b-808e-c2ef8f527198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_rs_rs
import Theorems.Thm_GlobalTheory_AffineThickening_app_rs
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_res
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_sub
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_one
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_sub_zero
import Theorems.Thm_GlobalTheory_AffineThickening_eq_of_preimage_eq
import Theorems.Thm_GlobalTheory_AffineThickening_exists_lifts
import Theorems.Thm_GlobalTheory_AffineThickening_isAffineOpen_inf
import Theorems.Thm_GlobalTheory_AffineThickening_isCoboundary_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
open GlobalTheory GlobalTheory.AffineThickening
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
variable {i}
variable [IsClosedImmersion i] [Surjective i]
  (hK : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U), Lifts i U a 0 → Lifts i U b 0 → a * b = 0)
  {ι : Type*} {f : ι → Γ(Z, ⊤)} {U : ι → Y.Opens} (hU : ∀ j, IsAffineOpen (U j))
  (hD : ∀ j, i ⁻¹ᵁ U j = Z.basicOpen (f j))
  {s : Γ(Z, ⊤)} {σ : ∀ j, Γ(Y, U j)} (hσ : ∀ j, Lifts i (U j) (σ j) s)
include hK hU hD
namespace GlobalTheory.AffineThickening
theorem _root_.solution [IsAffine Z] [Finite ι] (hf : Ideal.span (Set.range f) = ⊤)
    (s : Γ(Z, ⊤)) : ∃ a, Lifts i ⊤ a s := by
  choose σ hσ using fun j ↦ exists_lifts (i := i) (hU j) s
  obtain ⟨ρ, t, hρ, ht, e⟩ := isCoboundary_one hK hU hD hσ hf
  have hZ : ⊤ ≤ ⨆ j, i ⁻¹ᵁ U j := by
    have := ((isAffineOpen_top Z).iSup_basicOpen_eq_self_iff).2 hf
    rw [← this, iSup_le_iff]
    rintro ⟨_, j, rfl⟩
    exact le_iSup_of_le j (hD j).ge
  have hY : ⊤ ≤ ⨆ j, U j := by
    refine (eq_of_preimage_eq (i := i) ?_).le
    rw [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_top]
    exact hZ.antisymm le_top
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hY
    (fun j ↦ σ j - t j) (fun j k ↦ by
      have h0 := hK _ (isAffineOpen_inf (hU j) (hD k)) _ _
        (Lifts.one.sub_zero ((hρ j).res inf_le_left))
        (((hσ j).res inf_le_left).sub_zero ((hσ k).res inf_le_right))
      change rs inf_le_left (σ j - t j) = rs inf_le_right (σ k - t k)
      simp only [map_sub]
      linear_combination h0 - e j k)
  refine ⟨a, Z.sheaf.eq_of_locally_eq' (fun j ↦ i ⁻¹ᵁ U j) (i ⁻¹ᵁ ⊤)
    (fun j ↦ homOfLE (i.preimage_mono le_top)) (le_top.trans hZ) _ _ fun j ↦ ?_⟩
  have h1 : rs le_top a = σ j - t j := ha j
  have h2 : (i.app (U j)).hom (σ j - t j) = rs le_top (s - 0) := (hσ j).sub (ht j)
  rw [← h1, sub_zero] at h2
  exact ((app_rs i le_top a).symm.trans h2).trans (rs_rs le_top _ s).symm
end GlobalTheory.AffineThickening
