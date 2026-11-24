-- Prove2me | solution 1 for GlobalTheory.AffineThickening.isAffine_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:18.341832+00:00
-- url     : https://prove2.me/submissions/638ab904-e60a-4750-a9e7-2c0a72ea0d98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_add
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_mul
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_zero
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_zero_iff
import Theorems.Thm_GlobalTheory_AffineThickening_eq_of_preimage_eq
import Theorems.Thm_GlobalTheory_AffineThickening_Lifts_basicOpen_eq
import Theorems.Thm_GlobalTheory_AffineThickening_isAffineOpen_inf
import Theorems.Thm_GlobalTheory_AffineThickening_IsCoboundary_mul
import Theorems.Thm_GlobalTheory_AffineThickening_IsCoboundary_add
import Theorems.Thm_GlobalTheory_AffineThickening_exists_lifts_top_of_cover

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
namespace GlobalTheory.AffineThickening
theorem _root_.solution (i : Z ⟶ Y) [IsClosedImmersion i] [Surjective i] [IsAffine Z]
    (hK : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U),
      (i.app U).hom a = 0 → (i.app U).hom b = 0 → a * b = 0) : IsAffine Y := by
  have hK' : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U),
      Lifts i U a 0 → Lifts i U b 0 → a * b = 0 :=
    fun U hU a b ha hb ↦ hK U hU a b (Lifts.zero_iff.1 ha) (Lifts.zero_iff.1 hb)
  have hD : ∀ r : Γ(Z, ⊤), ∃ D : Y.Opens, i ⁻¹ᵁ D = Z.basicOpen r := fun r ↦ by
    obtain ⟨O, hO, hO'⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp (Z.basicOpen r).isOpen
    exact ⟨⟨O, hO⟩, Opens.ext hO'⟩
  choose D hD using hD
  have hS : Ideal.span {r | IsAffineOpen (D r)} = ⊤ := by
    rw [← (isAffineOpen_top Z).iSup_basicOpen_eq_self_iff, eq_top_iff]
    intro z _
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i z)) isOpen_univ
    obtain ⟨r, hr, hz⟩ := (isAffineOpen_top Z).exists_basicOpen_le (V := i ⁻¹ᵁ W) ⟨z, hzW⟩ trivial
    have e : W ⊓ D r = D r := eq_of_preimage_eq (i := i) (by
      rw [Scheme.Hom.preimage_inf, hD, inf_eq_right.2 hr])
    exact Opens.mem_iSup.2 ⟨⟨r, show IsAffineOpen (D r) from e ▸ isAffineOpen_inf hW (hD r)⟩, hz⟩
  obtain ⟨T, hT, hT'⟩ := (Ideal.span_eq_top_iff_finite _).1 hS
  have hsurj : ∀ s, ∃ a, Lifts i ⊤ a s :=
    exists_lifts_top_of_cover (ι := T) (f := fun r ↦ r.1) (U := fun r ↦ D r.1) hK'
      (fun r ↦ hT r.2) (fun r ↦ hD _) (by simpa using hT')
  choose g hg using hsurj
  refine isAffine_of_isAffineOpen_basicOpen (g '' T) ?_ ?_
  · have key : ∀ r ∈ Ideal.span (T : Set Γ(Z, ⊤)), ∃ a ∈ Ideal.span (g '' T), Lifts i ⊤ a r := by
      intro r hr
      induction hr using Submodule.span_induction with
      | mem x h => exact ⟨g x, Ideal.subset_span ⟨x, h, rfl⟩, hg x⟩
      | zero => exact ⟨0, zero_mem _, Lifts.zero⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, ha'⟩ := hx
        obtain ⟨b, hb, hb'⟩ := hy
        exact ⟨a + b, add_mem ha hb, ha'.add hb'⟩
      | smul c x _ hx =>
        obtain ⟨a, ha, ha'⟩ := hx
        exact ⟨g c * a, Ideal.mul_mem_left _ _ ha, (hg c).mul ha'⟩
    obtain ⟨a, ha, ha'⟩ := key 1 (hT' ▸ Submodule.mem_top)
    refine Ideal.eq_top_of_isUnit_mem _ ha ?_
    have e : Y.basicOpen a = ⊤ := by
      rw [← ha'.basicOpen_eq (D := ⊤) (by simp), top_inf_eq]
    refine Y.toRingedSpace.isUnit_of_isUnit_germ ⊤ a fun x hx ↦ ?_
    exact (Y.mem_basicOpen a x hx).1 (e.ge hx)
  · rintro _ ⟨r, hr, rfl⟩
    rw [← (hg r).basicOpen_eq (hD r), top_inf_eq]
    exact hT hr
end GlobalTheory.AffineThickening
