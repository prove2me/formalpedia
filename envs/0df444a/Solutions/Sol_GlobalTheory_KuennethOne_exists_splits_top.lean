-- Prove2me | solution 1 for GlobalTheory.KuennethOne.exists_splits_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:33:48.160099+00:00
-- url     : https://prove2.me/submissions/9661ac11-e10a-4681-bbd8-0bb5bc7a023c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenInfOfIsSeparated
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_exists_isDiff
import Theorems.Thm_GlobalTheory_KuennethOne_pull_coboundary
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_GlobalTheory_KuennethOne_splits_glue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KuennethOne
open TopologicalSpace TensorProduct
variable {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
  (H : IsPullback p q iX iY) {I : Type} {V : I → Z.Opens} {φ : ∀ a b, Γ(Z, V a ⊓ V b)}
include H
namespace GlobalTheory.KuennethOne
theorem _root_.solution [IsAffine S] [Flat iY] [CompactSpace X] [QuasiSeparatedSpace X]
    (hY : ∀ U U' : Y.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hiX : Function.Bijective iX.appTop.hom) {t : Y ⟶ Z} (ht : t ≫ q = 𝟙 Y)
    (hV : ⨆ a, V a = ⊤) (ρ : ∀ a, Γ(Y, t ⁻¹ᵁ V a))
    (hρ : ∀ a b, (t.app (V a ⊓ V b)).hom (φ a b) =
      rs (t.preimage_mono inf_le_left) (ρ a) - rs (t.preimage_mono inf_le_right) (ρ b))
    (hτ : ∀ W : Y.affineOpens, ∃ τ, Splits V φ (q ⁻¹ᵁ W.1) τ) : ∃ χ, Splits V φ ⊤ χ := by
  choose τ hτ using hτ
  have hN : ∀ N : Y.Opens, N ≤ t ⁻¹ᵁ (q ⁻¹ᵁ N) := by
    intro N
    rw [← Scheme.Hom.comp_preimage, ht]
    exact le_rfl
  have hN' : ∀ N : Y.Opens, N ≤ (𝟙 Y : Y ⟶ Y) ⁻¹ᵁ N := fun N => le_rfl
  obtain ⟨x, hx⟩ := pull_coboundary hV t ρ hρ (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ
    (fun j => j.1) (fun j => hN _)
  refine splits_glue (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ
    (fun j => (q.appLE j.1 _ le_rfl).hom (x j)) ?_ ⊤ ?_
  · intro j k a M hj hk ha
    have hW' := hY _ _ j.2 k.2
    have m1 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1 := q.preimage_mono inf_le_left
    have m2 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1 := q.preimage_mono inf_le_right
    obtain ⟨e, he⟩ := exists_isDiff hV (hτ j) (hτ k) m1 m2
    have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := j.1 ⊓ k.1) (UX := ⊤)
      (UY := q ⁻¹ᵁ (j.1 ⊓ k.1)) le_top le_top (by simp)).1
      (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _) hW'
        (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ))
    have : IsIso (iX.appLE ⊤ ⊤ le_top) := by
      have e : iX.appTop = iX.appLE ⊤ ⊤ le_top := iX.app_eq_appLE (U := ⊤)
      rw [← e]
      exact (ConcreteCategory.isIso_iff_bijective _).mpr hiX
    have hiso := po.isIso_inr_of_isIso
    obtain ⟨u, hu⟩ := (ConcreteCategory.bijective_of_isIso
      (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl)).2 e
    have hu' : (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl).hom u = e := hu
    have h1 := hx j k _ m1 m2 e he (j.1 ⊓ k.1) inf_le_left inf_le_right (hN _)
    rw [← hu', appLE_appLE t q _ ht _ _ (hN' _), id_appLE, rs_self] at h1
    have hM : M ≤ q ⁻¹ᵁ (j.1 ⊓ k.1) := by rw [q.preimage_inf]; exact le_inf hj hk
    have h2 := he a M hM ha
    rw [← hu', h1] at h2
    simp only [map_sub, appLE_rs, rs_appLE] at h2 ⊢
    exact h2.symm
  · rw [← q.preimage_iSup, iSup_affineOpens_eq_top]
    exact le_top
end GlobalTheory.KuennethOne
