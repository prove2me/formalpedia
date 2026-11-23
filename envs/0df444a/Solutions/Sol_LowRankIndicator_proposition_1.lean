-- Prove2me | solution 1 for LowRankIndicator.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:34:13.253166+00:00
-- url     : https://prove2.me/submissions/92769338-1083-44ec-bd8c-a9f4fd01720f

import Mathlib
import Definitions.Def_VectorSpaceOpt_support_functional

set_option autoImplicit false

namespace LowRankIndicator.Prop1Proof

theorem supp_mono {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : Set E} (hAB : A ⊆ B) (φ : E →L[ℝ] ℝ) :
    VectorSpaceOpt_support_functional A φ ≤ VectorSpaceOpt_support_functional B φ :=
  iSup_le fun x => le_iSup_of_le ⟨x.1, hAB x.2⟩ le_rfl

theorem supp_closure_convexHull {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Set E) (φ : E →L[ℝ] ℝ) :
    VectorSpaceOpt_support_functional (closure (convexHull ℝ S)) φ =
      VectorSpaceOpt_support_functional S φ := by
  apply le_antisymm
  · cases hM : VectorSpaceOpt_support_functional S φ using EReal.rec with
    | top => exact le_top
    | bot =>
      have hSempty : S = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have hle : ((φ x : ℝ) : EReal) ≤ ⊥ :=
          hM ▸ le_iSup (fun k : S => ((φ k.1 : ℝ) : EReal)) ⟨x, hx⟩
        exact not_le_of_gt (EReal.bot_lt_coe (φ x)) hle
      subst hSempty
      simp [VectorSpaceOpt_support_functional]
    | coe m =>
      have hSH : S ⊆ {z : E | φ z ≤ m} := by
        intro x hx
        have hle : ((φ x : ℝ) : EReal) ≤ (m : EReal) :=
          hM ▸ le_iSup (fun k : S => ((φ k.1 : ℝ) : EReal)) ⟨x, hx⟩
        exact EReal.coe_le_coe_iff.mp hle
      have hHconv : Convex ℝ {z : E | φ z ≤ m} := by
        intro x hx y hy a b ha hb hab
        simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at hx hy ⊢
        have h1 : a * φ x ≤ a * m := mul_le_mul_of_nonneg_left hx ha
        have h2 : b * φ y ≤ b * m := mul_le_mul_of_nonneg_left hy hb
        have h3 : a * m + b * m = m := by rw [← add_mul, hab, one_mul]
        linarith
      have hHclosed : IsClosed {z : E | φ z ≤ m} :=
        isClosed_le φ.continuous continuous_const
      have hsub : closure (convexHull ℝ S) ⊆ {z : E | φ z ≤ m} :=
        closure_minimal (convexHull_min hSH hHconv) hHclosed
      exact iSup_le fun x => EReal.coe_le_coe_iff.mpr (hsub x.2)
  · exact supp_mono ((subset_convexHull ℝ S).trans subset_closure) φ

theorem subset_of_supp_le {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : Set E} (hBconv : Convex ℝ B) (hBclosed : IsClosed B)
    (hle : ∀ φ : E →L[ℝ] ℝ,
      VectorSpaceOpt_support_functional A φ ≤ VectorSpaceOpt_support_functional B φ) :
    A ⊆ B := by
  intro x hxA
  by_contra hxB
  obtain ⟨φ, u, hux, hBu⟩ := geometric_hahn_banach_point_closed hBconv hBclosed hxB
  have hsuppB : VectorSpaceOpt_support_functional B (-φ) ≤ ((-u : ℝ) : EReal) :=
    iSup_le fun b => EReal.coe_le_coe_iff.mpr (by simp; linarith [hBu b.1 b.2])
  have hφx : (((-φ) x : ℝ) : EReal) ≤ ((-u : ℝ) : EReal) :=
    (le_iSup (fun a : A => (((-φ) a.1 : ℝ) : EReal)) ⟨x, hxA⟩).trans ((hle (-φ)).trans hsuppB)
  have hle_real : -φ x ≤ -u := EReal.coe_le_coe_iff.mp hφx
  linarith

end LowRankIndicator.Prop1Proof

open LowRankIndicator.Prop1Proof in
theorem solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (S T : Set E)
    (hTclosed : IsClosed T) (hTconvex : Convex ℝ T) :
    T = closure (convexHull ℝ S) ↔
      ∀ φ : E →L[ℝ] ℝ,
        VectorSpaceOpt_support_functional T φ = VectorSpaceOpt_support_functional S φ := by
  constructor
  · rintro rfl φ
    exact supp_closure_convexHull S φ
  · intro hφ
    have heq : ∀ φ : E →L[ℝ] ℝ,
        VectorSpaceOpt_support_functional T φ =
          VectorSpaceOpt_support_functional (closure (convexHull ℝ S)) φ :=
      fun φ => (hφ φ).trans (supp_closure_convexHull S φ).symm
    exact Set.Subset.antisymm
      (subset_of_supp_le (convex_convexHull ℝ S).closure isClosed_closure fun φ => (heq φ).le)
      (subset_of_supp_le hTconvex hTclosed fun φ => (heq φ).ge)
