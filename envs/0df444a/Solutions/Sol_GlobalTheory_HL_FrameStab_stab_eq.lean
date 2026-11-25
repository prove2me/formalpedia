-- Prove2me | solution 1 for GlobalTheory.HL.FrameStab.stab_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:18:02.258376+00:00
-- url     : https://prove2.me/submissions/25d2dda2-b68a-42ce-9ee2-3c468105bf82

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Theorems.Thm_GlobalTheory_HL_FrameStab_hf_sum_l
import Theorems.Thm_GlobalTheory_HL_FrameStab_isom_span
import Theorems.Thm_GlobalTheory_HL_FrameStab_spanTo_top
import Theorems.Thm_GlobalTheory_HL_FrameStab_pair_eq
import Theorems.Thm_GlobalTheory_HL_FrameStab_gram_eq
import Theorems.Thm_GlobalTheory_HL_FrameStab_mem_Nof
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_HL_FrameOnto_coords
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameStab
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
namespace GlobalTheory.HL.FrameStab
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ h ∈ S.St, ∀ w ∈ S.W0, h w = w) ∧ ∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) → ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) → (cT L s * S.Zh * s' = S.Zh ↔ ∃ h ∈ S.St, (∀ j, h (S.f j) = ∑ i, s i j • S.f i) ∧ ∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hli, hco, -, hU, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hU' : IsUnit S.Zh.det := hU
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    rw [Frames.ME, spanTo_top, spanTo_top, Set.Sum.elim_range, Submodule.span_union]
  refine ⟨fun h hh w hw => ?_, fun s s' hs hs' => ⟨fun hz => ?_, ?_⟩⟩
  · have hd := (linearIndependent_sum.1 hli).2.2
    have h1 : h w - w ∈ S.spanTo S.f r := hh.1.2.2 w fun y hy =>
      hw y (Submodule.mem_sup_left (spanTo_mono S _ (Nat.le_succ _) hy))
    have h2 : h w - w ∈ S.spanTo S.f' r := hh.2.2.2 w fun y hy =>
      hw y (Submodule.mem_sup_right (spanTo_mono S _ (Nat.le_succ _) hy))
    have h3 := spanTo_mono S _ (Nat.le_succ _) h1
    have h4 := spanTo_mono S _ (Nat.le_succ _) h2
    rw [spanTo_top] at h3 h4
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h3 h4)
  · have hco' := hco
    rw [hME] at hco'
    let t : Fin (r + 1) ⊕ Fin (r + 1) → S.V :=
      Sum.elim (fun j => ∑ i, s i j • S.f i) (fun j => ∑ i, s' i j • S.f' i)
    let φ : S.V →ₗ[E] S.V :=
      LinearMap.ofIsCompl hco' ((Module.Basis.span hli).constr E t) S.W0.subtype
    have hφ1 : ∀ i, φ (Sum.elim S.f S.f' i) = t i := by
      intro i
      have h1 := LinearMap.ofIsCompl_apply_left hco' (φ := (Module.Basis.span hli).constr E t)
        (ψ := S.W0.subtype) (Module.Basis.span hli i)
      rw [Module.Basis.constr_basis, Module.Basis.span_apply] at h1
      exact h1
    have hφ2 : ∀ w ∈ S.W0, φ w = w := fun w hw =>
      LinearMap.ofIsCompl_apply_right hco' (φ := (Module.Basis.span hli).constr E t)
        (ψ := S.W0.subtype) ⟨w, hw⟩
    have hmem : ∀ i, Sum.elim S.f S.f' i ∈ S.ME := fun i => hME ▸ Submodule.subset_span ⟨i, rfl⟩
    have htm : ∀ i, t i ∈ S.ME := by
      rintro (j | j)
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem (Sum.inl i))
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem (Sum.inr i))
    have hmix : ∀ a b, hf L S.Hm (t (Sum.inr b)) (t (Sum.inl a)) = hf L S.Hm (S.f' b) (S.f a) := by
      intro a b
      have := pair_eq S s s' a b
      rw [hz] at this
      exact this
    have hiso : ∀ x y, hf L S.Hm (φ x) (φ y) = hf L S.Hm x y := by
      have h1 := isom_span L S.Hm φ (Set.range (Sum.elim S.f S.f') ∪ S.W0) (by
        rintro _ (⟨i, rfl⟩ | hx) _ (⟨j, rfl⟩ | hy)
        · rw [hφ1, hφ1]
          rcases i with i | i <;> rcases j with j | j
          · exact gram_eq S S.f S.T S.gram s hs i j
          · rw [← hf_cj L S.herm.1, hmix, hf_cj L S.herm.1]; rfl
          · exact hmix j i
          · exact gram_eq S S.f' S.T' S.gram' s' hs' i j
        · rw [hφ1, hφ2 _ hy, ← hf_cj L S.herm.1, hy _ (htm i), ← hf_cj L S.herm.1 _ (Sum.elim _ _ _),
            hy _ (hmem i)]
        · rw [hφ1, hφ2 _ hx, hx _ (htm j), hx _ (hmem j)]
        · rw [hφ2 _ hx, hφ2 _ hy])
      rw [Submodule.span_union, Submodule.span_eq, hco'.sup_eq_top] at h1
      exact fun x y => h1 x trivial y trivial
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      apply Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 S.herm.2)
      funext j
      have h1 := hiso v (Pi.single j 1)
      rw [hv] at h1
      simpa [hf, Pi.single_apply, Matrix.vecMul, dotProduct, apply_ite L.cj] using h1.symm
    let h : S.GLV := LinearEquiv.ofBijective φ (IsArtinian.bijective_of_injective_endomorphism φ hinj)
    have hg : ∀ j, h (S.f j) = ∑ i, s i j • S.f i := fun j => hφ1 (Sum.inl j)
    have hg' : ∀ j, h (S.f' j) = ∑ i, s' i j • S.f' i := fun j => hφ1 (Sum.inr j)
    refine ⟨h, ⟨?_, ?_⟩, hg, hg'⟩
    · refine mem_Nof S S.f S.f' S.T S.gram S.W0 (fun w hw y hy => hw y (Submodule.mem_sup_left hy))
        hco.sup_eq_top ?_ s s' hs hs' h hiso hg hg' hφ2
      intro u hu h0
      obtain ⟨c, -, rfl⟩ := coords S _ hu
      have : c = 0 := by
        apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
        funext a
        have h1 := h0 _ (mem_spanTo S S.f a.2)
        rw [hf_sum_l] at h1
        rw [Matrix.mulVec_zero, Pi.zero_apply, ← h1]
        unfold Matrix.mulVec dotProduct
        exact Finset.sum_congr rfl fun b _ => mul_comm _ _
      simp [this]
    · refine mem_Nof S S.f' S.f S.T' S.gram' S.W0 (fun w hw y hy => hw y (Submodule.mem_sup_right hy))
        (by rw [sup_comm (S.spanTo S.f' _)]; exact hco.sup_eq_top) ?_ s' s hs' hs h hiso hg' hg hφ2
      intro u hu h0
      obtain ⟨c, -, rfl⟩ := coords S _ hu
      have : (fun i => L.cj (c i)) = 0 := by
        apply Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
        funext a
        have h1 := congrArg L.cj (h0 _ (mem_spanTo S S.f' a.2))
        rw [hf_sum_l, map_zero, map_sum] at h1
        simp only [map_mul, hf_cj L S.herm.1] at h1
        simp only [Matrix.zero_vecMul, Pi.zero_apply]
        exact h1
      have h2 : ∀ i, c i = 0 := fun i => by simpa using congrFun this i
      simp [h2]
  · rintro ⟨h, hh, h1, h2⟩
    ext a b
    rw [← pair_eq, ← h1, ← h2]
    exact hh.1.1.1 _ _
end GlobalTheory.HL.FrameStab
