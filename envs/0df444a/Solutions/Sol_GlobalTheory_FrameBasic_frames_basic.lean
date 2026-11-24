-- Prove2me | solution 1 for GlobalTheory.FrameBasic.frames_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:08:45.19639+00:00
-- url     : https://prove2.me/submissions/cb719c8b-0ced-4643-9b8e-6c08e1b37e20

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_basis_of_isCompl
import Theorems.Thm_GlobalTheory_FrameBasic_lead_unit
import Theorems.Thm_GlobalTheory_FrameBasic_full_unit
import Theorems.Thm_GlobalTheory_FrameBasic_solve_zero
import Theorems.Thm_GlobalTheory_FrameBasic_hf_conj
import Theorems.Thm_GlobalTheory_FrameBasic_split_of_gram
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) :
    LinearIndependent E (Sum.elim S.f S.f') ∧ IsCompl S.ME S.W0 ∧
    (∃ c : F, c ≠ 0 ∧ S.G = algebraMap F E c) ∧ IsUnit (S.D (Fin.last (r + 1))) ∧
    (∀ l, S.D l ≠ 0 → IsUnit (S.D l)) ∧ S.th ≠ 0 ∧ S.th ∈ 𝒪[F] ∧
    ∃ b : Fin (k - 1) → S.V, LinearIndependent E b ∧ S.W0 = Submodule.span E (Set.range b) := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hZ : S.Zh = Matrix.of fun a b => S.w.mat a b * (-1) ^ (r - (b : ℕ)) := by
    ext a b; exact S.relevant a b
  have hε : ∀ b : Fin (r + 1), IsUnit ((-1 : E) ^ (r - (b : ℕ))) := fun b =>
    (isUnit_one.neg).pow _
  have hD1 : S.D (Fin.last (r + 1)) = S.Zh.det := rfl
  have hD0 : S.D (Fin.last r).castSucc = (S.Zh.submatrix Fin.castSucc Fin.castSucc).det := rfl
  have hU : IsUnit S.Zh.det := by rw [hZ]; exact full_unit _ _ hε
  have hc : ∃ c : F, c ≠ 0 ∧ S.G = algebraMap F E c := by
    have hfix : L.cj S.G = S.G := by
      simp only [Frames.G, map_sub, map_mul, L.cj_cj, AlgEquiv.commutes]; ring
    obtain ⟨c, hc⟩ := (L.cj_fix _).1 hfix
    refine ⟨c, ?_, hc.symm⟩
    rintro rfl
    exact S.G_ne (show S.G = 0 by rw [← hc, map_zero])
  have hGu : IsUnit S.G := by
    obtain ⟨c, h0, hc⟩ := hc
    rw [hc]; exact (IsUnit.mk0 c h0).map _
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    simp only [Frames.ME, Frames.spanTo, hs, Set.image_univ, Set.Sum.elim_range, Submodule.span_union]
  have hdet : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) E), (A.map L.cj).transpose.det = L.cj A.det := by
    intro m A
    rw [Matrix.det_transpose]
    exact (AlgEquiv.map_det L.cj A).symm
  obtain ⟨hli, hco⟩ := split_of_gram L S.herm.1 (Sum.elim S.f S.f') (by
    intro γ hγ
    have := solve_zero S.Zh (S.Zh.map L.cj).transpose (algebraMap F E S.T) (algebraMap F E S.T') hU
      (by rw [hdet]; exact hU.map _)
      (by
        have e : ((S.Zh.map L.cj).transpose.submatrix Fin.castSucc Fin.castSucc) =
          ((S.Zh.submatrix Fin.castSucc Fin.castSucc).map L.cj).transpose := rfl
        rw [e, hdet, hdet, ← map_mul, ← hD0, ← hD1]; exact hGu)
      (fun a => γ (Sum.inl a)) (fun b => γ (Sum.inr b))
      (by
        funext a
        have h1 := hγ (Sum.inl a)
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, S.gram] at h1
        have h2 : S.Zh.mulVec (fun b => γ (Sum.inr b)) a =
            ∑ b, γ (Sum.inr b) * hf L S.Hm (S.f' b) (S.f a) := by
          unfold Matrix.mulVec dotProduct
          exact Finset.sum_congr rfl fun b _ => mul_comm _ _
        rw [h2, Pi.single_apply]
        split_ifs with ha
        · simp [ha] at h1 ⊢
          linear_combination h1
        · simpa [ha] using h1)
      (by
        funext b
        have h1 := hγ (Sum.inr b)
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, S.gram'] at h1
        have h2 : (S.Zh.map L.cj).transpose.mulVec (fun a => γ (Sum.inl a)) b =
            ∑ a, γ (Sum.inl a) * hf L S.Hm (S.f a) (S.f' b) := by
          unfold Matrix.mulVec dotProduct
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hf_conj L S.herm.1]; exact mul_comm _ _
        rw [h2, Pi.single_apply]
        split_ifs with ha
        · simp [ha] at h1 ⊢
          linear_combination h1
        · simpa [ha] using h1)
    funext i
    rcases i with a | b
    · exact congrFun this.1 a
    · exact congrFun this.2 b)
  have hW : S.W0 = perp L S.Hm (Submodule.span E (Set.range (Sum.elim S.f S.f'))) := by
    rw [← hME]; rfl
  refine ⟨hli, by rw [hW, hME]; exact hco, hc, hU, fun l => ?_, ?_, ?_, ?_⟩
  · unfold Frames.D lead
    rw [hZ]
    exact lead_unit _ _ hε _
  · unfold Frames.th
    split_ifs
    · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
    · exact one_ne_zero
  · unfold Frames.th
    split_ifs
    · exact S.ϖ.2
    · exact one_mem _
  · have : Module.Free E (Submodule.span E (Set.range (Sum.elim S.f S.f'))) :=
      Module.Free.of_basis (Module.Basis.span hli)
    obtain ⟨b⟩ := basis_of_isCompl hco
    have hn : Module.finrank E (Fin (k + 2 * r + 1) → E) -
        Module.finrank E (Submodule.span E (Set.range (Sum.elim S.f S.f'))) = k - 1 := by
      rw [Module.finrank_eq_card_basis (Module.Basis.span hli), Module.finrank_fin_fun]
      simp only [Fintype.card_sum, Fintype.card_fin]; omega
    let b' := b.reindex (finCongr hn)
    refine ⟨fun i => (b' i : S.V), b'.linearIndependent.map' (Submodule.subtype _)
      (Submodule.ker_subtype _), ?_⟩
    rw [hW]
    have h3 := congrArg (Submodule.map (Submodule.subtype _)) b'.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h3
    exact h3.symm
end GlobalTheory.FrameBasic
