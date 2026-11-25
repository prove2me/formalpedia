-- Prove2me | solution 1 for GlobalTheory.HL.FrameTuple.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:57:22.658813+00:00
-- url     : https://prove2.me/submissions/8ceb859f-0407-4ae1-b257-053f33f35437

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNondegenerateTupleComplementFixer
import Theorems.Thm_GlobalTheory_HL_FrameTuple_tup_indep
import Theorems.Thm_GlobalTheory_HL_FrameTuple_tup_span
import Theorems.Thm_GlobalTheory_HL_FrameTuple_tup_change
import Theorems.Thm_GlobalTheory_HL_FrameTuple_det_uni
import Theorems.Thm_GlobalTheory_HL_FrameTuple_comb_mul
import Theorems.Thm_GlobalTheory_HL_FrameTuple_gram_unit
import Theorems.Thm_GlobalTheory_HL_FrameTuple_isLat_std
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_FrameOnto_unipotent_onto
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
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTuple
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.FrameTuple
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∃ x : Fin (2 * r + 2) → S.V, IsUnit (gramT L S.Hm x).det ∧ Submodule.span E (Set.range x) = S.ME ∧ S.H0 = fixG L S.Hm S.ME ∧ IsLat L (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) ∧ (∀ Mh, S.massSig Mh = sigMass L S.Hm S.ME (Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))) Mh) ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∃ (y : Fin (2 * r + 2) → S.V) (B : Matrix (Fin (2 * r + 2)) (Fin (2 * r + 2)) E), B.det * L.cj B.det = 1 ∧ y = rmul x B ∧ S.Mof p.1 p.2 = Submodule.span L.O (Set.range y) := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  obtain ⟨hli, hco, -, -, -, hth, -⟩ := FrameBasic.main L r k S
  obtain ⟨hN, hN', -⟩ := FrameOnto.unipotent_onto L r k S
  let e : Fin (r + 1) ⊕ Fin (r + 1) ≃ Fin (2 * r + 2) := finSumFinEquiv.trans (finCongr (by omega))
  have hθ : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hth, map_one]
  have hME : S.ME = Submodule.span E (Set.range (Sum.elim S.f S.f')) := by
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    simp only [Frames.ME, Frames.spanTo, hs, Set.image_univ, Set.Sum.elim_range, Submodule.span_union]
  have hspan : Submodule.span E (Set.range (tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm)) = S.ME := by
    rw [e.symm.surjective.range_comp, tup_span hθ, hME]
  refine ⟨tup (algebraMap F E S.th⁻¹) S.f S.f' ∘ e.symm, ?_, hspan, rfl, isLat_std L _, fun _ => rfl, ?_⟩
  · refine gram_unit L S.herm.1 _ ((tup_indep hθ hli).comp _ e.symm.injective) ?_
    rw [hspan]
    exact hco.disjoint
  · rintro C ⟨n, hn, n', hn', rfl⟩ p ⟨A, A', -, -, h0, h1, -, hp, hp'⟩
    obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := hN n hn
    obtain ⟨s', ⟨hs0', hs1'⟩, hs'⟩ := hN' n' hn'
    simp only [hs, hs', comb_mul] at hp hp'
    refine ⟨tup (algebraMap F E S.th⁻¹) p.1 p.2 ∘ e.symm,
      (Matrix.fromBlocks (s * A) (algebraMap F E S.th⁻¹ • (s' * A' - s * A)) 0 (s' * A')).submatrix
        e.symm e.symm, ?_, ?_, ?_⟩
    · rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul,
        det_uni s hs0 hs1, det_uni s' hs0' hs1', det_uni A (fun i j h => (h0 i j h).1) fun i => (h1 i).1,
        det_uni A' (fun i j h => (h0 i j h).2) fun i => (h1 i).2]
      simp
    · funext j
      rw [Function.comp_apply, tup_change _ S.f S.f' p.1 p.2 _ _ hp hp', rmul]
      exact (e.symm.sum_comp _).symm
    · rw [e.symm.surjective.range_comp, tup, Set.Sum.elim_range]
      rfl
end GlobalTheory.HL.FrameTuple
