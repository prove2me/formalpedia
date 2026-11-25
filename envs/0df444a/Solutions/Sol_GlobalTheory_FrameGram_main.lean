-- Prove2me | solution 1 for GlobalTheory.FrameGram.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:50:44.756346+00:00
-- url     : https://prove2.me/submissions/65e77ef3-4a1b-4d97-8549-7cb39e7cddb6

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
import Theorems.Thm_GlobalTheory_FrameGram_lead_mul_upper
import Theorems.Thm_GlobalTheory_FrameGram_lead_lower_mul
import Theorems.Thm_GlobalTheory_FrameGram_gram_change
import Theorems.Thm_GlobalTheory_FrameGram_det_conj
import Theorems.Thm_GlobalTheory_FrameGram_span_frames
import Theorems.Thm_GlobalTheory_FrameGram_vE_const
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_hf_conj
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_HL_det_gram_two_frames
import Theorems.Thm_GlobalTheory_HL_frame_unipotent_unitriangular
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
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameGram
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameGram
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ n ∈ S.N, ∀ n' ∈ S.N', (∃ c : F, c ≠ 0 ∧ vE L S.ϖ (algebraMap F E c) = S.a ∧ (Matrix.of fun a b => S.h (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) b) (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))) a)).det = algebraMap F E c) ∧ (∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l) ∧ Submodule.span E (Set.range (Sum.elim (fun i => n (S.f i)) (fun i => algebraMap F E S.th⁻¹ • (n' (S.f' i) - n (S.f i))))) = S.ME := by
  intro F _ _ _ _ _ E _ _ _ L r k S n hn n' hn'
  obtain ⟨⟨s, ⟨hs0, hs1⟩, hs⟩, hsp, -⟩ := (GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩)).2 n hn
  obtain ⟨⟨s', ⟨hs0', hs1'⟩, hs'⟩, hsp', -⟩ :=
    (GlobalTheory.HL.frame_unipotent_unitriangular L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩)).2 n' hn'
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, -, hth, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hlead : ∀ l, lead (Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a))) l = S.D l := by
    intro l
    have e := gram_change L S.herm.1 S.f S.f' _ _ s s' hs hs'
    unfold Frames.h
    rw [e, lead_mul_upper _ _ hs0' hs1', lead_lower_mul]
    · rfl
    · intro i j hij; rw [Matrix.map_apply, hs0 i j hij, map_zero]
    · intro i; rw [Matrix.map_apply, hs1, map_one]
  refine ⟨⟨(-1) ^ (r + 1) * c * S.th⁻¹ ^ (2 * (r + 1)),
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) hc0) (pow_ne_zero _ (inv_ne_zero hth)),
    ?_, ?_⟩, hlead, ?_⟩
  · rw [vE_const L r k S c hc0, Frames.a, hc]
    push_cast; ring
  · set Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
      Matrix.of fun a b => S.h (n' (S.f' b)) (n (S.f a)) with hZ
    set t : E := algebraMap F E S.th⁻¹ with ht
    let P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
      Matrix.fromBlocks 1 (Matrix.diagonal fun _ => -t) 0 (Matrix.diagonal fun _ => t)
    have hP : ∀ j, (Sum.elim (fun i => n (S.f i)) (fun i => t • (n' (S.f' i) - n (S.f i)))) j =
        ∑ i, P i j • (Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) i := by
      rintro (j | j)
      · simp [P, Fintype.sum_sum_type, Matrix.one_apply]
      · simp [P, Fintype.sum_sum_type, Matrix.diagonal_apply, smul_sub]
        abel
    have hPd : P.det = t ^ (r + 1) := by
      simp [P, Matrix.det_fromBlocks_zero₂₁]
    have e := gram_change L S.herm.1 _ _ _ _ P P hP hP
    have hG : (Matrix.of fun a b => hf L S.Hm
        ((Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) b)
        ((Sum.elim (fun i => n (S.f i)) (fun i => n' (S.f' i))) a)) =
        Matrix.fromBlocks (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E S.T))) Z
          (Z.map L.cj).transpose
          (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E S.T'))) := by
      ext (a | a) (b | b)
      · have := hn.1.1 (S.f b) (S.f a)
        simp only [Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, this, S.gram,
          Matrix.single_apply, eq_comm, and_comm]
      · rfl
      · exact GlobalTheory.FrameBasic.hf_conj L S.herm.1 _ _
      · have := hn'.1.1 (S.f' b) (S.f' a)
        simp only [Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, this, S.gram',
          Matrix.single_apply, eq_comm, and_comm]
    have hD1 : Z.det = S.D (Fin.last (r + 1)) := hlead (Fin.last (r + 1))
    have hD0 : (Z.submatrix Fin.castSucc Fin.castSucc).det = S.D (Fin.last r).castSucc :=
      hlead (Fin.last r).castSucc
    have e2 : ((Z.map L.cj).transpose.submatrix Fin.castSucc Fin.castSucc) =
      ((Z.submatrix Fin.castSucc Fin.castSucc).map L.cj).transpose := rfl
    have hct : L.cj t = t := L.cj.commutes _
    unfold Frames.h
    rw [e, Matrix.det_mul, Matrix.det_mul, det_conj, hPd, hG, GlobalTheory.HL.det_gram_two_frames, e2,
      det_conj, det_conj, hD1, hD0, ← map_mul (algebraMap F E), map_pow, hct]
    change _ * (_ * S.G) * _ = _
    rw [hc, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, ← ht]
    ring
  · have hu : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    rw [span_frames _ _ _ hth, Frames.ME, ← hsp, ← hsp']
    simp only [Frames.spanTo, hu, Set.image_univ]
end GlobalTheory.FrameGram
