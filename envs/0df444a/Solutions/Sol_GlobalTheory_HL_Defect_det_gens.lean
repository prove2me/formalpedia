-- Prove2me | solution 1 for GlobalTheory.HL.Defect.det_gens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:46.672106+00:00
-- url     : https://prove2.me/submissions/a3c912a5-1e47-4263-a198-9b65b5e96828

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFramesLevelLeIffCongrFlagSteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Theorems.Thm_GlobalTheory_HL_Defect_gram_change
import Theorems.Thm_GlobalTheory_HL_Defect_lead_translate
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Eichler_hf_cj
import Theorems.Thm_GlobalTheory_det_gram_two_frames
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Defect
open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.Defect
theorem _root_.solution {n n' : S.GLV} (hn : n ∈ S.N) (hn' : n' ∈ S.N') :
    (Matrix.of fun i j => hf L S.Hm (gens S (fun b => n (S.f b)) (fun b => n' (S.f' b)) i)
      (gens S (fun b => n (S.f b)) (fun b => n' (S.f' b)) j)).det =
      (-1) ^ (r + 1) * algebraMap F E S.th⁻¹ ^ (2 * (r + 1)) * S.G := by
  set t := algebraMap F E S.th⁻¹ with ht
  let e : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim (fun b => n (S.f b)) (fun b => n' (S.f' b))
  let P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
    Matrix.fromBlocks 1 (-(t • 1)) 0 (t • 1)
  have hP : ∀ i, gens S (fun b => n (S.f b)) (fun b => n' (S.f' b)) i = ∑ k, P k i • e k := by
    rintro (i | i)
    · simp [gens, P, e, Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
    · simp [gens, P, e, Fintype.sum_sum_type, Matrix.one_apply, ite_smul, ← ht,
        sub_eq_neg_add]
  have hPd : P.det = t ^ (r + 1) := by
    simp [P, Matrix.det_fromBlocks_zero₂₁]
  have hdet : ∀ {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m E),
      (A.map L.cj).det = L.cj A.det := fun A => (AlgEquiv.map_det L.cj A).symm
  set Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
    Matrix.of fun a b => hf L S.Hm (n' (S.f' b)) (n (S.f a)) with hZ
  have he : (Matrix.of fun i j => hf L S.Hm (e i) (e j)) = Matrix.fromBlocks
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E S.T else 0) (Z.map L.cj) Zᵀ
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E S.T' else 0) := by
    have i1 : n ∈ isomG L S.Hm := hn.1.1
    have i2 : n' ∈ isomG L S.Hm := hn'.1.1
    ext (i | i) (j | j)
    · simp only [e, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, i1 _ _, S.gram,
        Matrix.diagonal_apply]
      by_cases h : i = j
      · simp [h]
      · rw [if_neg h, if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl
    · exact (hf_cj L S.herm.1 _ _).symm
    · rfl
    · simp only [e, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, i2 _ _, S.gram',
        Matrix.diagonal_apply]
      by_cases h : i = j
      · simp [h]
      · rw [if_neg h, if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl
  have hD1 : Z.det = S.D (Fin.last (r + 1)) := lead_translate S hn hn' (Fin.last (r + 1))
  have hD0 : (Z.submatrix Fin.castSucc Fin.castSucc).det = S.D (Fin.last r).castSucc :=
    lead_translate S hn hn' (Fin.last r).castSucc
  rw [gram_change L S.Hm e e _ _ P P hP hP, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hdet, hPd, he, GlobalTheory.det_gram_two_frames, Matrix.det_transpose, hdet, hD1,
    ← Matrix.transpose_submatrix, Matrix.det_transpose, Matrix.submatrix_map, hdet, hD0, map_pow,
    ht, AlgEquiv.commutes, Frames.G, map_mul]
  ring
end GlobalTheory.HL.Defect
