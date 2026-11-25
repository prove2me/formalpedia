-- Prove2me | solution 1 for GlobalTheory.HL.BlockStab.stabiliser_blockDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:07.005593+00:00
-- url     : https://prove2.me/submissions/960af841-d34c-4a55-895a-6d159b2d9f48

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Theorems.Thm_GlobalTheory_HL_BlockStab_exists_monomial
import Theorems.Thm_GlobalTheory_HL_BlockStab_stab_monomial
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
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BlockStab
namespace GlobalTheory.HL.BlockStab
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → IsUni s' → cT L s * S.Zh * s' = S.Zh → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0 ∧ s' i j = 0) ∧ (IsIntM L s ↔ IsIntM L s')) ∧ ∀ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni s → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false → s i j = 0) → ∃ s', IsUni s' ∧ cT L s * S.Zh * s' = S.Zh := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  obtain ⟨σ, β, t, h⟩ := exists_monomial S.w.blocks
  rw [S.w.size] at h
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ a, (h a a.2).1⟩
  have hsb : ∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = false ↔ β i ≠ β j := fun i j => by
    rw [Ne, ← ((h i i.2).2.2.2 j j.2).1]; simp
  simp only [hsb]
  refine stab_monomial L σ' (fun a => β a) (fun a => t (β a) * (-1) ^ (r - σ a)) S.Zh
    (fun a => Fin.ext (h a a.2).2.1) (fun a => (h a a.2).2.2.1)
    (fun a b hab => ((h a a.2).2.2.2 b b.2).2.1 hab) (fun a b hab hl => ?_) (fun a b hab => ?_)
    (fun a b => ?_)
  · have h1 := ((h a a.2).2.2.2 b b.2).2.2.1 hab
    have h2 : (a : ℕ) < b := hl
    show σ b < σ a
    omega
  · simp only [hab]
    rcases neg_one_pow_eq_or Eˣ (r - σ a) with h1 | h1 <;>
      rcases neg_one_pow_eq_or Eˣ (r - σ b) with h2 | h2 <;> simp [h1, h2]
  · have h1 : S.Zh a b = S.w.mat a b * (-1) ^ (r - (b : ℕ)) := S.relevant a b
    rw [h1, Pt.mat, ((h a a.2).2.2.2 b b.2).2.2.2]
    by_cases h2 : b = σ' a
    · subst h2; simp [σ']
    · have h3 : ¬ (b : ℕ) = σ a := fun h => h2 (Fin.ext h)
      simp [h2, h3]
end GlobalTheory.HL.BlockStab
