-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.unit_of_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:15.621709+00:00
-- url     : https://prove2.me/submissions/e85ff98a-e78a-49fb-8074-07f4469582ec

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Theorems.Thm_GlobalTheory_HL_GoodClass_UpU_mul
import Theorems.Thm_GlobalTheory_HL_GoodClass_UpU_det
import Theorems.Thm_GlobalTheory_HL_GoodClass_UnitIn_mul
import Theorems.Thm_GlobalTheory_HL_GoodClass_UnitIn_cancel
import Theorems.Thm_GlobalTheory_HL_GoodClass_unitIn_sign
import Theorems.Thm_GlobalTheory_HL_GoodClass_unitIn_prod
import Theorems.Thm_GlobalTheory_HL_GoodClass_sig_mono
import Theorems.Thm_GlobalTheory_HL_GoodClass_unit_entries
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_det_mono
import Theorems.Thm_GlobalTheory_FrameBasic_entry_unit
import Theorems.Thm_GlobalTheory_FrameBasic_entry_zero
import Theorems.Thm_GlobalTheory_FrameBasic_sig_sig
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
open GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]
namespace GlobalTheory.HL.GoodClass
theorem _root_.solution [Nontrivial E] (O : Subring E) (hO : ∀ (x : E) (s : ℕ), 0 < s → x ^ s ∈ O → x ∈ O)
    {n : ℕ} (w : Pt E n) (ε : Fin n → ℕ) (Z : Matrix (Fin n) (Fin n) E)
    (hZ : ∀ a b, Z a b = w.mat a b * (-1) ^ ε b) (h : ∀ l, lead Z l ≠ 0 → UnitIn O (lead Z l)) :
    ∃ σ : Fin n → Fin n, (∀ a, σ (σ a) = a) ∧ (∀ a b : Fin n, a ≤ b → (a : ℕ) + σ a ≤ b + σ b) ∧
      (∀ a b, b ≠ σ a → Z a b = 0) ∧ ∀ a, UnitIn O (Z a (σ a)) := by
  have hs : ∀ a : Fin n, sig w.blocks a < n := fun a => by
    have := (entry_unit w.blocks a (by rw [w.size]; omega)).1
    rwa [w.size] at this
  refine ⟨fun a => ⟨_, hs a⟩, fun a => Fin.ext (sig_sig _ _), fun a b hab => sig_mono _ _ _ hab,
    fun a b hb => ?_, fun a => ?_⟩
  · rw [hZ, Pt.mat, entry_zero, zero_mul]
    exact fun h => hb (Fin.ext h)
  · rw [hZ]
    refine UnitIn.mul ?_ (unitIn_sign O _)
    refine unit_entries O hO w.blocks (fun l hl hsl => ?_) a (by rw [w.size]; exact a.2)
    rw [w.size] at hl
    let τ : Fin l → Fin l := fun a => ⟨_, hsl a a.2⟩
    have hτ : Function.Injective τ := by
      intro a b hab
      have h1 : sig w.blocks a = sig w.blocks b := congrArg Fin.val hab
      apply Fin.ext
      rw [← sig_sig w.blocks a, h1, sig_sig]
    have h1 : lead Z ⟨l, Nat.lt_succ_of_le hl⟩ = _ :=
      det_mono (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)) τ (fun a b hb => by
        rw [Matrix.submatrix_apply, hZ, Pt.mat, entry_zero, zero_mul]
        exact fun h => hb (Fin.ext h))
    have h2 : UnitIn O ((1 : Matrix (Fin l) (Fin l) E).submatrix τ id).det := by
      have hb := Finite.injective_iff_bijective.1 hτ
      have := Matrix.det_permute (Equiv.ofBijective τ hb) (1 : Matrix (Fin l) (Fin l) E)
      rw [Equiv.coe_ofBijective] at this
      rw [this, Matrix.det_one, mul_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective τ hb)) with h3 | h3
      · rw [h3]; simpa using unitIn_sign O 0
      · rw [h3]; simpa using unitIn_sign O 1
    have h3 : ∏ a, Z.submatrix (Fin.castLE hl) (Fin.castLE hl) a (τ a) =
        (∏ a : Fin l, (-1 : E) ^ ε (Fin.castLE hl (τ a))) *
          ∏ a ∈ Finset.range l, ptEntryL w.blocks a (sig w.blocks a) := by
      rw [Finset.prod_range, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [Matrix.submatrix_apply, hZ, mul_comm]; rfl
    have h4 := unitIn_prod O Finset.univ (fun a : Fin l => (-1 : E) ^ ε (Fin.castLE hl (τ a)))
      fun a _ => unitIn_sign O _
    rw [h3, mul_comm, ← mul_assoc] at h1
    have h5 := h2.mul h4
    refine h5.cancel (h1 ▸ h _ ?_)
    rw [h1]
    refine IsUnit.ne_zero (IsUnit.mul ?_ ?_)
    · obtain ⟨_, y, _, hy⟩ := h5
      exact IsUnit.of_mul_eq_one y hy
    · rw [IsUnit.prod_iff]
      intro a ha
      exact (entry_unit w.blocks a (by rw [w.size]; have := Finset.mem_range.1 ha; omega)).2
end GlobalTheory.HL.GoodClass
