-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.c1_le_encodedSet_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:29:31.517518+00:00
-- url     : https://prove2.me/submissions/1eceda04-b7aa-4e52-b695-d93fb0b1f307

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
universe u
theorem h49_dist_nonneg {X : Type*} (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y) (f : X → RealL1) :
    0 ≤ distortion ρ f := by
  unfold distortion
  apply mul_nonneg
  · apply Real.sSup_nonneg; rintro r ⟨x, y, -, rfl⟩; exact div_nonneg (norm_nonneg _) (hρ x y)
  · apply Real.sSup_nonneg; rintro r ⟨x, y, -, rfl⟩; exact div_nonneg (hρ x y) (norm_nonneg _)

theorem h49_c1_nonempty (Y : Type*) [Fintype Y] (ρ : Y → Y → ℝ) :
    {D' : ℝ | ∃ f : Y → RealL1, Function.Injective f ∧ D' = distortion ρ f}.Nonempty := by
  classical
  let e := Fintype.equivFin Y
  let f : Y → RealL1 := fun y => lp.single (E := fun _ : ℕ => ℝ) 1 ((e y : ℕ)) (1:ℝ)
  refine ⟨_, f, ?_, rfl⟩
  intro y z hyz
  by_contra hne'
  have hi : ((e y : ℕ)) ≠ ((e z : ℕ)) := by
    intro h; exact hne' (e.injective (Fin.ext h))
  have := congrArg (fun g : RealL1 => g ((e y : ℕ))) hyz
  simp only [f, lp.single_apply_self, lp.single_apply_ne _ _ _ hi] at this
  norm_num at this
theorem h49_ed_pos {β : Type*} (x y : List β) (h : x ≠ y) : (0:ℝ) < (ed x y : ℝ) := by
  have : ed x y ≠ 0 := fun h0 => h (ed_eq_zero_iff.1 h0)
  exact_mod_cast Nat.pos_of_ne_zero this

theorem solution {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) (W : Finset (Word α M)) (hW : 2 ≤ W.card)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ))
    (hupper : ∀ x y : Word α M,
      (ed (encode c x.val) (encode c y.val) : ℝ) ≤
        b * (ed x.val y.val : ℝ)) :
    c1 {x : Word α M // x ∈ W}
      (fun x y => (ed x.val.val y.val.val : ℝ)) ≤
        (b / a) * binarySetDistortion (encodedSet c W) := by
  classical
  set em := encodedMember c W
  have hemv : ∀ x, (em x).val.val = encode c x.val.val := fun x => rfl
  have hem_inj : Function.Injective em := by
    intro x y hxy
    by_contra hne
    have hne' : x.val.val ≠ y.val.val := fun h => hne (Subtype.ext (Subtype.ext h))
    have h1 := hlower x.val y.val
    have h2 : encode c x.val.val = encode c y.val.val := by rw [← hemv, ← hemv, hxy]
    rw [h2, ed_self] at h1
    have := h49_ed_pos _ _ hne'
    push_cast at h1
    nlinarith
  have hclaim : ∀ g : {y : Word Bool (M * P) // y ∈ encodedSet c W} → RealL1, Function.Injective g →
      c1 {x : Word α M // x ∈ W} (fun x y => (ed x.val.val y.val.val : ℝ)) ≤
        (b / a) * distortion (fun x y => (ed x.val.val y.val.val : ℝ)) g := by
    intro g hg
    set S1 := sSup {r : ℝ | ∃ x y : {y : Word Bool (M * P) // y ∈ encodedSet c W}, x ≠ y ∧
      r = ‖g x - g y‖ / (ed x.val.val y.val.val : ℝ)} with hS1
    set S2 := sSup {r : ℝ | ∃ x y : {y : Word Bool (M * P) // y ∈ encodedSet c W}, x ≠ y ∧
      r = (ed x.val.val y.val.val : ℝ) / ‖g x - g y‖} with hS2
    have hb1 : BddAbove {r : ℝ | ∃ x y : {y : Word Bool (M * P) // y ∈ encodedSet c W}, x ≠ y ∧
        r = ‖g x - g y‖ / (ed x.val.val y.val.val : ℝ)} := by
      refine ((Set.finite_range (fun p : {y : Word Bool (M * P) // y ∈ encodedSet c W} ×
        {y : Word Bool (M * P) // y ∈ encodedSet c W} =>
          ‖g p.1 - g p.2‖ / (ed p.1.val.val p.2.val.val : ℝ))).subset ?_).bddAbove
      rintro r ⟨x, y, -, rfl⟩; exact ⟨(x, y), rfl⟩
    have hb2 : BddAbove {r : ℝ | ∃ x y : {y : Word Bool (M * P) // y ∈ encodedSet c W}, x ≠ y ∧
        r = (ed x.val.val y.val.val : ℝ) / ‖g x - g y‖} := by
      refine ((Set.finite_range (fun p : {y : Word Bool (M * P) // y ∈ encodedSet c W} ×
        {y : Word Bool (M * P) // y ∈ encodedSet c W} =>
          (ed p.1.val.val p.2.val.val : ℝ) / ‖g p.1 - g p.2‖)).subset ?_).bddAbove
      rintro r ⟨x, y, -, rfl⟩; exact ⟨(x, y), rfl⟩
    have hS1n : 0 ≤ S1 := by
      apply Real.sSup_nonneg; rintro r ⟨x, y, -, rfl⟩; positivity
    have hS2n : 0 ≤ S2 := by
      apply Real.sSup_nonneg; rintro r ⟨x, y, -, rfl⟩; positivity
    have hf : Function.Injective (g ∘ em) := hg.comp hem_inj
    have hle : c1 {x : Word α M // x ∈ W} (fun x y => (ed x.val.val y.val.val : ℝ)) ≤
        distortion (fun x y => (ed x.val.val y.val.val : ℝ)) (g ∘ em) := by
      refine csInf_le (⟨0, ?_⟩ : BddBelow _) ⟨g ∘ em, hf, rfl⟩
      rintro _ ⟨f, -, rfl⟩
      exact h49_dist_nonneg _ (fun _ _ => by positivity) f
    refine hle.trans ?_
    have hdg : distortion (fun x y => (ed x.val.val y.val.val : ℝ)) g = S1 * S2 := rfl
    rw [hdg]
    unfold distortion
    have T1 : sSup {r : ℝ | ∃ x y : {x : Word α M // x ∈ W}, x ≠ y ∧
        r = ‖(g ∘ em) x - (g ∘ em) y‖ / (ed x.val.val y.val.val : ℝ)} ≤ b * S1 := by
      apply Real.sSup_le _ (by positivity)
      rintro r ⟨x, y, hxy, rfl⟩
      have hne : em x ≠ em y := hem_inj.ne hxy
      have hne' : x.val.val ≠ y.val.val := fun h => hxy (Subtype.ext (Subtype.ext h))
      have hp := h49_ed_pos _ _ hne'
      have hpe := h49_ed_pos _ _ (fun h => hne (Subtype.ext (Subtype.ext h)))
      have k1 : ‖g (em x) - g (em y)‖ / (ed (em x).val.val (em y).val.val : ℝ) ≤ S1 :=
        le_csSup hb1 ⟨em x, em y, hne, rfl⟩
      rw [div_le_iff₀ hpe] at k1
      have k2 := hupper x.val y.val
      rw [← hemv, ← hemv] at k2
      rw [div_le_iff₀ hp]
      simp only [Function.comp_apply]
      calc ‖g (em x) - g (em y)‖ ≤ S1 * (ed (em x).val.val (em y).val.val : ℝ) := k1
        _ ≤ S1 * (b * (ed x.val.val y.val.val : ℝ)) := mul_le_mul_of_nonneg_left k2 hS1n
        _ = b * S1 * (ed x.val.val y.val.val : ℝ) := by ring
    have T2 : sSup {r : ℝ | ∃ x y : {x : Word α M // x ∈ W}, x ≠ y ∧
        r = (ed x.val.val y.val.val : ℝ) / ‖(g ∘ em) x - (g ∘ em) y‖} ≤ S2 / a := by
      apply Real.sSup_le _ (by positivity)
      rintro r ⟨x, y, hxy, rfl⟩
      have hne : em x ≠ em y := hem_inj.ne hxy
      have hn : 0 < ‖g (em x) - g (em y)‖ := norm_pos_iff.2 (sub_ne_zero.2 (hg.ne hne))
      have k1 : (ed (em x).val.val (em y).val.val : ℝ) / ‖g (em x) - g (em y)‖ ≤ S2 :=
        le_csSup hb2 ⟨em x, em y, hne, rfl⟩
      rw [div_le_iff₀ hn] at k1
      have k2 := hlower x.val y.val
      rw [← hemv, ← hemv] at k2
      simp only [Function.comp_apply]
      rw [div_le_iff₀ hn, div_mul_eq_mul_div, le_div_iff₀ ha]
      nlinarith
    have T1n : 0 ≤ sSup {r : ℝ | ∃ x y : {x : Word α M // x ∈ W}, x ≠ y ∧
        r = ‖(g ∘ em) x - (g ∘ em) y‖ / (ed x.val.val y.val.val : ℝ)} := by
      apply Real.sSup_nonneg; rintro r ⟨x, y, -, rfl⟩; positivity
    calc _ ≤ (b * S1) * (S2 / a) := mul_le_mul T1 T2 (Real.sSup_nonneg (by
            rintro r ⟨x, y, -, rfl⟩; positivity)) (by positivity)
      _ = b / a * (S1 * S2) := by field_simp
  -- conclude
  have hne := h49_c1_nonempty {y : Word Bool (M * P) // y ∈ encodedSet c W}
    (fun x y => (ed x.val.val y.val.val : ℝ))
  have hba : 0 < b / a := div_pos hb ha
  unfold binarySetDistortion
  rw [← div_le_iff₀' hba]
  apply le_csInf hne
  rintro _ ⟨g, hg, rfl⟩
  rw [div_le_iff₀' hba]
  exact hclaim g hg

