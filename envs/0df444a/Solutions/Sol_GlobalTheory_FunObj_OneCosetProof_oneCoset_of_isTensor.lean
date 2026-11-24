-- Prove2me | solution 1 for GlobalTheory.FunObj.OneCosetProof.oneCoset_of_isTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:33.415958+00:00
-- url     : https://prove2.me/submissions/f95c2a89-6a29-4542-a81b-e86910277a69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_step_form
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_frameGL_stair
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_mem_rowR
import Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_mem_KO_of_frameGL
import Theorems.Thm_GlobalTheory_FunObj_onColumn_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
namespace GlobalTheory.FunObj.OneCosetProof
theorem _root_.solution [ν.IsAddHaarMeasure] (hs : 1 ≤ G.s) {J : G.Level} (hψ : HasConductor ψ 1)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) (hJ : ∀ j, 0 < j → j < G.m → J (G.m, j) = KO k _) :
    OneCoset hs ψ ν J T ϖ e := by
  intro β hβ
  have hne : flatTensor hs ψ ν (moved G false ((Reps.through hs J (stair G ϖ e)).elt β) T) ≠ 0 := hβ
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  obtain ⟨y, hxy⟩ := Function.ne_iff.mp hx
  have hEltAt : ∀ n : ℕ, (Reps.through hs J (stair G ϖ e)).elt β (G.m, n + 1) =
      if h : n < G.m - 2 then (Reps.through hs J (stair G ϖ e)).rep ⟨n, h⟩ (β ⟨n, h⟩) else 1 := by
    intro n
    simp only [Reps.elt, onColumn_apply]
  have h0 : (Reps.through hs J (stair G ϖ e)).elt β (G.m, 0) = stair G ϖ e 0 := by
    simp only [Reps.elt, onColumn_apply]
    rfl
  have key : ∀ n : ℕ, n + 2 ≤ G.m → (Reps.through hs J (stair G ϖ e)).elt β (G.m, n) = stair G ϖ e n := by
    intro n
    induction n with
    | zero => intro _; exact h0
    | succ n ih =>
      intro hn
      have hn1 : n < G.m - 1 := by omega
      have hn2 : n < G.m - 2 := by omega
      have hj := frameGL_stair hs ϖ e (j := n) (by omega) (src_eq hs ⟨n, hn1⟩)
      rw [← ih (by omega)] at hj
      obtain ⟨r, hr, w, hw, hrw⟩ := step_form hs hψ hT _ x y hxy ⟨n, hn1⟩ hj
      have hD := frameGL_stair hs ϖ e (j := n + 1) (by omega) (tgt_eq hs ⟨n, hn1⟩)
      rw [← hD] at hrw
      have hg' : (Reps.through hs J (stair G ϖ e)).elt β (G.m, n + 1) =
          (frameGL (tgt_eq hs ⟨n, hn1⟩)).symm r * stair G ϖ e (n + 1) * (frameGL (tgt_eq hs ⟨n, hn1⟩)).symm w := by
        apply (frameGL (tgt_eq hs ⟨n, hn1⟩)).injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
        exact hrw
      have hr' : (frameGL (tgt_eq hs ⟨n, hn1⟩)).symm r ∈ rowR hs (j := n + 1) (by omega) :=
        mem_rowR hs (by omega) (tgt_eq hs ⟨n, hn1⟩) (by rw [MulEquiv.apply_symm_apply]; exact hr)
      have hw' : (frameGL (tgt_eq hs ⟨n, hn1⟩)).symm w ∈ KO k _ :=
        mem_KO_of_frameGL (tgt_eq hs ⟨n, hn1⟩) (by rw [MulEquiv.apply_symm_apply]; exact hw)
      have hJn : J (G.m, n + 1) = KO k _ := hJ (n + 1) (by omega) (by omega)
      have hmk : DoubleCoset.mk (rowR hs (j := n + 1) (by omega)) (J (G.m, n + 1)) (stair G ϖ e (n + 1)) =
          DoubleCoset.mk (rowR hs (j := n + 1) (by omega)) (J (G.m, n + 1))
            ((Reps.through hs J (stair G ϖ e)).elt β (G.m, n + 1)) := by
        rw [DoubleCoset.eq]
        exact ⟨_, hr', _, hJn ▸ hw', hg'⟩
      rw [hEltAt n, dif_pos hn2] at hmk ⊢
      have hb := (Reps.through hs J (stair G ϖ e)).mk_rep ⟨n, hn2⟩ (β ⟨n, hn2⟩)
      dsimp only [Reps.through]
      rw [if_pos (hmk.trans hb)]
  intro i
  have hi := key (i + 1) (by have := i.isLt; omega)
  rw [hEltAt i, dif_pos i.isLt] at hi
  rw [← (Reps.through hs J (stair G ϖ e)).mk_rep i (β i)]
  exact congrArg _ hi
end GlobalTheory.FunObj.OneCosetProof
