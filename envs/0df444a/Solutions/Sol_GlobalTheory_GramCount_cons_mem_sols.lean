-- Prove2me | solution 1 for GlobalTheory.GramCount.cons_mem_sols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:31:38.088493+00:00
-- url     : https://prove2.me/submissions/acfd19a7-7636-4521-94b5-e63b75eabfaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTupleExtensionsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesWithGramMatrixResidueRing
import Theorems.Thm_GlobalTheory_GramCount_cj_ip


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
variable {B : Type} [CommRing B]
namespace GlobalTheory.GramCount
theorem _root_.solution (c : B →+* B) (hc : ∀ u, c (c u) = u) {m n : ℕ}
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) B) (hG : ∀ a b, c (G b a) = G a b)
    (x : Fin m → Fin n → B) (hx : x ∈ sols c n (G.submatrix Fin.succ Fin.succ))
    (y : Fin n → B) :
    (Fin.cons y x : Fin (m + 1) → Fin n → B) ∈ sols c n G ↔
      Prim c (Fin.cons y x : Fin (m + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = G i.succ 0) ∧
        ip c y y = G 0 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i => by simpa using h2 i.succ 0, by simpa using h2 0 0⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun a b => ?_⟩
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simpa using h3
    · simp only [Fin.cons_succ, Fin.cons_zero]
      rw [← cj_ip c hc, h2, hG]
    · simpa using h2 a
    · simpa using hx.2 a b
end GlobalTheory.GramCount
