-- Prove2me | solution 1 for GlobalTheory.BetaEx.smul_det_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:26.974058+00:00
-- url     : https://prove2.me/submissions/818d65ca-afd9-45f9-85c1-c89bdc09fc24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Theorems.Thm_GlobalTheory_BetaEx_det_mem
import Theorems.Thm_GlobalTheory_BetaEx_row_update_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BetaEx
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
omit [NumberField E]
namespace GlobalTheory.BetaEx
theorem _root_.solution (M' : Submodule (𝓞 E) (Fin n → E)) (m : Fin n → E) (a : 𝓞 E) (ha : a • m ∈ M')
    (w : Matrix (Fin n) (Fin n) E) (hw : ∀ i, w i ∈ M' ⊔ Submodule.span (𝓞 E) {m}) :
    a • w.det ∈ detSpan M' := by
  classical
  have dec : ∀ x ∈ M' ⊔ Submodule.span (𝓞 E) {m}, ∃ v ∈ M', ∃ t : 𝓞 E, x = v + t • m := by
    intro x hx
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨v, hv, t, rfl⟩
  have key : ∀ s : Finset (Fin n), ∀ w : Matrix (Fin n) (Fin n) E,
      (∀ i, w i ∈ M' ⊔ Submodule.span (𝓞 E) {m}) → (∀ i, i ∉ s → w i ∈ M') → a • w.det ∈ detSpan M' := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro w _ h; exact Submodule.smul_mem _ _ (det_mem w fun i => h i (by simp))
    | insert j s hj ih =>
      intro w hw h
      choose v hv t ht using fun i => dec _ (hw i)
      have e1 : w.det = (w.updateRow j (v j)).det + (t j : E) * (w.updateRow j m).det := by
        conv_lhs => rw [← Matrix.updateRow_eq_self w j, ht j]
        rw [Matrix.det_updateRow_add, ← Matrix.det_updateRow_smul]
        rfl
      have e2 : (w.updateRow j m).det = ((Matrix.of v).updateRow j m).det := by
        apply Matrix.det_eq_of_forall_row_eq_smul_add_const (fun i => if i = j then 0 else (t i : E)) j (by simp)
        intro i k
        by_cases hi : i = j
        · subst hi; simp
        · simp only [Matrix.updateRow_ne hi, hi, if_false, Matrix.updateRow_self, Matrix.of_apply]
          rw [ht i]; rfl
      rw [e1, smul_add]
      refine Submodule.add_mem _ (ih _ (row_update_mem w hw j _ (Submodule.mem_sup_left (hv j))) ?_) ?_
      · intro i hi
        by_cases hij : i = j
        · subst hij; rw [Matrix.updateRow_self]; exact hv i
        · rw [Matrix.updateRow_ne hij]; exact h i (by simp [hij, hi])
      · have e3 : a • ((t j : E) * (w.updateRow j m).det) =
            ((Matrix.of v).updateRow j (t j • a • m)).det := by
          rw [e2]
          change (a : E) * _ = ((Matrix.of v).updateRow j ((t j : E) • (a : E) • m)).det
          rw [Matrix.det_updateRow_smul, Matrix.det_updateRow_smul]; ring
        rw [e3]
        exact det_mem _ (row_update_mem _ hv j _ (M'.smul_mem _ ha))
  exact key Finset.univ w hw (fun i hi => absurd (Finset.mem_univ i) hi)
end GlobalTheory.BetaEx
