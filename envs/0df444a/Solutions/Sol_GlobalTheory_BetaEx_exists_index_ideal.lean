-- Prove2me | solution 1 for GlobalTheory.BetaEx.exists_index_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:35:58.592819+00:00
-- url     : https://prove2.me/submissions/35c3e2ec-d562-48eb-8935-010f13e2dcec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIndexIdeal
import Theorems.Thm_GlobalTheory_BetaEx_detSpan_cyclic
import Theorems.Thm_GlobalTheory_BetaEx_index_cyclic

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
namespace GlobalTheory.BetaEx
theorem _root_.solution (M' M : Submodule (𝓞 E) (Fin n → E)) (hle : M' ≤ M) (hb : Bdd M)
    (ht : ∀ m ∈ M, ∃ a : 𝓞 E, a ≠ 0 ∧ a • m ∈ M') :
    ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan M' = 𝔞 • detSpan M ∧
      Ideal.absNorm 𝔞 = M'.toAddSubgroup.relIndex M.toAddSubgroup := by
  classical
  have key : ∀ s : Finset (Fin n → E), (∀ x ∈ s, x ∈ M) →
      ∃ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ ∧ detSpan M' = 𝔞 • detSpan (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))) ∧
        Ideal.absNorm 𝔞 = M'.toAddSubgroup.relIndex
          (M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E))).toAddSubgroup := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨⊤, by simp, by simp, by simp⟩
    | insert m s _ ih =>
      intro hs
      obtain ⟨𝔞, h0, h1, h2⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
      set N := M' ⊔ Submodule.span (𝓞 E) (s : Set (Fin n → E)) with hN
      have hm : m ∈ M := hs m (Finset.mem_insert_self _ _)
      have e : M' ⊔ Submodule.span (𝓞 E) ((insert m s : Finset (Fin n → E)) : Set (Fin n → E)) =
          N ⊔ Submodule.span (𝓞 E) {m} := by
        rw [Finset.coe_insert, Submodule.span_insert, hN, sup_assoc, sup_comm (Submodule.span _ {m})]
      have hNM : N ⊔ Submodule.span (𝓞 E) {m} ≤ M := by
        rw [← e]
        exact sup_le hle (Submodule.span_le.2 fun x hx => hs x hx)
      have hb' : Bdd (N ⊔ Submodule.span (𝓞 E) {m}) := by
        obtain ⟨k, hk, h⟩ := hb
        exact ⟨k, hk, fun v hv => h v (hNM hv)⟩
      rw [e]
      refine ⟨𝔞 * (N.comap (LinearMap.toSpanSingleton (𝓞 E) _ m) : Ideal (𝓞 E)), ?_, ?_, ?_⟩
      · refine mul_ne_zero h0 ?_
        obtain ⟨a, ha, ham⟩ := ht m hm
        exact (Submodule.ne_bot_iff _).2 ⟨a, (le_sup_left : M' ≤ N) ham, ha⟩
      · rw [h1, Submodule.mul_smul, ← detSpan_cyclic N m hb']
      · rw [map_mul, h2, index_cyclic]
        exact AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono le_sup_left)
          (Submodule.toAddSubgroup_mono le_sup_left)
  have hfg : M.FG := by
    obtain ⟨k, hk, h⟩ := hb
    have hs : (stdLat E n).FG := Submodule.fg_pi fun _ => by
      rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
    apply Submodule.fg_of_fg_map_injective (LinearMap.lsmul (𝓞 E) (Fin n → E) k)
      (fun x y hxy => smul_right_injective _ hk hxy)
    exact hs.of_le (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)
  obtain ⟨s, rfl⟩ := hfg
  have := key s fun x hx => Submodule.subset_span hx
  rwa [sup_eq_right.2 hle] at this
end GlobalTheory.BetaEx
