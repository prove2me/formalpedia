-- Prove2me | solution 1 for GlobalTheory.FlagEich.desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:36:39.712642+00:00
-- url     : https://prove2.me/submissions/5b770941-b320-44aa-93c2-ac949d3ce145

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
import Theorems.Thm_GlobalTheory_FlagEich_prod_update
import Theorems.Thm_GlobalTheory_FlagEich_eq_one
import Theorems.Thm_GlobalTheory_FlagEich_step
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FlagEich
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.FlagEich
theorem _root_.solution {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0)
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (H2 : ∀ i j, hf L S.Hm (gs i) (gs j) = 0) :
    ∀ d m : ℕ, m + d = r → ∀ n ∈ S.Nof g,
      (∀ a : Fin r, (a : ℕ) < m → n (g a.castSucc) = g a.castSucc ∧ n (gs a) = gs a) →
      ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV),
        (∀ i, (∀ j, j ≤ i → hf L S.Hm (u i) (g j.castSucc) = 0 ∧ hf L S.Hm (u i) (gs j) = 0) ∧
          s i + L.cj (s i) = hf L S.Hm (u i) (u i) ∧
          ∀ v, e i v = eich L S.Hm (g i.castSucc) (u i) (s i) v) ∧
        (∀ i : Fin r, (i : ℕ) < m → e i = 1) ∧ n = (List.ofFn e).prod := by
  intro d
  induction d with
  | zero =>
    intro m hm n hn hfix
    have h1 : n = 1 := eq_one S H1 n hn (fun a => hfix a (by omega))
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 1, fun i => ⟨fun j _ => ⟨by simp [hf], by simp [hf]⟩,
      by simp [hf], fun v => by simp [eich, hf]⟩, fun _ _ => rfl, ?_⟩
    rw [h1]; simp
  | succ d ih =>
    intro m hm n hn hfix
    have hmr : m < r := by omega
    obtain ⟨u0, s0, E0, hc0, hE0, hfix2⟩ := step S H0 H1 H2 n hn ⟨m, hmr⟩
      (fun a ha => hfix a (Fin.lt_def.mp ha))
    have hn' : E0⁻¹ * n ∈ S.Nof g := Subgroup.mul_mem _ (Subgroup.inv_mem _ hE0) hn
    obtain ⟨u', s', e', hc', h1', hp'⟩ := ih (m + 1) (by omega) (E0⁻¹ * n) hn'
      (fun a ha => hfix2 a (Fin.le_iff_val_le_val.mpr (by simp; omega)))
    refine ⟨Function.update u' ⟨m, hmr⟩ u0, Function.update s' ⟨m, hmr⟩ s0,
      Function.update e' ⟨m, hmr⟩ E0, fun i => ?_, fun i hi => ?_, ?_⟩
    · by_cases hi : i = ⟨m, hmr⟩
      · subst hi; simp only [Function.update_apply, if_true]; exact hc0
      · simp only [Function.update_apply, if_neg hi]; exact hc' i
    · have hi' : i ≠ ⟨m, hmr⟩ := fun h => by rw [h] at hi; simp at hi
      rw [Function.update_apply, if_neg hi']; exact h1' i (by omega)
    · rw [prod_update e' ⟨m, hmr⟩ E0 (fun i hi => h1' i (by rw [Fin.le_iff_val_le_val] at hi; simp at hi; omega)),
        ← hp', mul_inv_cancel_left]
end GlobalTheory.FlagEich
