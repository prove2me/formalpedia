-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.adaptedChainData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:49.244829+00:00
-- url     : https://prove2.me/submissions/70f92738-225b-4522-ae25-31a386d61212

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_GlobalTheory_AdaptedChain_chain
import Theorems.Thm_GlobalTheory_AdaptedChain_stable_intSpan
import Theorems.Thm_GlobalTheory_AdaptedChain_adapted
import Theorems.Thm_GlobalTheory_AdaptedChain_even_val_iff
import Theorems.Thm_GlobalTheory_AdaptedChain_co_ge
import Theorems.Thm_GlobalTheory_AdaptedChain_co_two
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Good_bound
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_co_spec
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_cur_zero_inl
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_l_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_l_ne_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_eq16
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_lattice_inclusion_forms_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {X : Cart V d I J}
namespace GlobalTheory.AdaptedChain
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type)
    [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.AdaptedChainData := by
  intro C _ V d _ I J _ _ X hAlt g a hbig i hi hid U hU
  haveI := X.algClosed
  obtain ⟨⟨hUi, w, hw, hUw⟩, hUa⟩ := hU
  obtain ⟨S0, Q, hQ, hcard, hQL⟩ := adapted (X.G g) U w hUi hw (fun c c' => by
    rw [hUw]; congr) a hUa
  have hK : 0 < Formalism.BaseCaseIdentities.Kn i ∧ 2 * Formalism.BaseCaseIdentities.Kn i = i + 1 := by
    obtain ⟨m, rfl⟩ := hi; unfold Formalism.BaseCaseIdentities.Kn; omega
  have hsmall : ∀ s : ℕ, ¬ X.big g (a + ((2 * s : ℕ) : ZMod d) + 1) := by
    intro s
    have e := even_val_iff hAlt.1 a s
    have hg : g = 0 ∨ g = 1 - 0 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · rw [hAlt.2] at hbig ⊢; tauto
    · rw [X.big_compl, hAlt.2] at hbig ⊢; tauto
  obtain ⟨S, lev, -, p2, p3, p4, p5⟩ := chain (X := X.G g) X.j' (Formalism.BaseCaseIdentities.Kn i)
    (fun s h0 h1 h => by
      rw [ZMod.natCast_eq_zero_iff] at h
      have := Nat.le_of_dvd (by omega) h
      omega) a
    (fun s _ => by
      refine le_of_eq ?_
      rw [← X.rk_small g _ (hsmall s)]) S0 Q hQ _ (stable_intSpan U) hQL
  have hgood : ∀ c, lev c < Formalism.BaseCaseIdentities.Kn i → (X.G g).Good _ _ (S.cur c) :=
    fun c hc => ⟨S.curve c, (p2 c hc).2⟩
  have hex : ∀ c, ∃ gg lam : I g → C, (∀ e, V.Ge 0 (gg e)) ∧ (∀ e, V.Ge 0 (lam e)) ∧
      (lev c + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ e, lev e ≠ lev c + 1 → gg e = 0) ∧
      (lev c < Formalism.BaseCaseIdentities.Kn i → ∀ b, S.co (S.cur c 2) b = (V.l : C)⁻¹ * (gg b + (V.l : C) * lam b)) := by
    intro c
    by_cases h1 : lev c + 1 < Formalism.BaseCaseIdentities.Kn i
    · obtain ⟨gg, lam, g1, g2, g3, g4⟩ := p5 c h1
      exact ⟨gg, S.co (Sum.elim lam 0), g1, co_ge S g2, fun _ => g3, fun _ => co_two S _ gg lam g4⟩
    · by_cases h2 : lev c < Formalism.BaseCaseIdentities.Kn i
      · refine ⟨fun b => (V.l : C) * S.co (S.cur c 2) b, 0, fun b => ?_, fun _ => VF.Ge.zero 0,
          fun h => absurd h h1, fun _ b => by simp [VF.l_ne_zero]⟩
        simpa using (co_ge S (fun k => (hgood c h2).bound 0 (Sum.inl k)) b).l_mul
      · exact ⟨0, 0, fun _ => VF.Ge.zero 0, fun _ => VF.Ge.zero 0, fun h => absurd h h1,
          fun h => absurd h h2⟩
  choose gg lam g1 g2 g3 g4 using hex
  set Q0 := Q.filter fun c => lev c = 0 with hQ0
  have hmem : ∀ δ, (Q0.equivFin.symm δ).1 ∈ Q ∧ lev (Q0.equivFin.symm δ).1 = 0 :=
    fun δ => Finset.mem_filter.mp (Q0.equivFin.symm δ).2
  have hl3 : 3 ≤ V.l := by
    have := V.l_prime.two_le
    have := X.l_odd
    omega
  choose A hA1 hA2 using fun δ => p3 _ (hmem δ).1 (hmem δ).2
  refine ⟨S, Q0.card,
    { v := V.v, l := V.l, l_prime := V.l_prime, l_ge := hl3, v_l := V.v_l, i := i, i_odd := hi,
      good := fun c => lev c < Formalism.BaseCaseIdentities.Kn i, lev := lev, pure_good := fun _ h => h,
      ι := fun δ => (Q0.equivFin.symm δ).1,
      ι_inj := Subtype.val_injective.comp Q0.equivFin.symm.injective,
      ι_lev := fun δ => (hmem δ).2,
      al := fun c k b => S.co (S.cur c k) b, g := gg, lam := lam,
      al_all := fun c j b => co_ge S (fun k => lattice_inclusion_forms_injective _ S c j _) b,
      al_good := fun c hc j b hj => co_ge S (eq16 _ _ _ _ (hgood c hc) j hj).1 b,
      al_one := fun c hc b => by simp [Sys.co, (p2 c hc).2],
      al_two := g4, g_int := g1, lam_int := g2, g_supp := g3 },
    rfl, rfl, rfl, fun c k x _ => ?_, fun c hc => (p2 c hc).1, ?_, A, hA1, fun δ x => ?_⟩
  · simp only [Sys.al, S.cur_zero_inl]
    exact (S.co_spec (S.cur c k) x).symm
  · rw [hcard, Fintype.card_fin] at p4
    rw [Nat.succ_mul]
    omega
  · simp only [Sys.al, S.cur_zero_inl]
    exact hA2 δ x
end GlobalTheory.AdaptedChain
