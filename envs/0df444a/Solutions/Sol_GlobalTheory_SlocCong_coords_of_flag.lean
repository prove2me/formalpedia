-- Prove2me | solution 1 for GlobalTheory.SlocCong.coords_of_flag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:47:40.651528+00:00
-- url     : https://prove2.me/submissions/6da9fd6e-20b1-4e61-81f7-711df65b49bc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFamiliesCongrModUnitriangular
import Theorems.Thm_GlobalTheory_SlocCong_stab_of_flag
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
open Formalism.MainNotions.S
open GlobalTheory GlobalTheory.SlocCong
namespace GlobalTheory.SlocCong
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V]
    [Module E V] {H : Loc.HermSp M V} {r : ℕ} (Fr : LocNG.FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))
    (g : V ≃ₗ[E] V) (hg : ∀ a, g (Fr.f a) - Fr.f a ∈ Submodule.span E (Fr.f '' {c | c < a}))
    (y : Fin (r + 1) → V) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hB : ∀ a b, b < a → B a b = 0) (hBO : ∀ a, B a a ∈ M.L.O)
    (hy : ∀ b, y b = ∑ a, B a b • Fr.f a) (hyL : ∀ b, g (y b) ∈ Fr.LamStd L) :
    ∃ W : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, b < a → W a b = 0) ∧ (∀ a, W a a = B a a) ∧
      (∀ a b, W a b ∈ M.L.O) ∧ ∀ b, g (y b) = ∑ c, W c b • Fr.f c := by
  classical
  have hLam : ∀ v ∈ Fr.LamStd L, ∀ i, H.h v (Fr.es i) ∈ M.L.O := by
    intro v hv i
    induction hv using Submodule.span_induction with
    | mem x hx => exact hx.1 i
    | zero => rw [H.h_zero_left]; exact M.L.O.zero_mem
    | add x y _ _ hx hy => rw [H.h_add_left]; exact M.L.O.add_mem hx hy
    | smul a x _ hx =>
      rw [show a • x = (a : E) • x from rfl, H.h_smul_left]
      exact M.L.O.mul_mem a.2 hx
  have hsum : ∀ (w : V) (c : Fin (r + 1) → E),
      H.h (∑ a, c a • Fr.f a) w = ∑ a, c a * H.h (Fr.f a) w := by
    intro w c
    let φ : V →ₗ[E] E :=
      { toFun := fun v => H.h v w
        map_add' := fun x y => H.h_add_left x y w
        map_smul' := fun a x => by simp [H.h_smul_left] }
    rw [show H.h (∑ a, c a • Fr.f a) w = φ (∑ a, c a • Fr.f a) from rfl, map_sum]
    simp [φ, H.h_smul_left]
  have hex : ∀ b, ∃ l : Fin (r + 1) →₀ E, (∀ c, ¬ c < b → l c = 0) ∧
      g (y b) = B b b • Fr.f b + ∑ c, l c • Fr.f c := by
    intro b
    have hmem : g (y b) - B b b • Fr.f b ∈ Submodule.span E (Fr.f '' {c | c < b}) := by
      have e1 : g (y b) - B b b • Fr.f b =
          ∑ a, (B a b • g (Fr.f a) - if a = b then B b b • Fr.f b else 0) := by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ b, if_pos (Finset.mem_univ _), hy b]
        simp [map_sum, map_smul]
      rw [e1]
      refine Submodule.sum_mem _ fun a _ => ?_
      rcases lt_trichotomy a b with h | rfl | h
      · rw [if_neg (ne_of_lt h), sub_zero]
        refine Submodule.smul_mem _ _ ?_
        exact stab_of_flag Fr.f (g : V →ₗ[E] V) hg b _ (Submodule.subset_span ⟨a, h, rfl⟩)
      · rw [if_pos rfl, ← smul_sub]
        exact Submodule.smul_mem _ _ (hg a)
      · rw [hB a b h, if_neg (ne_of_gt h), zero_smul, sub_zero]
        exact Submodule.zero_mem _
    obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hmem
    refine ⟨l, fun c hc => ?_, ?_⟩
    · by_contra hne
      exact hc (hl (Finsupp.mem_support_iff.2 hne))
    · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
      rw [hlc]; abel
  choose l hl0 hlsum using hex
  refine ⟨Matrix.of fun c b => l b c + if c = b then B b b else 0, ?_, ?_, ?_, ?_⟩
  · intro a b h
    simp [hl0 b a (not_lt.2 (le_of_lt h)), ne_of_gt h]
  · intro a
    simp [hl0 a a (lt_irrefl a)]
  · have hcoord : ∀ b, ∀ c, c ≠ Fin.last r → l b c + (if c = b then B b b else 0) ∈ M.L.O := by
      intro b c hc
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hc
      have hv := hLam _ (hyL b) i
      have eqv : g (y b) = ∑ c, (l b c + if c = b then B b b else 0) • Fr.f c := by
        simp only [add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        rw [hlsum b]; abel
      rw [eqv, hsum] at hv
      rw [Finset.sum_eq_single i.castSucc] at hv
      · rw [Fr.h_es i i, if_pos rfl, mul_one] at hv
        exact hv
      · intro c _ hc'
        rcases Fin.eq_castSucc_or_eq_last c with ⟨j, rfl⟩ | rfl
        · rw [Fr.h_es j i, if_neg (show j ≠ i from fun h => hc' (h ▸ rfl)), mul_zero]
        · rw [H.h_herm, Fr.h_sz, map_zero, mul_zero]
      · simp
    intro c b
    by_cases hc : c = Fin.last r
    · subst hc
      simp only [Matrix.of_apply]
      rw [hl0 b (Fin.last r) (not_lt.2 (Fin.le_last b))]
      split_ifs with h
      · subst h; simpa using hBO (Fin.last r)
      · simpa using M.L.O.zero_mem
    · exact hcoord b c hc
  · intro b
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [hlsum b]; abel
end GlobalTheory.SlocCong
