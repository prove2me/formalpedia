-- Prove2me | solution 1 for GlobalTheory.exists_pseudoCoords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:40.7891+00:00
-- url     : https://prove2.me/submissions/58879865-37af-4dd5-bef0-bf8087c657ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Theorems.Thm_GlobalTheory_exists_smul_mem_of_mem_span_fraction
import Theorems.Thm_GlobalTheory_exists_splitting_vector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
      [FiniteDimensional K V], Module.finrank K V = n →
      ∀ (Λ : Submodule R V) (I : Submodule K V), Λ.FG → Submodule.span K (Λ : Set V) = ⊤ →
      ∃ (s : ℕ) (f : Fin n → (V →ₗ[K] K)) (c : Fin n → FractionalIdeal R⁰ K),
        (∀ v, (∀ a, f a v = 0) → v = 0) ∧ (∀ a, c a ≠ 0) ∧ (∀ v, v ∈ Λ ↔ ∀ a, f a v ∈ c a) ∧
        ∀ v, v ∈ I ↔ ∀ a : Fin n, s ≤ (a : ℕ) → f a v = 0 := by
  induction n with
  | zero =>
    intro V _ _ _ _ _ hV Λ I _ _
    have : Subsingleton V := Module.finrank_zero_iff.1 hV
    refine ⟨0, Fin.elim0, Fin.elim0, fun v _ => Subsingleton.elim _ _, fun a => a.elim0, ?_, ?_⟩
    · intro v
      rw [Subsingleton.elim v 0]
      exact ⟨fun _ a => a.elim0, fun _ => Λ.zero_mem⟩
    · intro v
      rw [Subsingleton.elim v 0]
      exact ⟨fun _ a => a.elim0, fun _ => I.zero_mem⟩
  | succ n ih =>
    intro V _ _ _ _ _ hV Λ I hfg hsp
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    obtain ⟨l, hl, hI⟩ : ∃ l : V →ₗ[K] K, l ≠ 0 ∧ (I = ⊤ ∨ I ≤ LinearMap.ker l) := by
      by_cases h : I = ⊤
      · obtain ⟨l, hl, -⟩ := Submodule.exists_le_ker_of_lt_top (⊥ : Submodule K V) bot_lt_top
        exact ⟨l, hl, Or.inl h⟩
      · obtain ⟨l, hl, h2⟩ := Submodule.exists_le_ker_of_lt_top I (lt_top_iff_ne_top.2 h)
        exact ⟨l, hl, Or.inr h2⟩
    obtain ⟨c0, e, hc0, he, hΛc, hce⟩ := exists_splitting_vector Λ hfg hsp l hl
    set W := LinearMap.ker l with hW
    have hWn : Module.finrank K W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker l
      have h2 : LinearMap.range l = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨x • e, by simp [he]⟩
      rw [h2, finrank_top, Module.finrank_self, hV] at h1
      rw [hW]; omega
    let ι : W →ₗ[R] V := W.subtype.restrictScalars R
    have hι : Function.Injective ι := Subtype.val_injective
    let Λ' : Submodule R W := Λ.comap ι
    have hΛ' : ∀ w : W, w ∈ Λ' ↔ (w : V) ∈ Λ := fun w => Iff.rfl
    have hfg' : Λ'.FG := by
      apply Submodule.fg_of_fg_map_injective ι hι
      exact Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
    have hsp' : Submodule.span K (Λ' : Set W) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span_fraction (K := K) Λ (w : V)
        (by rw [hsp]; trivial)
      have hd1 : algebraMap R K d ≠ 0 := by simpa using hd
      have hm : algebraMap R K d • w ∈ Λ' := by
        rw [hΛ']
        simpa using hdw
      have : w = (algebraMap R K d)⁻¹ • (algebraMap R K d • w) := by
        rw [smul_smul, inv_mul_cancel₀ hd1, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
    obtain ⟨s, f, c, hf, hc, hfΛ, hfI⟩ := ih W hWn Λ' (I.comap W.subtype) hfg' hsp'
    let p : V →ₗ[K] W := LinearMap.codRestrict W (LinearMap.id - l.smulRight e) (by
      intro v
      simp [hW, he])
    have hp : ∀ v, (p v : V) = v - l v • e := fun v => rfl
    let F : Fin (n + 1) → (V →ₗ[K] K) := Fin.snoc (fun a => f a ∘ₗ p) l
    let C : Fin (n + 1) → FractionalIdeal R⁰ K := Fin.snoc c c0
    have hF1 : ∀ a v, F (Fin.castSucc a) v = f a (p v) := by
      intro a v; simp [F]
    have hF2 : ∀ v, F (Fin.last n) v = l v := by
      intro v; simp [F]
    have hC1 : ∀ a, C (Fin.castSucc a) = c a := by
      intro a; simp [C]
    have hC2 : C (Fin.last n) = c0 := by
      simp [C]
    have A1 : ∀ v, (∀ a, F a v = 0) → v = 0 := by
      intro v hv
      have h1 : l v = 0 := by rw [← hF2]; exact hv _
      have h2 : p v = 0 := hf _ fun a => by rw [← hF1]; exact hv _
      have h3 := hp v
      rw [h2, h1] at h3
      simpa using h3.symm
    have A2 : ∀ a, C a ≠ 0 := by
      intro a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rwa [hC2]
      · rw [hC1]; exact hc a
    have A3 : ∀ v, v ∈ Λ ↔ ∀ a, F a v ∈ C a := by
      intro v
      rw [Fin.forall_fin_succ']
      simp only [hF1, hF2, hC1, hC2]
      rw [← hfΛ, hΛ', hp]
      constructor
      · intro hv
        exact ⟨Λ.sub_mem hv (hce _ (hΛc v hv)), hΛc v hv⟩
      · rintro ⟨h1, h2⟩
        have := Λ.add_mem h1 (hce _ h2)
        simpa using this
    rcases hI with hI | hI
    · refine ⟨n + 1, F, C, A1, A2, A3, ?_⟩
      intro v
      refine ⟨fun _ a ha => absurd a.2 (not_lt.2 ha), fun _ => ?_⟩
      rw [hI]; trivial
    · refine ⟨min s n, F, C, A1, A2, A3, ?_⟩
      intro v
      rw [Fin.forall_fin_succ']
      simp only [hF1, hF2]
      have hh : (∀ a : Fin n, min s n ≤ ((Fin.castSucc a : Fin (n + 1)) : ℕ) → f a (p v) = 0) ↔
          (p v : V) ∈ I := by
        rw [show ((p v : V) ∈ I) ↔ p v ∈ I.comap W.subtype from Iff.rfl, hfI]
        refine forall_congr' fun a => imp_congr_left ?_
        have := a.2
        simp only [Fin.val_castSucc]
        omega
      rw [hh, hp]
      constructor
      · intro hv
        have h0 : l v = 0 := hI hv
        refine ⟨by simpa [h0] using hv, fun _ => h0⟩
      · rintro ⟨h1, h2⟩
        have h0 : l v = 0 := h2 (by simp)
        simpa [h0] using h1
end GlobalTheory
