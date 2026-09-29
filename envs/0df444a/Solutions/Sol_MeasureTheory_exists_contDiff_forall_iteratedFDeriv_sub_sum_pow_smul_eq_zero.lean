-- Prove2me | solution 1 for MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/dd7a340e-0a63-5ac0-a5dc-a29e82687dd6

import Mathlib
import Theorems.Thm_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
import Theorems.Thm_iteratedFDeriv_smul_comp_apply_append_inl_inr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Fin Function

namespace TaylorFlat

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "ρ̂" => (((0 : E), (1 : ℝ)) : E × ℝ)

def pv {m : ℕ} (b : Fin m → Bool) (u : Fin m → E) : Fin m → E × ℝ :=
  fun i => if b i then ρ̂ else ((u i, 0) : E × ℝ)

def sv (m : ℕ) {j : ℕ} (u : Fin j → E) : Fin m → E × ℝ :=
  fun i => if h : (i : ℕ) < j then ((u ⟨i, h⟩, 0) : E × ℝ) else ρ̂

theorem sv_eq_append {j l : ℕ} (u : Fin j → E) :
    sv (j + l) u = Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ρ̂) := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun k => ?_) i
  · rw [Fin.append_left]
    simp [sv]
  · rw [Fin.append_right]
    simp [sv]

def Symm {m : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin m => E × ℝ) F) : Prop :=
  ∀ (σ : Equiv.Perm (Fin m)) (w : Fin m → E × ℝ), M (w ∘ σ) = M w

theorem eq_of_forall_pv {m : ℕ} (M₁ M₂ : ContinuousMultilinearMap ℝ (fun _ : Fin m => E × ℝ) F)
    (h : ∀ (b : Fin m → Bool) (u : Fin m → E), M₁ (pv b u) = M₂ (pv b u)) : M₁ = M₂ := by
  classical
  ext v
  have hv : v = (fun i => (((v i).1, 0) : E × ℝ)) + fun i => (v i).2 • ρ̂ := by
    funext i; ext <;> simp
  have key : ∀ (M : ContinuousMultilinearMap ℝ (fun _ : Fin m => E × ℝ) F) (s : Finset (Fin m)),
      M (s.piecewise (fun i => (((v i).1, 0) : E × ℝ)) fun i => (v i).2 • ρ̂) =
        (∏ i, (if i ∈ s then (1 : ℝ) else (v i).2)) •
          M (pv (fun i => decide (i ∉ s)) fun i => (v i).1) := by
    intro M s
    show M.toMultilinearMap _ = _ • M.toMultilinearMap _
    rw [← MultilinearMap.map_smul_univ]
    congr 1
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, pv, hi]
  rw [hv]
  show M₁.toMultilinearMap (_ + _) = M₂.toMultilinearMap (_ + _)
  rw [MultilinearMap.map_add_univ, MultilinearMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  show M₁ _ = M₂ _
  rw [key M₁, key M₂, h]

def liftPerm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e)

@[scoped simp] theorem liftPerm_zero {n : ℕ} (e : Equiv.Perm (Fin n)) : liftPerm e 0 = 0 := by
  simp [liftPerm]

@[scoped simp] theorem liftPerm_succ {n : ℕ} (e : Equiv.Perm (Fin n)) (k : Fin n) :
    liftPerm e k.succ = (e k).succ := by
  simp [liftPerm]

theorem cons_comp_liftPerm {n : ℕ} {α : Type} (a : α) (w : Fin n → α) (τ : Equiv.Perm (Fin n)) :
    (Fin.cons a w : Fin (n + 1) → α) ∘ liftPerm τ = Fin.cons a (w ∘ τ) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp
  · simp

theorem symm_apply_snoc {m : ℕ} {M : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E × ℝ) F}
    (hM : Symm M) (w : Fin m → E × ℝ) (a : E × ℝ) :
    M (Fin.snoc w a) = M (Fin.cons a w) := by
  rw [Fin.snoc_eq_cons_rotate]
  exact hM (finRotate (m + 1)) (Fin.cons a w)

theorem symm_curryLeft {m : ℕ} {M : ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E × ℝ) F}
    (hM : Symm M) (a : E × ℝ) : Symm (M.curryLeft a) := by
  intro τ w
  rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.curryLeft_apply,
    ← cons_comp_liftPerm, hM]

theorem pv_eq_snoc {m : ℕ} (b : Fin (m + 1) → Bool) (u : Fin (m + 1) → E) :
    pv b u = Fin.snoc (pv (b ∘ Fin.castSucc) (u ∘ Fin.castSucc))
      (if b (Fin.last m) then ρ̂ else ((u (Fin.last m), 0) : E × ℝ)) := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [Fin.snoc_last]; rfl
  · rw [Fin.snoc_castSucc]; rfl

theorem cons_sv {m j : ℕ} (hj : j ≤ m) (x : E) (u : Fin j → E) :
    Fin.cons ((x, 0) : E × ℝ) (sv m u) = sv (m + 1) (Fin.cons x u : Fin (j + 1) → E) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [sv]
  · rw [Fin.cons_succ]
    simp only [sv, Fin.val_succ]
    by_cases hk : (k : ℕ) < j
    · rw [dif_pos hk, dif_pos (by omega)]
      congr 2
    · rw [dif_neg hk, dif_neg (by omega)]

theorem snoc_sv {m j : ℕ} (hj : j ≤ m) (u : Fin j → E) :
    Fin.snoc (sv m u) ρ̂ = sv (m + 1) u := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [Fin.snoc_last]
    simp only [sv, Fin.val_last]
    rw [dif_neg (by omega)]
  · rw [Fin.snoc_castSucc]
    simp [sv]

theorem eq_pv_of_symm_of_sorted : ∀ (m : ℕ) (M₁ M₂ : ContinuousMultilinearMap ℝ (fun _ : Fin m => E × ℝ) F),
    Symm M₁ → Symm M₂ →
    (∀ (j : ℕ), j ≤ m → ∀ (u : Fin j → E), M₁ (sv m u) = M₂ (sv m u)) →
    ∀ (b : Fin m → Bool) (u : Fin m → E), M₁ (pv b u) = M₂ (pv b u) := by
  intro m
  induction m with
  | zero =>
    intro M₁ M₂ _ _ hs b u
    have : pv b u = sv 0 (Fin.elim0 : Fin 0 → E) := funext fun i => i.elim0
    rw [this]
    exact hs 0 le_rfl _
  | succ m ih =>
    intro M₁ M₂ h₁ h₂ hs b u
    rw [pv_eq_snoc, symm_apply_snoc h₁, symm_apply_snoc h₂, ← ContinuousMultilinearMap.curryLeft_apply,
      ← ContinuousMultilinearMap.curryLeft_apply]
    refine ih _ _ (symm_curryLeft h₁ _) (symm_curryLeft h₂ _) ?_ _ _
    intro j hj u'
    rw [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.curryLeft_apply]
    by_cases hb : b (Fin.last m) = true
    · rw [if_pos hb, ← symm_apply_snoc h₁, ← symm_apply_snoc h₂, snoc_sv hj]
      exact hs j (by omega) u'
    · rw [if_neg hb, cons_sv hj]
      exact hs (j + 1) (by omega) _

theorem eq_of_symm_of_sorted {m : ℕ} (M₁ M₂ : ContinuousMultilinearMap ℝ (fun _ : Fin m => E × ℝ) F)
    (h₁ : Symm M₁) (h₂ : Symm M₂)
    (hs : ∀ (j : ℕ), j ≤ m → ∀ (u : Fin j → E), M₁ (sv m u) = M₂ (sv m u)) : M₁ = M₂ :=
  eq_of_forall_pv M₁ M₂ (eq_pv_of_symm_of_sorted m M₁ M₂ h₁ h₂ hs)

end TaylorFlat
p2m_reactivate "P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero.TaylorFlat"

open scoped Topology
open Filter

namespace Borel44

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

noncomputable def chi : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def T (k : ℕ) (a : E → F) : E × ℝ → F :=
  fun p => ((chi : ℝ → ℝ) p.2 * (p.2 ^ k / (k.factorial : ℝ))) • a p.1

theorem T_contDiff (k : ℕ) {a : E → F} (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    ContDiff ℝ (⊤ : ℕ∞) (T k a) := by
  unfold T
  refine ContDiff.smul ?_ (ha.comp contDiff_fst)
  exact ((chi.contDiff).comp contDiff_snd).mul ((contDiff_snd.pow k).div_const _)

theorem T_hasCompactSupport (k : ℕ) {a : E → F} {C : Set E} (hC : IsCompact C)
    (hsupp : ∀ e, e ∉ C → a e = 0) : HasCompactSupport (T k a) := by

  refine HasCompactSupport.intro (hC.prod (isCompact_closedBall (0 : ℝ) 2)) (fun p hp => ?_)
  rw [Set.mem_prod, not_and_or] at hp
  unfold T
  rcases hp with h1 | h2
  · rw [hsupp p.1 h1, smul_zero]
  · have hχ : (chi : ℝ → ℝ) p.2 = 0 := by
      have : p.2 ∉ Function.support (chi : ℝ → ℝ) := by
        rw [ContDiffBump.support_eq]
        exact fun h => h2 (Metric.ball_subset_closedBall h)
      simpa [Function.mem_support] using this
    rw [hχ, zero_mul, zero_smul]

noncomputable def S (ε : ℝ) : E × ℝ →L[ℝ] E × ℝ :=
  (ContinuousLinearMap.fst ℝ E ℝ).prod (ε⁻¹ • ContinuousLinearMap.snd ℝ E ℝ)

theorem S_apply (ε : ℝ) (p : E × ℝ) : S ε p = (p.1, ε⁻¹ * p.2) := by
  simp [S]

theorem norm_S_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : ‖(S ε : E × ℝ →L[ℝ] E × ℝ)‖ ≤ ε⁻¹ := by
  have hε' : 1 ≤ ε⁻¹ := one_le_inv_iff₀.mpr ⟨hε, hε1⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hε.le) (fun p => ?_)
  rw [S_apply, Prod.norm_def, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖p.1‖ = 1 * ‖p.1‖ := (one_mul _).symm
      _ ≤ ε⁻¹ * max ‖p.1‖ ‖p.2‖ := mul_le_mul hε' (le_max_left _ _) (norm_nonneg _) (zero_le_one.trans hε')
  · rw [norm_mul, norm_inv, Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hε.le)

noncomputable def term (k : ℕ) (ε : ℝ) (a : E → F) : E × ℝ → F := fun p => ε ^ k • T k a (S ε p)

theorem term_eq (k : ℕ) {ε : ℝ} (hε : 0 < ε) (a : E → F) (p : E × ℝ) :
    term k ε a p = ((chi : ℝ → ℝ) (p.2 / ε) * (p.2 ^ k / (k.factorial : ℝ))) • a p.1 := by
  unfold term T
  rw [S_apply]
  simp only
  rw [smul_smul]
  congr 1
  rw [inv_mul_eq_div, div_pow]
  field_simp

theorem term_contDiff (k : ℕ) (ε : ℝ) {a : E → F} (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    ContDiff ℝ (⊤ : ℕ∞) (term k ε a) :=
  contDiff_const.smul ((T_contDiff k ha).comp (S ε : E × ℝ →L[ℝ] E × ℝ).contDiff)

theorem iteratedDeriv_monomial (k l : ℕ) :
    iteratedDeriv l (fun r : ℝ => r ^ k / (k.factorial : ℝ)) 0 = if l = k then 1 else 0 := by
  have h : (fun r : ℝ => r ^ k / (k.factorial : ℝ)) = fun r => ((k.factorial : ℝ)⁻¹) * (fun r : ℝ => r ^ k) r := by
    funext r; simp [div_eq_inv_mul]
  rw [h, iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  rcases lt_trichotomy l k with hlt | rfl | hgt
  · rw [if_neg hlt.ne, zero_pow (by omega), mul_zero, mul_zero]
  · rw [if_pos rfl, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one,
      inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _)]
  · rw [if_neg hgt.ne', Nat.descFactorial_eq_zero_iff_lt.mpr hgt]; simp

theorem norm_iteratedFDeriv_term_le (k j : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a : E → F}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) {N : ℝ} (hN : ∀ q : E × ℝ, ‖iteratedFDeriv ℝ j (T k a) q‖ ≤ N) (p : E × ℝ) :
    ‖iteratedFDeriv ℝ j (term k ε a) p‖ ≤ ε ^ k * (ε⁻¹) ^ j * N := by
  have hT := T_contDiff k ha
  have hTS : ContDiff ℝ (⊤ : ℕ∞) (T k a ∘ (S ε : E × ℝ →L[ℝ] E × ℝ)) :=
    hT.comp (ContinuousLinearMap.contDiff (S ε : E × ℝ →L[ℝ] E × ℝ))
  have h1 : iteratedFDeriv ℝ j (term k ε a) p = ε ^ k • iteratedFDeriv ℝ j (T k a ∘ (S ε : E × ℝ →L[ℝ] E × ℝ)) p := by
    unfold term
    exact iteratedFDeriv_const_smul_apply' (hTS.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right (S ε) hT p (by exact_mod_cast le_top), norm_smul,
    norm_pow, Real.norm_of_nonneg hε.le]
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN p)
  calc ε ^ k * ‖(iteratedFDeriv ℝ j (T k a) (S ε p)).compContinuousLinearMap fun _ => S ε‖
      ≤ ε ^ k * (‖iteratedFDeriv ℝ j (T k a) (S ε p)‖ * ∏ _i : Fin j, ‖(S ε : E × ℝ →L[ℝ] E × ℝ)‖) := by
        gcongr
        exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ε ^ k * (N * (ε⁻¹) ^ j) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        gcongr
        · exact hN _
        · exact norm_S_le hε hε1
    _ = ε ^ k * (ε⁻¹) ^ j * N := by ring

theorem term_eventuallyEq (k : ℕ) {ε : ℝ} (hε : 0 < ε) (a : E → F) (e : E) :
    term k ε a =ᶠ[𝓝 ((e, 0) : E × ℝ)] fun p => (p.2 ^ k / (k.factorial : ℝ)) • a p.1 := by
  have ho : IsOpen {p : E × ℝ | |p.2| < ε} := isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
  have hm : ((e, 0) : E × ℝ) ∈ {p : E × ℝ | |p.2| < ε} := by simp [hε]
  refine Filter.eventually_of_mem (ho.mem_nhds hm) fun p hp => ?_
  rw [term_eq k hε a p]
  have h1 : (chi : ℝ → ℝ) (p.2 / ε) = 1 := by
    refine chi.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hε]
    show |p.2| / ε ≤ 1
    rw [div_le_one hε]
    exact le_of_lt hp
  rw [h1, one_mul]

theorem iteratedFDeriv_monomial_eq_zero (k m : ℕ) (hmk : m < k) {a : E → F} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (e : E) :
    iteratedFDeriv ℝ m (fun p : E × ℝ => (p.2 ^ k / (k.factorial : ℝ)) • a p.1) (e, 0) = 0 := by
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun p : E × ℝ => (p.2 ^ k / (k.factorial : ℝ)) • a p.1) :=
    ((contDiff_snd.pow k).div_const _).smul (ha.comp contDiff_fst)
  have hsymm : TaylorFlat.Symm (iteratedFDeriv ℝ m (fun p : E × ℝ => (p.2 ^ k / (k.factorial : ℝ)) • a p.1) (e, 0)) := by
    intro σ w
    rw [← iteratedFDerivWithin_univ]
    exact iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex convex_univ
      (by rw [interior_univ]; exact Set.univ_nonempty) (hP.contDiffOn.of_le (by exact_mod_cast le_top))
      (Set.mem_univ _) σ w
  have h0 : TaylorFlat.Symm (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => E × ℝ) F) := fun _ _ => rfl
  refine TaylorFlat.eq_of_symm_of_sorted _ _ hsymm h0 fun j hj u => ?_
  obtain ⟨l, rfl⟩ : ∃ l, m = j + l := ⟨m - j, by omega⟩
  rw [TaylorFlat.sv_eq_append, ContinuousMultilinearMap.zero_apply,
    iteratedFDeriv_smul_comp_apply_append_inl_inr (fun r : ℝ => r ^ k / (k.factorial : ℝ))
      ((contDiff_id.pow k).div_const _) a ha j l e 0 u,
    iteratedDeriv_monomial, if_neg (by omega), zero_smul]

end Borel44
p2m_reactivate "P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero.TaylorFlat"

open Borel44 in
theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (C : Set E) (hC : IsCompact C)
    (a : ℕ → E → F) (ha : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) (hsupp : ∀ k (e : E), e ∉ C → a k e = 0) :
    ∃ B : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (n m : ℕ), m ≤ n → ∀ e : E,
        iteratedFDeriv ℝ m
          (fun p : E × ℝ => B p - ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1) (e, 0) = 0 := by
  classical

  have hT : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (T k (a k)) := fun k => T_contDiff k (ha k)
  have hTc : ∀ k, HasCompactSupport (T k (a k)) := fun k => T_hasCompactSupport k hC (hsupp k)
  have hN : ∀ k j, ∃ N : ℝ, 0 ≤ N ∧ ∀ q, ‖iteratedFDeriv ℝ j (T k (a k)) q‖ ≤ N := by
    intro k j
    obtain ⟨N, hN⟩ := ((hT k).continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).bounded_above_of_compact_support
      ((hTc k).iteratedFDeriv j)
    exact ⟨max N 0, le_max_right _ _, fun q => (hN q).trans (le_max_left _ _)⟩
  choose N hN0 hN using hN

  set ε : ℕ → ℝ := fun k => min 1 ((1 / 2) ^ k / (1 + ∑ j ∈ Finset.range k, N k j)) with hε
  have hden : ∀ k, 0 < 1 + ∑ j ∈ Finset.range k, N k j := fun k =>
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => hN0 k j)
  have hε_pos : ∀ k, 0 < ε k := fun k => lt_min one_pos (div_pos (pow_pos (by norm_num) k) (hden k))
  have hε_le1 : ∀ k, ε k ≤ 1 := fun k => min_le_left _ _
  have hε_le : ∀ k, ε k ≤ (1 / 2) ^ k / (1 + ∑ j ∈ Finset.range k, N k j) := fun k => min_le_right _ _

  set v : ℕ → ℕ → ℝ := fun j k => ε k ^ k * (ε k)⁻¹ ^ j * N k j with hv
  have hv0 : ∀ j k, 0 ≤ v j k := fun j k =>
    mul_nonneg (mul_nonneg (pow_nonneg (hε_pos k).le _) (pow_nonneg (inv_nonneg.mpr (hε_pos k).le) _)) (hN0 k j)
  have hbound : ∀ j k p, ‖iteratedFDeriv ℝ j (term k (ε k) (a k)) p‖ ≤ v j k := fun j k p =>
    norm_iteratedFDeriv_term_le k j (hε_pos k) (hε_le1 k) (ha k) (hN k j) p
  have hv_small : ∀ j k, j < k → v j k ≤ (1 / 2) ^ k := by
    intro j k hjk
    have hεk := hε_pos k
    have h1 : ε k ^ k * (ε k)⁻¹ ^ j = ε k ^ (k - j) := by
      rw [inv_pow, pow_sub₀ _ hεk.ne' hjk.le]
    have h2 : ε k ^ (k - j) ≤ ε k := by
      calc ε k ^ (k - j) ≤ ε k ^ 1 := pow_le_pow_of_le_one hεk.le (hε_le1 k) (by omega)
        _ = ε k := pow_one _
    have h3 : N k j ≤ 1 + ∑ j' ∈ Finset.range k, N k j' := by
      have := Finset.single_le_sum (fun j' _ => hN0 k j') (Finset.mem_range.mpr hjk)
      linarith
    calc v j k = ε k ^ (k - j) * N k j := by rw [show v j k = ε k ^ k * (ε k)⁻¹ ^ j * N k j from rfl, h1]
      _ ≤ ε k * N k j := mul_le_mul_of_nonneg_right h2 (hN0 k j)
      _ ≤ (1 / 2) ^ k / (1 + ∑ j' ∈ Finset.range k, N k j') * (1 + ∑ j' ∈ Finset.range k, N k j') :=
          mul_le_mul (hε_le k) h3 (hN0 k j) (div_nonneg (pow_nonneg (by norm_num) _) (hden k).le)
      _ = (1 / 2) ^ k := div_mul_cancel₀ _ (hden k).ne'
  have hv_summ : ∀ j, Summable (v j) := by
    intro j
    refine Summable.of_nonneg_of_le (hv0 j) (f := fun k => (if k ∈ Finset.range (j + 1) then v j k else 0) + (1 / 2) ^ k)
      (fun k => ?_) ?_
    · show v j k ≤ (if k ∈ Finset.range (j + 1) then v j k else 0) + (1 / 2) ^ k
      by_cases hk : k ∈ Finset.range (j + 1)
      · rw [if_pos hk]; linarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) k]
      · rw [if_neg hk, zero_add]
        exact hv_small j k (by simpa using hk)
    · refine Summable.add ?_ summable_geometric_two
      exact summable_of_ne_finset_zero (s := Finset.range (j + 1)) fun k hk => if_neg hk

  refine ⟨fun p => ∑' k, term k (ε k) (a k) p, ?_, ?_⟩
  · exact contDiff_tsum_of_eventually (fun k => term_contDiff k (ε k) (ha k)) (fun j _ => hv_summ j)
      fun j _ => Filter.Eventually.of_forall fun k p => hbound j k p
  · intro n m hmn e
    set mono : ℕ → E × ℝ → F := fun k p => (p.2 ^ k / (k.factorial : ℝ)) • a k p.1 with hmono
    have hmono_s : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (mono k) := fun k =>
      ((contDiff_snd.pow k).div_const _).smul ((ha k).comp contDiff_fst)
    have hB : ContDiff ℝ (⊤ : ℕ∞) (fun p => ∑' k, term k (ε k) (a k) p) :=
      contDiff_tsum_of_eventually (fun k => term_contDiff k (ε k) (ha k)) (fun j _ => hv_summ j)
        fun j _ => Filter.Eventually.of_forall fun k p => hbound j k p
    have hfun : (fun p : E × ℝ => (∑' k, term k (ε k) (a k) p) -
        ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1) =
        (fun p => ∑' k, term k (ε k) (a k) p) - ∑ k ∈ Finset.range (n + 1), mono k := by
      funext p; simp [mono, Finset.sum_apply]
    rw [hfun, iteratedFDeriv_sub_apply (hB.contDiffAt.of_le (by exact_mod_cast le_top))
      (by rw [Finset.sum_fn]; exact ContDiffAt.sum fun k _ => (hmono_s k).contDiffAt.of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_sum_apply (fun k _ => (hmono_s k).contDiffAt.of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_tsum_apply (N := (⊤ : ℕ∞)) (fun k => term_contDiff k (ε k) (ha k)) (fun j _ => hv_summ j)
        (fun j k p _ => hbound j k p) (by exact_mod_cast le_top)]
    have hk : ∀ k, iteratedFDeriv ℝ m (term k (ε k) (a k)) (e, 0) = iteratedFDeriv ℝ m (mono k) (e, 0) := fun k =>
      ((term_eventuallyEq k (hε_pos k) (a k) e).iteratedFDeriv ℝ m).eq_of_nhds
    rw [tsum_congr hk, tsum_eq_sum (s := Finset.range (n + 1)) (fun k hk' => ?_), sub_self]
    exact iteratedFDeriv_monomial_eq_zero k m (by simp at hk'; omega) (ha k) e

end S_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero
end P2MW
export P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero (solution)
