-- Prove2me | solution 1 for MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8e152bc0-fe37-5281-965c-2528881c4835

import Mathlib
import Theorems.Thm_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
import Theorems.Thm_iteratedFDeriv_smul_comp_apply_append_inl_inr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero

set_option autoImplicit false

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
p2m_reactivate "P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero.TaylorFlat"

namespace TaylorFlat

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "ρ̂" => (((0 : E), (1 : ℝ)) : E × ℝ)
set_option quotPrecheck false in
local notation "H" => ({p : E × ℝ | 0 ≤ p.2} : Set (E × ℝ))

theorem convex_H : Convex ℝ H := by
  intro a ha b hb s t hs ht _
  show (0 : ℝ) ≤ (s • a + t • b).2
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  exact add_nonneg (mul_nonneg hs ha) (mul_nonneg ht hb)

theorem interior_H_nonempty : (interior H).Nonempty := by
  refine ⟨((0 : E), (1 : ℝ)), ?_⟩
  rw [mem_interior_iff_mem_nhds]
  have ho : IsOpen {p : E × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  exact Filter.mem_of_superset (ho.mem_nhds (by show (0 : ℝ) < 1; norm_num))
    fun p hp => show (0 : ℝ) ≤ p.2 from le_of_lt hp

theorem uniqueDiffOn_H : UniqueDiffOn ℝ H := uniqueDiffOn_convex convex_H interior_H_nonempty

omit [NormedSpace ℝ E] in
theorem mem_H (e : E) : ((e, (0 : ℝ)) : E × ℝ) ∈ H := show (0 : ℝ) ≤ 0 from le_rfl

theorem iteratedFDerivWithin_succ_const (Ψ : E × ℝ → F) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ H) (l : ℕ) (e : E) :
    iteratedFDerivWithin ℝ (l + 1) Ψ H (e, 0) (fun _ => ρ̂) =
      iteratedFDerivWithin ℝ l (fun y => fderivWithin ℝ Ψ H y ρ̂) H (e, 0) (fun _ => ρ̂) := by
  rw [iteratedFDerivWithin_succ_apply_right uniqueDiffOn_H (mem_H e)]
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderivWithin ℝ Ψ H) H :=
    hΨ.fderivWithin uniqueDiffOn_H (by exact_mod_cast le_top)
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_left (ContinuousLinearMap.apply ℝ F ρ̂)
    (hfd (e, 0) (mem_H e)) uniqueDiffOn_H (mem_H e) (i := l) (by exact_mod_cast le_top)
  rw [show (⇑(ContinuousLinearMap.apply ℝ F ρ̂) ∘ fderivWithin ℝ Ψ H) = fun y => fderivWithin ℝ Ψ H y ρ̂ from rfl] at h
  rw [h]
  rfl

theorem sorted_within (l : ℕ) : ∀ (Ψ : E × ℝ → F), ContDiffOn ℝ (⊤ : ℕ∞) Ψ H →
    ∀ (j : ℕ) (e : E) (u : Fin j → E),
      iteratedFDerivWithin ℝ (j + l) Ψ H (e, 0) (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ρ̂)) =
        iteratedFDeriv ℝ j (fun e' : E => iteratedFDerivWithin ℝ l Ψ H (e', 0) (fun _ => ρ̂)) e u := by
  induction l with
  | zero =>
    intro Ψ hΨ j e u
    have hv : (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin 0 => ρ̂) : Fin (j + 0) → E × ℝ) =
        fun i : Fin j => ((u i, 0) : E × ℝ) := by
      rw [show (fun _ : Fin 0 => ρ̂) = Fin.elim0 from funext fun i => i.elim0, Fin.append_elim0]
      rfl
    show iteratedFDerivWithin ℝ j Ψ H (e, 0) (Fin.append (fun i => ((u i, 0) : E × ℝ)) (fun _ : Fin 0 => ρ̂)) = _
    rw [hv]
    have h0 : (fun e' : E => iteratedFDerivWithin ℝ 0 Ψ H (e', 0) (fun _ => ρ̂)) =
        Ψ ∘ (ContinuousLinearMap.inl ℝ E ℝ) := by
      funext e'; simp
    rw [h0]
    have hpre : (ContinuousLinearMap.inl ℝ E ℝ) ⁻¹' H = Set.univ := by
      ext e'; simp
    have hc := ContinuousLinearMap.iteratedFDerivWithin_comp_right (ContinuousLinearMap.inl ℝ E ℝ) hΨ uniqueDiffOn_H
      (by rw [hpre]; exact uniqueDiffOn_univ) (x := e) (mem_H e) (i := j) (by exact_mod_cast le_top)
    rw [hpre, iteratedFDerivWithin_univ] at hc
    rw [hc]
    rfl
  | succ l ih =>
    intro Ψ hΨ j e u
    show iteratedFDerivWithin ℝ (j + l + 1) Ψ H (e, 0)
      (Fin.append (m := j) (n := l + 1) (fun i : Fin j => ((u i, 0) : E × ℝ)) (fun _ : Fin (l + 1) => ρ̂)) = _
    rw [iteratedFDerivWithin_succ_apply_right uniqueDiffOn_H (mem_H e)]
    have hsn : (fun _ : Fin (l + 1) => ρ̂) = Fin.snoc (fun _ : Fin l => ρ̂) ρ̂ := by
      funext i; simp only [Fin.snoc]; split_ifs <;> rfl
    rw [hsn, Fin.append_snoc, Fin.init_snoc]
    erw [Fin.snoc_last]
    have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderivWithin ℝ Ψ H) H :=
      hΨ.fderivWithin uniqueDiffOn_H (by exact_mod_cast le_top)
    have h := ContinuousLinearMap.iteratedFDerivWithin_comp_left (ContinuousLinearMap.apply ℝ F ρ̂)
      (hfd (e, 0) (mem_H e)) uniqueDiffOn_H (mem_H e) (i := j + l) (by exact_mod_cast le_top)
    rw [show (⇑(ContinuousLinearMap.apply ℝ F ρ̂) ∘ fderivWithin ℝ Ψ H) = fun y => fderivWithin ℝ Ψ H y ρ̂ from rfl] at h
    have hΨ₁ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => fderivWithin ℝ Ψ H y ρ̂) H := hfd.clm_apply contDiffOn_const
    have step : iteratedFDerivWithin ℝ (j + l) (fun y => fderivWithin ℝ Ψ H y) H (e, 0)
        (Fin.append (fun i : Fin j => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ρ̂)) ρ̂ =
        iteratedFDerivWithin ℝ (j + l) (fun y => fderivWithin ℝ Ψ H y ρ̂) H (e, 0)
        (Fin.append (fun i : Fin j => ((u i, 0) : E × ℝ)) (fun _ : Fin l => ρ̂)) := by
      rw [show (fun y => fderivWithin ℝ Ψ H y) = fderivWithin ℝ Ψ H from rfl, h]; rfl
    rw [step, ih _ hΨ₁ j e u, ← hsn]
    congr 2
    funext e'
    exact (iteratedFDerivWithin_succ_const Ψ hΨ l e').symm

theorem contDiff_coeff (Ψ : E × ℝ → F) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ H) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun e' : E => iteratedFDerivWithin ℝ k Ψ H (e', 0) (fun _ => ρ̂)) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedFDerivWithin ℝ k Ψ H) H := fun x hx =>
    (hΨ x hx).iteratedFDerivWithin_right uniqueDiffOn_H (m := (⊤ : ℕ∞)) (by exact_mod_cast le_top) hx
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDerivWithin ℝ k Ψ H ∘ fun e' : E => ((e', (0 : ℝ)) : E × ℝ)) :=
    h1.comp_contDiff (contDiff_id.prodMk contDiff_const) fun e' => mem_H e'
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E × ℝ) F (fun _ => ρ̂)).contDiff.comp h2

theorem coeff_eq_zero (Ψ : E × ℝ → F) (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → Ψ p = 0)
    (k : ℕ) (e : E) (he : e ∉ C) : iteratedFDerivWithin ℝ k Ψ H (e, 0) (fun _ => ρ̂) = 0 := by
  have hev : Ψ =ᶠ[nhdsWithin ((e, (0 : ℝ)) : E × ℝ) H] fun _ => (0 : F) := by
    have ho : IsOpen {p : E × ℝ | p.1 ∉ C} := hC.isClosed.isOpen_compl.preimage continuous_fst
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Filter.eventually_of_mem (ho.mem_nhds he) fun p hp => hsupp p hp)
  rw [hev.iteratedFDerivWithin_eq (hsupp _ he) k]
  by_cases hk : k = 0
  · subst hk; rfl
  · rw [iteratedFDerivWithin_const_of_ne hk]; rfl

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

end TaylorFlat
p2m_reactivate "P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero.TaylorFlat"

set_option autoImplicit false

open TaylorFlat in
theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : E × ℝ → F) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {p : E × ℝ | 0 ≤ p.2})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → Ψ p = 0) :
    ∃ a : ℕ → E → F, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) ∧ (∀ k (e : E), e ∉ C → a k e = 0) ∧
      ∀ (n m : ℕ), m ≤ n → ∀ e : E,
        iteratedFDerivWithin ℝ m
          (fun p : E × ℝ => Ψ p - ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1)
          {p : E × ℝ | 0 ≤ p.2} (e, 0) = 0 := by
  classical

  have hU : UniqueDiffOn ℝ {p : E × ℝ | 0 ≤ p.2} := TaylorFlat.uniqueDiffOn_H
  set a : ℕ → E → F := fun k e' => iteratedFDerivWithin ℝ k Ψ {p : E × ℝ | 0 ≤ p.2} (e', 0)
    (fun _ => (((0 : E), (1 : ℝ)) : E × ℝ)) with ha
  have hsm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k) := fun k => TaylorFlat.contDiff_coeff Ψ hΨ k
  refine ⟨a, hsm, fun k e he => TaylorFlat.coeff_eq_zero Ψ C hC hsupp k e he, ?_⟩
  intro n m hmn e

  set P : ℕ → E × ℝ → F := fun k p => (p.2 ^ k / (k.factorial : ℝ)) • a k p.1 with hP
  have hPs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (P k) := fun k =>
    ((contDiff_snd.pow k).div_const _).smul ((hsm k).comp contDiff_fst)
  have hx : ((e, (0 : ℝ)) : E × ℝ) ∈ {p : E × ℝ | 0 ≤ p.2} := TaylorFlat.mem_H e

  have hsum : (fun p : E × ℝ => Ψ p - ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1) =
      Ψ - ∑ k ∈ Finset.range (n + 1), P k := by
    funext p; simp [P, Finset.sum_apply]
  have hg : ContDiffWithinAt ℝ m (∑ k ∈ Finset.range (n + 1), P k) {p : E × ℝ | 0 ≤ p.2} (e, 0) := by
    rw [Finset.sum_fn]
    exact ContDiffWithinAt.sum fun k _ => ((hPs k).of_le (by exact_mod_cast le_top)).contDiffAt.contDiffWithinAt
  rw [hsum, iteratedFDerivWithin_sub_apply ((hΨ _ hx).of_le (by exact_mod_cast le_top)) hg hU hx,
    iteratedFDerivWithin_sum_apply hU hx (fun k _ => ((hPs k).of_le (by exact_mod_cast le_top)).contDiffAt.contDiffWithinAt)]
  rw [sub_eq_zero]

  refine TaylorFlat.eq_of_symm_of_sorted _ _ ?_ ?_ ?_
  · intro σ w
    exact iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex TaylorFlat.convex_H
      TaylorFlat.interior_H_nonempty (hΨ.of_le (by exact_mod_cast le_top)) hx σ w
  · intro σ w
    rw [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU ((hPs k).contDiffAt.of_le (by exact_mod_cast le_top)) hx,
      ← iteratedFDerivWithin_univ]
    exact iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex convex_univ
      (by rw [interior_univ]; exact Set.univ_nonempty) ((hPs k).contDiffOn.of_le (by exact_mod_cast le_top))
      (Set.mem_univ _) σ w
  · intro j hj u
    obtain ⟨l, rfl⟩ : ∃ l, m = j + l := ⟨m - j, by omega⟩
    rw [TaylorFlat.sv_eq_append, ContinuousMultilinearMap.sum_apply]
    rw [TaylorFlat.sorted_within l Ψ hΨ j e u]
    have hterm : ∀ k, iteratedFDerivWithin ℝ (j + l) (P k) {p : E × ℝ | 0 ≤ p.2} (e, 0)
        (Fin.append (fun i => ((u i, 0) : E × ℝ)) fun _ : Fin l => (((0 : E), (1 : ℝ)) : E × ℝ)) =
        (if l = k then (1 : ℝ) else 0) • iteratedFDeriv ℝ j (a k) e u := by
      intro k
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hU ((hPs k).contDiffAt.of_le (by exact_mod_cast le_top)) hx,
        ← TaylorFlat.iteratedDeriv_monomial k l]
      exact iteratedFDeriv_smul_comp_apply_append_inl_inr (fun r : ℝ => r ^ k / (k.factorial : ℝ))
        ((contDiff_id.pow k).div_const _) (a k) (hsm k) j l e 0 u
    simp_rw [hterm, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq (Finset.range (n + 1)) l (fun k => iteratedFDeriv ℝ j (a k) e u),
      if_pos (Finset.mem_range.mpr (by omega))]

end S_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero
end P2MW
export P2MW.S_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero (solution)
