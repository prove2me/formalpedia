-- Prove2me | solution 1 for MasulloGRH.elemSchwartz_continuous_of_seminorm_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:04:32.825196+00:00
-- url     : https://prove2.me/submissions/a7e0eecd-210f-452c-b233-0486ddd119bc

import Definitions.Def_MasulloGRH_SchwartzBruhat

set_option autoImplicit false

open Topology Filter

namespace MasulloGRHContAux

open MasulloGRH

variable {m n r s : ℕ} {d : Fin s → ℕ}

lemma top_le (k : ℕ) : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

lemma isRapidDecay_zero : IsRapidDecay (0 : ElemGroup m n r s d → ℂ) := by
  have h0 : ∀ (a : Fin r → ℤ) (b : (i : Fin s) → ZMod (d i)),
      elemLift (0 : ElemGroup m n r s d → ℂ) a b = fun _ => 0 := fun a b => rfl
  refine ⟨fun a b => by rw [h0]; exact contDiff_const, fun i j k => ⟨0, fun a b xt => ?_⟩⟩
  rw [h0, iteratedFDeriv_fun_zero]
  simp

lemma isRapidDecay_add {f g : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f)
    (hg : IsRapidDecay g) : IsRapidDecay (f + g) := by
  have h0 : ∀ a b, elemLift (f + g) a b = elemLift f a b + elemLift g a b := fun a b => rfl
  refine ⟨fun a b => by rw [h0]; exact (hf.1 a b).add (hg.1 a b), fun i j k => ?_⟩
  obtain ⟨C₁, h₁⟩ := hf.2 i j k
  obtain ⟨C₂, h₂⟩ := hg.2 i j k
  refine ⟨C₁ + C₂, fun a b xt => ?_⟩
  rw [h0, iteratedFDeriv_add_apply ((hf.1 a b).contDiffAt.of_le (top_le k))
    ((hg.1 a b).contDiffAt.of_le (top_le k))]
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt +
        iteratedFDeriv ℝ k (elemLift g a b) xt‖
      ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖iteratedFDeriv ℝ k (elemLift f a b) xt‖ +
        ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ C₁ + C₂ := by rw [mul_add]; exact add_le_add (h₁ a b xt) (h₂ a b xt)

lemma isRapidDecay_smul (c : ℂ) {f : ElemGroup m n r s d → ℂ} (hf : IsRapidDecay f) :
    IsRapidDecay (c • f) := by
  have h0 : ∀ a b, elemLift (c • f) a b = c • elemLift f a b := fun a b => rfl
  refine ⟨fun a b => by rw [h0]; exact (hf.1 a b).const_smul c, fun i j k => ?_⟩
  obtain ⟨C₁, h₁⟩ := hf.2 i j k
  refine ⟨‖c‖ * C₁, fun a b xt => ?_⟩
  rw [h0, iteratedFDeriv_const_smul_apply ((hf.1 a b).contDiffAt.of_le (top_le k)), norm_smul]
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖c‖ * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖)
      = ‖c‖ * (‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖) := by ring
    _ ≤ ‖c‖ * C₁ := mul_le_mul_of_nonneg_left (h₁ a b xt) (norm_nonneg _)

theorem isRapidDecay_of_mem {g : ElemGroup m n r s d → ℂ}
    (hg : g ∈ elemSchwartzSubmodule m n r s d) : IsRapidDecay g := by
  induction hg using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isRapidDecay_zero
  | add x y _ _ hx hy => exact isRapidDecay_add hx hy
  | smul c x _ hx => exact isRapidDecay_smul c hx

theorem isRapidDecay_toFun (g : ElemSchwartz m n r s d) : IsRapidDecay g.toFun :=
  isRapidDecay_of_mem g.2

theorem iteratedFDeriv_sub (f g : ElemSchwartz m n r s d) (k : ℕ) (a : Fin r → ℤ)
    (b : (i : Fin s) → ZMod (d i)) (xt : (Fin m → ℝ) × (Fin n → ℝ)) :
    iteratedFDeriv ℝ k (elemLift (f - g).toFun a b) xt =
      iteratedFDeriv ℝ k (elemLift f.toFun a b) xt - iteratedFDeriv ℝ k (elemLift g.toFun a b) xt := by
  have h0 : elemLift (f - g).toFun a b = elemLift f.toFun a b - elemLift g.toFun a b := rfl
  rw [h0, iteratedFDeriv_sub_apply (((isRapidDecay_toFun f).1 a b).contDiffAt.of_le (top_le k))
    (((isRapidDecay_toFun g).1 a b).contDiffAt.of_le (top_le k))]

/-- the family of weighted derivatives defining the topology -/
noncomputable def Φ (g : ElemSchwartz m n r s d) (p : ℕ × ℕ × ℕ)
    (q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ))) :
    ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => (Fin m → ℝ) × (Fin n → ℝ)) ℂ :=
  (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) • iteratedFDeriv ℝ p.2.2 (elemLift g.toFun q.1 q.2.1) q.2.2

lemma continuous_Φ (p : ℕ × ℕ × ℕ) :
    Continuous (fun g : ElemSchwartz m n r s d => UniformFun.ofFun (Φ g p)) := by
  have h := continuous_induced_rng.1 (continuous_id (X := ElemSchwartz m n r s d))
  exact (continuous_apply p).comp h

lemma eventually_close (p : ℕ × ℕ × ℕ) (g₀ : ElemSchwartz m n r s d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ g in 𝓝 g₀, ∀ q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ)),
      ‖‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1 *
      ‖iteratedFDeriv ℝ p.2.2 (elemLift (g - g₀).toFun q.1 q.2.1) q.2.2‖‖ < δ := by
  have h := (continuous_Φ (m := m) (n := n) (r := r) (s := s) (d := d) p).tendsto g₀
  rw [UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff] at h
  filter_upwards [h δ hδ] with g hg q
  have := hg q
  simp only [Function.comp_apply, UniformFun.toFun_ofFun, Φ, dist_eq_norm] at this
  erw [← smul_sub, norm_smul, norm_sub_rev, ← iteratedFDeriv_sub] at this
  rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this ⊢

theorem main {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (L : ElemSchwartz m n r s d →+ ElemSchwartz m' n' r' s' d')
    (hL : ∀ p : ℕ × ℕ × ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (C : ℝ), ∀ (g : ElemSchwartz m n r s d) (M : ℝ),
      (∀ p' ∈ S, ∀ a b xt, ‖a‖ ^ p'.2.1 * ‖xt.1‖ ^ p'.1 *
        ‖iteratedFDeriv ℝ p'.2.2 (elemLift g.toFun a b) xt‖ ≤ M) →
      ∀ a b xt, ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 *
        ‖iteratedFDeriv ℝ p.2.2 (elemLift (L g).toFun a b) xt‖ ≤ C * M) :
    Continuous L := by
  refine continuous_induced_rng.2 (continuous_pi fun p => ?_)
  obtain ⟨S, C, hC⟩ := hL p
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  show Tendsto (fun g => UniformFun.ofFun (Φ (L g) p)) (𝓝 g₀) (𝓝 (UniformFun.ofFun (Φ (L g₀) p)))
  rw [UniformFun.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  intro ε hε
  set δ := ε / (2 * (|C| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hS := (eventually_all_finset S).2 fun p' _ => eventually_close p' g₀ hδ
  filter_upwards [hS] with g hg q
  have hM : ∀ p' ∈ S, ∀ a b xt, ‖a‖ ^ p'.2.1 * ‖xt.1‖ ^ p'.1 *
      ‖iteratedFDeriv ℝ p'.2.2 (elemLift (g - g₀).toFun a b) xt‖ ≤ δ := by
    intro p' hp' a b xt
    have := hg p' hp' (a, b, xt)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    exact this.le
  have hb := hC (g - g₀) δ hM q.1 q.2.1 q.2.2
  rw [map_sub, iteratedFDeriv_sub] at hb
  simp only [Function.comp_apply, UniformFun.toFun_ofFun, Φ, dist_eq_norm]
  erw [← smul_sub, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc _ ≤ C * δ := hb
    _ ≤ (|C| + 1) * δ := mul_le_mul_of_nonneg_right ((le_abs_self C).trans (by linarith)) hδ.le
    _ = ε / 2 := by rw [hδdef]; field_simp
    _ < ε := by linarith

end MasulloGRHContAux

open MasulloGRH in
theorem solution {m n r s : ℕ} {d : Fin s → ℕ}
    {m' n' r' s' : ℕ} {d' : Fin s' → ℕ}
    (L : ElemSchwartz m n r s d →+ ElemSchwartz m' n' r' s' d')
    (hL : ∀ p : ℕ × ℕ × ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (C : ℝ),
      ∀ (g : ElemSchwartz m n r s d) (M : ℝ),
        (∀ p' ∈ S, ∀ a b xt, ‖a‖ ^ p'.2.1 * ‖xt.1‖ ^ p'.1 *
          ‖iteratedFDeriv ℝ p'.2.2 (elemLift g.toFun a b) xt‖ ≤ M) →
        ∀ a b xt, ‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1 *
          ‖iteratedFDeriv ℝ p.2.2 (elemLift (L g).toFun a b) xt‖ ≤ C * M) :
    Continuous L :=
  MasulloGRHContAux.main L hL
