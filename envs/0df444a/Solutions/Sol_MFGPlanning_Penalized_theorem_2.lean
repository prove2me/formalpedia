-- Prove2me | solution 1 for MFGPlanning.Penalized.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T02:31:00.071647+00:00
-- url     : https://prove2.me/submissions/090ae63d-1bad-45c1-b983-6e2ac58b735e

import Mathlib
import Definitions.Def_MFGPlanning_Penalized_Grid
import Definitions.Def_MFGPlanning_Penalized_Hyp
import Definitions.Def_MFGPlanning_Penalized_Scheme
import Definitions.Def_MFGPlanning_Penalized_Duality

set_option autoImplicit false

section part0
open Finset

namespace MFGPlanning.Penalized
namespace C3

/-- `0 < N_T` as an instance (used locally). -/
theorem neZeroNT (d : Data) : NeZero d.NT := ⟨d.hNT.ne'⟩

attribute [local instance] neZeroNT

/-- `𝓕(Ψ) = (1/Δt)(∑ m0 Ψ⁰ − ∑ mT Ψ^{N_T})`. -/
noncomputable def F (d : Data) (Ψ : Fin (d.NT + 1) → Pt d → ℝ) : ℝ :=
  (1 / d.Δt) * (∑ p, d.m0 p * Ψ 0 p - ∑ p, d.mT p * Ψ (Fin.last d.NT) p)

/-- `Λ(Ψ) = (α, β)`. -/
noncomputable def Lam (d : Data) (Ψ : Fin (d.NT + 1) → Pt d → ℝ) :
    (Fin d.NT → Pt d → ℝ) × (Fin d.NT → Pt d → Fin 4 → ℝ) :=
  (fun k p => (Ψ k.succ p - Ψ k.castSucc p) / d.Δt - d.ν * lap d (Ψ k.succ) p,
   fun k p => Dh d (Ψ k.succ) p)

/-- the planning constraint with `M⁰ = m0`. -/
def PlanningConstraint (d : Data) (M : Fin d.NT → Pt d → ℝ) (Z : Fin d.NT → Pt d → Fin 4 → ℝ) :
    Prop :=
  (∀ (n : Fin d.NT) (p : Pt d),
      ((Fin.snoc (α := fun _ => Pt d → ℝ) M d.mT n.succ p) - M n p) / d.Δt
        + d.ν * lap d (M n) p + divh d (Z n) p = 0) ∧
  M 0 = d.m0

end C3
end MFGPlanning.Penalized
end part0

section part1
open Filter Topology Set

namespace C3phi

lemma superlin {W : ℝ → ℝ} (hW : Tendsto (fun m : ℝ => W m / |m|) (cocompact ℝ) atTop) (c : ℝ) :
    ∃ R, 0 < R ∧ ∀ m, R ≤ m → c * m ≤ W m := by
  have h1 : ∀ᶠ m in atTop, c ≤ W m / |m| :=
    (hW.eventually (eventually_ge_atTop c)).filter_mono atTop_le_cocompact
  obtain ⟨R, hR⟩ := eventually_atTop.mp h1
  refine ⟨max R 1, by positivity, fun m hm => ?_⟩
  have hm1 : 0 < m := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hm)
  have := hR m (le_trans (le_max_left _ _) hm)
  rw [abs_of_pos hm1, le_div_iff₀ hm1] at this
  exact this

lemma exists_max {W : ℝ → ℝ} (hc : Continuous W)
    (hW : Tendsto (fun m : ℝ => W m / |m|) (cocompact ℝ) atTop) (a : ℝ) :
    ∃ m, 0 ≤ m ∧ ∀ m', 0 ≤ m' → a * m' - W m' ≤ a * m - W m := by
  obtain ⟨R, hR0, hR⟩ := superlin hW (a + 1)
  set R' := max R (|W 0| + 1) with hR'
  have hR'0 : (0:ℝ) ≤ R' := le_trans hR0.le (le_max_left _ _)
  have hK : IsCompact (Icc (0:ℝ) R') := isCompact_Icc
  have hne : (Icc (0:ℝ) R').Nonempty := ⟨0, le_rfl, hR'0⟩
  have hcont : Continuous fun x : ℝ => a * x - W x := by fun_prop
  obtain ⟨m, hm, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  refine ⟨m, hm.1, fun m' hm' => ?_⟩
  by_cases h : m' ≤ R'
  · exact isMaxOn_iff.mp hmax m' ⟨hm', h⟩
  · push Not at h
    have h0 := isMaxOn_iff.mp hmax 0 ⟨le_rfl, hR'0⟩
    have h1 := hR m' (le_trans (le_max_left _ _) h.le)
    have h2 : |W 0| + 1 ≤ R' := le_max_right _ _
    have h3 := le_abs_self (W 0)
    have h4 : (a + 1) * m' = a * m' + m' := by ring
    simp only [mul_zero, zero_sub] at h0
    linarith

lemma max_unique {W : ℝ → ℝ} (hs : StrictConvexOn ℝ univ W) (a m₁ m₂ : ℝ) (h1 : 0 ≤ m₁)
    (h2 : 0 ≤ m₂)
    (hm₁ : ∀ m', 0 ≤ m' → a * m' - W m' ≤ a * m₁ - W m₁)
    (hm₂ : ∀ m', 0 ≤ m' → a * m' - W m' ≤ a * m₂ - W m₂) : m₁ = m₂ := by
  by_contra hne
  have := hs.2 (mem_univ m₁) (mem_univ m₂) hne (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simp only [smul_eq_mul] at this
  have h3 := hm₁ ((1/2) * m₁ + (1/2) * m₂) (by positivity)
  have h4 := hm₂ m₁ h1
  have h5 := hm₁ m₂ h2
  have h6 : a * ((1/2) * m₁ + (1/2) * m₂) = (1/2) * (a * m₁) + (1/2) * (a * m₂) := by ring
  linarith

lemma lim_is_max {W : ℝ → ℝ} (hc : Continuous W) (m : ℝ → ℝ) (hm0 : ∀ a, 0 ≤ m a)
    (hmax : ∀ a m', 0 ≤ m' → a * m' - W m' ≤ a * m a - W (m a))
    (l : Filter ℝ) [l.NeBot] (a L : ℝ) (hl : Tendsto id l (𝓝 a)) (hL : Tendsto m l (𝓝 L)) :
    0 ≤ L ∧ ∀ m', 0 ≤ m' → a * m' - W m' ≤ a * L - W L := by
  refine ⟨ge_of_tendsto hL (Eventually.of_forall hm0), fun m' hm' => ?_⟩
  have t1 : Tendsto (fun b : ℝ => b * m' - W m') l (𝓝 (a * m' - W m')) :=
    (hl.mul_const m').sub_const _
  have t2 : Tendsto (fun b : ℝ => b * m b - W (m b)) l (𝓝 (a * L - W L)) :=
    (hl.mul hL).sub ((hc.tendsto L).comp hL)
  exact le_of_tendsto_of_tendsto t1 t2 (Eventually.of_forall fun b => hmax b m' hm')

/-- The conjugate `(W + χ)^*` is a real differentiable function with derivative the maximiser. -/
theorem phi_props {W : ℝ → ℝ} (h2 : ContDiff ℝ 2 W) (hs : StrictConvexOn ℝ univ W)
    (hW : Tendsto (fun m : ℝ => W m / |m|) (cocompact ℝ) atTop) :
    ∃ φ φ' : ℝ → ℝ,
      (∀ a, (⨆ (m : ℝ) (_ : 0 ≤ m), ((a * m - W m : ℝ) : EReal)) = (φ a : EReal)) ∧
      (∀ a, HasDerivAt φ (φ' a) a) ∧ (∀ a, 0 ≤ φ' a) ∧
      (∀ a, 0 < φ' a → deriv W (φ' a) = a) ∧
      (∀ a b, φ a + (b - a) * φ' a ≤ φ b) ∧
      (∀ a m, 0 ≤ m → a * m - W m ≤ φ a) ∧
      (∀ a, φ a = a * φ' a - W (φ' a)) := by
  have hc : Continuous W := h2.continuous
  have hd : Differentiable ℝ W := h2.differentiable (by norm_num)
  choose m hm0 hmax using exists_max hc hW
  set φ : ℝ → ℝ := fun a => a * m a - W (m a) with hφ
  have sub : ∀ a b, φ a + (b - a) * m a ≤ φ b := by
    intro a b
    have := hmax b (m a) (hm0 a)
    simp only [hφ]
    nlinarith
  have mono : Monotone m := by
    intro a b hab
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · by_contra hc'
      push Not at hc'
      have h1 := sub a b
      have h2 := sub b a
      nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hc')]
  -- one-sided limits of the maximiser
  have right : ∀ a, Tendsto m (𝓝[>] a) (𝓝 (m a)) := by
    intro a
    have hT := mono.tendsto_nhdsGT a
    obtain ⟨hL0, hLmax⟩ := lim_is_max hc m hm0 hmax (𝓝[>] a) a _
      (tendsto_id.mono_left nhdsWithin_le_nhds) hT
    have := max_unique hs a _ _ hL0 (hm0 a) hLmax (hmax a)
    rw [this] at hT
    exact hT
  have left : ∀ a, Tendsto m (𝓝[<] a) (𝓝 (m a)) := by
    intro a
    have hT := mono.tendsto_nhdsLT a
    obtain ⟨hL0, hLmax⟩ := lim_is_max hc m hm0 hmax (𝓝[<] a) a _
      (tendsto_id.mono_left nhdsWithin_le_nhds) hT
    have := max_unique hs a _ _ hL0 (hm0 a) hLmax (hmax a)
    rw [this] at hT
    exact hT
  refine ⟨φ, m, fun a => ?_, fun a => ?_, hm0, fun a ha => ?_, sub, fun a x hx => hmax a x hx,
    fun a => rfl⟩
  · apply le_antisymm
    · exact iSup₂_le fun x hx => EReal.coe_le_coe_iff.2 (hmax a x hx)
    · exact le_iSup₂_of_le (m a) (hm0 a) le_rfl
  · rw [hasDerivAt_iff_tendsto_slope, ← nhdsLT_sup_nhdsGT]
    refine Tendsto.sup ?_ ?_
    · -- left: m b ≤ slope ≤ m a
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (left a) tendsto_const_nhds ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with b hb
        have hb' : b - a < 0 := sub_neg.2 hb
        rw [slope_def_field, le_div_iff_of_neg hb']
        have := sub b a
        nlinarith
      · filter_upwards [self_mem_nhdsWithin] with b hb
        have hb' : b - a < 0 := sub_neg.2 hb
        rw [slope_def_field, div_le_iff_of_neg hb']
        have := sub a b
        nlinarith
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (right a) ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with b hb
        have hb' : 0 < b - a := sub_pos.2 hb
        rw [slope_def_field, le_div_iff₀ hb']
        have := sub a b
        nlinarith
      · filter_upwards [self_mem_nhdsWithin] with b hb
        have hb' : 0 < b - a := sub_pos.2 hb
        rw [slope_def_field, div_le_iff₀ hb']
        have := sub b a
        nlinarith
  · have hloc : IsLocalMax (fun x : ℝ => a * x - W x) (m a) := by
      filter_upwards [Ioi_mem_nhds ha] with x hx
      exact hmax a x (le_of_lt hx)
    have hder : HasDerivAt (fun x : ℝ => a * x - W x) (a * 1 - deriv W (m a)) (m a) :=
      ((hasDerivAt_id (m a)).const_mul a).sub (hd (m a)).hasDerivAt
    have := hloc.hasDerivAt_eq_zero hder
    linarith

end C3phi
end part1

section part2
open Finset

namespace MFGPlanning.Penalized
namespace C3

attribute [local instance] neZeroNT

variable (d : Data)

lemma sum_shift1 (f : (Pt d) → ℝ) (c : ZMod d.Nh) : ∑ p : (Pt d), f (p.1 + c, p.2) = ∑ p, f p :=
  Fintype.sum_equiv ((Equiv.addRight c).prodCongr (Equiv.refl _)) _ _ (fun _ => rfl)

lemma sum_shift1' (f : (Pt d) → ℝ) (c : ZMod d.Nh) : ∑ p : (Pt d), f (p.1 - c, p.2) = ∑ p, f p :=
  Fintype.sum_equiv ((Equiv.subRight c).prodCongr (Equiv.refl _)) _ _ (fun _ => rfl)

lemma sum_shift2 (f : (Pt d) → ℝ) (c : ZMod d.Nh) : ∑ p : (Pt d), f (p.1, p.2 + c) = ∑ p, f p :=
  Fintype.sum_equiv ((Equiv.refl _).prodCongr (Equiv.addRight c)) _ _ (fun _ => rfl)

lemma sum_shift2' (f : (Pt d) → ℝ) (c : ZMod d.Nh) : ∑ p : (Pt d), f (p.1, p.2 - c) = ∑ p, f p :=
  Fintype.sum_equiv ((Equiv.refl _).prodCongr (Equiv.subRight c)) _ _ (fun _ => rfl)

/-- the four "move a shift across a product" identities -/
lemma sh_a (A B : (Pt d) → ℝ) :
    ∑ p : (Pt d), A p * B (p.1 + 1, p.2) = ∑ p : (Pt d), B p * A (p.1 - 1, p.2) := by
  rw [← sum_shift1 d (fun p => B p * A (p.1 - 1, p.2)) 1]
  refine sum_congr rfl fun p _ => ?_
  simp [mul_comm]

lemma sh_b (A B : (Pt d) → ℝ) :
    ∑ p : (Pt d), A p * B (p.1 - 1, p.2) = ∑ p : (Pt d), B p * A (p.1 + 1, p.2) := by
  rw [← sum_shift1' d (fun p => B p * A (p.1 + 1, p.2)) 1]
  refine sum_congr rfl fun p _ => ?_
  simp [mul_comm]

lemma sh_c (A B : (Pt d) → ℝ) :
    ∑ p : (Pt d), A p * B (p.1, p.2 + 1) = ∑ p : (Pt d), B p * A (p.1, p.2 - 1) := by
  rw [← sum_shift2 d (fun p => B p * A (p.1, p.2 - 1)) 1]
  refine sum_congr rfl fun p _ => ?_
  simp [mul_comm]

lemma sh_d (A B : (Pt d) → ℝ) :
    ∑ p : (Pt d), A p * B (p.1, p.2 - 1) = ∑ p : (Pt d), B p * A (p.1, p.2 + 1) := by
  rw [← sum_shift2' d (fun p => B p * A (p.1, p.2 + 1)) 1]
  refine sum_congr rfl fun p _ => ?_
  simp [mul_comm]

lemma sum_mul_lap (M V : (Pt d) → ℝ) : ∑ p, M p * lap d V p = ∑ p, V p * lap d M p := by
  have e : ∀ A B : (Pt d) → ℝ, ∑ p, A p * lap d B p =
      -(1 / d.h ^ 2) * (4 * ∑ p, A p * B p - ∑ p, A p * B (p.1 + 1, p.2)
        - ∑ p, A p * B (p.1 - 1, p.2) - ∑ p, A p * B (p.1, p.2 + 1)
        - ∑ p, A p * B (p.1, p.2 - 1)) := by
    intro A B
    simp only [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    unfold lap; ring
  rw [e, e, sh_a d M V, sh_b d M V, sh_c d M V, sh_d d M V]
  have : ∑ p, M p * V p = ∑ p, V p * M p := sum_congr rfl fun p _ => mul_comm _ _
  rw [this]; ring

lemma Dh0 (V : (Pt d) → ℝ) (p : (Pt d)) : Dh d V p 0 = D1 d V p := rfl
lemma Dh1 (V : (Pt d) → ℝ) (p : (Pt d)) : Dh d V p 1 = D1 d V (p.1 - 1, p.2) := rfl
lemma Dh2 (V : (Pt d) → ℝ) (p : (Pt d)) : Dh d V p 2 = D2 d V p := rfl
lemma Dh3 (V : (Pt d) → ℝ) (p : (Pt d)) : Dh d V p 3 = D2 d V (p.1, p.2 - 1) := rfl

lemma sum_Z_Dh (Z : (Pt d) → Fin 4 → ℝ) (V : (Pt d) → ℝ) :
    ∑ p, ∑ l, Z p l * Dh d V p l = -∑ p, V p * divh d Z p := by
  have e1 : ∑ p, ∑ l, Z p l * Dh d V p l =
      (1 / d.h) * ((∑ p, (fun q => Z q 0) p * V (p.1 + 1, p.2) - ∑ p, Z p 0 * V p)
        + (∑ p, Z p 1 * V p - ∑ p, (fun q => Z q 1) p * V (p.1 - 1, p.2))
        + (∑ p, (fun q => Z q 2) p * V (p.1, p.2 + 1) - ∑ p, Z p 2 * V p)
        + (∑ p, Z p 3 * V p - ∑ p, (fun q => Z q 3) p * V (p.1, p.2 - 1))) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    simp only [Fin.sum_univ_four, Dh0, Dh1, Dh2, Dh3, D1, D2, sub_add_cancel]
    field_simp
    try ring
  have e2 : ∑ p, V p * divh d Z p =
      (1 / d.h) * ((∑ p, V p * Z p 0 - ∑ p, V p * (fun q => Z q 0) (p.1 - 1, p.2))
        + (∑ p, V p * (fun q => Z q 1) (p.1 + 1, p.2) - ∑ p, V p * Z p 1)
        + (∑ p, V p * Z p 2 - ∑ p, V p * (fun q => Z q 2) (p.1, p.2 - 1))
        + (∑ p, V p * (fun q => Z q 3) (p.1, p.2 + 1) - ∑ p, V p * Z p 3)) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    unfold divh; ring
  rw [e1, e2, sh_a d (fun q => Z q 0) V, sh_b d (fun q => Z q 1) V, sh_c d (fun q => Z q 2) V,
    sh_d d (fun q => Z q 3) V]
  beta_reduce
  have c : ∀ l : Fin 4, ∑ p, Z p l * V p = ∑ p, V p * Z p l :=
    fun l => sum_congr rfl fun p _ => mul_comm _ _
  rw [c 0, c 1, c 2, c 3]
  ring

lemma time_sbp (n : ℕ) (a v : Fin (n + 1) → ℝ) :
    ∑ k : Fin n, a k.castSucc * (v k.succ - v k.castSucc) =
      ∑ k : Fin n, (a k.castSucc - a k.succ) * v k.succ + a (Fin.last n) * v (Fin.last n)
        - a 0 * v 0 := by
  have h1 := Fin.sum_univ_succ (fun j => a j * v j)
  have h2 := Fin.sum_univ_castSucc (fun j => a j * v j)
  simp only [mul_sub, sub_mul, sum_sub_distrib]
  linarith

/-- Summation by parts: `pair(M, Z, Λ V) + 𝓕(V)` against the residual of the planning constraint. -/
theorem pair_lam_F (M : Fin d.NT → (Pt d) → ℝ) (Z : Fin d.NT → (Pt d) → Fin 4 → ℝ)
    (V : Fin (d.NT + 1) → (Pt d) → ℝ) :
    pair d M Z (Lam d V).1 (Lam d V).2 + F d V =
      -(∑ k, ∑ p, V k.succ p *
          (((Fin.snoc (α := fun _ => (Pt d) → ℝ) M d.mT k.succ p) - M k p) / d.Δt
            + d.ν * lap d (M k) p + divh d (Z k) p))
        + (1 / d.Δt) * ∑ p, V 0 p * (d.m0 p - M 0 p) := by
  set Mt : Fin (d.NT + 1) → (Pt d) → ℝ := Fin.snoc (α := fun _ => (Pt d) → ℝ) M d.mT with hMt
  have hcs : ∀ k : Fin d.NT, Mt k.castSucc = M k := fun k => by simp [hMt]
  have hlast : Mt (Fin.last d.NT) = d.mT := by simp [hMt]
  have h0 : Mt 0 = M 0 := by
    rw [← hcs 0]; simp
  -- per-point time summation by parts
  have tp : ∀ p, ∑ k : Fin d.NT, M k p * (V k.succ p - V k.castSucc p) =
      ∑ k : Fin d.NT, (M k p - Mt k.succ p) * V k.succ p + d.mT p * V (Fin.last d.NT) p
        - M 0 p * V 0 p := by
    intro p
    have := time_sbp d.NT (fun j => Mt j p) (fun j => V j p)
    simp only [hcs, hlast, h0] at this
    exact this
  have hpair : pair d M Z (Lam d V).1 (Lam d V).2 =
      ∑ k, ((1 / d.Δt) * ∑ p, M k p * (V k.succ p - V k.castSucc p)
        - d.ν * ∑ p, V k.succ p * lap d (M k) p - ∑ p, V k.succ p * divh d (Z k) p) := by
    unfold pair Lam
    refine sum_congr rfl fun k _ => ?_
    simp only
    have hz := sum_Z_Dh d (Z k) (V k.succ)
    rw [← sum_mul_lap, show ∑ p, V k.succ p * divh d (Z k) p
      = -∑ p, ∑ l, Z k p l * Dh d (V k.succ) p l by linarith, sub_neg_eq_add]
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    ring
  have hA : ∑ k : Fin d.NT, ∑ p, M k p * (V k.succ p - V k.castSucc p) =
      ∑ k : Fin d.NT, ∑ p, (M k p - Mt k.succ p) * V k.succ p + ∑ p, d.mT p * V (Fin.last d.NT) p
        - ∑ p, M 0 p * V 0 p := by
    rw [sum_comm, sum_congr rfl (fun p _ => tp p)]
    simp only [sum_add_distrib, sum_sub_distrib]
    rw [sum_comm]
  have hR : ∑ k : Fin d.NT, ∑ p, V k.succ p * ((Mt k.succ p - M k p) / d.Δt
      + d.ν * lap d (M k) p + divh d (Z k) p) =
      -(1 / d.Δt) * ∑ k : Fin d.NT, ∑ p, (M k p - Mt k.succ p) * V k.succ p
        + d.ν * ∑ k : Fin d.NT, ∑ p, V k.succ p * lap d (M k) p
        + ∑ k : Fin d.NT, ∑ p, V k.succ p * divh d (Z k) p := by
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => sum_congr rfl fun p _ => ?_
    ring
  have hL : ∑ k : Fin d.NT, ((1 / d.Δt) * ∑ p, M k p * (V k.succ p - V k.castSucc p)
      - d.ν * ∑ p, V k.succ p * lap d (M k) p - ∑ p, V k.succ p * divh d (Z k) p) =
      (1 / d.Δt) * ∑ k : Fin d.NT, ∑ p, M k p * (V k.succ p - V k.castSucc p)
        - d.ν * ∑ k : Fin d.NT, ∑ p, V k.succ p * lap d (M k) p
        - ∑ k : Fin d.NT, ∑ p, V k.succ p * divh d (Z k) p := by
    simp only [sum_sub_distrib, ← mul_sum]
  have h0' : ∑ p, V 0 p * (d.m0 p - M 0 p) = ∑ p, d.m0 p * V 0 p - ∑ p, M 0 p * V 0 p := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun p _ => by ring
  have hT : ∑ p, d.mT p * V (Fin.last d.NT) p = ∑ p, d.mT p * V (Fin.last d.NT) p := rfl
  rw [hpair, hL, hA, hR, h0']
  unfold F
  ring

end C3
end MFGPlanning.Penalized
end part2

section part3
open Finset

namespace MFGPlanning.Penalized
namespace C3

attribute [local instance] neZeroNT

variable (d : Data)

lemma single_eq_smul (q : Fin 4 → ℝ) (l : Fin 4) :
    (Pi.single l (q l) : Fin 4 → ℝ) = q l • (Pi.single l (1 : ℝ) : Fin 4 → ℝ) := by
  ext j
  by_cases h : j = l
  · subst h; simp
  · simp [h]

lemma fderiv_expand (L : (Fin 4 → ℝ) →L[ℝ] ℝ) (q : Fin 4 → ℝ) :
    L q = ∑ l, q l * L (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single q]
  rw [map_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [single_eq_smul, map_smul, smul_eq_mul]

/-- tangent-plane lower bound of a convex function differentiable at `0`. -/
lemma affine_minorant (f : (Fin 4 → ℝ) → ℝ) (hc : ConvexOn ℝ Set.univ f)
    (hd : DifferentiableAt ℝ f 0) (q : Fin 4 → ℝ) :
    f 0 + ∑ l, q l * fderiv ℝ f 0 (Pi.single l 1) ≤ f q := by
  set φ : ℝ → ℝ := fun t => f (t • q) with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    have h := hc.comp_linearMap (LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ) q)
    rw [Set.preimage_univ] at h
    exact h
  have hφd : HasDerivAt φ (fderiv ℝ f 0 q) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • q) ((1 : ℝ) • q) 0 := (hasDerivAt_id 0).smul_const q
    have h2 : HasFDerivAt f (fderiv ℝ f 0) ((0 : ℝ) • q) := by simpa using hd.hasFDerivAt
    have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
    rw [one_smul] at h3
    exact h3
  have := hφc.deriv_le_slope (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hφd.differentiableAt
  rw [hφd.deriv, slope_def_field] at this
  simp only [hφ, one_smul, zero_smul, sub_zero, div_one] at this
  rw [fderiv_expand] at this
  linarith

/-- the linear bookkeeping of `gbox` (sixteen cases). -/
lemma comb (g zq G0 AL BL P0 P1 P2 P3 Q0 Q1 Q2 Q3 R0 R1 R2 R3 : ℝ) (hG0 : 0 ≤ G0)
    (hAL : 0 ≤ AL) (hBL : 0 ≤ BL) (hP0 : 0 ≤ P0) (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) (hP3 : 0 ≤ P3)
    (hQ0 : 0 ≤ Q0) (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (hQ3 : 0 ≤ Q3)
    (hR0 : 0 ≤ R0) (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) (hR3 : 0 ≤ R3)
    (hX : -G0 - (P0 + P1 + P2 + P3) - (R0 + R1 + R2 + R3) ≤ g)
    (hz : zq ≤ (Q0 + Q1 + Q2 + Q3) - (R0 + R1 + R2 + R3))
    (d0 : (P0 ≤ AL ∧ Q0 ≤ BL) ∨ 5 * P0 + 5 * Q0 ≤ g)
    (d1 : (P1 ≤ AL ∧ Q1 ≤ BL) ∨ 5 * P1 + 5 * Q1 ≤ g)
    (d2 : (P2 ≤ AL ∧ Q2 ≤ BL) ∨ 5 * P2 + 5 * Q2 ≤ g)
    (d3 : (P3 ≤ AL ∧ Q3 ≤ BL) ∨ 5 * P3 + 5 * Q3 ≤ g) :
    zq - (G0 + 4 * AL + 4 * BL) ≤ g := by
  rcases d0 with ⟨a0, b0⟩ | d0 <;> rcases d1 with ⟨a1, b1⟩ | d1 <;>
    rcases d2 with ⟨a2, b2⟩ | d2 <;> rcases d3 with ⟨a3, b3⟩ | d3 <;> linarith

/-- (G3)–(G5) give a uniform bound `g(x, q) ≥ z·q − K` for `z` in the box where `g^*` is finite. -/
theorem gbox (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) :
    ∃ A1 : ℝ, 0 ≤ A1 ∧ ∀ B : ℝ, ∃ K : ℝ, ∀ (p : (Pt d)) (q z : Fin 4 → ℝ),
      -B ≤ z 0 → z 0 ≤ -A1 → A1 ≤ z 1 → z 1 ≤ B → -B ≤ z 2 → z 2 ≤ -A1 → A1 ≤ z 3 →
      z 3 ≤ B → ∑ l, z l * q l - K ≤ d.g p q := by
  set a : (Pt d) → Fin 4 → ℝ := fun p l => fderiv ℝ (d.g p) 0 (Pi.single l 1) with ha
  set A1 : ℝ := ∑ p, ∑ l, |a p l| with hA1
  set G0 : ℝ := ∑ p, |d.g p 0| with hG0
  have hA1a : ∀ p l, |a p l| ≤ A1 := by
    intro p l
    have h1 : |a p l| ≤ ∑ l', |a p l'| :=
      single_le_sum (f := fun l' => |a p l'|) (fun _ _ => abs_nonneg _) (mem_univ l)
    have h2 : ∑ l', |a p l'| ≤ A1 :=
      single_le_sum (f := fun p' => ∑ l', |a p' l'|)
        (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ p)
    linarith
  have hG0p : ∀ p, |d.g p 0| ≤ G0 := fun p =>
    single_le_sum (f := fun p' => |d.g p' 0|) (fun _ _ => abs_nonneg _) (mem_univ p)
  have hA10 : 0 ≤ A1 := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hG00 : 0 ≤ G0 := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨A1, hA10, fun B => ?_⟩
  obtain ⟨⟨L0, h0⟩, ⟨L1, h1⟩, ⟨L2, h2⟩, ⟨L3, h3⟩⟩ :=
    (⟨hG5.1 (5 * (A1 + B)), hG5.2.1 (5 * (A1 + B)), hG5.2.2.1 (5 * (A1 + B)),
      hG5.2.2.2 (5 * (A1 + B))⟩ : _ ∧ _ ∧ _ ∧ _)
  set L : ℝ := |L0| + |L1| + |L2| + |L3| with hL
  have hL0 : 0 ≤ L := by positivity
  refine ⟨G0 + 4 * (A1 * L) + 4 * (B * L), fun p q z hz0 hz0' hz1 hz1' hz2 hz2' hz3 hz3' => ?_⟩
  have hB : 0 ≤ B := by linarith
  -- affine minorant
  have hX := affine_minorant (d.g p) (hG4 p) ((hG3 p).differentiable (by norm_num) 0) q
  simp only [Fin.sum_univ_four] at hX ⊢
  have hg0 : -G0 ≤ d.g p 0 := le_trans (neg_le_neg (hG0p p)) (neg_abs_le _)
  -- bad / good parts
  set b0 := max (-q 0) 0
  set c0 := max (q 0) 0
  set b1 := max (q 1) 0
  set c1 := max (-q 1) 0
  set b2 := max (-q 2) 0
  set c2 := max (q 2) 0
  set b3 := max (q 3) 0
  set c3 := max (-q 3) 0
  have e0 : q 0 = c0 - b0 := by
    rcases le_total (q 0) 0 with h | h
    · simp [b0, c0, max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    · simp [b0, c0, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
  have e1 : q 1 = b1 - c1 := by
    rcases le_total (q 1) 0 with h | h
    · simp [b1, c1, max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    · simp [b1, c1, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
  have e2 : q 2 = c2 - b2 := by
    rcases le_total (q 2) 0 with h | h
    · simp [b2, c2, max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    · simp [b2, c2, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
  have e3 : q 3 = b3 - c3 := by
    rcases le_total (q 3) 0 with h | h
    · simp [b3, c3, max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    · simp [b3, c3, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
  have pb0 : 0 ≤ b0 := le_max_right _ _
  have pb1 : 0 ≤ b1 := le_max_right _ _
  have pb2 : 0 ≤ b2 := le_max_right _ _
  have pb3 : 0 ≤ b3 := le_max_right _ _
  have pc0 : 0 ≤ c0 := le_max_right _ _
  have pc1 : 0 ≤ c1 := le_max_right _ _
  have pc2 : 0 ≤ c2 := le_max_right _ _
  have pc3 : 0 ≤ c3 := le_max_right _ _
  -- affine terms
  have aff : ∀ (l : Fin 4) (b c : ℝ), 0 ≤ b → 0 ≤ c → (q l = c - b ∨ q l = b - c) →
      -(A1 * b) - A1 * c ≤ q l * a p l := by
    intro l b c hb hc hq
    have habs : |q l| ≤ b + c := by
      rcases hq with hq | hq <;> rw [hq] <;> exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg hb, abs_of_nonneg hc]; try linarith)
    have h1 : |q l * a p l| ≤ (b + c) * A1 := by
      rw [abs_mul]; exact mul_le_mul habs (hA1a p l) (abs_nonneg _) (by linarith)
    have := neg_abs_le (q l * a p l)
    nlinarith
  have a0 := aff 0 b0 c0 pb0 pc0 (Or.inl e0)
  have a1 := aff 1 b1 c1 pb1 pc1 (Or.inr e1)
  have a2 := aff 2 b2 c2 pb2 pc2 (Or.inl e2)
  have a3 := aff 3 b3 c3 pb3 pc3 (Or.inr e3)
  -- the z-terms
  have z0 : z 0 * q 0 ≤ B * b0 - A1 * c0 := by
    have t : z 0 * q 0 = z 0 * c0 - z 0 * b0 := by rw [e0]; ring
    have u1 := mul_le_mul_of_nonneg_right hz0' pc0
    have u2 := mul_le_mul_of_nonneg_right hz0 pb0
    have u3 : -A1 * c0 = -(A1 * c0) := by ring
    have u4 : -B * b0 = -(B * b0) := by ring
    linarith
  have z1 : z 1 * q 1 ≤ B * b1 - A1 * c1 := by
    have t : z 1 * q 1 = z 1 * b1 - z 1 * c1 := by rw [e1]; ring
    have u1 := mul_le_mul_of_nonneg_right hz1' pb1
    have u2 := mul_le_mul_of_nonneg_right hz1 pc1
    linarith
  have z2 : z 2 * q 2 ≤ B * b2 - A1 * c2 := by
    have t : z 2 * q 2 = z 2 * c2 - z 2 * b2 := by rw [e2]; ring
    have u1 := mul_le_mul_of_nonneg_right hz2' pc2
    have u2 := mul_le_mul_of_nonneg_right hz2 pb2
    have u3 : -A1 * c2 = -(A1 * c2) := by ring
    have u4 : -B * b2 = -(B * b2) := by ring
    linarith
  have z3 : z 3 * q 3 ≤ B * b3 - A1 * c3 := by
    have t : z 3 * q 3 = z 3 * b3 - z 3 * c3 := by rw [e3]; ring
    have u1 := mul_le_mul_of_nonneg_right hz3' pb3
    have u2 := mul_le_mul_of_nonneg_right hz3 pc3
    linarith
  -- coercive directions
  have hLL0 : L0 ≤ L := by
    have := le_abs_self L0; have := abs_nonneg L1; have := abs_nonneg L2; have := abs_nonneg L3
    linarith
  have hLL1 : L1 ≤ L := by
    have := le_abs_self L1; have := abs_nonneg L0; have := abs_nonneg L2; have := abs_nonneg L3
    linarith
  have hLL2 : L2 ≤ L := by
    have := le_abs_self L2; have := abs_nonneg L1; have := abs_nonneg L0; have := abs_nonneg L3
    linarith
  have hLL3 : L3 ≤ L := by
    have := le_abs_self L3; have := abs_nonneg L1; have := abs_nonneg L2; have := abs_nonneg L0
    linarith
  have small : ∀ b : ℝ, b ≤ L → A1 * b ≤ A1 * L ∧ B * b ≤ B * L := fun b hb =>
    ⟨mul_le_mul_of_nonneg_left hb hA10, mul_le_mul_of_nonneg_left hb hB⟩
  have d0 : (A1 * b0 ≤ A1 * L ∧ B * b0 ≤ B * L) ∨ 5 * (A1 * b0) + 5 * (B * b0) ≤ d.g p q := by
    rcases le_or_gt b0 L with h | h
    · exact Or.inl (small _ h)
    · right
      have hb : b0 = -q 0 := by
        rcases le_total (q 0) 0 with h' | h'
        · simp [b0, max_eq_left (neg_nonneg.2 h')]
        · simp [b0, max_eq_right (neg_nonpos.2 h')] at h ⊢; linarith
      have hq0 : q 0 ≤ 0 := by linarith
      have hq : q 0 ≤ -L0 := by linarith
      have := h0 p q hq
      rw [abs_of_nonpos hq0, ← hb] at this
      linarith
  have d1 : (A1 * b1 ≤ A1 * L ∧ B * b1 ≤ B * L) ∨ 5 * (A1 * b1) + 5 * (B * b1) ≤ d.g p q := by
    rcases le_or_gt b1 L with h | h
    · exact Or.inl (small _ h)
    · right
      have hb : b1 = q 1 := by
        rcases le_total (q 1) 0 with h' | h'
        · simp [b1, max_eq_right h'] at h ⊢; linarith
        · simp [b1, max_eq_left h']
      have := h1 p q (by linarith)
      rw [← hb] at this; linarith
  have d2 : (A1 * b2 ≤ A1 * L ∧ B * b2 ≤ B * L) ∨ 5 * (A1 * b2) + 5 * (B * b2) ≤ d.g p q := by
    rcases le_or_gt b2 L with h | h
    · exact Or.inl (small _ h)
    · right
      have hb : b2 = -q 2 := by
        rcases le_total (q 2) 0 with h' | h'
        · simp [b2, max_eq_left (neg_nonneg.2 h')]
        · simp [b2, max_eq_right (neg_nonpos.2 h')] at h ⊢; linarith
      have hq0 : q 2 ≤ 0 := by linarith
      have hq : q 2 ≤ -L2 := by linarith
      have := h2 p q hq
      rw [abs_of_nonpos hq0, ← hb] at this
      linarith
  have d3 : (A1 * b3 ≤ A1 * L ∧ B * b3 ≤ B * L) ∨ 5 * (A1 * b3) + 5 * (B * b3) ≤ d.g p q := by
    rcases le_or_gt b3 L with h | h
    · exact Or.inl (small _ h)
    · right
      have hb : b3 = q 3 := by
        rcases le_total (q 3) 0 with h' | h'
        · simp [b3, max_eq_right h'] at h ⊢; linarith
        · simp [b3, max_eq_left h']
      have := h3 p q (by linarith)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ q 3), ← hb] at this; linarith
  have hXX : -G0 - (A1 * b0 + A1 * b1 + A1 * b2 + A1 * b3) - (A1 * c0 + A1 * c1 + A1 * c2 + A1 * c3)
      ≤ d.g p q := by linarith
  have hzz : z 0 * q 0 + z 1 * q 1 + z 2 * q 2 + z 3 * q 3 ≤
      (B * b0 + B * b1 + B * b2 + B * b3) - (A1 * c0 + A1 * c1 + A1 * c2 + A1 * c3) := by linarith
  exact comb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG00 (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hXX hzz d0 d1 d2 d3

end C3
end MFGPlanning.Penalized
end part3

section part4
open Finset

namespace MFGPlanning.Penalized
namespace C3

attribute [local instance] neZeroNT

/-- discrete antiderivative on `Fin (n+1)` with wrap-around. -/
lemma fin_antideriv (n : ℕ) (s : Fin (n + 1) → ℝ) (hs : ∑ x, s x = 0) :
    ∃ w : Fin (n + 1) → ℝ, ∀ x, w x - w (x - 1) = s x := by
  refine ⟨fun x => ∑ i : Fin (n + 1), if (i : ℕ) ≤ (x : ℕ) then s i else 0, fun x => ?_⟩
  simp only
  rw [Fin.coe_sub_one]
  by_cases hx : x = 0
  · simp only [hx, if_true]
    have h1 : ∑ i : Fin (n + 1), (if (i : ℕ) ≤ n then s i else 0) = 0 := by
      rw [← hs]
      exact sum_congr rfl fun i _ => if_pos (Nat.lt_succ_iff.mp i.isLt)
    rw [h1, sub_zero]
    rw [sum_eq_single (0 : Fin (n + 1))]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [Fin.val_zero, this]
    · simp
  · simp only [hx, if_false]
    have hx0 : (x : ℕ) ≠ 0 := fun h => hx (Fin.ext h)
    rw [← sum_sub_distrib, sum_eq_single x]
    · have : ¬ (x : ℕ) ≤ (x : ℕ) - 1 := by omega
      simp [this]
    · intro b _ hb
      have hb' : (b : ℕ) ≠ (x : ℕ) := fun h => hb (Fin.ext h)
      by_cases h1 : (b : ℕ) ≤ (x : ℕ)
      · have h2 : (b : ℕ) ≤ (x : ℕ) - 1 := by omega
        simp [h1, h2]
      · have h2 : ¬ (b : ℕ) ≤ (x : ℕ) - 1 := by omega
        simp [h1, h2]
    · simp

/-- discrete antiderivative on the cycle `ℤ/N`. -/
lemma cyc_antideriv (N : ℕ) [NeZero N] (s : ZMod N → ℝ) (hs : ∑ x, s x = 0) :
    ∃ w : ZMod N → ℝ, ∀ x, w x - w (x - 1) = s x := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos N)).symm⟩
  exact fin_antideriv n s hs

variable (d : Data)

/-- `div_h` is onto the zero-mean grid functions. -/
lemma divh_surj (f : (Pt d) → ℝ) (hf : ∑ p, f p = 0) : ∃ Z : (Pt d) → Fin 4 → ℝ, ∀ p, divh d Z p = f p := by
  have hN : (d.Nh : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d.Nh)
  set r : ZMod d.Nh → ℝ := fun j => ∑ i, f (i, j) with hr
  have hr0 : ∑ j, r j / d.Nh = 0 := by
    rw [← sum_div]
    have : ∑ j, r j = 0 := by
      rw [← hf, Fintype.sum_prod_type_right]
    rw [this, zero_div]
  obtain ⟨u, hu⟩ := cyc_antideriv d.Nh (fun j => r j / d.Nh) hr0
  have hs : ∀ j, ∑ i, (f (i, j) - r j / d.Nh) = 0 := by
    intro j
    rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    field_simp
    simp [hr]
  choose v hv using fun j => cyc_antideriv d.Nh (fun i => f (i, j) - r j / d.Nh) (hs j)
  set Z : (Pt d) → Fin 4 → ℝ := fun p => ![d.h * v p.2 p.1, 0, d.h * u p.2, 0] with hZ
  have z0 : ∀ q, Z q 0 = d.h * v q.2 q.1 := fun _ => rfl
  have z1 : ∀ q, Z q 1 = 0 := fun _ => rfl
  have z2 : ∀ q, Z q 2 = d.h * u q.2 := fun _ => rfl
  have z3 : ∀ q, Z q 3 = 0 := fun _ => rfl
  refine ⟨Z, fun p => ?_⟩
  have hh : d.h ≠ 0 := by unfold Data.h; exact inv_ne_zero hN
  unfold divh
  rw [z0, z0, z1, z1, z2, z2, z3, z3, ← mul_sub, ← mul_sub, mul_div_cancel_left₀ _ hh,
    mul_div_cancel_left₀ _ hh, hv p.2 p.1, hu p.2]
  simp only [sub_self, zero_div, add_zero, Prod.mk.eta]
  ring

/-- connectivity of the cycle -/
lemma cyc_const (N : ℕ) [NeZero N] (w : ZMod N → ℝ) (hw : ∀ x, w (x + 1) = w x) :
    ∀ x, w x = w 0 := by
  have : ∀ k : ℕ, w (k : ZMod N) = w 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, hw, ih]
  intro x
  rw [← ZMod.natCast_zmod_val x]
  exact this _

lemma torus_const (U : (Pt d) → ℝ) (h1 : ∀ p : (Pt d), U (p.1 + 1, p.2) = U p)
    (h2 : ∀ p : (Pt d), U (p.1, p.2 + 1) = U p) : ∀ p, U p = U (0, 0) := by
  intro p
  have a := cyc_const d.Nh (fun i => U (i, p.2)) (fun i => h1 (i, p.2)) p.1
  have b := cyc_const d.Nh (fun j => U (0, j)) (fun j => h2 (0, j)) p.2
  rw [a, b]

/-- the kernel of `Λ` consists of the constants. -/
lemma lam_ker (V : Fin (d.NT + 1) → (Pt d) → ℝ) (h : Lam d V = (0, 0)) :
    ∀ j p, V j p = V 0 (0, 0) := by
  have hh : d.h ≠ 0 := by
    unfold Data.h; exact inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne d.Nh))
  have hdt : d.Δt ≠ 0 := by
    unfold Data.Δt
    exact div_ne_zero d.hT.ne' (Nat.cast_ne_zero.2 (NeZero.ne d.NT))
  have hα : ∀ (k : Fin d.NT) (p : (Pt d)), (V k.succ p - V k.castSucc p) / d.Δt - d.ν * lap d (V k.succ) p = 0 :=
    fun k p => congrFun (congrFun (congrArg Prod.fst h) k) p
  have hβ : ∀ (k : Fin d.NT) (p : (Pt d)), Dh d (V k.succ) p = 0 :=
    fun k p => congrFun (congrFun (congrArg Prod.snd h) k) p
  have hconst : ∀ k : Fin d.NT, ∀ p, V k.succ p = V k.succ (0, 0) := by
    intro k
    apply torus_const
    · intro p
      have := congrFun (hβ k p) 0
      simp only [Dh, D1, Matrix.cons_val_zero, Pi.zero_apply, div_eq_zero_iff, hh, or_false]
        at this
      linarith
    · intro p
      have := congrFun (hβ k p) 2
      simp only [Dh, D2, Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.tail_cons,
        Matrix.head_cons, Pi.zero_apply, div_eq_zero_iff, hh, or_false] at this
      linarith
  have hlap : ∀ k : Fin d.NT, ∀ p, lap d (V k.succ) p = 0 := by
    intro k p
    unfold lap
    rw [hconst k p, hconst k (p.1 + 1, p.2), hconst k (p.1 - 1, p.2), hconst k (p.1, p.2 + 1),
      hconst k (p.1, p.2 - 1)]
    ring
  have hstep : ∀ k : Fin d.NT, ∀ p, V k.castSucc p = V k.succ (0, 0) := by
    intro k p
    have := hα k p
    rw [hlap, mul_zero, sub_zero, div_eq_zero_iff] at this
    rcases this with h' | h'
    · rw [← hconst k p]; linarith
    · exact absurd h' hdt
  -- every level equals the value at level 0
  have key : ∀ j : Fin (d.NT + 1), ∀ p, V j p = V 0 (0, 0) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro p
      have h0 := hstep ⟨0, NeZero.pos d.NT⟩ p
      have h1 := hstep ⟨0, NeZero.pos d.NT⟩ (0, 0)
      have e : (Fin.castSucc (⟨0, NeZero.pos d.NT⟩ : Fin d.NT)) = 0 := rfl
      rw [e] at h0 h1
      rw [h0, h1]
    | succ k ih =>
      intro p
      rw [hconst k p, ← hstep k (0, 0), ih]
  exact key

end C3
end MFGPlanning.Penalized
end part4

section part5
open Finset

namespace MFGPlanning.Penalized
namespace C3

attribute [local instance] neZeroNT

variable (d : Data)

/-- the primal objective `J(U) = Θ(Λ U) + 𝓕(U)` with `Θ` written through the real conjugate `φ`. -/
noncomputable def Jfun (φ : ℝ → ℝ) (U : Fin (d.NT + 1) → (Pt d) → ℝ) : ℝ :=
  ∑ k, ∑ p, φ ((Lam d U).1 k p + d.g p ((Lam d U).2 k p)) + F d U

/-- the L¹ size of `Λ U` -/
noncomputable def lamNorm (U : Fin (d.NT + 1) → (Pt d) → ℝ) : ℝ :=
  ∑ k, ∑ p, (|(Lam d U).1 k p| + ∑ l, |(Lam d U).2 k p l|)

lemma le_flat3 {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] (Y : ι → κ → μ → ℝ)
    (i : ι) (j : κ) (l : μ) : |Y i j l| ≤ ∑ x : ι × κ × μ, |Y x.1 x.2.1 x.2.2| :=
  single_le_sum (f := fun x : ι × κ × μ => |Y x.1 x.2.1 x.2.2|) (fun _ _ => abs_nonneg _)
    (mem_univ (i, j, l))

lemma le_flat2 {ι κ : Type*} [Fintype ι] [Fintype κ] (Y : ι → κ → ℝ) (i : ι) (j : κ) :
    |Y i j| ≤ ∑ x : ι × κ, |Y x.1 x.2| :=
  single_le_sum (f := fun x : ι × κ => |Y x.1 x.2|) (fun _ _ => abs_nonneg _) (mem_univ (i, j))

/-- the per-site lower bound behind coercivity. -/
lemma site_bound (φ W : ℝ → ℝ) (gq : (Fin 4 → ℝ) → ℝ) (hφ : ∀ a m, 0 ≤ m → a * m - W m ≤ φ a)
    (A1 B K ε δ SZ Mv a : ℝ) (Zv β : Fin 4 → ℝ)
    (hK : ∀ z : Fin 4 → ℝ, -B ≤ z 0 → z 0 ≤ -A1 → A1 ≤ z 1 → z 1 ≤ B → -B ≤ z 2 → z 2 ≤ -A1 →
      A1 ≤ z 3 → z 3 ≤ B → ∑ l, z l * β l - K ≤ gq β)
    (hδ : 0 < δ) (hA1 : 0 ≤ A1) (hε0 : 0 < ε) (hεδ : ε * (1 + A1) = δ / 2) (hMv : δ ≤ Mv)
    (hZ : Zv 0 + A1 * Mv ≤ -δ ∧ A1 * Mv - Zv 1 ≤ -δ ∧ Zv 2 + A1 * Mv ≤ -δ ∧ A1 * Mv - Zv 3 ≤ -δ)
    (hZs : ∀ l, |Zv l| ≤ SZ) (hB : B = (SZ + ε) / (δ / 2)) :
    Mv * a + ∑ l, Zv l * β l + ε * (|a| + ∑ l, |β l|)
      - ((|Mv + ε| + |Mv - ε|) * |K| + |W (Mv + ε)| + |W (Mv - ε)|) ≤ φ (a + gq β) := by
  set sM : ℝ := if 0 ≤ a then 1 else -1 with hsMdef
  set s : Fin 4 → ℝ := fun l => if 0 ≤ β l then 1 else -1 with hsdef
  have hsM : sM * a = |a| := by
    by_cases h : 0 ≤ a
    · simp [sM, h, abs_of_nonneg h]
    · simp [sM, h, abs_of_neg (not_le.mp h)]
  have hs : ∀ l, s l * β l = |β l| := by
    intro l
    by_cases h : 0 ≤ β l
    · simp [s, h, abs_of_nonneg h]
    · simp [s, h, abs_of_neg (not_le.mp h)]
  have hsMc : sM = 1 ∨ sM = -1 := by by_cases h : 0 ≤ a <;> simp [sM, h]
  have hsc : ∀ l, s l = 1 ∨ s l = -1 := by intro l; by_cases h : 0 ≤ β l <;> simp [s, h]
  have hεs : ∀ t : ℝ, (t = 1 ∨ t = -1) → -ε ≤ ε * t ∧ ε * t ≤ ε := by
    intro t ht; rcases ht with h | h <;> rw [h] <;> constructor <;> linarith
  set m' : ℝ := Mv + ε * sM with hm'def
  set z' : Fin 4 → ℝ := fun l => Zv l + ε * s l with hz'def
  have hεle : ε ≤ δ / 2 := by nlinarith
  have hm' : δ / 2 ≤ m' := by
    have := (hεs sM hsMc).1
    simp only [m']; linarith
  have hm'0 : 0 < m' := lt_of_lt_of_le (by positivity) hm'
  have hz : ∀ l, |z' l| ≤ SZ + ε := by
    intro l
    have h2 := hεs (s l) (hsc l)
    have h3 : |ε * s l| ≤ ε := abs_le.mpr ⟨h2.1, h2.2⟩
    exact (abs_add_le _ _).trans (by linarith [hZs l])
  set z : Fin 4 → ℝ := fun l => z' l / m' with hzdef
  have hzB : ∀ l, -B ≤ z l ∧ z l ≤ B := by
    intro l
    apply abs_le.mp
    simp only [z, abs_div, abs_of_pos hm'0, hB]
    calc |z' l| / m' ≤ (SZ + ε) / m' := div_le_div_of_nonneg_right (hz l) hm'0.le
      _ ≤ (SZ + ε) / (δ / 2) :=
        div_le_div_of_nonneg_left (le_trans (abs_nonneg _) (hz l)) (by positivity) hm'
  obtain ⟨hZ0, hZ1, hZ2, hZ3⟩ := hZ
  have hAε : A1 * ε + ε = δ / 2 := by linarith [hεδ]
  have hAm1 : A1 * m' ≤ A1 * Mv + A1 * ε := by
    have := mul_le_mul_of_nonneg_left (hεs sM hsMc).2 hA1
    simp only [m', mul_add]; linarith
  have hAm2 : A1 * Mv - A1 * ε ≤ A1 * m' := by
    have := mul_le_mul_of_nonneg_left (hεs sM hsMc).1 hA1
    simp only [m', mul_add]; linarith
  have c0 : z 0 ≤ -A1 := by
    simp only [z]; rw [div_le_iff₀ hm'0]
    have := (hεs (s 0) (hsc 0)).2
    simp only [z']; linarith
  have c1 : A1 ≤ z 1 := by
    simp only [z]; rw [le_div_iff₀ hm'0]
    have := (hεs (s 1) (hsc 1)).1
    simp only [z']; linarith
  have c2 : z 2 ≤ -A1 := by
    simp only [z]; rw [div_le_iff₀ hm'0]
    have := (hεs (s 2) (hsc 2)).2
    simp only [z']; linarith
  have c3 : A1 ≤ z 3 := by
    simp only [z]; rw [le_div_iff₀ hm'0]
    have := (hεs (s 3) (hsc 3)).1
    simp only [z']; linarith
  have hg := hK z (hzB 0).1 c0 c1 (hzB 1).2 (hzB 2).1 c2 c3 (hzB 3).2
  have hg' : ∑ l, z' l * β l - m' * K ≤ m' * gq β := by
    have := mul_le_mul_of_nonneg_left hg hm'0.le
    have e : m' * (∑ l, z l * β l - K) = ∑ l, z' l * β l - m' * K := by
      rw [mul_sub, mul_sum]
      congr 1
      refine sum_congr rfl fun l _ => ?_
      simp only [z]; field_simp
    linarith
  have hφ' := hφ (a + gq β) m' hm'0.le
  have hmK : m' * K ≤ (|Mv + ε| + |Mv - ε|) * |K| := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rcases hsMc with h | h
    · simp only [m', h, mul_one]; linarith [abs_nonneg (Mv - ε)]
    · have e : Mv + ε * sM = Mv - ε := by rw [h]; ring
      simp only [m', e]; linarith [abs_nonneg (Mv + ε)]
  have hW : W m' ≤ |W (Mv + ε)| + |W (Mv - ε)| := by
    rcases hsMc with h | h
    · simp only [m', h, mul_one]
      linarith [le_abs_self (W (Mv + ε)), abs_nonneg (W (Mv - ε))]
    · have e : Mv + ε * sM = Mv - ε := by rw [h]; ring
      simp only [m', e]
      linarith [le_abs_self (W (Mv - ε)), abs_nonneg (W (Mv + ε))]
  have hz'β : ∑ l, z' l * β l = ∑ l, Zv l * β l + ε * ∑ l, |β l| := by
    simp only [z', add_mul, sum_add_distrib, mul_sum]
    congr 1
    refine sum_congr rfl fun l _ => ?_
    rw [mul_assoc, hs l]
  have hm'α : m' * a = Mv * a + ε * |a| := by
    simp only [m']; rw [← hsM]; ring
  have e2 : (a + gq β) * m' = m' * a + m' * gq β := by ring
  rw [e2, hm'α] at hφ'
  rw [hz'β] at hg'
  have e3 : ε * (|a| + ∑ l, |β l|) = ε * |a| + ε * ∑ l, |β l| := by ring
  rw [e3]
  linarith

/-- Coercivity of `J` from a strictly feasible dual point. -/
theorem coercive (φ : ℝ → ℝ) (hφ : ∀ a m, 0 ≤ m → a * m - d.W m ≤ φ a)
    (A1 : ℝ) (hA1 : 0 ≤ A1)
    (hbox : ∀ B : ℝ, ∃ K : ℝ, ∀ (p : (Pt d)) (q z : Fin 4 → ℝ),
      -B ≤ z 0 → z 0 ≤ -A1 → A1 ≤ z 1 → z 1 ≤ B → -B ≤ z 2 → z 2 ≤ -A1 → A1 ≤ z 3 →
      z 3 ≤ B → ∑ l, z l * q l - K ≤ d.g p q)
    (Mb : Fin d.NT → (Pt d) → ℝ) (Zb : Fin d.NT → (Pt d) → Fin 4 → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hMb : ∀ k p, δ ≤ Mb k p)
    (hZb : ∀ k p, Zb k p 0 + A1 * Mb k p ≤ -δ ∧ A1 * Mb k p - Zb k p 1 ≤ -δ ∧
      Zb k p 2 + A1 * Mb k p ≤ -δ ∧ A1 * Mb k p - Zb k p 3 ≤ -δ)
    (hpair : ∀ V : Fin (d.NT + 1) → (Pt d) → ℝ, pair d Mb Zb (Lam d V).1 (Lam d V).2 + F d V = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ U, ε * lamNorm d U - C ≤ Jfun d φ U := by
  set ε : ℝ := δ / (2 * (1 + A1)) with hε
  have hε0 : 0 < ε := by positivity
  have hεδ : ε * (1 + A1) = δ / 2 := by rw [hε]; field_simp
  set SZ : ℝ := ∑ x : Fin d.NT × (Pt d) × Fin 4, |Zb x.1 x.2.1 x.2.2|
  set B : ℝ := (SZ + ε) / (δ / 2) with hB
  obtain ⟨K, hK⟩ := hbox B
  refine ⟨ε, hε0, ?_⟩
  set Ck : Fin d.NT → (Pt d) → ℝ := fun k p =>
    (|Mb k p + ε| + |Mb k p - ε|) * |K| + |d.W (Mb k p + ε)| + |d.W (Mb k p - ε)| with hCk
  refine ⟨∑ k, ∑ p, Ck k p, fun U => ?_⟩
  have site : ∀ k p, Mb k p * (Lam d U).1 k p + ∑ l, Zb k p l * (Lam d U).2 k p l
      + ε * (|(Lam d U).1 k p| + ∑ l, |(Lam d U).2 k p l|) - Ck k p
        ≤ φ ((Lam d U).1 k p + d.g p ((Lam d U).2 k p)) := fun k p =>
    site_bound φ d.W (d.g p) hφ A1 B K ε δ SZ (Mb k p) ((Lam d U).1 k p) (Zb k p)
      ((Lam d U).2 k p) (fun z => hK p _ z) hδ hA1 hε0 hεδ (hMb k p) (hZb k p)
      (fun l => le_flat3 Zb k p l) hB
  have hsum := sum_le_sum (fun k (_ : k ∈ univ) => sum_le_sum (fun p (_ : p ∈ univ) => site k p))
  have hp := hpair U
  have e : ∑ k, ∑ p, (Mb k p * (Lam d U).1 k p + ∑ l, Zb k p l * (Lam d U).2 k p l
      + ε * (|(Lam d U).1 k p| + ∑ l, |(Lam d U).2 k p l|) - Ck k p) =
      pair d Mb Zb (Lam d U).1 (Lam d U).2 + ε * lamNorm d U - ∑ k, ∑ p, Ck k p := by
    unfold pair lamNorm
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  unfold Jfun
  rw [e] at hsum
  linarith

end C3
end MFGPlanning.Penalized
end part5

section part6
open Finset

namespace MFGPlanning.Penalized
namespace C3

attribute [local instance] neZeroNT

variable (d : Data)

lemma divh_add_const (Y : (Pt d) → Fin 4 → ℝ) (c : Fin 4 → ℝ) (p : (Pt d)) :
    divh d (fun q l => Y q l + c l) p = divh d Y p := by
  unfold divh; ring

lemma snoc_interp (Mb : Fin d.NT → (Pt d) → ℝ) (t : ℕ → ℝ)
    (hMb : ∀ k : Fin d.NT, ∀ p, Mb k p = (1 - t k) * d.m0 p + t k * d.mT p)
    (ht : t d.NT = 1) (k : Fin d.NT) (p : (Pt d)) :
    Fin.snoc (α := fun _ => (Pt d) → ℝ) Mb d.mT k.succ p
      = (1 - t ((k : ℕ) + 1)) * d.m0 p + t ((k : ℕ) + 1) * d.mT p := by
  by_cases h : (k : ℕ) + 1 < d.NT
  · have e : k.succ = Fin.castSucc (⟨(k : ℕ) + 1, h⟩ : Fin d.NT) := Fin.ext (by simp)
    rw [e, Fin.snoc_castSucc, hMb]
  · have hk : (k : ℕ) + 1 = d.NT := by have := k.isLt; omega
    have e : k.succ = Fin.last d.NT := Fin.ext (by simp [hk])
    rw [e, Fin.snoc_last, hk, ht]
    ring

/-- A strictly feasible point of the planning constraint, deep inside the domain of `Θ^*`. -/
theorem feasible (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (A1 : ℝ) (hA1 : 0 ≤ A1)
    (hsurj : ∀ f : (Pt d) → ℝ, ∑ p, f p = 0 → ∃ Z : (Pt d) → Fin 4 → ℝ, ∀ p, divh d Z p = f p)
    (hlap0 : ∀ U : (Pt d) → ℝ, ∑ p, lap d U p = 0) :
    ∃ (Mb : Fin d.NT → (Pt d) → ℝ) (Zb : Fin d.NT → (Pt d) → Fin 4 → ℝ) (δ : ℝ), 0 < δ ∧
      PlanningConstraint d Mb Zb ∧ (∀ k p, δ ≤ Mb k p) ∧
      (∀ k p, Zb k p 0 + A1 * Mb k p ≤ -δ ∧ A1 * Mb k p - Zb k p 1 ≤ -δ ∧
        Zb k p 2 + A1 * Mb k p ≤ -δ ∧ A1 * Mb k p - Zb k p 3 ≤ -δ) := by
  have hNT : (0 : ℝ) < d.NT := Nat.cast_pos.2 d.hNT
  have hdt : d.Δt ≠ 0 := by unfold Data.Δt; exact div_ne_zero d.hT.ne' hNT.ne'
  have hh : d.h ≠ 0 := by
    unfold Data.h; exact inv_ne_zero (Nat.cast_ne_zero.2 (NeZero.ne d.Nh))
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, ∀ k, t k = (k : ℝ) / d.NT := ⟨_, fun _ => rfl⟩
  have ht1 : t d.NT = 1 := by rw [ht]; exact div_self hNT.ne'
  obtain ⟨Mb, hMb⟩ : ∃ Mb : Fin d.NT → (Pt d) → ℝ, ∀ k : Fin d.NT, ∀ p,
      Mb k p = (1 - t k) * d.m0 p + t k * d.mT p := ⟨_, fun _ _ => rfl⟩
  -- mass balance
  have hmass : ∑ p, d.mT p = ∑ p, d.m0 p := by
    have h1 := hm0.1; have h2 := hmT.1
    have : d.h ^ 2 ≠ 0 := pow_ne_zero 2 hh
    exact mul_left_cancel₀ this (h2.trans h1.symm)
  obtain ⟨f, hf⟩ : ∃ f : Fin d.NT → (Pt d) → ℝ, ∀ k p,
      f k p = (d.m0 p - d.mT p) * (1 / (d.NT * d.Δt)) - d.ν * lap d (Mb k) p :=
    ⟨_, fun _ _ => rfl⟩
  have hf0 : ∀ k, ∑ p, f k p = 0 := by
    intro k
    rw [sum_congr rfl fun p _ => hf k p, sum_sub_distrib, ← sum_mul, ← mul_sum, hlap0,
      sum_sub_distrib, hmass]
    ring
  choose Y hY using fun k => hsurj (f k) (hf0 k)
  -- lower bound for Mb
  obtain ⟨p0, -, hp0⟩ := exists_min_image univ d.m0 univ_nonempty
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = d.m0 p0 / d.NT := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (hm0pos p0) hNT
  have hMbδ : ∀ k p, δ ≤ Mb k p := by
    intro k p
    have hk : (k : ℝ) + 1 ≤ d.NT := by exact_mod_cast k.isLt
    have h1 : 1 / (d.NT : ℝ) ≤ 1 - t k := by
      rw [ht, div_le_iff₀ hNT, sub_mul, div_mul_cancel₀ _ hNT.ne']; linarith
    have h2 : 0 ≤ t k := by rw [ht]; positivity
    have h3 : d.m0 p0 ≤ d.m0 p := hp0 p (mem_univ p)
    have h4 : 0 ≤ d.mT p := hmT.2 p
    have h5 : δ ≤ 1 / (d.NT : ℝ) * d.m0 p := by
      rw [hδ, one_div_mul_eq_div]; exact div_le_div_of_nonneg_right h3 hNT.le
    have h6 : 1 / (d.NT : ℝ) * d.m0 p ≤ (1 - t k) * d.m0 p :=
      mul_le_mul_of_nonneg_right h1 (hm0pos p).le
    have h7 := mul_nonneg h2 h4
    rw [hMb]; linarith
  obtain ⟨SY, hSYd⟩ : ∃ SY : ℝ, SY = ∑ x : Fin d.NT × (Pt d) × Fin 4, |Y x.1 x.2.1 x.2.2| :=
    ⟨_, rfl⟩
  obtain ⟨SM, hSMd⟩ : ∃ SM : ℝ, SM = ∑ x : Fin d.NT × (Pt d), |Mb x.1 x.2| := ⟨_, rfl⟩
  have hSY : ∀ k p l, |Y k p l| ≤ SY := fun k p l => hSYd ▸
    single_le_sum (f := fun x : Fin d.NT × (Pt d) × Fin 4 => |Y x.1 x.2.1 x.2.2|)
      (fun _ _ => abs_nonneg _) (mem_univ (k, p, l))
  have hSM : ∀ k p, |Mb k p| ≤ SM := fun k p => hSMd ▸
    single_le_sum (f := fun x : Fin d.NT × (Pt d) => |Mb x.1 x.2|)
      (fun _ _ => abs_nonneg _) (mem_univ (k, p))
  obtain ⟨C0, hC0⟩ : ∃ C0 : ℝ, C0 = SY + A1 * SM + δ := ⟨_, rfl⟩
  refine ⟨Mb, fun k q l => Y k q l + (![-C0, C0, -C0, C0] : Fin 4 → ℝ) l, δ, hδ0,
    ⟨fun n p => ?_, ?_⟩, hMbδ, fun k p => ?_⟩
  · rw [snoc_interp d Mb t hMb ht1 n p, hMb, divh_add_const, hY, hf, ht, ht]
    push_cast
    field_simp
    ring
  · funext p
    rw [hMb]
    simp [ht]
  · have hAM : A1 * Mb k p ≤ A1 * SM :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hSM k p)) hA1
    have y0 := (abs_le.mp ((hSY k p 0))); have y1 := (abs_le.mp ((hSY k p 1)))
    have y2 := (abs_le.mp ((hSY k p 2))); have y3 := (abs_le.mp ((hSY k p 3)))
    have hc0 : (![-C0, C0, -C0, C0] : Fin 4 → ℝ) 0 = -C0 := rfl
    have hc1 : (![-C0, C0, -C0, C0] : Fin 4 → ℝ) 1 = C0 := rfl
    have hc2 : (![-C0, C0, -C0, C0] : Fin 4 → ℝ) 2 = -C0 := rfl
    have hc3 : (![-C0, C0, -C0, C0] : Fin 4 → ℝ) 3 = C0 := rfl
    simp only [hc0, hc1, hc2, hc3]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end C3
end MFGPlanning.Penalized
end part6

section part7
open Finset Filter Topology

namespace MFGPlanning.Penalized
namespace C3

attribute [local instance] neZeroNT

variable (d : Data)


lemma Dh_add (U V : (Pt d) → ℝ) (p : (Pt d)) : Dh d (U + V) p = Dh d U p + Dh d V p := by
  funext l; fin_cases l <;> simp [Dh, D1, D2] <;> ring

lemma Dh_smul (c : ℝ) (U : (Pt d) → ℝ) (p : (Pt d)) : Dh d (c • U) p = c • Dh d U p := by
  funext l; fin_cases l <;> simp [Dh, D1, D2] <;> ring

lemma lam_add (U V : Fin (d.NT + 1) → (Pt d) → ℝ) : Lam d (U + V) = Lam d U + Lam d V := by
  refine Prod.ext ?_ ?_
  · funext k p; simp only [Lam, Prod.fst_add, Pi.add_apply, lap]; ring
  · funext k p; simp only [Lam, Prod.snd_add, Pi.add_apply]; exact Dh_add d _ _ p

lemma lam_smul (c : ℝ) (U : Fin (d.NT + 1) → (Pt d) → ℝ) : Lam d (c • U) = c • Lam d U := by
  refine Prod.ext ?_ ?_
  · funext k p; simp only [Lam, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, lap]; ring
  · funext k p; simp only [Lam, Prod.smul_snd, Pi.smul_apply]; exact Dh_smul d c _ p

lemma F_add (U V : Fin (d.NT + 1) → (Pt d) → ℝ) : F d (U + V) = F d U + F d V := by
  unfold F; simp only [Pi.add_apply, mul_add, sum_add_distrib]; ring

lemma F_smul (c : ℝ) (U : Fin (d.NT + 1) → (Pt d) → ℝ) : F d (c • U) = c * F d U := by
  unfold F
  have e1 : ∑ p, d.m0 p * (c • U) 0 p = c * ∑ p, d.m0 p * U 0 p := by
    rw [mul_sum]; refine sum_congr rfl fun p _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  have e2 : ∑ p, d.mT p * (c • U) (Fin.last d.NT) p = c * ∑ p, d.mT p * U (Fin.last d.NT) p := by
    rw [mul_sum]; refine sum_congr rfl fun p _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e1, e2]; ring

/-- `U ↦ (Λ U, ∑ U⁰)` -/
noncomputable def Tmap : (Fin (d.NT + 1) → (Pt d) → ℝ) →ₗ[ℝ]
    ((Fin d.NT → (Pt d) → ℝ) × (Fin d.NT → (Pt d) → Fin 4 → ℝ)) × ℝ where
  toFun U := (Lam d U, ∑ p, U 0 p)
  map_add' U V := by
    simp only [lam_add, Pi.add_apply, sum_add_distrib, Prod.mk_add_mk]
  map_smul' c U := by
    simp only [lam_smul, Pi.smul_apply, smul_eq_mul, ← mul_sum, RingHom.id_apply, Prod.smul_mk]

lemma lamNorm_ge (U : Fin (d.NT + 1) → (Pt d) → ℝ) (k : Fin d.NT) (p : (Pt d)) :
    |(Lam d U).1 k p| + ∑ l, |(Lam d U).2 k p l| ≤ lamNorm d U := by
  unfold lamNorm
  have hnn : ∀ k' p', 0 ≤ |(Lam d U).1 k' p'| + ∑ l, |(Lam d U).2 k' p' l| :=
    fun _ _ => add_nonneg (abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)
  exact (single_le_sum (f := fun p' => |(Lam d U).1 k p'| + ∑ l, |(Lam d U).2 k p' l|)
    (fun _ _ => hnn _ _) (mem_univ p)).trans
    (single_le_sum (f := fun k' => ∑ p', (|(Lam d U).1 k' p'| + ∑ l, |(Lam d U).2 k' p' l|))
      (fun _ _ => sum_nonneg fun _ _ => hnn _ _) (mem_univ k))

lemma Tmap_norm (U : Fin (d.NT + 1) → (Pt d) → ℝ) :
    ‖Tmap d U‖ ≤ lamNorm d U + |∑ p, U 0 p| := by
  have h0 : 0 ≤ lamNorm d U :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
      add_nonneg (abs_nonneg _) (sum_nonneg fun _ _ => abs_nonneg _)
  have hL1 : ‖(Lam d U).1‖ ≤ lamNorm d U := by
    refine (pi_norm_le_iff_of_nonneg h0).2 fun k => (pi_norm_le_iff_of_nonneg h0).2 fun p => ?_
    rw [Real.norm_eq_abs]
    have := lamNorm_ge d U k p
    have : 0 ≤ ∑ l, |(Lam d U).2 k p l| := sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hL2 : ‖(Lam d U).2‖ ≤ lamNorm d U := by
    refine (pi_norm_le_iff_of_nonneg h0).2 fun k => (pi_norm_le_iff_of_nonneg h0).2 fun p =>
      (pi_norm_le_iff_of_nonneg h0).2 fun l => ?_
    rw [Real.norm_eq_abs]
    have := lamNorm_ge d U k p
    have := single_le_sum (f := fun l => |(Lam d U).2 k p l|) (fun _ _ => abs_nonneg _)
      (mem_univ l)
    have := abs_nonneg ((Lam d U).1 k p)
    linarith
  change ‖((Lam d U), ∑ p, U 0 p)‖ ≤ _
  rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs]
  have := abs_nonneg (∑ p, U 0 p)
  refine max_le (max_le ?_ ?_) ?_ <;> linarith

/-- Existence of a stationary point of the penalized primal problem
`J_e(U) = Θ(Λ U) + 𝓕(U) + (e/(2Δt)) ∑ (U⁰)²`. -/
theorem stationaryE (φ φ' : ℝ → ℝ) (hφd : ∀ a, HasDerivAt φ (φ' a) a) (hG3 : G3 d)
    (e : ℝ) (he : 0 < e)
    (hcoer : ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∀ U, ε * lamNorm d U - C ≤ Jfun d φ U)
    (hker : ∀ V : Fin (d.NT + 1) → (Pt d) → ℝ, Lam d V = (0, 0) → ∀ j p, V j p = V 0 (0, 0))
    (hexp : ∀ (L : (Fin 4 → ℝ) →L[ℝ] ℝ) (q : Fin 4 → ℝ), L q = ∑ l, q l * L (Pi.single l 1)) :
    ∃ U : Fin (d.NT + 1) → (Pt d) → ℝ, ∀ V : Fin (d.NT + 1) → (Pt d) → ℝ,
      pair d (fun k p => φ' ((Lam d U).1 k p + d.g p ((Lam d U).2 k p)))
        (fun k p l => φ' ((Lam d U).1 k p + d.g p ((Lam d U).2 k p)) *
          dg d p ((Lam d U).2 k p) l) (Lam d V).1 (Lam d V).2 + F d V
        + e / d.Δt * ∑ p, U 0 p * V 0 p = 0 := by
  obtain ⟨ε, hε, C, hC⟩ := hcoer
  have hdt : 0 < d.Δt := by unfold Data.Δt; exact div_pos d.hT (Nat.cast_pos.2 d.hNT)
  set J' : (Fin (d.NT + 1) → (Pt d) → ℝ) → ℝ :=
    fun U => Jfun d φ U + e / (2 * d.Δt) * ∑ p, U 0 p ^ 2 with hJ'
  have hcardpos : (0 : ℝ) < Fintype.card (Pt d) := by
    have : 0 < Fintype.card (Pt d) := Fintype.card_pos
    exact_mod_cast this
  have hcard : (Fintype.card (Pt d) : ℝ) ≠ 0 := hcardpos.ne'
  -- injectivity of `Tmap`
  have hinj : LinearMap.ker (Tmap d) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun U hU => ?_
    have h1 : Lam d U = (0, 0) := congrArg Prod.fst hU
    have h2 : ∑ p, U 0 p = 0 := congrArg Prod.snd hU
    have hc := hker U h1
    have h3 : ∑ p, U 0 p = Fintype.card (Pt d) * U 0 (0, 0) := by
      rw [sum_congr rfl fun p _ => hc 0 p, sum_const, card_univ, nsmul_eq_mul]
    have h4 : U 0 (0, 0) = 0 := by
      rw [h2] at h3
      exact (mul_eq_zero.mp h3.symm).resolve_left hcard
    funext j p
    rw [hc j p, h4]; rfl
  obtain ⟨K, hK0, hK⟩ := (Tmap d).exists_antilipschitzWith hinj
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hnorm : ∀ U, ‖U‖ ≤ K * (lamNorm d U + |∑ p, U 0 p|) := by
    intro U
    have h := hK.le_mul_dist U 0
    rw [dist_zero_right, map_zero, dist_zero_right] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Tmap_norm d U) hKpos.le)
  -- coercivity of `J'`
  set κ : ℝ := e / (2 * d.Δt * Fintype.card (Pt d)) with hκ
  have hκpos : 0 < κ := by positivity
  have hsq : ∀ U : Fin (d.NT + 1) → (Pt d) → ℝ,
      κ * (∑ p, U 0 p) ^ 2 ≤ e / (2 * d.Δt) * ∑ p, U 0 p ^ 2 := by
    intro U
    have cs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Pt d))) (f := fun p => U 0 p)
    rw [card_univ] at cs
    have e1 : κ * (∑ p, U 0 p) ^ 2 * Fintype.card (Pt d) = e / (2 * d.Δt) * (∑ p, U 0 p) ^ 2 := by
      rw [hκ]; field_simp
    have h2 : e / (2 * d.Δt) * (∑ p, U 0 p) ^ 2 ≤
        e / (2 * d.Δt) * (Fintype.card (Pt d) * ∑ p, U 0 p ^ 2) :=
      mul_le_mul_of_nonneg_left cs (by positivity)
    have h3 : κ * (∑ p, U 0 p) ^ 2 * Fintype.card (Pt d) ≤
        (e / (2 * d.Δt) * ∑ p, U 0 p ^ 2) * Fintype.card (Pt d) := by
      rw [e1]; linarith
    exact le_of_mul_le_mul_right h3 hcardpos
  have hcoer' : ∀ U, ε / K * ‖U‖ - (C + ε ^ 2 / (4 * κ)) ≤ J' U := by
    intro U
    have h1 := hnorm U
    have h2 := hC U
    have h3 : ε / K * ‖U‖ ≤ ε * (lamNorm d U + |∑ p, U 0 p|) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hKpos]
      nlinarith
    have h4 : 0 ≤ κ * (|∑ p, U 0 p| - ε / (2 * κ)) ^ 2 := by positivity
    have h5 : |∑ p, U 0 p| ^ 2 = (∑ p, U 0 p) ^ 2 := sq_abs _
    have h6 := hsq U
    have h7 : κ * (|∑ p, U 0 p| - ε / (2 * κ)) ^ 2
        = κ * |∑ p, U 0 p| ^ 2 - ε * |∑ p, U 0 p| + ε ^ 2 / (4 * κ) := by
      field_simp; ring
    simp only [hJ']
    nlinarith
  -- continuity
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun a => (hφd a).continuousAt
  have hgc : ∀ p, Continuous (d.g p) := fun p => (hG3 p).continuous
  have hLc : Continuous (Lam d) := by
    have : Continuous (Tmap d) := LinearMap.continuous_of_finiteDimensional _
    exact continuous_fst.comp this
  have h1c : ∀ k p, Continuous fun U : Fin (d.NT + 1) → (Pt d) → ℝ => (Lam d U).1 k p :=
    fun k p => (continuous_apply p).comp ((continuous_apply k).comp (continuous_fst.comp hLc))
  have h2c : ∀ k p, Continuous fun U : Fin (d.NT + 1) → (Pt d) → ℝ => (Lam d U).2 k p :=
    fun k p => (continuous_apply p).comp ((continuous_apply k).comp (continuous_snd.comp hLc))
  have hFc : Continuous fun U : Fin (d.NT + 1) → (Pt d) → ℝ => F d U := by
    unfold F; fun_prop
  have hJc : Continuous J' := by
    simp only [hJ', Jfun]
    refine ((continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun p _ =>
      hφc.comp ((h1c k p).add ((hgc p).comp (h2c k p)))).add hFc).add ?_
    fun_prop
  have htend : Tendsto J' (cocompact _) atTop := by
    refine tendsto_atTop_mono hcoer' ?_
    have := (tendsto_norm_cocompact_atTop (E := Fin (d.NT + 1) → (Pt d) → ℝ)).const_mul_atTop
      (div_pos hε hKpos)
    exact tendsto_atTop_add_const_right _ _ this
  obtain ⟨U, hU⟩ := hJc.exists_forall_le htend
  -- the first variation
  set a : Fin d.NT → (Pt d) → ℝ := fun k p => (Lam d U).1 k p + d.g p ((Lam d U).2 k p) with ha
  have deriv0 : ∀ V : Fin (d.NT + 1) → (Pt d) → ℝ,
      ∑ k, ∑ p, φ' (a k p) * ((Lam d V).1 k p
          + ∑ l, (Lam d V).2 k p l * dg d p ((Lam d U).2 k p) l)
        + F d V + e / (2 * d.Δt) * ∑ p, 2 * U 0 p * V 0 p = 0 := by
    intro V
    have hline : (fun t : ℝ => J' (U + t • V)) = fun t =>
        ∑ k, ∑ p, φ (((Lam d U).1 k p + t * (Lam d V).1 k p)
          + d.g p ((Lam d U).2 k p + t • (Lam d V).2 k p))
        + (F d U + t * F d V) + e / (2 * d.Δt) * ∑ p, (U 0 p + t * V 0 p) ^ 2 := by
      funext t
      simp only [hJ', Jfun, lam_add, lam_smul, F_add, F_smul, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib,
        ← mul_sum]
    have hsite : ∀ k p, HasDerivAt (fun t : ℝ => φ (((Lam d U).1 k p + t * (Lam d V).1 k p)
          + d.g p ((Lam d U).2 k p + t • (Lam d V).2 k p)))
        (φ' (a k p) * ((Lam d V).1 k p
          + ∑ l, (Lam d V).2 k p l * dg d p ((Lam d U).2 k p) l)) 0 := by
      intro k p
      set β := (Lam d U).2 k p
      set βV := (Lam d V).2 k p
      have hβl : HasDerivAt (fun t : ℝ => β + t • βV) βV 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const βV).const_add β
      have hg : HasFDerivAt (d.g p) (fderiv ℝ (d.g p) β) (β + (0 : ℝ) • βV) := by
        simpa using ((hG3 p).differentiable (by norm_num) β).hasFDerivAt
      have hgc := hg.comp_hasDerivAt (0 : ℝ) hβl
      have hαl : HasDerivAt (fun t : ℝ => (Lam d U).1 k p + t * (Lam d V).1 k p)
          ((Lam d V).1 k p) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((Lam d V).1 k p)).const_add
          ((Lam d U).1 k p)
      have hin := hαl.add hgc
      have e' : ((Lam d U).1 k p + (0 : ℝ) * (Lam d V).1 k p)
          + (d.g p ∘ fun t : ℝ => β + t • βV) 0 = a k p := by
        simp [ha, β]
      have hc := (hφd (((Lam d U).1 k p + (0 : ℝ) * (Lam d V).1 k p)
          + (d.g p ∘ fun t : ℝ => β + t • βV) 0)).comp (0 : ℝ) hin
      rw [e', hexp (fderiv ℝ (d.g p) β) βV] at hc
      exact hc
    have hsum : HasDerivAt (fun t : ℝ => ∑ k, ∑ p, φ (((Lam d U).1 k p + t * (Lam d V).1 k p)
          + d.g p ((Lam d U).2 k p + t • (Lam d V).2 k p)))
        (∑ k, ∑ p, φ' (a k p) * ((Lam d V).1 k p
          + ∑ l, (Lam d V).2 k p l * dg d p ((Lam d U).2 k p) l)) 0 :=
      HasDerivAt.fun_sum fun k _ => HasDerivAt.fun_sum fun p _ => hsite k p
    have hF : HasDerivAt (fun t : ℝ => F d U + t * F d V) (F d V) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (F d V)).const_add (F d U)
    have hsq1 : ∀ p, HasDerivAt (fun t : ℝ => (U 0 p + t * V 0 p) ^ 2) (2 * U 0 p * V 0 p) 0 := by
      intro p
      have h1 : HasDerivAt (fun t : ℝ => U 0 p + t * V 0 p) (V 0 p) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (V 0 p)).const_add (U 0 p)
      have h2 := h1.mul h1
      have e1 : (fun t : ℝ => (U 0 p + t * V 0 p) ^ 2) =
          fun t => (U 0 p + t * V 0 p) * (U 0 p + t * V 0 p) := by
        funext t; ring
      rw [e1]
      exact h2.congr_deriv (by simp only [zero_mul, add_zero]; ring)
    have hsq2 : HasDerivAt (fun t : ℝ => e / (2 * d.Δt) * ∑ p, (U 0 p + t * V 0 p) ^ 2)
        (e / (2 * d.Δt) * ∑ p, 2 * U 0 p * V 0 p) 0 :=
      (HasDerivAt.fun_sum fun p _ => hsq1 p).const_mul _
    have hall : HasDerivAt (fun t : ℝ => J' (U + t • V))
        (∑ k, ∑ p, φ' (a k p) * ((Lam d V).1 k p
          + ∑ l, (Lam d V).2 k p l * dg d p ((Lam d U).2 k p) l) + F d V
          + e / (2 * d.Δt) * ∑ p, 2 * U 0 p * V 0 p) 0 := by
      rw [hline]; exact (hsum.add hF).add hsq2
    have hmin : IsLocalMin (fun t : ℝ => J' (U + t • V)) 0 :=
      Eventually.of_forall fun t => by simpa using hU (U + t • V)
    exact hmin.hasDerivAt_eq_zero hall
  refine ⟨U, fun V => ?_⟩
  have h := deriv0 V
  have hq : e / (2 * d.Δt) * ∑ p, 2 * U 0 p * V 0 p = e / d.Δt * ∑ p, U 0 p * V 0 p := by
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    field_simp
  rw [hq] at h
  rw [← h]
  congr 2
  unfold pair
  refine sum_congr rfl fun k _ => sum_congr rfl fun p _ => ?_
  simp only [ha, mul_add, mul_sum]
  congr 1
  all_goals first | exact sum_congr rfl fun l _ => by ring | ring1

end C3
end MFGPlanning.Penalized
end part7

section part8
open Finset

namespace MFGPlanning.Penalized
namespace C3

attribute [local instance] neZeroNT

variable (d : Data)

lemma dg_sign (hG1 : G1 d) (hG3 : G3 d) (p : (Pt d)) (q : Fin 4 → ℝ) :
    dg d p q 0 ≤ 0 ∧ 0 ≤ dg d p q 1 ∧ dg d p q 2 ≤ 0 ∧ 0 ≤ dg d p q 3 := by
  have hd : ∀ l : Fin 4, HasDerivAt (fun t : ℝ => d.g p (q + t • (Pi.single l 1 : Fin 4 → ℝ)))
      (dg d p q l) 0 := by
    intro l
    have h1 : HasDerivAt (fun t : ℝ => q + t • (Pi.single l 1 : Fin 4 → ℝ))
        (Pi.single l 1 : Fin 4 → ℝ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l 1 : Fin 4 → ℝ)).const_add q
    have h2 : HasFDerivAt (d.g p) (fderiv ℝ (d.g p) q)
        (q + (0 : ℝ) • (Pi.single l 1 : Fin 4 → ℝ)) := by
      simpa using ((hG3 p).differentiable (by norm_num) q).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have ev : ∀ (l j : Fin 4) (t : ℝ),
      (q + t • (Pi.single l 1 : Fin 4 → ℝ)) j = q j + if j = l then t else 0 := by
    intro l j t; by_cases h : j = l <;> simp [Pi.single_apply, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← (hd 0).deriv]
    apply Antitone.deriv_nonpos
    intro t s hts
    apply hG1 <;> simp [ev] <;> linarith
  · rw [← (hd 1).deriv]
    apply Monotone.deriv_nonneg
    intro t s hts
    apply hG1 <;> simp [ev] <;> linarith
  · rw [← (hd 2).deriv]
    apply Antitone.deriv_nonpos
    intro t s hts
    apply hG1 <;> simp [ev] <;> linarith
  · rw [← (hd 3).deriv]
    apply Monotone.deriv_nonneg
    intro t s hts
    apply hG1 <;> simp [ev] <;> linarith

lemma B_eq_divh (U M : (Pt d) → ℝ) (p : (Pt d)) :
    B d U M p = divh d (fun q l => M q * dg d q (Dh d U q) l) p := by
  unfold B divh; dsimp only; ring

lemma h_pos : 0 < d.h := by
  unfold Data.h; exact inv_pos.2 (Nat.cast_pos.2 d.hNh)

lemma dt_pos : 0 < d.Δt := by
  unfold Data.Δt; exact div_pos d.hT (Nat.cast_pos.2 d.hNT)

/-- a zero of the density at time `n` propagates forward (and, with viscosity, to the
neighbours). -/
lemma zero_step (hG1 : G1 d) (hG3 : G3 d) (Mt : Fin (d.NT + 1) → (Pt d) → ℝ)
    (U : Fin (d.NT + 1) → (Pt d) → ℝ) (hnn : ∀ j p, 0 ≤ Mt j p)
    (hFP : ∀ (n : Fin d.NT) (p : (Pt d)), (Mt n.succ p - Mt n.castSucc p) / d.Δt
      + d.ν * lap d (Mt n.castSucc) p + B d (U n.succ) (Mt n.castSucc) p = 0)
    (n : Fin d.NT) (p : (Pt d)) (h0 : Mt n.castSucc p = 0) :
    Mt n.succ p = 0 ∧ (0 < d.ν → Mt n.castSucc (p.1 + 1, p.2) = 0 ∧
      Mt n.castSucc (p.1, p.2 + 1) = 0) := by
  have hh := h_pos d
  have hdt := dt_pos d
  set m := Mt n.castSucc with hm
  have e := hFP n p
  rw [← hm] at e
  have hlap : lap d m p = (1 / d.h ^ 2) * (m (p.1 + 1, p.2) + m (p.1 - 1, p.2)
      + m (p.1, p.2 + 1) + m (p.1, p.2 - 1)) := by
    unfold lap; rw [h0]; ring
  have s1 := dg_sign d hG1 hG3 (p.1 - 1, p.2) (Dh d (U n.succ) (p.1 - 1, p.2))
  have s2 := dg_sign d hG1 hG3 (p.1 + 1, p.2) (Dh d (U n.succ) (p.1 + 1, p.2))
  have s3 := dg_sign d hG1 hG3 (p.1, p.2 - 1) (Dh d (U n.succ) (p.1, p.2 - 1))
  have s4 := dg_sign d hG1 hG3 (p.1, p.2 + 1) (Dh d (U n.succ) (p.1, p.2 + 1))
  have f1 := mul_nonpos_of_nonneg_of_nonpos (hnn n.castSucc (p.1 - 1, p.2)) s1.1
  have f2 := mul_nonneg (hnn n.castSucc (p.1 + 1, p.2)) s2.2.1
  have f3 := mul_nonpos_of_nonneg_of_nonpos (hnn n.castSucc (p.1, p.2 - 1)) s3.2.2.1
  have f4 := mul_nonneg (hnn n.castSucc (p.1, p.2 + 1)) s4.2.2.2
  have hB : 0 ≤ B d (U n.succ) m p := by
    unfold B
    dsimp only
    rw [h0]
    apply mul_nonneg (by positivity)
    simp only [zero_mul, zero_sub, sub_zero]
    linarith
  have hL : 0 ≤ lap d m p := by
    rw [hlap]
    have := hnn n.castSucc (p.1 + 1, p.2); have := hnn n.castSucc (p.1 - 1, p.2)
    have := hnn n.castSucc (p.1, p.2 + 1); have := hnn n.castSucc (p.1, p.2 - 1)
    apply mul_nonneg (by positivity)
    linarith
  have hT : 0 ≤ (Mt n.succ p - m p) / d.Δt := by
    rw [h0, sub_zero]; exact div_nonneg (hnn _ _) hdt.le
  have hνL : 0 ≤ d.ν * lap d m p := mul_nonneg d.hν hL
  have z1 : (Mt n.succ p - m p) / d.Δt = 0 := by linarith
  have z2 : d.ν * lap d m p = 0 := by linarith
  refine ⟨?_, fun hν => ?_⟩
  · rw [h0, sub_zero, div_eq_zero_iff] at z1
    exact z1.resolve_right hdt.ne'
  · have hl0 : lap d m p = 0 := (mul_eq_zero.mp z2).resolve_left hν.ne'
    rw [hlap] at hl0
    have hs : m (p.1 + 1, p.2) + m (p.1 - 1, p.2) + m (p.1, p.2 + 1) + m (p.1, p.2 - 1) = 0 :=
      (mul_eq_zero.mp hl0).resolve_left (by positivity)
    have := hnn n.castSucc (p.1 + 1, p.2); have := hnn n.castSucc (p.1 - 1, p.2)
    have := hnn n.castSucc (p.1, p.2 + 1); have := hnn n.castSucc (p.1, p.2 - 1)
    constructor <;> linarith

/-- the densities are positive before the final time. -/
theorem positivity_of_FP (hG1 : G1 d) (hG3 : G3 d) (Mt : Fin (d.NT + 1) → (Pt d) → ℝ)
    (U : Fin (d.NT + 1) → (Pt d) → ℝ) (hnn : ∀ j p, 0 ≤ Mt j p)
    (hFP : ∀ (n : Fin d.NT) (p : (Pt d)), (Mt n.succ p - Mt n.castSucc p) / d.Δt
      + d.ν * lap d (Mt n.castSucc) p + B d (U n.succ) (Mt n.castSucc) p = 0)
    (hlast : Mt (Fin.last d.NT) = d.mT) (hmT : InK d d.mT)
    (hν : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p)) :
    ∀ (n : Fin d.NT) (p : (Pt d)), 0 < Mt n.castSucc p := by
  intro n p
  rcases (hnn n.castSucc p).lt_or_eq with h | h
  · exact h
  exfalso
  have step := zero_step d hG1 hG3 Mt U hnn hFP
  -- index helpers
  have cs : ∀ (j : ℕ) (hj : j < d.NT), (Fin.castSucc (⟨j, hj⟩ : Fin d.NT)) = ⟨j, by omega⟩ :=
    fun _ _ => rfl
  have sc : ∀ (j : ℕ) (hj : j < d.NT), (Fin.succ (⟨j, hj⟩ : Fin d.NT)) = ⟨j + 1, by omega⟩ :=
    fun _ _ => rfl
  rcases hν with hν | ⟨hν0, hmTp⟩
  · -- viscous case: the whole level vanishes, then all later levels
    have hall : ∀ q, Mt n.castSucc q = 0 := by
      have hz1 : ∀ q, Mt n.castSucc q = 0 → Mt n.castSucc (q.1 + 1, q.2) = 0 :=
        fun q hq => ((step n q hq).2 hν).1
      have hz2 : ∀ q, Mt n.castSucc q = 0 → Mt n.castSucc (q.1, q.2 + 1) = 0 :=
        fun q hq => ((step n q hq).2 hν).2
      have r1 : ∀ k : ℕ, Mt n.castSucc (p.1 + k, p.2) = 0 := by
        intro k; induction k with
        | zero => simpa using h.symm
        | succ k ih => have := hz1 _ ih; simpa [add_assoc] using this
      have r2 : ∀ (k j : ℕ), Mt n.castSucc (p.1 + k, p.2 + j) = 0 := by
        intro k j; induction j with
        | zero => simpa using r1 k
        | succ j ih => have := hz2 _ ih; simpa [add_assoc] using this
      intro q
      have := r2 (q.1 - p.1).val (q.2 - p.2).val
      simpa [ZMod.natCast_zmod_val] using this
    have prop : ∀ j : ℕ, (n : ℕ) ≤ j → ∀ (hj : j < d.NT + 1) q, Mt ⟨j, hj⟩ q = 0 := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro hj q; exact hall q
      | succ j hnj ih =>
        intro hj q
        have hjl : j < d.NT := by omega
        have := (step ⟨j, hjl⟩ q (by rw [cs]; exact ih (by omega) q)).1
        rwa [sc] at this
    have hT := prop d.NT (by omega) (by omega)
    have e : (⟨d.NT, by omega⟩ : Fin (d.NT + 1)) = Fin.last d.NT := rfl
    have hz : ∀ q, d.mT q = 0 := fun q => by rw [← hlast, ← e]; exact hT q
    have := hmT.1
    simp [hz] at this
  · -- inviscid case: the zero travels to the final time at the same point
    have prop : ∀ j : ℕ, (n : ℕ) ≤ j → ∀ (hj : j < d.NT + 1), Mt ⟨j, hj⟩ p = 0 := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => intro hj; exact h.symm
      | succ j hnj ih =>
        intro hj
        have hjl : j < d.NT := by omega
        have := (step ⟨j, hjl⟩ p (by rw [cs]; exact ih (by omega))).1
        rwa [sc] at this
    have hT := prop d.NT (by omega) (by omega)
    have e : (⟨d.NT, by omega⟩ : Fin (d.NT + 1)) = Fin.last d.NT := rfl
    rw [e, hlast] at hT
    exact absurd hT (hmTp p).ne'

/-- mass conservation along the scheme gives `M^n ∈ 𝒦` at every time (mass fixed by `m_T`). -/
theorem inK_allE (Mt : Fin (d.NT + 1) → (Pt d) → ℝ) (U : Fin (d.NT + 1) → (Pt d) → ℝ)
    (hnn : ∀ j p, 0 ≤ Mt j p)
    (hFP : ∀ (n : Fin d.NT) (p : (Pt d)), (Mt n.succ p - Mt n.castSucc p) / d.Δt
      + d.ν * lap d (Mt n.castSucc) p + B d (U n.succ) (Mt n.castSucc) p = 0)
    (hl : Mt (Fin.last d.NT) = d.mT) (hmT : InK d d.mT)
    (hsumlap : ∀ V : (Pt d) → ℝ, ∑ p, lap d V p = 0)
    (hsumdiv : ∀ Z : (Pt d) → Fin 4 → ℝ, ∑ p, divh d Z p = 0) :
    ∀ j, InK d (Mt j) := by
  have hdt := dt_pos d
  have hstep : ∀ n : Fin d.NT, ∑ p, Mt n.succ p = ∑ p, Mt n.castSucc p := by
    intro n
    have e := sum_congr rfl fun p (_ : p ∈ univ) => hFP n p
    rw [sum_const_zero, sum_add_distrib, sum_add_distrib, ← mul_sum, hsumlap, mul_zero,
      add_zero, sum_congr rfl fun p _ => B_eq_divh d _ _ p, hsumdiv, add_zero, ← sum_div,
      div_eq_zero_iff, sum_sub_distrib] at e
    rcases e with e | e
    · linarith
    · exact absurd e hdt.ne'
  have hall : ∀ j, ∑ p, Mt j p = ∑ p, Mt 0 p := by
    intro j
    induction j using Fin.induction with
    | zero => rfl
    | succ k ih => rw [hstep k]; exact ih
  intro j
  refine ⟨?_, hnn j⟩
  rw [hall j, ← hall (Fin.last d.NT), hl]; exact hmT.1

/-- the penalized constraint from the first variation, through summation by parts. -/
theorem constraint_of_idE (M : Fin d.NT → (Pt d) → ℝ) (Z : Fin d.NT → (Pt d) → Fin 4 → ℝ)
    (w : (Pt d) → ℝ)
    (hid : ∀ V : Fin (d.NT + 1) → (Pt d) → ℝ, pair d M Z (Lam d V).1 (Lam d V).2 + F d V
      + (1 / d.Δt) * ∑ p, V 0 p * w p = 0)
    (hsbp : ∀ V : Fin (d.NT + 1) → (Pt d) → ℝ, pair d M Z (Lam d V).1 (Lam d V).2 + F d V =
      -(∑ k, ∑ p, V k.succ p *
          (((Fin.snoc (α := fun _ => (Pt d) → ℝ) M d.mT k.succ p) - M k p) / d.Δt
            + d.ν * lap d (M k) p + divh d (Z k) p))
        + (1 / d.Δt) * ∑ p, V 0 p * (d.m0 p - M 0 p)) :
    (∀ (n : Fin d.NT) (p : Pt d),
      ((Fin.snoc (α := fun _ => Pt d → ℝ) M d.mT n.succ p) - M n p) / d.Δt
        + d.ν * lap d (M n) p + divh d (Z n) p = 0) ∧
    ∀ q, M 0 q = d.m0 q + w q := by
  have hdt := dt_pos d
  refine ⟨fun n q => ?_, fun q => ?_⟩
  · have h := hid fun j p => if j = n.succ ∧ p = q then 1 else 0
    rw [hsbp] at h
    have e1 : ∑ p, (fun j p => if j = n.succ ∧ p = q then (1 : ℝ) else 0) 0 p
        * (d.m0 p - M 0 p) = 0 := by
      refine sum_eq_zero fun p _ => ?_
      have : (0 : Fin (d.NT + 1)) ≠ n.succ := (Fin.succ_ne_zero n).symm
      simp [this]
    have e2 : ∑ p, (fun j p => if j = n.succ ∧ p = q then (1 : ℝ) else 0) 0 p * w p = 0 := by
      refine sum_eq_zero fun p _ => ?_
      have : (0 : Fin (d.NT + 1)) ≠ n.succ := (Fin.succ_ne_zero n).symm
      simp [this]
    simp only [e1, e2, mul_zero, add_zero] at h
    rw [sum_eq_single n, sum_eq_single q] at h
    · simp at h; linarith
    · intro b _ hb; simp [hb]
    · simp
    · intro b _ hb
      refine sum_eq_zero fun p _ => ?_
      have : b.succ ≠ n.succ := fun h' => hb (Fin.succ_injective _ h')
      simp [this]
    · simp
  · have h := hid fun j p => if j = 0 ∧ p = q then 1 else 0
    rw [hsbp] at h
    have e1 : ∑ k : Fin d.NT, ∑ p, (fun j p => if j = 0 ∧ p = q then (1 : ℝ) else 0) k.succ p *
        (((Fin.snoc (α := fun _ => (Pt d) → ℝ) M d.mT k.succ p) - M k p) / d.Δt
          + d.ν * lap d (M k) p + divh d (Z k) p) = 0 := by
      refine sum_eq_zero fun k _ => sum_eq_zero fun p _ => ?_
      simp [Fin.succ_ne_zero]
    rw [e1, neg_zero, zero_add, sum_eq_single q, sum_eq_single q] at h
    · simp at h
      have h2 : d.Δt⁻¹ * (d.m0 q - M 0 q + w q) = 0 := by rw [mul_add]; linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (inv_ne_zero hdt.ne')
      · linarith
    · intro b _ hb; simp [hb]
    · simp
    · intro b _ hb; simp [hb]
    · simp

end C3
end MFGPlanning.Penalized
end part8

open Finset

namespace MFGPlanning.Penalized
namespace C3

attribute [local instance] neZeroNT

variable (d : Data)

lemma ereal_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, EReal.coe_add, ih]

/-- tangent-plane bound at an arbitrary base point. -/
lemma tangent_le (f : (Fin 4 → ℝ) → ℝ) (hc : ConvexOn ℝ Set.univ f) (x : Fin 4 → ℝ)
    (hd : DifferentiableAt ℝ f x) (q : Fin 4 → ℝ) :
    f x + ∑ l, (q l - x l) * fderiv ℝ f x (Pi.single l 1) ≤ f q := by
  set φ : ℝ → ℝ := fun t => f (x + t • (q - x)) with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    have h1 := hc.translate_right x
    rw [Set.preimage_univ] at h1
    have h := h1.comp_linearMap (LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (q - x))
    rw [Set.preimage_univ] at h
    exact h
  have hφd : HasDerivAt φ (fderiv ℝ f x (q - x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • (q - x)) ((1 : ℝ) • (q - x)) 0 :=
      ((hasDerivAt_id 0).smul_const (q - x)).const_add x
    have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (q - x)) := by
      simpa using hd.hasFDerivAt
    have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
    rw [one_smul] at h3
    exact h3
  have := hφc.deriv_le_slope (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hφd.differentiableAt
  rw [hφd.deriv, slope_def_field] at this
  simp only [hφ, one_smul, zero_smul, add_zero, sub_zero, div_one, add_sub_cancel] at this
  rw [fderiv_expand] at this
  simp only [Pi.sub_apply] at this
  linarith

lemma pair_sub (M : Fin d.NT → (Pt d) → ℝ) (Z : Fin d.NT → (Pt d) → Fin 4 → ℝ)
    (α α' : Fin d.NT → (Pt d) → ℝ) (β β' : Fin d.NT → (Pt d) → Fin 4 → ℝ) :
    pair d M Z (α' - α) (β' - β) = pair d M Z α' β' - pair d M Z α β := by
  unfold pair
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]
  ring

theorem main (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (M : Fin (d.NT + 1) → Pt d → ℝ) (Z : Fin d.NT → Pt d → Fin 4 → ℝ),
      ((∀ (n : Fin d.NT) (p : Pt d),
          (M n.succ p - M n.castSucc p) / d.Δt + d.ν * lap d (M n.castSucc) p
            + divh d (Z n) p = 0) ∧ M (Fin.last d.NT) = d.mT) ∧
      (∀ (M' : Fin (d.NT + 1) → Pt d → ℝ) (Z' : Fin d.NT → Pt d → Fin 4 → ℝ),
        ((∀ (n : Fin d.NT) (p : Pt d),
            (M' n.succ p - M' n.castSucc p) / d.Δt + d.ν * lap d (M' n.castSucc) p
              + divh d (Z' n) p = 0) ∧ M' (Fin.last d.NT) = d.mT) →
        ΘStar d (Fin.init M) Z
            + (((1 / (2 * ε * d.Δt)) * ∑ p, (M 0 p - d.m0 p) ^ 2 : ℝ) : EReal)
          ≤ ΘStar d (Fin.init M') Z'
            + (((1 / (2 * ε * d.Δt)) * ∑ p, (M' 0 p - d.m0 p) ^ 2 : ℝ) : EReal)) ∧
      ∃ U : Fin (d.NT + 1) → Pt d → ℝ,
        (∀ (k : Fin d.NT) (p : Pt d) (l : Fin 4),
          Z k p l = M k.castSucc p * dg d p (Dh d (U k.succ) p) l) ∧
        IsPenalizedSol d ε U M := by
  classical
  obtain ⟨φ, φ', hconj, hφd, hφ'0, hVφ, hsub, hlow, -⟩ := C3phi.phi_props hW.1 hW.2.1 hW.2.2
  have hconjW : ∀ a, conjWchi d a = (φ a : EReal) := hconj
  obtain ⟨A1, hA1, hbox⟩ := gbox d hG3 hG4 hG5
  have hdt := dt_pos d
  have hsumlap : ∀ V : (Pt d) → ℝ, ∑ p, lap d V p = 0 := by
    intro V
    have h := sum_mul_lap d (fun _ => 1) V
    have h1 : ∀ p, lap d (fun _ => (1 : ℝ)) p = 0 := fun p => by unfold lap; ring
    simp only [one_mul, h1, mul_zero, Finset.sum_const_zero] at h
    exact h
  have hsumdiv : ∀ Z : (Pt d) → Fin 4 → ℝ, ∑ p, divh d Z p = 0 := by
    intro Z
    have h := sum_Z_Dh d Z (fun _ => 1)
    have h1 : ∀ p l, Dh d (fun _ => (1 : ℝ)) p l = 0 := by
      intro p l; fin_cases l <;> simp [Dh, D1, D2]
    simp only [h1, mul_zero, Finset.sum_const_zero, one_mul] at h
    linarith
  obtain ⟨Mb, Zb, δ, hδ, hPC, hMb, hZb⟩ :=
    feasible d hm0 hmT hm0pos A1 hA1 (divh_surj d) hsumlap
  have hpairMb : ∀ V : Fin (d.NT + 1) → (Pt d) → ℝ,
      pair d Mb Zb (Lam d V).1 (Lam d V).2 + F d V = 0 := by
    intro V
    rw [pair_lam_F]
    have h1 : ∀ k p, ((Fin.snoc (α := fun _ => (Pt d) → ℝ) Mb d.mT k.succ p) - Mb k p) / d.Δt
        + d.ν * lap d (Mb k) p + divh d (Zb k) p = 0 := hPC.1
    simp only [h1, mul_zero, Finset.sum_const_zero, neg_zero, hPC.2, sub_self, zero_add]
  have hcoer := coercive d φ hlow A1 hA1 hbox Mb Zb δ hδ hMb hZb hpairMb
  obtain ⟨U, hstat⟩ := stationaryE d φ φ' hφd hG3 ε hε hcoer (lam_ker d) fderiv_expand
  set α := (Lam d U).1 with hα
  set β := (Lam d U).2 with hβ
  set M : Fin d.NT → (Pt d) → ℝ := fun k p => φ' (α k p + d.g p (β k p)) with hM
  set Z : Fin d.NT → (Pt d) → Fin 4 → ℝ := fun k p l => M k p * dg d p (β k p) l with hZ
  have hid : ∀ V : Fin (d.NT + 1) → (Pt d) → ℝ, pair d M Z (Lam d V).1 (Lam d V).2 + F d V
      + (1 / d.Δt) * ∑ p, V 0 p * (ε * U 0 p) = 0 := by
    intro V
    rw [← hstat V]
    congr 1
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    field_simp
  obtain ⟨hFPc, hM0⟩ := constraint_of_idE d M Z (fun p => ε * U 0 p) hid (pair_lam_F d M Z)
  set S : ℝ := ∑ k, ∑ p, φ (α k p + d.g p (β k p)) with hS
  have hTheta : ∀ α' β', Θ d α' β' = ((∑ k, ∑ p, φ (α' k p + d.g p (β' k p)) : ℝ) : EReal) := by
    intro α' β'
    unfold Θ
    rw [ereal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ereal_sum]
    exact Finset.sum_congr rfl fun p _ => hconjW _
  -- subgradient inequality for Θ
  have hΘsub : ∀ α' β', S + (pair d M Z α' β' - pair d M Z α β) ≤
      ∑ k, ∑ p, φ (α' k p + d.g p (β' k p)) := by
    intro α' β'
    rw [← pair_sub, hS]
    unfold pair
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    have ht := tangent_le (d.g p) (hG4 p) (β k p)
      ((hG3 p).differentiable (by norm_num) (β k p)) (β' k p)
    have hs := hsub (α k p + d.g p (β k p)) (α' k p + d.g p (β' k p))
    have h0 := hφ'0 (α k p + d.g p (β k p))
    have e : ∑ l, Z k p l * (β' k p l - β k p l) =
        φ' (α k p + d.g p (β k p)) * ∑ l, (β' k p l - β k p l) * dg d p (β k p) l := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hZ, hM]; ring
    have hdg : ∑ l, (β' k p l - β k p l) * dg d p (β k p) l ≤
        d.g p (β' k p) - d.g p (β k p) := by
      unfold dg; linarith
    simp only [Pi.sub_apply]
    rw [e]
    simp only [hM]
    nlinarith [mul_le_mul_of_nonneg_left hdg h0]
  have hThS : ΘStar d M Z = ((pair d M Z α β - S : ℝ) : EReal) := by
    apply le_antisymm
    · unfold ΘStar
      refine iSup₂_le fun α' β' => ?_
      rw [hTheta, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have := hΘsub α' β'
      linarith
    · unfold ΘStar
      refine le_iSup₂_of_le α β ?_
      rw [hTheta, ← EReal.coe_sub]
  -- the penalized system
  set Mt : Fin (d.NT + 1) → (Pt d) → ℝ := Fin.snoc (α := fun _ => (Pt d) → ℝ) M d.mT with hMt
  have hMtc : ∀ n : Fin d.NT, Mt n.castSucc = M n := fun n => by simp [hMt]
  have hMtl : Mt (Fin.last d.NT) = d.mT := by simp [hMt]
  have hMt0 : Mt 0 = M 0 := by rw [← hMtc 0]; simp
  have hinit : Fin.init Mt = M := by simp [hMt]
  have hnn : ∀ j p, 0 ≤ Mt j p := by
    intro j p
    induction j using Fin.lastCases with
    | last => rw [hMtl]; exact hmT.2 p
    | cast n => rw [hMtc]; exact hφ'0 _
  have hFPdiv : ∀ (n : Fin d.NT) (p : (Pt d)), (Mt n.succ p - Mt n.castSucc p) / d.Δt
      + d.ν * lap d (Mt n.castSucc) p + divh d (Z n) p = 0 := by
    intro n p
    rw [hMtc]
    exact hFPc n p
  have hFP : ∀ (n : Fin d.NT) (p : (Pt d)), (Mt n.succ p - Mt n.castSucc p) / d.Δt
      + d.ν * lap d (Mt n.castSucc) p + B d (U n.succ) (Mt n.castSucc) p = 0 := by
    intro n p
    rw [hMtc, B_eq_divh]
    exact hFPc n p
  have hpos := positivity_of_FP d hG1 hG3 Mt U hnn hFP hMtl hmT hνmT
  have hK := inK_allE d Mt U hnn hFP hMtl hmT hsumlap hsumdiv
  have hHJB : ∀ (n : Fin d.NT) (p : (Pt d)),
      (U n.succ p - U n.castSucc p) / d.Δt - d.ν * lap d (U n.succ) p + d.g p (Dh d (U n.succ) p)
        = d.V (Mt n.castSucc p) := by
    intro n p
    have hp := hpos n p
    rw [hMtc] at hp ⊢
    have := hVφ (α n p + d.g p (β n p)) hp
    show _ = deriv d.W (M n p)
    rw [show M n p = φ' (α n p + d.g p (β n p)) from rfl, this]
    rfl
  have hU0 : ∀ p, U 0 p = (Mt 0 p - d.m0 p) / ε := by
    intro p
    rw [hMt0, hM0 p]
    field_simp
    ring
  -- the value identity for the minimiser
  have hpU : pair d M Z α β + F d U = (1 / d.Δt) * ∑ p, U 0 p * (d.m0 p - M 0 p) := by
    rw [pair_lam_F d M Z U]
    have h0 : ∀ k p, U k.succ p *
        (((Fin.snoc (α := fun _ => (Pt d) → ℝ) M d.mT k.succ p) - M k p) / d.Δt
          + d.ν * lap d (M k) p + divh d (Z k) p) = 0 := fun k p => by rw [hFPc k p, mul_zero]
    simp only [h0, Finset.sum_const_zero, neg_zero, zero_add]
  refine ⟨Mt, Z, ⟨hFPdiv, hMtl⟩, fun M' Z' hM' => ?_, U, fun k p l => ?_, ?_⟩
  · -- minimality
    have hsn : Fin.snoc (α := fun _ => (Pt d) → ℝ) (Fin.init M') d.mT = M' := by
      rw [← hM'.2]; exact Fin.snoc_init_self M'
    have hpU' : pair d (Fin.init M') Z' α β + F d U
        = (1 / d.Δt) * ∑ p, U 0 p * (d.m0 p - M' 0 p) := by
      rw [pair_lam_F d (Fin.init M') Z' U, hsn]
      have h0 : ∀ k p, U k.succ p * ((M' k.succ p - Fin.init M' k p) / d.Δt
          + d.ν * lap d (Fin.init M' k) p + divh d (Z' k) p) = 0 := fun k p => by
        have := hM'.1 k p
        simp only [Fin.init] at this ⊢
        rw [this, mul_zero]
      simp only [h0, Finset.sum_const_zero, neg_zero, zero_add]
      congr 1
    have h1 : ((pair d (Fin.init M') Z' α β - S : ℝ) : EReal) ≤ ΘStar d (Fin.init M') Z' := by
      unfold ΘStar
      refine le_iSup₂_of_le α β ?_
      rw [hTheta, ← EReal.coe_sub]
    have hreal : pair d M Z α β - S + (1 / (2 * ε * d.Δt)) * ∑ p, (Mt 0 p - d.m0 p) ^ 2
        ≤ pair d (Fin.init M') Z' α β - S
          + (1 / (2 * ε * d.Δt)) * ∑ p, (M' 0 p - d.m0 p) ^ 2 := by
      have key : (1 / d.Δt) * ∑ p, U 0 p * (d.m0 p - M 0 p)
            + (1 / (2 * ε * d.Δt)) * ∑ p, (Mt 0 p - d.m0 p) ^ 2
          ≤ (1 / d.Δt) * ∑ p, U 0 p * (d.m0 p - M' 0 p)
            + (1 / (2 * ε * d.Δt)) * ∑ p, (M' 0 p - d.m0 p) ^ 2 := by
        rw [mul_sum, mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
        refine sum_le_sum fun p _ => ?_
        rw [hMt0, hM0 p]
        have hdiff : (1 / d.Δt) * (U 0 p * (d.m0 p - M' 0 p))
              + (1 / (2 * ε * d.Δt)) * (M' 0 p - d.m0 p) ^ 2
            - ((1 / d.Δt) * (U 0 p * (d.m0 p - (d.m0 p + ε * U 0 p)))
              + (1 / (2 * ε * d.Δt)) * (d.m0 p + ε * U 0 p - d.m0 p) ^ 2)
            = (1 / (2 * ε * d.Δt)) * (ε * U 0 p - (M' 0 p - d.m0 p)) ^ 2 := by
          field_simp; ring
        have : 0 ≤ (1 / (2 * ε * d.Δt)) * (ε * U 0 p - (M' 0 p - d.m0 p)) ^ 2 := by positivity
        linarith
      linarith
    rw [hinit, hThS, ← EReal.coe_add]
    calc ((pair d M Z α β - S + 1 / (2 * ε * d.Δt) * ∑ p, (Mt 0 p - d.m0 p) ^ 2 : ℝ) : EReal)
        ≤ ((pair d (Fin.init M') Z' α β - S
            + 1 / (2 * ε * d.Δt) * ∑ p, (M' 0 p - d.m0 p) ^ 2 : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.2 hreal
      _ = ((pair d (Fin.init M') Z' α β - S : ℝ) : EReal)
            + ((1 / (2 * ε * d.Δt) * ∑ p, (M' 0 p - d.m0 p) ^ 2 : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ ΘStar d (Fin.init M') Z'
            + ((1 / (2 * ε * d.Δt) * ∑ p, (M' 0 p - d.m0 p) ^ 2 : ℝ) : EReal) :=
          add_le_add h1 le_rfl
  · rw [hMtc]; rfl
  · exact ⟨hHJB, hFP, fun n => hK n.castSucc, hU0, hMtl⟩

end C3
end MFGPlanning.Penalized

open MFGPlanning.Penalized in
theorem solution (d : Data) (hG1 : G1 d) (hG3 : G3 d) (hG4 : G4 d) (hG5 : G5 d) (hW : HypW d)
    (hm0 : InK d d.m0) (hmT : InK d d.mT) (hm0pos : ∀ p, 0 < d.m0 p)
    (hνmT : 0 < d.ν ∨ (d.ν = 0 ∧ ∀ p, 0 < d.mT p))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (M : Fin (d.NT + 1) → Pt d → ℝ) (Z : Fin d.NT → Pt d → Fin 4 → ℝ),
      ((∀ (n : Fin d.NT) (p : Pt d),
          (M n.succ p - M n.castSucc p) / d.Δt + d.ν * lap d (M n.castSucc) p
            + divh d (Z n) p = 0) ∧ M (Fin.last d.NT) = d.mT) ∧
      (∀ (M' : Fin (d.NT + 1) → Pt d → ℝ) (Z' : Fin d.NT → Pt d → Fin 4 → ℝ),
        ((∀ (n : Fin d.NT) (p : Pt d),
            (M' n.succ p - M' n.castSucc p) / d.Δt + d.ν * lap d (M' n.castSucc) p
              + divh d (Z' n) p = 0) ∧ M' (Fin.last d.NT) = d.mT) →
        ΘStar d (Fin.init M) Z
            + (((1 / (2 * ε * d.Δt)) * ∑ p, (M 0 p - d.m0 p) ^ 2 : ℝ) : EReal)
          ≤ ΘStar d (Fin.init M') Z'
            + (((1 / (2 * ε * d.Δt)) * ∑ p, (M' 0 p - d.m0 p) ^ 2 : ℝ) : EReal)) ∧
      ∃ U : Fin (d.NT + 1) → Pt d → ℝ,
        (∀ (k : Fin d.NT) (p : Pt d) (l : Fin 4),
          Z k p l = M k.castSucc p * dg d p (Dh d (U k.succ) p) l) ∧
        IsPenalizedSol d ε U M := by
  exact C3.main d hG1 hG3 hG4 hG5 hW hm0 hmT hm0pos hνmT ε hε
