-- Prove2me | solution 1 for ModernConvex.SLemma.zero_set_projective_connected
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T01:26:31.810768+00:00
-- url     : https://prove2.me/submissions/94879397-97f8-42df-ba6d-e742fc6d8253

import Mathlib
import Definitions.Def_ModernConvex_SLemma_ProjectiveSpace

open Matrix

namespace ZS101

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

def qf (Q : Matrix (Fin n) (Fin n) ℝ) (u : E n) : ℝ :=
  WithLp.ofLp u ⬝ᵥ (Q *ᵥ WithLp.ofLp u)

def bf (Q : Matrix (Fin n) (Fin n) ℝ) (u w : E n) : ℝ :=
  WithLp.ofLp u ⬝ᵥ (Q *ᵥ WithLp.ofLp w) + WithLp.ofLp w ⬝ᵥ (Q *ᵥ WithLp.ofLp u)

lemma qf3 (Q : Matrix (Fin n) (Fin n) ℝ) (a c d : ℝ) (x y w : E n) :
    qf Q (a • x + c • y + d • w) = a ^ 2 * qf Q x + c ^ 2 * qf Q y + d ^ 2 * qf Q w
      + a * c * bf Q x y + a * d * bf Q x w + c * d * bf Q y w := by
  simp only [qf, bf, WithLp.ofLp_add, WithLp.ofLp_smul, mulVec_add, mulVec_smul, dotProduct_add,
    add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma bf_lin (Q : Matrix (Fin n) (Fin n) ℝ) (a c d : ℝ) (z x y w : E n) :
    bf Q z (a • x + c • y + d • w) = a * bf Q z x + c * bf Q z y + d * bf Q z w := by
  simp only [bf, WithLp.ofLp_add, WithLp.ofLp_smul, mulVec_add, mulVec_smul, dotProduct_add,
    add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma bf_self (Q : Matrix (Fin n) (Fin n) ℝ) (x : E n) : bf Q x x = 2 * qf Q x := by
  simp only [bf, qf]; ring

lemma bf_comm (Q : Matrix (Fin n) (Fin n) ℝ) (x y : E n) : bf Q x y = bf Q y x := by
  simp only [bf]; ring

lemma qf_smul (Q : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (x : E n) : qf Q (a • x) = a ^ 2 * qf Q x := by
  simp only [qf, WithLp.ofLp_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring

lemma bf_smul (Q : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (x y : E n) : bf Q x (a • y) = a * bf Q x y := by
  simpa using bf_lin Q a 0 0 x y y y

lemma qf_neg (Q : Matrix (Fin n) (Fin n) ℝ) (x : E n) : qf Q (-x) = qf Q x := by
  simpa using qf_smul Q (-1) x

lemma bf_neg (Q : Matrix (Fin n) (Fin n) ℝ) (x y : E n) : bf Q x (-y) = - bf Q x y := by
  simpa using bf_smul Q (-1) x y

open ModernConvex.SLemma

abbrev Sph (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

def Yset (Q : Matrix (Fin n) (Fin n) ℝ) : Set (Sph n) := {x | qf Q (x : E n) = 0}

lemma proj_neg (x : Sph n) : canonicalProjection n (-x) = canonicalProjection n x := by
  unfold canonicalProjection
  exact Quotient.sound (Or.inr rfl)

/-- A continuous nonvanishing curve inside the cone `qf = 0` yields a preconnected subset. -/
lemma path_link (Q : Matrix (Fin n) (Fin n) ℝ) (v : ℝ → E n) (hc : Continuous v)
    (hv : ∀ θ ∈ Set.Icc (0:ℝ) 1, v θ ≠ 0) (hq : ∀ θ ∈ Set.Icc (0:ℝ) 1, qf Q (v θ) = 0)
    (x y : Sph n) (h0 : v 0 = x) (h1 : v 1 = y) :
    ∃ T ⊆ canonicalProjection n '' Yset Q, IsPreconnected T ∧
      canonicalProjection n x ∈ T ∧ canonicalProjection n y ∈ T := by
  let g : Set.Icc (0:ℝ) 1 → Sph n := fun θ => ⟨‖v θ‖⁻¹ • v θ, by
    have := hv θ θ.2
    simp [norm_smul, this]⟩
  have hg : Continuous g := by
    apply Continuous.subtype_mk
    have hcv : Continuous fun θ : Set.Icc (0:ℝ) 1 => v θ := hc.comp continuous_subtype_val
    exact (hcv.norm.inv₀ fun θ => norm_ne_zero_iff.mpr (hv θ θ.2)).smul hcv
  have hunit : ∀ (θ : Set.Icc (0:ℝ) 1) (z : Sph n), v θ = z → g θ = z := by
    intro θ z hz
    apply Subtype.ext
    simp only [g, hz]
    have : ‖(z : E n)‖ = 1 := by simp
    rw [this]; simp
  have : PreconnectedSpace (Set.Icc (0:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  refine ⟨Set.range (canonicalProjection n ∘ g), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨θ, rfl⟩
    refine ⟨g θ, ?_, rfl⟩
    show qf Q (‖v θ‖⁻¹ • v θ) = 0
    rw [qf_smul, hq θ θ.2, mul_zero]
  · exact isPreconnected_range ((continuous_quot_mk).comp hg)
  · exact ⟨⟨0, by simp⟩, by show canonicalProjection n (g _) = _; rw [hunit _ x h0]⟩
  · exact ⟨⟨1, by simp⟩, by show canonicalProjection n (g _) = _; rw [hunit _ y h1]⟩

lemma link0 (Q : Matrix (Fin n) (Fin n) ℝ) (x y : Sph n) (hx : x ∈ Yset Q) (hy : y ∈ Yset Q)
    (hb : bf Q x y = 0) :
    ∃ T ⊆ canonicalProjection n '' Yset Q, IsPreconnected T ∧
      canonicalProjection n x ∈ T ∧ canonicalProjection n y ∈ T := by
  by_cases hxy : x = -y
  · refine ⟨{canonicalProjection n x}, Set.singleton_subset_iff.mpr ⟨x, hx, rfl⟩, isPreconnected_singleton,
      rfl, ?_⟩
    rw [hxy, proj_neg]; rfl
  · apply path_link Q (fun θ => (1 - θ) • (x : E n) + θ • (y : E n) + (0:ℝ) • (y : E n))
    · fun_prop
    · intro θ _ h0
      apply hxy
      simp only [zero_smul, add_zero] at h0
      have h1 : (1 - θ) • (x : E n) = -(θ • (y : E n)) := eq_neg_of_add_eq_zero_left h0
      have hn := congrArg norm h1
      have hx1 : ‖(x : E n)‖ = 1 := by simp
      have hy1 : ‖(y : E n)‖ = 1 := by simp
      rw [norm_neg, norm_smul, norm_smul, hx1, hy1] at hn
      simp only [Real.norm_eq_abs, mul_one] at hn
      rcases ‹θ ∈ Set.Icc (0:ℝ) 1› with ⟨ht0, ht1⟩
      rw [abs_of_nonneg (by linarith), abs_of_nonneg ht0] at hn
      have hθ : θ = 1 / 2 := by linarith
      subst hθ
      apply Subtype.ext
      have : (1 - 1/2 : ℝ) • (x : E n) = (1/2 : ℝ) • (-(y : E n)) := by rw [h1, smul_neg]
      have h2 : (x : E n) = -(y : E n) := by
        have := congrArg (fun z => (2:ℝ) • z) this
        simp only [smul_smul] at this
        norm_num at this
        exact this
      simpa using h2
    · intro θ _
      rw [qf3]
      simp only [Yset, Set.mem_ofPred_eq] at hx hy
      rw [hx, hy, hb]; ring
    · simp
    · simp


lemma bf_zero (Q : Matrix (Fin n) (Fin n) ℝ) (x : E n) : bf Q x 0 = 0 := by
  simp [bf]

lemma link_c (Q : Matrix (Fin n) (Fin n) ℝ) (x y : Sph n) (hx : x ∈ Yset Q) (hy : y ∈ Yset Q)
    (w : E n) (hxw : bf Q x w = 0) (hyw : bf Q y w = 0) (hbc : bf Q x y * qf Q w < 0) :
    ∃ T ⊆ canonicalProjection n '' Yset Q, IsPreconnected T ∧
      canonicalProjection n x ∈ T ∧ canonicalProjection n y ∈ T := by
  simp only [Yset, Set.mem_ofPred_eq] at hx hy
  set b := bf Q x y with hbdef
  set c := qf Q w with hcdef
  have hb : b ≠ 0 := by rintro h; rw [h, zero_mul] at hbc; exact lt_irrefl _ hbc
  have hc : c ≠ 0 := by rintro h; rw [h, mul_zero] at hbc; exact lt_irrefl _ hbc
  have hk : 0 ≤ -b / c := by
    have : -b / c = -(b * c) / c ^ 2 := by field_simp
    rw [this]; exact div_nonneg (by linarith) (sq_nonneg _)
  apply path_link Q (fun θ => (1 - θ) • (x : E n) + θ • (y : E n)
      + Real.sqrt (θ * (1 - θ) * (-b / c)) • w)
  · fun_prop
  · intro θ hθ h0
    have e1 := congrArg (bf Q x) h0
    have e2 := congrArg (bf Q y) h0
    rw [bf_lin, bf_zero, bf_self, hx, hxw] at e1
    rw [bf_lin, bf_zero, bf_self, hy, hyw, bf_comm Q y x] at e2
    have h1 : θ * b = 0 := by linarith
    have h2 : (1 - θ) * b = 0 := by linarith
    rcases mul_eq_zero.mp h1 with h | h
    · rw [h] at h2; simp at h2; exact hb h2
    · exact hb h
  · intro θ hθ
    rcases hθ with ⟨h0, h1⟩
    rw [qf3, hx, hy, hxw, hyw, ← hbdef, ← hcdef, Real.sq_sqrt (mul_nonneg (mul_nonneg h0 (by linarith)) hk)]
    field_simp
    ring
  · simp
  · simp

lemma exists_w (hn : 3 ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ) (x y : E n) :
    ∃ w : E n, w ≠ 0 ∧ bf Q x w = 0 ∧ bf Q y w = 0 := by
  let fL : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) := fun z =>
    { toFun := fun w => bf Q z w
      map_add' := fun u w => by simpa using bf_lin Q 1 1 0 z u w w
      map_smul' := fun a u => by simpa using bf_smul Q a z u }
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.pi ![fL x, fL y]
  have hlt : Module.finrank ℝ (Fin 2 → ℝ) < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simp; omega
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt hlt)
  refine ⟨w, hw0, ?_, ?_⟩
  · have := congrFun ((LinearMap.mem_ker (f := L)).mp hw) 0
    simpa [L, fL] using this
  · have := congrFun ((LinearMap.mem_ker (f := L)).mp hw) 1
    simpa [L, fL] using this

lemma link (hn : 3 ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ) (x y : Sph n) (hx : x ∈ Yset Q)
    (hy : y ∈ Yset Q) :
    ∃ T ⊆ canonicalProjection n '' Yset Q, IsPreconnected T ∧
      canonicalProjection n x ∈ T ∧ canonicalProjection n y ∈ T := by
  by_cases hb : bf Q x y = 0
  · exact link0 Q x y hx hy hb
  obtain ⟨w, hw0, hxw, hyw⟩ := exists_w hn Q x y
  have hny : -y ∈ Yset Q := by
    simp only [Yset, Set.mem_ofPred_eq] at hy ⊢
    rw [show ((-y : Sph n) : E n) = -(y : E n) from rfl, qf_neg, hy]
  rcases lt_trichotomy (bf Q x y * qf Q w) 0 with h | h | h
  · exact link_c Q x y hx hy w hxw hyw h
  · -- qf w = 0 : go through w
    have hc : qf Q w = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hb
      · exact h
    let w1 : Sph n := ⟨‖w‖⁻¹ • w, by simp [norm_smul, hw0]⟩
    have hw1 : w1 ∈ Yset Q := by
      show qf Q (‖w‖⁻¹ • w) = 0
      rw [qf_smul, hc, mul_zero]
    obtain ⟨T1, hT1, hp1, hx1, hw11⟩ := link0 Q x w1 hx hw1 (by
      show bf Q x (‖w‖⁻¹ • w) = 0
      rw [bf_smul, hxw, mul_zero])
    obtain ⟨T2, hT2, hp2, hw12, hy2⟩ := link0 Q w1 y hw1 hy (by
      rw [bf_comm]
      show bf Q y (‖w‖⁻¹ • w) = 0
      rw [bf_smul, hyw, mul_zero])
    exact ⟨T1 ∪ T2, Set.union_subset hT1 hT2, hp1.union _ hw11 hw12 hp2,
      Or.inl hx1, Or.inr hy2⟩
  · obtain ⟨T, hT, hp, hxT, hyT⟩ := link_c Q x (-y) hx hny w hxw (by
      rw [bf_comm, show ((-y : Sph n) : E n) = -(y : E n) from rfl, bf_neg, bf_comm, hyw, neg_zero])
      (by rw [show ((-y : Sph n) : E n) = -(y : E n) from rfl, bf_neg]; linarith)
    exact ⟨T, hT, hp, hxT, by rwa [proj_neg] at hyT⟩

end ZS101

open ZS101 in
theorem solution {n : ℕ} (hn : 3 ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hY : {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      WithLp.ofLp (x : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
        (Q *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))) = 0}.Nonempty) :
    (∀ x ∈ {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        WithLp.ofLp (x : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
          (Q *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))) = 0},
      -x ∈ {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        WithLp.ofLp (x : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
          (Q *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))) = 0}) ∧
    IsConnected (ModernConvex.SLemma.canonicalProjection n ''
      {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      WithLp.ofLp (x : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
        (Q *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))) = 0}) := by
  have hYe : {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      WithLp.ofLp (x : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
        (Q *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))) = 0} = Yset Q := rfl
  rw [hYe] at hY ⊢
  refine ⟨fun x hx => ?_, ?_⟩
  · simp only [Yset, Set.mem_ofPred_eq] at hx ⊢
    rw [show ((-x : Sph n) : EuclideanSpace ℝ (Fin n)) = -(x : EuclideanSpace ℝ (Fin n)) from rfl,
      qf_neg, hx]
  obtain ⟨x0, hx0⟩ := hY
  refine ⟨⟨_, x0, hx0, rfl⟩, ?_⟩
  apply isPreconnected_of_forall (ModernConvex.SLemma.canonicalProjection n x0)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨T, hT, hp, h1, h2⟩ := link hn Q x0 y hx0 hy
  exact ⟨T, hT, h1, h2, hp⟩
