-- Prove2me | solution 1 for LeblSCV.Holomorphic.power_series_on_polydisc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T06:35:35.458985+00:00
-- url     : https://prove2.me/submissions/5394a012-8060-4880-82d2-50de6669a092

import Mathlib
import Definitions.Def_LeblSCV_Shared_polydisc
import Definitions.Def_LeblSCV_Holomorphic_IsHolomorphicOn
import Definitions.Def_LeblSCV_Holomorphic_powerSeriesTerm

set_option autoImplicit false

open Complex Set MeasureTheory Function Filter Topology Metric
open scoped Real

namespace PSP

open LeblSCV.Holomorphic LeblSCV.Shared

/-- closed polydisc -/
def cpd {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) : Set (Fin n → ℂ) :=
  Set.pi univ fun k => closedBall (a k) (r k)

lemma mem_cpd {n : ℕ} {a : Fin n → ℂ} {r : Fin n → ℝ} {w : Fin n → ℂ} :
    w ∈ cpd a r ↔ ∀ k, ‖w k - a k‖ ≤ r k := by
  simp [cpd, dist_eq_norm]

lemma mem_polydisc {n : ℕ} {a : Fin n → ℂ} {r : Fin n → ℝ} {w : Fin n → ℂ} :
    w ∈ polydisc a r ↔ ∀ k, ‖w k - a k‖ < r k := Iff.rfl

lemma isCompact_cpd {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) : IsCompact (cpd a r) :=
  isCompact_univ_pi fun _ => isCompact_closedBall _ _

lemma isOpen_polydisc {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) : IsOpen (polydisc a r) := by
  have : polydisc a r = Set.pi univ fun k => ball (a k) (r k) := by
    ext w; simp [polydisc, dist_eq_norm]
  rw [this]; exact isOpen_set_pi finite_univ fun k _ => isOpen_ball

lemma tend_mul (c : ℝ) : Tendsto (fun t : ℝ => t * c) (𝓝[<] 1) (𝓝 c) := by
  have h : Tendsto (fun t : ℝ => t * c) (𝓝 1) (𝓝 (1 * c)) :=
    (continuous_id.mul continuous_const).tendsto 1
  rw [one_mul] at h
  exact h.mono_left nhdsWithin_le_nhds

/-! ### Part 2 -/

lemma term_cont {n : ℕ} (c : (Fin n → ℕ) → ℂ) (a : Fin n → ℂ) (α : Fin n → ℕ) :
    Continuous (powerSeriesTerm c a α) := by
  unfold powerSeriesTerm; fun_prop

lemma term_diff {n : ℕ} (c : (Fin n → ℕ) → ℂ) (a : Fin n → ℂ) (α : Fin n → ℕ) :
    Differentiable ℂ (powerSeriesTerm c a α) := by
  unfold powerSeriesTerm; fun_prop

lemma unif_signed {n : ℕ} (c : (Fin n → ℕ) → ℂ) (a : Fin n → ℂ) (K : Set (Fin n → ℂ))
    (f : (Fin n → ℂ) → ℂ) (hc : ConvergesUniformlyAbsolutelyOn c a K)
    (hf : ∀ z ∈ K, HasSum (fun α => powerSeriesTerm c a α z) (f z)) :
    TendstoUniformlyOn (fun (s : Finset (Fin n → ℕ)) z => ∑ α ∈ s, powerSeriesTerm c a α z)
      f atTop K := by
  obtain ⟨S, hS⟩ := hc
  have hpt : ∀ z ∈ K, HasSum (fun α => ‖powerSeriesTerm c a α z‖) (S z) :=
    fun z hz => hS.tendsto_at hz
  rw [Metric.tendstoUniformlyOn_iff] at hS ⊢
  intro ε hε
  filter_upwards [hS ε hε] with s hs z hz
  have hsn : Summable (fun α => ‖powerSeriesTerm c a α z‖) := (hpt z hz).summable
  have hsm : Summable (fun α => powerSeriesTerm c a α z) := (hf z hz).summable
  have e1 := hsm.sum_add_tsum_compl (s := s)
  have e2 := hsn.sum_add_tsum_compl (s := s)
  rw [(hf z hz).tsum_eq] at e1
  rw [(hpt z hz).tsum_eq] at e2
  have key : ‖f z - ∑ α ∈ s, powerSeriesTerm c a α z‖ ≤
      S z - ∑ α ∈ s, ‖powerSeriesTerm c a α z‖ := by
    rw [← e1, ← e2, add_sub_cancel_left, add_sub_cancel_left]
    exact norm_tsum_le_tsum_norm (hsn.subtype _)
  have h2 := hs z hz
  rw [dist_eq_norm] at h2 ⊢
  calc _ ≤ _ := key
    _ ≤ ‖S z - ∑ α ∈ s, ‖powerSeriesTerm c a α z‖‖ := Real.le_norm_self _
    _ < ε := h2

theorem part2 {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (c : (Fin n → ℕ) → ℂ)
    (f : (Fin n → ℂ) → ℂ)
    (hc : ∀ K ⊆ polydisc a ρ, IsCompact K → ConvergesUniformlyAbsolutelyOn c a K)
    (hf : ∀ z ∈ polydisc a ρ, HasSum (fun α => powerSeriesTerm c a α z) (f z)) :
    IsHolomorphicOn f (polydisc a ρ) := by
  have hU := isOpen_polydisc a ρ
  have hball : ∀ p ∈ polydisc a ρ, ∃ δ > 0, closedBall p δ ⊆ polydisc a ρ := by
    intro p hp
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU p hp
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
  have hunif : ∀ p, ∀ δ > 0, closedBall p δ ⊆ polydisc a ρ →
      TendstoUniformlyOn (fun (s : Finset (Fin n → ℕ)) z => ∑ α ∈ s, powerSeriesTerm c a α z)
        f atTop (closedBall p δ) := fun p δ _ hsub =>
    unif_signed c a _ f (hc _ hsub (isCompact_closedBall p δ)) (fun z hz => hf z (hsub hz))
  refine ⟨fun p hp => ?_, fun z hz k => ?_⟩
  · obtain ⟨δ, hδ, hsub⟩ := hball p hp
    have hu := hunif p δ hδ hsub
    rw [Metric.tendstoUniformlyOn_iff] at hu
    obtain ⟨s, hs⟩ := (hu 1 one_pos).exists
    obtain ⟨B, hB⟩ := (isCompact_closedBall p δ).exists_bound_of_continuousOn
      (f := fun z => ∑ α ∈ s, powerSeriesTerm c a α z)
      (continuous_finsetSum _ fun α _ => term_cont c a α).continuousOn
    refine ⟨closedBall p δ, closedBall_mem_nhds p hδ, B + 1, fun w hw => ?_⟩
    have h1 := hs w hw.1
    have h2 := hB w hw.1
    rw [dist_eq_norm] at h1
    have h3 := norm_sub_norm_le (f w) (∑ α ∈ s, powerSeriesTerm c a α w)
    linarith
  · obtain ⟨δ, hδ, hsub⟩ := hball z hz
    have hu := hunif z δ hδ hsub
    let φ : ℂ → (Fin n → ℂ) := fun ξ => update z k (z k + ξ)
    have hφd : Differentiable ℂ φ := by
      rw [differentiable_pi]
      intro j
      by_cases hj : j = k
      · subst hj; simp only [φ, update_self]; fun_prop
      · simp only [φ, update_of_ne hj]; fun_prop
    have hmaps : ball (0:ℂ) δ ⊆ φ ⁻¹' closedBall z δ := by
      intro ξ hξ
      simp only [mem_preimage, mem_closedBall, dist_eq_norm]
      refine (pi_norm_le_iff_of_nonneg hδ.le).2 fun j => ?_
      by_cases hj : j = k
      · subst hj; simp only [φ, Pi.sub_apply, update_self, add_sub_cancel_left]
        exact (mem_ball_zero_iff.1 hξ).le
      · simp [φ, update_of_ne hj, hδ.le]
    have hu2 := (hu.comp φ).mono hmaps
    have hT : ∀ α, Differentiable ℂ (fun ξ => powerSeriesTerm c a α (φ ξ)) :=
      fun α => (term_diff c a α).comp hφd
    have hd : DifferentiableOn ℂ (f ∘ φ) (ball 0 δ) :=
      hu2.tendstoLocallyUniformlyOn.differentiableOn
        (Eventually.of_forall fun s => Differentiable.differentiableOn (by
          show Differentiable ℂ (fun ξ => ∑ α ∈ s, powerSeriesTerm c a α (φ ξ))
          fun_prop))
        isOpen_ball
    exact hd.differentiableAt (ball_mem_nhds 0 hδ)

/-! ### Products of summable families -/

def consE (n : ℕ) : ℕ × (Fin n → ℕ) ≃ (Fin (n + 1) → ℕ) where
  toFun p := Fin.cons p.1 p.2
  invFun α := (α 0, Fin.tail α)
  left_inv p := by simp
  right_inv α := by simp

lemma consE_apply (n : ℕ) (x : ℕ × (Fin n → ℕ)) : consE n x = Fin.cons x.1 x.2 := rfl

lemma mul_aux {B : Type} (f : ℕ → ℂ) (g : B → ℂ) (gn : B → ℝ) (A G : ℂ)
    (hf : HasSum f A) (hg : HasSum g G) (hfn : Summable fun m => ‖f m‖)
    (hgn : Summable gn) (hgle : ∀ b, ‖g b‖ = gn b) :
    HasSum (fun x : ℕ × B => f x.1 * g x.2) (A * G) ∧
      Summable (fun x : ℕ × B => ‖f x.1‖ * gn x.2) := by
  have hmul2 : Summable (fun x : ℕ × B => ‖f x.1‖ * gn x.2) :=
    Summable.mul_of_nonneg hfn hgn (fun _ => norm_nonneg _) (fun b => (hgle b) ▸ norm_nonneg _)
  refine ⟨?_, hmul2⟩
  have hsm : Summable (fun x : ℕ × B => f x.1 * g x.2) := by
    refine Summable.of_norm (hmul2.congr fun x => ?_)
    rw [norm_mul, hgle]
  exact HasSum.mul hf hg hsm

lemma prod_hasSum (n : ℕ) : ∀ (u : Fin n → ℕ → ℂ), (∀ k, Summable fun m => ‖u k m‖) →
    HasSum (fun α : Fin n → ℕ => ∏ k, u k (α k)) (∏ k, ∑' m, u k m) ∧
    Summable (fun α : Fin n → ℕ => ∏ k, ‖u k (α k)‖) := by
  induction n with
  | zero =>
    intro u _
    refine ⟨?_, Summable.of_finite⟩
    simpa using hasSum_fintype (fun α : Fin 0 → ℕ => ∏ k, u k (α k))
  | succ n ih =>
    intro u hu
    have h1 : HasSum (fun β : Fin n → ℕ => ∏ k, u k.succ (β k)) (∏ k : Fin n, ∑' m, u k.succ m) :=
      (ih (fun k => u k.succ) (fun k => hu k.succ)).1
    have h2 : Summable (fun β : Fin n → ℕ => ∏ k, ‖u k.succ (β k)‖) :=
      (ih (fun k => u k.succ) (fun k => hu k.succ)).2
    have hf : HasSum (fun m => u 0 m) (∑' m, u 0 m) := (Summable.of_norm (hu 0)).hasSum
    have h0 : Summable (fun m => ‖u 0 m‖) := hu 0
    have hgle : ∀ b : Fin n → ℕ, ‖∏ k, u k.succ (b k)‖ = ∏ k, ‖u k.succ (b k)‖ :=
      fun b => norm_prod _ _
    obtain ⟨hmul, hmul2⟩ := mul_aux _ _ _ _ _ hf h1 h0 h2 hgle
    have e1 : (fun α : Fin (n + 1) → ℕ => ∏ k, u k (α k)) ∘ consE n =
        fun x : ℕ × (Fin n → ℕ) => u 0 x.1 * ∏ k, u k.succ (x.2 k) := by
      funext x
      simp only [Function.comp_apply, consE_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have e2 : (fun α : Fin (n + 1) → ℕ => ∏ k, ‖u k (α k)‖) ∘ consE n =
        fun x : ℕ × (Fin n → ℕ) => ‖u 0 x.1‖ * ∏ k, ‖u k.succ (x.2 k)‖ := by
      funext x
      simp only [Function.comp_apply, consE_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    refine ⟨?_, ?_⟩
    · rw [Fin.prod_univ_succ, ← (consE n).hasSum_iff, e1]; exact hmul
    · rw [← (consE n).summable_iff, e2]; exact hmul2

lemma geom1 (s d : ℂ) (hd : d ≠ 0) (h : ‖s‖ < ‖d‖) :
    HasSum (fun m : ℕ => s ^ m * (d ^ (m + 1))⁻¹) (d - s)⁻¹ ∧
      Summable (fun m : ℕ => ‖s ^ m * (d ^ (m + 1))⁻¹‖) := by
  have hw : ‖s / d‖ < 1 := by rw [norm_div, div_lt_one (norm_pos_iff.2 hd)]; exact h
  have e : ∀ m : ℕ, s ^ m * (d ^ (m + 1))⁻¹ = d⁻¹ * (s / d) ^ m := by
    intro m; rw [div_pow, pow_succ, mul_inv, div_eq_mul_inv]; ring
  simp_rw [e]
  refine ⟨?_, ?_⟩
  · have := (hasSum_geometric_of_norm_lt_one hw).mul_left d⁻¹
    have h1 : d⁻¹ * (1 - s / d)⁻¹ = (d - s)⁻¹ := by
      rw [show (1 : ℂ) - s / d = (d - s) / d by rw [sub_div, div_self hd], inv_div,
        div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    rwa [h1] at this
  · simp_rw [norm_mul, norm_pow]
    exact (summable_geometric_of_lt_one (norm_nonneg _) hw).mul_left _

lemma summ_B {n : ℕ} (s ρ : Fin n → ℝ) (hs : ∀ k, 0 ≤ s k) (hsρ : ∀ k, s k < ρ k) :
    Summable (fun α : Fin n → ℕ => ∏ k, (s k ^ (α k) * (ρ k ^ (α k + 1))⁻¹)) := by
  have hρ : ∀ k, 0 < ρ k := fun k => (hs k).trans_lt (hsρ k)
  have := (prod_hasSum n (fun k m => ((s k : ℂ)) ^ m * (((ρ k : ℂ)) ^ (m + 1))⁻¹)
    (fun k => (geom1 (s k) (ρ k) (by exact_mod_cast (hρ k).ne')
      (by simp [abs_of_nonneg (hs k), abs_of_pos (hρ k), hsρ k])).2)).2
  convert this using 1
  ext α
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [norm_mul, norm_pow, norm_inv, abs_of_nonneg (hs k), abs_of_pos (hρ k)]

/-! ### Cauchy formula on a torus -/

lemma torusMap_norm {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ k, 0 ≤ r k)
    (θ : Fin n → ℝ) (k : Fin n) : ‖torusMap a r θ k - a k‖ = r k := by
  simp [torusMap, norm_exp_ofReal_mul_I, abs_of_nonneg (hr k)]

lemma torusMap_mem {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ k, 0 ≤ r k)
    (θ : Fin n → ℝ) : torusMap a r θ ∈ cpd a r :=
  mem_cpd.2 fun k => (torusMap_norm a r hr θ k).le

lemma continuous_torusMap' {n : ℕ} (a : Fin n → ℂ) (r : Fin n → ℝ) :
    Continuous (torusMap a r) :=
  continuous_pi fun k => by
    show Continuous fun θ : Fin n → ℝ => a k + ((r k : ℝ) : ℂ) * Complex.exp (↑(θ k) * I)
    fun_prop

lemma prod_ne_zero_torus {n : ℕ} (a z : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hz : ∀ k, ‖z k - a k‖ < r k) (θ : Fin n → ℝ) :
    ∏ k, (torusMap a r θ k - z k) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro k _ h
  have h1 := torusMap_norm a r hr θ k
  rw [sub_eq_zero.1 h] at h1
  exact (hz k).ne h1

set_option maxHeartbeats 1000000 in
theorem cauchy : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (a : Fin n → ℂ) (r : Fin n → ℝ),
    (∀ k, 0 < r k) → ContinuousOn f (cpd a r) →
    (∀ w ∈ cpd a r, ∀ k, DifferentiableAt ℂ (fun ξ : ℂ => f (update w k (w k + ξ))) 0) →
    ∀ z ∈ polydisc a r,
    (∯ ζ in T(a, r), (∏ k, (ζ k - z k))⁻¹ • f ζ) = (2 * π * I) ^ n * f z
  | 0, f, a, r, _, _, _, z, _ => by
    simp [Subsingleton.elim z a]
  | n + 1, f, a, r, hr, hfc, hfd, z, hz => by
    have hz' := mem_polydisc.1 hz
    have hint : TorusIntegrable (fun ζ => (∏ k, (ζ k - z k))⁻¹ • f ζ) a r := by
      have hc : Continuous (fun θ => (∏ k, (torusMap a r θ k - z k))⁻¹ * f (torusMap a r θ)) := by
        refine Continuous.mul ?_ ?_
        · exact Continuous.inv₀ (continuous_finsetProd _ fun k _ =>
            ((continuous_apply k).comp (continuous_torusMap' a r)).sub continuous_const)
            (prod_ne_zero_torus a z r (fun k => (hr k).le) hz')
        · exact hfc.comp_continuous (continuous_torusMap' a r)
            (torusMap_mem a r (fun k => (hr k).le))
      exact hc.continuousOn.integrableOn_compact isCompact_Icc
    rw [torusIntegral_succAbove hint 0]
    set t : Fin n → ℂ := fun k => z k.succ with ht
    have ht' : t ∈ polydisc (a ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0) :=
      mem_polydisc.2 fun k => by simpa [t] using hz' k.succ
    have hcons : ∀ x : ℂ, ‖x - a 0‖ ≤ r 0 → ∀ y ∈ cpd (a ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0),
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ cpd a r := by
      intro x hx y hy
      rw [mem_cpd] at hy ⊢
      intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa using hx
      · simpa using hy j
    have hinner : ∀ x ∈ sphere (a 0) (r 0),
        (∯ y in T(a ∘ Fin.succAbove 0, r ∘ Fin.succAbove 0),
          (fun ζ => (∏ k, (ζ k - z k))⁻¹ • f ζ) ((0 : Fin (n + 1)).insertNth x y)) =
        (x - z 0)⁻¹ • ((2 * π * I) ^ n * f (Fin.cons x t)) := by
      intro x hx
      have hx' : ‖x - a 0‖ ≤ r 0 := (mem_sphere_iff_norm.1 hx).le
      have e : ∀ y : Fin n → ℂ,
          (∏ k, (((0 : Fin (n + 1)).insertNth x y : Fin (n + 1) → ℂ) k - z k))⁻¹ •
              f ((0 : Fin (n + 1)).insertNth x y) =
            (x - z 0)⁻¹ • ((∏ k, (y k - t k))⁻¹ • f (Fin.cons x y)) := by
        intro y
        simp only [Fin.insertNth_zero', Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
          smul_eq_mul, mul_inv, t]
        ring
      have hcc : Continuous (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) :=
        Continuous.finCons continuous_const continuous_id
      have IH := cauchy n (fun y => f (Fin.cons x y)) (a ∘ Fin.succAbove 0)
        (r ∘ Fin.succAbove 0) (fun k => hr _)
        (hfc.comp hcc.continuousOn (fun y hy => hcons x hx' y hy))
        (by
          intro w hw k
          have := hfd _ (hcons x hx' w hw) k.succ
          simpa [Fin.cons_update] using this)
        t ht'
      calc _ = ∯ y in T(a ∘ Fin.succAbove 0, r ∘ Fin.succAbove 0),
            (x - z 0)⁻¹ • ((∏ k, (y k - t k))⁻¹ • f (Fin.cons x y)) := by
              exact congrArg (fun F : (Fin n → ℂ) → ℂ =>
                ∯ y in T(a ∘ Fin.succAbove 0, r ∘ Fin.succAbove 0), F y) (funext e)
        _ = _ := by rw [torusIntegral_smul, IH]
    rw [circleIntegral.integral_congr (hr 0).le hinner]
    have hφd : ∀ x ∈ closedBall (a 0) (r 0), DifferentiableAt ℂ (fun x => f (Fin.cons x t)) x := by
      intro x hx
      have hmem := hcons x (mem_closedBall_iff_norm.1 hx) t
        (mem_cpd.2 fun k => (mem_polydisc.1 ht' k).le)
      have h0 := hfd _ hmem 0
      simp only [Fin.update_cons_zero, Fin.cons_zero] at h0
      have h0' : DifferentiableAt ℂ (fun ξ => f (Fin.cons (x + ξ) t)) (x - x) := by
        rwa [sub_self]
      have h2 := h0'.comp (f := fun y : ℂ => y - x) x ((differentiableAt_id).sub_const x)
      have hfeq : (fun y => f (Fin.cons y t)) =
          (fun ξ => f (Fin.cons (x + ξ) t)) ∘ (fun y : ℂ => y - x) := by
        funext y; simp
      rw [hfeq]; exact h2
    have hdcc : DiffContOnCl ℂ (fun x => f (Fin.cons x t)) (ball (a 0) (r 0)) := by
      refine ⟨fun x hx => (hφd x (ball_subset_closedBall hx)).differentiableWithinAt, ?_⟩
      rw [closure_ball (a 0) (hr 0).ne']
      exact fun x hx => (hφd x hx).continuousAt.continuousWithinAt
    have hcauchy : (2 * π * I : ℂ)⁻¹ • (∮ x in C(a 0, r 0), (x - z 0)⁻¹ • f (Fin.cons x t)) =
        f (Fin.cons (z 0) t) :=
      hdcc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (mem_ball_iff_norm.2 (hz' 0))
    have hzt : (Fin.cons (z 0) t : Fin (n + 1) → ℂ) = z := Fin.cons_self_tail z
    rw [hzt] at hcauchy
    have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have hI : (∮ x in C(a 0, r 0), (x - z 0)⁻¹ • f (Fin.cons x t)) = (2 * π * I) * f z := by
      rw [← hcauchy, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
    have e2 : (fun x => (x - z 0)⁻¹ • ((2 * π * I) ^ n * f (Fin.cons x t))) =
        fun x => (2 * π * I) ^ n • ((x - z 0)⁻¹ • f (Fin.cons x t)) := by
      funext x; simp only [smul_eq_mul]; ring
    rw [e2, circleIntegral.integral_smul, hI, smul_eq_mul, pow_succ]
    ring

lemma cpd_subset_closure {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k) :
    cpd a ρ ⊆ closure (polydisc a ρ) := by
  intro w hw
  rw [mem_cpd] at hw
  have hT : Tendsto (fun t : ℝ => a + (t : ℂ) • (w - a)) (𝓝[<] 1) (𝓝 w) := by
    have hc : Continuous (fun t : ℝ => a + (t : ℂ) • (w - a)) := by fun_prop
    have h := hc.tendsto 1
    rw [show a + ((1 : ℝ) : ℂ) • (w - a) = w by simp] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with t ht
  refine mem_polydisc.2 fun k => ?_
  have e : (a + (t : ℂ) • (w - a)) k - a k = (t : ℂ) * (w k - a k) := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
  calc t * ‖w k - a k‖ ≤ t * ρ k := mul_le_mul_of_nonneg_left (hw k) ht.1.le
    _ < ρ k := by nlinarith [hρ k, ht.2]

set_option maxHeartbeats 1000000 in
theorem cauchy_rho {n : ℕ} (f : (Fin n → ℂ) → ℂ) (a : Fin n → ℂ) (ρ : Fin n → ℝ)
    (hρ : ∀ k, 0 < ρ k) (hfc : ContinuousOn f (cpd a ρ))
    (hfd : ∀ w ∈ polydisc a ρ, ∀ k, DifferentiableAt ℂ (fun ξ : ℂ => f (update w k (w k + ξ))) 0)
    (z : Fin n → ℂ) (hz : z ∈ polydisc a ρ) :
    (∯ ζ in T(a, ρ), (∏ k, (ζ k - z k))⁻¹ • f ζ) = (2 * π * I) ^ n * f z := by
  have hz' := mem_polydisc.1 hz
  have hev : ∀ᶠ t in 𝓝[<] (1:ℝ), ∀ k, ‖z k - a k‖ < t * ρ k := by
    rw [Filter.eventually_all]
    intro k
    exact (tend_mul (ρ k)).eventually (lt_mem_nhds (hz' k))
  obtain ⟨t0, ht0, ht01⟩ := (hev.and (Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num))).exists
  have h01 : t0 ≤ 1 := ht01.2.le
  let P : ℝ → ℝ := fun s => (Set.projIcc t0 1 h01 s : ℝ)
  have hPc : Continuous P := continuous_subtype_val.comp continuous_projIcc
  have hPge : ∀ s, t0 ≤ P s := fun s => (Set.projIcc t0 1 h01 s).2.1
  have hPle : ∀ s, P s ≤ 1 := fun s => (Set.projIcc t0 1 h01 s).2.2
  let R : ℝ → Fin n → ℝ := fun s k => P s * ρ k
  have hR0 : ∀ s k, 0 ≤ R s k := fun s k => mul_nonneg (ht01.1.le.trans (hPge s)) (hρ k).le
  have hRle : ∀ s k, R s k ≤ ρ k := fun s k => by
    show P s * ρ k ≤ ρ k
    nlinarith [hPle s, hρ k]
  have hRgt : ∀ s k, ‖z k - a k‖ < R s k := fun s k =>
    (ht0 k).trans_le (mul_le_mul_of_nonneg_right (hPge s) (hρ k).le)
  let Φ : ℝ → ℂ := fun s => ∯ ζ in T(a, R s), (∏ k, (ζ k - z k))⁻¹ • f ζ
  have hΦc : Continuous Φ := by
    have hRc : ∀ k, Continuous (fun p : ℝ × (Fin n → ℝ) => ((R p.1 k : ℝ) : ℂ)) := fun k =>
      continuous_ofReal.comp ((hPc.comp continuous_fst).mul continuous_const)
    have hT : Continuous (fun p : ℝ × (Fin n → ℝ) => torusMap a (R p.1) p.2) := by
      refine continuous_pi fun k => ?_
      show Continuous fun p : ℝ × (Fin n → ℝ) =>
        a k + ((R p.1 k : ℝ) : ℂ) * Complex.exp (↑(p.2 k) * I)
      exact continuous_const.add ((hRc k).mul (by fun_prop))
    have hmem : ∀ p : ℝ × (Fin n → ℝ), torusMap a (R p.1) p.2 ∈ cpd a ρ := fun p =>
      mem_cpd.2 fun k => by rw [torusMap_norm a (R p.1) (hR0 p.1) p.2 k]; exact hRle p.1 k
    have hne : ∀ p : ℝ × (Fin n → ℝ), ∏ k, (torusMap a (R p.1) p.2 k - z k) ≠ 0 := fun p =>
      prod_ne_zero_torus a z (R p.1) (hR0 p.1) (fun k => hRgt p.1 k) p.2
    have hcont : Continuous (fun p : ℝ × (Fin n → ℝ) =>
        (∏ i, ((R p.1 i : ℝ) : ℂ) * Complex.exp (↑(p.2 i) * I) * I) *
          ((∏ k, (torusMap a (R p.1) p.2 k - z k))⁻¹ * f (torusMap a (R p.1) p.2))) := by
      refine Continuous.mul ?_ (Continuous.mul ?_ ?_)
      · exact continuous_finsetProd _ fun i _ =>
          ((hRc i).mul (by fun_prop)).mul continuous_const
      · exact Continuous.inv₀ (continuous_finsetProd _ fun k _ =>
          ((continuous_apply k).comp hT).sub continuous_const) hne
      · exact hfc.comp_continuous hT hmem
    exact continuous_parametric_integral_of_continuous (μ := volume) hcont isCompact_Icc
  have hR1 : R 1 = ρ := by
    funext k; show P 1 * ρ k = ρ k
    simp [P, Set.projIcc_right]
  have hlim : Tendsto Φ (𝓝[<] 1) (𝓝 (Φ 1)) := (hΦc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto Φ (𝓝[<] 1) (𝓝 ((2 * π * I) ^ n * f z)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht01.2] with s hs
    have hPs : P s = s := by
      simp [P, Set.projIcc_of_mem h01 ⟨hs.1.le, hs.2.le⟩]
    have hRlt : ∀ k, R s k < ρ k := fun k => by
      show P s * ρ k < ρ k
      rw [hPs]; nlinarith [hs.2, hρ k]
    refine (cauchy n f a (R s) (fun k => (norm_nonneg _).trans_lt (hRgt s k))
      (hfc.mono fun w hw => mem_cpd.2 fun k => (mem_cpd.1 hw k).trans (hRle s k)) ?_ z
      (mem_polydisc.2 fun k => hRgt s k)).symm
    intro w hw k
    exact hfd w (mem_polydisc.2 fun j => (mem_cpd.1 hw j).trans_lt (hRlt j)) k
  have key : (∯ ζ in T(a, R 1), (∏ k, (ζ k - z k))⁻¹ • f ζ) = (2 * π * I) ^ n * f z :=
    tendsto_nhds_unique hlim hlim2
  rwa [hR1] at key

/-! ### Part 1 -/

noncomputable def coef {n : ℕ} (f : (Fin n → ℂ) → ℂ) (a : Fin n → ℂ) (ρ : Fin n → ℝ)
    (α : Fin n → ℕ) : ℂ :=
  ((2 * π * I : ℂ) ^ n)⁻¹ * ∯ ζ in T(a, ρ), (∏ k, (ζ k - a k) ^ (α k + 1))⁻¹ • f ζ

lemma compact_scale {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (K : Set (Fin n → ℂ))
    (hK : IsCompact K) (hKs : K ⊆ polydisc a ρ) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ z ∈ K, ∀ k, ‖z k - a k‖ ≤ t * ρ k := by
  have hev : ∀ᶠ t in 𝓝[<] (1:ℝ), ∀ k, ∀ z ∈ K, ‖z k - a k‖ ≤ t * ρ k := by
    rw [Filter.eventually_all]
    intro k
    rcases K.eq_empty_or_nonempty with hE | hne
    · exact Eventually.of_forall fun t z hz => by simp [hE] at hz
    obtain ⟨z0, hz0, hmax⟩ := hK.exists_isMaxOn hne
      (f := fun z => ‖z k - a k‖) (by fun_prop)
    have hlt : ‖z0 k - a k‖ < ρ k := mem_polydisc.1 (hKs hz0) k
    filter_upwards [(tend_mul (ρ k)).eventually (lt_mem_nhds hlt)] with t ht z hz
    exact (show ‖z k - a k‖ ≤ ‖z0 k - a k‖ from hmax hz).trans ht.le
  obtain ⟨t, ht, ht01⟩ := (hev.and (Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num))).exists
  exact ⟨t, ht01.1, ht01.2, fun z hz k => ht k z hz⟩

set_option maxHeartbeats 1000000 in
theorem part1 {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ k, 0 < ρ k)
    (f : (Fin n → ℂ) → ℂ) (hfc : ContinuousOn f (closure (polydisc a ρ)))
    (hfh : IsHolomorphicOn f (polydisc a ρ)) :
    ∃ c : (Fin n → ℕ) → ℂ,
      (∀ K ⊆ polydisc a ρ, IsCompact K → ConvergesUniformlyAbsolutelyOn c a K) ∧
      ∀ z ∈ polydisc a ρ, HasSum (fun α => powerSeriesTerm c a α z) (f z) := by
  have hρ0 : ∀ k, 0 ≤ ρ k := fun k => (hρ k).le
  have hfc' : ContinuousOn f (cpd a ρ) := hfc.mono (cpd_subset_closure a ρ hρ)
  obtain ⟨M, hM⟩ := (isCompact_cpd a ρ).exists_bound_of_continuousOn hfc'
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a (mem_cpd.2 fun k => by simp [hρ0 k]))
  have hnorm : ∀ θ k, ‖torusMap a ρ θ k - a k‖ = ρ k := torusMap_norm a ρ hρ0
  have hne : ∀ θ k, torusMap a ρ θ k - a k ≠ 0 := fun θ k h => by
    have := hnorm θ k; rw [h, norm_zero] at this; exact (hρ k).ne this
  have hcontT : Continuous (torusMap a ρ) := continuous_torusMap' a ρ
  have hfT : Continuous (fun θ => f (torusMap a ρ θ)) :=
    hfc'.comp_continuous hcontT (torusMap_mem a ρ hρ0)
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  -- Cauchy estimates
  have hI : ∀ α : Fin n → ℕ, ‖∯ ζ in T(a, ρ), (∏ k, (ζ k - a k) ^ (α k + 1))⁻¹ • f ζ‖ ≤
      ((2 * π) ^ n * ∏ i, |ρ i|) * (M * (∏ k, ρ k ^ (α k + 1))⁻¹) := by
    intro α
    apply norm_torusIntegral_le_of_norm_le_const
    intro θ
    rw [norm_smul, norm_inv, norm_prod]
    simp only [norm_pow, hnorm]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _ (torusMap_mem a ρ hρ0 θ))
      (inv_nonneg.2 (Finset.prod_nonneg fun k _ => pow_nonneg (hρ0 k) _))
  have hc_bd : ∀ α : Fin n → ℕ, ‖coef f a ρ α‖ ≤
      (∏ i, |ρ i|) * M * (∏ k, ρ k ^ (α k + 1))⁻¹ := by
    intro α
    have h2 : ‖((2 * π * I : ℂ) ^ n)⁻¹‖ = ((2 * π) ^ n)⁻¹ := by
      rw [norm_inv, norm_pow]; congr 2; simp [abs_of_pos Real.pi_pos]
    rw [coef, norm_mul, h2]
    have hpos : (0 : ℝ) < (2 * π) ^ n := by positivity
    calc _ ≤ ((2 * π) ^ n)⁻¹ * (((2 * π) ^ n * ∏ i, |ρ i|) * (M * (∏ k, ρ k ^ (α k + 1))⁻¹)) :=
          mul_le_mul_of_nonneg_left (hI α) (by positivity)
      _ = _ := by field_simp
  refine ⟨coef f a ρ, ?_, ?_⟩
  · -- uniform absolute convergence on compacts
    intro K hKs hK
    obtain ⟨t, ht0, ht1, htK⟩ := compact_scale a ρ K hK hKs
    let v : (Fin n → ℕ) → ℝ := fun α =>
      (∏ i, |ρ i|) * M * ∏ k, ((t * ρ k) ^ (α k) * (ρ k ^ (α k + 1))⁻¹)
    have hv : Summable v := (summ_B (fun k => t * ρ k) ρ (fun k => mul_nonneg ht0.le (hρ0 k))
      (fun k => by nlinarith [hρ k])).mul_left _
    refine ⟨fun z => ∑' α, ‖powerSeriesTerm (coef f a ρ) a α z‖, ?_⟩
    refine tendstoUniformlyOn_tsum hv fun α z hz => ?_
    rw [norm_norm]
    unfold powerSeriesTerm
    rw [norm_mul, norm_prod]
    simp only [norm_pow]
    have hP : ∏ k, ‖z k - a k‖ ^ α k ≤ ∏ k, (t * ρ k) ^ α k :=
      Finset.prod_le_prod (fun k _ => by positivity)
        (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (htK z hz k) _)
    have hC : 0 ≤ (∏ i, |ρ i|) * M * (∏ k, ρ k ^ (α k + 1))⁻¹ :=
      mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => abs_nonneg _) hM0)
        (inv_nonneg.2 (Finset.prod_nonneg fun k _ => pow_nonneg (hρ0 k) _))
    calc ‖coef f a ρ α‖ * ∏ k, ‖z k - a k‖ ^ α k ≤
        ((∏ i, |ρ i|) * M * (∏ k, ρ k ^ (α k + 1))⁻¹) * ∏ k, (t * ρ k) ^ α k :=
          mul_le_mul (hc_bd α) hP (by positivity) hC
      _ = v α := by
          simp only [v, Finset.prod_mul_distrib, Finset.prod_inv_distrib]; ring
  · -- expansion
    intro z hz
    have hz' := mem_polydisc.1 hz
    let u : (Fin n → ℝ) → Fin n → ℕ → ℂ := fun θ k m =>
      (z k - a k) ^ m * ((torusMap a ρ θ k - a k) ^ (m + 1))⁻¹
    have hgeo : ∀ θ k, HasSum (u θ k) (torusMap a ρ θ k - z k)⁻¹ ∧
        Summable (fun m => ‖u θ k m‖) := by
      intro θ k
      have := geom1 (z k - a k) (torusMap a ρ θ k - a k) (hne θ k)
        (by rw [hnorm]; exact hz' k)
      rwa [sub_sub_sub_cancel_right] at this
    have hun : ∀ θ k m, ‖u θ k m‖ = ‖z k - a k‖ ^ m * (ρ k ^ (m + 1))⁻¹ := by
      intro θ k m; simp only [u, norm_mul, norm_inv, norm_pow, hnorm]
    let B : (Fin n → ℕ) → ℝ := fun α => ∏ k, (‖z k - a k‖ ^ (α k) * (ρ k ^ (α k + 1))⁻¹)
    have hB : Summable B := summ_B (fun k => ‖z k - a k‖) ρ (fun k => norm_nonneg _) hz'
    let J : (Fin n → ℝ) → ℂ := fun θ => ∏ i, ((ρ i : ℝ) : ℂ) * Complex.exp (↑(θ i) * I) * I
    have hJ : ∀ θ, ‖J θ‖ = ∏ i, |ρ i| := by
      intro θ; simp [J, norm_prod, norm_mul, norm_exp_ofReal_mul_I]
    have hJc : Continuous J := by
      show Continuous fun θ : Fin n → ℝ => ∏ i, ((ρ i : ℝ) : ℂ) * Complex.exp (↑(θ i) * I) * I
      fun_prop
    let G : (Fin n → ℕ) → (Fin n → ℝ) → ℂ := fun α θ =>
      J θ • ((∏ k, u θ k (α k)) • f (torusMap a ρ θ))
    let G0 : (Fin n → ℝ) → ℂ := fun θ =>
      J θ • ((∏ k, (torusMap a ρ θ k - z k))⁻¹ • f (torusMap a ρ θ))
    have hu_c : ∀ k m, Continuous (fun θ => u θ k m) := fun k m =>
      continuous_const.mul (Continuous.inv₀
        ((((continuous_apply k).comp hcontT).sub continuous_const).pow _)
        (fun θ => pow_ne_zero _ (hne θ k)))
    have hGc : ∀ α, Continuous (G α) := fun α =>
      hJc.smul ((continuous_finsetProd _ fun k _ => hu_c k (α k)).smul hfT)
    let μ : Measure (Fin n → ℝ) := volume.restrict (Icc (0 : Fin n → ℝ) fun _ => 2 * π)
    have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
    have hHS : HasSum (fun α => ∫ θ, G α θ ∂μ) (∫ θ, G0 θ ∂μ) := by
      refine hasSum_integral_of_dominated_convergence
        (fun α _ => (∏ i, |ρ i|) * (B α * M))
        (fun α => (hGc α).aestronglyMeasurable) (fun α => ae_of_all _ fun θ => ?_)
        (ae_of_all _ fun θ => (hB.mul_right M).mul_left _) (integrable_const _)
        (ae_of_all _ fun θ => ?_)
      · show ‖J θ • ((∏ k, u θ k (α k)) • f (torusMap a ρ θ))‖ ≤ _
        rw [norm_smul, norm_smul, hJ, norm_prod]
        simp only [hun]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hM _ (torusMap_mem a ρ hρ0 θ))
            (Finset.prod_nonneg fun k _ => mul_nonneg (pow_nonneg (norm_nonneg _) _)
              (inv_nonneg.2 (pow_nonneg (hρ0 k) _))))
          (Finset.prod_nonneg fun i _ => abs_nonneg _)
      · have h := (prod_hasSum n (u θ) (fun k => (hgeo θ k).2)).1
        have htsum : ∏ k, ∑' m, u θ k m = (∏ k, (torusMap a ρ θ k - z k))⁻¹ := by
          rw [← Finset.prod_inv_distrib]
          exact Finset.prod_congr rfl fun k _ => (hgeo θ k).1.tsum_eq
        rw [htsum] at h
        exact (h.smul_const (f (torusMap a ρ θ))).const_smul (J θ)
    have e0 : ∫ θ, G0 θ ∂μ = ∯ ζ in T(a, ρ), (∏ k, (ζ k - z k))⁻¹ • f ζ := rfl
    have eα : ∀ α : Fin n → ℕ, ∫ θ, G α θ ∂μ = (∏ k, (z k - a k) ^ (α k)) *
        ∯ ζ in T(a, ρ), (∏ k, (ζ k - a k) ^ (α k + 1))⁻¹ • f ζ := by
      intro α
      rw [← smul_eq_mul, ← torusIntegral_smul]
      show ∫ θ, G α θ ∂μ = ∫ θ, J θ • ((∏ k, (z k - a k) ^ (α k)) •
        ((∏ k, (torusMap a ρ θ k - a k) ^ (α k + 1))⁻¹ • f (torusMap a ρ θ))) ∂μ
      refine integral_congr_ae (ae_of_all _ fun θ => ?_)
      simp only [G, u, smul_eq_mul]
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]; ring
    have h2 := hHS.mul_left (((2 * π * I : ℂ) ^ n)⁻¹)
    rw [e0, cauchy_rho f a ρ hρ hfc' hfh.2 z hz, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ h2pi), one_mul] at h2
    have hfun : (fun α => powerSeriesTerm (coef f a ρ) a α z) =
        fun α => ((2 * π * I : ℂ) ^ n)⁻¹ * ∫ θ, G α θ ∂μ := by
      funext α; rw [eα]; simp only [powerSeriesTerm, coef]; ring
    rw [hfun]; exact h2

end PSP

open LeblSCV.Holomorphic in
theorem solution {n : ℕ} (a : Fin n → ℂ) (ρ : Fin n → ℝ)
    (hρ : ∀ k, 0 < ρ k) :
    (∀ f : (Fin n → ℂ) → ℂ, ContinuousOn f (closure (LeblSCV.Shared.polydisc a ρ)) →
        IsHolomorphicOn f (LeblSCV.Shared.polydisc a ρ) →
        ∃ c : (Fin n → ℕ) → ℂ,
          (∀ K ⊆ LeblSCV.Shared.polydisc a ρ, IsCompact K → ConvergesUniformlyAbsolutelyOn c a K) ∧
          ∀ z ∈ LeblSCV.Shared.polydisc a ρ, HasSum (fun α => powerSeriesTerm c a α z) (f z)) ∧
    (∀ (c : (Fin n → ℕ) → ℂ) (f : (Fin n → ℂ) → ℂ),
        (∀ K ⊆ LeblSCV.Shared.polydisc a ρ, IsCompact K → ConvergesUniformlyAbsolutelyOn c a K) →
        (∀ z ∈ LeblSCV.Shared.polydisc a ρ, HasSum (fun α => powerSeriesTerm c a α z) (f z)) →
        IsHolomorphicOn f (LeblSCV.Shared.polydisc a ρ)) := by
  exact ⟨fun f hfc hfh => PSP.part1 a ρ hρ f hfc hfh, fun c f hc hf => PSP.part2 a ρ c f hc hf⟩
