-- Prove2me | solution 1 for GuthMaynard.norm_S_three_le_refined
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:49:40.840909+00:00
-- url     : https://prove2.me/submissions/560c0a86-e43d-4f46-a987-3f455704528a

import Mathlib
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_J_le_of_fourier_decay

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
/-!
# Blueprint: Guth–Maynard Proposition 10.1 (`norm_S_three_le_refined`), pp. 20–38

Design: `P101BRIEF.md` (same folder), with the corrections listed below. Notation:
`R(v) = ∑_{t ∈ W} v^{it}` (`Rv`), `L = T^{1+η}/N`, `Q = T^η`, `M = scale i = 2^i/2`, `ρ = Q/(NM)`.

* P1 `box_trunc`: `‖S₃‖ ≤ ∑_{m ∈ box L} ‖I_m‖ + T²|W|^{3/2}`.
* P2 `Iterm_cyc`, `conj_Iterm` (the corrected conjugation identity
  `conj I_m = I_{(-m₀, -m₂, -m₁)}`), `sum_box_le` (`∑_box ≤ 6 ∑_{ordered box}`).
* P3 `norm_Iterm_le`: `‖I_m‖ ≤ N³ ∫∫ |R(v₁)||R(v₂/v₁)||R(v₂)||K_m(v₁,v₂)|` (`Ifull`), and
  `Kfun_le` (`|K_m| ≤ A`, `|K_m| (N|phase|)^k ≤ A`).
* P4 `far_sum_le`: the ordered `m` with `|m₂| > 5|m₁|` are negligible; `sum_ordBox_le` splits the
  rest into the dyadic groups `grp L i₁ i` (`|m₀| ∼ scale i₁`, `|m₁| ∼ scale i`, `|m₂| ≤ 5|m₁|`),
  `scale_le`, `card_nsc_le` (`O(L^η)` scales).
* P5 `local_bound`: the `v₂`-integral `Kint` for fixed `m, v₁`.
* P6 `fP_adm`: `f = fP W ρ` satisfies the hypotheses of Proposition 9.1 with `C = 16`.
* P7 `moments`: `∫_{1/2}^2 |R|² , ∫ f ≲ T^η |W|`, `∫ f² ≲ T^η E(W)`.
* P8 `intY_le`, `intX_le` (the two `J`-sums), `group_sum_le` (one group), and the assembly
  `norm_S_three_le_refined_dev`, which is proved here from the stubs and Proposition 9.1.

Corrections to the brief:
* `ψ_out` must be `≥ 1` on `[1/8, 8]`, not `[1/4, 4]`: in P5 the point `x = c/v₁` at which
  `Ψ(x) ≤ ρ f(x)` is needed only satisfies `x ∈ [1/4 - 2ρ, 4 + 2ρ]`. So `supp ψ_out ⊆ (1/16, 16)`
  and Proposition 9.1 is applied with `C = 16` (any `C ≥ 1` is allowed). `ψ_in ≥ 1` on `[1/4, 4]`,
  `supp ψ_in ⊆ (1/8, 33/8)`, `φ = 1` on `[-2, 2]`, `supp φ ⊆ (-3, 3)`.
* P6 needs no `ρ ≤ 1/4`: `f(1) ≥ ρ⁻¹ ∫_{|y-1| ≤ 1/(4T)} |R|² ≥ |W|²/(8ρT)` uses only `ρT ≥ 1`.
* The conjugation identity: `conj I_m = I_{(-m₀,-m₂,-m₁)}` (as in the brief; checked:
  `conj ĥ_t(ξ) = ĥ_{-t}(-ξ)` and the relabelling `(t₁,t₂,t₃) ↦ (t₁,t₃,t₂)`).
* Indexing is 0-based: `m = (m 0, m 1, m 2)`, phase `m₀v₁ + m₁v₂ + m₂`, ordered means
  `|m 0| ≤ |m 1| ≤ |m 2|`; the paper's `(m₁, m₂, m₃)`.
-/
/-! ## Definitions -/
/-- `R(v) = ∑_{t ∈ W} v^{it}`. -/
noncomputable def Rv (W : Finset ℝ) (v : ℝ) : ℂ := ∑ t ∈ W, (v : ℂ) ^ ((t : ℂ) * I)

/-- The phase `m₀v₁ + m₁v₂ + m₂` of `K_m`. -/
noncomputable def phase (m : Fin 3 → ℤ) (v₁ v₂ : ℝ) : ℝ := m 0 * v₁ + m 1 * v₂ + m 2

/-- `K_m(v₁,v₂) = ∫ e(-N·phase·u) u² w(u)² w(v₁u)² w(v₂u)² du`. -/
noncomputable def Kfun (w : ℝ → ℝ) (N : ℕ) (m : Fin 3 → ℤ) (v₁ v₂ : ℝ) : ℂ :=
  𝓕 (fun u : ℝ => ((u ^ 2 * w u ^ 2 * w (v₁ * u) ^ 2 * w (v₂ * u) ^ 2 : ℝ) : ℂ))
    ((N : ℝ) * phase m v₁ v₂)

/-- The inner integral `∫_{1/2}^{2} |R(v₂/v₁)| |R(v₂)| |K_m(v₁,v₂)| dv₂`. -/
noncomputable def Kint (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) (v₁ : ℝ) : ℝ :=
  ∫ v₂ in Set.Icc (1 / 2 : ℝ) 2, ‖Rv W (v₂ / v₁)‖ * ‖Rv W v₂‖ * ‖Kfun w N m v₁ v₂‖

/-- `∫∫_{[1/2,2]²} |R(v₁)| |R(v₂/v₁)| |R(v₂)| |K_m(v₁,v₂)|`. -/
noncomputable def Ifull (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) : ℝ :=
  ∫ v₁ in Set.Icc (1 / 2 : ℝ) 2, ‖Rv W v₁‖ * Kint w N W m v₁

/-- `box L = {m : all mᵢ ≠ 0, |mᵢ| ≤ L}`. -/
noncomputable def box (L : ℝ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ => (Finset.Icc (-⌊L⌋) ⌊L⌋).erase 0

/-- The ordered part of the box: `|m₀| ≤ |m₁| ≤ |m₂|`. -/
noncomputable def ordBox (L : ℝ) : Finset (Fin 3 → ℤ) :=
  (box L).filter fun m => |m 0| ≤ |m 1| ∧ |m 1| ≤ |m 2|

/-- The negligible ordered terms `|m₂| > 5|m₁|`. -/
noncomputable def far (L : ℝ) : Finset (Fin 3 → ℤ) :=
  (ordBox L).filter fun m => 5 * |m 1| < |m 2|

/-- Dyadic scales `2^i/2` (`dyadic (scale i) = (2^{i-1}, 2^i] ∩ ℤ`). -/
noncomputable def scale (i : ℕ) : ℝ := 2 ^ i / 2

/-- Number of dyadic scales needed below `L`. -/
noncomputable def nsc (L : ℝ) : ℕ := Nat.clog 2 ⌊L⌋₊ + 1

/-- A group: ordered, `|m₀| ∼ scale i₁`, `|m₁| ∼ scale i`, `|m₂| ≤ 5|m₁|`. -/
noncomputable def grp (L : ℝ) (i₁ i : ℕ) : Finset (Fin 3 → ℤ) :=
  (ordBox L).filter fun m =>
    |m 0| ∈ dyadic (scale i₁) ∧ |m 1| ∈ dyadic (scale i) ∧ |m 2| ≤ 5 * |m 1|

/-- `x_m(v₁) = (m₀v₁ + m₂)/(-m₁v₁)` (`= c/v₁`). -/
noncomputable def xm (m : Fin 3 → ℤ) (v : ℝ) : ℝ := (m 0 * v + m 2) / (-(m 1 : ℝ) * v)

/-- `y_m(v₁) = (m₀v₁ + m₂)/(-m₁)` (`= c`, the zero of the phase in `v₂`). -/
noncomputable def ym (m : Fin 3 → ℤ) (v : ℝ) : ℝ := (m 0 * v + m 2) / (-(m 1 : ℝ))

/-- `∫_{1/2}^{2} |R|²`. -/
noncomputable def RL2 (W : Finset ℝ) : ℝ := ∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖Rv W v‖ ^ 2

/-- `φ`: `= 1` on `[-2, 2]`, support `(-3, 3)`. -/
noncomputable def φb : ContDiffBump (0 : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩

/-- `ψ_in`: `= 1` on `[1/4, 4]`, support `(1/8, 33/8)`. -/
noncomputable def ψinb : ContDiffBump (17 / 8 : ℝ) := ⟨15 / 8, 2, by norm_num, by norm_num⟩

/-- `ψ_out`: `= 1` on `[1/8, 8]`, support `(1/16, 129/16)`. -/
noncomputable def ψoutb : ContDiffBump (65 / 16 : ℝ) := ⟨63 / 16, 4, by norm_num, by norm_num⟩

noncomputable def φ (x : ℝ) : ℝ := φb x

noncomputable def ψin (x : ℝ) : ℝ := ψinb x

noncomputable def ψout (x : ℝ) : ℝ := ψoutb x

/-- The function of P6: `f(x) = ψ_out(x) ρ⁻¹ ∫ φ((y-x)/ρ) ψ_in(y) |R(y)|² dy`. -/
noncomputable def fP (W : Finset ℝ) (ρ x : ℝ) : ℝ :=
  ψout x * (ρ⁻¹ * ∫ y, φ ((y - x) / ρ) * ψin y * ‖Rv W y‖ ^ 2)

/-! ## Proved basic facts -/
theorem Kint_nonneg (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) (v₁ : ℝ) :
    0 ≤ Kint w N W m v₁ :=
  integral_nonneg fun _ => by positivity

theorem Ifull_nonneg (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) :
    0 ≤ Ifull w N W m :=
  integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (Kint_nonneg _ _ _ _ _)

theorem scale_pos (i : ℕ) : 0 < scale i := by unfold scale; positivity

theorem half_le_scale (i : ℕ) : 1 / 2 ≤ scale i := by
  unfold scale
  have := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := i)
  linarith

theorem separated_one {T ε : ℝ} (hT : 1 ≤ T) (hε : 0 < ε) {W : Finset ℝ}
    (h : IsSeparated (T ^ ε) W) : IsSeparated 1 W :=
  fun t ht t' ht' hne => le_trans (Real.one_le_rpow hT hε.le) (h t ht t' ht' hne)

theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part1
open GuthMaynard GuthMaynard.P101 MeasureTheory Complex Set
open scoped Real
/-! ## Copied from `GuthMaynardS56` (Amp, Ibp, DecayZero, DecayFreq, HHat) -/
/-- amplitude: smooth, supported in `[1,2]` -/
def Amp (G : ℝ → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) G ∧ tsupport G ⊆ Icc (1:ℝ) 2

theorem Amp.zero_of_lt {G : ℝ → ℂ} (h : Amp G) {u : ℝ} (hu : u < 1) : G u = 0 := by
  by_contra hne
  have : u ∈ tsupport G := subset_tsupport _ (Function.mem_support.2 hne)
  have := h.2 this
  simp only [mem_Icc] at this
  linarith [this.1]

theorem Amp.zero_of_notMem {G : ℝ → ℂ} (h : Amp G) {u : ℝ} (hu : u ∉ Icc (1:ℝ) 2) : G u = 0 := by
  by_contra hne
  exact hu (h.2 (subset_tsupport _ (Function.mem_support.2 hne)))

theorem Amp.deriv {G : ℝ → ℂ} (h : Amp G) : Amp (deriv G) := by
  refine ⟨?_, ?_⟩
  · exact (contDiff_infty_iff_deriv.1 h.1).2
  · have h1 : tsupport (_root_.deriv G) ⊆ tsupport G := tsupport_deriv_subset
    exact h1.trans h.2

theorem Amp.mul_inv {G : ℝ → ℂ} (h : Amp G) : Amp (fun u => G u * ((u⁻¹ : ℝ) : ℂ)) := by
  refine ⟨?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < 1
    · have : (fun u => G u * ((u⁻¹ : ℝ) : ℂ)) =ᶠ[nhds x] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hx] with u hu
        simp [h.zero_of_lt hu]
      exact (contDiffAt_const).congr_of_eventuallyEq this
    · have hx0 : x ≠ 0 := by intro h0; apply hx; rw [h0]; norm_num
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) G x := h.1.contDiffAt
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_inv ℝ hx0)
      exact h1.mul h2
  · refine (tsupport_mul_subset_left).trans h.2

/-- Whole-line integration by parts for a compactly supported amplitude. -/
theorem ibp_amp {A A' F F' : ℝ → ℂ} (hAs : tsupport A ⊆ Icc (1:ℝ) 2)
    (hA : ∀ x, HasDerivAt A (A' x) x) (hF : ∀ x ∈ Icc (1:ℝ) 2, HasDerivAt F (F' x) x)
    (hA'z : ∀ x, x ∉ Icc (1:ℝ) 2 → A' x = 0)
    (hA'c : ContinuousOn A' (Icc 1 2)) (hF'c : ContinuousOn F' (Icc 1 2))
    (hFc : ContinuousOn F (Icc 1 2)) :
    ∫ x, A x * F' x = -∫ x, A' x * F x := by
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun x => (hA x).continuousAt
  have hAz : ∀ x, x ∉ Icc (1:ℝ) 2 → A x = 0 := fun x hx => by
    by_contra hne
    exact hx (hAs (subset_tsupport _ (Function.mem_support.2 hne)))
  have hI1 : Integrable (A * F') := by
    have : IntegrableOn (A * F') (Icc 1 2) :=
      (hAc.continuousOn.mul hF'c).integrableOn_Icc
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 this
    intro x hx
    by_contra hx'
    exact hx (by simp [Pi.mul_apply, hAz x hx'])
  have hI2 : Integrable (A' * F) := by
    have : IntegrableOn (A' * F) (Icc 1 2) := (hA'c.mul hFc).integrableOn_Icc
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 this
    intro x hx
    by_contra hx'
    exact hx (by simp [Pi.mul_apply, hA'z x hx'])
  have key := integral_mul_deriv_eq_deriv_mul (u := A) (v := F) (u' := A') (v' := F')
    (a' := 0) (b' := 0) (fun x _ => hA x) ?_ hI1 hI2 ?_ ?_
  · simpa using key
  · intro x hx
    exact hF x (hAs hx)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_lt_atBot (1:ℝ)] with x hx
    simp [hAz x (fun h => by linarith [h.1])]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (2:ℝ)] with x hx
    simp [hAz x (fun h => by linarith [h.2])]

theorem norm_cpow_it {u : ℝ} (hu : 0 < u) (t : ℝ) : ‖(u:ℂ)^((t:ℂ)*I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]; simp

theorem contAt_cpow (c : ℂ) {u : ℝ} (hu : 0 < u) : ContinuousAt (fun u : ℝ => (u:ℂ)^c) u :=
  ContinuousAt.cpow (Complex.continuous_ofReal.continuousAt) continuousAt_const (Complex.ofReal_mem_slitPlane.2 hu)

theorem contOn_cpow (c : ℂ) : ContinuousOn (fun u : ℝ => (u:ℂ)^c) (Icc 1 2) := fun u hu =>
  (contAt_cpow c (by linarith [hu.1])).continuousWithinAt

theorem Amp.continuous {G : ℝ → ℂ} (h : Amp G) : Continuous G := h.1.continuous

theorem Amp.integrable_norm {G : ℝ → ℂ} (h : Amp G) : Integrable (fun u => ‖G u‖) := by
  have hc : HasCompactSupport G := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) h.2
  exact (h.continuous.integrable_of_hasCompactSupport hc).norm

theorem Amp.integrable_mul {G : ℝ → ℂ} (h : Amp G) {H : ℝ → ℂ} (hH : ContinuousOn H (Icc 1 2)) :
    Integrable (fun u => G u * H u) := by
  have : IntegrableOn (fun u => G u * H u) (Icc 1 2) :=
    (h.continuous.continuousOn.mul hH).integrableOn_Icc
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 this
  intro x hx
  by_contra hx'
  exact hx (by simp [h.zero_of_notMem hx'])

/-- the character `u ↦ e(-ξu)` as `exp(c u)` -/
noncomputable def Ec (ξ : ℝ) (u : ℝ) : ℂ := Complex.exp ((((-2 * π * ξ : ℝ) : ℂ) * I) * (u:ℂ))

theorem norm_Ec (ξ u : ℝ) : ‖Ec ξ u‖ = 1 := by
  unfold Ec
  rw [Complex.norm_exp]
  simp

theorem hasDerivAt_Ec (ξ u : ℝ) :
    HasDerivAt (Ec ξ) ((((-2 * π * ξ : ℝ) : ℂ) * I) * Ec ξ u) u := by
  unfold Ec
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp ((((-2 * π * ξ : ℝ) : ℂ) * I) * z))
      (Complex.exp ((((-2 * π * ξ : ℝ) : ℂ) * I) * (u:ℂ)) * (((-2 * π * ξ : ℝ) : ℂ) * I)) (u:ℂ) := by
    have := ((hasDerivAt_id (u:ℂ)).const_mul ((((-2 * π * ξ : ℝ) : ℂ) * I))).cexp
    simpa using this
  have := h1.comp_ofReal
  convert this using 1
  ring

theorem continuous_Ec (ξ : ℝ) : Continuous (Ec ξ) := by
  unfold Ec
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

theorem hasDerivAt_cpow_it (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y:ℂ)^((t:ℂ)*I)) ((t:ℂ)*I * ((x⁻¹ : ℝ) : ℂ) * (x:ℂ)^((t:ℂ)*I)) x := by
  by_cases ht : t = 0
  · subst ht; simpa using hasDerivAt_const x (1:ℂ)
  · have hr : (t:ℂ)*I ≠ 0 := by simp [ht]
    have h := hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hr
    have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
    convert h using 1
    rw [Complex.cpow_sub _ _ hx0, Complex.cpow_one]
    push_cast
    ring

theorem decay_freq : ∀ k : ℕ, ∀ G : ℝ → ℂ, Amp G → ∃ C : ℝ, ∀ t ξ : ℝ, ξ ≠ 0 →
    ‖∫ u, G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ * |ξ|^k ≤ C * (1 + |t|)^k := by
  intro k
  induction k with
  | zero =>
    intro G hG
    refine ⟨∫ u, ‖G u‖, fun t ξ hξ => ?_⟩
    simp only [pow_zero, mul_one]
    refine norm_integral_le_of_norm_le hG.integrable_norm (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : 0 < u
    · simp [norm_cpow_it hu, norm_Ec]
    · have : G u = 0 := hG.zero_of_notMem (fun hh => hu (by linarith [hh.1]))
      simp [this]
  | succ k ih =>
    intro G hG
    obtain ⟨C1, hC1⟩ := ih (deriv G) hG.deriv
    obtain ⟨C3, hC3⟩ := ih (fun u => G u * ((u⁻¹ : ℝ) : ℂ)) hG.mul_inv
    refine ⟨|C1| + |C3|, fun t ξ hξ => ?_⟩
    set c : ℂ := (((-2 * π * ξ : ℝ) : ℂ) * I) with hc
    have hc0 : c ≠ 0 := by
      simp only [hc]
      have : (-2 * π * ξ : ℝ) ≠ 0 := by
        have := Real.pi_pos
        intro h
        have : ξ = 0 := by
          have h2 : (-2 * π) * ξ = 0 := h
          rcases mul_eq_zero.1 h2 with h3 | h3
          · linarith
          · exact h3
        exact hξ this
      exact mul_ne_zero (by exact_mod_cast this) Complex.I_ne_zero
    have hcn : ‖c‖ = 2 * π * |ξ| := by
      simp only [hc]; rw [norm_mul]; simp [abs_of_pos Real.pi_pos]
    set A : ℝ → ℂ := fun u => G u * (u:ℂ)^((t:ℂ)*I) with hAdef
    set A' : ℝ → ℂ := fun u => (deriv G u + (t:ℂ)*I * (G u * ((u⁻¹ : ℝ) : ℂ))) * (u:ℂ)^((t:ℂ)*I)
      with hA'def
    have hAd : ∀ x, HasDerivAt A (A' x) x := by
      intro x
      by_cases hx : 0 < x
      · have h1 : HasDerivAt G (deriv G x) x :=
          (hG.1.differentiable (by simp)).differentiableAt.hasDerivAt
        have h2 := h1.mul (hasDerivAt_cpow_it t hx)
        refine h2.congr_deriv ?_
        simp only [hA'def]; ring
      · have hev : A =ᶠ[nhds x] fun _ => 0 := by
          have hx1 : x < 1 := by linarith
          filter_upwards [Iio_mem_nhds hx1] with u hu
          simp [hAdef, hG.zero_of_lt hu]
        have h0 : HasDerivAt (fun _ : ℝ => (0:ℂ)) 0 x := hasDerivAt_const x 0
        have := h0.congr_of_eventuallyEq hev
        have hxn : x ∉ Icc (1:ℝ) 2 := fun hh => hx (by linarith [hh.1])
        refine this.congr_deriv ?_
        simp [hA'def, hG.deriv.zero_of_notMem hxn, hG.zero_of_notMem hxn]
    set F : ℝ → ℂ := fun u => Ec ξ u / c with hFdef
    have hFd : ∀ x, HasDerivAt F (Ec ξ x) x := by
      intro x
      have := (hasDerivAt_Ec ξ x).div_const c
      refine this.congr_deriv ?_
      exact mul_div_cancel_left₀ _ hc0
    have hcontcpow : ContinuousOn (fun u : ℝ => (u:ℂ)^((t:ℂ)*I)) (Icc 1 2) := contOn_cpow _
    have hA'c : ContinuousOn A' (Icc 1 2) := by
      have h1 : ContinuousOn (fun u : ℝ => deriv G u) (Icc 1 2) := hG.deriv.continuous.continuousOn
      have h2 : ContinuousOn (fun u : ℝ => G u * ((u⁻¹ : ℝ) : ℂ)) (Icc 1 2) :=
        hG.mul_inv.continuous.continuousOn
      exact (h1.add (continuousOn_const.mul h2)).mul hcontcpow
    have key : ∫ x, A x * Ec ξ x = -∫ x, A' x * F x := by
      refine ibp_amp (A := A) (A' := A') (F := F) (F' := Ec ξ) ?_ hAd (fun x _ => hFd x) ?_ hA'c
        (continuous_Ec ξ).continuousOn ((continuous_Ec ξ).div_const c).continuousOn
      · exact (tsupport_mul_subset_left).trans hG.2
      · intro x hx
        simp [hA'def, hG.deriv.zero_of_notMem hx, hG.zero_of_notMem hx]
    have hI1 : Integrable (fun u => deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) :=
      hG.deriv.integrable_mul (hcontcpow.mul (continuous_Ec ξ).continuousOn)
    have hI3 : Integrable (fun u => (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) :=
      hG.mul_inv.integrable_mul (hcontcpow.mul (continuous_Ec ξ).continuousOn)
    have hsplit : ∫ x, A' x * F x = (1 / c) * ((∫ u, deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) +
        (t:ℂ)*I * ∫ u, (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) := by
      have hpt : (fun x => A' x * F x) = fun x => (1 / c) * (deriv G x * ((x:ℂ)^((t:ℂ)*I) * Ec ξ x) +
          (t:ℂ)*I * ((G x * ((x⁻¹ : ℝ) : ℂ)) * ((x:ℂ)^((t:ℂ)*I) * Ec ξ x))) := by
        funext x
        simp only [hA'def, hFdef]
        field_simp
      rw [hpt, integral_const_mul, integral_add hI1 (hI3.const_mul _), integral_const_mul]
    have hmain : ∫ u, G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u) = -∫ x, A' x * F x := by
      rw [← key]; congr 1; funext x; simp only [hAdef]; ring
    rw [hmain, hsplit, norm_neg, norm_mul, norm_div, norm_one, hcn]
    have h1 := hC1 t ξ hξ
    have h3 := hC3 t ξ hξ
    have hξp : 0 < |ξ| := abs_pos.2 hξ
    have hpi : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
    have hsum : ‖(∫ u, deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)) +
        (t:ℂ)*I * ∫ u, (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ * |ξ|^k ≤
        (|C1| + |C3|) * (1 + |t|)^(k+1) := by
      calc _ ≤ (‖∫ u, deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ +
            |t| * ‖∫ u, (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖) * |ξ|^k := by
              gcongr
              refine (norm_add_le _ _).trans ?_
              gcongr
              simp
        _ = ‖∫ u, deriv G u * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ * |ξ|^k +
            |t| * (‖∫ u, (G u * ((u⁻¹ : ℝ) : ℂ)) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u)‖ * |ξ|^k) := by ring
        _ ≤ |C1| * (1 + |t|)^k + |t| * (|C3| * (1 + |t|)^k) := by
              exact add_le_add
                (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
                (mul_le_mul_of_nonneg_left
                  (h3.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)))
                  (abs_nonneg t))
        _ ≤ (|C1| + |C3|) * (1 + |t|)^(k+1) := by
              have hp : 0 ≤ (1 + |t|)^k := by positivity
              have : (1 + |t|)^(k+1) = (1+|t|)^k * (1 + |t|) := pow_succ _ _
              rw [this]
              nlinarith [abs_nonneg C1, abs_nonneg C3, abs_nonneg t, mul_nonneg (abs_nonneg C1) hp,
                mul_nonneg (abs_nonneg C3) hp, mul_nonneg (mul_nonneg (abs_nonneg C3) hp) (abs_nonneg t),
                mul_nonneg (mul_nonneg (abs_nonneg C1) hp) (abs_nonneg t)]
    have hfac : 1 / (2 * π * |ξ|) ≤ 1 / |ξ| := by
      apply one_div_le_one_div_of_le hξp
      nlinarith
    have hg : ∀ X : ℝ, 1 / |ξ| * X * |ξ|^(k+1) = X * |ξ|^k := by
      intro X; rw [pow_succ]; field_simp
    calc 1 / (2 * π * |ξ|) * ‖_‖ * |ξ|^(k+1) ≤ 1 / |ξ| * ‖_‖ * |ξ|^(k+1) := by gcongr
      _ = _ := hg _
      _ ≤ _ := hsum

theorem ampW {w : ℝ → ℝ} (hw : IsWeight w) :
    Amp (fun u => ((w u ^ 2 : ℝ) : ℂ)) := by
  refine ⟨?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((hw.smooth).pow 2)
  · have h1 : tsupport (fun u => ((w u ^ 2 : ℝ) : ℂ)) ⊆ tsupport w := by
      apply closure_mono
      intro u hu
      simp only [Function.mem_support] at hu ⊢
      intro h; apply hu; simp [h]
    refine h1.trans ?_
    exact closure_minimal hw.support_subset isClosed_Icc

theorem hHat_eq {w : ℝ → ℝ} (t ξ : ℝ) :
    hHat w t ξ =
      ∫ u, ((w u ^ 2 : ℝ) : ℂ) * ((u:ℂ)^((t:ℂ)*I) * Ec ξ u) := by
  unfold hHat
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext u
  simp only [smul_eq_mul, Ec]
  have : (((-2 * π * u * ξ : ℝ) : ℂ) * I) = (((-2 * π * ξ : ℝ) : ℂ) * I) * (u:ℂ) := by
    push_cast; ring
  rw [this]; ring

theorem hHat_bdd {w : ℝ → ℝ} (hw : IsWeight w) :
    ∃ C : ℝ, ∀ t ξ : ℝ, ‖hHat w t ξ‖ ≤ C := by
  have hG := ampW hw
  refine ⟨∫ u, ‖((w u ^ 2 : ℝ) : ℂ)‖, fun t ξ => ?_⟩
  rw [hHat_eq]
  refine norm_integral_le_of_norm_le hG.integrable_norm (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : 0 < u
  · simp [norm_cpow_it hu, norm_Ec]
  · have : ((w u ^ 2 : ℝ) : ℂ) = 0 := hG.zero_of_notMem (fun hh => hu (by linarith [hh.1]))
    simp [this]

theorem hHat_decay_freq {w : ℝ → ℝ} (hw : IsWeight w) (k : ℕ) :
    ∃ C : ℝ, ∀ t ξ : ℝ, ξ ≠ 0 → ‖hHat w t ξ‖ * |ξ|^k ≤ C * (1 + |t|)^k := by
  obtain ⟨C, hC⟩ := decay_freq k _ (ampW hw)
  exact ⟨C, fun t ξ hξ => by rw [hHat_eq]; exact hC t ξ hξ⟩

/-! ## Targets -/
/-- Bounds for `ĥ` (copy `GuthMaynardS56.hHat_bdd`, `hHat_decay_freq`). -/
theorem hHat_bound {w : ℝ → ℝ} (hw : IsWeight w) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ξ : ℝ, ‖hHat w t ξ‖ ≤ A ∧
      (ξ ≠ 0 → ‖hHat w t ξ‖ * |ξ| ^ k ≤ A * (1 + |t|) ^ k) := by
  obtain ⟨C, hC⟩ := hHat_bdd hw
  obtain ⟨C', hC'⟩ := hHat_decay_freq hw k
  refine ⟨|C| + |C'|, by positivity, fun t ξ => ⟨?_, fun hξ => ?_⟩⟩
  · exact (hC t ξ).trans ((le_abs_self C).trans (le_add_of_nonneg_right (abs_nonneg _)))
  · refine (hC' t ξ hξ).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (le_abs_self C').trans (le_add_of_nonneg_left (abs_nonneg _))

end GuthMaynard.P101.Part1
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
/-! ## P1: truncation to the box -/

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part1
open GuthMaynard GuthMaynard.P101 MeasureTheory Complex Set
open scoped Real
/-- A `1`-separated set in an interval of length `T` has at most `T + 1` points. -/
theorem card_le_of_sep {T a : ℝ} (hT : 0 ≤ T) {W : Finset ℝ} (hW : IsSeparated 1 W)
    (hWa : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) : (W.card : ℝ) ≤ T + 1 := by
  have h1 : W.card ≤ (Finset.range (⌊T⌋₊ + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun t => ⌊t - a⌋₊) (fun t ht => ?_) ?_
    · have := hWa t ht
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.floor_le_floor (by linarith [this.2]))
    · intro t ht t' ht' he
      by_contra hne
      have hs := hW t ht t' ht' hne
      have h0 := (hWa t ht).1
      have h0' := (hWa t' ht').1
      have e1 := Nat.floor_le (show 0 ≤ t - a by linarith)
      have e2 := Nat.lt_floor_add_one (t - a)
      have e3 := Nat.floor_le (show 0 ≤ t' - a by linarith)
      have e4 := Nat.lt_floor_add_one (t' - a)
      simp only at he
      rw [he] at e1 e2
      rcases le_abs'.1 hs with hs | hs
      · linarith
      · linarith
  rw [Finset.card_range] at h1
  calc (W.card : ℝ) ≤ ((⌊T⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ T + 1 := by push_cast; linarith [Nat.floor_le hT]

end GuthMaynard.P101.Part1
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias card_le_of_sep := GuthMaynard.P101.Part1.card_le_of_sep

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part1
open GuthMaynard GuthMaynard.P101 MeasureTheory Complex Set
open scoped Real
/-! ## Helpers for `box_trunc` -/
/-- `h(z) = 1/z²` (`= 0` at `z = 0`). -/
noncomputable def hz (z : ℤ) : ℝ := 1 / (z : ℝ) ^ 2

/-- `h'(m) = ∏ᵢ 1/mᵢ²`. -/
noncomputable def hm (m : Fin 3 → ℤ) : ℝ := hz (m 0) * hz (m 1) * hz (m 2)

theorem hz_nonneg (z : ℤ) : 0 ≤ hz z := by unfold hz; positivity

theorem hm_nonneg (m : Fin 3 → ℤ) : 0 ≤ hm m := by
  unfold hm; exact mul_nonneg (mul_nonneg (hz_nonneg _) (hz_nonneg _)) (hz_nonneg _)

/-- `ℤ³ ≃ (Fin 3 → ℤ)`. -/
def e3 : ℤ × ℤ × ℤ ≃ (Fin 3 → ℤ) where
  toFun x := ![x.1, x.2.1, x.2.2]
  invFun m := (m 0, m 1, m 2)
  left_inv _ := rfl
  right_inv m := by funext i; fin_cases i <;> rfl

theorem summable_hm : Summable hm := by
  have h1 : Summable hz := by
    have := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
    exact this
  have h2 : Summable fun p : ℤ × ℤ => hz p.1 * hz p.2 :=
    h1.mul_of_nonneg h1 hz_nonneg hz_nonneg
  have h3 : Summable fun x : ℤ × ℤ × ℤ => hz x.1 * (hz x.2.1 * hz x.2.2) :=
    h1.mul_of_nonneg h2 hz_nonneg (fun p => mul_nonneg (hz_nonneg _) (hz_nonneg _))
  refine e3.summable_iff.1 ?_
  convert h3 using 1
  funext x
  exact mul_assoc _ _ _

/-- `‖I_m‖ ≤ N³ |W|³ b₀ b₁ b₂` from per-coordinate bounds. -/
theorem norm_Iterm_le_prod {w : ℝ → ℝ} (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) (T : ℝ)
    (hW : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) (b : Fin 3 → ℝ)
    (hb : ∀ i d, |d| ≤ T → ‖hHat w d ((m i : ℝ) * N)‖ ≤ b i) :
    ‖Iterm w N W m‖ ≤ (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 * (b 0 * b 1 * b 2)) := by
  unfold Iterm
  rw [norm_mul, show ‖(N : ℂ) ^ 3‖ = (N : ℝ) ^ 3 by simp]
  gcongr
  calc _ ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, b 0 * b 1 * b 2 := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₁ h₁ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₂ h₂ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₃ h₃ => ?_)
        have a0 := hb 0 _ (hW t₁ h₁ t₂ h₂)
        have a1 := hb 1 _ (hW t₂ h₂ t₃ h₃)
        have a2 := hb 2 _ (hW t₃ h₃ t₁ h₁)
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul a0 a1 (norm_nonneg _) ((norm_nonneg _).trans a0)) a2
          (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans a0) ((norm_nonneg _).trans a1))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Per-coordinate decay: `‖ĥ_d(zN)‖ ≤ B/z²`, and `≤ E/z²` when `|z| > L`. -/
theorem coord_le {w : ℝ → ℝ} {A2 Ak : ℝ} (n : ℕ) (hA2 : 0 ≤ A2) (hAk : 0 ≤ Ak)
    (h2 : ∀ t ξ : ℝ, ξ ≠ 0 → ‖hHat w t ξ‖ * |ξ| ^ 2 ≤ A2 * (1 + |t|) ^ 2)
    (hk : ∀ t ξ : ℝ, ξ ≠ 0 → ‖hHat w t ξ‖ * |ξ| ^ (n + 2) ≤ Ak * (1 + |t|) ^ (n + 2))
    {T L : ℝ} (hL : 0 < L) {N : ℕ} (hN : 1 ≤ (N : ℝ)) {d : ℝ} (hd : |d| ≤ T) {z : ℤ}
    (hz0 : z ≠ 0) :
    ‖hHat w d ((z : ℝ) * N)‖ ≤ A2 * (1 + T) ^ 2 / (N : ℝ) ^ 2 * hz z ∧
      (L < |(z : ℝ)| →
        ‖hHat w d ((z : ℝ) * N)‖ ≤ Ak * (1 + T) ^ (n + 2) / ((N : ℝ) ^ (n + 2) * L ^ n) * hz z) := by
  have hz' : (z : ℝ) ≠ 0 := by exact_mod_cast hz0
  have hN0 : (0 : ℝ) < N := by linarith
  have hξ : (z : ℝ) * N ≠ 0 := mul_ne_zero hz' hN0.ne'
  have habs : |(z : ℝ) * N| = |(z : ℝ)| * N := by rw [abs_mul, abs_of_pos hN0]
  have hza : 0 < |(z : ℝ)| := abs_pos.2 hz'
  have ht : (1 + |d|) ≤ 1 + T := by linarith
  have h0 : 0 ≤ 1 + |d| := by positivity
  refine ⟨?_, fun hzL => ?_⟩
  · have e := (h2 d _ hξ).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 ht 2) hA2)
    rw [habs] at e
    have : A2 * (1 + T) ^ 2 / (N : ℝ) ^ 2 * hz z = A2 * (1 + T) ^ 2 / (|(z : ℝ)| * N) ^ 2 := by
      unfold hz; rw [mul_pow, sq_abs]; field_simp
    rw [this, le_div_iff₀ (by positivity)]
    exact e
  · have e := (hk d _ hξ).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 ht _) hAk)
    rw [habs] at e
    have hp : (N : ℝ) ^ (n + 2) * L ^ n * (z : ℝ) ^ 2 ≤ (|(z : ℝ)| * N) ^ (n + 2) := by
      rw [← sq_abs (z : ℝ)]
      have : L ^ n ≤ |(z : ℝ)| ^ n := pow_le_pow_left₀ hL.le hzL.le n
      calc (N : ℝ) ^ (n + 2) * L ^ n * |(z : ℝ)| ^ 2
          ≤ (N : ℝ) ^ (n + 2) * |(z : ℝ)| ^ n * |(z : ℝ)| ^ 2 := by gcongr
        _ = _ := by ring
    have : Ak * (1 + T) ^ (n + 2) / ((N : ℝ) ^ (n + 2) * L ^ n) * hz z =
        Ak * (1 + T) ^ (n + 2) / ((N : ℝ) ^ (n + 2) * L ^ n * (z : ℝ) ^ 2) := by
      unfold hz; field_simp
    rw [this, le_div_iff₀ (by positivity)]
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans e

theorem mem_P_ne {m : Fin 3 → ℤ} (h : (Finset.univ.filter fun i => m i ≠ 0).card = 3) (i : Fin 3) :
    m i ≠ 0 :=
  Finset.filter_card_eq (by simpa using h) i (Finset.mem_univ _)

theorem exists_gt_of_notMem_box {L : ℝ} {m : Fin 3 → ℤ} (hm : ∀ i, m i ≠ 0) (hb : m ∉ box L) :
    ∃ i, L < |(m i : ℝ)| := by
  by_contra hc
  simp only [not_exists, not_lt] at hc
  apply hb
  simp only [box, Fintype.mem_piFinset, Finset.mem_erase, Finset.mem_Icc]
  intro i
  have := abs_le.1 (hc i)
  refine ⟨hm i, ?_, Int.le_floor.2 this.2⟩
  have : (-(m i) : ℤ) ≤ ⌊L⌋ := Int.le_floor.2 (by push_cast; linarith)
  omega

/-- P1. Summability of `I_m` on `{m : all mᵢ ≠ 0}` and the tail bound outside `box L`, with
`L = T^{1+η}/N`: each `|I_m| ≤ N³|W|³ ∏ᵢ min(A, A(1+T)^k/(|mᵢ|N)^k)`, and one coordinate
exceeds `L`, so the tail is `≪ N³|W|³ T^{1/2} L (2T^{-η})^k`; take `kη` large and use
`|W| ≤ T + 1`. -/
theorem box_trunc {w : ℝ → ℝ} (hw : IsWeight w) (η : ℝ) (hη : 0 < η) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ, T ^ (3 / 4 : ℝ) ≤ N → (N : ℝ) ≤ T →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 3 w N W‖ ≤ ∑ m ∈ box (T ^ (1 + η) / N), ‖Iterm w N W m‖ +
        T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) := by
  obtain ⟨A2, hA2, hA2'⟩ := hHat_bound hw 2
  obtain ⟨Ak, hAk, hAk'⟩ := hHat_bound hw (⌈7 / η⌉₊ + 2)
  set n : ℕ := ⌈7 / η⌉₊ with hndef
  have hn : 7 ≤ η * n := by
    have := Nat.le_ceil (7 / η)
    rw [div_le_iff₀ hη] at this
    linarith
  have h2 : ∀ t ξ : ℝ, ξ ≠ 0 → ‖hHat w t ξ‖ * |ξ| ^ 2 ≤ A2 * (1 + |t|) ^ 2 :=
    fun t ξ hξ => (hA2' t ξ).2 hξ
  have hk : ∀ t ξ : ℝ, ξ ≠ 0 → ‖hHat w t ξ‖ * |ξ| ^ (n + 2) ≤ Ak * (1 + |t|) ^ (n + 2) :=
    fun t ξ hξ => (hAk' t ξ).2 hξ
  set D := ∑' m, hm m with hDdef
  have hD : 0 ≤ D := tsum_nonneg hm_nonneg
  set c := Ak * A2 ^ 2 * 2 ^ (n + 6) with hcdef
  have hc : 0 ≤ c := by positivity
  refine ⟨max 1 (4 * c * D), fun T hT N hNT _ W a hW hWa => ?_⟩
  have hT1 : 1 ≤ T := le_of_max_le_left hT
  have hT0 : 0 < T := by linarith
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_rpow hT1 (by norm_num)).trans hNT
  have hN0 : (0 : ℝ) < N := by linarith
  set Q := T ^ η with hQ
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hT0 η
  have hQn : T ^ 7 ≤ Q ^ n := by
    rw [hQ, ← Real.rpow_mul_natCast hT0.le, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith)
  set L := T ^ (1 + η) / N with hL
  have hLe : L = T * Q / N := by rw [hL, Real.rpow_add hT0, Real.rpow_one]
  have hL0 : 0 < L := by rw [hLe]; positivity
  set B := A2 * (1 + T) ^ 2 / (N : ℝ) ^ 2 with hBdef
  set E := Ak * (1 + T) ^ (n + 2) / ((N : ℝ) ^ (n + 2) * L ^ n) with hEdef
  have hB : 0 ≤ B := by positivity
  have hE : 0 ≤ E := by positivity
  have hWd : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T := by
    intro t ht t' ht'
    have e1 := hWa t ht
    have e2 := hWa t' ht'
    rw [abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  set P : Set (Fin 3 → ℤ) := {m | (Finset.univ.filter fun i => m i ≠ 0).card = 3} with hPdef
  set u : (Fin 3 → ℤ) → ℝ := fun m => if m ∈ box L then ‖Iterm w N W m‖ else 0 with hudef
  set C := (N : ℝ) ^ 3 * ((W.card : ℝ) ^ 3 * (E * B ^ 2)) with hCdef
  have hC : 0 ≤ C := by positivity
  have hpt : ∀ m, ‖P.indicator (Iterm w N W) m‖ ≤ u m + C * hm m := by
    intro m
    have hu0 : 0 ≤ u m := by
      simp only [hudef]; split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    by_cases hmP : m ∈ P
    · rw [Set.indicator_of_mem hmP]
      have hne := mem_P_ne hmP
      by_cases hb : m ∈ box L
      · simp only [hudef, if_pos hb]
        linarith [mul_nonneg hC (hm_nonneg m)]
      · simp only [hudef, if_neg hb, zero_add]
        obtain ⟨i, hi⟩ := exists_gt_of_notMem_box hne hb
        let b : Fin 3 → ℝ := fun j => if j = i then E * hz (m j) else B * hz (m j)
        have hbnd := norm_Iterm_le_prod (w := w) N W m T hWd b (fun j d hd => by
          have hcj := coord_le n hA2 hAk h2 hk hL0 hN1 hd (hne j)
          simp only [b]
          split_ifs with hji
          · subst hji; exact hcj.2 hi
          · exact hcj.1)
        refine hbnd.trans (le_of_eq ?_)
        simp only [hCdef, hm, b]
        fin_cases i <;> simp <;> ring
    · rw [Set.indicator_of_notMem hmP, norm_zero]
      exact add_nonneg hu0 (mul_nonneg hC (hm_nonneg m))
  have hsu : Summable u :=
    summable_of_ne_finset_zero (s := box L) (fun m hmb => by simp only [hudef, if_neg hmb])
  have hsv : Summable fun m => C * hm m := summable_hm.mul_left C
  have hsF : Summable fun m => ‖P.indicator (Iterm w N W) m‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsu.add hsv)
  have hS : S 3 w N W = ∑' m, P.indicator (Iterm w N W) m := tsum_subtype P _
  have htu : ∑' m, u m = ∑ m ∈ box L, ‖Iterm w N W m‖ := by
    rw [tsum_eq_sum (s := box L) (fun m hmb => by simp only [hudef, if_neg hmb])]
    exact Finset.sum_congr rfl fun m hmb => by simp only [hudef, if_pos hmb]
  -- the tail
  have hX : (N : ℝ) ^ 3 * (E * B ^ 2) ≤ c / T := by
    have e1 : (N : ℝ) ^ 3 * (E * B ^ 2) =
        Ak * A2 ^ 2 * (1 + T) ^ (n + 6) / ((N : ℝ) ^ 3 * (T * Q) ^ n) := by
      have hNL : (N : ℝ) ^ (n + 2) * L ^ n = (N : ℝ) ^ 2 * (T * Q) ^ n := by
        rw [show T * Q = N * L by rw [hLe]; field_simp, mul_pow, pow_add]; ring
      rw [hEdef, hBdef, hNL]; field_simp; ring
    have e2 : c / T = Ak * A2 ^ 2 * (2 * T) ^ (n + 6) / (T ^ n * T ^ 7) := by
      rw [hcdef]; field_simp; ring
    rw [e1, e2]
    apply div_le_div₀ (by positivity) (by gcongr; linarith) (by positivity)
    calc T ^ n * T ^ 7 ≤ 1 * (T ^ n * Q ^ n) := by rw [one_mul]; gcongr
      _ ≤ (N : ℝ) ^ 3 * (T * Q) ^ n := by rw [mul_pow]; gcongr; exact one_le_pow₀ hN1
  have htail : C * D ≤ T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) := by
    by_cases hW0 : W.card = 0
    · rw [show C = 0 by simp [hCdef, hW0], zero_mul]; positivity
    have hW1 : (1 : ℝ) ≤ W.card := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hW0
    have hWc := card_le_of_sep hT0.le hW hWa
    have hpow : (W.card : ℝ) ^ 3 = (W.card : ℝ) ^ (3 / 2 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add (by positivity)]; norm_num
    have h32 : (W.card : ℝ) ^ (3 / 2 : ℝ) ≤ 4 * T ^ 2 := by
      calc _ ≤ (W.card : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num)
        _ = (W.card : ℝ) ^ 2 := Real.rpow_two _
        _ ≤ (2 * T) ^ 2 := by gcongr; linarith
        _ = 4 * T ^ 2 := by ring
    calc C * D = ((N : ℝ) ^ 3 * (E * B ^ 2)) * D * (W.card : ℝ) ^ 3 := by rw [hCdef]; ring
      _ ≤ (c / T) * D * ((W.card : ℝ) ^ (3 / 2 : ℝ) * (4 * T ^ 2)) := by
          rw [hpow]; gcongr
      _ = (4 * c * D / T) * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ)) := by ring
      _ ≤ 1 * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ)) := by
          gcongr; exact (div_le_one hT0).2 (le_of_max_le_right hT)
      _ = _ := one_mul _
  calc ‖S 3 w N W‖ ≤ ∑' m, ‖P.indicator (Iterm w N W) m‖ := by
        rw [hS]; exact norm_tsum_le_tsum_norm hsF
    _ ≤ ∑' m, (u m + C * hm m) := hsF.tsum_le_tsum hpt (hsu.add hsv)
    _ = ∑ m ∈ box L, ‖Iterm w N W m‖ + C * D := by
        rw [hsu.tsum_add hsv, htu, tsum_mul_left]
    _ ≤ _ := by gcongr

end GuthMaynard.P101.Part1
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias box_trunc := GuthMaynard.P101.Part1.box_trunc

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part2
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal
/-- `conj ĥ_t(ξ) = ĥ_{-t}(-ξ)`. -/
theorem conj_hHat {w : ℝ → ℝ} (hw : IsWeight w) (t ξ : ℝ) :
    (starRingEnd ℂ) (hHat w t ξ) = hHat w (-t) (-ξ) := by
  unfold hHat
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj]
  congr 1; funext u
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
  by_cases hu : 0 < u
  · have hc := Complex.conj_cpow (u : ℂ) ((t : ℂ) * I)
      (by rw [Complex.arg_ofReal_of_nonneg hu.le]; exact Real.pi_ne_zero.symm)
    rw [Complex.conj_ofReal] at hc
    rw [← Complex.exp_conj, hc]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
    push_cast
    ring_nf
  · have : w u = 0 := by
      by_contra h
      exact hu (by linarith [(hw.support_subset h).1])
    simp [this]

/-- Cyclic relabelling of `(t₁, t₂, t₃)`. -/
theorem Iterm_cyc (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) :
    Iterm w N W ![m 1, m 2, m 0] = Iterm w N W m := by
  unfold Iterm
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  ring

end GuthMaynard.P101.Part2
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
/-! ## P2: symmetries -/

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part2
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal
/-- The corrected conjugation identity (the paper's p. 24 has `conj I_{(m₂,m₁,m₃)}`):
`conj ĥ_t(ξ) = ĥ_{-t}(-ξ)` (`GuthMaynard.S2.hHat_neg`) and `(t₁,t₂,t₃) ↦ (t₁,t₃,t₂)`. -/
theorem conj_Iterm {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) :
    (starRingEnd ℂ) (Iterm w N W m) = Iterm w N W ![-m 0, -m 2, -m 1] := by
  unfold Iterm
  simp only [map_mul, map_pow, Complex.conj_natCast, map_sum, conj_hHat hw,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  simp only [neg_sub, Int.cast_neg, neg_mul]
  ring

end GuthMaynard.P101.Part2
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part2
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal
/-- Signed coordinate permutations `m ↦ (ε m_{σ 0}, ε m_{σ 1}, ε m_{σ 2})`. -/
def gmap (p : ℤ × (Fin 3 → Fin 3)) (m : Fin 3 → ℤ) : Fin 3 → ℤ := fun i => p.1 * m (p.2 i)

/-- The six sign-normalized permutations. -/
def P6 : Fin 6 → ℤ × (Fin 3 → Fin 3) :=
  ![(1, ![0, 1, 2]), (1, ![1, 2, 0]), (1, ![2, 0, 1]), (-1, ![0, 2, 1]), (-1, ![1, 0, 2]),
    (-1, ![2, 1, 0])]

theorem P6_sign (k : Fin 6) : (P6 k).1 = 1 ∨ (P6 k).1 = -1 := by
  fin_cases k <;> simp [P6]

theorem P6_surj (k : Fin 6) : Function.Surjective (P6 k).2 := by
  fin_cases k <;> decide

theorem gmap_inj (k : Fin 6) : Function.Injective (gmap (P6 k)) := by
  intro a b h
  funext i
  obtain ⟨j, rfl⟩ := P6_surj k i
  have h1 := congrFun h j
  simp only [gmap] at h1
  rcases P6_sign k with h2 | h2 <;> rw [h2] at h1 <;> linarith

theorem norm_Iterm_gmap {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (W : Finset ℝ) (k : Fin 6)
    (m : Fin 3 → ℤ) : ‖Iterm w N W (gmap (P6 k) m)‖ = ‖Iterm w N W m‖ := by
  have c1 := Iterm_cyc w N W m
  have c2 := Iterm_cyc w N W ![m 1, m 2, m 0]
  have d0 := conj_Iterm hw N W m
  have d1 := conj_Iterm hw N W ![m 1, m 2, m 0]
  have d2 := conj_Iterm hw N W ![m 2, m 0, m 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at c1 c2 d0 d1 d2
  have ev : ∀ v : Fin 3 → ℤ, v = ![v 0, v 1, v 2] := fun v => by
    funext i; fin_cases i <;> rfl
  fin_cases k
  · rw [ev (gmap _ m)]; simp [gmap, P6, ← ev m]
  · rw [ev (gmap _ m)]; simp [gmap, P6, c1]
  · rw [ev (gmap _ m)]; simp [gmap, P6, c2, c1]
  · rw [ev (gmap _ m)]; simp [gmap, P6, ← d0]
  · rw [ev (gmap _ m)]; simp [gmap, P6, ← d1, c1]
  · rw [ev (gmap _ m)]; simp [gmap, P6, ← d2, c2, c1]

theorem gmap_mem_box (L : ℝ) (k : Fin 6) {m : Fin 3 → ℤ} (hm : m ∈ box L) :
    gmap (P6 k) m ∈ box L := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_erase, Finset.mem_Icc] at hm ⊢
  intro i
  obtain ⟨h1, h2, h3⟩ := hm ((P6 k).2 i)
  simp only [gmap]
  rcases P6_sign k with h | h <;> rw [h] <;> refine ⟨?_, ?_, ?_⟩ <;> omega

theorem abs_gmap (k : Fin 6) (m : Fin 3 → ℤ) (i : Fin 3) :
    |gmap (P6 k) m i| = |m ((P6 k).2 i)| := by
  simp only [gmap]
  rcases P6_sign k with h | h <;> rw [h] <;> simp

theorem exists_ord (m : Fin 3 → ℤ) : ∃ k : Fin 6,
    |gmap (P6 k) m 0| ≤ |gmap (P6 k) m 1| ∧ |gmap (P6 k) m 1| ≤ |gmap (P6 k) m 2| := by
  simp only [abs_gmap]
  have h : (|m 0| ≤ |m 1| ∧ |m 1| ≤ |m 2|) ∨ (|m 1| ≤ |m 2| ∧ |m 2| ≤ |m 0|) ∨
      (|m 2| ≤ |m 0| ∧ |m 0| ≤ |m 1|) ∨ (|m 0| ≤ |m 2| ∧ |m 2| ≤ |m 1|) ∨
      (|m 1| ≤ |m 0| ∧ |m 0| ≤ |m 2|) ∨ (|m 2| ≤ |m 1| ∧ |m 1| ≤ |m 0|) := by omega
  rcases h with h | h | h | h | h | h
  · exact ⟨0, by simpa [P6] using h⟩
  · exact ⟨1, by simpa [P6] using h⟩
  · exact ⟨2, by simpa [P6] using h⟩
  · exact ⟨3, by simpa [P6] using h⟩
  · exact ⟨4, by simpa [P6] using h⟩
  · exact ⟨5, by simpa [P6] using h⟩

theorem sum_ite_gmap_le (k : Fin 6) (s t : Finset (Fin 3 → ℤ)) (f : (Fin 3 → ℤ) → ℝ)
    (hf : ∀ m, 0 ≤ f m) :
    ∑ m ∈ s, (if gmap (P6 k) m ∈ t then f (gmap (P6 k) m) else 0) ≤ ∑ n ∈ t, f n := by
  rw [← Finset.sum_filter,
    ← Finset.sum_image (f := f) (fun a _ b _ h => gmap_inj k h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => hf n
  intro n hn
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hn
  exact (Finset.mem_filter.1 ha).2

/-- P2. `|I_m| = |I_{sgn(σ) σ m}|` for every permutation `σ`; the box is symmetric, so sorting
`|m|` is an at most `6`-to-`1` map onto the ordered box. -/
theorem sum_box_le {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (W : Finset ℝ) (L : ℝ) :
    ∑ m ∈ box L, ‖Iterm w N W m‖ ≤ 6 * ∑ m ∈ ordBox L, ‖Iterm w N W m‖ := by
  set f : (Fin 3 → ℤ) → ℝ := fun m => ‖Iterm w N W m‖ with hf
  have step : ∀ m ∈ box L, f m ≤
      ∑ k : Fin 6, (if gmap (P6 k) m ∈ ordBox L then f (gmap (P6 k) m) else 0) := by
    intro m hm
    obtain ⟨k, hk⟩ := exists_ord m
    have hmem : gmap (P6 k) m ∈ ordBox L :=
      Finset.mem_filter.2 ⟨gmap_mem_box L k hm, hk⟩
    have h1 : f m = (if gmap (P6 k) m ∈ ordBox L then f (gmap (P6 k) m) else 0) := by
      rw [if_pos hmem, hf]; exact (norm_Iterm_gmap hw N W k m).symm
    rw [h1]
    exact Finset.single_le_sum (f := fun k : Fin 6 =>
      (if gmap (P6 k) m ∈ ordBox L then f (gmap (P6 k) m) else 0))
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ k)
  calc ∑ m ∈ box L, f m
      ≤ ∑ m ∈ box L, ∑ k : Fin 6,
          (if gmap (P6 k) m ∈ ordBox L then f (gmap (P6 k) m) else 0) :=
        Finset.sum_le_sum step
    _ = ∑ k : Fin 6, ∑ m ∈ box L,
          (if gmap (P6 k) m ∈ ordBox L then f (gmap (P6 k) m) else 0) := Finset.sum_comm
    _ ≤ ∑ _k : Fin 6, ∑ n ∈ ordBox L, f n :=
        Finset.sum_le_sum fun k _ => sum_ite_gmap_le k _ _ f fun m => norm_nonneg _
    _ = 6 * ∑ n ∈ ordBox L, f n := by simp

end GuthMaynard.P101.Part2
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias sum_box_le := GuthMaynard.P101.Part2.sum_box_le

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part3
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex Set
open scoped Real
/-! ## `Kfun_le` -/
/-- Uniform bounds on the first `k` derivatives. -/
def BddUpTo (k : ℕ) (B : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B

theorem BddUpTo.nonneg {k : ℕ} {B : ℝ} {f : ℝ → ℂ} (h : BddUpTo k B f) : 0 ≤ B :=
  (norm_nonneg _).trans (h 0 (Nat.zero_le _) 0)

theorem bdd_of_cs {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) :
    ∀ k : ℕ, ∃ B, BddUpTo k B f := by
  have hj : ∀ j : ℕ, ∃ B, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B := fun j =>
    (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hcs.iteratedFDeriv j)
  intro k
  induction k with
  | zero =>
    obtain ⟨B, hB⟩ := hj 0
    exact ⟨B, fun j hj x => by rw [Nat.le_zero.1 hj]; exact hB x⟩
  | succ k ih =>
    obtain ⟨B, hB⟩ := ih
    obtain ⟨B', hB'⟩ := hj (k + 1)
    refine ⟨max B B', fun j hj x => ?_⟩
    rcases Nat.lt_or_eq_of_le hj with h | h
    · exact (hB j (Nat.lt_succ_iff.1 h) x).trans (le_max_left _ _)
    · subst h; exact (hB' x).trans (le_max_right _ _)

theorem bdd_mul {k : ℕ} {B₁ B₂ : ℝ} {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (h₁ : BddUpTo k B₁ f) (h₂ : BddUpTo k B₂ g) :
    BddUpTo k (2 ^ k * B₁ * B₂) (fun x => f x * g x) := by
  intro j hj x
  have hB₁ := h₁.nonneg
  have hB₂ := h₂.nonneg
  refine (norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
          ‖iteratedFDeriv ℝ (j - i) g x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B₁ * B₂ := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          gcongr
          · exact h₁ i (hi'.trans hj) x
          · exact h₂ (j - i) ((Nat.sub_le _ _).trans hj) x
    _ = 2 ^ j * B₁ * B₂ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ k * B₁ * B₂ := by
          gcongr
          · norm_num

theorem bdd_scale {k : ℕ} {B : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (h : BddUpTo k B f) {c : ℝ} (hc : |c| ≤ 2) :
    BddUpTo k (2 ^ k * B) (fun x => f (c * x)) := by
  intro j hj x
  have hB := h.nonneg
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_comp_const_smul (hf.of_le (by exact_mod_cast le_top)) c, norm_smul,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_pow, Real.norm_eq_abs]
  calc |c| ^ j * ‖iteratedFDeriv ℝ j f (c * x)‖ ≤ 2 ^ j * B := by
        gcongr
        exact h j hj _
    _ ≤ 2 ^ k * B := by gcongr; norm_num

theorem norm_fourier_le_integral (F : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 F ξ‖ ≤ ∫ u, ‖F u‖ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem iteratedDeriv_eq_zero_of_notMem {f : ℝ → ℂ} (hs : tsupport f ⊆ Icc (1 : ℝ) 2)
    (j : ℕ) {x : ℝ} (hx : x ∉ Icc (1 : ℝ) 2) : iteratedDeriv j f x = 0 := by
  have h0 : iteratedFDeriv ℝ j f x = 0 := by
    by_contra hne
    exact hx (hs (support_iteratedFDeriv_subset j (Function.mem_support.2 hne)))
  rw [iteratedDeriv_eq_iteratedFDeriv, h0]
  rfl

theorem integral_norm_iteratedDeriv_le {k : ℕ} {B : ℝ} {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : tsupport f ⊆ Icc (1 : ℝ) 2) (h : BddUpTo k B f)
    {j : ℕ} (hj : j ≤ k) : ∫ u, ‖iteratedDeriv j f u‖ ≤ B := by
  have hc : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j (by exact_mod_cast le_top)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1 : ℝ) 2)
    (fun x hx => by rw [iteratedDeriv_eq_zero_of_notMem hs j hx, norm_zero])]
  calc ∫ u in Icc (1 : ℝ) 2, ‖iteratedDeriv j f u‖ ≤ ∫ u in Icc (1 : ℝ) 2, B := by
        refine setIntegral_mono_on hc.norm.integrableOn_Icc (integrableOn_const ?_ ?_)
          measurableSet_Icc fun x _ => ?_
        · simp
        · simp
        · rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact h j hj x
    _ = B := by simp; norm_num

theorem fourier_bound {k : ℕ} {B : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : tsupport f ⊆ Icc (1 : ℝ) 2) (h : BddUpTo k B f) (ξ : ℝ) :
    ‖𝓕 f ξ‖ ≤ B ∧ ‖𝓕 f ξ‖ * |ξ| ^ k ≤ B := by
  have hint : ∀ n : ℕ, Integrable (iteratedDeriv n f) := fun n =>
    (hf.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_Icc fun x hx => iteratedDeriv_eq_zero_of_notMem hs n hx)
  constructor
  · refine (norm_fourier_le_integral f ξ).trans ?_
    have := integral_norm_iteratedDeriv_le hf hs h (Nat.zero_le k)
    simpa using this
  · have hF := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (n := k) hf (fun n _ => hint n)
      (by exact_mod_cast le_top)
    have h1 := norm_fourier_le_integral (iteratedDeriv k f) ξ
    rw [hF, norm_smul, norm_pow] at h1
    have h2 := integral_norm_iteratedDeriv_le hf hs h le_rfl
    have hn : ‖(2 * π * I * ξ : ℂ)‖ = 2 * π * |ξ| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I]
      simp [abs_of_pos Real.pi_pos]
    rw [hn] at h1
    have hpi : |ξ| ^ k ≤ (2 * π * |ξ|) ^ k := by
      gcongr
      have := Real.pi_gt_three
      nlinarith [abs_nonneg ξ]
    calc ‖𝓕 f ξ‖ * |ξ| ^ k ≤ (2 * π * |ξ|) ^ k * ‖𝓕 f ξ‖ := by
          rw [mul_comm]; gcongr
      _ ≤ B := h1.trans h2

/-- `u ↦ w(u)²` as a complex function. -/
noncomputable def hc (w : ℝ → ℝ) (u : ℝ) : ℂ := ((w u ^ 2 : ℝ) : ℂ)

/-- `u ↦ u² w(u)²` as a complex function. -/
noncomputable def h0c (w : ℝ → ℝ) (u : ℝ) : ℂ := ((u ^ 2 * w u ^ 2 : ℝ) : ℂ)

theorem w_eq_zero {w : ℝ → ℝ} (hw : IsWeight w) {x : ℝ} (hx : x ∉ Icc (1 : ℝ) 2) : w x = 0 := by
  by_contra h; exact hx (hw.support_subset (Function.mem_support.2 h))

theorem tsupport_sub {f : ℝ → ℂ}
    (hf : ∀ x, x ∉ Icc (1 : ℝ) 2 → f x = 0) : tsupport f ⊆ Icc (1 : ℝ) 2 :=
  closure_minimal (fun x hx => by_contra fun h => hx (hf x h)) isClosed_Icc

theorem hc_smooth {w : ℝ → ℝ} (hw : IsWeight w) : ContDiff ℝ (⊤ : ℕ∞) (hc w) :=
  Complex.ofRealCLM.contDiff.comp (hw.smooth.pow 2)

theorem h0c_smooth {w : ℝ → ℝ} (hw : IsWeight w) : ContDiff ℝ (⊤ : ℕ∞) (h0c w) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_id.pow 2).mul (hw.smooth.pow 2))

theorem Kfun_le {w : ℝ → ℝ} (hw : IsWeight w) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ) (m : Fin 3 → ℤ) (v₁ v₂ : ℝ), v₁ ∈ Set.Icc (1 / 2 : ℝ) 2 →
      v₂ ∈ Set.Icc (1 / 2 : ℝ) 2 →
      ‖Kfun w N m v₁ v₂‖ ≤ A ∧ ‖Kfun w N m v₁ v₂‖ * ((N : ℝ) * |phase m v₁ v₂|) ^ k ≤ A := by
  obtain ⟨B₀, hB₀⟩ := bdd_of_cs (h0c_smooth hw)
    (HasCompactSupport.intro (isCompact_Icc (a := (1:ℝ)) (b := 2)) fun x hx => by simp [h0c, w_eq_zero hw hx]) k
  obtain ⟨B₁, hB₁⟩ := bdd_of_cs (hc_smooth hw)
    (HasCompactSupport.intro (isCompact_Icc (a := (1:ℝ)) (b := 2)) fun x hx => by simp [hc, w_eq_zero hw hx]) k
  have hB₀n := hB₀.nonneg
  have hB₁n := hB₁.nonneg
  refine ⟨2 ^ k * B₀ * (2 ^ k * (2 ^ k * B₁) * (2 ^ k * B₁)), by positivity, ?_⟩
  intro N m v₁ v₂ hv₁ hv₂
  have habs : ∀ v ∈ Icc (1 / 2 : ℝ) 2, |v| ≤ 2 := fun v hv => by
    rw [abs_le]; constructor <;> linarith [hv.1, hv.2]
  have hs1 : ContDiff ℝ (⊤ : ℕ∞) (fun u => hc w (v₁ * u)) :=
    (hc_smooth hw).comp (contDiff_const.mul contDiff_id)
  have hs2 : ContDiff ℝ (⊤ : ℕ∞) (fun u => hc w (v₂ * u)) :=
    (hc_smooth hw).comp (contDiff_const.mul contDiff_id)
  have hb := bdd_mul (h0c_smooth hw) (hs1.mul hs2) hB₀
    (bdd_mul hs1 hs2 (bdd_scale (hc_smooth hw) hB₁ (habs v₁ hv₁))
      (bdd_scale (hc_smooth hw) hB₁ (habs v₂ hv₂)))
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun u => h0c w u * (hc w (v₁ * u) * hc w (v₂ * u))) :=
    (h0c_smooth hw).mul (hs1.mul hs2)
  have hts : tsupport (fun u => h0c w u * (hc w (v₁ * u) * hc w (v₂ * u))) ⊆ Icc (1 : ℝ) 2 :=
    tsupport_sub fun x hx => by simp [h0c, w_eq_zero hw hx]
  have hK : Kfun w N m v₁ v₂ =
      𝓕 (fun u => h0c w u * (hc w (v₁ * u) * hc w (v₂ * u))) ((N : ℝ) * phase m v₁ v₂) := by
    unfold Kfun h0c hc
    refine congrArg (fun F : ℝ → ℂ => 𝓕 F ((N : ℝ) * phase m v₁ v₂)) ?_
    funext u; push_cast; ring
  obtain ⟨h1, h2⟩ := fourier_bound hsm hts hb ((N : ℝ) * phase m v₁ v₂)
  rw [hK]
  refine ⟨h1, ?_⟩
  rwa [abs_mul, Nat.abs_cast] at h2

/-! ## `norm_Iterm_le`: basic objects -/
/-- `e(-x) = exp(-2πix)`. -/
noncomputable def ex (x : ℝ) : ℂ := Complex.exp (((-2 * π * x : ℝ) : ℂ) * I)

/-- `x^{it}`. -/
noncomputable def cpw (x t : ℝ) : ℂ := (x : ℂ) ^ ((t : ℂ) * I)

theorem Rv_eq (W : Finset ℝ) (v : ℝ) : Rv W v = ∑ t ∈ W, cpw v t := rfl

theorem ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem continuous_ex : Continuous ex := by
  unfold ex; fun_prop

theorem cpw_exp {x : ℝ} (hx : 0 < x) (t : ℝ) :
    cpw x t = Complex.exp ((Real.log x : ℂ) * ((t : ℂ) * I)) := by
  unfold cpw
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), Complex.ofReal_log hx.le]

theorem cpw_sub {x : ℝ} (hx : 0 < x) (a b : ℝ) : cpw x (a - b) = cpw x a / cpw x b := by
  rw [cpw_exp hx, cpw_exp hx, cpw_exp hx, ← Complex.exp_sub]; congr 1; push_cast; ring

theorem cpw_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    cpw (x / y) t = cpw x t / cpw y t := by
  rw [cpw_exp (div_pos hx hy), cpw_exp hx, cpw_exp hy, ← Complex.exp_sub,
    Real.log_div hx.ne' hy.ne']
  congr 1; push_cast; ring

theorem norm_cpw {x : ℝ} (hx : 0 < x) (t : ℝ) : ‖cpw x t‖ = 1 := by
  rw [cpw_exp hx, Complex.norm_exp]; simp

theorem cpw_contAt {x : ℝ} (hx : 0 < x) (t : ℝ) : ContinuousAt (fun v => cpw v t) x := by
  unfold cpw
  exact (Complex.continuous_ofReal.continuousAt).cpow continuousAt_const
    (Complex.ofReal_mem_slitPlane.2 hx)

theorem Rv_contAt (W : Finset ℝ) {v : ℝ} (hv : 0 < v) : ContinuousAt (Rv W) v := by
  have : Rv W = fun v => ∑ t ∈ W, cpw v t := rfl
  rw [this]
  exact tendsto_finsetSum _ fun t _ => cpw_contAt hv t

theorem norm_Rv_inv (W : Finset ℝ) {v : ℝ} (hv : 0 < v) : ‖Rv W v⁻¹‖ = ‖Rv W v‖ := by
  have : Rv W v⁻¹ = (starRingEnd ℂ) (Rv W v) := by
    rw [Rv_eq, Rv_eq, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [inv_eq_one_div, cpw_div one_pos hv, cpw_exp one_pos, Real.log_one]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_div]
    exact Complex.inv_eq_conj (norm_cpw hv t)
  rw [this, Complex.norm_conj]

theorem hc_eq_zero {w : ℝ → ℝ} (hw : IsWeight w) {x : ℝ} (hx : x ∉ Icc (1 : ℝ) 2) :
    hc w x = 0 := by simp [hc, w_eq_zero hw hx]

theorem hc_eq_zero_of_nonpos {w : ℝ → ℝ} (hw : IsWeight w) {x : ℝ} (hx : x ≤ 0) :
    hc w x = 0 := hc_eq_zero hw fun h => by linarith [h.1]

theorem h0c_eq {w : ℝ → ℝ} (x : ℝ) : h0c w x = (x : ℂ) ^ 2 * hc w x := by
  simp [h0c, hc]

theorem integrable_of_cont_on {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) {f : X → ℂ} (hf : ContinuousOn f K)
    (hz : ∀ x ∉ K, f x = 0) : Integrable f μ :=
  (integrableOn_iff_integrable_of_support_subset
    (fun x hx => by_contra fun h => hx (hz x h))).1 (hf.integrableOn_compact hK)

theorem hHat_eq' (w : ℝ → ℝ) (t ξ : ℝ) :
    hHat w t ξ = ∫ u, ex (u * ξ) * (hc w u * cpw u t) := by
  unfold hHat
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext u
  simp only [smul_eq_mul, ex, hc, cpw]
  rw [show (-2 * π * u * ξ : ℝ) = -2 * π * (u * ξ) by ring]

theorem integrable_hterm {w : ℝ → ℝ} (hw : IsWeight w) (t ξ : ℝ) :
    Integrable (fun u => ex (u * ξ) * (hc w u * cpw u t)) := by
  refine integrable_of_cont_on (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_ fun x hx => by
    simp [hc_eq_zero hw hx]
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  refine ContinuousAt.continuousWithinAt ?_
  exact (continuous_ex.comp (continuous_id.mul continuous_const)).continuousAt.mul
    ((hc_smooth hw).continuous.continuousAt.mul (cpw_contAt hx0 t))

/-! ## Step A: `I_m` as an integral over `ℝ³` -/
/-- The measure on `ℝ × (ℝ × ℝ)`, points `(u₃, (u₁, u₂))`. -/
noncomputable abbrev μ3 : Measure (ℝ × ℝ × ℝ) := (volume : Measure ℝ).prod (volume.prod volume)

/-- The term for `p = (t₁, t₂, t₃)`. -/
noncomputable def Fterm (w : ℝ → ℝ) (N : ℕ) (m : Fin 3 → ℤ) (p z : ℝ × ℝ × ℝ) : ℂ :=
  (ex (z.1 * (m 2 * N)) * (hc w z.1 * cpw z.1 (p.2.2 - p.1))) *
    ((ex (z.2.1 * (m 0 * N)) * (hc w z.2.1 * cpw z.2.1 (p.1 - p.2.1))) *
      (ex (z.2.2 * (m 1 * N)) * (hc w z.2.2 * cpw z.2.2 (p.2.1 - p.2.2))))

/-- `w₁(u) e(-N m·u) R(u₁/u₃) R(u₂/u₁) R(u₃/u₂)`. -/
noncomputable def Phi1 (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) (z : ℝ × ℝ × ℝ) : ℂ :=
  hc w z.1 * hc w z.2.1 * hc w z.2.2 *
    (ex (z.1 * (m 2 * N)) * ex (z.2.1 * (m 0 * N)) * ex (z.2.2 * (m 1 * N))) *
    (Rv W (z.2.1 / z.1) * Rv W (z.2.2 / z.2.1) * Rv W (z.1 / z.2.2))

theorem Fterm_integrable {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (m : Fin 3 → ℤ)
    (p : ℝ × ℝ × ℝ) : Integrable (Fterm w N m p) μ3 :=
  (integrable_hterm hw _ _).mul_prod ((integrable_hterm hw _ _).mul_prod (integrable_hterm hw _ _))

theorem prod_hHat_eq (w : ℝ → ℝ) (N : ℕ) (m : Fin 3 → ℤ) (p : ℝ × ℝ × ℝ) :
    hHat w (p.1 - p.2.1) (m 0 * N) * hHat w (p.2.1 - p.2.2) (m 1 * N) *
      hHat w (p.2.2 - p.1) (m 2 * N) = ∫ z, Fterm w N m p z ∂μ3 := by
  unfold Fterm
  rw [integral_prod_mul (fun x => ex (x * (m 2 * N)) * (hc w x * cpw x (p.2.2 - p.1)))
    (fun y : ℝ × ℝ => (ex (y.1 * (m 0 * N)) * (hc w y.1 * cpw y.1 (p.1 - p.2.1))) *
      (ex (y.2 * (m 1 * N)) * (hc w y.2 * cpw y.2 (p.2.1 - p.2.2)))),
    integral_prod_mul (fun x => ex (x * (m 0 * N)) * (hc w x * cpw x (p.1 - p.2.1)))
      (fun y => ex (y * (m 1 * N)) * (hc w y * cpw y (p.2.1 - p.2.2))),
    hHat_eq', hHat_eq', hHat_eq']
  ring

theorem Rv_triple (W : Finset ℝ) (a b c : ℝ) :
    Rv W a * Rv W b * Rv W c = ∑ p ∈ W ×ˢ W ×ˢ W, cpw a p.1 * cpw b p.2.1 * cpw c p.2.2 := by
  rw [Finset.sum_product, Rv_eq, Rv_eq, Rv_eq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_product, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]

theorem sum_Fterm_eq {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ)
    (z : ℝ × ℝ × ℝ) : ∑ p ∈ W ×ˢ W ×ˢ W, Fterm w N m p z = Phi1 w N W m z := by
  obtain ⟨u₃, u₁, u₂⟩ := z
  by_cases h : 0 < u₃ ∧ 0 < u₁ ∧ 0 < u₂
  · obtain ⟨h₃, h₁, h₂⟩ := h
    unfold Phi1
    simp only
    rw [Rv_triple, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold Fterm
    simp only
    rw [cpw_sub h₃, cpw_sub h₁, cpw_sub h₂, cpw_div h₁ h₃, cpw_div h₂ h₁, cpw_div h₃ h₂]
    ring
  · have h0 : hc w u₃ * hc w u₁ * hc w u₂ = 0 := by
      simp only [not_and_or, not_lt] at h
      rcases h with h | h | h <;> simp [hc_eq_zero_of_nonpos hw h]
    have hz : Phi1 w N W m (u₃, u₁, u₂) = 0 := by
      unfold Phi1; simp only; rw [h0]; ring
    rw [hz]
    refine Finset.sum_eq_zero fun p _ => ?_
    unfold Fterm; simp only
    linear_combination (ex (u₃ * (m 2 * N)) * cpw u₃ (p.2.2 - p.1) *
      (ex (u₁ * (m 0 * N)) * cpw u₁ (p.1 - p.2.1)) *
      (ex (u₂ * (m 1 * N)) * cpw u₂ (p.2.1 - p.2.2))) * h0

theorem Iterm_eq {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) :
    Iterm w N W m = (N : ℂ) ^ 3 * ∫ z, Phi1 w N W m z ∂μ3 ∧
      Integrable (Phi1 w N W m) μ3 := by
  have hfun : (fun z => ∑ p ∈ W ×ˢ W ×ˢ W, Fterm w N m p z) = Phi1 w N W m :=
    funext (sum_Fterm_eq hw N W m)
  have hint : Integrable (fun z => ∑ p ∈ W ×ˢ W ×ˢ W, Fterm w N m p z) μ3 :=
    integrable_finsetSum _ fun p _ => Fterm_integrable hw N m p
  refine ⟨?_, hfun ▸ hint⟩
  unfold Iterm
  congr 1
  rw [← hfun, integral_finsetSum _ fun p _ => Fterm_integrable hw N m p]
  simp only [← prod_hHat_eq, Finset.sum_product]

/-! ## Step B: the substitution `u₁ = v₁u₃`, `u₂ = v₂u₃` -/
/-- `u₃² w(u₃)² w(v₁u₃)² w(v₂u₃)² e(-N u₃ phase) R(v₁) R(v₂/v₁) R(1/v₂)`, `z = (u₃, (v₁, v₂))`. -/
noncomputable def Psi (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) (z : ℝ × ℝ × ℝ) : ℂ :=
  h0c w z.1 * hc w (z.2.1 * z.1) * hc w (z.2.2 * z.1) * ex (z.1 * (N * phase m z.2.1 z.2.2)) *
    (Rv W z.2.1 * Rv W (z.2.2 / z.2.1) * Rv W z.2.2⁻¹)

theorem Phi1_smul (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) {u : ℝ} (hu : u ≠ 0)
    (q : ℝ × ℝ) : (u : ℂ) ^ 2 * Phi1 w N W m (u, u • q) = Psi w N W m (u, q) := by
  obtain ⟨q₁, q₂⟩ := q
  simp only [Prod.smul_mk, smul_eq_mul]
  unfold Phi1 Psi
  simp only
  rw [mul_div_cancel_left₀ q₁ hu, mul_div_mul_left q₂ q₁ hu, div_mul_cancel_left₀ hu q₂,
    h0c_eq, mul_comm u q₁, mul_comm u q₂,
    show u * (N * phase m q₁ q₂) = u * (m 2 * N) + q₁ * u * (m 0 * N) + q₂ * u * (m 1 * N) by
      unfold phase; ring, ex_add, ex_add]
  ring

theorem inner_eq {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) (u : ℝ) :
    ∫ p, Phi1 w N W m (u, p) ∂(volume.prod volume) =
      ∫ q, Psi w N W m (u, q) ∂(volume.prod volume) := by
  by_cases hu : u ≤ 0
  · have h1 : ∀ p, Phi1 w N W m (u, p) = 0 := fun p => by
      simp [Phi1, hc_eq_zero_of_nonpos hw hu]
    have h2 : ∀ p, Psi w N W m (u, p) = 0 := fun p => by
      simp [Psi, h0c_eq, hc_eq_zero_of_nonpos hw hu]
    simp [h1, h2]
  · have hu0 : u ≠ 0 := by intro h; apply hu; rw [h]
    have h := Measure.integral_comp_smul (μ := (volume : Measure ℝ).prod volume)
      (fun p => Phi1 w N W m (u, p)) u
    simp only [Module.finrank_prod, Module.finrank_self] at h
    have hfun : (fun q => Psi w N W m (u, q)) =
        fun q => (u : ℂ) ^ 2 * Phi1 w N W m (u, u • q) := funext fun q => (Phi1_smul w N W m hu0 q).symm
    rw [hfun, integral_const_mul, h, Complex.real_smul]
    have hpos : 0 < u ^ (1 + 1) := pow_pos (not_le.1 hu) _
    have hu0' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu0
    rw [abs_of_pos (inv_pos.2 hpos), ← mul_assoc]
    have : (u : ℂ) ^ 2 * ((u ^ (1 + 1))⁻¹ : ℝ) = 1 := by
      push_cast
      field_simp
    rw [this, one_mul]

theorem hc_scale_zero {w : ℝ → ℝ} (hw : IsWeight w) {u v : ℝ} (hu : u ∈ Icc (1 : ℝ) 2)
    (hv : v ∉ Icc (1 / 2 : ℝ) 2) : hc w (v * u) = 0 := by
  refine hc_eq_zero hw fun h => hv ⟨?_, ?_⟩
  · by_contra h'; push Not at h'
    rcases le_or_gt v 0 with h0 | h0
    · nlinarith [h.1, hu.1]
    · nlinarith [h.1, hu.2]
  · by_contra h'; push Not at h'
    nlinarith [h.2, hu.1]

/-- The box `[1,2] × [1/2,2]²`. -/
def Bx : Set (ℝ × ℝ × ℝ) := Icc (1 : ℝ) 2 ×ˢ (Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2)

theorem Psi_integrable {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) :
    Integrable (Psi w N W m) μ3 := by
  refine integrable_of_cont_on (K := Bx) (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    ?_ ?_
  · intro z hz
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have hq₁ : 0 < z.2.1 := by linarith [hz2.1]
    have hq₂ : 0 < z.2.2 := by linarith [hz3.1]
    refine ContinuousAt.continuousWithinAt ?_
    have hph : Continuous fun z : ℝ × ℝ × ℝ => z.1 * (N * phase m z.2.1 z.2.2) := by
      unfold phase; fun_prop
    have c1 : ContinuousAt (fun z : ℝ × ℝ × ℝ => Rv W z.2.1) z :=
      (Rv_contAt W hq₁).comp (f := fun z : ℝ × ℝ × ℝ => z.2.1) (by fun_prop)
    have c2 : ContinuousAt (fun z : ℝ × ℝ × ℝ => Rv W (z.2.2 / z.2.1)) z :=
      (Rv_contAt W (div_pos hq₂ hq₁)).comp (f := fun z : ℝ × ℝ × ℝ => z.2.2 / z.2.1)
        ((continuous_snd.snd.continuousAt).div (continuous_snd.fst.continuousAt) hq₁.ne')
    have c3 : ContinuousAt (fun z : ℝ × ℝ × ℝ => Rv W z.2.2⁻¹) z :=
      (Rv_contAt W (inv_pos.2 hq₂)).comp (f := fun z : ℝ × ℝ × ℝ => z.2.2⁻¹)
        ((continuous_snd.snd.continuousAt).inv₀ hq₂.ne')
    have hh0 := (h0c_smooth hw).continuous
    have hh := (hc_smooth hw).continuous
    unfold Psi
    refine ContinuousAt.mul ?_ ((c1.mul c2).mul c3)
    refine ContinuousAt.mul ?_ (continuous_ex.comp hph).continuousAt
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_
    · exact (hh0.comp continuous_fst).continuousAt
    · exact (hh.comp (continuous_snd.fst.mul continuous_fst)).continuousAt
    · exact (hh.comp (continuous_snd.snd.mul continuous_fst)).continuousAt
  · intro z hz
    unfold Psi
    by_cases h1 : z.1 ∈ Icc (1 : ℝ) 2
    · by_cases h2 : z.2.1 ∈ Icc (1 / 2 : ℝ) 2
      · have h3 : z.2.2 ∉ Icc (1 / 2 : ℝ) 2 := fun h3 => hz ⟨h1, h2, h3⟩
        rw [hc_scale_zero hw h1 h3]; ring
      · rw [hc_scale_zero hw h1 h2]; ring
    · rw [h0c_eq, hc_eq_zero hw h1]; ring

theorem Kfun_eq (w : ℝ → ℝ) (N : ℕ) (m : Fin 3 → ℤ) (v₁ v₂ : ℝ) :
    Kfun w N m v₁ v₂ =
      ∫ u, h0c w u * hc w (v₁ * u) * hc w (v₂ * u) * ex (u * (N * phase m v₁ v₂)) := by
  unfold Kfun
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext u
  simp only [smul_eq_mul, ex, h0c, hc]
  rw [show (-2 * π * u * (N * phase m v₁ v₂) : ℝ) = -2 * π * (u * (N * phase m v₁ v₂)) by ring]
  push_cast; ring

theorem Kfun_zero {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (m : Fin 3 → ℤ) {v₁ v₂ : ℝ}
    (h : v₁ ∉ Icc (1 / 2 : ℝ) 2 ∨ v₂ ∉ Icc (1 / 2 : ℝ) 2) : Kfun w N m v₁ v₂ = 0 := by
  rw [Kfun_eq]
  have : ∀ u, h0c w u * hc w (v₁ * u) * hc w (v₂ * u) * ex (u * (N * phase m v₁ v₂)) = 0 := by
    intro u
    by_cases hu : u ∈ Icc (1 : ℝ) 2
    · rcases h with h | h
      · rw [hc_scale_zero hw hu h]; ring
      · rw [hc_scale_zero hw hu h]; ring
    · rw [h0c_eq, hc_eq_zero hw hu]; ring
  simp [this]

/-- The integrand after integrating out `u₃`. -/
noncomputable def Xf (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) (q : ℝ × ℝ) : ℂ :=
  (Rv W q.1 * Rv W (q.2 / q.1) * Rv W q.2⁻¹) * Kfun w N m q.1 q.2

theorem integral_Psi_eq (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) (q : ℝ × ℝ) :
    ∫ u, Psi w N W m (u, q) = Xf w N W m q := by
  unfold Xf Psi
  rw [Kfun_eq, ← integral_const_mul]
  congr 1; funext u
  simp only
  ring

theorem Iterm_eq_X {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) :
    Iterm w N W m = (N : ℂ) ^ 3 * ∫ q, Xf w N W m q ∂(volume.prod volume) ∧
      Integrable (Xf w N W m) (volume.prod volume) := by
  obtain ⟨hI, hΦ⟩ := Iterm_eq hw N W m
  have hΨ := Psi_integrable hw N W m
  have hX : Integrable (Xf w N W m) (volume.prod volume) := by
    have := hΨ.integral_prod_right
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    exact integral_Psi_eq w N W m q
  refine ⟨?_, hX⟩
  rw [hI, integral_prod _ hΦ]
  congr 1
  calc ∫ u, ∫ p, Phi1 w N W m (u, p) ∂(volume.prod volume)
      = ∫ u, ∫ q, Psi w N W m (u, q) ∂(volume.prod volume) :=
        integral_congr_ae (Filter.Eventually.of_forall fun u => inner_eq hw N W m u)
    _ = ∫ q, (∫ u, Psi w N W m (u, q)) ∂(volume.prod volume) :=
        integral_integral_swap (f := fun u q => Psi w N W m (u, q)) hΨ
    _ = ∫ q, Xf w N W m q ∂(volume.prod volume) :=
        integral_congr_ae (Filter.Eventually.of_forall fun q => integral_Psi_eq w N W m q)

/-! ## Step C: norms -/
theorem norm_Iterm_le {w : ℝ → ℝ} (hw : IsWeight w) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) :
    ‖Iterm w N W m‖ ≤ (N : ℝ) ^ 3 * Ifull w N W m := by
  obtain ⟨hI, hX⟩ := Iterm_eq_X hw N W m
  rw [hI, norm_mul, norm_pow, Complex.norm_natCast]
  gcongr
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [integral_prod _ hX.norm]
  unfold Ifull
  rw [← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q₁ => ?_)
  simp only
  by_cases h : q₁ ∈ Icc (1 / 2 : ℝ) 2
  · rw [indicator_of_mem h]
    have hq₁ : 0 < q₁ := by linarith [h.1]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1 / 2 : ℝ) 2)
      (fun q₂ hq₂ => by simp [Xf, Kfun_zero hw N m (Or.inr hq₂)])]
    unfold Kint
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun q₂ hq₂ => ?_
    have hq₂ : 0 < q₂ := by linarith [hq₂.1]
    simp only [Xf, norm_mul]
    rw [norm_Rv_inv W hq₂]
    ring
  · rw [indicator_of_notMem h]
    simp [Xf, Kfun_zero hw N m (Or.inl h)]

end GuthMaynard.P101.Part3
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
/-! ## P3: the integral expansion and the kernel -/
alias norm_Iterm_le := GuthMaynard.P101.Part3.norm_Iterm_le

alias Kfun_le := GuthMaynard.P101.Part3.Kfun_le

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part2
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal
/-! ## P4: dyadic groups -/
theorem two_pow_clog_lt (n : ℕ) (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n < 2 * n := by
  rcases hn.eq_or_lt with h | h
  · subst h; simp
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h2 := Nat.clog_pos (b := 2) (by norm_num) h
    obtain ⟨k, hk⟩ : ∃ k, Nat.clog 2 n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h2).symm⟩
    rw [hk] at h1 ⊢
    rw [pow_succ]
    simp only [Nat.pred_succ] at h1
    omega

theorem two_pow_clog_lt_real (n : ℕ) (hn : 1 ≤ n) : (2 : ℝ) ^ Nat.clog 2 n < 2 * n := by
  exact_mod_cast two_pow_clog_lt n hn

theorem mem_dyadic_clog (n : ℕ) (hn : 1 ≤ n) : (n : ℤ) ∈ dyadic (scale (Nat.clog 2 n)) := by
  have h1 := two_pow_clog_lt_real n hn
  have h2 : (n : ℝ) ≤ 2 ^ Nat.clog 2 n := by exact_mod_cast Nat.le_pow_clog (by norm_num) n
  simp only [dyadic, scale, Finset.mem_Ioc, Int.floor_lt, Int.le_floor]
  push_cast
  constructor <;> linarith

theorem natAbs_le_floor {L : ℝ} {z : ℤ} (hz : z ∈ Finset.Icc (-⌊L⌋) ⌊L⌋) :
    z.natAbs ≤ ⌊L⌋₊ := by
  rw [Finset.mem_Icc] at hz
  apply Nat.le_floor
  have : ((|z| : ℤ) : ℝ) ≤ L := by
    rw [← Int.le_floor]; exact abs_le.2 ⟨by omega, by omega⟩
  rw [Nat.cast_natAbs]; exact this

theorem mem_grp_of (L : ℝ) {m : Fin 3 → ℤ} (hm : m ∈ ordBox L) (hfar : ¬ 5 * |m 1| < |m 2|) :
    m ∈ grp L (Nat.clog 2 (m 0).natAbs) (Nat.clog 2 (m 1).natAbs) ∧
      Nat.clog 2 (m 0).natAbs < nsc L ∧ Nat.clog 2 (m 1).natAbs < nsc L := by
  have hb := (Finset.mem_filter.1 hm).1
  simp only [box, Fintype.mem_piFinset, Finset.mem_erase] at hb
  have hn : ∀ i, 1 ≤ (m i).natAbs := fun i => Int.natAbs_pos.2 (hb i).1
  have hL : ∀ i, (m i).natAbs ≤ ⌊L⌋₊ := fun i => natAbs_le_floor (hb i).2
  refine ⟨Finset.mem_filter.2 ⟨hm, ?_, ?_, by omega⟩, ?_, ?_⟩
  · rw [Int.abs_eq_natAbs]; exact mem_dyadic_clog _ (hn 0)
  · rw [Int.abs_eq_natAbs]; exact mem_dyadic_clog _ (hn 1)
  · exact Nat.lt_succ_of_le (Nat.clog_mono_right 2 (hL 0))
  · exact Nat.lt_succ_of_le (Nat.clog_mono_right 2 (hL 1))

/-- Every ordered non-far `m` lies in exactly one group `grp L i₁ i` with `i, i₁ < nsc L`
(`i = Nat.clog 2 |m₁|`, `i₁ = Nat.clog 2 |m₀|`). -/
theorem sum_ordBox_le (L : ℝ) (hL : 1 ≤ L) (g : (Fin 3 → ℤ) → ℝ) (hg : ∀ m, 0 ≤ g m) :
    ∑ m ∈ ordBox L, g m ≤ ∑ m ∈ far L, g m +
      ∑ i ∈ Finset.range (nsc L), ∑ i₁ ∈ Finset.range (nsc L), ∑ m ∈ grp L i₁ i, g m := by
  set P : ℕ → ℕ → (Fin 3 → ℤ) → Prop := fun i₁ i m =>
    |m 0| ∈ dyadic (scale i₁) ∧ |m 1| ∈ dyadic (scale i) ∧ |m 2| ≤ 5 * |m 1| with hP
  have hgrp : ∀ i₁ i, ∑ m ∈ grp L i₁ i, g m =
      ∑ m ∈ ordBox L, if P i₁ i m then g m else 0 := fun i₁ i => by
    rw [grp, Finset.sum_filter]
  have hfar : ∑ m ∈ far L, g m = ∑ m ∈ ordBox L, if 5 * |m 1| < |m 2| then g m else 0 := by
    rw [far, Finset.sum_filter]
  have hnn : ∀ m i₁ i, 0 ≤ (if P i₁ i m then g m else 0) := fun m i₁ i => by
    split_ifs <;> simp [hg]
  have step : ∀ m ∈ ordBox L, g m ≤ (if 5 * |m 1| < |m 2| then g m else 0) +
      ∑ i ∈ Finset.range (nsc L), ∑ i₁ ∈ Finset.range (nsc L), if P i₁ i m then g m else 0 := by
    intro m hm
    have h0 : 0 ≤ ∑ i ∈ Finset.range (nsc L), ∑ i₁ ∈ Finset.range (nsc L),
        (if P i₁ i m then g m else 0) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i₁ _ => hnn m i₁ i
    by_cases hf : 5 * |m 1| < |m 2|
    · rw [if_pos hf]; linarith
    · rw [if_neg hf, zero_add]
      obtain ⟨hmg, h₁, h⟩ := mem_grp_of L hm hf
      have hPm := (Finset.mem_filter.1 hmg).2
      calc g m = if P (Nat.clog 2 (m 0).natAbs) (Nat.clog 2 (m 1).natAbs) m then g m else 0 :=
            (if_pos hPm).symm
        _ ≤ ∑ i₁ ∈ Finset.range (nsc L),
              (if P i₁ (Nat.clog 2 (m 1).natAbs) m then g m else 0) :=
            Finset.single_le_sum (f := fun i₁ =>
              if P i₁ (Nat.clog 2 (m 1).natAbs) m then g m else 0)
              (fun i₁ _ => hnn m i₁ _) (Finset.mem_range.2 h₁)
        _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ i₁ ∈ Finset.range (nsc L),
              (if P i₁ i m then g m else 0))
              (fun i _ => Finset.sum_nonneg fun i₁ _ => hnn m i₁ i) (Finset.mem_range.2 h)
  calc ∑ m ∈ ordBox L, g m
      ≤ ∑ m ∈ ordBox L, ((if 5 * |m 1| < |m 2| then g m else 0) +
          ∑ i ∈ Finset.range (nsc L), ∑ i₁ ∈ Finset.range (nsc L),
            if P i₁ i m then g m else 0) := Finset.sum_le_sum step
    _ = ∑ m ∈ far L, g m +
        ∑ i ∈ Finset.range (nsc L), ∑ i₁ ∈ Finset.range (nsc L), ∑ m ∈ grp L i₁ i, g m := by
      rw [Finset.sum_add_distrib, hfar, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i₁ _ => (hgrp i₁ i).symm

end GuthMaynard.P101.Part2
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias sum_ordBox_le := GuthMaynard.P101.Part2.sum_ordBox_le

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part2
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal
theorem scale_le (L : ℝ) (hL : 1 ≤ L) (i : ℕ) (hi : i < nsc L) : scale i ≤ L := by
  have hn : 1 ≤ ⌊L⌋₊ := Nat.le_floor (by exact_mod_cast hL)
  have h1 := two_pow_clog_lt_real _ hn
  have h2 : (2 : ℝ) ^ i ≤ 2 ^ Nat.clog 2 ⌊L⌋₊ :=
    pow_le_pow_right₀ (by norm_num) (Nat.lt_succ_iff.1 hi)
  have h3 : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  unfold scale
  linarith

end GuthMaynard.P101.Part2
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias scale_le := GuthMaynard.P101.Part2.scale_le

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part2
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal
theorem card_nsc_le (η : ℝ) (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ L : ℝ, 1 ≤ L → (nsc L : ℝ) ≤ A * L ^ η := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 + 1 / (η * Real.log 2), by positivity, fun L hL => ?_⟩
  have hn : 1 ≤ ⌊L⌋₊ := Nat.le_floor (by exact_mod_cast hL)
  set c := Nat.clog 2 ⌊L⌋₊ with hc
  have h1 := two_pow_clog_lt_real _ hn
  have h3 : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hL0 : 0 < L := by linarith
  have h4 : (2 : ℝ) ^ c ≤ 2 * L := by linarith
  have h5 : (c : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log L := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) hL0.ne']
    exact Real.log_le_log (by positivity) h4
  have h6 : Real.log L ≤ L ^ η / η := Real.log_le_rpow_div hL0.le hη
  have h7 : 1 ≤ L ^ η := Real.one_le_rpow hL hη.le
  have h8 : (c : ℝ) ≤ 1 + L ^ η / (η * Real.log 2) := by
    have : (c : ℝ) * Real.log 2 ≤ Real.log 2 + L ^ η / η := by linarith
    have e : 1 + L ^ η / (η * Real.log 2) = (Real.log 2 + L ^ η / η) / Real.log 2 := by
      field_simp
    rw [e, le_div_iff₀ hl2]
    exact this
  unfold nsc
  push_cast
  rw [← hc]
  have e2 : (2 + 1 / (η * Real.log 2)) * L ^ η = 2 * L ^ η + L ^ η / (η * Real.log 2) := by
    ring
  rw [e2]
  linarith

/-! ## P4: the far terms -/
theorem norm_Rv_le (W : Finset ℝ) {v : ℝ} (hv : 0 < v) : ‖Rv W v‖ ≤ W.card := by
  unfold Rv
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hv]
  simp

theorem one_le_abs_phase {L : ℝ} {m : Fin 3 → ℤ} (hm : m ∈ far L) {v₁ v₂ : ℝ}
    (h₁ : v₁ ∈ Set.Icc (1 / 2 : ℝ) 2) (h₂ : v₂ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    1 ≤ |phase m v₁ v₂| := by
  obtain ⟨hm', h5⟩ := Finset.mem_filter.1 hm
  obtain ⟨-, h01, -⟩ := Finset.mem_filter.1 hm'
  have h5' : 5 * |m 1| + 1 ≤ |m 2| := h5
  have r01 : |(m 0 : ℝ)| ≤ |(m 1 : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast h01
  have r5 : 5 * |(m 1 : ℝ)| + 1 ≤ |(m 2 : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast h5'
  have ha : |(m 0 : ℝ) * v₁| ≤ 2 * |(m 1 : ℝ)| := by
    rw [abs_mul, abs_of_pos (by linarith [h₁.1] : (0 : ℝ) < v₁)]
    nlinarith [abs_nonneg (m 0 : ℝ), h₁.2]
  have hb : |(m 1 : ℝ) * v₂| ≤ 2 * |(m 1 : ℝ)| := by
    rw [abs_mul, abs_of_pos (by linarith [h₂.1] : (0 : ℝ) < v₂)]
    nlinarith [abs_nonneg (m 1 : ℝ), h₂.2]
  have hc : |(m 2 : ℝ)| ≤ |phase m v₁ v₂| + |(m 0 : ℝ) * v₁| + |(m 1 : ℝ) * v₂| := by
    have e : (m 2 : ℝ) = phase m v₁ v₂ - (m 0 : ℝ) * v₁ - (m 1 : ℝ) * v₂ := by
      unfold phase; ring
    rw [e]
    exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  linarith [abs_nonneg (m 1 : ℝ)]

theorem Ifull_le_of (w : ℝ → ℝ) (N : ℕ) (W : Finset ℝ) (m : Fin 3 → ℤ) {B : ℝ}
    (hK : ∀ v₁ ∈ Set.Icc (1 / 2 : ℝ) 2, ∀ v₂ ∈ Set.Icc (1 / 2 : ℝ) 2, ‖Kfun w N m v₁ v₂‖ ≤ B) :
    Ifull w N W m ≤ W.card * ((W.card * W.card * B) * (3 / 2)) * (3 / 2) := by
  have hvol : volume.real (Set.Icc (1 / 2 : ℝ) 2) = 3 / 2 := by
    rw [Real.volume_real_Icc_of_le (by norm_num)]; norm_num
  have hc : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hKint : ∀ v₁ ∈ Set.Icc (1 / 2 : ℝ) 2,
      Kint w N W m v₁ ≤ (W.card * W.card * B) * (3 / 2) := by
    intro v₁ hv₁
    have hv₁0 : 0 < v₁ := by linarith [hv₁.1]
    refine (Real.le_norm_self _).trans ((norm_setIntegral_le_of_norm_le_const
      measure_Icc_lt_top fun v₂ hv₂ => ?_).trans_eq (by rw [hvol]))
    have hv₂0 : 0 < v₂ := by linarith [hv₂.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (mul_le_mul (norm_Rv_le W (div_pos hv₂0 hv₁0)) (norm_Rv_le W hv₂0)
      (norm_nonneg _) hc) (hK v₁ hv₁ v₂ hv₂) (norm_nonneg _) (by positivity)
  unfold Ifull
  refine (Real.le_norm_self _).trans ((norm_setIntegral_le_of_norm_le_const
    measure_Icc_lt_top fun v₁ hv₁ => ?_).trans_eq (by rw [hvol]))
  have hv₁0 : 0 < v₁ := by linarith [hv₁.1]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Kint_nonneg _ _ _ _ _))]
  exact mul_le_mul (norm_Rv_le W hv₁0) (hKint v₁ hv₁) (Kint_nonneg _ _ _ _ _) hc

theorem card_box_le {L : ℝ} (hL : 0 ≤ L) : ((box L).card : ℝ) ≤ (2 * L + 1) ^ 3 := by
  unfold box
  rw [Fintype.card_piFinset_const, Nat.cast_pow]
  refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 3
  have h0 : 0 ≤ ⌊L⌋ := Int.floor_nonneg.2 hL
  have h1 : (((Finset.Icc (-⌊L⌋) ⌊L⌋).erase 0).card : ℤ) ≤ 2 * ⌊L⌋ + 1 := by
    have := Finset.card_erase_le (s := Finset.Icc (-⌊L⌋) ⌊L⌋) (a := 0)
    rw [Int.card_Icc] at this
    omega
  have h2 : ((((Finset.Icc (-⌊L⌋) ⌊L⌋).erase 0).card : ℤ) : ℝ) ≤ ((2 * ⌊L⌋ + 1 : ℤ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  linarith [Int.floor_le L]

/-- P4. For ordered `m` with `|m₂| > 5|m₁|`, `|phase| ≥ |m₂|/5 ≥ 1/5` on `[1/2,2]²`, so
`Ifull ≤ (9/4)|W|³ A_k (5/N)^k`; at most `(2L+1)³` terms, `N ≥ T^{3/4}`. -/
theorem far_sum_le {w : ℝ → ℝ} (hw : IsWeight w) (η : ℝ) (hη : 0 < η) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ, T ^ (3 / 4 : ℝ) ≤ N → (N : ℝ) ≤ T →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ∑ m ∈ far (T ^ (1 + η) / N), (N : ℝ) ^ 3 * Ifull w N W m ≤
        T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (4 * η + 8)
  obtain ⟨A, hA0, hA⟩ := Kfun_le hw k
  refine ⟨243 * A + 1, fun T hT N hN1 hN2 W a hsep hWa => ?_⟩
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hT0 _) hN1
  set L := T ^ (1 + η) / N with hLdef
  have hTη : T ^ (1 + η) = T * T ^ η := by
    rw [Real.rpow_add hT0, Real.rpow_one]
  have hLN : L * N = T ^ (1 + η) := div_mul_cancel₀ _ hN0.ne'
  have hL1 : 1 ≤ L := by
    rw [hLdef, le_div_iff₀ hN0, one_mul, hTη]
    have := Real.one_le_rpow hT1 hη.le
    nlinarith
  -- the bound on each term
  set c : ℝ := (W.card : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hNk : 0 < (N : ℝ) ^ k := pow_pos hN0 k
  have hterm : ∀ m ∈ far L, (N : ℝ) ^ 3 * Ifull w N W m ≤
      (N : ℝ) ^ 3 * (c * ((c * c * (A / (N : ℝ) ^ k)) * (3 / 2)) * (3 / 2)) := by
    intro m hm
    refine mul_le_mul_of_nonneg_left (Ifull_le_of w N W m ?_) (by positivity)
    intro v₁ hv₁ v₂ hv₂
    have h1 := (hA N m v₁ v₂ hv₁ hv₂).2
    have hph := one_le_abs_phase hm hv₁ hv₂
    have h2 : (N : ℝ) ^ k ≤ ((N : ℝ) * |phase m v₁ v₂|) ^ k :=
      pow_le_pow_left₀ hN0.le (le_mul_of_one_le_right hN0.le hph) k
    rw [le_div_iff₀ hNk]
    exact (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans h1
  have hcard : ((far L).card : ℝ) ≤ 27 * L ^ 3 := by
    have h1 : (far L).card ≤ (box L).card :=
      Finset.card_le_card ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    have h2 : (2 * L + 1) ^ 3 ≤ (3 * L) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    calc ((far L).card : ℝ) ≤ (box L).card := by exact_mod_cast h1
      _ ≤ (2 * L + 1) ^ 3 := card_box_le (by linarith)
      _ ≤ 27 * L ^ 3 := by rw [mul_pow] at h2; norm_num at h2; exact h2
  -- `|W| ≤ 2T`, `|W|³ ≤ 4T² |W|^{3/2}`
  have hW : c ≤ 2 * T := by
    have := card_le_of_sep hT0.le hsep hWa; linarith
  have hp : c ^ (3 / 2 : ℝ) ≤ 4 * T ^ 2 := by
    calc c ^ (3 / 2 : ℝ) ≤ (2 * T) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow hc0 hW (by norm_num)
      _ ≤ (2 * T) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 4 * T ^ 2 := by rw [Real.rpow_two]; ring
  have hc3 : c * (c * c) ≤ 4 * T ^ 2 * c ^ (3 / 2 : ℝ) := by
    have e : c * (c * c) = c ^ (3 / 2 : ℝ) * c ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_add' hc0 (by norm_num)]; norm_num; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  -- `243 A T^{3(1+η)} ≤ N^k`
  have hpow : 243 * A * (T ^ (1 + η)) ^ 3 ≤ (N : ℝ) ^ k := by
    have h1 : (T ^ (3 / 4 : ℝ)) ^ k ≤ (N : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hN1 k
    have h2 : T * (T ^ (1 + η)) ^ 3 ≤ (T ^ (3 / 4 : ℝ)) ^ k := by
      rw [← Real.rpow_mul_natCast hT0.le, ← Real.rpow_mul_natCast hT0.le]
      rw [show T * T ^ ((1 + η) * (3 : ℕ)) = T ^ (1 + (1 + η) * (3 : ℕ)) by
        rw [Real.rpow_add hT0, Real.rpow_one]]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith)
    have h3 : 243 * A ≤ T := by linarith
    have h4 : 0 ≤ (T ^ (1 + η)) ^ 3 := by positivity
    nlinarith
  calc ∑ m ∈ far L, (N : ℝ) ^ 3 * Ifull w N W m
      ≤ ∑ m ∈ far L, (N : ℝ) ^ 3 * (c * ((c * c * (A / (N : ℝ) ^ k)) * (3 / 2)) * (3 / 2)) :=
        Finset.sum_le_sum hterm
    _ = (far L).card * ((N : ℝ) ^ 3 * (c * ((c * c * (A / (N : ℝ) ^ k)) * (3 / 2)) * (3 / 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 27 * L ^ 3 * ((N : ℝ) ^ 3 * (c * ((c * c * (A / (N : ℝ) ^ k)) * (3 / 2)) * (3 / 2))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (243 / 4) * A * (L * N) ^ 3 * (c * (c * c)) / (N : ℝ) ^ k := by
        field_simp; ring
    _ ≤ (243 / 4) * A * (L * N) ^ 3 * (4 * T ^ 2 * c ^ (3 / 2 : ℝ)) / (N : ℝ) ^ k := by
        gcongr
    _ = (243 * A * (T ^ (1 + η)) ^ 3) * (T ^ 2 * c ^ (3 / 2 : ℝ)) / (N : ℝ) ^ k := by
        rw [hLN]; ring
    _ ≤ (N : ℝ) ^ k * (T ^ 2 * c ^ (3 / 2 : ℝ)) / (N : ℝ) ^ k := by
        gcongr
    _ = T ^ 2 * c ^ (3 / 2 : ℝ) := by field_simp

end GuthMaynard.P101.Part2
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
/-! ## P4: far terms and the dyadic groups -/
alias far_sum_le := GuthMaynard.P101.Part2.far_sum_le

alias card_nsc_le := GuthMaynard.P101.Part2.card_nsc_le

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part4
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution
/-! ### The bumps -/
theorem φ_contDiff : ContDiff ℝ (⊤ : ℕ∞) φ := φb.contDiff

theorem ψout_contDiff : ContDiff ℝ (⊤ : ℕ∞) ψout := ψoutb.contDiff

theorem φ_nonneg (x : ℝ) : 0 ≤ φ x := φb.nonneg

theorem ψin_nonneg (x : ℝ) : 0 ≤ ψin x := ψinb.nonneg

theorem ψout_nonneg (x : ℝ) : 0 ≤ ψout x := ψoutb.nonneg

theorem ψin_le_one (x : ℝ) : ψin x ≤ 1 := ψinb.le_one

theorem φ_hcs : HasCompactSupport φ := φb.hasCompactSupport

theorem ψin_hcs : HasCompactSupport ψin := ψinb.hasCompactSupport

theorem ψout_hcs : HasCompactSupport ψout := ψoutb.hasCompactSupport

theorem ψin_pos_of_ne {y : ℝ} (h : ψin y ≠ 0) : 1 / 8 < y ∧ y < 33 / 8 := by
  have : y ∈ Function.support ψinb := h
  rw [ψinb.support_eq, Metric.mem_ball, Real.dist_eq] at this
  have h2 : ψinb.rOut = 2 := rfl
  rw [h2, abs_lt] at this
  constructor <;> linarith [this.1, this.2]

theorem ψout_mem_of_ne {y : ℝ} (h : ψout y ≠ 0) : 1 / 16 < y ∧ y < 129 / 16 := by
  have : y ∈ Function.support ψoutb := h
  rw [ψoutb.support_eq, Metric.mem_ball, Real.dist_eq] at this
  have h2 : ψoutb.rOut = 4 := rfl
  rw [h2, abs_lt] at this
  constructor <;> linarith [this.1, this.2]

theorem ψout_one : ψout 1 = 1 := by
  apply ψoutb.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  have h2 : ψoutb.rIn = 63 / 16 := rfl
  rw [h2, abs_le]; constructor <;> norm_num

theorem ψin_eq_one {y : ℝ} (h1 : 1 / 4 ≤ y) (h2 : y ≤ 4) : ψin y = 1 := by
  apply ψinb.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  have h3 : ψinb.rIn = 15 / 8 := rfl
  rw [h3, abs_le]; constructor <;> linarith

theorem φ_eq_one {y : ℝ} (h : |y| ≤ 2) : φ y = 1 := by
  apply φb.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact h

/-! ### `R` -/
theorem norm_cpow_I {y : ℝ} (hy : 0 < y) (t : ℝ) : ‖(y : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

theorem norm_Rv_le (W : Finset ℝ) {y : ℝ} (hy : 0 < y) : ‖Rv W y‖ ≤ W.card := by
  unfold Rv
  refine (norm_sum_le _ _).trans ?_
  simp [norm_cpow_I hy]

theorem Rv_continuousAt (W : Finset ℝ) {y : ℝ} (hy : 0 < y) : ContinuousAt (Rv W) y := by
  unfold Rv
  have hs : (y : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hy
  fun_prop (disch := exact hs)

/-! ### `g = ψ_in |R|²` and the convolution form of `f` -/
noncomputable def gR (W : Finset ℝ) (y : ℝ) : ℝ := ψin y * ‖Rv W y‖ ^ 2

theorem gR_nonneg (W : Finset ℝ) (y : ℝ) : 0 ≤ gR W y :=
  mul_nonneg (ψin_nonneg y) (by positivity)

theorem gR_le (W : Finset ℝ) (y : ℝ) : gR W y ≤ (W.card : ℝ) ^ 2 := by
  unfold gR
  by_cases h : ψin y = 0
  · rw [h, zero_mul]; positivity
  have hy : 0 < y := by linarith [(ψin_pos_of_ne h).1]
  have h1 := norm_Rv_le W hy
  calc ψin y * ‖Rv W y‖ ^ 2 ≤ 1 * (W.card : ℝ) ^ 2 := by
        gcongr
        · exact ψin_le_one y
    _ = _ := one_mul _

theorem gR_continuous (W : Finset ℝ) : Continuous (gR W) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : 0 < y
  · exact (ψinb.continuous.continuousAt).mul ((Rv_continuousAt W hy).norm.pow 2)
  · have hev : gR W =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show y < 1 / 8 by linarith)] with z hz
      have : ψin z = 0 := by
        by_contra h
        exact absurd (ψin_pos_of_ne h).1 (not_lt.2 (le_of_lt hz))
      simp [gR, this]
    exact (continuousAt_const).congr hev.symm

theorem gR_hcs (W : Finset ℝ) : HasCompactSupport (gR W) :=
  ψin_hcs.mul_right

/-- `k_ρ(z) = ρ⁻¹ φ(-ρ⁻¹ z)`. -/
noncomputable def kρ (ρ : ℝ) (z : ℝ) : ℝ := ρ⁻¹ * φ (-ρ⁻¹ * z)

theorem kρ_contDiff (ρ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (kρ ρ) :=
  contDiff_const.mul (φ_contDiff.comp (contDiff_const.mul contDiff_id))

theorem kρ_hcs {ρ : ℝ} (hρ : ρ ≠ 0) : HasCompactSupport (kρ ρ) := by
  have : HasCompactSupport (fun z : ℝ => φ (-ρ⁻¹ * z)) := by
    simpa [smul_eq_mul] using φ_hcs.comp_smul (neg_ne_zero.2 (inv_ne_zero hρ))
  exact this.mul_left

/-- `h = g ⋆ k_ρ`. -/
noncomputable def hconv (W : Finset ℝ) (ρ : ℝ) : ℝ → ℝ :=
  gR W ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] kρ ρ

theorem fP_eq (W : Finset ℝ) (ρ : ℝ) : fP W ρ = fun x => ψout x * hconv W ρ x := by
  funext x
  simp only [fP, hconv, convolution_def, ContinuousLinearMap.mul_apply', kρ, gR,
    ← integral_const_mul]
  congr 1; funext y
  rw [show (y - x) / ρ = -ρ⁻¹ * (x - y) by ring]
  ring

theorem hconv_contDiff (W : Finset ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (hconv W ρ) :=
  (kρ_hcs hρ).contDiff_convolution_right _ (gR_continuous W).locallyIntegrable (kρ_contDiff ρ)

theorem fP_contDiff (W : Finset ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (fP W ρ) := by
  rw [fP_eq]; exact ψout_contDiff.mul (hconv_contDiff W hρ)

theorem fP_nonneg (W : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) : 0 ≤ fP W ρ x := by
  unfold fP
  refine mul_nonneg (ψout_nonneg x) (mul_nonneg (inv_nonneg.2 hρ.le) (integral_nonneg fun y => ?_))
  exact mul_nonneg (mul_nonneg (φ_nonneg _) (ψin_nonneg _)) (by positivity)

theorem fP_support (W : Finset ℝ) (ρ : ℝ) :
    Function.support (fP W ρ) ⊆ Set.Ioo (1 / 16) (129 / 16) := by
  intro x hx
  have : ψout x ≠ 0 := by
    intro h; apply hx; simp [fP, h]
  exact ψout_mem_of_ne this

theorem fP_hcs (W : Finset ℝ) (ρ : ℝ) : HasCompactSupport (fP W ρ) := by
  rw [fP_eq]; exact ψout_hcs.mul_right

theorem fP_bdd (W : Finset ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) : BddAbove (Set.range (fP W ρ)) := by
  obtain ⟨C, hC⟩ := (fP_contDiff W hρ).continuous.bounded_above_of_compact_support (fP_hcs W ρ)
  exact ⟨C, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (hC x)⟩

/-! ### Derivatives -/
theorem hcs_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : HasCompactSupport f) (n : ℕ) : HasCompactSupport (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem contDiff_iteratedDeriv' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n f) := by
  rw [iteratedDeriv_eq_iterate]; exact hf.iterate_deriv n

theorem iteratedDeriv_kρ (ρ : ℝ) (n : ℕ) (z : ℝ) :
    iteratedDeriv n (kρ ρ) z = ρ⁻¹ * ((-ρ⁻¹) ^ n * iteratedDeriv n φ (-ρ⁻¹ * z)) := by
  have : kρ ρ = fun z => ρ⁻¹ * (fun z => φ (-ρ⁻¹ * z)) z := rfl
  rw [this, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (f := φ) (φb.contDiff (n := n))]

noncomputable def Φ (n : ℕ) : ℝ := ∫ z, |iteratedDeriv n φ z|

theorem Φ_nonneg (n : ℕ) : 0 ≤ Φ n := integral_nonneg fun _ => abs_nonneg _

theorem integrable_iteratedDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) (n : ℕ) :
    Integrable (iteratedDeriv n f) :=
  (hf.continuous_iteratedDeriv n (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (hcs_iteratedDeriv hcs n)

theorem integral_abs_iteratedDeriv_kρ {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    ∫ z, |iteratedDeriv n (kρ ρ) z| = Φ n / ρ ^ n := by
  simp_rw [iteratedDeriv_kρ, abs_mul, abs_pow, abs_neg, abs_inv, abs_of_pos hρ]
  rw [integral_const_mul, integral_const_mul,
    Measure.integral_comp_mul_left (fun z => |iteratedDeriv n φ z|), Φ]
  rw [smul_eq_mul, inv_neg, inv_inv, abs_neg, abs_of_pos hρ, div_eq_mul_inv, ← inv_pow]
  field_simp

theorem iteratedDeriv_hconv (W : Finset ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (n : ℕ) :
    iteratedDeriv n (hconv W ρ) =
      gR W ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] iteratedDeriv n (kρ ρ) := by
  induction n with
  | zero => simp [hconv]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    exact ((hcs_iteratedDeriv (kρ_hcs hρ) n).hasDerivAt_convolution_right _
      (gR_continuous W).locallyIntegrable
      ((contDiff_iteratedDeriv' (kρ_contDiff ρ) n).of_le (by exact_mod_cast le_top)) x).deriv

theorem abs_iteratedDeriv_hconv_le (W : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (hconv W ρ) x| ≤ (W.card : ℝ) ^ 2 * (Φ n / ρ ^ n) := by
  rw [iteratedDeriv_hconv W hρ.ne', convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  set k := iteratedDeriv n (kρ ρ)
  have hk : Integrable k := integrable_iteratedDeriv (kρ_contDiff ρ) (kρ_hcs hρ.ne') n
  have hk' : Integrable (fun y => (W.card : ℝ) ^ 2 * |k (x - y)|) :=
    ((hk.comp_sub_left x).abs).const_mul _
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hk' (Filter.Eventually.of_forall fun y => ?_)).trans
    (le_of_eq ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gR_nonneg W y)]
    exact mul_le_mul_of_nonneg_right (gR_le W y) (abs_nonneg _)
  · rw [integral_const_mul, integral_sub_left_eq_self (fun z => |k z|),
      integral_abs_iteratedDeriv_kρ hρ]

theorem ψout_deriv_bdd (a : ℕ) : ∃ P, 0 ≤ P ∧ ∀ x, |iteratedDeriv a ψout x| ≤ P := by
  obtain ⟨C, hC⟩ := (ψout_contDiff.continuous_iteratedDeriv a
    (by exact_mod_cast le_top)).bounded_above_of_compact_support (hcs_iteratedDeriv ψout_hcs a)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

noncomputable def Pd (a : ℕ) : ℝ := Classical.choose (ψout_deriv_bdd a)

theorem Pd_nonneg (a : ℕ) : 0 ≤ Pd a := (Classical.choose_spec (ψout_deriv_bdd a)).1

theorem Pd_spec (a : ℕ) (x : ℝ) : |iteratedDeriv a ψout x| ≤ Pd a :=
  (Classical.choose_spec (ψout_deriv_bdd a)).2 x

noncomputable def Cf (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Pd i * Φ (j - i)

theorem Cf_nonneg (j : ℕ) : 0 ≤ Cf j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (Pd_nonneg i)) (Φ_nonneg _)

theorem abs_iteratedDeriv_fP_le (W : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ)
    (x : ℝ) : |iteratedDeriv j (fP W ρ) x| ≤ Cf j * ((W.card : ℝ) ^ 2 / ρ ^ j) := by
  rw [fP_eq, ← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  refine (norm_iteratedFDeriv_mul_le ψout_contDiff (hconv_contDiff W hρ.ne') x
    (by exact_mod_cast le_top)).trans ?_
  rw [Cf, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := Pd_spec i x
  have h2 := abs_iteratedDeriv_hconv_le W hρ (j - i) x
  have hρp : ρ ^ j ≤ ρ ^ (j - i) := pow_le_pow_of_le_one hρ.le hρ1 (Nat.sub_le j i)
  have h3 : (W.card : ℝ) ^ 2 * (Φ (j - i) / ρ ^ (j - i)) ≤ Φ (j - i) * ((W.card : ℝ) ^ 2 / ρ ^ j) := by
    rw [mul_div_assoc', mul_div_assoc', mul_comm (Φ (j - i))]
    exact div_le_div_of_nonneg_left (mul_nonneg (by positivity) (Φ_nonneg _)) (by positivity) hρp
  calc (j.choose i : ℝ) * |iteratedDeriv i ψout x| * |iteratedDeriv (j - i) (hconv W ρ) x|
      ≤ (j.choose i : ℝ) * Pd i * (Φ (j - i) * ((W.card : ℝ) ^ 2 / ρ ^ j)) := by
        gcongr <;> first | exact h1 | exact h2.trans h3 |
          exact mul_nonneg (by positivity) (Pd_nonneg i)
    _ = _ := by ring

/-! ### Fourier decay -/
theorem norm_fourier_le (g : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 g ξ‖ ≤ ∫ x, ‖g x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

noncomputable def Fc (W : Finset ℝ) (ρ : ℝ) (u : ℝ) : ℂ := (fP W ρ u : ℂ)

theorem Fc_eq (W : Finset ℝ) (ρ : ℝ) : Fc W ρ = Complex.ofRealLI ∘ fP W ρ := rfl

theorem Fc_contDiff (W : Finset ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (Fc W ρ) :=
  Complex.ofRealCLM.contDiff.comp (fP_contDiff W hρ)

theorem Fc_hcs (W : Finset ℝ) (ρ : ℝ) : HasCompactSupport (Fc W ρ) :=
  (fP_hcs W ρ).comp_left Complex.ofReal_zero

theorem norm_iteratedDeriv_Fc (W : Finset ℝ) {ρ : ℝ} (hρ : ρ ≠ 0) (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (Fc W ρ) x‖ = |iteratedDeriv j (fP W ρ) x| := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← Real.norm_eq_abs,
    ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, Fc_eq,
    LinearIsometry.norm_iteratedFDeriv_comp_left _ (fP_contDiff W hρ).contDiffAt
      (by exact_mod_cast le_top)]

theorem tsupport_fP (W : Finset ℝ) (ρ : ℝ) : tsupport (fP W ρ) ⊆ Set.Icc (1 / 16) (129 / 16) :=
  closure_minimal ((fP_support W ρ).trans Set.Ioo_subset_Icc_self) isClosed_Icc

theorem iteratedDeriv_fP_eq_zero (W : Finset ℝ) (ρ : ℝ) (j : ℕ) {x : ℝ}
    (hx : x ∉ Set.Icc (1 / 16 : ℝ) (129 / 16)) : iteratedDeriv j (fP W ρ) x = 0 := by
  have : x ∉ Function.support (iteratedFDeriv ℝ j (fP W ρ)) :=
    fun h => hx (tsupport_fP W ρ (support_iteratedFDeriv_subset j h))
  rw [Function.notMem_support] at this
  rw [← norm_eq_zero, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv, this, norm_zero]

theorem integral_norm_iteratedDeriv_Fc_le (W : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (j : ℕ) : ∫ x, ‖iteratedDeriv j (Fc W ρ) x‖ ≤ 8 * (Cf j * ((W.card : ℝ) ^ 2 / ρ ^ j)) := by
  set c := Cf j * ((W.card : ℝ) ^ 2 / ρ ^ j)
  have hle : ∀ x, ‖iteratedDeriv j (Fc W ρ) x‖ ≤
      Set.indicator (Set.Icc (1 / 16 : ℝ) (129 / 16)) (fun _ => c) x := by
    intro x
    rw [norm_iteratedDeriv_Fc W hρ.ne']
    by_cases hx : x ∈ Set.Icc (1 / 16 : ℝ) (129 / 16)
    · rw [Set.indicator_of_mem hx]; exact abs_iteratedDeriv_fP_le W hρ hρ1 j x
    · rw [Set.indicator_of_notMem hx, iteratedDeriv_fP_eq_zero W ρ j hx, abs_zero]
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
    ((integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc)
    (Filter.Eventually.of_forall hle)).trans (le_of_eq ?_)
  rw [integral_indicator measurableSet_Icc, setIntegral_const]
  simp
  norm_num

theorem key_decay (W : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j : ℕ) (ξ : ℝ) :
    (2 * Real.pi * |ξ|) ^ j * ‖𝓕 (Fc W ρ) ξ‖ ≤ 8 * (Cf j * ((W.card : ℝ) ^ 2 / ρ ^ j)) := by
  have hF := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) (n := j) (Fc_contDiff W hρ.ne')
    (fun n _ => integrable_iteratedDeriv (Fc_contDiff W hρ.ne') (Fc_hcs W ρ) n)
    (by exact_mod_cast le_top)
  have h := congrFun hF ξ
  have e : (2 * Real.pi * |ξ|) ^ j * ‖𝓕 (Fc W ρ) ξ‖ = ‖𝓕 (iteratedDeriv j (Fc W ρ)) ξ‖ := by
    rw [h, norm_smul, norm_pow]
    congr 2
    simp [abs_of_pos Real.pi_pos]
  rw [e]
  exact (norm_fourier_le _ ξ).trans (integral_norm_iteratedDeriv_Fc_le W hρ hρ1 j)

theorem one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (j : ℕ) : (1 + x) ^ j ≤ 2 ^ j * (1 + x ^ j) := by
  rcases le_total x 1 with h | h
  · calc (1 + x) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
      _ ≤ 2 ^ j * (1 + x ^ j) := le_mul_of_one_le_right (by positivity)
          (le_add_of_nonneg_right (by positivity))
  · calc (1 + x) ^ j ≤ (2 * x) ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
      _ = 2 ^ j * x ^ j := mul_pow _ _ _
      _ ≤ 2 ^ j * (1 + x ^ j) := by gcongr; linarith

/-! ## Targets -/
theorem fP_basic (W : Finset ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (fP W ρ) ∧ (∀ u, 0 ≤ fP W ρ u) ∧
      Function.support (fP W ρ) ⊆ Set.Icc (1 / 16) 16 ∧ BddAbove (Set.range (fP W ρ)) := by
  refine ⟨fP_contDiff W hρ.ne', fP_nonneg W hρ, fun x hx => ?_, fP_bdd W hρ.ne'⟩
  have := fP_support W ρ hx
  exact ⟨this.1.le, by linarith [this.2]⟩

end GuthMaynard.P101.Part4
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
/-! ## P6: the function for Proposition 9.1 -/
alias fP_basic := GuthMaynard.P101.Part4.fP_basic

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part4
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution
theorem fP_fourier_le (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (W : Finset ℝ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ ξ : ℝ,
      ‖𝓕 (fun u => (fP W ρ u : ℂ)) ξ‖ * (1 + ρ * |ξ|) ^ j ≤ B * (W.card : ℝ) ^ 2 := by
  refine ⟨2 ^ j * (8 * Cf 0 + 8 * Cf j), by
    have := Cf_nonneg 0; have := Cf_nonneg j; positivity, fun W ρ hρ hρ1 ξ => ?_⟩
  change ‖𝓕 (Fc W ρ) ξ‖ * _ ≤ _
  set F := ‖𝓕 (Fc W ρ) ξ‖
  have hF0 : 0 ≤ F := norm_nonneg _
  have h0 := key_decay W hρ hρ1 0 ξ
  simp only [pow_zero, one_mul, div_one] at h0
  have hj := key_decay W hρ hρ1 j ξ
  have hρj : 0 < ρ ^ j := pow_pos hρ j
  have hx : 0 ≤ ρ * |ξ| := by positivity
  have h2π : (1 : ℝ) ≤ (2 * Real.pi) ^ j := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hjj : (ρ * |ξ|) ^ j * F ≤ 8 * Cf j * (W.card : ℝ) ^ 2 := by
    have e1 : (ρ * |ξ|) ^ j * F * (2 * Real.pi) ^ j = ρ ^ j * ((2 * Real.pi * |ξ|) ^ j * F) := by
      rw [mul_pow, mul_pow, mul_pow]; ring
    have e2 : ρ ^ j * (8 * (Cf j * ((W.card : ℝ) ^ 2 / ρ ^ j))) = 8 * Cf j * (W.card : ℝ) ^ 2 := by
      field_simp
    have hA : 0 ≤ (ρ * |ξ|) ^ j * F := by positivity
    calc (ρ * |ξ|) ^ j * F ≤ (ρ * |ξ|) ^ j * F * (2 * Real.pi) ^ j := le_mul_of_one_le_right hA h2π
      _ = _ := e1
      _ ≤ ρ ^ j * (8 * (Cf j * ((W.card : ℝ) ^ 2 / ρ ^ j))) := by gcongr
      _ = _ := e2
  calc F * (1 + ρ * |ξ|) ^ j ≤ F * (2 ^ j * (1 + (ρ * |ξ|) ^ j)) := by
        gcongr; exact one_add_pow_le hx j
    _ = 2 ^ j * (F + (ρ * |ξ|) ^ j * F) := by ring
    _ ≤ 2 ^ j * (8 * Cf 0 * (W.card : ℝ) ^ 2 + 8 * Cf j * (W.card : ℝ) ^ 2) := by
        gcongr
        linarith
    _ = _ := by ring

end GuthMaynard.P101.Part4
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part4
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution
/-! ### The lower bound at `1` -/
theorem norm_Rv_ge {T : ℝ} (W : Finset ℝ) (a : ℝ)
    (hWa : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) {y : ℝ} (hy : 0 < y)
    (hlog : |Real.log y| * T ≤ 1 / 3) : (W.card : ℝ) / 2 ≤ ‖Rv W y‖ := by
  have hterm : ∀ t : ℝ, (y : ℂ) ^ ((t : ℂ) * I) = exp (((t * Real.log y : ℝ) : ℂ) * I) := by
    intro t
    rw [cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← ofReal_log hy.le]
    push_cast; ring_nf
  have hrot : exp (((-a * Real.log y : ℝ) : ℂ) * I) * Rv W y =
      ∑ t ∈ W, exp ((((t - a) * Real.log y : ℝ) : ℂ) * I) := by
    rw [Rv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hterm, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hn : ‖Rv W y‖ = ‖exp (((-a * Real.log y : ℝ) : ℂ) * I) * Rv W y‖ := by
    rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
  rw [hn, hrot]
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [Complex.re_sum]
  simp_rw [Complex.exp_ofReal_mul_I_re]
  have hcos : ∀ t ∈ W, (1 / 2 : ℝ) ≤ Real.cos ((t - a) * Real.log y) := by
    intro t ht
    have h1 := hWa t ht
    have hb : |(t - a) * Real.log y| ≤ 1 / 3 := by
      rw [abs_mul, abs_of_nonneg (by linarith [h1.1])]
      calc (t - a) * |Real.log y| ≤ T * |Real.log y| := by
            gcongr; linarith [h1.2]
        _ ≤ 1 / 3 := by linarith
    have hc := Real.one_sub_sq_div_two_le_cos (x := (t - a) * Real.log y)
    have hsq : ((t - a) * Real.log y) ^ 2 ≤ 1 / 9 := by
      rw [← sq_abs]; nlinarith [abs_nonneg ((t - a) * Real.log y)]
    linarith
  have := Finset.card_nsmul_le_sum W _ (1 / 2 : ℝ) hcos
  rw [nsmul_eq_mul] at this
  linarith

theorem fP_one_ge (T : ℝ) (hT : 1 ≤ T) (W : Finset ℝ) (a : ℝ)
    (hWa : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) (ρ : ℝ) (hρ : 0 < ρ) (hρT : 1 ≤ ρ * T) :
    (W.card : ℝ) ^ 2 / (8 * ρ * T) ≤ fP W ρ 1 := by
  have hT0 : 0 < T := by linarith
  set δ : ℝ := 1 / (4 * T) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 4 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hδρ : δ ≤ 2 * ρ := by
    rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
  set F : ℝ → ℝ := fun y => φ ((y - 1) / ρ) * ψin y * ‖Rv W y‖ ^ 2 with hFdef
  have hFeq : F = fun y => φ ((y - 1) / ρ) * gR W y := by
    funext y; simp only [hFdef, gR]; ring
  have hFnn : ∀ y, 0 ≤ F y := fun y => by
    rw [hFeq]; exact mul_nonneg (φ_nonneg _) (gR_nonneg W y)
  have hFint : Integrable F := by
    rw [hFeq]
    refine Continuous.integrable_of_hasCompactSupport ?_ (gR_hcs W).mul_left
    exact (φb.continuous.comp ((continuous_id.sub continuous_const).div_const ρ)).mul
      (gR_continuous W)
  set S := Set.Icc (1 - δ) (1 + δ)
  have hpt : ∀ y ∈ S, (W.card : ℝ) ^ 2 / 4 ≤ F y := by
    intro y hy
    have hy1 : 1 - δ ≤ y := hy.1
    have hy2 : y ≤ 1 + δ := hy.2
    have hy0 : 0 < y := by linarith
    have hφ : φ ((y - 1) / ρ) = 1 := by
      apply φ_eq_one
      rw [abs_div, abs_of_pos hρ, div_le_iff₀ hρ, abs_le]
      constructor <;> linarith
    have hψ : ψin y = 1 := ψin_eq_one (by linarith) (by linarith)
    have hlog : |Real.log y| * T ≤ 1 / 3 := by
      have hu := Real.log_le_sub_one_of_pos hy0
      have hl := Real.one_sub_inv_le_log_of_pos hy0
      have hinv : y⁻¹ ≤ 1 + 4 / 3 * δ := by
        rw [inv_eq_one_div, div_le_iff₀ hy0]; nlinarith
      have hTδ : δ * T = 1 / 4 := by rw [hδ]; field_simp
      have hab : |Real.log y| ≤ 4 / 3 * δ := abs_le.2 ⟨by linarith, by linarith⟩
      nlinarith
    have hR := norm_Rv_ge W a hWa hy0 hlog
    simp only [hFdef, hφ, hψ, one_mul]
    have : 0 ≤ (W.card : ℝ) / 2 := by positivity
    nlinarith
  have hlow : (W.card : ℝ) ^ 2 / (8 * T) ≤ ∫ y, F y := by
    calc (W.card : ℝ) ^ 2 / (8 * T) = ∫ y in S, (W.card : ℝ) ^ 2 / 4 := by
          rw [setIntegral_const]
          simp only [S, Real.volume_real_Icc, smul_eq_mul]
          rw [max_eq_left (by linarith), hδ]; field_simp; ring
      _ ≤ ∫ y in S, F y := setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne)
          hFint.integrableOn measurableSet_Icc hpt
      _ ≤ ∫ y, F y := setIntegral_le_integral hFint (Filter.Eventually.of_forall hFnn)
  have hf1 : fP W ρ 1 = ρ⁻¹ * ∫ y, F y := by
    simp only [fP, ψout_one, one_mul, hFdef]
  rw [hf1, show (W.card : ℝ) ^ 2 / (8 * ρ * T) = ρ⁻¹ * ((W.card : ℝ) ^ 2 / (8 * T)) by
    field_simp]
  exact mul_le_mul_of_nonneg_left hlow (inv_nonneg.2 hρ.le)

end GuthMaynard.P101.Part4
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part4
open GuthMaynard GuthMaynard.P101 MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution
/-! ### Admissibility -/
theorem integral_fP_le (W : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ u, fP W ρ u ≤ 8 * ⨆ u, fP W ρ u := by
  set M := ⨆ u, fP W ρ u
  have hle : ∀ x, fP W ρ x ≤ Set.indicator (Set.Icc (1 / 16 : ℝ) (129 / 16)) (fun _ => M) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (1 / 16 : ℝ) (129 / 16)
    · rw [Set.indicator_of_mem hx]; exact le_ciSup (fP_bdd W hρ.ne') x
    · rw [Set.indicator_of_notMem hx]
      have : x ∉ Function.support (fP W ρ) := fun h => hx (Set.Ioo_subset_Icc_self (fP_support W ρ h))
      rw [Function.notMem_support.1 this]
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall (fP_nonneg W hρ))
    ((integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc)
    (Filter.Eventually.of_forall hle)).trans (le_of_eq ?_)
  rw [integral_indicator measurableSet_Icc, setIntegral_const]
  simp
  norm_num

noncomputable def Bf (j : ℕ) : ℝ := Classical.choose (fP_fourier_le j)

theorem fP_adm : ∃ c : ℕ → ℝ → ℝ, ∀ T : ℝ, 1 ≤ T → ∀ (W : Finset ℝ) (a : ℝ),
    (∀ t ∈ W, t ∈ Set.Icc a (a + T)) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → 1 ≤ ρ * T →
      ContDiff ℝ (⊤ : ℕ∞) (fP W ρ) ∧ (∀ u, 0 ≤ fP W ρ u) ∧
      Function.support (fP W ρ) ⊆ Set.Icc (1 / 16) 16 ∧
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖FourierTransform.fourier (fun u => (fP W ρ u : ℂ)) ξ‖ ≤
          c j ε * T ^ ε * (T / |ξ|) ^ j * ⨆ u, fP W ρ u) := by
  refine ⟨fun j _ => if j = 0 then 16 else 8 * Bf j, ?_⟩
  intro T hT W a hWa ρ hρ hρ1 hρT
  obtain ⟨h1, h2, h3, -⟩ := fP_basic W ρ hρ
  refine ⟨h1, h2, h3, fun j ε hε ξ hξ => ?_⟩
  set M := ⨆ u, fP W ρ u
  have hM1 : fP W ρ 1 ≤ M := le_ciSup (fP_bdd W hρ.ne') 1
  have hM0 : 0 ≤ M := (h2 1).trans hM1
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hT0 : 0 < T := by linarith
  set F := ‖FourierTransform.fourier (fun u => (fP W ρ u : ℂ)) ξ‖
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [if_true, pow_zero, mul_one]
    have hF : F ≤ 8 * M := by
      refine (norm_fourier_le _ ξ).trans ?_
      simp_rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h2 _)]
      exact integral_fP_le W hρ
    nlinarith
  · simp only [if_neg hj.ne']
    have hB := (Classical.choose_spec (fP_fourier_le j)).2 W ρ hρ hρ1 ξ
    have hB0 := (Classical.choose_spec (fP_fourier_le j)).1
    change F * _ ≤ Bf j * _ at hB
    change 0 ≤ Bf j at hB0
    have hW : (W.card : ℝ) ^ 2 ≤ 8 * ρ * T * M := by
      have := (fP_one_ge T hT W a hWa ρ hρ hρT).trans hM1
      rwa [div_le_iff₀ (by positivity), mul_comm] at this
    have hξ0 : 0 < |ξ| := abs_pos.2 hξ
    have hx : 0 < (ρ * |ξ|) ^ j := by positivity
    have hF0 : 0 ≤ F := norm_nonneg _
    have hpow : (ρ * |ξ|) ^ j ≤ (1 + ρ * |ξ|) ^ j :=
      pow_le_pow_left₀ (by positivity) (by linarith) j
    have hρTj : ρ * T ≤ (ρ * T) ^ j := le_self_pow₀ hρT hj.ne'
    have e : (T / |ξ|) ^ j * (ρ * |ξ|) ^ j = (ρ * T) ^ j := by
      rw [← mul_pow]; congr 1; field_simp
    have key : F * (ρ * |ξ|) ^ j ≤ (8 * Bf j * (T / |ξ|) ^ j * M) * (ρ * |ξ|) ^ j := by
      calc F * (ρ * |ξ|) ^ j ≤ F * (1 + ρ * |ξ|) ^ j := mul_le_mul_of_nonneg_left hpow hF0
        _ ≤ Bf j * (W.card : ℝ) ^ 2 := hB
        _ ≤ Bf j * (8 * ρ * T * M) := mul_le_mul_of_nonneg_left hW hB0
        _ = 8 * Bf j * M * (ρ * T) := by ring
        _ ≤ 8 * Bf j * M * (ρ * T) ^ j := by gcongr
        _ = (8 * Bf j * (T / |ξ|) ^ j * M) * (ρ * |ξ|) ^ j := by rw [← e]; ring
    have hF : F ≤ 8 * Bf j * (T / |ξ|) ^ j * M := le_of_mul_le_mul_right key hx
    have hR : 0 ≤ 8 * Bf j * (T / |ξ|) ^ j * M := by positivity
    calc F ≤ 8 * Bf j * (T / |ξ|) ^ j * M := hF
      _ ≤ 8 * Bf j * T ^ ε * (T / |ξ|) ^ j * M := by nlinarith

end GuthMaynard.P101.Part4
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias fP_adm := GuthMaynard.P101.Part4.fP_adm

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part5
open GuthMaynard GuthMaynard.P101 MeasureTheory Complex
open scoped ENNReal Convolution
/-! ### Exponential sums and mean values over `[-1, 1]` (from E111 PartD) -/
/-- `E x = e^{ix}`. -/
noncomputable def E (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * I)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma conj_E (x : ℝ) : (starRingEnd ℂ) (E x) = E (-x) := by
  unfold E; rw [← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := Complex.norm_exp_ofReal_mul_I x

lemma sq_eq_mul_conj (z : ℂ) : (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj']; push_cast; ring

lemma continuous_E_mul (a : ℝ) : Continuous fun y : ℝ => E (a * y) := by
  unfold E; fun_prop

lemma hasDerivAt_E_mul (a y : ℝ) :
    HasDerivAt (fun y : ℝ => E (a * y)) (((a : ℂ) * I) * E (a * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => (a : ℂ) * (y : ℂ) * I) ((a : ℂ) * 1 * I) y :=
    ((hasDerivAt_id y).ofReal_comp.const_mul (a : ℂ)).mul_const I
  have h2 := h1.cexp
  unfold E
  convert h2 using 1
  · funext y; push_cast; ring_nf
  · push_cast; ring

noncomputable def G {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (y : ℝ) : ℂ :=
  ∑ i ∈ S, E (φ i * y)

lemma continuous_G {ι : Type*} (S : Finset ι) (φ : ι → ℝ) : Continuous (G S φ) := by
  unfold G; exact continuous_finsetSum _ fun i _ => continuous_E_mul _

lemma G_WW (W : Finset ℝ) (y : ℝ) :
    G (W ×ˢ W) (fun p => p.1 + p.2) y = G W (fun t => t) y ^ 2 := by
  unfold G; rw [sq, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← E_add]; congr 1; ring

noncomputable def kern (x : ℝ) : ℝ := 6 / (|((⌊x⌋ : ℤ) : ℝ)| + 1)

lemma norm_integral_E_le (x : ℝ) : ‖∫ y in (-1 : ℝ)..1, E (x * y)‖ ≤ kern x := by
  set n := ‖∫ y in (-1 : ℝ)..1, E (x * y)‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have ha : n ≤ 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
      (C := 1) (f := fun y => E (x * y)) (fun y _ => by rw [norm_E])
    norm_num at this; linarith
  have hb : x ≠ 0 → n * |x| ≤ 2 := by
    intro hx
    have hxI : ((x : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hx) I_ne_zero
    have hd : ∀ y, HasDerivAt (fun y : ℝ => E (x * y) / ((x : ℂ) * I)) (E (x * y)) y := by
      intro y
      have := (hasDerivAt_E_mul x y).div_const ((x : ℂ) * I)
      rwa [mul_div_cancel_left₀ _ hxI] at this
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 1)
      (fun y _ => hd y) ((continuous_E_mul x).intervalIntegrable _ _)
    rw [hn, hint, ← sub_div, norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one, mul_one]
    rw [div_mul_cancel₀ _ (abs_pos.mpr hx).ne']
    calc ‖E x - E (x * -1)‖ ≤ ‖E x‖ + ‖E (x * -1)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_E, norm_E]; norm_num
  unfold kern
  rw [le_div_iff₀ (by positivity)]
  set k := ⌊x⌋
  have k1 := Int.floor_le x
  have k2 := Int.lt_floor_add_one x
  by_cases h1 : 1 ≤ k
  · have hK : (1 : ℝ) ≤ k := by exact_mod_cast h1
    have hx : 0 < x := by linarith
    have := hb hx.ne'
    rw [abs_of_pos hx] at this
    rw [abs_of_pos (by linarith : (0 : ℝ) < k)]
    nlinarith
  · by_cases h2 : k ≤ -2
    · have hK : (k : ℝ) ≤ -2 := by exact_mod_cast h2
      have hx : x < 0 := by linarith
      have := hb hx.ne
      rw [abs_of_neg hx] at this
      rw [abs_of_neg (by linarith : (k : ℝ) < 0)]
      nlinarith
    · have hK : |(k : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor
        · have : -1 ≤ k := by omega
          exact_mod_cast this
        · have : k ≤ 1 := by omega
          exact_mod_cast this
      nlinarith

lemma mv {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (c : ι → ℂ) (B : ℝ) (hc : ∀ i ∈ S, ‖c i‖ ≤ B) :
    ∫ y in (-1 : ℝ)..1, ‖∑ i ∈ S, c i * E (φ i * y)‖ ^ 2 ≤
      B ^ 2 * ∑ i ∈ S, ∑ j ∈ S, kern (φ i - φ j) := by
  have hcont : ∀ i j, Continuous fun y : ℝ => c i * (starRingEnd ℂ) (c j) * E ((φ i - φ j) * y) :=
    fun i j => continuous_const.mul (continuous_E_mul _)
  have hexp : ∀ y : ℝ, (((‖∑ i ∈ S, c i * E (φ i * y)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j) * E ((φ i - φ j) * y) := by
    intro y
    rw [sq_eq_mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, conj_E, show (φ i - φ j) * y = φ i * y + -(φ j * y) by ring, E_add]; ring
  have hI : ((∫ y in (-1 : ℝ)..1, ‖∑ i ∈ S, c i * E (φ i * y)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j) * ∫ y in (-1 : ℝ)..1, E ((φ i - φ j) * y) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hexp]
    rw [intervalIntegral.integral_finsetSum
      (fun i _ => (continuous_finsetSum _ fun j _ => hcont i j).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont i j).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  set r := ∫ y in (-1 : ℝ)..1, ‖∑ i ∈ S, c i * E (φ i * y)‖ ^ 2
  have h1 : r ≤ ‖(r : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self r
  rw [hI] at h1
  refine h1.trans ((norm_sum_le _ _).trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have hci := hc i hi
  have hcj := hc j hj
  have hk := norm_integral_E_le (φ i - φ j)
  have hB : 0 ≤ B := (norm_nonneg _).trans hci
  calc ‖c i‖ * ‖c j‖ * ‖∫ y in (-1 : ℝ)..1, E ((φ i - φ j) * y)‖ ≤ B * B * kern (φ i - φ j) := by
        gcongr
    _ = B ^ 2 * kern (φ i - φ j) := by ring

lemma sum_Icc_inv (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 1 / (|(k : ℝ)| + 1) ≤
      2 * ∑ j ∈ Finset.range (n + 1), 1 / ((j : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n + 1 : ℕ) : ℤ)) (insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) n)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [e, Finset.sum_insert (by simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; push_cast; omega),
      Finset.sum_range_succ _ (n + 1)]
    have h1 : |(((-((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
    have h2 : |((((n + 1 : ℕ) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast; rw [abs_of_nonneg (by positivity)]
    rw [h1, h2]
    push_cast
    linarith

lemma sum_kern_Icc (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 6 / (|(k : ℝ)| + 1) ≤ 12 * (1 + Real.log (n + 1)) := by
  have h := sum_Icc_inv n
  have hh : ∑ j ∈ Finset.range (n + 1), 1 / ((j : ℝ) + 1) = ((harmonic (n + 1) : ℚ) : ℝ) := by
    simp [harmonic]
  have hl := harmonic_le_one_add_log (n + 1)
  rw [hh] at h
  push_cast at hl
  calc ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 6 / (|(k : ℝ)| + 1)
      = 6 * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 1 / (|(k : ℝ)| + 1) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 6 * (2 * ((harmonic (n + 1) : ℚ) : ℝ)) := by gcongr
    _ ≤ _ := by linarith

lemma ksum {ι : Type*} [DecidableEq ι] (S : Finset ι) (φ : ι → ℝ) (A R : ℝ) (hR0 : 0 ≤ R)
    (hA : ∀ k : ℤ, (((S ×ˢ S).filter (fun q => ⌊φ q.1 - φ q.2⌋ = k)).card : ℝ) ≤ A)
    (hR : ∀ i ∈ S, ∀ j ∈ S, |φ i - φ j| ≤ R) :
    ∑ i ∈ S, ∑ j ∈ S, kern (φ i - φ j) ≤ 12 * A * (1 + Real.log (R + 2)) := by
  classical
  set n := ⌈R⌉₊
  have hRn : R ≤ n := Nat.le_ceil R
  have hn1 : (n : ℝ) < R + 1 := Nat.ceil_lt_add_one hR0
  have hA0 : 0 ≤ A := (Nat.cast_nonneg _).trans (hA 0)
  have hmaps : ∀ q ∈ S ×ˢ S, ⌊φ q.1 - φ q.2⌋ ∈ Finset.Icc (-(n : ℤ)) n := by
    intro q hq
    rw [Finset.mem_product] at hq
    have := abs_le.mp (hR _ hq.1 _ hq.2)
    rw [Finset.mem_Icc]
    constructor
    · apply Int.le_floor.mpr; push_cast; linarith
    · have := Int.floor_le (φ q.1 - φ q.2)
      have : ((⌊φ q.1 - φ q.2⌋ : ℤ) : ℝ) ≤ (n : ℤ) := by push_cast; linarith
      exact_mod_cast this
  rw [← Finset.sum_product' (f := fun i j => kern (φ i - φ j))]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Finset.Icc (-(n : ℤ)) n, ∑ q ∈ (S ×ˢ S).filter (fun q => ⌊φ q.1 - φ q.2⌋ = k),
        kern (φ q.1 - φ q.2)
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          (((S ×ˢ S).filter (fun q => ⌊φ q.1 - φ q.2⌋ = k)).card : ℝ) * (6 / (|(k : ℝ)| + 1)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => 6 / (|(k : ℝ)| + 1)), Finset.sum_const,
          nsmul_eq_mul]
        intro q hq
        unfold kern
        rw [(Finset.mem_filter.mp hq).2]
    _ ≤ ∑ k ∈ Finset.Icc (-(n : ℤ)) n, A * (6 / (|(k : ℝ)| + 1)) := by
        gcongr with k _
        exact hA k
    _ = A * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 6 / (|(k : ℝ)| + 1) := by rw [Finset.mul_sum]
    _ ≤ A * (12 * (1 + Real.log (n + 1))) := by gcongr; exact sum_kern_Icc n
    _ ≤ A * (12 * (1 + Real.log (R + 2))) := by
        have := Real.log_le_log (by positivity : (0 : ℝ) < n + 1) (by linarith : (n : ℝ) + 1 ≤ R + 2)
        nlinarith
    _ = _ := by ring

lemma bin1 (W : Finset ℝ) (hW : IsSeparated 1 W) (c : ℝ) (k : ℤ) :
    (((W ×ˢ W).filter (fun q => ⌊(q.1 - c) - (q.2 - c)⌋ = k)).card : ℝ) ≤ W.card := by
  classical
  have hle : ∀ x ∈ W, (W.filter (fun y => ⌊(x - c) - (y - c)⌋ = k)).card ≤ 1 := by
    intro x _
    apply Finset.card_le_one.mpr
    intro y hy y' hy'
    rw [Finset.mem_filter] at hy hy'
    by_contra hne
    have hs := hW y hy.1 y' hy'.1 hne
    have a1 := Int.floor_le ((x - c) - (y - c))
    have a2 := Int.lt_floor_add_one ((x - c) - (y - c))
    have b1 := Int.floor_le ((x - c) - (y' - c))
    have b2 := Int.lt_floor_add_one ((x - c) - (y' - c))
    rw [hy.2] at a1 a2; rw [hy'.2] at b1 b2
    rcases le_abs.mp hs with h | h <;> linarith
  have : ((W ×ˢ W).filter (fun q => ⌊(q.1 - c) - (q.2 - c)⌋ = k)).card ≤ W.card := by
    rw [Finset.card_filter, Finset.sum_product]
    calc ∑ x ∈ W, ∑ y ∈ W, (if ⌊(x - c) - (y - c)⌋ = k then 1 else 0)
        = ∑ x ∈ W, (W.filter (fun y => ⌊(x - c) - (y - c)⌋ = k)).card :=
          Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
      _ ≤ ∑ x ∈ W, 1 := Finset.sum_le_sum hle
      _ = W.card := by simp
  exact_mod_cast this

end GuthMaynard.P101.Part5
end

section
namespace GuthMaynard.P101.Part5
open GuthMaynard GuthMaynard.P101 MeasureTheory Complex
open scoped ENNReal Convolution
variable {α : Type*}
def Qc (V : Finset α) (g : α → ℤ) (k : ℤ) : ℕ :=
  ((V ×ˢ V).filter (fun q => g q.1 - g q.2 = k)).card

def rc (V : Finset α) (g : α → ℤ) (j : ℤ) : ℕ := (V.filter (fun p => g p = j)).card

lemma Qc_eq (V : Finset α) (g : α → ℤ) (k : ℤ) :
    Qc V g k = ∑ j ∈ V.image g, rc V g j * rc V g (j - k) := by
  unfold Qc
  rw [Finset.card_filter, Finset.sum_product]
  have : ∀ p ∈ V, ∑ q ∈ V, (if g p - g q = k then 1 else 0) = rc V g (g p - k) := by
    intro p _
    rw [← Finset.card_filter]; unfold rc
    congr 1; apply Finset.filter_congr; intro q _; omega
  rw [Finset.sum_congr rfl this, Finset.sum_comp (fun j => rc V g (j - k)) g]
  rfl

lemma rc_ne_zero (V : Finset α) (g : α → ℤ) (j : ℤ) (h : rc V g j ≠ 0) : j ∈ V.image g := by
  unfold rc at h
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  rw [Finset.mem_filter] at hp
  exact Finset.mem_image.mpr ⟨p, hp.1, hp.2⟩

lemma Qc_le (V : Finset α) (g : α → ℤ) (k : ℤ) : Qc V g k ≤ Qc V g 0 := by
  rw [Qc_eq, Qc_eq]
  simp only [sub_zero]
  set J := V.image g
  have hsh : ∑ j ∈ J, rc V g (j - k) ^ 2 ≤ ∑ j ∈ J, rc V g j ^ 2 := by
    rw [← Finset.sum_image (f := fun j => rc V g j ^ 2) (s := J) (g := fun j => j - k)
      (fun a _ b _ h => by simpa using h)]
    apply Finset.sum_le_sum_of_ne_zero
    intro j _ hj
    exact rc_ne_zero V g j (by intro h0; apply hj; simp [h0])
  have h2 : ∀ j ∈ J, 2 * (rc V g j * rc V g (j - k)) ≤ rc V g j ^ 2 + rc V g (j - k) ^ 2 := by
    intro j _
    nlinarith [sq_nonneg ((rc V g j : ℤ) - rc V g (j - k))]
  have h3 : 2 * ∑ j ∈ J, rc V g j * rc V g (j - k) ≤
      ∑ j ∈ J, rc V g j ^ 2 + ∑ j ∈ J, rc V g (j - k) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_le_sum h2
  have h4 : ∑ j ∈ J, rc V g j * rc V g j = ∑ j ∈ J, rc V g j ^ 2 :=
    Finset.sum_congr rfl fun j _ => (sq _).symm
  omega

end GuthMaynard.P101.Part5
end

section
namespace GuthMaynard.P101.Part5
open GuthMaynard GuthMaynard.P101 MeasureTheory Complex
open scoped ENNReal Convolution
lemma floor_sub_cases (x y : ℝ) (k : ℤ) (h : ⌊x - y⌋ = k) :
    ⌊x⌋ - ⌊y⌋ = k ∨ ⌊x⌋ - ⌊y⌋ = k + 1 := by
  have a1 := Int.floor_le x; have a2 := Int.lt_floor_add_one x
  have b1 := Int.floor_le y; have b2 := Int.lt_floor_add_one y
  have c1 := Int.floor_le (x - y); have c2 := Int.lt_floor_add_one (x - y)
  rw [h] at c1 c2
  have h1 : ((k : ℤ) : ℝ) - 1 < ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by push_cast; linarith
  have h2 : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) < ((k + 2 : ℤ) : ℝ) := by push_cast; linarith
  have h1' : k - 1 < ⌊x⌋ - ⌊y⌋ := by exact_mod_cast h1
  have h2' : ⌊x⌋ - ⌊y⌋ < k + 2 := by exact_mod_cast h2
  omega

lemma bin2 (W : Finset ℝ) (c : ℝ) (k : ℤ) :
    ((((W ×ˢ W) ×ˢ (W ×ˢ W)).filter
      (fun q => ⌊(q.1.1 + q.1.2 - c) - (q.2.1 + q.2.2 - c)⌋ = k)).card : ℝ) ≤
      2 * (energy W : ℝ) := by
  classical
  set V := W ×ˢ W with hV
  set g : ℝ × ℝ → ℤ := fun p => ⌊p.1 + p.2⌋
  have hsub : ((V ×ˢ V).filter
      (fun q => ⌊(q.1.1 + q.1.2 - c) - (q.2.1 + q.2.2 - c)⌋ = k)) ⊆
      ((V ×ˢ V).filter (fun q => g q.1 - g q.2 = k)) ∪
        ((V ×ˢ V).filter (fun q => g q.1 - g q.2 = k + 1)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    have e : (q.1.1 + q.1.2 - c) - (q.2.1 + q.2.2 - c) = (q.1.1 + q.1.2) - (q.2.1 + q.2.2) := by
      ring
    rw [e] at hq
    rcases floor_sub_cases _ _ k hq.2 with h | h
    · exact Or.inl ⟨hq.1, h⟩
    · exact Or.inr ⟨hq.1, h⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hQ0 : Qc V g 0 ≤ energy W := by
    unfold Qc energy
    apply Finset.card_le_card_of_injOn (fun q => (q.1.1, q.1.2, q.2.1, q.2.2))
    · intro q hq
      simp only [hV, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at hq ⊢
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hq
      refine ⟨⟨h1, h2, h3, h4⟩, ?_⟩
      have hg : ⌊q.1.1 + q.1.2⌋ = ⌊q.2.1 + q.2.2⌋ := by simp only [g] at h5; omega
      have a1 := Int.floor_le (q.1.1 + q.1.2); have a2 := Int.lt_floor_add_one (q.1.1 + q.1.2)
      have b1 := Int.floor_le (q.2.1 + q.2.2); have b2 := Int.lt_floor_add_one (q.2.1 + q.2.2)
      rw [hg] at a1 a2
      rw [abs_le]; constructor <;> linarith
    · intro q _ q' _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)
  have hk1 := Qc_le V g k
  have hk2 := Qc_le V g (k + 1)
  unfold Qc at hk1 hk2 hQ0
  have : ((V ×ˢ V).filter
      (fun q => ⌊(q.1.1 + q.1.2 - c) - (q.2.1 + q.2.2 - c)⌋ = k)).card ≤ 2 * energy W := by
    omega
  exact_mod_cast this

/-! ### Mean values over `[-3, 3]` -/
lemma mv_shift {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (s : ℝ) :
    ∫ y in (-1 : ℝ)..1, ‖G S φ (y + s)‖ ^ 2 ≤ ∑ i ∈ S, ∑ j ∈ S, kern (φ i - φ j) := by
  have h := mv S φ (fun i => E (φ i * s)) 1 (fun i _ => by rw [norm_E])
  rw [one_pow, one_mul] at h
  have e : ∀ y, G S φ (y + s) = ∑ i ∈ S, E (φ i * s) * E (φ i * y) := fun y => by
    unfold G; refine Finset.sum_congr rfl fun i _ => ?_; rw [← E_add]; congr 1; ring
  simp_rw [e]; exact h

lemma mv3 {ι : Type*} (S : Finset ι) (φ : ι → ℝ) :
    ∫ y in (-3 : ℝ)..3, ‖G S φ y‖ ^ 2 ≤ 3 * ∑ i ∈ S, ∑ j ∈ S, kern (φ i - φ j) := by
  have hc : Continuous fun y => ‖G S φ y‖ ^ 2 := by have := continuous_G S φ; fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun y => ‖G S φ y‖ ^ 2) volume a b :=
    fun a b => hc.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-3) (-1)) (hi (-1) 3),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-1) 1) (hi 1 3)]
  have h1 := mv_shift S φ (-2)
  have h2 := mv_shift S φ 0
  have h3 := mv_shift S φ 2
  rw [intervalIntegral.integral_comp_add_right (fun y => ‖G S φ y‖ ^ 2)] at h1 h2 h3
  norm_num at h1 h2 h3
  linarith

lemma MV1 (W : Finset ℝ) (hW : IsSeparated 1 W) (a T : ℝ) (hT : 0 ≤ T)
    (hWa : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) :
    ∑ i ∈ W, ∑ j ∈ W, kern ((fun t : ℝ => t) i - (fun t : ℝ => t) j) ≤
      12 * W.card * (1 + Real.log (T + 2)) := by
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    congrArg kern (show (fun t : ℝ => t) i - (fun t : ℝ => t) j =
      (fun t : ℝ => t - a) i - (fun t : ℝ => t - a) j by ring))
    (ksum W (fun t => t - a) _ T hT (bin1 W hW a) fun i hi j hj => ?_)
  have := hWa i hi; have := hWa j hj
  simp only [Set.mem_Icc] at *
  rw [abs_le]; constructor <;> linarith

lemma MV2 (W : Finset ℝ) (a T : ℝ) (hT : 0 ≤ T) (hWa : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) :
    ∑ i ∈ W ×ˢ W, ∑ j ∈ W ×ˢ W,
      kern ((fun p : ℝ × ℝ => p.1 + p.2) i - (fun p : ℝ × ℝ => p.1 + p.2) j) ≤
      12 * (2 * (energy W : ℝ)) * (1 + Real.log (2 * T + 2)) := by
  classical
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    congrArg kern (show (fun p : ℝ × ℝ => p.1 + p.2) i - (fun p : ℝ × ℝ => p.1 + p.2) j =
      (fun p : ℝ × ℝ => p.1 + p.2 - 2 * a) i - (fun p : ℝ × ℝ => p.1 + p.2 - 2 * a) j by ring))
    (ksum (W ×ˢ W) (fun p => p.1 + p.2 - 2 * a) _ (2 * T) (by positivity)
      (bin2 W (2 * a)) fun i hi j hj => ?_)
  rw [Finset.mem_product] at hi hj
  have := hWa _ hi.1; have := hWa _ hi.2; have := hWa _ hj.1; have := hWa _ hj.2
  simp only [Set.mem_Icc] at *
  rw [abs_le]; constructor <;> linarith

/-! ### `R` in logarithmic coordinates -/
lemma Rv_exp (W : Finset ℝ) (τ : ℝ) : Rv W (Real.exp τ) = G W (fun t => t) τ := by
  unfold Rv G; refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos τ).ne'),
    ← Complex.ofReal_log (Real.exp_pos τ).le, Real.log_exp]
  unfold E; congr 1; push_cast; ring

/-! ### The bumps and `g = ψ_in |R|²` (from P101 Part4) -/
theorem ψin_nonneg (x : ℝ) : 0 ≤ ψin x := ψinb.nonneg

theorem ψin_le_one (x : ℝ) : ψin x ≤ 1 := ψinb.le_one

theorem φ_nonneg (x : ℝ) : 0 ≤ φ x := φb.nonneg

theorem φ_hcs : HasCompactSupport φ := φb.hasCompactSupport

theorem ψin_pos_of_ne {y : ℝ} (h : ψin y ≠ 0) : 1 / 8 < y ∧ y < 33 / 8 := by
  have : y ∈ Function.support ψinb := h
  rw [ψinb.support_eq, Metric.mem_ball, Real.dist_eq] at this
  have h2 : ψinb.rOut = 2 := rfl
  rw [h2, abs_lt] at this
  constructor <;> linarith [this.1, this.2]

theorem ψin_eq_one {y : ℝ} (h1 : 1 / 4 ≤ y) (h2 : y ≤ 4) : ψin y = 1 := by
  apply ψinb.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  have h3 : ψinb.rIn = 15 / 8 := rfl
  rw [h3, abs_le]; constructor <;> linarith

theorem Rv_continuousAt (W : Finset ℝ) {y : ℝ} (hy : 0 < y) : ContinuousAt (Rv W) y := by
  unfold Rv
  have hs : (y : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hy
  fun_prop (disch := exact hs)

noncomputable def gR (W : Finset ℝ) (y : ℝ) : ℝ := ψin y * ‖Rv W y‖ ^ 2

theorem gR_nonneg (W : Finset ℝ) (y : ℝ) : 0 ≤ gR W y :=
  mul_nonneg (ψin_nonneg y) (by positivity)

theorem gR_continuous (W : Finset ℝ) : Continuous (gR W) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : 0 < y
  · exact (ψinb.continuous.continuousAt).mul ((Rv_continuousAt W hy).norm.pow 2)
  · have hev : gR W =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show y < 1 / 8 by linarith)] with z hz
      have : ψin z = 0 := by
        by_contra h
        exact absurd (ψin_pos_of_ne h).1 (not_lt.2 (le_of_lt hz))
      simp [gR, this]
    exact (continuousAt_const).congr hev.symm

theorem gR_hcs (W : Finset ℝ) : HasCompactSupport (gR W) :=
  ψinb.hasCompactSupport.mul_right

noncomputable def kρ (ρ : ℝ) (z : ℝ) : ℝ := ρ⁻¹ * φ (-ρ⁻¹ * z)

theorem kρ_continuous (ρ : ℝ) : Continuous (kρ ρ) :=
  continuous_const.mul (φb.continuous.comp (continuous_const.mul continuous_id))

theorem kρ_hcs {ρ : ℝ} (hρ : ρ ≠ 0) : HasCompactSupport (kρ ρ) := by
  have : HasCompactSupport (fun z : ℝ => φ (-ρ⁻¹ * z)) := by
    simpa [smul_eq_mul] using φ_hcs.comp_smul (neg_ne_zero.2 (inv_ne_zero hρ))
  exact this.mul_left

theorem integral_kρ {ρ : ℝ} (hρ : 0 < ρ) : ∫ z, kρ ρ z = ∫ z, φ z := by
  unfold kρ
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun z => φ z), inv_neg, inv_inv, abs_neg,
    abs_of_pos hρ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hρ.ne', one_mul]

theorem fP_eq (W : Finset ℝ) (ρ : ℝ) :
    fP W ρ = fun x => ψout x * (gR W ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] kρ ρ) x := by
  funext x
  simp only [fP, convolution_def, ContinuousLinearMap.mul_apply', kρ, gR,
    ← integral_const_mul]
  congr 1; funext y
  rw [show (y - x) / ρ = -ρ⁻¹ * (x - y) by ring]
  ring

theorem kρ_nonneg {ρ : ℝ} (hρ : 0 < ρ) (z : ℝ) : 0 ≤ kρ ρ z :=
  mul_nonneg (inv_nonneg.2 hρ.le) (φ_nonneg _)

/-! ### Change of variables `y = e^τ` -/
lemma exp3_le : Real.exp 3 ≤ 21 := by
  have h := Real.exp_one_lt_d9
  have e : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h0 := Real.exp_pos 1
  rw [e]; nlinarith

lemma exp3_ge : 8 ≤ Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [e]; nlinarith

lemma int_exp (F B : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ y, 0 ≤ F y)
    (hs : ∀ y, F y ≠ 0 → 1 / 8 < y ∧ y < 33 / 8) (hB : ∀ τ, F (Real.exp τ) ≤ B τ)
    (hBi : IntervalIntegrable B volume (-3) 3) :
    ∫ y, F y ≤ 21 * ∫ τ in (-3 : ℝ)..3, B τ := by
  have hlo : Real.exp (-3) ≤ 1 / 8 := by
    rw [Real.exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; exact exp3_ge)
  have hhi : 33 / 8 ≤ Real.exp 3 := le_trans (by norm_num) exp3_ge
  have h1 : ∫ y, F y = ∫ y in Real.exp (-3)..Real.exp 3, F y := by
    rw [intervalIntegral.integral_of_le (Real.exp_le_exp.2 (by norm_num)),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro y hy
    by_contra h
    exact hy ⟨by linarith [(hs y h).1], by linarith [(hs y h).2]⟩
  have h2 : ∫ y in Real.exp (-3)..Real.exp 3, F y =
      ∫ τ in (-3 : ℝ)..3, (F ∘ Real.exp) τ * Real.exp τ :=
    (intervalIntegral.integral_comp_mul_deriv (fun x _ => Real.hasDerivAt_exp x)
      Real.continuous_exp.continuousOn hF).symm
  rw [h1, h2, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact ((hF.comp Real.continuous_exp).mul Real.continuous_exp).intervalIntegrable _ _
  · exact hBi.const_mul 21
  · intro τ hτ
    have e3 : Real.exp τ ≤ 21 := (Real.exp_le_exp.2 hτ.2).trans exp3_le
    have := hF0 (Real.exp τ); have := hB τ
    simp only [Function.comp]
    nlinarith [Real.exp_pos τ]

/-! ### Cauchy–Schwarz inside the convolution -/
lemma conv_sq_le (g k : ℝ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hk : Continuous k) (hkc : HasCompactSupport k) (hk0 : ∀ z, 0 ≤ k z)
    (hK : 0 < ∫ z, k z) (x : ℝ) :
    ((g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] k) x) ^ 2 ≤
      (∫ z, k z) * ((fun y => g y ^ 2) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] k) x := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  set K := ∫ z, k z
  set h := ∫ t, g t * k (x - t)
  set Q := ∫ t, g t ^ 2 * k (x - t)
  have hk' : Continuous fun t => k (x - t) := hk.comp (continuous_const.sub continuous_id)
  have ik : Integrable (fun t => k (x - t)) :=
    (hk.integrable_of_hasCompactSupport hkc).comp_sub_left x
  have ig : Integrable (fun t => g t * k (x - t)) :=
    (hg.mul hk').integrable_of_hasCompactSupport hgc.mul_right
  have ig2 : Integrable (fun t => g t ^ 2 * k (x - t)) := by
    have e : (fun t => g t ^ 2 * k (x - t)) = g * fun t => g t * k (x - t) := by
      funext t; simp only [Pi.mul_apply]; ring
    rw [e]; exact (hg.mul (hg.mul hk')).integrable_of_hasCompactSupport hgc.mul_right
  have hpt : ∀ t, 2 * h * (g t * k (x - t)) ≤
      h ^ 2 / K * k (x - t) + K * (g t ^ 2 * k (x - t)) := by
    intro t
    have e : h ^ 2 / K * k (x - t) + K * (g t ^ 2 * k (x - t)) - 2 * h * (g t * k (x - t)) =
        (h - K * g t) ^ 2 / K * k (x - t) := by field_simp; ring
    have : 0 ≤ (h - K * g t) ^ 2 / K * k (x - t) :=
      mul_nonneg (div_nonneg (sq_nonneg _) hK.le) (hk0 _)
    linarith
  have hi := integral_mono (ig.const_mul (2 * h)) ((ik.const_mul (h ^ 2 / K)).add (ig2.const_mul K))
    hpt
  simp only [Pi.add_apply] at hi
  rw [integral_add (ik.const_mul _) (ig2.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_sub_left_eq_self k volume x] at hi
  have : h ^ 2 / K * K = h ^ 2 := div_mul_cancel₀ _ hK.ne'
  nlinarith

/-! ### P7 -/
theorem moments (η : ℝ) (hη : 0 < η) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₀ ≤ T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      RL2 W ≤ A * T ^ η * W.card ∧
      ∀ ρ : ℝ, 0 < ρ → (∫ u, fP W ρ u) ≤ A * T ^ η * W.card ∧
        (∫ u, fP W ρ u ^ 2) ≤ A * T ^ η * (energy W : ℝ) := by
  have hKpos : 0 < ∫ z, φ z := φb.integral_pos
  set Kφ := ∫ z, φ z with hKφ
  have hc0 : (0 : ℝ) ≤ 4 ^ η / η := by positivity
  refine ⟨(1 + Kφ + Kφ ^ 2) * 1512 * (1 + 4 ^ η / η), 1, by positivity, ?_⟩
  intro T hT W a hW hWa
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hTη : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  set Lg := 1 + 4 ^ η / η with hLg
  have hLg0 : 0 ≤ Lg := by positivity
  have hlog : 1 + Real.log (2 * T + 2) ≤ Lg * T ^ η := by
    have h1 := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 2 * T + 2) hη
    have h2 : (2 * T + 2) ^ η ≤ (4 * T) ^ η :=
      Real.rpow_le_rpow (by positivity) (by linarith) hη.le
    rw [Real.mul_rpow (by norm_num) hT0] at h2
    have h3 := div_le_div_of_nonneg_right h2 hη.le
    have e1 : 4 ^ η * T ^ η / η = 4 ^ η / η * T ^ η := by ring
    have e2 : Lg * T ^ η = T ^ η + 4 ^ η / η * T ^ η := by rw [hLg]; ring
    linarith
  have hlog1 : 1 + Real.log (T + 2) ≤ Lg * T ^ η := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < T + 2) (by linarith : T + 2 ≤ 2 * T + 2)
    linarith
  have hcard : (0 : ℝ) ≤ W.card := by positivity
  have hE : (0 : ℝ) ≤ energy W := by positivity
  have hLT : 0 ≤ Lg * T ^ η := by positivity
  -- the two mean values
  have hsupp : ∀ y, gR W y ≠ 0 → 1 / 8 < y ∧ y < 33 / 8 :=
    fun y h => ψin_pos_of_ne fun h0 => h (by simp [gR, h0])
  have hI2 : ∫ y, gR W y ≤ 756 * W.card * (Lg * T ^ η) := by
    have h1 := int_exp (gR W) (fun τ => ‖G W (fun t => t) τ‖ ^ 2) (gR_continuous W) (gR_nonneg W)
      hsupp (fun τ => by
        rw [gR, Rv_exp]; exact mul_le_of_le_one_left (by positivity) (ψin_le_one _))
      ((by have := continuous_G W (fun t : ℝ => t); fun_prop :
        Continuous fun τ => ‖G W (fun t : ℝ => t) τ‖ ^ 2).intervalIntegrable _ _)
    have h3 := mv3 W (fun t : ℝ => t)
    have h4 := MV1 W hW a T hT0 hWa
    have h5 : 12 * (W.card : ℝ) * (1 + Real.log (T + 2)) ≤ 12 * W.card * (Lg * T ^ η) :=
      mul_le_mul_of_nonneg_left hlog1 (by positivity)
    linarith
  have hI4 : ∫ y, gR W y ^ 2 ≤ 1512 * (energy W : ℝ) * (Lg * T ^ η) := by
    have h1 := int_exp (fun y => gR W y ^ 2)
      (fun τ => ‖G (W ×ˢ W) (fun p : ℝ × ℝ => p.1 + p.2) τ‖ ^ 2) ((gR_continuous W).pow 2)
      (fun y => by positivity)
      (fun y h => hsupp y fun h0 => h (by simp [h0])) (fun τ => by
        rw [gR, Rv_exp, G_WW, norm_pow]
        exact pow_le_pow_left₀ (mul_nonneg (ψin_nonneg _) (by positivity))
          (mul_le_of_le_one_left (by positivity) (ψin_le_one _)) 2)
      ((by have := continuous_G (W ×ˢ W) (fun p : ℝ × ℝ => p.1 + p.2); fun_prop :
        Continuous fun τ => ‖G (W ×ˢ W) (fun p : ℝ × ℝ => p.1 + p.2) τ‖ ^ 2).intervalIntegrable _ _)
    have h3 := mv3 (W ×ˢ W) (fun p : ℝ × ℝ => p.1 + p.2)
    have h4 := MV2 W a T hT0 hWa
    have h5 : 12 * (2 * (energy W : ℝ)) * (1 + Real.log (2 * T + 2)) ≤
        12 * (2 * (energy W : ℝ)) * (Lg * T ^ η) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    linarith
  have igR : Integrable (gR W) := (gR_continuous W).integrable_of_hasCompactSupport (gR_hcs W)
  have hA1 : 756 * W.card * (Lg * T ^ η) ≤
      (1 + Kφ + Kφ ^ 2) * 1512 * Lg * T ^ η * W.card := by
    have : (756 : ℝ) ≤ (1 + Kφ + Kφ ^ 2) * 1512 := by nlinarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hLT hcard)
    linarith
  refine ⟨?_, fun ρ hρ => ?_⟩
  · -- `∫_{1/2}^2 |R|² ≤ ∫ g`
    have e : RL2 W = ∫ v in Set.Icc (1 / 2 : ℝ) 2, gR W v := by
      unfold RL2
      refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
      rw [gR, ψin_eq_one (by linarith [hv.1]) (by linarith [hv.2]), one_mul]
    rw [e]
    exact (setIntegral_le_integral igR (Filter.Eventually.of_forall (gR_nonneg W))).trans
      (hI2.trans hA1)
  -- the convolution
  have ik : Integrable (kρ ρ) :=
    (kρ_continuous ρ).integrable_of_hasCompactSupport (kρ_hcs hρ.ne')
  set hc := gR W ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] kρ ρ with hhc
  have hcnn : ∀ x, 0 ≤ hc x := fun x => by
    rw [hhc, convolution_def]
    exact integral_nonneg fun t => mul_nonneg (gR_nonneg W t) (kρ_nonneg hρ _)
  have hfP : ∀ x, fP W ρ x = ψout x * hc x := fun x => by rw [fP_eq]
  have hfP0 : ∀ x, 0 ≤ fP W ρ x := fun x => by
    rw [hfP]; exact mul_nonneg ψoutb.nonneg (hcnn x)
  have hfPle : ∀ x, fP W ρ x ≤ hc x := fun x => by
    rw [hfP]; exact mul_le_of_le_one_left (hcnn x) ψoutb.le_one
  have hK : ∫ z, kρ ρ z = Kφ := integral_kρ hρ
  constructor
  · have h1 : ∫ x, hc x = (∫ y, gR W y) * Kφ := by
      rw [hhc, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) igR ik, ContinuousLinearMap.mul_apply', hK]
    have h2 := integral_mono_of_nonneg (Filter.Eventually.of_forall hfP0)
      (igR.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) ik)
      (Filter.Eventually.of_forall hfPle)
    rw [h1] at h2
    have h3 : (∫ y, gR W y) * Kφ ≤ 756 * W.card * (Lg * T ^ η) * Kφ :=
      mul_le_mul_of_nonneg_right hI2 hKpos.le
    have : (756 : ℝ) * Kφ ≤ (1 + Kφ + Kφ ^ 2) * 1512 := by nlinarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hLT hcard)
    nlinarith
  · have igR2 : Integrable fun y => gR W y ^ 2 :=
      ((gR_continuous W).pow 2).integrable_of_hasCompactSupport (by
        rw [sq]; exact (gR_hcs W).mul_right)
    have hpt : ∀ x, fP W ρ x ^ 2 ≤
        Kφ * ((fun y => gR W y ^ 2) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] kρ ρ) x := by
      intro x
      have h1 := conv_sq_le (gR W) (kρ ρ) (gR_continuous W) (gR_hcs W) (kρ_continuous ρ)
        (kρ_hcs hρ.ne') (kρ_nonneg hρ) (by rw [hK]; exact hKpos) x
      rw [hK] at h1
      exact (pow_le_pow_left₀ (hfP0 x) (hfPle x) 2).trans h1
    have h2 := integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg (fP W ρ x))
      ((igR2.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) ik).const_mul Kφ)
      (Filter.Eventually.of_forall hpt)
    rw [integral_const_mul, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) igR2 ik, ContinuousLinearMap.mul_apply', hK] at h2
    have h3 : Kφ * ((∫ y, gR W y ^ 2) * Kφ) ≤
        Kφ * (1512 * (energy W : ℝ) * (Lg * T ^ η) * Kφ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hI4 hKpos.le) hKpos.le
    have : (1512 : ℝ) * Kφ ^ 2 ≤ (1 + Kφ + Kφ ^ 2) * 1512 := by nlinarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hLT hE)
    nlinarith

end GuthMaynard.P101.Part5
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
/-! ## P7: moments -/
alias moments := GuthMaynard.P101.Part5.moments

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part6
open GuthMaynard GuthMaynard.P101 MeasureTheory Set
open scoped ENNReal
/-! ### Finite sums and `J` -/
/-- The inner sum of `J`. -/
noncomputable def gsum (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ dyadic M₁ ∪ (dyadic M₁).map (Equiv.neg ℤ).toEmbedding, ∑ m₂ ∈ dyadic M₂,
    ∑ m₃ ∈ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋, f ((m₁ * u + m₃) / m₂)

/-- The index set of `gsum`. -/
noncomputable def tri (K M₁ M₂ M₃ : ℝ) : Finset (ℤ × ℤ × ℤ) :=
  (dyadic M₁ ∪ (dyadic M₁).map (Equiv.neg ℤ).toEmbedding) ×ˢ
    (dyadic M₂ ×ˢ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋)

theorem gsum_eq (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    gsum K M₁ M₂ M₃ f u = ∑ p ∈ tri K M₁ M₂ M₃, f ((p.1 * u + p.2.2) / p.2.1) := by
  simp only [gsum, tri, Finset.sum_product]

theorem gsum_nonneg (K M₁ M₂ M₃ : ℝ) {f : ℝ → ℝ} (hnn : ∀ u, 0 ≤ f u) (u : ℝ) :
    0 ≤ gsum K M₁ M₂ M₃ f u := by
  rw [gsum_eq]; exact Finset.sum_nonneg fun _ _ => hnn _

theorem gsum_cont (K M₁ M₂ M₃ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (gsum K M₁ M₂ M₃ f) := by
  unfold gsum; fun_prop

theorem lintegral_le_J {M K M₁ M₂ M₃ : ℝ} (f : ℝ → ℝ) (h₁ : M₁ ∈ Ioo 0 M) (h₂ : M₂ ∈ Ioo 0 M)
    (h₃ : M₃ ∈ Ioo 0 M) :
    ∫⁻ u, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) ≤ J M K f := by
  unfold J
  exact le_iSup₂_of_le M₁ h₁ (le_iSup₂_of_le M₂ h₂ (le_iSup₂_of_le M₃ h₃ le_rfl))

theorem sum_comp_le {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β) (τ : α → β)
    (hτ : Function.Injective τ) (hst : ∀ x ∈ s, τ x ∈ t) (F : β → ℝ) (hF : ∀ p, 0 ≤ F p) :
    ∑ x ∈ s, F (τ x) ≤ ∑ p ∈ t, F p := by
  rw [← Finset.sum_image (fun x _ y _ h => hτ h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hF p)
  intro p hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hp
  exact hst x hx

theorem sum_union_le {β : Type*} [DecidableEq β] (A B : Finset β) (F : β → ℝ)
    (hF : ∀ p, 0 ≤ F p) : ∑ p ∈ A ∪ B, F p ≤ ∑ p ∈ A, F p + ∑ p ∈ B, F p := by
  rw [← Finset.sum_union_inter]
  have : 0 ≤ ∑ p ∈ A ∩ B, F p := Finset.sum_nonneg fun p _ => hF p
  linarith

theorem mem_pm {M : ℝ} {z : ℤ} (h : |z| ∈ dyadic M) :
    z ∈ dyadic M ∪ (dyadic M).map (Equiv.neg ℤ).toEmbedding := by
  rcases abs_choice z with hz | hz
  · rw [hz] at h; exact Finset.mem_union_left _ h
  · rw [hz] at h
    exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨-z, h, by simp⟩)

theorem mem_grp {L : ℝ} {i₁ i : ℕ} {m : Fin 3 → ℤ} (hm : m ∈ grp L i₁ i) :
    |m 0| ∈ dyadic (scale i₁) ∧ |m 1| ∈ dyadic (scale i) ∧ |m 0| ≤ |m 1| ∧ |m 1| ≤ |m 2| ∧
      |m 2| ≤ 5 * |m 1| := by
  simp only [grp, ordBox, Finset.mem_filter] at hm
  exact ⟨hm.2.1, hm.2.2.1, hm.1.2.1, hm.1.2.2, hm.2.2.2⟩

theorem dyadic_bounds {M : ℝ} {z : ℤ} (h : z ∈ dyadic M) : M < z ∧ (z : ℝ) ≤ 2 * M := by
  simp only [dyadic, Finset.mem_Ioc] at h
  exact ⟨Int.floor_lt.1 h.1, Int.le_floor.1 h.2⟩

theorem mem_Icc_floor {B : ℝ} {z : ℤ} (h : |(z : ℝ)| ≤ B) : z ∈ Finset.Icc (-⌊B⌋) ⌊B⌋ := by
  rw [Finset.mem_Icc]
  have h1 : z ≤ ⌊B⌋ := Int.le_floor.2 (le_trans (le_abs_self _) h)
  have h2 : -z ≤ ⌊B⌋ := Int.le_floor.2 (by push_cast; exact le_trans (neg_le_abs _) h)
  omega

/-- Real-valued facts about a group member. -/
theorem grp_real {L : ℝ} {i₁ i : ℕ} {m : Fin 3 → ℤ} (hm : m ∈ grp L i₁ i) :
    scale i₁ < |(m 0 : ℝ)| ∧ scale i < |(m 1 : ℝ)| ∧ |(m 1 : ℝ)| ≤ 2 * scale i ∧
      |(m 0 : ℝ)| ≤ |(m 1 : ℝ)| ∧ |(m 1 : ℝ)| ≤ |(m 2 : ℝ)| ∧ |(m 2 : ℝ)| ≤ 5 * |(m 1 : ℝ)| := by
  obtain ⟨h0, h1, h01, h12, h2⟩ := mem_grp hm
  have a := dyadic_bounds h0
  have b := dyadic_bounds h1
  push_cast at a b
  refine ⟨a.1, b.1, b.2, ?_, ?_, ?_⟩
  · have : ((|m 0| : ℤ) : ℝ) ≤ ((|m 1| : ℤ) : ℝ) := by exact_mod_cast h01
    simpa using this
  · have : ((|m 1| : ℤ) : ℝ) ≤ ((|m 2| : ℤ) : ℝ) := by exact_mod_cast h12
    simpa using this
  · have : ((|m 2| : ℤ) : ℝ) ≤ ((5 * |m 1| : ℤ) : ℝ) := by exact_mod_cast h2
    simpa using this

theorem inj1 : Function.Injective fun m : Fin 3 → ℤ => (m 0, -m 1, m 2) := by
  intro a b h
  simp only [Prod.mk.injEq, neg_inj] at h
  funext j; fin_cases j <;> simp [h.1, h.2.1, h.2.2]

theorem inj2 : Function.Injective fun m : Fin 3 → ℤ => (-m 0, m 1, -m 2) := by
  intro a b h
  simp only [Prod.mk.injEq, neg_inj] at h
  funext j; fin_cases j <;> simp [h.1, h.2.1, h.2.2]

theorem inj3 : Function.Injective fun m : Fin 3 → ℤ => (m 2, -m 1, m 0) := by
  intro a b h
  simp only [Prod.mk.injEq, neg_inj] at h
  funext j; fin_cases j <;> simp [h.1, h.2.1, h.2.2]

theorem inj4 : Function.Injective fun m : Fin 3 → ℤ => (-m 2, m 1, -m 0) := by
  intro a b h
  simp only [Prod.mk.injEq, neg_inj] at h
  funext j; fin_cases j <;> simp [h.1, h.2.1, h.2.2]

theorem neg_div_swap (a b : ℝ) : a / -b = -a / b := by rw [div_neg, neg_div]

/-- `Y(v) ≤ 2 gsum`. -/
theorem sum_ym_le (L : ℝ) (i₁ i : ℕ) (f : ℝ → ℝ) (hnn : ∀ u, 0 ≤ f u) (v : ℝ) :
    ∑ m ∈ grp L i₁ i, f (ym m v) ≤ 2 * gsum 20 (scale i₁) (scale i) (scale i) f v := by
  classical
  have hM := scale_pos i
  rw [← Finset.sum_filter_add_sum_filter_not (grp L i₁ i) (fun m => m 1 < 0), two_mul, gsum_eq]
  set F : ℤ × ℤ × ℤ → ℝ := fun p => f ((p.1 * v + p.2.2) / p.2.1) with hFdef
  have hF : ∀ p, 0 ≤ F p := fun p => hnn _
  have h2 : ∀ m ∈ grp L i₁ i, m 2 ∈ Finset.Icc (-⌊20 * scale i⌋) ⌊20 * scale i⌋ ∧
      -m 2 ∈ Finset.Icc (-⌊20 * scale i⌋) ⌊20 * scale i⌋ := by
    intro m hm
    obtain ⟨-, -, b2, -, -, c⟩ := grp_real hm
    exact ⟨mem_Icc_floor (by linarith), mem_Icc_floor (by push_cast; rw [abs_neg]; linarith)⟩
  apply add_le_add
  · calc ∑ m ∈ (grp L i₁ i).filter (fun m => m 1 < 0), f (ym m v)
          = ∑ m ∈ (grp L i₁ i).filter (fun m => m 1 < 0), F (m 0, -m 1, m 2) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hFdef, ym]; push_cast; rfl
      _ ≤ _ := by
          refine sum_comp_le _ _ _ inj1 ?_ F hF
          intro m hm
          rw [Finset.mem_filter] at hm
          obtain ⟨h0, h1, -⟩ := mem_grp hm.1
          refine Finset.mem_product.2 ⟨mem_pm h0, Finset.mem_product.2 ⟨?_, (h2 m hm.1).1⟩⟩
          rw [abs_of_neg hm.2] at h1; exact h1
  · calc ∑ m ∈ (grp L i₁ i).filter (fun m => ¬ m 1 < 0), f (ym m v)
          = ∑ m ∈ (grp L i₁ i).filter (fun m => ¬ m 1 < 0), F (-m 0, m 1, -m 2) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hFdef, ym]; push_cast
          rw [neg_div_swap]; congr 2; ring
      _ ≤ _ := by
          refine sum_comp_le _ _ _ inj2 ?_ F hF
          intro m hm
          rw [Finset.mem_filter] at hm
          obtain ⟨h0, h1, -⟩ := mem_grp hm.1
          refine Finset.mem_product.2 ⟨mem_pm (by rw [abs_neg]; exact h0),
            Finset.mem_product.2 ⟨?_, (h2 m hm.1).2⟩⟩
          rw [abs_of_nonneg (not_lt.1 hm.2)] at h1; exact h1

/-- A set integral of a nonnegative function, bounded through its lower integral. -/
theorem setIntegral_le_of_lintegral {h : ℝ → ℝ} (h0 : ∀ v, 0 ≤ h v) {s : Set ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hl : ∫⁻ v in s, ENNReal.ofReal (h v) ≤ ENNReal.ofReal B) :
    ∫ v in s, h v ≤ B := by
  by_cases hi : Integrable h (volume.restrict s)
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hi.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hB hl
  · rw [integral_undef hi]; exact hB

theorem intY_le (L : ℝ) (i₁ i : ℕ) (f : ℝ → ℝ) (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u)
    (X : ℝ) (hX : 0 ≤ X) (hJ : J (20 * scale i) 20 f ≤ ENNReal.ofReal X) :
    ∫ v in Set.Icc (1 / 2 : ℝ) 2, (∑ m ∈ grp L i₁ i, f (ym m v)) ^ 2 ≤ 4 * X := by
  by_cases hne : (grp L i₁ i).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp; positivity
  obtain ⟨m, hm⟩ := hne
  have hM := scale_pos i
  obtain ⟨a0, -, b2, h01, -, -⟩ := grp_real hm
  have hM₁ : scale i₁ ∈ Ioo 0 (20 * scale i) := ⟨scale_pos _, by linarith⟩
  have hMM : scale i ∈ Ioo 0 (20 * scale i) := ⟨hM, by linarith⟩
  have hlin := lintegral_le_J (K := 20) f hM₁ hMM hMM
  set g := gsum 20 (scale i₁) (scale i) (scale i) f with hg
  have hpt : ∀ v, (∑ m ∈ grp L i₁ i, f (ym m v)) ^ 2 ≤ 4 * g v ^ 2 := by
    intro v
    have h1 := sum_ym_le L i₁ i f hnn v
    have h0 : 0 ≤ ∑ m ∈ grp L i₁ i, f (ym m v) := Finset.sum_nonneg fun _ _ => hnn _
    nlinarith
  refine setIntegral_le_of_lintegral (fun _ => sq_nonneg _) (by positivity) ?_
  calc ∫⁻ v in Icc (1 / 2 : ℝ) 2, ENNReal.ofReal ((∑ m ∈ grp L i₁ i, f (ym m v)) ^ 2)
      ≤ ∫⁻ v, ENNReal.ofReal ((∑ m ∈ grp L i₁ i, f (ym m v)) ^ 2) :=
        setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ v, ENNReal.ofReal 4 * ENNReal.ofReal (g v ^ 2) := lintegral_mono fun v => by
        rw [← ENNReal.ofReal_mul (by norm_num)]; exact ENNReal.ofReal_le_ofReal (hpt v)
    _ = ENNReal.ofReal 4 * ∫⁻ v, ENNReal.ofReal (g v ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal X := by gcongr; exact hlin.trans hJ
    _ = ENNReal.ofReal (4 * X) := (ENNReal.ofReal_mul (by norm_num)).symm

end GuthMaynard.P101.Part6
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
/-! ## P8: the `J`-sums and one group -/

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part6
open GuthMaynard GuthMaynard.P101 MeasureTheory Set
open scoped ENNReal
/-- The four dyadic blocks covering `(⌊M⌋, ⌊16M⌋]`. -/
theorem mem_t4 {M : ℝ} {z : ℤ} {r : ℤ × ℤ} (hz1 : ⌊M⌋ < |z|) (hz2 : |z| ≤ ⌊16 * M⌋)
    (hr : r ∈ dyadic M ×ˢ Finset.Icc (-⌊20 * M⌋) ⌊20 * M⌋) :
    (z, r) ∈ tri 20 M M M ∪ tri 20 (2 * M) M M ∪ tri 20 (4 * M) M M ∪ tri 20 (8 * M) M M := by
  have e2 : 2 * (2 * M) = 4 * M := by ring
  have e4 : 2 * (4 * M) = 8 * M := by ring
  have e8 : 2 * (8 * M) = 16 * M := by ring
  have key : ∀ c : ℝ, ⌊c⌋ < |z| → |z| ≤ ⌊2 * c⌋ → (z, r) ∈ tri 20 c M M := fun c h1 h2 =>
    Finset.mem_product.2 ⟨mem_pm (Finset.mem_Ioc.2 ⟨h1, h2⟩), hr⟩
  by_cases a1 : |z| ≤ ⌊2 * M⌋
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (key M hz1 a1)))
  by_cases a2 : |z| ≤ ⌊2 * (2 * M)⌋
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (key (2 * M) (not_le.1 a1) a2)))
  by_cases a3 : |z| ≤ ⌊2 * (4 * M)⌋
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (key (4 * M) (by rw [← e2]; exact not_le.1 a2) a3))
  · exact Finset.mem_union_right _
      (key (8 * M) (by rw [← e4]; exact not_le.1 a3) (by rw [e8]; exact hz2))

theorem sum_t4_le {M : ℝ} (F : ℤ × ℤ × ℤ → ℝ) (hF : ∀ p, 0 ≤ F p) :
    ∑ p ∈ tri 20 M M M ∪ tri 20 (2 * M) M M ∪ tri 20 (4 * M) M M ∪ tri 20 (8 * M) M M, F p ≤
      ∑ p ∈ tri 20 M M M, F p + ∑ p ∈ tri 20 (2 * M) M M, F p +
        ∑ p ∈ tri 20 (4 * M) M M, F p + ∑ p ∈ tri 20 (8 * M) M M, F p := by
  classical
  refine (sum_union_le _ _ F hF).trans (add_le_add ?_ le_rfl)
  refine (sum_union_le _ _ F hF).trans (add_le_add ?_ le_rfl)
  exact sum_union_le _ _ F hF

/-- The `x`-sum after `u = 1/v`, bounded by four `gsum`s. -/
theorem sum_xm_le (L : ℝ) (i₁ i : ℕ) (f : ℝ → ℝ) (hnn : ∀ u, 0 ≤ f u) (u : ℝ) :
    ∑ m ∈ grp L i₁ i, f ((m 2 * u + m 0) / (-(m 1 : ℝ))) ≤
      2 * (gsum 20 (scale i) (scale i) (scale i) f u + gsum 20 (2 * scale i) (scale i) (scale i) f u +
        gsum 20 (4 * scale i) (scale i) (scale i) f u +
          gsum 20 (8 * scale i) (scale i) (scale i) f u) := by
  classical
  set M := scale i with hMdef
  have hM : 0 < M := scale_pos i
  set F : ℤ × ℤ × ℤ → ℝ := fun p => f ((p.1 * u + p.2.2) / p.2.1) with hFdef
  have hF : ∀ p, 0 ≤ F p := fun p => hnn _
  simp only [gsum_eq]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_t4_le F hF) (by norm_num))
  rw [← Finset.sum_filter_add_sum_filter_not (grp L i₁ i) (fun m => m 1 < 0), two_mul]
  have hz : ∀ m ∈ grp L i₁ i, ⌊M⌋ < |m 2| ∧ |m 2| ≤ ⌊16 * M⌋ ∧
      m 0 ∈ Finset.Icc (-⌊20 * M⌋) ⌊20 * M⌋ ∧ -m 0 ∈ Finset.Icc (-⌊20 * M⌋) ⌊20 * M⌋ := by
    intro m hm
    obtain ⟨-, h1, -, h12, -⟩ := mem_grp hm
    obtain ⟨-, -, b2, a01, -, c⟩ := grp_real hm
    have hfl : ⌊M⌋ < |m 1| := (Finset.mem_Ioc.1 h1).1
    refine ⟨by omega, Int.le_floor.2 ?_, mem_Icc_floor (by linarith),
      mem_Icc_floor (by push_cast; rw [abs_neg]; linarith)⟩
    push_cast; linarith
  apply add_le_add
  · calc ∑ m ∈ (grp L i₁ i).filter (fun m => m 1 < 0), f ((m 2 * u + m 0) / (-(m 1 : ℝ)))
          = ∑ m ∈ (grp L i₁ i).filter (fun m => m 1 < 0), F (m 2, -m 1, m 0) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hFdef]; push_cast; rfl
      _ ≤ _ := by
          refine sum_comp_le _ _ _ inj3 ?_ F hF
          intro m hm
          rw [Finset.mem_filter] at hm
          obtain ⟨-, h1, -⟩ := mem_grp hm.1
          obtain ⟨z1, z2, z3, -⟩ := hz m hm.1
          refine mem_t4 z1 z2 (Finset.mem_product.2 ⟨?_, z3⟩)
          rw [abs_of_neg hm.2] at h1; exact h1
  · calc ∑ m ∈ (grp L i₁ i).filter (fun m => ¬ m 1 < 0), f ((m 2 * u + m 0) / (-(m 1 : ℝ)))
          = ∑ m ∈ (grp L i₁ i).filter (fun m => ¬ m 1 < 0), F (-m 2, m 1, -m 0) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [hFdef]; push_cast
          rw [neg_div_swap]; congr 2; ring
      _ ≤ _ := by
          refine sum_comp_le _ _ _ inj4 ?_ F hF
          intro m hm
          rw [Finset.mem_filter] at hm
          obtain ⟨-, h1, -⟩ := mem_grp hm.1
          obtain ⟨z1, z2, -, z4⟩ := hz m hm.1
          refine mem_t4 (by rw [abs_neg]; exact z1) (by rw [abs_neg]; exact z2)
            (Finset.mem_product.2 ⟨?_, z4⟩)
          rw [abs_of_nonneg (not_lt.1 hm.2)] at h1; exact h1

theorem image_inv_Icc' : (fun x : ℝ => x⁻¹) '' Icc (1 / 2 : ℝ) 2 = Icc (1 / 2) 2 := by
  ext y; constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have hx0 : 0 < x := by linarith
    constructor
    · rw [le_inv_comm₀ (by norm_num) hx0]; norm_num; linarith
    · rw [inv_le_comm₀ hx0 (by norm_num)]; norm_num; linarith
  · rintro ⟨hy1, hy2⟩
    have hy0 : 0 < y := by linarith
    refine ⟨y⁻¹, ⟨?_, ?_⟩, inv_inv y⟩
    · rw [le_inv_comm₀ (by norm_num) hy0]; norm_num; linarith
    · rw [inv_le_comm₀ hy0 (by norm_num)]; norm_num; linarith

/-- `∫_{1/2}^2 G(1/v) dv ≤ 4 ∫_{1/2}^2 G` for `G ≥ 0`. -/
theorem lintegral_inv_le (G : ℝ → ℝ≥0∞) :
    ∫⁻ v in Icc (1 / 2 : ℝ) 2, G v⁻¹ ≤ ENNReal.ofReal 4 * ∫⁻ u in Icc (1 / 2 : ℝ) 2, G u := by
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (s := Icc (1 / 2 : ℝ) 2)
    (f := fun x : ℝ => x⁻¹) (f' := fun x => -(x ^ 2)⁻¹) measurableSet_Icc
    (fun x hx => (hasDerivAt_inv (by linarith [hx.1] : x ≠ 0)).hasDerivWithinAt)
    inv_injective.injOn G
  rw [image_inv_Icc'] at hcv
  rw [hcv, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun x hx => ?_
  have hx0 : 0 < x := by linarith [hx.1]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
  refine le_mul_of_one_le_left (by positivity) ?_
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [abs_neg, abs_of_pos (by positivity)]
  have : x ^ 2 ≤ 4 := by nlinarith [hx.2]
  rw [le_mul_inv_iff₀ (by positivity)]; linarith

theorem intX_le (L : ℝ) (i₁ i : ℕ) (f : ℝ → ℝ) (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u)
    (X : ℝ) (hX : 0 ≤ X) (hJ : J (20 * scale i) 20 f ≤ ENNReal.ofReal X) :
    ∫ v in Set.Icc (1 / 2 : ℝ) 2, (∑ m ∈ grp L i₁ i, f (xm m v)) ^ 2 ≤ 256 * X := by
  set M := scale i with hMdef
  have hM : 0 < M := scale_pos i
  set H : ℝ → ℝ := fun u => ∑ m ∈ grp L i₁ i, f ((m 2 * u + m 0) / (-(m 1 : ℝ))) with hH
  have hgJ : ∀ c : ℝ, 0 < c → c < 20 →
      ∫⁻ u, ENNReal.ofReal (gsum 20 (c * M) M M f u ^ 2) ≤ ENNReal.ofReal X := fun c h0 h1 =>
    (lintegral_le_J (K := 20) f ⟨by positivity, by nlinarith⟩ ⟨hM, by linarith⟩
      ⟨hM, by linarith⟩).trans hJ
  have hmeas : ∀ c : ℝ, Measurable fun u => ENNReal.ofReal (gsum 20 c M M f u ^ 2) := fun c =>
    ((gsum_cont 20 c M M hf).pow 2).measurable.ennreal_ofReal
  have hpt : ∀ u, H u ^ 2 ≤ 16 * (gsum 20 M M M f u ^ 2 + gsum 20 (2 * M) M M f u ^ 2 +
      gsum 20 (4 * M) M M f u ^ 2 + gsum 20 (8 * M) M M f u ^ 2) := by
    intro u
    have h1 : H u ≤ 2 * (gsum 20 M M M f u + gsum 20 (2 * M) M M f u +
      gsum 20 (4 * M) M M f u + gsum 20 (8 * M) M M f u) := sum_xm_le L i₁ i f hnn u
    have h0 : 0 ≤ H u := Finset.sum_nonneg fun _ _ => hnn _
    have a1 := gsum_nonneg 20 M M M hnn u
    have a2 := gsum_nonneg 20 (2 * M) M M hnn u
    have a3 := gsum_nonneg 20 (4 * M) M M hnn u
    have a4 := gsum_nonneg 20 (8 * M) M M hnn u
    set x1 := gsum 20 M M M f u
    set x2 := gsum 20 (2 * M) M M f u
    set x3 := gsum 20 (4 * M) M M f u
    set x4 := gsum 20 (8 * M) M M f u
    have hs : (x1 + x2 + x3 + x4) ^ 2 ≤ 4 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2) := by
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - x3), sq_nonneg (x1 - x4),
        sq_nonneg (x2 - x3), sq_nonneg (x2 - x4), sq_nonneg (x3 - x4)]
    have : H u ^ 2 ≤ (2 * (x1 + x2 + x3 + x4)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    nlinarith
  have hHl : ∫⁻ u, ENNReal.ofReal (H u ^ 2) ≤ ENNReal.ofReal (64 * X) := by
    calc ∫⁻ u, ENNReal.ofReal (H u ^ 2)
        ≤ ∫⁻ u, ENNReal.ofReal 16 * (ENNReal.ofReal (gsum 20 M M M f u ^ 2) +
            ENNReal.ofReal (gsum 20 (2 * M) M M f u ^ 2) +
            ENNReal.ofReal (gsum 20 (4 * M) M M f u ^ 2) +
            ENNReal.ofReal (gsum 20 (8 * M) M M f u ^ 2)) := lintegral_mono fun u => by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (hpt u)
      _ = ENNReal.ofReal 16 * ((∫⁻ u, ENNReal.ofReal (gsum 20 M M M f u ^ 2)) +
            (∫⁻ u, ENNReal.ofReal (gsum 20 (2 * M) M M f u ^ 2)) +
            (∫⁻ u, ENNReal.ofReal (gsum 20 (4 * M) M M f u ^ 2)) +
            ∫⁻ u, ENNReal.ofReal (gsum 20 (8 * M) M M f u ^ 2)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ (hmeas _),
            lintegral_add_right _ (hmeas _), lintegral_add_right _ (hmeas _)]
      _ ≤ ENNReal.ofReal 16 * (ENNReal.ofReal X + ENNReal.ofReal X + ENNReal.ofReal X +
            ENNReal.ofReal X) := by
          gcongr
          · simpa using hgJ 1 (by norm_num) (by norm_num)
          · exact hgJ 2 (by norm_num) (by norm_num)
          · exact hgJ 4 (by norm_num) (by norm_num)
          · exact hgJ 8 (by norm_num) (by norm_num)
      _ = ENNReal.ofReal (64 * X) := by
          rw [← ENNReal.ofReal_add hX hX, ← ENNReal.ofReal_add (by positivity) hX,
            ← ENNReal.ofReal_add (by positivity) hX, ← ENNReal.ofReal_mul (by norm_num)]
          ring_nf
  refine setIntegral_le_of_lintegral (fun _ => sq_nonneg _) (by positivity) ?_
  calc ∫⁻ v in Icc (1 / 2 : ℝ) 2, ENNReal.ofReal ((∑ m ∈ grp L i₁ i, f (xm m v)) ^ 2)
      = ∫⁻ v in Icc (1 / 2 : ℝ) 2, ENNReal.ofReal (H v⁻¹ ^ 2) := by
        refine setLIntegral_congr_fun measurableSet_Icc fun v hv => ?_
        have hv0 : v ≠ 0 := by linarith [hv.1]
        congr 2
        refine Finset.sum_congr rfl fun m _ => ?_
        congr 1
        unfold xm
        rw [div_mul_eq_div_div_swap]; congr 1; field_simp; ring
    _ ≤ ENNReal.ofReal 4 * ∫⁻ u in Icc (1 / 2 : ℝ) 2, ENNReal.ofReal (H u ^ 2) :=
        lintegral_inv_le fun u => ENNReal.ofReal (H u ^ 2)
    _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (64 * X) := by
        gcongr; exact (setLIntegral_le_lintegral _ _).trans hHl
    _ = ENNReal.ofReal (256 * X) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]; ring_nf

/-! ### The local bound (P5) -/
theorem φ_nonneg (x : ℝ) : 0 ≤ φ x := φb.nonneg

theorem ψin_nonneg (x : ℝ) : 0 ≤ ψin x := ψinb.nonneg

theorem ψin_hcs : HasCompactSupport ψin := ψinb.hasCompactSupport

theorem ψin_pos_of_ne {y : ℝ} (h : ψin y ≠ 0) : 1 / 8 < y ∧ y < 33 / 8 := by
  have : y ∈ Function.support ψinb := h
  rw [ψinb.support_eq, Metric.mem_ball, Real.dist_eq] at this
  have h2 : ψinb.rOut = 2 := rfl
  rw [h2, abs_lt] at this
  constructor <;> linarith [this.1, this.2]

theorem ψin_eq_one {y : ℝ} (h1 : 1 / 4 ≤ y) (h2 : y ≤ 4) : ψin y = 1 := by
  apply ψinb.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  have h3 : ψinb.rIn = 15 / 8 := rfl
  rw [h3, abs_le]; constructor <;> linarith

theorem ψout_eq_one {y : ℝ} (h1 : 1 / 8 ≤ y) (h2 : y ≤ 8) : ψout y = 1 := by
  apply ψoutb.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  have h3 : ψoutb.rIn = 63 / 16 := rfl
  rw [h3, abs_le]; constructor <;> linarith

theorem φ_eq_one {y : ℝ} (h : |y| ≤ 2) : φ y = 1 := by
  apply φb.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact h

theorem norm_Rv_le (W : Finset ℝ) {y : ℝ} (hy : 0 < y) : ‖Rv W y‖ ≤ W.card := by
  unfold Rv
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ t : ℝ, ‖(y : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := fun t => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]; simp
  simp [h1]

theorem Rv_continuousAt (W : Finset ℝ) {y : ℝ} (hy : 0 < y) : ContinuousAt (Rv W) y := by
  unfold Rv
  have hs : (y : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hy
  fun_prop (disch := exact hs)

theorem measurable_Rv (W : Finset ℝ) : Measurable (Rv W) := by
  unfold Rv; fun_prop

noncomputable def gR (W : Finset ℝ) (y : ℝ) : ℝ := ψin y * ‖Rv W y‖ ^ 2

theorem gR_continuous (W : Finset ℝ) : Continuous (gR W) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : 0 < y
  · exact (ψinb.continuous.continuousAt).mul ((Rv_continuousAt W hy).norm.pow 2)
  · have hev : gR W =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show y < 1 / 8 by linarith)] with z hz
      have : ψin z = 0 := by
        by_contra h
        exact absurd (ψin_pos_of_ne h).1 (not_lt.2 (le_of_lt hz))
      simp [gR, this]
    exact (continuousAt_const).congr hev.symm

/-- The integrand of `f` at `x`. -/
noncomputable def Φx (W : Finset ℝ) (ρ x y : ℝ) : ℝ := φ ((y - x) / ρ) * ψin y * ‖Rv W y‖ ^ 2

theorem Φx_nonneg (W : Finset ℝ) (ρ x y : ℝ) : 0 ≤ Φx W ρ x y :=
  mul_nonneg (mul_nonneg (φ_nonneg _) (ψin_nonneg _)) (by positivity)

theorem Φx_integrable (W : Finset ℝ) (ρ x : ℝ) : Integrable (Φx W ρ x) := by
  have e : Φx W ρ x = fun y => φ ((y - x) / ρ) * gR W y := by
    funext y; simp only [Φx, gR, mul_assoc]
  rw [e]
  refine Continuous.integrable_of_hasCompactSupport ?_ (ψin_hcs.mul_right.mul_left)
  exact ((φb.continuous.comp (by fun_prop)).mul (gR_continuous W))

theorem integral_Φx (W : Finset ℝ) {ρ x : ℝ} (hρ : 0 < ρ) (hx : ψout x = 1) :
    ∫ y, Φx W ρ x y = ρ * fP W ρ x := by
  unfold fP Φx
  rw [hx, one_mul, ← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]

theorem integrable_Icc {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |f x| ≤ C) : Integrable f (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
  Integrable.of_bound hf.aestronglyMeasurable C ((ae_restrict_iff' measurableSet_Icc).2
    (Filter.Eventually.of_forall fun x hx => by rw [Real.norm_eq_abs]; exact hC x hx))

theorem memLp_Icc {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |f x| ≤ C) : MemLp f 2 (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
  MemLp.of_bound hf.aestronglyMeasurable C ((ae_restrict_iff' measurableSet_Icc).2
    (Filter.Eventually.of_forall fun x hx => by rw [Real.norm_eq_abs]; exact hC x hx))

/-- Cauchy–Schwarz on `[1/2, 2]` for bounded measurable functions. -/
theorem cs_Icc {g h : ℝ → ℝ} (hg : Measurable g) (hh : Measurable h) (g0 : ∀ x, 0 ≤ g x)
    (h0 : ∀ x, 0 ≤ h x) {C D : ℝ} (hgC : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |g x| ≤ C)
    (hhD : ∀ x ∈ Icc (1 / 2 : ℝ) 2, |h x| ≤ D) :
    ∫ x in Icc (1 / 2 : ℝ) 2, g x * h x ≤
      √(∫ x in Icc (1 / 2 : ℝ) 2, g x ^ 2) * √(∫ x in Icc (1 / 2 : ℝ) 2, h x ^ 2) := by
  have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Icc (1 / 2 : ℝ) 2))
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall g0) (Filter.Eventually.of_forall h0)
    (by rw [ENNReal.ofReal_ofNat]; exact memLp_Icc hg hgC)
    (by rw [ENNReal.ofReal_ofNat]; exact memLp_Icc hh hhD)
  simp only [Real.rpow_two] at this
  rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

theorem setIntegral_const_Icc (c : ℝ) : ∫ _ in Icc (1 / 2 : ℝ) 2, c = 3 / 2 * c := by
  rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem fP_nonneg' (W : Finset ℝ) {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) : 0 ≤ fP W ρ x := by
  unfold fP
  exact mul_nonneg ψoutb.nonneg
    (mul_nonneg (inv_nonneg.2 hρ.le) (integral_nonneg fun y => Φx_nonneg W ρ x y))

/-- `1[|v - c| ≤ ρ] |R(v/s)|`. -/
noncomputable def ind (W : Finset ℝ) (c ρ s v : ℝ) : ℝ := if |v - c| ≤ ρ then ‖Rv W (v / s)‖ else 0

theorem ind_meas (W : Finset ℝ) (c ρ s : ℝ) : Measurable (ind W c ρ s) := by
  unfold ind
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    ((measurable_Rv W).comp (measurable_id.div_const s)).norm measurable_const

theorem ind_nonneg (W : Finset ℝ) (c ρ s v : ℝ) : 0 ≤ ind W c ρ s v := by
  unfold ind; split_ifs <;> positivity

theorem ind_le (W : Finset ℝ) (c ρ : ℝ) {s : ℝ} (hs : 0 < s) {v : ℝ} (hv : v ∈ Icc (1 / 2 : ℝ) 2) :
    |ind W c ρ s v| ≤ W.card := by
  rw [abs_of_nonneg (ind_nonneg W c ρ s v)]; unfold ind; split_ifs
  · exact norm_Rv_le W (div_pos (by linarith [hv.1]) hs)
  · positivity

/-- `∫ 1[|v-c| ≤ ρ] |R(v/s)|² ≤ s ρ f(c/s)`. -/
theorem ind_sq_le (W : Finset ℝ) {ρ c s : ℝ} (hρ0 : 0 < ρ) (hs : s ∈ Icc (1 / 2 : ℝ) 2)
    (hx1 : 1 / 8 ≤ c / s) (hx2 : c / s ≤ 8) :
    ∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ s v ^ 2 ≤ s * (ρ * fP W ρ (c / s)) := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hint := (Φx_integrable W ρ (c / s)).comp_div hs0.ne'
  calc ∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ s v ^ 2
      ≤ ∫ v in Icc (1 / 2 : ℝ) 2, Φx W ρ (c / s) (v / s) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity)
          hint.integrableOn ((ae_restrict_iff' measurableSet_Icc).2
            (Filter.Eventually.of_forall fun v hv => ?_))
        show ind W c ρ s v ^ 2 ≤ Φx W ρ (c / s) (v / s)
        unfold ind
        split_ifs with hS
        · have hy1 : 1 / 4 ≤ v / s := by rw [le_div_iff₀ hs0]; linarith [hv.1, hs.2]
          have hy2 : v / s ≤ 4 := by rw [div_le_iff₀ hs0]; linarith [hv.2, hs.1]
          have hφ : |(v / s - c / s) / ρ| ≤ 2 := by
            rw [← sub_div, abs_div, abs_div, abs_of_pos hρ0, abs_of_pos hs0, div_le_iff₀ hρ0,
              div_le_iff₀ hs0]
            nlinarith [hs.1]
          simp only [Φx, φ_eq_one hφ, ψin_eq_one hy1 hy2, one_mul, le_refl]
        · simpa using Φx_nonneg W ρ (c / s) (v / s)
    _ ≤ ∫ v, Φx W ρ (c / s) (v / s) :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun v => Φx_nonneg _ _ _ _)
    _ = s * (ρ * fP W ρ (c / s)) := by
        rw [Measure.integral_comp_div, abs_of_pos hs0, smul_eq_mul,
          integral_Φx W hρ0 (ψout_eq_one hx1 hx2)]

/-- The main term of P5: Cauchy–Schwarz on `|v₂ - c| ≤ ρ`. -/
theorem main_term (W : Finset ℝ) {ρ c v₁ : ℝ} (hρ0 : 0 < ρ) (hρ4 : ρ ≤ 1 / 4)
    (hv₁ : v₁ ∈ Icc (1 / 2 : ℝ) 2) :
    ∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ v₁ v * ind W c ρ 1 v ≤
      2 * ρ * √(fP W ρ (c / v₁)) * √(fP W ρ c) := by
  have hv₁0 : 0 < v₁ := by linarith [hv₁.1]
  by_cases hD : ∃ v ∈ Icc (1 / 2 : ℝ) 2, |v - c| ≤ ρ
  swap
  · push Not at hD
    have : (∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ v₁ v * ind W c ρ 1 v) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      simp [ind, not_le.2 (hD v hv)]
    rw [this]; positivity
  obtain ⟨v₀, hv₀, hv₀c⟩ := hD
  rw [abs_le] at hv₀c
  have hc1 : 1 / 4 ≤ c := by linarith [hv₀.1]
  have hc2 : c ≤ 9 / 4 := by linarith [hv₀.2]
  have hx1 : 1 / 8 ≤ c / v₁ := by rw [le_div_iff₀ hv₁0]; linarith [hv₁.2]
  have hx2 : c / v₁ ≤ 8 := by rw [div_le_iff₀ hv₁0]; linarith [hv₁.1]
  have hg2 := ind_sq_le W hρ0 hv₁ hx1 hx2
  have hh2 := ind_sq_le W hρ0 (c := c) (s := 1) ⟨by norm_num, by norm_num⟩
    (by rw [div_one]; linarith) (by rw [div_one]; linarith)
  rw [div_one, one_mul] at hh2
  have hcs := cs_Icc (ind_meas W c ρ v₁) (ind_meas W c ρ 1) (ind_nonneg W c ρ v₁)
    (ind_nonneg W c ρ 1) (fun v hv => ind_le W c ρ hv₁0 hv) (fun v hv => ind_le W c ρ one_pos hv)
  have hfx := fP_nonneg' W hρ0 (c / v₁)
  have hfc := fP_nonneg' W hρ0 c
  have h1 : √(∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ v₁ v ^ 2) ≤ 2 * √ρ * √(fP W ρ (c / v₁)) := by
    calc √(∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ v₁ v ^ 2) ≤ √(2 * (ρ * fP W ρ (c / v₁))) :=
          Real.sqrt_le_sqrt (hg2.trans (mul_le_mul_of_nonneg_right hv₁.2 (by positivity)))
      _ = √2 * √ρ * √(fP W ρ (c / v₁)) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hρ0.le, mul_assoc]
      _ ≤ 2 * √ρ * √(fP W ρ (c / v₁)) := by
          have : √2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
          gcongr
  have h2 : √(∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ 1 v ^ 2) ≤ √ρ * √(fP W ρ c) := by
    rw [← Real.sqrt_mul hρ0.le]; exact Real.sqrt_le_sqrt hh2
  have hρs : √ρ * √ρ = ρ := Real.mul_self_sqrt hρ0.le
  calc (∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ v₁ v * ind W c ρ 1 v)
      ≤ (2 * √ρ * √(fP W ρ (c / v₁))) * (√ρ * √(fP W ρ c)) :=
        hcs.trans (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity))
    _ = 2 * (√ρ * √ρ) * √(fP W ρ (c / v₁)) * √(fP W ρ c) := by ring
    _ = 2 * ρ * √(fP W ρ (c / v₁)) * √(fP W ρ c) := by rw [hρs]

theorem rho_le {η T M : ℝ} {N : ℕ} (hη' : η ≤ 1 / 4) (hT64 : 64 ≤ T)
    (hN : T ^ (3 / 4 : ℝ) ≤ N) (hM : 1 / 2 ≤ M) : T ^ η / (N * M) ≤ 1 / 4 := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have h8 : (8 : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    calc (8 : ℝ) = √64 := by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ √T := Real.sqrt_le_sqrt hT64
  have h34 : T ^ (3 / 4 : ℝ) = T ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  have hq : T ^ η ≤ T ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hη'
  have hq0 : 0 ≤ T ^ (1 / 4 : ℝ) := by positivity
  have hN8 : 8 * T ^ (1 / 4 : ℝ) ≤ N := by
    calc 8 * T ^ (1 / 4 : ℝ) ≤ T ^ (1 / 2 : ℝ) * T ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right h8 hq0
      _ = T ^ (3 / 4 : ℝ) := by rw [h34, mul_comm]
      _ ≤ N := hN
  have hNpos : (0 : ℝ) < N := by have : 0 < T ^ (1 / 4 : ℝ) := by positivity
                                 linarith
  rw [div_le_iff₀ (by positivity)]; nlinarith

theorem Qk_ge {η T : ℝ} (hη : 0 < η) (hT1 : 1 ≤ T) : T ^ 20 * T ≤ (T ^ η) ^ ⌈21 / η⌉₊ := by
  have hk : 21 ≤ η * ⌈21 / η⌉₊ := by
    have := Nat.le_ceil (21 / η)
    rw [div_le_iff₀ hη] at this; linarith
  calc T ^ 20 * T = T ^ (21 : ℝ) := by rw [← pow_succ, ← Real.rpow_natCast]; norm_num
    _ ≤ T ^ (η * ⌈21 / η⌉₊) := Real.rpow_le_rpow_of_exponent_le hT1 hk
    _ = (T ^ η) ^ ⌈21 / η⌉₊ := by rw [Real.rpow_mul (by linarith), Real.rpow_natCast]

theorem tail_arith {Ak Qk T W2 I : ℝ} (hAk0 : 0 ≤ Ak) (hT0 : 0 < T) (hQk : T ^ 20 * T ≤ Qk)
    (hTA : 2 * Ak + 1 ≤ T) (hI : I ≤ 3 / 2 * W2 ^ 2) : Ak / Qk * I ≤ W2 ^ 2 / T ^ 20 := by
  have hT20 : 0 < T ^ 20 := by positivity
  have hQk0 : 0 < Qk := lt_of_lt_of_le (by positivity) hQk
  calc Ak / Qk * I ≤ Ak / Qk * (3 / 2 * W2 ^ 2) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ ≤ W2 ^ 2 / T ^ 20 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hQk0 hT20]
        have : Ak * (3 / 2) * T ^ 20 ≤ Qk := by
          calc Ak * (3 / 2) * T ^ 20 ≤ T * T ^ 20 := by
                apply mul_le_mul_of_nonneg_right _ hT20.le; linarith
            _ = T ^ 20 * T := mul_comm _ _
            _ ≤ Qk := hQk
        have hW2' : 0 ≤ W2 ^ 2 := by positivity
        nlinarith

theorem local_bound {w : ℝ → ℝ} (hw : IsWeight w) (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ, T ^ (3 / 4 : ℝ) ≤ N →
      ∀ (W : Finset ℝ) (M : ℝ), 1 / 2 ≤ M → ∀ m : Fin 3 → ℤ, M ≤ |(m 1 : ℝ)| →
      ∀ v₁ ∈ Set.Icc (1 / 2 : ℝ) 2,
        Kint w N W m v₁ ≤ A * (T ^ η / (N * M)) *
            √(fP W (T ^ η / (N * M)) (xm m v₁)) * √(fP W (T ^ η / (N * M)) (ym m v₁)) +
          (W.card : ℝ) ^ 2 / T ^ 20 := by
  obtain ⟨Ak, hAk0, hAk⟩ := Kfun_le hw ⌈21 / η⌉₊
  refine ⟨2 * Ak, max 64 (2 * Ak + 1), by positivity, ?_⟩
  intro T hT N hN W M hM m hm v₁ hv₁
  have hT64 : 64 ≤ T := le_of_max_le_left hT
  have hTA : 2 * Ak + 1 ≤ T := le_of_max_le_right hT
  have hT0 : 0 < T := by linarith
  have hv₁0 : 0 < v₁ := by linarith [hv₁.1]
  have hQk := Qk_ge hη (by linarith : (1 : ℝ) ≤ T)
  set Q := T ^ η with hQdef
  set k := ⌈21 / η⌉₊ with hkdef
  have hQ1 : 1 ≤ Q := Real.one_le_rpow (by linarith) hη.le
  have hQk0 : 0 < Q ^ k := by positivity
  have hρ4 := rho_le hη' hT64 hN hM
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hM0 : 0 < M := by linarith
  set ρ := Q / (N * M) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρQ : (N : ℝ) * M * ρ = Q := by rw [hρdef]; field_simp
  have hm1 : (m 1 : ℝ) ≠ 0 := by
    intro h; rw [h, abs_zero] at hm; linarith
  set c := ym m v₁ with hcdef
  have hxc : xm m v₁ = c / v₁ := by rw [hcdef]; unfold xm ym; rw [div_div]
  have hphase : ∀ v, phase m v₁ v = m 1 * (v - c) := by
    intro v; rw [hcdef]; unfold phase ym; field_simp; ring
  set a : ℝ → ℝ := fun v => ‖Rv W (v / v₁)‖ * ‖Rv W v‖ with hadef
  have haC : ∀ v ∈ Icc (1 / 2 : ℝ) 2, |a v| ≤ (W.card : ℝ) ^ 2 := fun v hv => by
    rw [abs_of_nonneg (by positivity), sq]
    exact mul_le_mul (norm_Rv_le W (div_pos (by linarith [hv.1]) hv₁0))
      (norm_Rv_le W (by linarith [hv.1])) (norm_nonneg _) (Nat.cast_nonneg _)
  have hghC : ∀ v ∈ Icc (1 / 2 : ℝ) 2, |ind W c ρ v₁ v * ind W c ρ 1 v| ≤ (W.card : ℝ) ^ 2 :=
    fun v hv => by
      rw [abs_mul, sq]
      exact mul_le_mul (ind_le W c ρ hv₁0 hv) (ind_le W c ρ one_pos hv) (abs_nonneg _)
        (Nat.cast_nonneg _)
  have hgh_int : Integrable (fun v => ind W c ρ v₁ v * ind W c ρ 1 v)
      (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
    integrable_Icc ((ind_meas W c ρ v₁).mul (ind_meas W c ρ 1)) hghC
  have ha_int : Integrable a (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
    integrable_Icc (((measurable_Rv W).comp (measurable_id.div_const v₁)).norm.mul
      (measurable_Rv W).norm) haC
  -- the pointwise bound on the kernel
  have hpt : ∀ v ∈ Icc (1 / 2 : ℝ) 2, ‖Rv W (v / v₁)‖ * ‖Rv W v‖ * ‖Kfun w N m v₁ v‖ ≤
      Ak * (ind W c ρ v₁ v * ind W c ρ 1 v) + Ak / Q ^ k * a v := by
    intro v hv
    obtain ⟨hK1, hK2⟩ := hAk N m v₁ v hv₁ hv
    have ha0 : 0 ≤ a v := by positivity
    unfold ind
    split_ifs with hS
    · rw [div_one]
      have : 0 ≤ Ak / Q ^ k * a v := by positivity
      have h2 : ‖Rv W (v / v₁)‖ * ‖Rv W v‖ * ‖Kfun w N m v₁ v‖ ≤
          Ak * (‖Rv W (v / v₁)‖ * ‖Rv W v‖) := by
        rw [mul_comm Ak]; exact mul_le_mul_of_nonneg_left hK1 (by positivity)
      linarith
    · rw [zero_mul, mul_zero, zero_add]
      have hQle : Q ≤ (N : ℝ) * |phase m v₁ v| := by
        rw [hphase, abs_mul, ← hρQ]
        have : M * ρ ≤ |(m 1 : ℝ)| * |v - c| :=
          mul_le_mul hm (not_le.1 hS).le hρ0.le (abs_nonneg _)
        nlinarith
      have hKQ : ‖Kfun w N m v₁ v‖ * Q ^ k ≤ Ak :=
        le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hQle k)
          (norm_nonneg _)) hK2
      have hK : ‖Kfun w N m v₁ v‖ ≤ Ak / Q ^ k := by rw [le_div_iff₀ hQk0]; exact hKQ
      calc ‖Rv W (v / v₁)‖ * ‖Rv W v‖ * ‖Kfun w N m v₁ v‖ = a v * ‖Kfun w N m v₁ v‖ := rfl
        _ ≤ a v * (Ak / Q ^ k) := mul_le_mul_of_nonneg_left hK ha0
        _ = Ak / Q ^ k * a v := mul_comm _ _
  have hKint : Kint w N W m v₁ ≤ Ak * (∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ v₁ v * ind W c ρ 1 v) +
      Ak / Q ^ k * (∫ v in Icc (1 / 2 : ℝ) 2, a v) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hgh_int.const_mul _)
      (ha_int.const_mul _)]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity)
      ((hgh_int.const_mul _).add (ha_int.const_mul _)) ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hpt)
  have hia : (∫ v in Icc (1 / 2 : ℝ) 2, a v) ≤ 3 / 2 * (W.card : ℝ) ^ 2 := by
    rw [← setIntegral_const_Icc]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity)
      (integrable_const _) ((ae_restrict_iff' measurableSet_Icc).2
        (Filter.Eventually.of_forall fun v hv => (le_abs_self _).trans (haC v hv)))
  have hmain := main_term W hρ0 hρ4 hv₁ (c := c)
  rw [hxc]
  calc Kint w N W m v₁ ≤ Ak * (∫ v in Icc (1 / 2 : ℝ) 2, ind W c ρ v₁ v * ind W c ρ 1 v) +
        Ak / Q ^ k * (∫ v in Icc (1 / 2 : ℝ) 2, a v) := hKint
    _ ≤ Ak * (2 * ρ * √(fP W ρ (c / v₁)) * √(fP W ρ c)) + (W.card : ℝ) ^ 2 / T ^ 20 :=
        add_le_add (mul_le_mul_of_nonneg_left hmain hAk0) (tail_arith hAk0 hT0 hQk hTA hia)
    _ = 2 * Ak * ρ * √(fP W ρ (c / v₁)) * √(fP W ρ c) + (W.card : ℝ) ^ 2 / T ^ 20 := by ring

end GuthMaynard.P101.Part6
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
/-! ## P5: the local bound -/

end GuthMaynard.P101
end

section
namespace GuthMaynard.P101.Part6
open GuthMaynard GuthMaynard.P101 MeasureTheory Set
open scoped ENNReal
/-! ### One group (P8) -/
/-- Cauchy–Schwarz in `m` and in `v₁`, then `intX_le`, `intY_le`. -/
theorem gs_main (W : Finset ℝ) (G : Finset (Fin 3 → ℤ)) (f : ℝ → ℝ) (hf : Continuous f)
    (hnn : ∀ u, 0 ≤ f u) {B : ℝ} (hB : ∀ u, f u ≤ B) {X : ℝ}
    (hXs : ∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ G, f (xm m v)) ^ 2 ≤ 256 * X)
    (hYs : ∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ G, f (ym m v)) ^ 2 ≤ 4 * X) :
    ∫ v in Icc (1 / 2 : ℝ) 2, ‖Rv W v‖ * ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v)) ≤
      12 * (√(RL2 W) * √X) := by
  have hfm := hf.measurable
  have hxm : ∀ m, Measurable (xm m) := fun m => by unfold xm; fun_prop
  have hym : ∀ m, Measurable (ym m) := fun m => by unfold ym; fun_prop
  have hB0 : 0 ≤ B := (hnn 0).trans (hB 0)
  set n : ℝ := (G.card : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hPm : Measurable fun v => ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v)) :=
    Finset.measurable_sum _ fun m _ =>
      ((hfm.comp (hxm m)).sqrt).mul ((hfm.comp (hym m)).sqrt)
  have hXm : Measurable fun v => ∑ m ∈ G, f (xm m v) :=
    Finset.measurable_sum _ fun m _ => hfm.comp (hxm m)
  have hYm : Measurable fun v => ∑ m ∈ G, f (ym m v) :=
    Finset.measurable_sum _ fun m _ => hfm.comp (hym m)
  have hsum_le : ∀ (g : (Fin 3 → ℤ) → ℝ), (∀ m, 0 ≤ g m) → (∀ m, g m ≤ B) →
      |∑ m ∈ G, g m| ≤ n * B := fun g h0 h1 => by
    rw [abs_of_nonneg (Finset.sum_nonneg fun m _ => h0 m)]
    have := Finset.sum_le_card_nsmul G g B fun m _ => h1 m
    rwa [nsmul_eq_mul] at this
  have hsq_le : ∀ (g : (Fin 3 → ℤ) → ℝ), (∀ m, 0 ≤ g m) → (∀ m, g m ≤ B) →
      |(∑ m ∈ G, g m) ^ 2| ≤ (n * B) ^ 2 := fun g h0 h1 => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hsum_le g h0 h1) 2
  have hsB : ∀ u, √(f u) ≤ √B := fun u => Real.sqrt_le_sqrt (hB u)
  have hss : ∀ u u', √(f u) * √(f u') ≤ B := fun u u' => by
    calc √(f u) * √(f u') ≤ √B * √B :=
          mul_le_mul (hsB u) (hsB u') (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = B := Real.mul_self_sqrt hB0
  have hP0 : ∀ v, 0 ≤ ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v)) := fun v =>
    Finset.sum_nonneg fun _ _ => by positivity
  have hcs := cs_Icc (measurable_Rv W).norm hPm (fun v => norm_nonneg _) hP0
    (C := W.card) (D := n * B)
    (fun v hv => by rw [abs_of_nonneg (norm_nonneg _)]; exact norm_Rv_le W (by linarith [hv.1]))
    (fun v _ => hsum_le _ (fun m => by positivity) (fun m => hss _ _))
  have hXi : Integrable (fun v => (∑ m ∈ G, f (xm m v)) ^ 2) (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
    integrable_Icc (hXm.pow_const 2) fun v _ => hsq_le _ (fun m => hnn _) (fun m => hB _)
  have hYi : Integrable (fun v => (∑ m ∈ G, f (ym m v)) ^ 2) (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
    integrable_Icc (hYm.pow_const 2) fun v _ => hsq_le _ (fun m => hnn _) (fun m => hB _)
  have hP2 : ∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ G, √(f (xm m v)) * √(f (ym m v))) ^ 2 ≤ 130 * X := by
    calc ∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ G, √(f (xm m v)) * √(f (ym m v))) ^ 2
        ≤ ∫ v in Icc (1 / 2 : ℝ) 2,
            ((∑ m ∈ G, f (xm m v)) ^ 2 + (∑ m ∈ G, f (ym m v)) ^ 2) / 2 := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity)
            ((hXi.add hYi).div_const 2) (Filter.Eventually.of_forall fun v => ?_)
          have h1 := Real.sum_sqrt_mul_sqrt_le G (f := fun m => f (xm m v))
            (g := fun m => f (ym m v)) (fun m => hnn _) (fun m => hnn _)
          have hX0 : 0 ≤ ∑ m ∈ G, f (xm m v) := Finset.sum_nonneg fun _ _ => hnn _
          have hY0 : 0 ≤ ∑ m ∈ G, f (ym m v) := Finset.sum_nonneg fun _ _ => hnn _
          have h2 := pow_le_pow_left₀ (hP0 v) h1 2
          rw [mul_pow, Real.sq_sqrt hX0, Real.sq_sqrt hY0] at h2
          show _ ≤ _
          nlinarith [sq_nonneg (∑ m ∈ G, f (xm m v) - ∑ m ∈ G, f (ym m v))]
      _ = ((∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ G, f (xm m v)) ^ 2) +
            ∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ G, f (ym m v)) ^ 2) / 2 := by
          rw [integral_div, integral_add hXi hYi]
      _ ≤ 130 * X := by linarith
  have h130 : √(130 * X) ≤ 12 * √X := by
    rw [Real.sqrt_mul (by norm_num)]
    have : √130 ≤ 12 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
  calc ∫ v in Icc (1 / 2 : ℝ) 2, ‖Rv W v‖ * ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v))
      ≤ √(RL2 W) * √(∫ v in Icc (1 / 2 : ℝ) 2, (∑ m ∈ G, √(f (xm m v)) * √(f (ym m v))) ^ 2) :=
        hcs
    _ ≤ √(RL2 W) * (12 * √X) :=
        mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt hP2).trans h130) (Real.sqrt_nonneg _)
    _ = 12 * (√(RL2 W) * √X) := by ring

theorem card_box_le {L : ℝ} (hL : 0 ≤ L) : ((box L).card : ℝ) ≤ (2 * L + 1) ^ 3 := by
  unfold box
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ 3
  have h1 := Finset.card_erase_le (s := Finset.Icc (-⌊L⌋) ⌊L⌋) (a := 0)
  rw [Int.card_Icc] at h1
  have hf0 : 0 ≤ ⌊L⌋ := Int.floor_nonneg.2 hL
  have h2 : ((((Finset.Icc (-⌊L⌋) ⌊L⌋).erase 0).card : ℕ) : ℤ) ≤ 2 * ⌊L⌋ + 1 := by omega
  have h3 : ((((Finset.Icc (-⌊L⌋) ⌊L⌋).erase 0).card : ℕ) : ℝ) ≤ 2 * (⌊L⌋ : ℝ) + 1 := by
    exact_mod_cast h2
  linarith [Int.floor_le L]

theorem rpow_three_halves' {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * √x := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' hx (by norm_num), Real.rpow_one]

theorem gtail_arith {T N W G : ℝ} (hT : 2 ≤ T) (hN0 : 0 ≤ N) (hN : N ≤ T) (hW0 : 0 ≤ W)
    (hW : W ≤ T + 1) (hG0 : 0 ≤ G) (hG : G ≤ (2 * T + 1) ^ 3) :
    N ^ 3 * (G * (W ^ 2 / T ^ 20) * (3 / 2 * W)) ≤ T ^ 2 * W ^ (3 / 2 : ℝ) := by
  have hT0 : 0 < T := by linarith
  rw [rpow_three_halves' hW0]
  set s := √W with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = W := Real.sq_sqrt hW0
  have hsT : s ≤ T + 1 := by
    rw [hs, Real.sqrt_le_left (by linarith)]; nlinarith
  have hWs : W * s ≤ (T + 1) ^ 2 := by
    rw [sq]; exact mul_le_mul hW hsT hs0 (by linarith)
  have hWs0 : 0 ≤ W * s := by positivity
  have hW3 : W ^ 3 = (W * s) ^ 2 := by rw [mul_pow, hs2]; ring
  have hN3 : N ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hN0 hN 3
  have hG' : G ≤ 27 * T ^ 3 := hG.trans (by nlinarith [pow_le_pow_left₀ (by linarith) (show 2 * T + 1 ≤ 3 * T by linarith) 3])
  have hT1' : (T + 1) ^ 2 ≤ 4 * T ^ 2 := by nlinarith
  have hT14 : 162 ≤ T ^ 14 := by
    have := pow_le_pow_left₀ (by norm_num) hT 14
    norm_num at this; linarith
  have hT20 : 0 < T ^ 20 := by positivity
  have key : 3 / 2 * N ^ 3 * G * (W * s) ≤ T ^ 22 := by
    calc 3 / 2 * N ^ 3 * G * (W * s) ≤ 3 / 2 * T ^ 3 * (27 * T ^ 3) * (4 * T ^ 2) := by
          exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hN3 (by norm_num)) hG' hG0
            (by positivity)) (hWs.trans hT1') hWs0 (by positivity)
      _ = 162 * T ^ 8 := by ring
      _ ≤ T ^ 14 * T ^ 8 := by gcongr
      _ = T ^ 22 := by ring
  have e : N ^ 3 * (G * (W ^ 2 / T ^ 20) * (3 / 2 * W)) =
      (3 / 2 * N ^ 3 * G * (W * s)) * (W * s) / T ^ 20 := by
    calc N ^ 3 * (G * (W ^ 2 / T ^ 20) * (3 / 2 * W)) = 3 / 2 * N ^ 3 * G * W ^ 3 / T ^ 20 := by
          ring
      _ = _ := by rw [hW3]; ring
  rw [e, div_le_iff₀ hT20]
  calc 3 / 2 * N ^ 3 * G * (W * s) * (W * s) ≤ T ^ 22 * (W * s) :=
        mul_le_mul_of_nonneg_right key hWs0
    _ = T ^ 2 * (W * s) * T ^ 20 := by ring

theorem group_sum_le {w : ℝ → ℝ} (hw : IsWeight w) (η : ℝ) (hη : 0 < η) (hη' : η ≤ 1 / 4) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₀ ≤ T → ∀ N : ℕ, T ^ (3 / 4 : ℝ) ≤ N → (N : ℝ) ≤ T →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ∀ i₁ i : ℕ, ∀ X : ℝ, 0 ≤ X →
      J (20 * scale i) 20 (fP W (T ^ η / (N * scale i))) ≤ ENNReal.ofReal X →
      ∑ m ∈ grp (T ^ (1 + η) / N) i₁ i, (N : ℝ) ^ 3 * Ifull w N W m ≤
        A * (N : ℝ) ^ 3 * (T ^ η / (N * scale i)) * √(RL2 W) * √X +
          T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) := by
  obtain ⟨Al, Tl, hAl0, hloc⟩ := local_bound hw η hη hη'
  refine ⟨12 * Al, max Tl 2, by positivity, ?_⟩
  intro T hT N hN1 hN2 W a hsep hWa i₁ i X hX hJ
  have hTl : Tl ≤ T := le_of_max_le_left hT
  have hT2 : 2 ≤ T := le_of_max_le_right hT
  have hT0 : 0 < T := by linarith
  have hMh := half_le_scale i
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN1
  have hρ0 : 0 < T ^ η / (N * scale i) := by have := scale_pos i; positivity
  obtain ⟨hsm, -, -, hbdd⟩ := fP_basic W _ hρ0
  set ρ := T ^ η / (N * scale i) with hρdef
  set f := fP W ρ with hfdef
  have hf : Continuous f := hsm.continuous
  have hnn : ∀ u, 0 ≤ f u := fP_nonneg' W hρ0
  obtain ⟨B, hB⟩ := hbdd
  have hfB : ∀ u, f u ≤ B := fun u => hB ⟨u, rfl⟩
  have hB0 : 0 ≤ B := (hnn 0).trans (hfB 0)
  set L := T ^ (1 + η) / N with hLdef
  set G := grp L i₁ i with hGdef
  set tl := (W.card : ℝ) ^ 2 / T ^ 20 with htl
  have htl0 : 0 ≤ tl := by positivity
  have hmain := gs_main W G f hf hnn hfB (intX_le L i₁ i f hf hnn X hX hJ)
    (intY_le L i₁ i f hf hnn X hX hJ)
  have hfm := hf.measurable
  have hRb : ∀ v ∈ Icc (1 / 2 : ℝ) 2, ‖Rv W v‖ ≤ W.card := fun v hv =>
    norm_Rv_le W (by linarith [hv.1])
  have hsB : ∀ u, √(f u) ≤ √B := fun u => Real.sqrt_le_sqrt (hfB u)
  have hss : ∀ u u', √(f u) * √(f u') ≤ B := fun u u' => by
    calc √(f u) * √(f u') ≤ √B * √B :=
          mul_le_mul (hsB u) (hsB u') (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = B := Real.mul_self_sqrt hB0
  -- the per-`m` bound
  have hUint : ∀ m : Fin 3 → ℤ, Integrable
      (fun v => ‖Rv W v‖ * (Al * ρ * √(f (xm m v)) * √(f (ym m v)) + tl))
      (volume.restrict (Icc (1 / 2 : ℝ) 2)) := fun m => by
    have hxm : Measurable (xm m) := by unfold xm; fun_prop
    have hym : Measurable (ym m) := by unfold ym; fun_prop
    refine integrable_Icc ((measurable_Rv W).norm.mul ((((measurable_const.mul
      (hfm.comp hxm).sqrt)).mul (hfm.comp hym).sqrt).add measurable_const))
      (C := W.card * (Al * ρ * B + tl)) fun v hv => ?_
    have h1 : Al * ρ * √(f (xm m v)) * √(f (ym m v)) ≤ Al * ρ * B := by
      rw [mul_assoc (Al * ρ)]; exact mul_le_mul_of_nonneg_left (hss _ _) (by positivity)
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (hRb v hv) (by linarith) (by positivity) (Nat.cast_nonneg _)
  have hIf : ∀ m ∈ G, Ifull w N W m ≤
      ∫ v in Icc (1 / 2 : ℝ) 2, ‖Rv W v‖ * (Al * ρ * √(f (xm m v)) * √(f (ym m v)) + tl) := by
    intro m hm
    obtain ⟨-, hm1, -⟩ := grp_real hm
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v =>
      mul_nonneg (norm_nonneg _) (Kint_nonneg _ _ _ _ _)) (hUint m)
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun v hv => ?_))
    exact mul_le_mul_of_nonneg_left (hloc T hTl N hN1 W (scale i) hMh m hm1.le v hv)
      (norm_nonneg _)
  -- summing over the group
  have hRint : Integrable (fun v => ‖Rv W v‖) (volume.restrict (Icc (1 / 2 : ℝ) 2)) :=
    integrable_Icc (measurable_Rv W).norm fun v hv => by
      rw [abs_of_nonneg (norm_nonneg _)]; exact hRb v hv
  have hRPint : Integrable (fun v => ‖Rv W v‖ * ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v)))
      (volume.restrict (Icc (1 / 2 : ℝ) 2)) := by
    have hPm : Measurable fun v => ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v)) :=
      Finset.measurable_sum _ fun m _ =>
        ((hfm.comp (by unfold xm; fun_prop)).sqrt).mul ((hfm.comp (by unfold ym; fun_prop)).sqrt)
    refine integrable_Icc ((measurable_Rv W).norm.mul hPm) (C := W.card * (G.card * B))
      fun v hv => ?_
    have hP0 : 0 ≤ ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v)) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hPB : ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v)) ≤ G.card * B := by
      have := Finset.sum_le_card_nsmul G _ B fun m _ => hss (xm m v) (ym m v)
      rwa [nsmul_eq_mul] at this
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (hRb v hv) hPB hP0 (Nat.cast_nonneg _)
  have hRi : ∫ v in Icc (1 / 2 : ℝ) 2, ‖Rv W v‖ ≤ 3 / 2 * W.card := by
    rw [← setIntegral_const_Icc]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _)
      (integrable_const _) ((ae_restrict_iff' measurableSet_Icc).2
        (Filter.Eventually.of_forall hRb))
  have hsum : ∑ m ∈ G, Ifull w N W m ≤
      Al * ρ * (12 * (√(RL2 W) * √X)) + G.card * tl * (3 / 2 * W.card) := by
    calc ∑ m ∈ G, Ifull w N W m
        ≤ ∑ m ∈ G, ∫ v in Icc (1 / 2 : ℝ) 2,
            ‖Rv W v‖ * (Al * ρ * √(f (xm m v)) * √(f (ym m v)) + tl) := Finset.sum_le_sum hIf
      _ = ∫ v in Icc (1 / 2 : ℝ) 2, ∑ m ∈ G,
            ‖Rv W v‖ * (Al * ρ * √(f (xm m v)) * √(f (ym m v)) + tl) :=
          (integral_finsetSum G fun m _ => hUint m).symm
      _ = ∫ v in Icc (1 / 2 : ℝ) 2, (Al * ρ * (‖Rv W v‖ *
            ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v))) + G.card * tl * ‖Rv W v‖) := by
          congr 1; funext v
          calc ∑ m ∈ G, ‖Rv W v‖ * (Al * ρ * √(f (xm m v)) * √(f (ym m v)) + tl)
              = ∑ m ∈ G, (Al * ρ * ‖Rv W v‖ * (√(f (xm m v)) * √(f (ym m v))) +
                  tl * ‖Rv W v‖) := Finset.sum_congr rfl fun m _ => by ring
            _ = Al * ρ * ‖Rv W v‖ * ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v)) +
                  G.card * (tl * ‖Rv W v‖) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
            _ = _ := by ring
      _ = Al * ρ * (∫ v in Icc (1 / 2 : ℝ) 2, ‖Rv W v‖ *
            ∑ m ∈ G, √(f (xm m v)) * √(f (ym m v))) +
            G.card * tl * ∫ v in Icc (1 / 2 : ℝ) 2, ‖Rv W v‖ := by
          rw [integral_add (hRPint.const_mul _) (hRint.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := by
          gcongr
  -- the tail
  have hLT : L ≤ T := by
    rw [hLdef, div_le_iff₀ hNpos, Real.rpow_add hT0, Real.rpow_one]
    have : T ^ η ≤ T ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    nlinarith
  have hL0 : 0 ≤ L := by positivity
  have hG : (G.card : ℝ) ≤ (2 * T + 1) ^ 3 := by
    have h1 : G ⊆ box L := fun m hm =>
      Finset.mem_of_mem_filter m (Finset.mem_of_mem_filter m hm)
    calc (G.card : ℝ) ≤ (box L).card := by exact_mod_cast Finset.card_le_card h1
      _ ≤ (2 * L + 1) ^ 3 := card_box_le hL0
      _ ≤ (2 * T + 1) ^ 3 := by gcongr
  have hWT := card_le_of_sep hT0.le hsep hWa
  have htail := gtail_arith hT2 hNpos.le hN2 (Nat.cast_nonneg W.card) hWT (Nat.cast_nonneg _) hG
  rw [← Finset.mul_sum]
  calc (N : ℝ) ^ 3 * ∑ m ∈ G, Ifull w N W m
      ≤ (N : ℝ) ^ 3 * (Al * ρ * (12 * (√(RL2 W) * √X)) + G.card * tl * (3 / 2 * W.card)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 12 * Al * (N : ℝ) ^ 3 * ρ * √(RL2 W) * √X +
          (N : ℝ) ^ 3 * (G.card * tl * (3 / 2 * W.card)) := by ring
    _ ≤ _ := add_le_add le_rfl htail

end GuthMaynard.P101.Part6
end

section
namespace GuthMaynard.P101
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal
alias group_sum_le := GuthMaynard.P101.Part6.group_sum_le

/-! ## Assembly (proved from the stubs) -/
/-- The per-group arithmetic: `N³ρ (∫|R|²)^{1/2} X^{1/2} ≪ Q⁵ T^{δ/2}(T²|W|^{3/2} + TN|W|^{1/2}E^{1/2})`
with `ρ = Q/(NM)`, `NM ≤ TQ`. -/
theorem group_arith {Ag A c' Tδ Q T N M W1 E I1 I2 R2 P12 E12 : ℝ} (hAg : 0 ≤ Ag) (hA : 0 ≤ A)
    (hc' : 0 ≤ c') (hTδ : 0 ≤ Tδ) (hQ : 1 ≤ Q) (hT : 0 < T) (hN : 0 < N) (hM : 0 < M)
    (hNM : N * M ≤ T * Q) (hW1 : 0 ≤ W1) (_hE : 0 ≤ E) (hI1 : 0 ≤ I1) (hI1' : I1 ≤ A * Q * W1)
    (hI2 : 0 ≤ I2) (hI2' : I2 ≤ A * Q * E) (hR2' : R2 ≤ A * Q * W1)
    (hP12 : P12 = √W1) (hE12 : E12 = √E) :
    Ag * N ^ 3 * (Q / (N * M)) * √R2 * √(c' * Tδ * ((20 * M) ^ 6 * I1 ^ 2 + (20 * M) ^ 4 * I2)) ≤
      (Ag * √A * √c' * (8000 * A + 400 * √A)) * √Tδ * Q ^ 5 *
        (T ^ 2 * (W1 * P12) + T * N * P12 * E12) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hM0 : 0 ≤ M := hM.le
  set s := √Q with hs
  have hs2 : s ^ 2 = Q := Real.sq_sqrt hQ0
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_sqrt.mpr hQ
  have hsQ : s ≤ Q := by nlinarith
  have hP0 : 0 ≤ P12 := by rw [hP12]; exact Real.sqrt_nonneg _
  have hE0 : 0 ≤ E12 := by rw [hE12]; exact Real.sqrt_nonneg _
  -- `√R2 ≤ √A s P12`
  have hR : √R2 ≤ √A * s * P12 := by
    calc √R2 ≤ √(A * Q * W1) := Real.sqrt_le_sqrt hR2'
      _ = √A * s * P12 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hA, hP12]
  -- `√X ≤ √c' √Tδ (8000 M³ A Q W1 + 400 M² √A s E12)`
  have hI2s : √I2 ≤ √A * s * E12 := by
    calc √I2 ≤ √(A * Q * E) := Real.sqrt_le_sqrt hI2'
      _ = √A * s * E12 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hA, hE12]
  have hX : √(c' * Tδ * ((20 * M) ^ 6 * I1 ^ 2 + (20 * M) ^ 4 * I2)) ≤
      √c' * √Tδ * (8000 * M ^ 3 * (A * Q * W1) + 400 * M ^ 2 * (√A * s * E12)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hc']
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (sqrt_add_le' (by positivity) (by positivity)).trans ?_
    have h1 : √((20 * M) ^ 6 * I1 ^ 2) = 8000 * M ^ 3 * I1 := by
      rw [show (20 * M) ^ 6 * I1 ^ 2 = (8000 * M ^ 3 * I1) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have h2 : √((20 * M) ^ 4 * I2) = 400 * M ^ 2 * √I2 := by
      rw [Real.sqrt_mul (by positivity), show (20 * M) ^ 4 = (400 * M ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [h1, h2]
    have hM2 : 0 ≤ 400 * M ^ 2 := by positivity
    have hM3 : 0 ≤ 8000 * M ^ 3 := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left hI1' hM3) (mul_le_mul_of_nonneg_left hI2s hM2)
  have hpre : 0 ≤ Ag * N ^ 3 * (Q / (N * M)) := by positivity
  have hNQ : N ^ 3 * (Q / (N * M)) = N ^ 2 * Q / M := by field_simp
  calc Ag * N ^ 3 * (Q / (N * M)) * √R2 *
        √(c' * Tδ * ((20 * M) ^ 6 * I1 ^ 2 + (20 * M) ^ 4 * I2))
      ≤ Ag * N ^ 3 * (Q / (N * M)) * (√A * s * P12) *
          (√c' * √Tδ * (8000 * M ^ 3 * (A * Q * W1) + 400 * M ^ 2 * (√A * s * E12))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hR hpre) hX (Real.sqrt_nonneg _)
          (by positivity)
    _ = Ag * √A * √c' * √Tδ * (8000 * A * ((N * M) ^ 2 * (Q ^ 2 * s)) * (W1 * P12) +
          400 * √A * (N * (N * M) * (Q * s ^ 2)) * P12 * E12) := by
        rw [mul_assoc Ag, hNQ]
        field_simp
    _ ≤ Ag * √A * √c' * √Tδ * (8000 * A * ((T * Q) ^ 2 * (Q ^ 2 * Q)) * (W1 * P12) +
          400 * √A * (N * (T * Q) * (Q * Q ^ 2)) * P12 * E12) := by
        have hk : 0 ≤ Ag * √A * √c' * √Tδ := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hk
        have hNM0 : 0 ≤ N * M := by positivity
        have ha : (N * M) ^ 2 * (Q ^ 2 * s) ≤ (T * Q) ^ 2 * (Q ^ 2 * Q) :=
          mul_le_mul (pow_le_pow_left₀ hNM0 hNM 2)
            (mul_le_mul_of_nonneg_left hsQ (by positivity)) (by positivity) (by positivity)
        have hb : N * (N * M) * (Q * s ^ 2) ≤ N * (T * Q) * (Q * Q ^ 2) := by
          rw [hs2]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hNM hN.le)
            (mul_le_mul_of_nonneg_left (by nlinarith) hQ0) (by positivity) (by positivity)
        have hW : 0 ≤ W1 * P12 := by positivity
        have h8 : 0 ≤ 8000 * A := by positivity
        have h4 : 0 ≤ 400 * √A := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha h8) hW)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hb h4) hP0) hE0)
    _ ≤ Ag * √A * √c' * √Tδ * ((8000 * A + 400 * √A) * Q ^ 5 *
          (T ^ 2 * (W1 * P12) + T * N * P12 * E12)) := by
        have hk : 0 ≤ Ag * √A * √c' * √Tδ := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hk
        set x := T ^ 2 * (W1 * P12) with hx
        set y := T * N * P12 * E12 with hy
        have hx0 : 0 ≤ x := by positivity
        have hy0 : 0 ≤ y := by positivity
        have e1 : 8000 * A * ((T * Q) ^ 2 * (Q ^ 2 * Q)) * (W1 * P12) +
            400 * √A * (N * (T * Q) * (Q * Q ^ 2)) * P12 * E12 =
            8000 * A * Q ^ 5 * x + 400 * √A * Q ^ 4 * y := by rw [hx, hy]; ring
        have e2 : (8000 * A + 400 * √A) * Q ^ 5 * (x + y) =
            8000 * A * Q ^ 5 * x + 400 * √A * Q ^ 5 * y +
              (8000 * A * Q ^ 5 * y + 400 * √A * Q ^ 5 * x) := by ring
        rw [e1, e2]
        have hQ45 : Q ^ 4 ≤ Q ^ 5 := pow_le_pow_right₀ hQ (by norm_num)
        have h1 : 400 * √A * Q ^ 4 * y ≤ 400 * √A * Q ^ 5 * y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ45 (by positivity)) hy0
        have h2 : 0 ≤ 8000 * A * Q ^ 5 * y + 400 * √A * Q ^ 5 * x := by positivity
        linarith
    _ = (Ag * √A * √c' * (8000 * A + 400 * √A)) * √Tδ * Q ^ 5 *
          (T ^ 2 * (W1 * P12) + T * N * P12 * E12) := by ring

theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * √x := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' hx (by norm_num), Real.rpow_one]

/-- One group, from the group stub, Proposition 9.1 and the moments. -/
theorem one_group {Sg Ag A c' Tδ Q T N M W1 E I1 I2 R2 B₀ : ℝ} {Jv : ℝ≥0∞} (hAg : 0 ≤ Ag)
    (hA : 0 ≤ A) (hTδ : 0 ≤ Tδ) (hQ : 1 ≤ Q) (hT : 0 < T) (hN : 0 < N) (hM : 0 < M)
    (hNM : N * M ≤ T * Q) (hW1 : 0 ≤ W1) (hE : 0 ≤ E) (hI1 : 0 ≤ I1) (hI1' : I1 ≤ A * Q * W1)
    (hI2 : 0 ≤ I2) (hI2' : I2 ≤ A * Q * E) (hR2' : R2 ≤ A * Q * W1)
    (hJ : Jv ≤ ENNReal.ofReal (c' * Tδ * ((20 * M) ^ 6 * I1 ^ 2 + (20 * M) ^ 4 * I2)))
    (hgs : ∀ X : ℝ, 0 ≤ X → Jv ≤ ENNReal.ofReal X →
      Sg ≤ Ag * N ^ 3 * (Q / (N * M)) * √R2 * √X + B₀) :
    Sg ≤ (Ag * √A * √(max c' 0) * (8000 * A + 400 * √A)) * √Tδ * Q ^ 5 *
      (T ^ 2 * W1 ^ (3 / 2 : ℝ) + T * N * W1 ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) + B₀ := by
  set X := max c' 0 * Tδ * ((20 * M) ^ 6 * I1 ^ 2 + (20 * M) ^ 4 * I2) with hX
  have hX0 : 0 ≤ X := by positivity
  have hJX : Jv ≤ ENNReal.ofReal X := by
    refine hJ.trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ Tδ * ((20 * M) ^ 6 * I1 ^ 2 + (20 * M) ^ 4 * I2) := by positivity
    rw [hX, mul_assoc, mul_assoc (max c' 0)]
    exact mul_le_mul_of_nonneg_right (le_max_left c' 0) this
  have har := group_arith (Ag := Ag) (A := A) (c' := max c' 0) (Tδ := Tδ) (Q := Q) (T := T)
    (N := N) (M := M) (W1 := W1) (E := E) (I1 := I1) (I2 := I2) (R2 := R2)
    (P12 := W1 ^ (1 / 2 : ℝ)) (E12 := E ^ (1 / 2 : ℝ)) hAg hA (le_max_right _ _)
    hTδ hQ hT hN hM hNM hW1 hE hI1 hI1' hI2 hI2' hR2'
    (by rw [Real.sqrt_eq_rpow]) (by rw [Real.sqrt_eq_rpow])
  have h32 : W1 * W1 ^ (1 / 2 : ℝ) = W1 ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves hW1, Real.sqrt_eq_rpow]
  rw [h32] at har
  exact (hgs X hX0 hJX).trans (add_le_add har le_rfl)

/-- The final arithmetic of the assembly. -/
theorem final_arith {Snorm n An G D Q B B₀ Tδ : ℝ}
    (hS : Snorm ≤ 6 * (B₀ + n * (n * (G * D * Q ^ 5 * B + B₀))) + B₀) (hn0 : 0 ≤ n)
    (hnQ : n ≤ An * Q) (hAn : 0 ≤ An) (hG0 : 0 ≤ G) (hD1 : 1 ≤ D) (hQ1 : 1 ≤ Q) (hB₀0 : 0 ≤ B₀)
    (hB₀B : B₀ ≤ B) (hQ7 : Q ^ 7 * D ≤ Tδ) :
    Snorm ≤ (7 + 6 * An ^ 2 * (G + 1)) * Tδ * B := by
  have hB0 : 0 ≤ B := le_trans hB₀0 hB₀B
  have hn2 : n * n ≤ An ^ 2 * Q ^ 2 :=
    calc n * n ≤ (An * Q) * (An * Q) := mul_le_mul hnQ hnQ hn0 (by positivity)
      _ = An ^ 2 * Q ^ 2 := by ring
  have hQ5 : 1 ≤ Q ^ 5 := one_le_pow₀ hQ1
  have hinner : G * D * Q ^ 5 * B + B₀ ≤ (G + 1) * D * Q ^ 5 * B := by
    have h1 : 1 ≤ D * Q ^ 5 := one_le_mul_of_one_le_of_one_le hD1 hQ5
    have : B₀ ≤ D * Q ^ 5 * B := le_trans hB₀B (le_mul_of_one_le_left hB0 h1)
    have e : (G + 1) * D * Q ^ 5 * B = G * D * Q ^ 5 * B + D * Q ^ 5 * B := by ring
    rw [e]; linarith
  have hin0 : 0 ≤ G * D * Q ^ 5 * B + B₀ := by
    have : 0 ≤ D := by linarith
    positivity
  have hstep : n * (n * (G * D * Q ^ 5 * B + B₀)) ≤
      An ^ 2 * Q ^ 2 * ((G + 1) * D * Q ^ 5 * B) := by
    rw [← mul_assoc]
    exact mul_le_mul hn2 hinner hin0 (by positivity)
  have hBD : B ≤ Q ^ 7 * D * B :=
    le_mul_of_one_le_left hB0 (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ1) hD1)
  have e : An ^ 2 * Q ^ 2 * ((G + 1) * D * Q ^ 5 * B) =
      An ^ 2 * (G + 1) * (Q ^ 7 * D * B) := by ring
  have e3 : (7 + 6 * An ^ 2 * (G + 1)) * (Q ^ 7 * D) * B =
      7 * (Q ^ 7 * D * B) + 6 * (An ^ 2 * (G + 1) * (Q ^ 7 * D * B)) := by ring
  have hC0 : 0 ≤ 7 + 6 * An ^ 2 * (G + 1) := by positivity
  have hY : 0 ≤ An ^ 2 * (G + 1) * (Q ^ 7 * D * B) := by
    have : 0 ≤ D := by linarith
    positivity
  calc Snorm ≤ 6 * (B₀ + An ^ 2 * Q ^ 2 * ((G + 1) * D * Q ^ 5 * B)) + B₀ := by linarith
    _ ≤ (7 + 6 * An ^ 2 * (G + 1)) * (Q ^ 7 * D) * B := by rw [e, e3]; linarith
    _ ≤ (7 + 6 * An ^ 2 * (G + 1)) * Tδ * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ7 hC0) hB0

/-- Proposition 10.1, proved from the stubs and Proposition 9.1. -/
theorem norm_S_three_le_refined_dev (w : ℝ → ℝ) (hw : IsWeight w) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (W : Finset ℝ) (a : ℝ), IsSeparated (T ^ ε) W →
      (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      ‖S 3 w N W‖ ≤ C * T ^ δ * (T ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
        T * N * (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ)) := by
  intro δ hδ
  set η := min δ 1 / 14 with hηdef
  have hη : 0 < η := by positivity
  have hη1 : η ≤ 1 / 14 := by
    have := min_le_right δ 1; rw [hηdef]; linarith
  have hηδ : 7 * η ≤ δ / 2 := by
    have := min_le_left δ 1; rw [hηdef]; linarith
  have hη4 : η ≤ 1 / 4 := by linarith
  obtain ⟨c, hc⟩ := fP_adm
  obtain ⟨c', hc'⟩ := J_le_of_fourier_decay 20 16 (by norm_num) (by norm_num) c δ hδ
  obtain ⟨T₁, hT₁⟩ := box_trunc hw η hη
  obtain ⟨T₂, hT₂⟩ := far_sum_le hw η hη
  obtain ⟨Ag, T₃, hAg, hT₃⟩ := group_sum_le hw η hη hη4
  obtain ⟨An, hAn, hnsc⟩ := card_nsc_le η hη
  obtain ⟨A, T₄, hA, hT₄⟩ := moments η hη
  set c'' := max c' 0 with hc''
  set G := Ag * √A * √c'' * (8000 * A + 400 * √A) with hG
  have hG0 : 0 ≤ G := by positivity
  refine ⟨7 + 6 * An ^ 2 * (G + 1), max (max (max T₁ T₂) (max T₃ T₄)) 4, ?_⟩
  intro T hT N hN W a hsep hWa
  have hT4 : 4 ≤ T := le_of_max_le_right hT
  have hT1 : 1 ≤ T := by linarith
  have hT' := le_of_max_le_left hT
  have hTb1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT'
  have hTb2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT'
  have hTb3 : T₃ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT'
  have hTb4 : T₄ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT'
  have hT0 : 0 < T := by linarith
  have hsep1 := separated_one hT1 hε hsep
  obtain ⟨hN1, hN2⟩ := hN
  -- `Q = T^η`, `L = T^{1+η}/N = T Q / N`
  set Q := T ^ η with hQdef
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hT1 hη.le
  have hTN : T ^ η ≤ T ^ (3 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  have h2Q : 2 * Q ≤ N := by
    have h34 : T ^ (3 / 4 : ℝ) = T ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hT0]; norm_num
    have hq : Q ≤ T ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h2 : 2 ≤ T ^ (1 / 2 : ℝ) :=
      calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := h4.symm
        _ ≤ T ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hT4 (by norm_num)
    have hq0 : 0 ≤ T ^ (1 / 4 : ℝ) := by positivity
    have : 2 * Q ≤ T ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by nlinarith
    linarith
  set L := T ^ (1 + η) / N with hLdef
  have hTQ : T ^ (1 + η) = T * Q := by rw [Real.rpow_add hT0, Real.rpow_one]
  have hL1 : 1 ≤ L := by
    rw [hLdef, hTQ, le_div_iff₀ hNpos]; nlinarith
  have hLT : L ≤ T := by
    rw [hLdef, hTQ, div_le_iff₀ hNpos]; nlinarith
  -- energy and card
  set W1 : ℝ := ((W.card : ℕ) : ℝ) with hW1
  set E : ℝ := (energy W : ℝ) with hE
  have hW10 : 0 ≤ W1 := Nat.cast_nonneg _
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  set B₀ := T ^ 2 * W1 ^ (3 / 2 : ℝ) with hB₀
  set B := T ^ 2 * W1 ^ (3 / 2 : ℝ) + T * N * W1 ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) with hB
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hB₀B : B₀ ≤ B := by
    have : 0 ≤ T * N * W1 ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) := by positivity
    linarith
  have hB0 : 0 ≤ B := le_trans hB₀0 hB₀B
  set D := √(T ^ δ) with hD
  have hD1 : 1 ≤ D := Real.one_le_sqrt.mpr (Real.one_le_rpow hT1 hδ.le)
  -- the per-group bound
  have hgrp : ∀ i ∈ Finset.range (nsc L), ∀ i₁ ∈ Finset.range (nsc L),
      ∑ m ∈ grp L i₁ i, (N : ℝ) ^ 3 * Ifull w N W m ≤ G * D * Q ^ 5 * B + B₀ := by
    intro i hi i₁ _
    have hMle := scale_le L hL1 i (Finset.mem_range.mp hi)
    set M := scale i with hMdef
    have hM0 : 0 < M := scale_pos i
    have hNM : (N : ℝ) * M ≤ T * Q := by
      have := mul_le_mul_of_nonneg_left hMle hNpos.le
      rw [hLdef, mul_div_cancel₀ _ hNpos.ne', hTQ] at this
      exact this
    set ρ := Q / (N * M) with hρ
    have hρ0 : 0 < ρ := by positivity
    have hρT : 1 ≤ ρ * T := by
      rw [hρ, div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul, mul_comm Q T]
      exact hNM
    have hρ1 : ρ ≤ 1 := by
      rw [hρ, div_le_one (by positivity)]
      have := mul_le_mul_of_nonneg_left (half_le_scale i) hNpos.le
      linarith
    obtain ⟨hsm, hnn, hsupp, hdec⟩ := hc T hT1 W a hWa ρ hρ0 hρ1 hρT
    have hJ := hc' T hT0 (20 * M) (by positivity) (fP W ρ) hsm hnn hsupp hdec
    obtain ⟨hR2, hmom⟩ := hT₄ T hTb4 W a hsep1 hWa
    obtain ⟨hI1', hI2'⟩ := hmom ρ hρ0
    exact one_group hAg hA (by positivity) hQ1 hT0 hNpos hM0 hNM hW10 hE0
      (integral_nonneg hnn) hI1' (integral_nonneg fun u => sq_nonneg _) hI2' hR2 hJ
      (fun X hX hJX => hT₃ T hTb3 N hN1 hN2 W a hsep1 hWa i₁ i X hX hJX)
  -- summing the groups
  have hnscQ : (nsc L : ℝ) ≤ An * Q := by
    refine (hnsc L hL1).trans (mul_le_mul_of_nonneg_left ?_ hAn)
    exact Real.rpow_le_rpow (by linarith) hLT hη.le
  have hsumgrp : ∑ i ∈ Finset.range (nsc L), ∑ i₁ ∈ Finset.range (nsc L),
      ∑ m ∈ grp L i₁ i, (N : ℝ) ^ 3 * Ifull w N W m ≤
        (nsc L : ℝ) * ((nsc L : ℝ) * (G * D * Q ^ 5 * B + B₀)) := by
    have h1 : ∀ i ∈ Finset.range (nsc L), ∑ i₁ ∈ Finset.range (nsc L),
        ∑ m ∈ grp L i₁ i, (N : ℝ) ^ 3 * Ifull w N W m ≤
          (nsc L : ℝ) * (G * D * Q ^ 5 * B + B₀) := by
      intro i hi
      have := Finset.sum_le_card_nsmul _ _ _ (hgrp i hi)
      rwa [Finset.card_range, nsmul_eq_mul] at this
    have := Finset.sum_le_card_nsmul _ _ _ h1
    rwa [Finset.card_range, nsmul_eq_mul] at this
  -- the chain
  have hbox := hT₁ T hTb1 N hN1 hN2 W a hsep1 hWa
  have hsym := sum_box_le hw N W L
  have hP3 : ∑ m ∈ ordBox L, ‖Iterm w N W m‖ ≤ ∑ m ∈ ordBox L, (N : ℝ) ^ 3 * Ifull w N W m :=
    Finset.sum_le_sum fun m _ => norm_Iterm_le hw N W m
  have hcov := sum_ordBox_le L hL1 (fun m => (N : ℝ) ^ 3 * Ifull w N W m)
    (fun m => mul_nonneg (by positivity) (Ifull_nonneg _ _ _ _))
  have hfar := hT₂ T hTb2 N hN1 hN2 W a hsep1 hWa
  have hn0 : (0 : ℝ) ≤ nsc L := Nat.cast_nonneg _
  have hQ7 : Q ^ 7 * D ≤ T ^ δ := by
    have h1 : Q ^ 7 = T ^ (7 * η) := by
      rw [hQdef, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le, mul_comm]; norm_num
    have h2 : D = T ^ (δ / 2) := by
      rw [hD, Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]; congr 1; ring
    rw [h1, h2, ← Real.rpow_add hT0]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hsumle : ‖S 3 w N W‖ ≤ 6 * (B₀ + (nsc L : ℝ) * ((nsc L : ℝ) *
      (G * D * Q ^ 5 * B + B₀))) + B₀ := by
    calc ‖S 3 w N W‖ ≤ ∑ m ∈ box L, ‖Iterm w N W m‖ + B₀ := hbox
      _ ≤ 6 * ∑ m ∈ ordBox L, (N : ℝ) ^ 3 * Ifull w N W m + B₀ := by
        linarith [hsym, hP3]
      _ ≤ _ := by
        have := hcov.trans (add_le_add hfar hsumgrp)
        linarith
  exact final_arith hsumle hn0 hnscQ hAn hG0 hD1 hQ1 hB₀0 hB₀B hQ7

end GuthMaynard.P101
end


theorem solution : type_of% @GuthMaynard.P101.norm_S_three_le_refined_dev := @GuthMaynard.P101.norm_S_three_le_refined_dev
