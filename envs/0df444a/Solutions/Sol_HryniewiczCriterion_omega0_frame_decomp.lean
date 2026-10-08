-- Prove2me | solution 1 for HryniewiczCriterion.omega0_frame_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T20:01:46.605986+00:00
-- url     : https://prove2.me/submissions/7c10833f-dd28-4113-9d27-b128f1129aea

import Definitions.Def_HryniewiczCriterion_GraphAngle
import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open HryniewiczCriterion
open scoped ContDiff
open scoped ContDiff Topology
open Filter Set

namespace HryniewiczCriterion

/-- `e i` is the `i`-th standard basis vector of `ℝ⁴`. -/
lemma clm_apply_eq_sum (L : R4 →L[ℝ] ℝ) (v : R4) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) +
      v 2 * L (Pi.single 2 1) + v 3 * L (Pi.single 3 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, Fin.sum_univ_four, smul_eq_mul]

/-- The linear map `L ↦ J ∇L`: `jvec L = (-L e₁, L e₀, -L e₃, L e₂)`. -/
noncomputable def jvec : (R4 →L[ℝ] ℝ) →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ![-(ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 0 1 : R4),
      -(ContinuousLinearMap.apply ℝ ℝ (Pi.single 3 1 : R4)),
      ContinuousLinearMap.apply ℝ ℝ (Pi.single 2 1 : R4)] i

lemma jvec_apply (L : R4 →L[ℝ] ℝ) :
    jvec L = ![-L (Pi.single 1 1), L (Pi.single 0 1), -L (Pi.single 3 1), L (Pi.single 2 1)] := by
  ext i; fin_cases i <;> simp [jvec]

lemma hamiltonianVectorField_eq (H : R4 → ℝ) :
    hamiltonianVectorField H = fun y => jvec (fderiv ℝ H y) := by
  funext y; rw [jvec_apply]; rfl

lemma omega0_jvec_left (L : R4 →L[ℝ] ℝ) (q : R4) : omega0 (jvec L) q = -L q := by
  rw [clm_apply_eq_sum L q, jvec_apply]; simp [omega0]; ring

lemma omega0_jvec_right (L : R4 →L[ℝ] ℝ) (p : R4) : omega0 p (jvec L) = L p := by
  rw [clm_apply_eq_sum L p, jvec_apply]; simp [omega0] <;> ring

lemma apply_jvec_add (L M : R4 →L[ℝ] ℝ) : L (jvec M) + M (jvec L) = 0 := by
  rw [clm_apply_eq_sum L, clm_apply_eq_sum M, jvec_apply, jvec_apply]; simp; ring

lemma apply_jvec_self (L : R4 →L[ℝ] ℝ) : L (jvec L) = 0 := by
  have := apply_jvec_add L L; linarith

lemma liouvilleForm_eq (x v : R4) : liouvilleForm x v = omega0 x v / 2 := by
  simp [liouvilleForm, omega0]

lemma omega0_antisymm (u v : R4) : omega0 u v = -omega0 v u := by
  simp [omega0]; ring

lemma omega0_self (u : R4) : omega0 u u = 0 := by
  simp [omega0]; ring

lemma omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma omega0_lin_left (u a b : R4) (p q : ℝ) :
    omega0 (p • a + q • b) u = p * omega0 a u + q * omega0 b u := by
  simp [omega0]; ring

lemma omega0_smul_smul (u v : R4) (p q : ℝ) : omega0 (p • u) (q • v) = p * q * omega0 u v := by
  simp [omega0]; ring

/-- A symplectic pair `Z₁, Z₂` together with an `ω₀`-orthogonal symplectic pair `a, b`
spans `ℝ⁴`; every `v` that is `ω₀`-orthogonal to `a, b` lies in `span (Z₁, Z₂)`. -/
lemma eq_frame_of_omega0 (Z₁ Z₂ a b v : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0) :
    v = omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set w : Fin 4 → R4 := ![Z₁, Z₂, a, b] with hw
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    replace hg : g 0 • Z₁ + g 1 • Z₂ + g 2 • a + g 3 • b = 0 := by
      simpa [Fin.sum_univ_four, hw] using hg
    have e1 := congrArg (omega0 Z₁) hg
    have e2 := congrArg (omega0 Z₂) hg
    have e3 := congrArg (omega0 a) hg
    have e4 := congrArg (omega0 b) hg
    rw [omega0_lin_right] at e1 e2 e3 e4
    have z : ∀ u : R4, omega0 u 0 = 0 := fun u => by simp [omega0]
    rw [z] at e1 e2 e3 e4
    rw [omega0_self, h12, h1a, h1b] at e1
    rw [omega0_antisymm Z₂ Z₁, h12, omega0_self, h2a, h2b] at e2
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, h1a, h2a, omega0_self] at e3
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, h1b, h2b,
      omega0_self] at e4
    have g1 : g 1 = 0 := by linarith
    have g0 : g 0 = 0 := by linarith
    have g3 : g 3 = 0 := by
      have : g 3 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    have g2 : g 2 = 0 := by
      have : g 2 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    intro i; fin_cases i <;> assumption
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℝ (Set.range w) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  replace hc : c 0 • Z₁ + c 1 • Z₂ + c 2 • a + c 3 • b = v := by
    simpa [Fin.sum_univ_four, hw] using hc
  -- pair with `a` and `b` to kill the last two coefficients
  have ea : omega0 v a = c 0 * omega0 Z₁ a + c 1 * omega0 Z₂ a + c 2 * omega0 a a +
      c 3 * omega0 b a := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm a Z₁, omega0_antisymm a Z₂, omega0_antisymm a b, omega0_self]; ring
  have eb : omega0 v b = c 0 * omega0 Z₁ b + c 1 * omega0 Z₂ b + c 2 * omega0 a b +
      c 3 * omega0 b b := by
    rw [← hc, omega0_antisymm, omega0_lin_right]
    rw [omega0_antisymm b Z₁, omega0_antisymm b Z₂, omega0_antisymm b a, omega0_self]; ring
  rw [h1a, h2a, omega0_self, omega0_antisymm b a, hva] at ea
  rw [h1b, h2b, omega0_self, hvb] at eb
  have c3 : c 3 = 0 := by
    have : c 3 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have c2 : c 2 = 0 := by
    have : c 2 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have hv2 : v = c 0 • Z₁ + c 1 • Z₂ := by rw [← hc, c2, c3]; simp
  have k0 : omega0 v Z₂ = c 0 := by
    rw [hv2, omega0_lin_left, omega0_self, h12]; ring
  have k1 : omega0 Z₁ v = c 1 := by
    rw [hv2, omega0_antisymm, omega0_lin_left, omega0_self, omega0_antisymm Z₂ Z₁, h12]; ring
  rw [k0, k1]; exact hv2

/-- In the situation of `eq_frame_of_omega0`, `ω₀` on two such vectors is the
determinant of their `(Z₁, Z₂)`-coordinates. -/
lemma omega0_eq_det_of_frame (Z₁ Z₂ a b v w : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0)
    (hwa : omega0 w a = 0) (hwb : omega0 w b = 0) :
    omega0 v w = omega0 v Z₂ * omega0 Z₁ w - omega0 w Z₂ * omega0 Z₁ v := by
  have hv := eq_frame_of_omega0 Z₁ Z₂ a b v h12 h1a h1b h2a h2b hab hva hvb
  have hw := eq_frame_of_omega0 Z₁ Z₂ a b w h12 h1a h1b h2a h2b hab hwa hwb
  set p := omega0 v Z₂; set q := omega0 Z₁ v
  set r := omega0 w Z₂; set s := omega0 Z₁ w
  rw [hv, hw]
  simp only [omega0] at h12 ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (p * s - r * q) * h12

end HryniewiczCriterion

/-!
Leaf A, part 2: generic tools.

* `windingInterval_comp_reparam`: the winding interval is invariant under a reparametrization of
  `[0, 1]` that fixes both ends and has a continuous inverse.
* `exists_time_change`: for a continuous positive periodic `m`, the inverse `σ` of
  `τ(s) = ∫₀ˢ m` is a strictly increasing `C¹` time change with `σ' = 1 / m(σ)` and
  `σ(t + τ(T)) = σ(t) + T`.
* transfer lemmas for a defining function whose differential is a positive multiple of `dH`.
-/


namespace HryniewiczCriterion

variable {H : R4 → ℝ}

/-! ### Reparametrization invariance of the winding interval -/

lemma windingInterval_congr {φ φ' : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, φ t = φ' t) : windingInterval φ = windingInterval φ' := by
  have key : ∀ {φ φ' : ℝ → Matrix (Fin 2) (Fin 2) ℝ}, (∀ t ∈ Icc (0 : ℝ) 1, φ t = φ' t) →
      windingInterval φ ⊆ windingInterval φ' := by
    intro φ φ' h
    rintro d ⟨s, hs, θ, ⟨hc, h0, hθ⟩, rfl⟩
    exact ⟨s, hs, θ, ⟨hc, h0, fun t ht => (h t ht) ▸ hθ t ht⟩, rfl⟩
  exact subset_antisymm (key h) (key fun t ht => (h t ht).symm)

lemma windingInterval_subset_comp {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {ψ : ℝ → ℝ}
    (hψc : ContinuousOn ψ (Icc 0 1)) (hψm : MapsTo ψ (Icc 0 1) (Icc 0 1))
    (h0 : ψ 0 = 0) (h1 : ψ 1 = 1) :
    windingInterval φ ⊆ windingInterval (fun t => φ (ψ t)) := by
  rintro d ⟨s, hs, θ, ⟨hc, hθ0, hθ⟩, rfl⟩
  refine ⟨s, hs, fun t => θ (ψ t), ⟨hc.comp hψc hψm, by simp only [h0, hθ0],
    fun t ht => hθ (ψ t) (hψm ht)⟩, ?_⟩
  simp only [h1]

/-- The winding interval does not see a reparametrization `ψ` of `[0, 1]` fixing `0` and `1`
with a continuous inverse `χ`. -/
theorem windingInterval_comp_reparam {φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {ψ χ : ℝ → ℝ}
    (hψc : ContinuousOn ψ (Icc 0 1)) (hψm : MapsTo ψ (Icc 0 1) (Icc 0 1))
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 1)
    (hχc : ContinuousOn χ (Icc 0 1)) (hχm : MapsTo χ (Icc 0 1) (Icc 0 1))
    (hχ0 : χ 0 = 0) (hχ1 : χ 1 = 1) (hψχ : ∀ t ∈ Icc (0 : ℝ) 1, ψ (χ t) = t) :
    windingInterval (fun t => φ (ψ t)) = windingInterval φ := by
  apply subset_antisymm
  · calc windingInterval (fun t => φ (ψ t))
        ⊆ windingInterval (fun t => φ (ψ (χ t))) :=
          windingInterval_subset_comp (φ := fun t => φ (ψ t)) hχc hχm hχ0 hχ1
      _ = windingInterval φ := windingInterval_congr fun t ht => by rw [hψχ t ht]
  · exact windingInterval_subset_comp hψc hψm hψ0 hψ1

/-! ### Time change -/

/-- The inverse of `τ(s) = ∫₀ˢ m` for a continuous, positive, `T`-periodic `m`. -/
theorem exists_time_change {m : ℝ → ℝ} (hm : Continuous m) (hpos : ∀ s, 0 < m s) {T : ℝ}
    (hT : 0 < T) (hper : ∀ s, m (s + T) = m s) :
    ∃ (τf σ : ℝ → ℝ) (QT : ℝ), 0 < QT ∧ Continuous τf ∧ Continuous σ ∧ StrictMono τf ∧
      StrictMono σ ∧ (∀ t, τf (σ t) = t) ∧ (∀ s, σ (τf s) = s) ∧ τf 0 = 0 ∧ σ 0 = 0 ∧
      τf T = QT ∧ (∀ t, σ (t + QT) = σ t + T) ∧ ∀ t, HasDerivAt σ (m (σ t))⁻¹ t := by
  set τf : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, m u with hτf
  have hd : ∀ s, HasDerivAt τf (m s) s := fun s => (hm.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hcont : Continuous τf := continuous_iff_continuousAt.2 fun s => (hd s).continuousAt
  have hmono : StrictMono τf := strictMono_of_deriv_pos fun s => by rw [(hd s).deriv]; exact hpos s
  have hτ0 : τf 0 = 0 := intervalIntegral.integral_same
  -- uniform lower bound
  obtain ⟨s₀, -, hs₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le) hm.continuousOn
  have hδ : ∀ s, m s₀ ≤ m s := by
    intro s
    obtain ⟨y, hy, hys⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) hper hT s
    rw [hys]; exact hs₀ (Ico_subset_Icc_self hy)
  set δ := m s₀
  have hδpos : 0 < δ := hpos s₀
  have hg : Monotone fun s => τf s - δ * s := by
    have hgd : ∀ s, HasDerivAt (fun s => τf s - δ * s) (m s - δ) s := fun s => by
      have h := (hd s).sub ((hasDerivAt_id' s).const_mul δ)
      simp only [mul_one] at h
      exact h
    exact monotone_of_deriv_nonneg (fun s => (hgd s).differentiableAt)
      fun s => by rw [(hgd s).deriv]; linarith [hδ s]
  have hge : ∀ s, 0 ≤ s → δ * s ≤ τf s := fun s hs => by
    have := hg hs; simp only [hτ0, mul_zero, sub_zero] at this; linarith
  have hle : ∀ s, s ≤ 0 → τf s ≤ δ * s := fun s hs => by
    have := hg hs; simp only [hτ0, mul_zero, sub_zero] at this; linarith
  have htop : Tendsto τf atTop atTop :=
    tendsto_atTop_mono' atTop (eventually_ge_atTop 0 |>.mono fun s hs => hge s hs)
      (tendsto_id.const_mul_atTop hδpos)
  have hbot : Tendsto τf atBot atBot :=
    tendsto_atBot_mono' atBot (eventually_le_atBot 0 |>.mono fun s hs => hle s hs)
      (tendsto_id.const_mul_atBot hδpos)
  have hsurj := hcont.surjective htop hbot
  set e := StrictMono.orderIsoOfSurjective τf hmono hsurj
  have hτσ : ∀ t, τf (e.symm t) = t := fun t =>
    StrictMono.orderIsoOfSurjective_self_symm_apply τf hmono hsurj t
  have hστ : ∀ s, e.symm (τf s) = s := fun s =>
    StrictMono.orderIsoOfSurjective_symm_apply_self τf hmono hsurj s
  have hint : ∀ a b, IntervalIntegrable m MeasureTheory.volume a b := fun a b =>
    hm.intervalIntegrable a b
  have hadd : ∀ s, τf (s + T) = τf s + τf T := by
    intro s
    simp only [hτf]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s (s + T))]
    congr 1
    have := Function.Periodic.intervalIntegral_add_eq (f := m) (T := T) hper s 0
    rw [this, zero_add]
  refine ⟨τf, e.symm, τf T, ?_, hcont, e.symm.continuous, hmono, e.symm.strictMono, hτσ, hστ,
    hτ0, ?_, rfl, fun t => ?_, fun t => ?_⟩
  · rw [← hτ0]; exact hmono hT
  · calc e.symm 0 = e.symm (τf 0) := by rw [hτ0]
      _ = 0 := hστ 0
  · rw [← hστ (e.symm t + T), hadd, hτσ]
  · exact HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt (hd _)
      (hpos _).ne' (Eventually.of_forall hτσ)

/-! ### Defining functions with proportional differentials -/

lemma liouvilleForm_smul_r (y v : R4) (c : ℝ) :
    liouvilleForm y (c • v) = c * liouvilleForm y v := by
  simp [liouvilleForm]; ring

lemma hvf_of_fderiv_smul {K : R4 → ℝ} {y : R4} {c : ℝ}
    (h : fderiv ℝ K y = c • fderiv ℝ H y) :
    hamiltonianVectorField K y = c • hamiltonianVectorField H y := by
  rw [hamiltonianVectorField_eq, hamiltonianVectorField_eq]; simp only; rw [h, map_smul]

lemma xiFrameRaw_of_fderiv_smul {K : R4 → ℝ} {y : R4} {c : ℝ} (hc : c ≠ 0)
    (h : fderiv ℝ K y = c • fderiv ℝ H y) (Q : R4 → R4) :
    xiFrameRaw K Q y = xiFrameRaw H Q y := by
  simp only [xiFrameRaw, h, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hc]

lemma reebProjection_of_fderiv_smul {K : R4 → ℝ} {y : R4} {c : ℝ} (hc : c ≠ 0)
    (h : fderiv ℝ K y = c • fderiv ℝ H y) (v : R4) :
    reebProjection K y v = reebProjection H y v := by
  simp only [reebProjection, hvf_of_fderiv_smul h, liouvilleForm_smul_r, smul_smul]
  congr 2
  by_cases h0 : liouvilleForm y (hamiltonianVectorField H y) = 0
  · simp [h0]
  · field_simp

lemma reebProjection_add_hvf {y u : R4} (a : ℝ)
    (h0 : liouvilleForm y (hamiltonianVectorField H y) ≠ 0) :
    reebProjection H y (u + a • hamiltonianVectorField H y) = reebProjection H y u := by
  have hlin : liouvilleForm y (u + a • hamiltonianVectorField H y) =
      liouvilleForm y u + a * liouvilleForm y (hamiltonianVectorField H y) := by
    simp [liouvilleForm]; ring
  simp only [reebProjection, hlin]
  rw [add_div, mul_div_assoc, div_self h0, mul_one, add_smul]
  abel

/-! ### ω₀ as a continuous linear functional and the frame decomposition -/

/-- `v ↦ ω₀(u, v)`. -/
noncomputable def omegaL (u : R4) : R4 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => omega0 u v
      map_add' := fun v w => by simp [omega0]; ring
      map_smul' := fun c v => by simp [omega0]; ring }

@[simp] lemma omegaL_apply (u v : R4) : omegaL u v = omega0 u v := rfl

/-- Coordinates in a frame `x, X, Z₁, Z₂` with `ω₀(x, X) = μ ≠ 0`, `ω₀(Z₁, Z₂) = 1` and
`span{Z₁, Z₂}` `ω₀`-orthogonal to `x, X`. -/
lemma frame_decomp {x X Z₁ Z₂ : R4} {μ : ℝ} (hμ : omega0 x X = μ) (hμ0 : μ ≠ 0)
    (h12 : omega0 Z₁ Z₂ = 1) (h1a : omega0 Z₁ x = 0) (h1b : omega0 Z₁ X = 0)
    (h2a : omega0 Z₂ x = 0) (h2b : omega0 Z₂ X = 0) (v : R4) :
    v = (omega0 v X / μ) • x + (omega0 x v / μ) • X + omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set a := omega0 v X / μ
  set b := omega0 x v / μ
  set v' := v - a • x - b • X with hv'
  have hva : omega0 v' x = 0 := by
    have e1 : omega0 v' x = omega0 v x - a * omega0 x x - b * omega0 X x := by
      simp only [hv', omega0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, omega0_self, omega0_antisymm X x, hμ]
    simp only [b]; rw [omega0_antisymm x v]; field_simp; ring
  have hvb : omega0 v' X = 0 := by
    have e1 : omega0 v' X = omega0 v X - a * omega0 x X - b * omega0 X X := by
      simp only [hv', omega0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, omega0_self, hμ]
    simp only [a]; field_simp; ring
  have hab : omega0 x X ≠ 0 := by rw [hμ]; exact hμ0
  have hf := eq_frame_of_omega0 Z₁ Z₂ x X v' h12 h1a h1b h2a h2b hab hva hvb
  have e2 : omega0 v' Z₂ = omega0 v Z₂ := by
    have e1 : omega0 v' Z₂ = omega0 v Z₂ - a * omega0 x Z₂ - b * omega0 X Z₂ := by
      simp only [hv', omega0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, omega0_antisymm x, omega0_antisymm X, h2a, h2b]; ring
  have e3 : omega0 Z₁ v' = omega0 Z₁ v := by
    have e1 : omega0 Z₁ v' = omega0 Z₁ v - a * omega0 Z₁ x - b * omega0 Z₁ X := by
      simp only [hv', omega0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, h1a, h1b]; ring
  rw [e2, e3] at hf
  calc v = a • x + b • X + v' := by rw [hv']; abel
    _ = _ := by rw [hf]; abel

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (x X Z₁ Z₂ : R4) (μ : ℝ) (hμ : omega0 x X = μ) (hμ0 : μ ≠ 0)
    (h12 : omega0 Z₁ Z₂ = 1) (h1a : omega0 Z₁ x = 0) (h1b : omega0 Z₁ X = 0)
    (h2a : omega0 Z₂ x = 0) (h2b : omega0 Z₂ X = 0) (v : R4) :
    v = (omega0 v X / μ) • x + (omega0 x v / μ) • X + omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ :=
  frame_decomp hμ hμ0 h12 h1a h1b h2a h2b v
