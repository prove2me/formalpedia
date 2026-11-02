-- Prove2me | solution 1 for HryniewiczCriterion.exists_local_page_branch
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T16:09:53.047809+00:00
-- url     : https://prove2.me/submissions/e53b68f3-82b8-4799-98e0-b36a12e6006c

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

open HryniewiczCriterion
open scoped ContDiff Topology
open Filter

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
# A local branch of the page parameter along a trajectory

Child of `exists_page_parameter_along_trajectory`.
-/


namespace HryniewiczCriterion

variable {H : R4 → ℝ}

lemma ppa_isOpen_openUnitDisk : IsOpen openUnitDisk :=
  isOpen_lt (by fun_prop) continuous_const

lemma ppa_openUnitDisk_subset : openUnitDisk ⊆ closedUnitDisk := fun v hv => by
  simp only [openUnitDisk, closedUnitDisk, Set.mem_setOf_eq] at hv ⊢; exact hv.le

lemma ppa_dH_hvf (x : R4) : fderiv ℝ H x (hamiltonianVectorField H x) = 0 := by
  rw [hamiltonianVectorField_eq]; exact apply_jvec_self _

/-- `dH ∘ D(page) = 0` on `ℝ × D`. -/
lemma ppa_dH_fderiv_page (hH : ContDiff ℝ ∞ H) {page : ℝ → Plane → R4}
    (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2))
    (hDS : ∀ θ, page θ '' closedUnitDisk ⊆ energySurface H) {z : ℝ × Plane}
    (hz : z.2 ∈ openUnitDisk) (w : ℝ × Plane) :
    fderiv ℝ H (page z.1 z.2) (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) z w) = 0 := by
  set F : ℝ × Plane → R4 := fun z => page z.1 z.2
  have hopen : IsOpen {z : ℝ × Plane | z.2 ∈ openUnitDisk} :=
    ppa_isOpen_openUnitDisk.preimage continuous_snd
  have hev : (H ∘ F) =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
    filter_upwards [hopen.mem_nhds hz] with q hq
    exact hDS q.1 ⟨q.2, ppa_openUnitDisk_subset hq, rfl⟩
  have h0 : fderiv ℝ (H ∘ F) z = 0 := by rw [hev.fderiv_eq]; simp
  have hc : fderiv ℝ (H ∘ F) z = (fderiv ℝ H (F z)).comp (fderiv ℝ F z) :=
    fderiv_comp z ((hH.differentiable (by simp)) _) ((hsm.differentiable (by simp)) _)
  have := congrArg (fun L : ℝ × Plane →L[ℝ] ℝ => L w) (hc.symm.trans h0)
  simpa using this

lemma ppa_fderiv_page_slice {page : ℝ → Plane → R4}
    (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2)) (θ : ℝ) (u : Plane) :
    fderiv ℝ (page θ) u = (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)).comp
      (ContinuousLinearMap.inr ℝ ℝ Plane) := by
  have hF : HasFDerivAt (fun z : ℝ × Plane => page z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)) (θ, u) :=
    ((hsm.differentiable (by simp)) _).hasFDerivAt
  have hi : HasFDerivAt (fun v : Plane => ((θ, v) : ℝ × Plane))
      (ContinuousLinearMap.inr ℝ ℝ Plane) u :=
    (hasFDerivAt_const θ u).prodMk (hasFDerivAt_id u)
  exact (hF.comp u hi).fderiv

theorem exists_local_page_branch_aux (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (page : ℝ → Plane → R4) (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2))
    (hDS : ∀ θ, page θ '' closedUnitDisk ⊆ energySurface H)
    (htr : ∀ θ, ∀ u ∈ openUnitDisk,
      hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u))
    (hreg : ∀ θ : ℝ, ∀ u ∈ openUnitDisk,
      Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))
    (y : ℝ → R4) (hy : IsTrajectory H y) (t₀ θ₀ : ℝ) (u₀ : Plane) (hu₀ : u₀ ∈ openUnitDisk)
    (h0 : page θ₀ u₀ = y t₀) :
    ∃ (θ : ℝ → ℝ) (u : ℝ → Plane) (c : ℝ), c ≠ 0 ∧ HasDerivAt θ c t₀ ∧ θ t₀ = θ₀ ∧
      ∀ᶠ t in 𝓝 t₀, u t ∈ openUnitDisk ∧ page (θ t) (u t) = y t := by
  set F : ℝ × Plane → R4 := fun z => page z.1 z.2 with hFdef
  set z₀ : ℝ × Plane := (θ₀, u₀)
  set p₀ : (ℝ × Plane) × ℝ := (z₀, 1)
  set Ψ : (ℝ × Plane) × ℝ → R4 := fun p => p.2 • F p.1 with hΨdef
  set DF := fderiv ℝ F z₀
  have hx₀ : F z₀ = y t₀ := h0
  have hH1 : H (y t₀) = 1 := hy.2 t₀
  have hpos : 0 < fderiv ℝ H (y t₀) (y t₀) := hS.2.2 _ hH1
  -- strict derivative of `Ψ` at `p₀`
  have hFs : HasStrictFDerivAt F DF z₀ :=
    hsm.hasStrictFDerivAt (by simp)
  have hΨs : HasStrictFDerivAt Ψ
      ((1 : ℝ) • DF.comp (ContinuousLinearMap.fst ℝ (ℝ × Plane) ℝ) +
        (ContinuousLinearMap.snd ℝ (ℝ × Plane) ℝ).smulRight (F z₀)) p₀ := by
    have h := ((ContinuousLinearMap.snd ℝ (ℝ × Plane) ℝ).hasStrictFDerivAt (x := p₀)).smul
      (hFs.comp p₀ ((ContinuousLinearMap.fst ℝ (ℝ × Plane) ℝ).hasStrictFDerivAt (x := p₀)))
    exact h
  set L : (ℝ × Plane) × ℝ →L[ℝ] R4 :=
    (1 : ℝ) • DF.comp (ContinuousLinearMap.fst ℝ (ℝ × Plane) ℝ) +
      (ContinuousLinearMap.snd ℝ (ℝ × Plane) ℝ).smulRight (F z₀) with hLdef
  have hLapp : ∀ v : (ℝ × Plane) × ℝ, L v = DF v.1 + v.2 • y t₀ := by
    intro v; simp [hLdef, hx₀]
  have hdHDF : ∀ w, fderiv ℝ H (y t₀) (DF w) = 0 := by
    intro w; rw [← hx₀]; exact ppa_dH_fderiv_page hS.1 hsm hDS (z := z₀) hu₀ w
  have hdHL : ∀ v, fderiv ℝ H (y t₀) (L v) = v.2 * fderiv ℝ H (y t₀) (y t₀) := by
    intro v; rw [hLapp, map_add, map_smul, hdHDF]; simp
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun v hv' => ?_
    have hr : v.2 = 0 := by
      have := hdHL v; rw [hv', map_zero] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact h
      · exact absurd h hpos.ne'
    have hz : DF v.1 = 0 := by rw [hLapp, hr, zero_smul, add_zero] at hv'; exact hv'
    have hz' : v.1 = 0 := hreg θ₀ u₀ hu₀ (by rw [hz, map_zero])
    exact Prod.ext hz' hr
  have hfr : Module.finrank ℝ ((ℝ × Plane) × ℝ) = Module.finrank ℝ R4 := by simp
  have hsurj : Function.Surjective (L : (ℝ × Plane) × ℝ →ₗ[ℝ] R4) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj
  let e : ((ℝ × Plane) × ℝ) ≃L[ℝ] R4 :=
    (LinearEquiv.ofBijective (L : (ℝ × Plane) × ℝ →ₗ[ℝ] R4) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have he : ((e : ((ℝ × Plane) × ℝ) →L[ℝ] R4)) = L := by ext v <;> rfl
  have hΨe : HasStrictFDerivAt Ψ (e : ((ℝ × Plane) × ℝ) →L[ℝ] R4) p₀ := by rw [he]; exact hΨs
  have hΨp₀ : Ψ p₀ = y t₀ := by simp [hΨdef, p₀, hx₀]
  set g := hΨe.localInverse Ψ e p₀
  have hgp : g (y t₀) = p₀ := by rw [← hΨp₀]; exact hΨe.localInverse_apply_image
  have hgd : HasStrictFDerivAt g (e.symm : R4 →L[ℝ] ((ℝ × Plane) × ℝ)) (y t₀) := by
    rw [← hΨp₀]; exact hΨe.to_localInverse
  have hRinv : ∀ᶠ x in 𝓝 (y t₀), Ψ (g x) = x := by rw [← hΨp₀]; exact hΨe.eventually_right_inverse
  -- the branch along `y`
  set w : ℝ → (ℝ × Plane) × ℝ := fun t => g (y t)
  have hyc : ContinuousAt y t₀ := (hy.1 t₀).continuousAt
  have hwd : HasDerivAt w (e.symm (hamiltonianVectorField H (y t₀))) t₀ :=
    hgd.hasFDerivAt.comp_hasDerivAt t₀ (hy.1 t₀)
  have hwt : Tendsto w (𝓝 t₀) (𝓝 p₀) := by
    have := hgd.continuousAt.tendsto.comp hyc.tendsto
    rwa [hgp] at this
  set π₁ : (ℝ × Plane) × ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ Plane).comp (ContinuousLinearMap.fst ℝ (ℝ × Plane) ℝ)
  set X := hamiltonianVectorField H (y t₀)
  refine ⟨fun t => (w t).1.1, fun t => (w t).1.2, (e.symm X).1.1, ?_, ?_, ?_, ?_⟩
  · -- transversality
    intro hc
    set v := e.symm X
    have hev : L v = X := by rw [← he]; exact e.apply_symm_apply X
    have hr : v.2 = 0 := by
      have := hdHL v; rw [hev, ppa_dH_hvf] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · exact h
      · exact absurd h hpos.ne'
    have hv1 : v.1 = (0, v.1.2) := Prod.ext hc rfl
    have hX : DF v.1 = X := by rw [← hev, hLapp, hr, zero_smul, add_zero]
    apply htr θ₀ u₀ hu₀
    refine ⟨v.1.2, ?_⟩
    rw [ppa_fderiv_page_slice hsm, ContinuousLinearMap.comp_apply, h0]
    rw [hv1] at hX
    exact hX
  · exact π₁.hasFDerivAt.comp_hasDerivAt t₀ hwd
  · show (w t₀).1.1 = θ₀
    simp [w, hgp, p₀, z₀]
  · have hD : ∀ᶠ t in 𝓝 t₀, (w t).1.2 ∈ openUnitDisk :=
      hwt.eventually ((ppa_isOpen_openUnitDisk.preimage (continuous_snd.comp continuous_fst)).mem_nhds
        (by simpa [p₀, z₀] using hu₀))
    have hr0 : ∀ᶠ t in 𝓝 t₀, 0 < (w t).2 :=
      hwt.eventually ((isOpen_lt continuous_const continuous_snd).mem_nhds (by simp [p₀]))
    have hR : ∀ᶠ t in 𝓝 t₀, Ψ (w t) = y t := hyc.tendsto.eventually hRinv
    filter_upwards [hD, hr0, hR] with t hDt hrt hRt
    refine ⟨hDt, ?_⟩
    set q := F (w t).1
    have hq1 : H q = 1 := hDS (w t).1.1 ⟨(w t).1.2, ppa_openUnitDisk_subset hDt, rfl⟩
    have hq0 : q ≠ 0 := by
      intro h
      have := hS.2.2 q hq1
      rw [h, map_zero] at this
      exact lt_irrefl _ this
    have hyt : (w t).2 • q = y t := hRt
    have h1 : (w t).2 = 1 := by
      obtain ⟨r, -, hu⟩ := hS.2.1 q hq0
      have ha := hu (w t).2 ⟨hrt, by rw [hyt]; exact hy.2 t⟩
      have hb := hu 1 ⟨one_pos, by rw [one_smul]; exact hq1⟩
      rw [ha, hb]
    rw [h1, one_smul] at hyt
    exact hyt

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H)
    (page : ℝ → Plane → R4) (hsm : ContDiff ℝ ∞ (fun z : ℝ × Plane => page z.1 z.2))
    (hDS : ∀ θ, page θ '' closedUnitDisk ⊆ energySurface H)
    (htr : ∀ θ, ∀ u ∈ openUnitDisk,
      hamiltonianVectorField H (page θ u) ∉ Set.range (fderiv ℝ (page θ) u))
    (hreg : ∀ θ : ℝ, ∀ u ∈ openUnitDisk,
      Function.Injective (fderiv ℝ (fun z : ℝ × Plane => page z.1 z.2) (θ, u)))
    (y : ℝ → R4) (hy : IsTrajectory H y) (t₀ θ₀ : ℝ) (u₀ : Plane) (hu₀ : u₀ ∈ openUnitDisk)
    (h0 : page θ₀ u₀ = y t₀) :
    ∃ (θ : ℝ → ℝ) (u : ℝ → Plane) (c : ℝ), c ≠ 0 ∧ HasDerivAt θ c t₀ ∧ θ t₀ = θ₀ ∧
      ∀ᶠ t in 𝓝 t₀, u t ∈ openUnitDisk ∧ page (θ t) (u t) = y t :=
  exists_local_page_branch_aux H hS page hsm hDS htr hreg y hy t₀ θ₀ u₀ hu₀ h0
