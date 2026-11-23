-- Prove2me | solution 1 for NoHair.kerr_stationary_uniform_timelike_radius
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:25:37.672856+00:00
-- url     : https://prove2.me/submissions/656d5583-ede2-49da-b905-d9308307245d

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold
noncomputable section

private abbrev I4 := 𝓘(ℝ,E4)

private theorem generator_in_coordinates {m a : ℝ}
    (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
    (hφ : ∀ s x, (φ s x).val = x.val + s • coordBasis 0)
    (hsym : IsSymmetryFlow (kerrNewmanMetricField m a 0) (kerrNewmanFieldField a 0) φ)
    (x : kerrNewmanSpacetime a) : (flowGenerator φ x : E4) = coordBasis 0 := by
  let γ := fun s : ℝ => φ s x
  have hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ :=
    (hsym.2.2.1.comp (contMDiff_id.prodMk contMDiff_const)).of_le (by simp)
  have hd : HasDerivAt (fun t => (γ t).val) (coordBasis 0) 0 := by
    have he : (fun t => (γ t).val) = fun t : ℝ => x.val+t • coordBasis 0 :=
      funext fun t => hφ t x
    rw [he]
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (coordBasis 0)).const_add x.val
  have hval : ContMDiff I4 I4 1 (Subtype.val : kerrNewmanSpacetime a → E4) := contMDiff_subtype_val
  have hc := mfderiv_comp 0 (hval.mdifferentiableAt (by simp) (x := γ 0)) (hγ.mdifferentiableAt (by simp))
  have hi : (mfderiv I4 I4 (Subtype.val : kerrNewmanSpacetime a → E4) (γ 0) : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := γ 0)
  rw [hi] at hc
  have he : fderiv ℝ (fun t => (γ t).val) 0 = (mfderiv 𝓘(ℝ,ℝ) I4 γ 0 : ℝ →L[ℝ] E4) := by
    rw [← mfderiv_eq_fderiv]
    exact hc
  exact (congrArg (fun A : ℝ →L[ℝ] E4 => A 1) he).symm.trans hd.deriv

private theorem basis_entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem stationary_norm {m a : ℝ}
    (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
    (hφ : ∀ s x, (φ s x).val = x.val + s • coordBasis 0)
    (hsym : IsSymmetryFlow (kerrNewmanMetricField m a 0) (kerrNewmanFieldField a 0) φ)
    (x : kerrNewmanSpacetime a) :
    kerrNewmanMetricField m a 0 x (flowGenerator φ x) (flowGenerator φ x) =
      -1 + ksProfile m a 0 x.val := by
  change matrixBilin (kerrNewmanMetric m a 0 x.val) (flowGenerator φ x : E4) (flowGenerator φ x : E4) = _
  rw [generator_in_coordinates φ hφ hsym x, basis_entry]
  simp [kerrNewmanMetric, minkowski, ksNull]

private def equator (a q : ℝ) : E4 := WithLp.toLp 2 ![0,q,a,0]

private theorem equator_radius (a q : ℝ) (hq : 0 < q) : ksRadius a (equator a q) = q := by
  change Real.sqrt ((q^2+a^2+0^2-a^2 +
      Real.sqrt ((q^2+a^2+0^2-a^2)^2 + 4*a^2*0^2))/2) = q
  rw [show q^2+a^2+0^2-a^2=q^2 by ring]
  rw [show (q^2)^2+4*a^2*0^2=(q^2)^2 by ring, Real.sqrt_sq (sq_nonneg q)]
  rw [show (q^2+q^2)/2=q^2 by ring, Real.sqrt_sq hq.le]

private theorem equator_profile (m a q : ℝ) (hq : 0 < q) :
    ksProfile m a 0 (equator a q) = 2*m/q := by
  unfold ksProfile
  rw [equator_radius a q hq]
  change q^2*(2*m*q-0^2)/(q^4+a^2*0^2)=2*m/q
  rw [show q^4+a^2*0^2=q^4 by ring]
  field_simp [hq.ne'] <;> ring

theorem solution (m a R δ : ℝ) (hm : 0 < m) (hδ : 0 ≤ δ ∧ δ < 1)
    (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
    (hφ : ∀ s x, (φ s x).val = x.val + s • coordBasis 0)
    (hsym : IsSymmetryFlow (kerrNewmanMetricField m a 0) (kerrNewmanFieldField a 0) φ) :
    (∀ x : kerrNewmanSpacetime a, R < ksRadius a x.val →
      kerrNewmanMetricField m a 0 x (flowGenerator φ x) (flowGenerator φ x) < -δ)
      ↔ 2 * m ≤ (1 - δ) * R := by
  let c := 1-δ
  have hc : 0 < c := sub_pos.mpr hδ.2
  constructor
  · intro ht
    by_contra! hcut
    let q := 2*m/c
    have hq : 0 < q := div_pos (by positivity) hc
    have hRq : R < q := (lt_div_iff₀ hc).2 (by simpa [c, mul_comm] using hcut)
    let x : kerrNewmanSpacetime a := ⟨equator a q, by
      change 0 < ksRadius a (equator a q)
      rwa [equator_radius a q hq]⟩
    have hx : R < ksRadius a x.val := (equator_radius a q hq).symm ▸ hRq
    have hn := ht x hx
    rw [stationary_norm φ hφ hsym x] at hn
    change -1 + ksProfile m a 0 (equator a q) < -δ at hn
    rw [equator_profile m a q hq] at hn
    have hratio : 2*m/q=c := by
      apply (div_eq_iff hq.ne').2
      dsimp [q]
      field_simp [hc.ne'] <;> ring
    rw [hratio] at hn
    dsimp [c] at hn
    linarith
  · intro hcut x hx
    let r := ksRadius a x.val
    have hr : 0 < r := x.property
    have hstrict : 2*m < c*r := lt_of_le_of_lt hcut (mul_lt_mul_of_pos_left hx hc)
    have hd : 0 < r^4+a^2*(x.val 3)^2 := by positivity
    have hp : ksProfile m a 0 x.val ≤ 2*m/r := by
      change r^2*(2*m*r-0^2)/(r^4+a^2*(x.val 3)^2) ≤ 2*m/r
      apply (div_le_div_iff₀ hd hr).2
      nlinarith only [mul_nonneg (by positivity : 0 ≤ 2*m)
        (mul_nonneg (sq_nonneg a) (sq_nonneg (x.val 3)))]
    have hratio : 2*m/r < c := (div_lt_iff₀ hr).2 hstrict
    rw [stationary_norm φ hφ hsym x]
    dsimp [c] at hratio
    linarith
