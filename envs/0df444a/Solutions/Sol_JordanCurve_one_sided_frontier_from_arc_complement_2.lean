-- Prove2me | solution 2 for JordanCurve.one_sided_frontier_from_arc_complement
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T16:37:28.768534+00:00
-- url     : https://prove2.me/submissions/b5d0283a-271e-4895-80fb-17387d1fa083

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

theorem solution
    (hArc : ∀ α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      Continuous α → Function.Injective α →
        IsConnected ((Set.range α)ᶜ))
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ)
    (inside outside : Set (EuclideanSpace ℝ (Fin 2)))
    (hiopen : IsOpen inside) (hoopen : IsOpen outside)
    (hiconn : IsConnected inside) (hoconn : IsConnected outside)
    (hdisj : Disjoint inside outside)
    (hcover : inside ∪ outside = (Set.range γ)ᶜ) :
    Set.range γ ⊆ frontier inside := by
  rintro _ ⟨z, rfl⟩
  by_contra hfr
  have hzi : γ z ∉ inside := fun h =>
    (Set.ext_iff.mp hcover (γ z)).mp (Or.inl h) ⟨z, rfl⟩
  have hcl : γ z ∉ closure inside := by
    intro h; apply hfr
    rw [frontier, hiopen.interior_eq]; exact ⟨h, hzi⟩
  obtain ⟨r, hr, hrB⟩ : ∃ r > 0, ∀ y, dist y (γ z) < r → y ∉ inside := by
    rw [Metric.mem_closure_iff] at hcl
    push Not at hcl
    obtain ⟨r, hr, h⟩ := hcl
    exact ⟨r, hr, fun y hy hyi => absurd (h y hyi) (by rw [dist_comm]; exact not_le.mpr hy)⟩
  obtain ⟨ε, hε, hεγ⟩ := Metric.continuous_iff.mp hγ z r hr
  set R := Complex.orthonormalBasisOneI.repr with hR
  set ζ : ℂ := R.symm (z : EuclideanSpace ℝ (Fin 2)) with hζ
  have hζn : ‖ζ‖ = 1 := by
    rw [hζ, LinearIsometryEquiv.norm_map]
    simp
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζn; exact zero_ne_one hζn
  obtain ⟨δ', hδ', hδ'e⟩ := Metric.continuous_iff.mp
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const) :
      Continuous fun x : ℝ => Complex.exp ((x:ℂ) * Complex.I)) 0 ε hε
  set δ : ℝ := min δ' 1 with hδ
  have hδpos : 0 < δ := lt_min hδ' one_pos
  have hδδ : δ ≤ δ' := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hpi := Real.two_le_pi
  have hL : 0 < 2 * Real.pi - 2 * δ := by linarith
  let θ : Set.Icc (0:ℝ) 1 → ℝ := fun t => δ + (t:ℝ) * (2 * Real.pi - 2 * δ)
  have hθ : ∀ t, δ ≤ θ t ∧ θ t ≤ 2 * Real.pi - δ := by
    intro t
    have h0 := t.2.1; have h1 := t.2.2
    constructor <;> nlinarith
  have hmem : ∀ t, R (ζ * Complex.exp ((θ t : ℂ) * Complex.I)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro t
    simp [LinearIsometryEquiv.norm_map, norm_mul, hζn, Complex.norm_exp_ofReal_mul_I]
  let ψ : Set.Icc (0:ℝ) 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    fun t => ⟨_, hmem t⟩
  have hψc : Continuous ψ := by
    apply Continuous.subtype_mk
    apply R.continuous.comp
    apply continuous_const.mul
    apply Complex.continuous_exp.comp
    apply Continuous.mul _ continuous_const
    apply Complex.continuous_ofReal.comp
    exact continuous_const.add (continuous_subtype_val.mul continuous_const)
  have hψeq : ∀ t, (ψ t : EuclideanSpace ℝ (Fin 2)) = R (ζ * Complex.exp ((θ t : ℂ) * Complex.I)) :=
    fun t => rfl
  -- key: equal exponentials in the range force equal parameters
  have hexp : ∀ a b : ℝ, Complex.exp ((a:ℂ) * Complex.I) = Complex.exp ((b:ℂ) * Complex.I) →
      |a - b| < 2 * Real.pi → a = b := by
    intro a b h hab
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    have him := congrArg Complex.im hn
    simp at him
    have : (n:ℝ) = 0 := by
      have hn1 : |(n:ℝ)| < 1 := by
        have : |a - b| = |(n:ℝ)| * (2 * Real.pi) := by
          rw [him]; rw [show b + n * (2 * Real.pi) - b = n * (2 * Real.pi) by ring, abs_mul,
            abs_of_pos (by linarith : (0:ℝ) < 2 * Real.pi)]
        nlinarith
      have : n = 0 := by
        have := abs_lt.mp hn1
        have h1 : (n:ℝ) < 1 := this.2
        have h2 : (-1:ℝ) < n := this.1
        have : n < 1 := by exact_mod_cast h1
        have : -1 < n := by exact_mod_cast h2
        omega
      simp [this]
    rw [him, this]; ring
  have hψinj : Function.Injective ψ := by
    intro s t hst
    have h1 : R (ζ * Complex.exp ((θ s : ℂ) * Complex.I)) =
        R (ζ * Complex.exp ((θ t : ℂ) * Complex.I)) := by
      rw [← hψeq, ← hψeq, hst]
    have h2 := mul_left_cancel₀ hζ0 (R.injective h1)
    have h3 := hexp _ _ h2 (by
      obtain ⟨a1, a2⟩ := hθ s; obtain ⟨b1, b2⟩ := hθ t
      rw [abs_lt]; constructor <;> linarith)
    apply Subtype.ext
    have : ((s:ℝ) - t) * (2 * Real.pi - 2 * δ) = 0 := by
      simp only [θ] at h3; linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hzψ : ∀ t, ψ t ≠ z := by
    intro t h
    have h1 : R (ζ * Complex.exp ((θ t : ℂ) * Complex.I)) = R (ζ * Complex.exp (((0:ℝ) : ℂ) * Complex.I)) := by
      rw [← hψeq, h]; simp [hζ]
    have h2 := mul_left_cancel₀ hζ0 (R.injective h1)
    obtain ⟨a1, a2⟩ := hθ t
    have := hexp _ _ h2 (by rw [abs_lt]; constructor <;> linarith)
    linarith
  have hcov : ∀ w, w ∉ Set.range ψ → dist w z < ε := by
    intro w hw
    set q : ℂ := R.symm (w : EuclideanSpace ℝ (Fin 2)) / ζ with hq
    have hwn : ‖R.symm (w : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map]; simpa using w.2
    have hqn : ‖q‖ = 1 := by rw [hq, norm_div, hwn, hζn]; norm_num
    have hqe : Complex.exp ((Complex.arg q : ℂ) * Complex.I) = q := by
      have := Complex.norm_mul_exp_arg_mul_I q
      rwa [hqn, Complex.ofReal_one, one_mul] at this
    have hwq : R.symm (w : EuclideanSpace ℝ (Fin 2)) = ζ * q := by
      rw [hq]; field_simp
    have hwR : (w : EuclideanSpace ℝ (Fin 2)) = R (ζ * q) := by
      rw [← hwq]; simp
    have harg1 := Complex.neg_pi_lt_arg q
    have harg2 := Complex.arg_le_pi q
    set φ := Complex.arg q
    by_cases hsmall : |φ| < δ
    · rw [Subtype.dist_eq, dist_eq_norm, ← LinearIsometryEquiv.norm_map R.symm, map_sub, hwq, ← hζ]
      rw [show ζ * q - ζ = ζ * (q - 1) by ring, norm_mul, hζn, one_mul, ← hqe]
      have := hδ'e φ (by rw [Real.dist_eq, sub_zero]; linarith)
      simpa [dist_eq_norm] using this
    · exfalso; apply hw
      rcases le_or_gt 0 φ with h0 | h0
      · have hφ : δ ≤ φ := by rw [abs_of_nonneg h0] at hsmall; linarith
        have hm : (φ - δ) / (2 * Real.pi - 2 * δ) ∈ Set.Icc (0:ℝ) 1 :=
          ⟨div_nonneg (by linarith) hL.le, by rw [div_le_one hL]; linarith⟩
        refine ⟨⟨_, hm⟩, ?_⟩
        apply Subtype.ext
        rw [hψeq, hwR, ← hqe]
        have : θ ⟨_, hm⟩ = φ := by
          show δ + (φ - δ) / (2 * Real.pi - 2 * δ) * (2 * Real.pi - 2 * δ) = φ
          rw [div_mul_cancel₀ _ hL.ne']; ring
        rw [this]
      · have hφ : φ ≤ -δ := by rw [abs_of_neg h0] at hsmall; linarith
        have hm : (φ + 2 * Real.pi - δ) / (2 * Real.pi - 2 * δ) ∈ Set.Icc (0:ℝ) 1 :=
          ⟨div_nonneg (by linarith) hL.le, by rw [div_le_one hL]; linarith⟩
        refine ⟨⟨_, hm⟩, ?_⟩
        apply Subtype.ext
        rw [hψeq, hwR, ← hqe]
        congr 2
        have : ((θ ⟨_, hm⟩ : ℝ) : ℂ) = (φ : ℂ) + 2 * Real.pi := by
          have h : θ ⟨_, hm⟩ = φ + 2 * Real.pi := by
            show δ + (φ + 2 * Real.pi - δ) / (2 * Real.pi - 2 * δ) * (2 * Real.pi - 2 * δ) = _
            rw [div_mul_cancel₀ _ hL.ne']; ring
          rw [h]; push_cast; ring
        rw [this, add_mul, Complex.exp_add]
        have : Complex.exp (2 * Real.pi * Complex.I) = 1 := Complex.exp_two_pi_mul_I
        rw [show (2 * (Real.pi:ℂ)) * Complex.I = 2 * Real.pi * Complex.I by ring, this, mul_one]
  let α := γ ∘ ψ
  have hαc : Continuous α := hγ.comp hψc
  have hαi : Function.Injective α := hinj.comp hψinj
  have hAcl : IsClosed (Set.range α) := (isCompact_range hαc).isClosed
  have hconn := (hArc α hαc hαi).isPreconnected
  obtain ⟨y, hyA, hyi, hyU⟩ := hconn inside (outside ∪ (Metric.ball (γ z) r \ Set.range α))
    hiopen (hoopen.union (Metric.isOpen_ball.sdiff hAcl))
    (by
      intro x hx
      by_cases hxr : x ∈ Set.range γ
      · obtain ⟨w, rfl⟩ := hxr
        have hw : w ∉ Set.range ψ := by
          rintro ⟨t, rfl⟩; exact hx ⟨t, rfl⟩
        exact Or.inr (Or.inr ⟨hεγ w (hcov w hw), hx⟩)
      · have hxr' : x ∈ (Set.range γ)ᶜ := hxr
        rw [← hcover] at hxr'
        rcases hxr' with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    (by
      obtain ⟨y, hy⟩ := hiconn.nonempty
      refine ⟨y, ?_, hy⟩
      rintro ⟨t, rfl⟩
      have : α t ∈ (Set.range γ)ᶜ := by rw [← hcover]; exact Or.inl hy
      exact this ⟨_, rfl⟩)
    (by
      refine ⟨γ z, ?_, Or.inr ⟨Metric.mem_ball_self hr, ?_⟩⟩ <;>
      · rintro ⟨t, ht⟩; exact hzψ t (hinj ht))
  rcases hyU with h | ⟨hb, _⟩
  · exact Set.disjoint_left.mp hdisj hyi h
  · exact hrB y hb hyi
