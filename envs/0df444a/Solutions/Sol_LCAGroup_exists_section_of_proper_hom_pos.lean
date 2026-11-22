-- Prove2me | solution 1 for LCAGroup.exists_section_of_proper_hom_pos
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:48:23.324382+00:00
-- url     : https://prove2.me/submissions/1d6b7166-b7ec-45ae-9c25-b63f1d56f75b

import Mathlib
import Theorems.Thm_LCAGroup_pontryagin_duality
import Theorems.Thm_AddChar_exists_continuousLinearMap_fourierChar_eq

set_option autoImplicit false

namespace Sol_LCAGroup_exists_section_of_proper_hom_pos

open Real Topology Filter Set

lemma circle_re_le_one (w : Circle) : (w : ℂ).re ≤ 1 := by
  have := Complex.re_le_norm (w : ℂ)
  rwa [Circle.norm_coe] at this

lemma circle_sq_re (w : Circle) : ((w ^ 2 : Circle) : ℂ).re = 2 * (w : ℂ).re ^ 2 - 1 := by
  have h1 := Circle.normSq_coe w
  rw [Complex.normSq_apply] at h1
  rw [Circle.coe_pow, pow_two, Complex.mul_re]
  linear_combination (-1 : ℝ) * h1

/-- The only subgroup of the circle contained in the open right half-plane is trivial. -/
lemma circle_eq_one_of_forall_pow_re_pos (z : Circle)
    (h : ∀ n : ℕ, 0 < ((z ^ n : Circle) : ℂ).re) : z = 1 := by
  have hind : ∀ k : ℕ, 2 ^ k * (1 - (z : ℂ).re) ≤ 1 - ((z ^ (2 ^ k) : Circle) : ℂ).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e, circle_sq_re, pow_succ]
      have hpos := h (2 ^ k)
      have h1 := circle_re_le_one (z ^ 2 ^ k)
      nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr h1)]
  have hre : (z : ℂ).re = 1 := by
    by_contra hne
    have hlt : 0 < 1 - (z : ℂ).re := sub_pos.mpr (lt_of_le_of_ne (circle_re_le_one z) hne)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
    have h2 := hind k
    have h3 := h (2 ^ k)
    rw [div_lt_iff₀ hlt] at hk
    linarith
  have him : (z : ℂ).im = 0 := by
    have h1 := Circle.normSq_coe z
    rw [Complex.normSq_apply, hre] at h1
    exact mul_self_eq_zero.mp (by linarith)
  apply Circle.ext
  apply Complex.ext <;> simp [hre, him]

lemma circle_exp_re (t : ℝ) : ((Circle.exp t : Circle) : ℂ).re = Real.cos t := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

lemma eq_zero_of_forall_circle_exp_eq_one {d : ℝ} (h : ∀ s : ℝ, Circle.exp (s * d) = 1) :
    d = 0 := by
  by_contra hd
  have h1 := h (π / d)
  rw [div_mul_cancel₀ π hd, Circle.exp_eq_one] at h1
  obtain ⟨n, hn⟩ := h1
  have h2 : (1 - 2 * (n : ℝ)) * π = 0 := by linear_combination hn
  rcases mul_eq_zero.mp h2 with h3 | h3
  · have h4 : (1 : ℝ) = 2 * (n : ℝ) := by linarith
    have h5 : (1 : ℤ) = 2 * n := by exact_mod_cast h4
    omega
  · exact Real.pi_ne_zero h3

lemma isProperMap_of_isCompact_Icc {X : Type*} [TopologicalSpace X] (M : X → ℝ)
    (hMcont : Continuous M) (hMcpt : ∀ a b : ℝ, IsCompact (M ⁻¹' Icc a b)) : IsProperMap M := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hMcont, fun C hC => ?_⟩
  obtain ⟨a, ha⟩ := hC.bddBelow
  obtain ⟨b, hb⟩ := hC.bddAbove
  exact (hMcpt a b).of_isClosed_subset (hC.isClosed.preimage hMcont) (fun g hg => ⟨ha hg, hb hg⟩)

variable {G : Type*} [CommGroup G]

lemma map_one_of_add (M : G → ℝ) (hMmul : ∀ g h, M (g * h) = M g + M h) : M 1 = 0 := by
  have := hMmul 1 1
  rw [one_mul] at this
  linarith

lemma map_inv_of_add (M : G → ℝ) (hMmul : ∀ g h, M (g * h) = M g + M h) (g : G) :
    M g⁻¹ = - M g := by
  have := hMmul g g⁻¹
  rw [mul_inv_cancel, map_one_of_add M hMmul] at this
  linarith

lemma map_zpow_of_add (M : G → ℝ) (hMmul : ∀ g h, M (g * h) = M g + M h) (g : G) (n : ℤ) :
    M (g ^ n) = n * M g := by
  induction n using Int.induction_on with
  | zero => simp [map_one_of_add M hMmul]
  | succ k ih => rw [zpow_add_one, hMmul, ih]; push_cast; ring
  | pred k ih => rw [zpow_sub_one, hMmul, map_inv_of_add M hMmul, ih]; push_cast; ring

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The character `g ↦ exp (i y M g)`. -/
noncomputable def chi (M : G → ℝ) (hMmul : ∀ g h, M (g * h) = M g + M h) (hMcont : Continuous M)
    (y : ℝ) : G →ₜ* Circle where
  toFun g := Circle.exp (y * M g)
  map_one' := by rw [map_one_of_add M hMmul, mul_zero, Circle.exp_zero]
  map_mul' g h := by rw [hMmul, mul_add, Circle.exp_add]
  continuous_toFun := (map_continuous Circle.exp).comp (continuous_const.mul hMcont)

variable [T2Space G] [LocallyCompactSpace G]

/-- A continuous additive surjection `M : G → ℝ` with compact preimages of compact intervals
has a continuous one-parameter subgroup `φ` with `M ∘ φ = id`. -/
theorem exists_oneParameter (M : G → ℝ) (hMmul : ∀ g h, M (g * h) = M g + M h)
    (hMcont : Continuous M) (hMsurj : Function.Surjective M)
    (hMcpt : ∀ a b : ℝ, IsCompact (M ⁻¹' Icc a b)) :
    ∃ φ : ℝ → G, Continuous φ ∧ (∀ x y, φ (x + y) = φ x * φ y) ∧ ∀ x, M (φ x) = x := by
  classical
  have hM1 : M 1 = 0 := map_one_of_add M hMmul
  have hMinv : ∀ g, M g⁻¹ = - M g := map_inv_of_add M hMmul
  have hMquot : IsQuotientMap M :=
    (isProperMap_of_isCompact_Icc M hMcont hMcpt).isClosedMap.isQuotientMap hMcont hMsurj
  let χ : ℝ → PontryaginDual G := fun y => chi M hMmul hMcont y
  have hχ : ∀ y g, χ y g = Circle.exp (y * M g) := fun _ _ => rfl
  -- the injective homomorphism `y ↦ χ y`
  let f : ℝ →+ Additive (PontryaginDual G) :=
    { toFun := fun y => Additive.ofMul (χ y)
      map_zero' := by
        rw [ofMul_eq_zero]
        ext g
        rw [hχ, zero_mul, Circle.exp_zero]
        rfl
      map_add' := fun x y => by
        rw [← ofMul_mul]
        congr 1
        ext g
        rw [hχ, add_mul, Circle.exp_add]
        rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : χ x = χ y := Additive.ofMul.injective hxy
    have h0 : x - y = 0 := by
      apply eq_zero_of_forall_circle_exp_eq_one
      intro s
      obtain ⟨g, hg⟩ := hMsurj s
      have h1 := congrArg (fun c : PontryaginDual G => c g) hxy'
      simp only [hχ, hg] at h1
      rw [mul_sub, Circle.exp_sub, div_eq_one, mul_comm s x, mul_comm s y]
      exact h1
    linarith
  obtain ⟨hL, hhL⟩ :=
    (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom f hf (AddMonoidHom.id ℝ)
  let L : PontryaginDual G → ℝ := fun c => hL (Additive.ofMul c)
  have hLχ : ∀ y, L (χ y) = y := fun y => DFunLike.congr_fun hhL y
  have hLmul : ∀ a b, L (a * b) = L a + L b := fun a b => by
    simp only [L, ofMul_mul, map_add]
  have hL1 : L 1 = 0 := by simp only [L, ofMul_one, map_zero]
  -- continuity of `L` at `1`
  have hLcont1 : Tendsto L (𝓝 1) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set C : ℝ := π / (2 * ε) with hCdef
    have hC : 0 < C := by positivity
    let K : Set G := M ⁻¹' Icc 0 C
    let V : Set Circle := {z | 0 < (z : ℂ).re}
    have hV : IsOpen V := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
    have hWopen : IsOpen {c : PontryaginDual G | MapsTo c K V} := by
      have h1 : IsOpen {f : C(G, Circle) | MapsTo f K V} :=
        ContinuousMap.isOpen_setOfPred_mapsTo (hMcpt 0 C) hV
      exact h1.preimage (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
    have h1W : (1 : PontryaginDual G) ∈ {c : PontryaginDual G | MapsTo c K V} := by
      intro g _
      show 0 < (((1 : PontryaginDual G) g : Circle) : ℂ).re
      rw [PontryaginDual.one_apply]
      simp
    filter_upwards [hWopen.mem_nhds h1W] with c hc
    -- (i) `c` is trivial on the kernel of `M`
    have htriv : ∀ k, M k = 0 → c k = 1 := by
      intro k hk
      apply circle_eq_one_of_forall_pow_re_pos
      intro n
      have hkn : M (k ^ n) = 0 := by
        rw [← zpow_natCast, map_zpow_of_add M hMmul, hk, mul_zero]
      have hmem : k ^ n ∈ K := by
        show M (k ^ n) ∈ Icc 0 C
        rw [hkn]
        exact ⟨le_rfl, hC.le⟩
      have h2 := hc hmem
      rw [map_pow] at h2
      exact h2
    -- (ii) `c` factors through `M`
    let sec : ℝ → G := fun s => (hMsurj s).choose
    have hsec : ∀ s, M (sec s) = s := fun s => (hMsurj s).choose_spec
    let ψ : ℝ → Circle := fun s => c (sec s)
    have hψM : ∀ g, ψ (M g) = c g := by
      intro g
      have hk : M (sec (M g) * g⁻¹) = 0 := by rw [hMmul, hMinv, hsec]; ring
      have h2 := htriv _ hk
      rw [map_mul, map_inv] at h2
      exact mul_inv_eq_one.mp h2
    have hψcont : Continuous ψ := by
      rw [hMquot.continuous_iff]
      have : ψ ∘ M = c := funext hψM
      rw [this]
      exact map_continuous c
    let ψc : AddChar ℝ Circle :=
      { toFun := ψ
        map_zero_eq_one' := by rw [← hM1, hψM, map_one]
        map_add_eq_mul' := fun s t => by
          calc ψ (s + t) = ψ (M (sec s * sec t)) := by rw [hMmul, hsec, hsec]
            _ = c (sec s * sec t) := hψM _
            _ = c (sec s) * c (sec t) := map_mul c _ _ }
    -- (iii) classification of the characters of `ℝ`
    obtain ⟨l, hl⟩ := AddChar.exists_continuousLinearMap_fourierChar_eq ψc hψcont
    set y : ℝ := 2 * π * l 1 with hydef
    have hcy : c = χ y := by
      refine PontryaginDual.ext fun g => ?_
      rw [hχ, ← hψM g]
      have h2 : ψ (M g) = Real.fourierChar (l (M g)) := hl (M g)
      rw [h2, Real.fourierChar_apply']
      have h3 : l (M g) = M g * l 1 := by
        calc l (M g) = l (M g • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
          _ = M g • l 1 := l.map_smul _ _
          _ = M g * l 1 := smul_eq_mul _ _
      rw [h3, hydef]
      congr 1
      ring
    -- (iv) the frequency is small
    have hy : |y| < ε := by
      by_contra hge
      push Not at hge
      have hy0 : 0 < |y| := hε.trans_le hge
      set s : ℝ := π / (2 * |y|) with hsdef
      have hs0 : 0 ≤ s := by positivity
      have hsC : s ≤ C := by
        rw [hsdef, hCdef]
        apply div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
        linarith
      obtain ⟨g, hg⟩ := hMsurj s
      have hgK : g ∈ K := by
        show M g ∈ Icc 0 C
        rw [hg]
        exact ⟨hs0, hsC⟩
      have h2 : 0 < ((c g : Circle) : ℂ).re := hc hgK
      rw [hcy, hχ, hg, circle_exp_re, ← Real.cos_abs, abs_mul, abs_of_nonneg hs0] at h2
      have h3 : |y| * s = π / 2 := by
        rw [hsdef]
        field_simp
      rw [h3, Real.cos_pi_div_two] at h2
      exact lt_irrefl _ h2
    rw [Real.dist_eq, sub_zero, hcy, hLχ]
    exact hy
  have hLcont : Continuous L := by
    rw [continuous_iff_continuousAt]
    intro c0
    have h1 : Tendsto (fun c => c0⁻¹ * c) (𝓝 c0) (𝓝 1) := by
      have := (continuous_const_mul c0⁻¹).tendsto c0
      rwa [inv_mul_cancel] at this
    have h2 : Tendsto (fun c => L c0 + L (c0⁻¹ * c)) (𝓝 c0) (𝓝 (L c0 + 0)) :=
      tendsto_const_nhds.add (hLcont1.comp h1)
    rw [add_zero] at h2
    have h3 : (fun c => L c0 + L (c0⁻¹ * c)) = L := by
      funext c
      rw [← hLmul, mul_inv_cancel_left]
    rw [h3] at h2
    exact h2
  -- the one-parameter family of characters of the dual group
  let Φ : ℝ → (PontryaginDual G →ₜ* Circle) := fun x =>
    { toFun := fun c => Circle.exp (x * L c)
      map_one' := by rw [hL1, mul_zero, Circle.exp_zero]
      map_mul' := fun a b => by rw [hLmul, mul_add, Circle.exp_add]
      continuous_toFun := (map_continuous Circle.exp).comp (continuous_const.mul hLcont) }
  have hΦ : ∀ x c, Φ x c = Circle.exp (x * L c) := fun _ _ => rfl
  have hΦcont : Continuous Φ := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    show Continuous (fun p : ℝ × PontryaginDual G => Circle.exp (p.1 * L p.2))
    exact (map_continuous Circle.exp).comp (continuous_fst.mul (hLcont.comp continuous_snd))
  have hΦadd : ∀ x y, Φ (x + y) = Φ x * Φ y := by
    intro x y
    ext c
    rw [ContinuousMonoidHom.mul_apply, hΦ, hΦ, hΦ, add_mul, Circle.exp_add]
  obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality G
  let φ : ℝ → G := fun x => e.symm (Φ x)
  have hφc : ∀ x (c : PontryaginDual G), c (φ x) = Circle.exp (x * L c) := by
    intro x c
    have h1 : e (φ x) = Φ x := e.apply_symm_apply _
    rw [← he, h1]
    rfl
  refine ⟨φ, e.symm.continuous.comp hΦcont, fun x y => ?_, fun x => ?_⟩
  · show e.symm (Φ (x + y)) = e.symm (Φ x) * e.symm (Φ y)
    rw [hΦadd]
    exact map_mul e.symm (Φ x) (Φ y)
  · have h0 : M (φ x) - x = 0 := by
      apply eq_zero_of_forall_circle_exp_eq_one
      intro y
      have h1 := hφc x (χ y)
      rw [hχ, hLχ] at h1
      rw [mul_sub, Circle.exp_sub, div_eq_one, h1, mul_comm]
    linarith

end Sol_LCAGroup_exists_section_of_proper_hom_pos

open Sol_LCAGroup_exists_section_of_proper_hom_pos Filter Topology in
theorem solution (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G → ℝ) (hpos : ∀ g, 0 < m g) (hmul : ∀ g h, m (g * h) = m g * m h)
    (hcont : Continuous m) (hproper : ∀ a b : ℝ, 0 < a → IsCompact (m ⁻¹' Set.Icc a b)) :
    ∃ τ : ℝ → G, ContinuousOn τ (Set.range m) ∧
      (∀ s ∈ Set.range m, ∀ t ∈ Set.range m, τ (s * t) = τ s * τ t) ∧
      ∀ t ∈ Set.range m, m (τ t) = t := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : G → ℝ, ∀ g, M g = Real.log (m g) := ⟨fun g => Real.log (m g), fun _ => rfl⟩
  have hMmul : ∀ g h, M (g * h) = M g + M h := fun g h => by
    rw [hM, hM, hM, hmul, Real.log_mul (hpos g).ne' (hpos h).ne']
  have hMcont : Continuous M := by
    have : M = fun g => Real.log (m g) := funext hM
    rw [this]
    exact hcont.log (fun g => (hpos g).ne')
  have hmM : ∀ g, m g = Real.exp (M g) := fun g => by rw [hM, Real.exp_log (hpos g)]
  have hM1 : M 1 = 0 := map_one_of_add M hMmul
  have hMcpt : ∀ a b : ℝ, IsCompact (M ⁻¹' Set.Icc a b) := by
    intro a b
    have : M ⁻¹' Set.Icc a b = m ⁻¹' Set.Icc (Real.exp a) (Real.exp b) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_Icc, hmM g, Real.exp_le_exp]
    rw [this]
    exact hproper _ _ (Real.exp_pos a)
  by_cases hsurj : Function.Surjective M
  · -- the image is all of `ℝ_{>0}`: use a one-parameter subgroup
    obtain ⟨φ, hφc, hφadd, hφM⟩ := exists_oneParameter M hMmul hMcont hsurj hMcpt
    refine ⟨fun t => φ (Real.log t), ?_, ?_, ?_⟩
    · apply hφc.comp_continuousOn (Real.continuousOn_log.mono ?_)
      rintro _ ⟨g, rfl⟩
      exact (hpos g).ne'
    · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
      show φ (Real.log (m g * m h)) = φ (Real.log (m g)) * φ (Real.log (m h))
      rw [Real.log_mul (hpos g).ne' (hpos h).ne', hφadd]
    · rintro _ ⟨g, rfl⟩
      show m (φ (Real.log (m g))) = m g
      rw [hmM (φ _), hφM, Real.exp_log (hpos g)]
  · -- the image is a proper closed subgroup, hence cyclic
    let H : AddSubgroup ℝ :=
      { carrier := Set.range M
        add_mem' := by
          rintro _ _ ⟨g, rfl⟩ ⟨h, rfl⟩
          exact ⟨g * h, hMmul g h⟩
        zero_mem' := ⟨1, hM1⟩
        neg_mem' := by
          rintro _ ⟨g, rfl⟩
          exact ⟨g⁻¹, map_inv_of_add M hMmul g⟩ }
    have hHclosed : IsClosed (H : Set ℝ) :=
      (isProperMap_of_isCompact_Icc M hMcont hMcpt).isClosedMap.isClosed_range
    have hnd : ¬ Dense (H : Set ℝ) := by
      intro hd
      apply hsurj
      intro s
      have : s ∈ (H : Set ℝ) := hHclosed.closure_eq ▸ hd s
      exact this
    obtain ⟨a, ha⟩ := (H.dense_or_cyclic).resolve_left hnd
    rw [← AddSubgroup.zmultiples_eq_closure] at ha
    have hmem : ∀ g, ∃ n : ℤ, M g = n * a := by
      intro g
      have h1 : M g ∈ H := ⟨g, rfl⟩
      rw [ha] at h1
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp h1
      exact ⟨n, by rw [← hn, zsmul_eq_mul]⟩
    obtain ⟨g0, hg0⟩ : ∃ g0, M g0 = a := by
      have h1 : a ∈ H := by rw [ha]; exact AddSubgroup.mem_zmultiples a
      exact h1
    by_cases ha0 : a = 0
    · refine ⟨fun _ => 1, continuousOn_const, fun _ _ _ _ => (mul_one 1).symm, ?_⟩
      rintro _ ⟨g, rfl⟩
      obtain ⟨n, hn⟩ := hmem g
      show m 1 = m g
      rw [hmM 1, hmM g, hM1, hn, ha0, mul_zero]
    · have hround : ∀ g (n : ℤ), M g = n * a → round (Real.log (m g) / a) = n := by
        intro g n hn
        rw [← hM, hn, mul_div_cancel_right₀ _ ha0, round_intCast]
      refine ⟨fun t => g0 ^ round (Real.log t / a), ?_, ?_, ?_⟩
      · rintro _ ⟨g, rfl⟩
        obtain ⟨n, hn⟩ := hmem g
        apply ContinuousAt.continuousWithinAt
        have hlim : Tendsto (fun t => Real.log t / a) (𝓝 (m g)) (𝓝 (n : ℝ)) := by
          have h1 : ContinuousAt (fun t => Real.log t / a) (m g) :=
            (Real.continuousAt_log (hpos g).ne').div_const a
          have h2 : Real.log (m g) / a = n := by rw [← hM g, hn, mul_div_cancel_right₀ _ ha0]
          rw [← h2]
          exact h1
        have hev : ∀ᶠ t in 𝓝 (m g), round (Real.log t / a) = n := by
          filter_upwards [hlim (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))] with t ht
          rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at ht
          obtain ⟨h1, h2⟩ := abs_lt.mp ht
          rw [round_eq, Int.floor_eq_iff]
          constructor <;> linarith
        refine (continuousAt_const : ContinuousAt (fun _ : ℝ => g0 ^ n) (m g)).congr ?_
        filter_upwards [hev] with t ht
        rw [ht]
      · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
        obtain ⟨n1, hn1⟩ := hmem g
        obtain ⟨n2, hn2⟩ := hmem h
        show g0 ^ round (Real.log (m g * m h) / a) =
          g0 ^ round (Real.log (m g) / a) * g0 ^ round (Real.log (m h) / a)
        rw [← hmul, hround g n1 hn1, hround h n2 hn2,
          hround (g * h) (n1 + n2) (by rw [hMmul, hn1, hn2]; push_cast; ring), zpow_add]
      · rintro _ ⟨g, rfl⟩
        obtain ⟨n, hn⟩ := hmem g
        show m (g0 ^ round (Real.log (m g) / a)) = m g
        rw [hround g n hn, hmM, hmM g, map_zpow_of_add M hMmul, hg0, hn]
