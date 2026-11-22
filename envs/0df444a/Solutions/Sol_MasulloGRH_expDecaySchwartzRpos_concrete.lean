-- Prove2me | solution 1 for MasulloGRH.expDecaySchwartzRpos_concrete
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T09:26:18.307235+00:00
-- url     : https://prove2.me/submissions/7688555c-efa9-484f-8d08-ccd701f4d26f

import Definitions.Def_MasulloGRH_ExpDecaySpaces

set_option autoImplicit false

open Topology MasulloGRH

namespace AAux

variable {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The real coordinate of `G ≃ₜ* ℝ`. -/
def rho (e : G ≃ₜ* Multiplicative ℝ) (x : G) : ℝ := Multiplicative.toAdd (e x)

lemma rho_mul (e : G ≃ₜ* Multiplicative ℝ) (x y : G) : rho e (x * y) = rho e x + rho e y := by
  simp [rho]

lemma continuous_rho (e : G ≃ₜ* Multiplicative ℝ) : Continuous (rho e) :=
  continuous_toAdd.comp e.continuous

lemma rho_symm (e : G ≃ₜ* Multiplicative ℝ) (t : ℝ) :
    rho e (e.symm (Multiplicative.ofAdd t)) = t := by simp [rho]

lemma rho_injective (e : G ≃ₜ* Multiplicative ℝ) : Function.Injective (rho e) := by
  intro x y h
  apply e.injective
  simpa [rho] using h

/-- The character `x ↦ exp (i t ρ(x))`. -/
noncomputable def chr (e : G ≃ₜ* Multiplicative ℝ) (t : ℝ) : PontryaginDual G :=
  { toFun := fun x => Circle.exp (t * rho e x)
    map_one' := by simp [rho]
    map_mul' := fun x y => by rw [rho_mul, mul_add, Circle.exp_add]
    continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul (continuous_rho e)) }

lemma chr_apply (e : G ≃ₜ* Multiplicative ℝ) (t : ℝ) (x : G) :
    chr e t x = Circle.exp (t * rho e x) := rfl

lemma chr_add (e : G ≃ₜ* Multiplicative ℝ) (s t : ℝ) : chr e (s + t) = chr e s * chr e t := by
  refine PontryaginDual.ext fun x => ?_
  show Circle.exp ((s + t) * rho e x) = Circle.exp (s * rho e x) * Circle.exp (t * rho e x)
  rw [add_mul, Circle.exp_add]

lemma chr_zero (e : G ≃ₜ* Multiplicative ℝ) : chr e 0 = 1 := by
  refine PontryaginDual.ext fun x => ?_
  show Circle.exp (0 * rho e x) = 1
  simp

lemma chr_nsmul (e : G ≃ₜ* Multiplicative ℝ) (n : ℕ) (t : ℝ) : chr e (n * t) = chr e t ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, chr_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, chr_add, ih, pow_succ]

lemma continuous_chr (e : G ≃ₜ* Multiplicative ℝ) : Continuous (chr e) := by
  refine (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous_iff.2 ?_
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact Circle.exp.continuous.comp (continuous_fst.mul ((continuous_rho e).comp continuous_snd))

/-- Every continuous character of `G ≅ ℝ` is `chr e t`. -/
lemma char_classification (e : G ≃ₜ* Multiplicative ℝ) (χ : PontryaginDual G) :
    ∃ t : ℝ, χ = chr e t := by
  let f : C(ℝ, Circle) := ⟨fun t => χ (e.symm (Multiplicative.ofAdd t)),
    χ.continuous.comp (e.symm.continuous.comp continuous_ofAdd)⟩
  have hf0 : f 0 = 1 := by
    show χ (e.symm (Multiplicative.ofAdd 0)) = 1
    simp
  have hfadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    show χ (e.symm (Multiplicative.ofAdd (x + y))) =
      χ (e.symm (Multiplicative.ofAdd x)) * χ (e.symm (Multiplicative.ofAdd y))
    rw [ofAdd_add, map_mul, map_mul]
  obtain ⟨Θ, ⟨hΘ0, hΘ⟩, huniq⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (by rw [Circle.exp_zero, hf0])
  have hΘx : ∀ x, Circle.exp (Θ x) = f x := fun x => congrFun hΘ x
  have hadd : ∀ x y, Θ (x + y) = Θ x + Θ y := by
    intro x y
    let Θy : C(ℝ, ℝ) := ⟨fun x => Θ (x + y) - Θ y, by fun_prop⟩
    have h1 : Θy 0 = 0 := by simp [Θy]
    have h2 : Circle.exp ∘ Θy = f := by
      funext x
      simp only [Function.comp_apply, Θy, ContinuousMap.coe_mk]
      rw [sub_eq_add_neg, Circle.exp_add, Circle.exp_neg, hΘx, hΘx, hfadd]
      group
    have := huniq Θy ⟨h1, h2⟩
    have := congrArg (fun F : C(ℝ, ℝ) => F x) this
    simp only [Θy, ContinuousMap.coe_mk] at this
    linarith
  let Θh : ℝ →+ ℝ := ⟨⟨Θ, hΘ0⟩, hadd⟩
  have hlin : ∀ x, Θ x = x * Θ 1 := by
    intro x
    have := map_real_smul Θh Θ.continuous x 1
    simpa [Θh, smul_eq_mul] using this
  refine ⟨Θ 1, ?_⟩
  refine PontryaginDual.ext fun x => ?_
  have hx : x = e.symm (Multiplicative.ofAdd (rho e x)) := by simp [rho]
  rw [chr_apply, mul_comm, ← hlin, hΘx]
  show χ x = χ (e.symm (Multiplicative.ofAdd (rho e x)))
  rw [← hx]

/-- A good subgroup of `G ≅ ℝ` is trivial. -/
lemma good_eq_bot (e : G ≃ₜ* Multiplicative ℝ) {k : Subgroup G} (hk : IsGoodSubgroup k) :
    k = ⊥ := by
  obtain ⟨_, hopen, _⟩ := hk
  have h1 : (1 : PontryaginDual G) ∈ annihilator k := fun x _ => rfl
  have hpre : IsOpen (chr e ⁻¹' annihilator k) := hopen.preimage (continuous_chr e)
  have h0 : (0 : ℝ) ∈ chr e ⁻¹' annihilator k := by
    show chr e 0 ∈ annihilator k
    rw [chr_zero]; exact h1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0
  rw [eq_bot_iff]
  intro x0 hx0
  rw [Subgroup.mem_bot]
  by_contra hne
  set c := rho e x0
  have hc : c ≠ 0 := by
    intro h; apply hne; apply rho_injective e; rw [show rho e 1 = 0 by simp [rho]]; exact h
  set δ := min (ε * |c| / 2) Real.pi
  have hδ : 0 < δ := lt_min (by positivity) Real.pi_pos
  have hδπ : δ ≤ Real.pi := min_le_right _ _
  have ht : δ / c ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hδ,
      div_lt_iff₀ (abs_pos.2 hc)]
    have := min_le_left (ε * |c| / 2) Real.pi
    have : 0 < ε * |c| := by positivity
    linarith
  have hmem := hball ht x0 hx0
  rw [chr_apply, div_mul_cancel₀ _ hc, Circle.exp_eq_one] at hmem
  obtain ⟨n, hn⟩ := hmem
  have hpi := Real.pi_pos
  rcases lt_trichotomy n 0 with h | h | h
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt h
    nlinarith
  · rw [h] at hn; simp at hn; linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith

lemma isClosed_bot (e : G ≃ₜ* Multiplicative ℝ) : IsClosed ((⊥ : Subgroup G) : Set G) := by
  have : ((⊥ : Subgroup G) : Set G) = e ⁻¹' {1} := by
    ext x; simp [Subgroup.mem_bot]
  rw [this]
  exact isClosed_singleton.preimage e.continuous

/-- The trivial subgroup of `G ≅ ℝ` is good. -/
lemma bot_good (e : G ≃ₜ* Multiplicative ℝ) : IsGoodSubgroup (⊥ : Subgroup G) := by
  have hann : annihilator (⊥ : Subgroup G) = Set.univ := by
    ext χ; simp only [Set.mem_univ, iff_true]
    intro x hx; rw [Subgroup.mem_bot] at hx; rw [hx, map_one]
  refine ⟨isClosed_bot e, by rw [hann]; exact isOpen_univ, ⊤, by rw [hann]; rfl, ?_⟩
  let U : Set (PontryaginDual G) := chr e '' Set.Icc (-(Real.pi / 2)) (Real.pi / 2)
  refine ⟨U, isCompact_Icc.image (continuous_chr e), Set.subset_univ _, ?_, ?_⟩
  · let K : Set G := (fun t : ℝ => e.symm (Multiplicative.ofAdd t)) '' Set.Icc (-1) 1
    have hK : IsCompact K :=
      isCompact_Icc.image (e.symm.continuous.comp continuous_ofAdd)
    let O : Set Circle := {z | 0 < (z : ℂ).re}
    have hO : IsOpen O := isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)
    refine ⟨{χ | Set.MapsTo χ K O}, ?_, ?_⟩
    · refine IsOpen.mem_nhds ?_ ?_
      · exact (ContinuousMap.isOpen_setOf_mapsTo hK hO).preimage
          (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
      · intro x _; show 0 < ((1 : Circle) : ℂ).re; simp
    · rintro χ ⟨hχ, -⟩
      obtain ⟨t, rfl⟩ := char_classification e χ
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩ <;> by_contra hlt <;> push_neg at hlt
      · -- t < -π/2 : evaluate at x = -(π/2)/t ∈ [-1, 1]
        have ht0 : t < 0 := by linarith [Real.pi_pos]
        have hx : -(Real.pi / 2) / t ∈ Set.Icc (-1 : ℝ) 1 := by
          constructor
          · rw [le_div_iff_of_neg ht0]; linarith [Real.pi_pos]
          · rw [div_le_iff_of_neg ht0]; linarith [Real.pi_pos]
        have := hχ ⟨_, hx, rfl⟩
        simp only [O, Set.mem_setOf_eq, chr_apply, rho_symm, Circle.coe_exp] at this
        rw [mul_div_cancel₀ _ ht0.ne, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
          Real.cos_pi_div_two] at this
        exact lt_irrefl _ this
      · have ht0 : 0 < t := by linarith [Real.pi_pos]
        have hx : (Real.pi / 2) / t ∈ Set.Icc (-1 : ℝ) 1 := by
          constructor
          · rw [le_div_iff₀ ht0]; linarith [Real.pi_pos]
          · rw [div_le_iff₀ ht0]; linarith [Real.pi_pos]
        have := hχ ⟨_, hx, rfl⟩
        simp only [O, Set.mem_setOf_eq, chr_apply, rho_symm, Circle.coe_exp] at this
        rw [mul_div_cancel₀ _ ht0.ne', Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_two] at this
        exact lt_irrefl _ this
  · rw [eq_top_iff]
    intro χ _
    obtain ⟨t, rfl⟩ := char_classification e χ
    obtain ⟨N, hN⟩ := exists_nat_gt (|t| * 2 / Real.pi)
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hmem : chr e (t / N) ∈ U := by
      refine ⟨t / N, ⟨?_, ?_⟩, rfl⟩
      · rw [le_div_iff₀ hNpos]
        have := neg_abs_le t
        have : |t| < N * (Real.pi / 2) := by
          rw [div_lt_iff₀ Real.pi_pos] at hN; linarith
        linarith
      · rw [div_le_iff₀ hNpos]
        have := le_abs_self t
        have : |t| < N * (Real.pi / 2) := by
          rw [div_lt_iff₀ Real.pi_pos] at hN; linarith
        linarith
    have : chr e t = chr e (t / N) ^ N := by
      rw [← chr_nsmul, mul_div_cancel₀ _ hNpos.ne']
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure hmem) _


lemma connected (e : G ≃ₜ* Multiplicative ℝ) : ConnectedSpace G := by
  have hs : Function.Surjective (fun t : ℝ => e.symm (Multiplicative.ofAdd t)) := by
    intro x; exact ⟨rho e x, by simp [rho]⟩
  exact hs.connectedSpace (e.symm.continuous.comp continuous_ofAdd)

lemma open_subgroup_top (e : G ≃ₜ* Multiplicative ℝ) {Γ : Subgroup G}
    (hΓ : IsOpen (Γ : Set G)) : Γ = ⊤ := by
  haveI := connected e
  have hcl := Subgroup.isClosed_of_isOpen Γ hΓ
  rcases isClopen_iff.1 ⟨hcl, hΓ⟩ with h | h
  · exact absurd (h ▸ Γ.one_mem : (1 : G) ∈ (∅ : Set G)) (Set.notMem_empty _)
  · exact Subgroup.coe_eq_univ.1 h

lemma rapid_zero {m n r s : ℕ} {d : Fin s → ℕ} : IsRapidDecay (0 : ElemGroup m n r s d → ℂ) := by
  refine ⟨fun a b => ?_, fun i j k => ⟨0, fun a b xt => ?_⟩⟩
  · exact (contDiff_const : ContDiff ℝ _ (fun _ : (Fin m → ℝ) × (Fin n → ℝ) => (0 : ℂ)))
  · have : elemLift (0 : ElemGroup m n r s d → ℂ) a b = fun _ => 0 := rfl
    rw [this, iteratedFDeriv_zero_fun]; simp

lemma elemLift_add {m n r s : ℕ} {d : Fin s → ℕ} (f g : ElemGroup m n r s d → ℂ) (a b) :
    elemLift (f + g) a b = elemLift f a b + elemLift g a b := rfl

lemma elemLift_smul {m n r s : ℕ} {d : Fin s → ℕ} (c : ℂ) (f : ElemGroup m n r s d → ℂ) (a b) :
    elemLift (c • f) a b = c • elemLift f a b := rfl

lemma rapid_add {m n r s : ℕ} {d : Fin s → ℕ} {f g : ElemGroup m n r s d → ℂ}
    (hf : IsRapidDecay f) (hg : IsRapidDecay g) : IsRapidDecay (f + g) := by
  refine ⟨fun a b => by rw [elemLift_add]; exact (hf.1 a b).add (hg.1 a b), fun i j k => ?_⟩
  obtain ⟨C1, h1⟩ := hf.2 i j k
  obtain ⟨C2, h2⟩ := hg.2 i j k
  refine ⟨C1 + C2, fun a b xt => ?_⟩
  rw [elemLift_add, iteratedFDeriv_add_apply
    (((hf.1 a b).of_le (by exact_mod_cast le_top)).contDiffAt)
    (((hg.1 a b).of_le (by exact_mod_cast le_top)).contDiffAt)]
  have := norm_add_le (iteratedFDeriv ℝ k (elemLift f a b) xt)
    (iteratedFDeriv ℝ k (elemLift g a b) xt)
  have hn : 0 ≤ ‖a‖ ^ j * ‖xt.1‖ ^ i := by positivity
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt +
        iteratedFDeriv ℝ k (elemLift g a b) xt‖ ≤
      ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖iteratedFDeriv ℝ k (elemLift f a b) xt‖ +
        ‖iteratedFDeriv ℝ k (elemLift g a b) xt‖) := mul_le_mul_of_nonneg_left this hn
    _ ≤ C1 + C2 := by rw [mul_add]; linarith [h1 a b xt, h2 a b xt]

lemma rapid_smul {m n r s : ℕ} {d : Fin s → ℕ} (c : ℂ) {f : ElemGroup m n r s d → ℂ}
    (hf : IsRapidDecay f) : IsRapidDecay (c • f) := by
  refine ⟨fun a b => by rw [elemLift_smul]; exact (hf.1 a b).const_smul c, fun i j k => ?_⟩
  obtain ⟨C1, h1⟩ := hf.2 i j k
  refine ⟨‖c‖ * C1, fun a b xt => ?_⟩
  rw [elemLift_smul, iteratedFDeriv_const_smul_apply
    (((hf.1 a b).of_le (by exact_mod_cast le_top)).contDiffAt), norm_smul]
  have := h1 a b xt
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i * (‖c‖ * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖) =
      ‖c‖ * (‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f a b) xt‖) := by ring
    _ ≤ ‖c‖ * C1 := mul_le_mul_of_nonneg_left this (norm_nonneg c)

lemma rapid_of_elem {m n r s : ℕ} {d : Fin s → ℕ} (g : ElemSchwartz m n r s d) :
    IsRapidDecay g.toFun := by
  have h : g.toFun ∈ Submodule.span ℂ {g | IsRapidDecay g} := g.2
  exact Submodule.span_induction (p := fun x _ => IsRapidDecay x) (fun x hx => hx) rapid_zero
    (fun x y _ _ hx hy => rapid_add hx hy) (fun c x _ hx => rapid_smul c hx) h

/-- The shape of an elementary presentation of `G ≅ ℝ`: a rescaling of the real line. -/
lemma presentation_shape (e : G ≃ₜ* Multiplicative ℝ) {Γ k : Subgroup G} {m n r s : ℕ}
    {d : Fin s → ℕ} {π : Γ →* Multiplicative (ElemGroup m n r s d)}
    (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π) :
    IsEmpty (Fin n) ∧ ∃ v : Fin m → ℝ, v ≠ 0 ∧ ∀ (x : G) (hx : x ∈ Γ),
      Multiplicative.toAdd (π ⟨x, hx⟩) = (rho e x • v, fun _ => 0, 0, 0) := by
  have hΓ := open_subgroup_top e hs.1
  have hk := good_eq_bot e hs.2.2.1
  subst hΓ hk
  obtain ⟨_, hπc, hπo, hπs, hπk⟩ := hπ
  let ι : ℝ → (⊤ : Subgroup G) := fun t => ⟨e.symm (Multiplicative.ofAdd t), Subgroup.mem_top _⟩
  have hιc : Continuous ι := (e.symm.continuous.comp continuous_ofAdd).subtype_mk _
  let P : ℝ → ElemGroup m n r s d := fun t => Multiplicative.toAdd (π (ι t))
  have hPadd : ∀ s t, P (s + t) = P s + P t := by
    intro s t
    have : ι (s + t) = ι s * ι t := by
      apply Subtype.ext; simp [ι, ofAdd_add]
    simp only [P, this, map_mul, toAdd_mul]
  have hP0 : P 0 = 0 := by
    have := hPadd 0 0; simp only [add_zero] at this
    exact left_eq_add.1 this
  have hPc : Continuous P := continuous_toAdd.comp (hπc.comp hιc)
  have hιs : Function.Surjective ι := by
    rintro ⟨x, hx⟩
    exact ⟨rho e x, Subtype.ext (by simp [ι, rho])⟩
  have hPs : Function.Surjective P := by
    intro w
    obtain ⟨y, hy⟩ := hπs (Multiplicative.ofAdd w)
    obtain ⟨t, rfl⟩ := hιs y
    exact ⟨t, by simp [P, hy]⟩
  have hPi : Function.Injective P := by
    have h0 : ∀ t, P t = 0 → t = 0 := by
      intro t ht
      have h1 : π (ι t) = 1 := by
        have : Multiplicative.toAdd (π (ι t)) = 0 := ht
        simpa using congrArg Multiplicative.ofAdd this
      have := (hπk (ι t)).1 h1
      rw [Subgroup.mem_bot] at this
      have := congrArg (rho e) this
      simpa [ι, rho] using this
    intro s t hst
    have : P (s - t) = 0 := by
      have := hPadd (s - t) t
      rw [sub_add_cancel, hst] at this
      exact add_eq_right.1 this.symm
    exact sub_eq_zero.1 (h0 _ this)
  haveI : PreconnectedSpace ℝ := inferInstance
  -- discrete components are constant
  have h3 : ∀ t, (P t).2.2.1 = 0 := fun t => by
    have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℝ)
      (f := fun t => (P t).2.2.1) (continuous_fst.comp (continuous_snd.comp
        (continuous_snd.comp hPc))) (x := t) (y := 0)
    rw [this, hP0]; rfl
  have h4 : ∀ t, (P t).2.2.2 = 0 := fun t => by
    have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℝ)
      (f := fun t => (P t).2.2.2) (continuous_snd.comp (continuous_snd.comp
        (continuous_snd.comp hPc))) (x := t) (y := 0)
    rw [this, hP0]; rfl
  -- the vector part is linear
  let P1 : ℝ →+ (Fin m → ℝ) :=
    ⟨⟨fun t => (P t).1, by simp [hP0]⟩, fun s t => by simp [hPadd]⟩
  have hP1c : Continuous P1 := continuous_fst.comp hPc
  set v := (P 1).1 with hv
  have hP1 : ∀ t, (P t).1 = t • v := by
    intro t
    have := map_real_smul P1 hP1c t 1
    simpa [P1, smul_eq_mul] using this
  -- v ≠ 0, otherwise `ElemGroup` would be compact
  have hv0 : v ≠ 0 := by
    intro hv0
    let K : Set (ElemGroup m n r s d) :=
      Set.range (fun θ : Fin n → UnitAddCircle => ((0 : Fin m → ℝ), θ, (0 : Fin r → ℤ),
        (0 : (i : Fin s) → ZMod (d i))))
    have hK : IsCompact K := isCompact_range (by fun_prop)
    have hKu : (Set.univ : Set (ElemGroup m n r s d)) ⊆ K := by
      intro w _
      obtain ⟨t, rfl⟩ := hPs w
      refine ⟨(P t).2.1, ?_⟩
      ext1
      · simp [hP1, hv0]
      ext1
      · rfl
      ext1
      · exact (h3 t).symm
      · exact (h4 t).symm
    have hPo : IsOpenMap P := by
      intro U hU
      have h1 : IsOpen (ι '' U) := by
        have : ι '' U = Subtype.val ⁻¹' ((fun t => e.symm (Multiplicative.ofAdd t)) '' U) := by
          ext ⟨x, hx⟩
          simp only [Set.mem_image, Set.mem_preimage, ι, Subtype.mk.injEq]
        rw [this]
        refine IsOpen.preimage continuous_subtype_val ?_
        have he : IsOpenMap (fun t : ℝ => e.symm (Multiplicative.ofAdd t)) :=
          e.symm.toHomeomorph.isOpenMap.comp (Homeomorph.isOpenMap (Homeomorph.refl ℝ))
        exact he U hU
      have h2 := hπo _ h1
      have : P '' U = Multiplicative.ofAdd ⁻¹' (π '' (ι '' U)) := by
        ext w; simp [P, Set.image_image]
        constructor
        · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by simp⟩
        · rintro ⟨t, ht, h⟩; exact ⟨t, ht, by rw [h]; rfl⟩
      rw [this]
      exact h2.preimage continuous_ofAdd
    let E : ℝ ≃ₜ ElemGroup m n r s d :=
      (Equiv.ofBijective P ⟨hPi, hPs⟩).toHomeomorphOfContinuousOpen hPc hPo
    have hU : IsCompact (Set.univ : Set (ElemGroup m n r s d)) :=
      hK.of_isClosed_subset isClosed_univ hKu
    have := hU.image E.symm.continuous
    rw [Set.image_univ, E.symm.surjective.range_eq] at this
    exact (not_compactSpace_iff.2 (inferInstance : NoncompactSpace ℝ)) (isCompact_univ_iff.1 this)
  -- no torus factor
  have hn : IsEmpty (Fin n) := by
    by_contra hne
    rw [not_isEmpty_iff] at hne
    obtain ⟨j⟩ := hne
    let w : ElemGroup m n r s d := (0, fun _ => ((1 / 2 : ℝ) : UnitAddCircle), 0, 0)
    obtain ⟨t, ht⟩ := hPs w
    have ht1 : t • v = 0 := by rw [← hP1, ht]
    rcases smul_eq_zero.1 ht1 with h | h
    · rw [h, hP0] at ht
      have := congrArg (fun z => z.2.1 j) ht
      simp only [w] at this
      have h2 := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 this.symm
      obtain ⟨k, hk⟩ := h2
      rw [zsmul_eq_mul, mul_one] at hk
      have h3 : (2 : ℝ) * k = 1 := by rw [hk]; ring
      have h4 : (2 * k : ℤ) = 1 := by exact_mod_cast h3
      omega
    · exact hv0 h
  refine ⟨hn, v, hv0, fun x hx => ?_⟩
  have hx' : (⟨x, hx⟩ : (⊤ : Subgroup G)) = ι (rho e x) := Subtype.ext (by simp [ι, rho])
  rw [hx']
  show P (rho e x) = _
  ext1
  · exact hP1 _
  ext1
  · funext j; exact hn.elim j
  ext1
  · exact h3 _
  · exact h4 _

/-- The linear map `t ↦ (t • v, 0)`. -/
noncomputable def lineMap {m n : ℕ} (v : Fin m → ℝ) : ℝ →L[ℝ] (Fin m → ℝ) × (Fin n → ℝ) :=
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v).prod 0

lemma lineMap_apply {m n : ℕ} (v : Fin m → ℝ) (t : ℝ) :
    lineMap (n := n) v t = (t • v, 0) := by
  simp [lineMap]

/-- Rapid decay along a line gives a Schwartz function, with explicit seminorm control. -/
lemma schwartz_of_line {m n : ℕ} (h : (Fin m → ℝ) × (Fin n → ℝ) → ℂ)
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    (hb : ∀ i k : ℕ, ∃ C : ℝ, ∀ xt, ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k h xt‖ ≤ C)
    (v : Fin m → ℝ) (hv : v ≠ 0) :
    ∃ φ : SchwartzMap ℝ ℂ, ∀ t, φ t = h (lineMap (n := n) v t) := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  refine ⟨⟨fun t => h (lineMap v t), hh.comp (lineMap v).contDiff, fun i k => ?_⟩, fun t => rfl⟩
  obtain ⟨C, hC⟩ := hb i k
  refine ⟨(‖v‖⁻¹) ^ i * ‖lineMap (n := n) v‖ ^ k * C, fun t => ?_⟩
  have hcomp := (lineMap (n := n) v).iteratedFDeriv_comp_right hh t
    (i := k) (by exact_mod_cast le_top)
  have hnorm : ‖iteratedFDeriv ℝ k (fun t => h (lineMap v t)) t‖ ≤
      ‖iteratedFDeriv ℝ k h (lineMap v t)‖ * ‖lineMap (n := n) v‖ ^ k := by
    have : (fun t => h (lineMap (n := n) v t)) = h ∘ lineMap v := rfl
    rw [this, hcomp]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const]
  have ht : ‖t‖ = ‖(lineMap (n := n) v t).1‖ / ‖v‖ := by
    rw [lineMap_apply, norm_smul, mul_div_cancel_right₀ _ hvn.ne']
  have e1 := hC (lineMap v t)
  have hL := norm_nonneg (lineMap (n := n) v)
  calc ‖t‖ ^ i * ‖iteratedFDeriv ℝ k (fun t => h (lineMap v t)) t‖ ≤
      ‖t‖ ^ i * (‖iteratedFDeriv ℝ k h (lineMap v t)‖ * ‖lineMap (n := n) v‖ ^ k) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (‖v‖⁻¹) ^ i * ‖lineMap (n := n) v‖ ^ k *
        (‖(lineMap (n := n) v t).1‖ ^ i * ‖iteratedFDeriv ℝ k h (lineMap v t)‖) := by
        rw [ht, div_eq_mul_inv, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left e1 (by positivity)


lemma line_bound {m n : ℕ} (h : (Fin m → ℝ) × (Fin n → ℝ) → ℂ)
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) (v : Fin m → ℝ) (hv : v ≠ 0) (i k : ℕ) {δ : ℝ}
    (hδ : ∀ xt, ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k h xt‖ ≤ δ) (t : ℝ) :
    ‖t‖ ^ i * ‖iteratedFDeriv ℝ k (fun t => h (lineMap (n := n) v t)) t‖ ≤
      (‖v‖⁻¹) ^ i * ‖lineMap (n := n) v‖ ^ k * δ := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hcomp := (lineMap (n := n) v).iteratedFDeriv_comp_right hh t
    (i := k) (by exact_mod_cast le_top)
  have hnorm : ‖iteratedFDeriv ℝ k (fun t => h (lineMap (n := n) v t)) t‖ ≤
      ‖iteratedFDeriv ℝ k h (lineMap v t)‖ * ‖lineMap (n := n) v‖ ^ k := by
    have : (fun t => h (lineMap (n := n) v t)) = h ∘ lineMap v := rfl
    rw [this, hcomp]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const]
  have ht : ‖t‖ = ‖(lineMap (n := n) v t).1‖ / ‖v‖ := by
    rw [lineMap_apply, norm_smul, mul_div_cancel_right₀ _ hvn.ne']
  have e1 := hδ (lineMap v t)
  have hL := norm_nonneg (lineMap (n := n) v)
  calc ‖t‖ ^ i * ‖iteratedFDeriv ℝ k (fun t => h (lineMap (n := n) v t)) t‖ ≤
      ‖t‖ ^ i * (‖iteratedFDeriv ℝ k h (lineMap v t)‖ * ‖lineMap (n := n) v‖ ^ k) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (‖v‖⁻¹) ^ i * ‖lineMap (n := n) v‖ ^ k *
        (‖(lineMap (n := n) v t).1‖ ^ i * ‖iteratedFDeriv ℝ k h (lineMap v t)‖) := by
        rw [ht, div_eq_mul_inv, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left e1 (by positivity)

/-- The weighted derivative appearing in the topology of `ElemSchwartz`. -/
noncomputable def W {m n r s : ℕ} {d : Fin s → ℕ} (g : ElemGroup m n r s d → ℂ)
    (p : ℕ × ℕ × ℕ) (q : (Fin r → ℤ) × ((i : Fin s) → ZMod (d i)) × ((Fin m → ℝ) × (Fin n → ℝ))) :
    ContinuousMultilinearMap ℝ (fun _ : Fin p.2.2 => (Fin m → ℝ) × (Fin n → ℝ)) ℂ :=
  (‖q.1‖ ^ p.2.1 * ‖q.2.2.1‖ ^ p.1) • iteratedFDeriv ℝ p.2.2 (elemLift g q.1 q.2.1) q.2.2

lemma W_sub {m n r s : ℕ} {d : Fin s → ℕ} {f g : ElemGroup m n r s d → ℂ}
    (hf : IsRapidDecay f) (hg : IsRapidDecay g) (p q) : W (f - g) p q = W f p q - W g p q := by
  unfold W
  have : elemLift (f - g) q.1 q.2.1 = elemLift f q.1 q.2.1 - elemLift g q.1 q.2.1 := rfl
  rw [this, iteratedFDeriv_sub_apply
    (((hf.1 _ _).of_le (by exact_mod_cast le_top)).contDiffAt)
    (((hg.1 _ _).of_le (by exact_mod_cast le_top)).contDiffAt), smul_sub]

lemma norm_W_zero {m n r s : ℕ} {d : Fin s → ℕ} (f : ElemGroup m n r s d → ℂ) (i k : ℕ) (xt) :
    ‖W f (i, 0, k) (0, 0, xt)‖ = ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (elemLift f 0 0) xt‖ := by
  unfold W
  rw [norm_smul, Real.norm_of_nonneg (by positivity), pow_zero, one_mul]

lemma elem_eventually {m n r s : ℕ} {d : Fin s → ℕ} (g0 : ElemSchwartz m n r s d)
    (p : ℕ × ℕ × ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ g in 𝓝 g0, ∀ q, dist (W g.toFun p q) (W g0.toFun p q) < δ := by
  rw [nhds_induced]
  have hU := (UniformFun.hasBasis_nhds _ _ (UniformFun.ofFun (W g0.toFun p))).mem_of_mem
    (Metric.dist_mem_uniformity hδ)
  have hT := ((continuous_apply p).tendsto
    (fun p => UniformFun.ofFun (W g0.toFun p))) hU
  refine Filter.mem_of_superset (Filter.preimage_mem_comap hT) (fun g hg q => ?_)
  have := hg q
  rw [dist_comm]
  exact this

/-- Continuity of an arbitrary presentation, read in Schwartz coordinates. -/
lemma T1 (e : G ≃ₜ* Multiplicative ℝ) {Γ k : Subgroup G} {m n r s : ℕ} {d : Fin s → ℕ}
    {π : Γ →* Multiplicative (ElemGroup m n r s d)} (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (T : ElemSchwartz m n r s d → SchwartzMap ℝ ℂ)
    (hT : ∀ g t, T g t =
      (SchwartzBruhat.ofElem Γ k π hs hπ g).toFun (e.symm (Multiplicative.ofAdd t))) :
    Continuous T := by
  obtain ⟨hn, v, hv, hform⟩ := presentation_shape e hs hπ
  have hΓ := open_subgroup_top e hs.1
  have hval : ∀ g t, T g t = elemLift g.toFun 0 0 (lineMap (n := n) v t) := by
    intro g t
    rw [hT]
    show extendPullback Γ π g.toFun (e.symm (Multiplicative.ofAdd t)) = _
    unfold extendPullback
    have hmem : e.symm (Multiplicative.ofAdd t) ∈ Γ := by rw [hΓ]; trivial
    rw [dif_pos hmem, hform, rho_symm, lineMap_apply]
    unfold elemLift
    congr 2
    try (funext j; exact hn.elim j)
  have hsub : ∀ g g0, T g - T g0 = T (g - g0) := fun g g0 =>
    SchwartzMap.ext fun t => by
      rw [SchwartzMap.sub_apply, hval, hval, hval]; rfl
  refine continuous_iff_continuousAt.2 fun g0 => ?_
  rw [ContinuousAt, (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
  intro i ε hε
  set K := (‖v‖⁻¹) ^ i.1 * ‖lineMap (n := n) v‖ ^ i.2 with hK
  have hK0 : 0 ≤ K := by positivity
  set δ := ε / (2 * (K + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  filter_upwards [elem_eventually g0 (i.1, 0, i.2) hδ] with g hg
  rw [hsub]
  show SchwartzMap.seminorm ℂ i.1 i.2 (T (g - g0)) < ε
  have hr := rapid_of_elem (g - g0)
  have hb : ∀ xt, ‖xt.1‖ ^ i.1 * ‖iteratedFDeriv ℝ i.2 (elemLift (g - g0).toFun 0 0) xt‖ ≤ δ := by
    intro xt
    rw [← norm_W_zero]
    have := hg (0, 0, xt)
    rw [dist_eq_norm, ← W_sub (rapid_of_elem g) (rapid_of_elem g0)] at this
    exact this.le
  have hfun : ⇑(T (g - g0)) = fun t => elemLift (g - g0).toFun 0 0 (lineMap (n := n) v t) :=
    funext (hval _)
  have hle : SchwartzMap.seminorm ℂ i.1 i.2 (T (g - g0)) ≤ K * δ := by
    refine SchwartzMap.seminorm_le_bound ℂ i.1 i.2 _ (by positivity) (fun t => ?_)
    rw [hfun]
    exact line_bound _ (hr.1 0 0) v hv i.1 i.2 hb t
  calc _ ≤ K * δ := hle
    _ < ε := by
      rw [hδdef]
      rw [show K * (ε / (2 * (K + 1))) = ε * (K / (2 * (K + 1))) by ring]
      have : K / (2 * (K + 1)) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      nlinarith

/-! ### The standard presentation -/

noncomputable def proj1 : (Fin 1 → ℝ) × (Fin 0 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
    (ContinuousLinearMap.fst ℝ _ _)

lemma proj1_apply (xt : (Fin 1 → ℝ) × (Fin 0 → ℝ)) : proj1 xt = xt.1 0 := rfl

lemma std_bound (φ : SchwartzMap ℝ ℂ) (i j k : ℕ) (a : Fin 0 → ℤ)
    (xt : (Fin 1 → ℝ) × (Fin 0 → ℝ)) :
    ‖a‖ ^ j * ‖xt.1‖ ^ i * ‖iteratedFDeriv ℝ k (fun w : (Fin 1 → ℝ) × (Fin 0 → ℝ) => φ (w.1 0)) xt‖
      ≤ ‖proj1‖ ^ k * SchwartzMap.seminorm ℂ i k φ := by
  have ha : ‖a‖ ^ j ≤ 1 := by
    rw [Subsingleton.elim a 0, norm_zero]
    exact pow_le_one₀ le_rfl zero_le_one
  have hx : ‖xt.1‖ ≤ ‖xt.1 0‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by rw [Subsingleton.elim j 0]
  have hcomp := proj1.iteratedFDeriv_comp_right (φ.smooth ⊤) xt (i := k)
    (by exact_mod_cast le_top)
  have hnorm : ‖iteratedFDeriv ℝ k (fun w : (Fin 1 → ℝ) × (Fin 0 → ℝ) => φ (w.1 0)) xt‖ ≤
      ‖iteratedFDeriv ℝ k φ (xt.1 0)‖ * ‖proj1‖ ^ k := by
    have : (fun w : (Fin 1 → ℝ) × (Fin 0 → ℝ) => φ (w.1 0)) = ⇑φ ∘ proj1 := rfl
    rw [this, hcomp]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp [Finset.prod_const, proj1_apply]
  have hs := SchwartzMap.le_seminorm ℂ i k φ (xt.1 0)
  have h1 : ‖xt.1‖ ^ i ≤ ‖xt.1 0‖ ^ i := pow_le_pow_left₀ (norm_nonneg _) hx i
  have hD := norm_nonneg (iteratedFDeriv ℝ k φ (xt.1 0))
  have hP : 0 ≤ ‖proj1‖ ^ k := by positivity
  calc ‖a‖ ^ j * ‖xt.1‖ ^ i *
        ‖iteratedFDeriv ℝ k (fun w : (Fin 1 → ℝ) × (Fin 0 → ℝ) => φ (w.1 0)) xt‖
      ≤ 1 * ‖xt.1 0‖ ^ i * (‖iteratedFDeriv ℝ k φ (xt.1 0)‖ * ‖proj1‖ ^ k) := by
        gcongr
    _ = ‖proj1‖ ^ k * (‖xt.1 0‖ ^ i * ‖iteratedFDeriv ℝ k φ (xt.1 0)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs hP

lemma rapid_std (φ : SchwartzMap ℝ ℂ) :
    IsRapidDecay (fun w : ElemGroup 1 0 0 0 (fun _ => 1) => φ (w.1 0)) :=
  ⟨fun _ _ => (φ.smooth ⊤).comp proj1.contDiff,
    fun i j k => ⟨_, fun a _ xt => std_bound φ i j k a xt⟩⟩

noncomputable def stdElem (φ : SchwartzMap ℝ ℂ) : ElemSchwartz 1 0 0 0 (fun _ => 1) :=
  (⟨fun w => φ (w.1 0), by
    unfold elemSchwartzSubmodule; exact Submodule.subset_span (rapid_std φ)⟩ :
    ↥(elemSchwartzSubmodule 1 0 0 0 (fun _ => 1)))

lemma stdElem_toFun (φ : SchwartzMap ℝ ℂ) (w : ElemGroup 1 0 0 0 (fun _ => 1)) :
    (stdElem φ).toFun w = φ (w.1 0) := rfl

lemma T2 : Continuous stdElem := by
  refine continuous_induced_rng.2 (continuous_pi fun p => ?_)
  refine continuous_iff_continuousAt.2 fun φ0 => ?_
  rw [ContinuousAt, (UniformFun.hasBasis_nhds _ _ _).tendsto_right_iff]
  intro V hV
  obtain ⟨δ, hδ, hVδ⟩ := Metric.mem_uniformity_dist.1 hV
  set η := δ / (‖proj1‖ ^ p.2.2 + 1)
  have hη : 0 < η := by positivity
  have hev := ((schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds id φ0).1 Filter.tendsto_id
    (p.1, p.2.2) η hη
  filter_upwards [hev] with φ hφ
  intro q
  apply hVδ
  show dist (W (stdElem φ0).toFun p q) (W (stdElem φ).toFun p q) < δ
  rw [dist_comm, dist_eq_norm]
  have hsub : W (stdElem φ).toFun p q - W (stdElem φ0).toFun p q =
      W (stdElem (φ - φ0)).toFun p q := by
    exact (W_sub (rapid_std φ) (rapid_std φ0) p q).symm
  rw [hsub]
  unfold W
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hb := std_bound (φ - φ0) p.1 p.2.1 p.2.2 q.1 q.2.2
  have hφ' : SchwartzMap.seminorm ℂ p.1 p.2.2 (φ - φ0) < η := hφ
  have hP : 0 ≤ ‖proj1‖ ^ p.2.2 := by positivity
  calc _ ≤ ‖proj1‖ ^ p.2.2 * SchwartzMap.seminorm ℂ p.1 p.2.2 (φ - φ0) := hb
    _ ≤ ‖proj1‖ ^ p.2.2 * η := mul_le_mul_of_nonneg_left hφ'.le hP
    _ < δ := by
      rw [show η = δ / (‖proj1‖ ^ p.2.2 + 1) from rfl, mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith

noncomputable def stdPres (e : G ≃ₜ* Multiplicative ℝ) :
    (⊤ : Subgroup G) →* Multiplicative (ElemGroup 1 0 0 0 (fun _ => 1)) where
  toFun x := Multiplicative.ofAdd ((fun _ => rho e x.1), 0, 0, 0)
  map_one' := by
    show _ = Multiplicative.ofAdd 0
    congr 1
    ext1
    · funext j; simp [rho]
    · rfl
  map_mul' x y := by
    rw [← ofAdd_add]
    congr 1
    ext1
    · funext j; simp [rho_mul]
    · simp

lemma stdPres_toAdd (e : G ≃ₜ* Multiplicative ℝ) (x : (⊤ : Subgroup G)) :
    Multiplicative.toAdd (stdPres e x) = ((fun _ => rho e x.1), 0, 0, 0) := rfl

lemma top_cg (e : G ≃ₜ* Multiplicative ℝ) : IsCompactlyGeneratedSubgroup (⊤ : Subgroup G) := by
  let ι : ℝ → G := fun t => e.symm (Multiplicative.ofAdd t)
  have hιc : Continuous ι := e.symm.continuous.comp continuous_ofAdd
  have hιo : IsOpenMap ι := by
    have : ι = e.symm.toHomeomorph ∘ (Homeomorph.refl ℝ).trans
        (Homeomorph.mk Multiplicative.ofAdd continuous_ofAdd continuous_toAdd) := rfl
    rw [this]
    exact e.symm.toHomeomorph.isOpenMap.comp (Homeomorph.isOpenMap _)
  refine ⟨ι '' Set.Icc (-1) 1, isCompact_Icc.image hιc, Set.subset_univ _, ?_, ?_⟩
  · refine ⟨ι '' Set.Ioo (-1) 1, (hιo _ isOpen_Ioo).mem_nhds ⟨0, ⟨by norm_num, by norm_num⟩, by
      simp [ι]⟩, ?_⟩
    rintro _ ⟨⟨t, ht, rfl⟩, -⟩
    exact ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨N, hN⟩ := exists_nat_gt |rho e x|
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (abs_nonneg _) hN
    have hmem : ι (rho e x / N) ∈ ι '' Set.Icc (-1) 1 := by
      refine ⟨_, ⟨?_, ?_⟩, rfl⟩
      · rw [le_div_iff₀ hNpos]; have := neg_abs_le (rho e x); linarith
      · rw [div_le_iff₀ hNpos]; have := le_abs_self (rho e x); linarith
    have hx : x = ι (rho e x / N) ^ N := by
      apply rho_injective e
      simp only [ι, ← map_pow, ← ofAdd_nsmul, rho_symm, nsmul_eq_mul]
      rw [mul_div_cancel₀ _ hNpos.ne']
    rw [hx]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure hmem) _

lemma std_struct (e : G ≃ₜ* Multiplicative ℝ) : IsStructuralPair (⊤ : Subgroup G) ⊥ :=
  ⟨by rw [Subgroup.coe_top]; exact isOpen_univ, top_cg e, bot_good e, bot_le⟩

lemma std_pres (e : G ≃ₜ* Multiplicative ℝ) :
    IsElemPresentation (⊤ : Subgroup G) ⊥ (stdPres e) := by
  let inv : Multiplicative (ElemGroup 1 0 0 0 (fun _ => 1)) → (⊤ : Subgroup G) := fun w =>
    ⟨e.symm (Multiplicative.ofAdd ((Multiplicative.toAdd w).1 0)), Subgroup.mem_top _⟩
  have hinvc : Continuous inv :=
    (e.symm.continuous.comp (continuous_ofAdd.comp ((continuous_apply 0).comp
      (continuous_fst.comp continuous_toAdd)))).subtype_mk _
  have hc : Continuous (stdPres e) :=
    continuous_ofAdd.comp ((continuous_pi fun _ => (continuous_rho e).comp
      continuous_subtype_val).prodMk continuous_const)
  have hl : Function.LeftInverse (stdPres e) inv := by
    intro w
    apply Multiplicative.toAdd.injective
    rw [stdPres_toAdd]
    ext1
    · funext j; rw [Subsingleton.elim j 0]; simp [inv, rho]
    · exact Subsingleton.elim _ _
  have hr : Function.RightInverse (stdPres e) inv := by
    intro x
    apply Subtype.ext
    simp [inv, stdPres_toAdd, rho]
  refine ⟨fun i => i.elim0, hc, IsOpenMap.of_inverse hinvc hl hr, hl.surjective, fun x => ?_⟩
  rw [Subgroup.mem_bot]
  constructor
  · intro h
    have := congrArg (fun w => (Multiplicative.toAdd w).1 0) h
    simp only [stdPres_toAdd] at this
    apply rho_injective e
    simpa [rho] using this
  · intro h
    apply Multiplicative.toAdd.injective
    rw [stdPres_toAdd, h]
    ext1
    · funext j; simp [rho]
    · rfl


lemma extend_std (e : G ≃ₜ* Multiplicative ℝ) (φ : SchwartzMap ℝ ℂ) (x : G) :
    extendPullback ⊤ (stdPres e) (stdElem φ).toFun x = φ (rho e x) := by
  unfold extendPullback
  rw [dif_pos (Subgroup.mem_top x)]
  rfl

lemma sb_mem_iff (e : G ≃ₜ* Multiplicative ℝ) (f : G → ℂ) :
    f ∈ schwartzBruhatSubmodule G ↔
      ∃ φ : SchwartzMap ℝ ℂ, ∀ t, φ t = f (e.symm (Multiplicative.ofAdd t)) := by
  constructor
  · intro hf
    unfold schwartzBruhatSubmodule at hf
    refine Submodule.span_induction (p := fun f _ => ∃ φ : SchwartzMap ℝ ℂ,
      ∀ t, φ t = f (e.symm (Multiplicative.ofAdd t))) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨Γ, k, m, n, r, s, d, π, g, hs, hπ, rfl⟩
      obtain ⟨hn, v, hv, hform⟩ := presentation_shape e hs hπ
      have hΓ := open_subgroup_top e hs.1
      have hr := rapid_of_elem g
      obtain ⟨φ, hφ⟩ := schwartz_of_line (elemLift g.toFun 0 0) (hr.1 0 0)
        (fun i k => by
          obtain ⟨C, hC⟩ := hr.2 i 0 k
          exact ⟨C, fun xt => by simpa using hC 0 0 xt⟩) v hv
      refine ⟨φ, fun t => ?_⟩
      rw [hφ]
      unfold extendPullback
      have hmem : e.symm (Multiplicative.ofAdd t) ∈ Γ := by rw [hΓ]; trivial
      rw [dif_pos hmem, hform, rho_symm, lineMap_apply]
      unfold elemLift
      congr 2
      try (funext j; exact hn.elim j)
    · exact ⟨0, fun t => by simp⟩
    · rintro x y _ _ ⟨φ1, h1⟩ ⟨φ2, h2⟩
      exact ⟨φ1 + φ2, fun t => by simp [h1, h2]⟩
    · rintro c x _ ⟨φ, h⟩
      exact ⟨c • φ, fun t => by simp [h]⟩
  · rintro ⟨φ, hφ⟩
    have : f = extendPullback ⊤ (stdPres e) (stdElem φ).toFun := by
      funext x; rw [extend_std, hφ]; simp [rho]
    rw [this]
    unfold schwartzBruhatSubmodule
    exact Submodule.subset_span ⟨⊤, ⊥, 1, 0, 0, 0, fun _ => 1, stdPres e, stdElem φ,
      std_struct e, std_pres e, rfl⟩

lemma sb_topology (e : G ≃ₜ* Multiplicative ℝ) (Ψ : SchwartzBruhat G → SchwartzMap ℝ ℂ)
    (hΨ : ∀ f t, Ψ f t = f.toFun (e.symm (Multiplicative.ofAdd t))) :
    (inferInstance : TopologicalSpace (SchwartzBruhat G)) =
      TopologicalSpace.induced Ψ inferInstance := by
  let Ψl : SchwartzBruhat G →ₗ[ℂ] SchwartzMap ℝ ℂ :=
    { toFun := Ψ
      map_add' := fun f g => SchwartzMap.ext fun t => by
        rw [SchwartzMap.add_apply, hΨ, hΨ, hΨ]; rfl
      map_smul' := fun c f => SchwartzMap.ext fun t => by
        rw [SchwartzMap.smul_apply, hΨ, hΨ]; rfl }
  have hLC : IsLocallyConvexTopology (SchwartzBruhat G)
      (TopologicalSpace.induced Ψ inferInstance) :=
    ⟨ℕ × ℕ, inferInstance, _, Ψl.withSeminorms_induced (schwartz_withSeminorms ℂ ℝ ℂ)⟩
  apply le_antisymm
  · refine sInf_le ⟨hLC, fun Γ k m n r s d π hs hπ => ?_⟩
    exact continuous_induced_rng.2 (T1 e hs hπ _ (fun g t => hΨ _ t))
  · refine le_sInf fun t ht => ?_
    have hc := ht.2 ⊤ ⊥ 1 0 0 0 (fun _ => 1) (stdPres e) (std_struct e) (std_pres e)
    have hid : (id : SchwartzBruhat G → SchwartzBruhat G) =
        SchwartzBruhat.ofElem ⊤ ⊥ (stdPres e) (std_struct e) (std_pres e) ∘ stdElem ∘ Ψ := by
      funext f
      apply Subtype.ext
      funext x
      show f.toFun x = extendPullback ⊤ (stdPres e) (stdElem (Ψ f)).toFun x
      rw [extend_std, hΨ]; simp [rho]
    rw [← continuous_id_iff_le, hid]
    exact @Continuous.comp _ _ _ (TopologicalSpace.induced Ψ inferInstance) _ t _ _ hc
      (@Continuous.comp _ _ _ (TopologicalSpace.induced Ψ inferInstance) _ _ _ _ T2
        continuous_induced_dom)

end AAux

/-! ### The exponential-decay space on `ℝ_{>0}` -/

namespace AAux

noncomputable def qbot :
    (Multiplicative ℝ ⧸ (⊥ : Subgroup (Multiplicative ℝ))) ≃ₜ* Multiplicative ℝ :=
  { QuotientGroup.quotientBot with
    continuous_toFun := by
      refine (QuotientGroup.isQuotientMap_mk (⊥ : Subgroup (Multiplicative ℝ))).continuous_iff.2 ?_
      exact continuous_id
    continuous_invFun := QuotientGroup.continuous_mk }

lemma qbot_symm (t : ℝ) : qbot.symm (Multiplicative.ofAdd t) =
    (QuotientGroup.mk (Multiplicative.ofAdd t) : Multiplicative ℝ ⧸ (⊥ : Subgroup _)) := rfl

lemma out_mk (x : Multiplicative ℝ) :
    (QuotientGroup.mk x : Multiplicative ℝ ⧸ (⊥ : Subgroup (Multiplicative ℝ))).out = x := by
  have h := QuotientGroup.out_eq' (QuotientGroup.mk x : Multiplicative ℝ ⧸
    (⊥ : Subgroup (Multiplicative ℝ)))
  rw [QuotientGroup.eq, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h

lemma rpos_pow (a t : ℝ) : rposModule (Multiplicative.ofAdd t) ^ a = Real.exp (a * t) := by
  unfold rposModule
  rw [toAdd_ofAdd, ← Real.exp_mul, mul_comm]

def RefEq (I : Set ℝ) (f : Multiplicative ℝ → ℂ) : Prop :=
  ∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ,
    g x = (Real.exp (a * x) : ℂ) * f (Multiplicative.ofAdd x)

lemma weight_mem_iff (a : ℝ) (f : Multiplicative ℝ → ℂ) :
    (fun g => ((rposModule g ^ a : ℝ) : ℂ) * f g) ∈ schwartzBruhatSubmodule (Multiplicative ℝ) ↔
      ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ,
        g x = (Real.exp (a * x) : ℂ) * f (Multiplicative.ofAdd x) := by
  rw [sb_mem_iff (ContinuousMulEquiv.refl _)]
  apply exists_congr
  intro g
  apply forall_congr'
  intro x
  show g x = ((rposModule (Multiplicative.ofAdd x) ^ a : ℝ) : ℂ) * f (Multiplicative.ofAdd x) ↔ _
  rw [rpos_pow]

lemma expDecay_mem_iff (I : Set ℝ) (hne : I.Nonempty) (f : Multiplicative ℝ → ℂ) :
    f ∈ expDecaySubmodule (Multiplicative ℝ) rposModule I ↔ RefEq I f := by
  have key : ∀ f : Multiplicative ℝ → ℂ, (Continuous f ∧ ∀ a ∈ I,
      (fun g => ((rposModule g ^ a : ℝ) : ℂ) * f g) ∈
        schwartzBruhatSubmodule (Multiplicative ℝ)) ↔ RefEq I f := by
    intro f
    constructor
    · rintro ⟨_, h⟩ a ha; exact (weight_mem_iff a f).1 (h a ha)
    · intro h
      refine ⟨?_, fun a ha => (weight_mem_iff a f).2 (h a ha)⟩
      obtain ⟨a0, ha0⟩ := hne
      obtain ⟨g, hg⟩ := h a0 ha0
      have : f = fun y => (Real.exp (-(a0 * Multiplicative.toAdd y)) : ℂ) *
          g (Multiplicative.toAdd y) := by
        funext y
        rw [hg, ofAdd_toAdd, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
          Real.exp_zero, Complex.ofReal_one, one_mul]
      rw [this]
      exact Continuous.mul (by fun_prop) (g.continuous.comp continuous_toAdd)
  constructor
  · intro hf
    unfold expDecaySubmodule at hf
    refine Submodule.span_induction (p := fun f _ => RefEq I f) (fun x hx => (key x).1 hx)
      ?_ ?_ ?_ hf
    · intro a _; exact ⟨0, fun x => by simp⟩
    · rintro x y _ _ hx hy a ha
      obtain ⟨g1, h1⟩ := hx a ha
      obtain ⟨g2, h2⟩ := hy a ha
      exact ⟨g1 + g2, fun x => by simp [h1, h2, mul_add]⟩
    · rintro c x _ hx a ha
      obtain ⟨g1, h1⟩ := hx a ha
      exact ⟨c • g1, fun x => by simp [h1]; ring⟩
  · intro h
    unfold expDecaySubmodule
    exact Submodule.subset_span ((key f).2 h)

end AAux

namespace AAux

abbrev Gq := Multiplicative ℝ ⧸ (⊥ : Subgroup (Multiplicative ℝ))

noncomputable def Ψq (F : SchwartzBruhat Gq) : SchwartzMap ℝ ℂ :=
  ((sb_mem_iff qbot F.toFun).1 F.2).choose

lemma Ψq_apply (F : SchwartzBruhat Gq) (t : ℝ) :
    Ψq F t = F.toFun (qbot.symm (Multiplicative.ofAdd t)) :=
  ((sb_mem_iff qbot F.toFun).1 F.2).choose_spec t

lemma sbq_top : (inferInstance : TopologicalSpace (SchwartzBruhat Gq)) =
    TopologicalSpace.induced Ψq inferInstance := sb_topology qbot Ψq Ψq_apply

lemma Ψq_cont : Continuous Ψq := continuous_iff_le_induced.2 (le_of_eq sbq_top)

lemma weighted_mem {I : Set ℝ} (hne : I.Nonempty) (ϕ : ExpDecaySchwartzRpos I) {a : ℝ}
    (ha : a ∈ I) :
    (fun x : Gq => ((rposModule x.out ^ a : ℝ) : ℂ) * ϕ.toFun x.out) ∈
      schwartzBruhatSubmodule Gq := by
  rw [sb_mem_iff qbot]
  obtain ⟨g, hg⟩ := (expDecay_mem_iff I hne ϕ.1).1 ϕ.2 a ha
  refine ⟨g, fun t => ?_⟩
  rw [hg, qbot_symm, out_mk, rpos_pow]
  rfl

lemma Ψq_weighted {I : Set ℝ} (hne : I.Nonempty) (ϕ : ExpDecaySchwartzRpos I) {a : ℝ}
    (ha : a ∈ I) (t : ℝ) :
    Ψq (ExpDecaySchwartz.weighted ⊥ a ϕ) t =
      (Real.exp (a * t) : ℂ) * ϕ.toFun (Multiplicative.ofAdd t) := by
  have hwt : ExpDecaySchwartz.weighted ⊥ a ϕ = (⟨fun x : Gq =>
      ((rposModule x.out ^ a : ℝ) : ℂ) * ϕ.toFun x.out, weighted_mem hne ϕ ha⟩ :
        ↥(schwartzBruhatSubmodule Gq)) := by
    unfold ExpDecaySchwartz.weighted
    exact dif_pos (weighted_mem hne ϕ ha)
  rw [Ψq_apply, hwt]
  show ((rposModule (qbot.symm (Multiplicative.ofAdd t)).out ^ a : ℝ) : ℂ) *
    ϕ.toFun (qbot.symm (Multiplicative.ofAdd t)).out = _
  rw [qbot_symm, out_mk, rpos_pow]

lemma ed_topology (I : Set ℝ) (hne : I.Nonempty)
    (w : ℝ → ExpDecaySchwartzRpos I → SchwartzMap ℝ ℂ)
    (hw : ∀ a ∈ I, ∀ (ϕ : ExpDecaySchwartzRpos I) (x : ℝ),
      w a ϕ x = (Real.exp (a * x) : ℂ) * ϕ.toFun (Multiplicative.ofAdd x)) :
    (inferInstance : TopologicalSpace (ExpDecaySchwartzRpos I)) =
      ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (w a) inferInstance := by
  have hwq : ∀ a (ha : a ∈ I) ϕ, w a ϕ = Ψq (ExpDecaySchwartz.weighted ⊥ a ϕ) :=
    fun a ha ϕ => SchwartzMap.ext fun t => by rw [hw a ha, Ψq_weighted hne ϕ ha]
  let wl : ∀ a, a ∈ I → ExpDecaySchwartzRpos I →ₗ[ℂ] SchwartzMap ℝ ℂ := fun a ha =>
    { toFun := w a
      map_add' := fun ϕ χ => SchwartzMap.ext fun x => by
        rw [SchwartzMap.add_apply, hw a ha, hw a ha, hw a ha]
        change _ * (ϕ.toFun _ + χ.toFun _) = _
        ring
      map_smul' := fun c ϕ => SchwartzMap.ext fun x => by
        rw [SchwartzMap.smul_apply, hw a ha, hw a ha]
        change _ * (c * ϕ.toFun _) = _
        simp only [RingHom.id_apply, smul_eq_mul]
        ring }
  set τ' := ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (w a) inferInstance with hτ'
  have hLC : IsLocallyConvexTopology (ExpDecaySchwartzRpos I) τ' := by
    obtain ⟨a0, ha0⟩ := hne
    have heq : τ' = ⨅ a : {a // a ∈ I}, TopologicalSpace.induced (wl a.1 a.2) inferInstance :=
      iInf_subtype'
    refine ⟨(Σ _ : {a // a ∈ I}, ℕ × ℕ), ⟨⟨⟨a0, ha0⟩, (0, 0)⟩⟩,
      SeminormFamily.sigma (fun a : {a // a ∈ I} =>
        (schwartzSeminormFamily ℂ ℝ ℂ).comp (wl a.1 a.2)), ?_⟩
    rw [heq]
    exact withSeminorms_iInf fun a =>
      (wl a.1 a.2).withSeminorms_induced (schwartz_withSeminorms ℂ ℝ ℂ)
  apply le_antisymm
  · refine sInf_le ⟨hLC, fun k hk => ?_⟩
    have hk' := good_eq_bot (ContinuousMulEquiv.refl _) hk
    subst hk'
    refine continuous_iInf_rng.2 fun a => continuous_iInf_rng.2 fun ha =>
      continuous_induced_rng.2 ?_
    have : (w a ∘ Subtype.val) = Ψq ∘ (fun ϕ : {ϕ : ExpDecaySchwartzRpos I // ∀ h ∈
        (⊥ : Subgroup (Multiplicative ℝ)), ∀ g : Multiplicative ℝ,
          ϕ.toFun (g * h) = ϕ.toFun g} => ExpDecaySchwartz.weighted ⊥ a ϕ.1) :=
      funext fun ϕ => hwq a ha ϕ.1
    rw [this]
    exact @Continuous.comp _ _ _ (⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced
      (fun ϕ : {ϕ : ExpDecaySchwartzRpos I // ∀ h ∈ (⊥ : Subgroup (Multiplicative ℝ)),
        ∀ g : Multiplicative ℝ, ϕ.toFun (g * h) = ϕ.toFun g} =>
        ExpDecaySchwartz.weighted ⊥ a ϕ.1) inferInstance) _ _ _ _ Ψq_cont
      (continuous_iInf_dom (i := a) (continuous_iInf_dom (i := ha) continuous_induced_dom))
  · refine le_sInf fun t ht => ?_
    have hc := ht.2 ⊥ (bot_good (ContinuousMulEquiv.refl _))
    let σ : ExpDecaySchwartzRpos I → {ϕ : ExpDecaySchwartzRpos I // ∀ h ∈
        (⊥ : Subgroup (Multiplicative ℝ)), ∀ g : Multiplicative ℝ,
          ϕ.toFun (g * h) = ϕ.toFun g} :=
      fun ϕ => ⟨ϕ, fun h hh g => by rw [Subgroup.mem_bot.1 hh, mul_one]⟩
    have hσ : @Continuous _ _ τ' (⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced
        (fun ϕ : {ϕ : ExpDecaySchwartzRpos I // ∀ h ∈ (⊥ : Subgroup (Multiplicative ℝ)),
          ∀ g : Multiplicative ℝ, ϕ.toFun (g * h) = ϕ.toFun g} =>
          ExpDecaySchwartz.weighted ⊥ a ϕ.1) inferInstance) σ := by
      refine continuous_iInf_rng.2 fun a => continuous_iInf_rng.2 fun ha =>
        continuous_induced_rng.2 ?_
      have hwc : @Continuous _ _ τ' _ (w a) :=
        continuous_iInf_dom (i := a) (continuous_iInf_dom (i := ha) continuous_induced_dom)
      have key : τ' ≤ TopologicalSpace.induced
          (Ψq ∘ fun ϕ : ExpDecaySchwartzRpos I => ExpDecaySchwartz.weighted ⊥ a ϕ)
          inferInstance := by
        have : (Ψq ∘ fun ϕ : ExpDecaySchwartzRpos I => ExpDecaySchwartz.weighted ⊥ a ϕ) =
            w a := funext fun ϕ => (hwq a ha ϕ).symm
        rw [this]
        exact continuous_iff_le_induced.1 hwc
      rw [← induced_compose, ← sbq_top] at key
      exact continuous_iff_le_induced.2 key
    rw [← continuous_id_iff_le]
    exact @Continuous.comp _ _ _ τ' (⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced
        (fun ϕ : {ϕ : ExpDecaySchwartzRpos I // ∀ h ∈ (⊥ : Subgroup (Multiplicative ℝ)),
          ∀ g : Multiplicative ℝ, ϕ.toFun (g * h) = ϕ.toFun g} =>
          ExpDecaySchwartz.weighted ⊥ a ϕ.1) inferInstance) t _ _ hc hσ

end AAux

theorem solution (I : Set ℝ) (hne : I.Nonempty) :
    (∀ f : Multiplicative ℝ → ℂ, f ∈ MasulloGRH.expDecaySubmodule (Multiplicative ℝ)
        MasulloGRH.rposModule I ↔
      ∀ a ∈ I, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ,
        g x = (Real.exp (a * x) : ℂ) * f (Multiplicative.ofAdd x)) ∧
    ∀ w : ℝ → MasulloGRH.ExpDecaySchwartzRpos I → SchwartzMap ℝ ℂ,
      (∀ a ∈ I, ∀ (ϕ : MasulloGRH.ExpDecaySchwartzRpos I) (x : ℝ),
        w a ϕ x = (Real.exp (a * x) : ℂ) * ϕ.toFun (Multiplicative.ofAdd x)) →
      (inferInstance : TopologicalSpace (MasulloGRH.ExpDecaySchwartzRpos I)) =
        ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced (w a) inferInstance :=
  ⟨fun f => AAux.expDecay_mem_iff I hne f, fun w hw => AAux.ed_topology I hne w hw⟩
