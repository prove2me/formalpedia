-- Prove2me | solution 1 for MoreauProx.Characterization.prox_map_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T09:14:45.662497+00:00
-- url     : https://prove2.me/submissions/79faa5dc-8aec-4284-9bee-0de5b6c52295

import Mathlib
import Definitions.Def_MoreauProx_Characterization_Prox

set_option autoImplicit false

/-- If `0 ≤ K + t * M` for all `t ∈ (0, 1]` with `M ≥ 0`, then `0 ≤ K`. -/
theorem mpc_nonneg_of_forall {K M : ℝ} (hM : 0 ≤ M)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ K + t * M) : 0 ≤ K := by
  by_contra hK'
  have hK : K < 0 := not_le.mp hK'
  set s : ℝ := -K / (2 * (M + 1)) with hs
  have hM1 : 0 < 2 * (M + 1) := by linarith
  have hs0 : 0 < s := div_pos (neg_pos.mpr hK) hM1
  have hsM : s * (2 * (M + 1)) = -K := by
    rw [hs]; field_simp
  set t : ℝ := min 1 s with ht
  have ht0 : 0 < t := lt_min one_pos hs0
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ s := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : t * M ≤ s * M := mul_le_mul_of_nonneg_right ht2 hM
  nlinarith

open MoreauProx.Characterization in open scoped InnerProductSpace in
/-- A proximal point of a `Γ₀` function has a finite value. -/
theorem mpc_prox_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → EReal) (hg : GammaZero g) (z x : H) (hp : IsProx g z x) :
    ∃ a : ℝ, g x = (a : EReal) := by
  obtain ⟨x0, hx0⟩ := hg.2.1
  have h := hp x0
  have hne : g x ≠ ⊤ := by
    intro htop
    rw [htop, EReal.coe_add_top] at h
    have hc := (EReal.coe_toReal hx0 (hg.1 x0)).symm
    rw [hc, ← EReal.coe_add, top_le_iff] at h
    exact EReal.coe_ne_top _ h
  exact ⟨(g x).toReal, (EReal.coe_toReal hne (hg.1 x)).symm⟩

open MoreauProx.Characterization in open scoped InnerProductSpace in
/-- Variational inequality from minimality of the proximal objective and convexity. -/
theorem mpc_varineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → EReal) (hg : GammaZero g) (z x : H) (a : ℝ) (hgx : g x = (a : EReal))
    (hp : IsProx g z x) (u : H) (c : ℝ) (hgu : g u = (c : EReal)) :
    ⟪u - x, z - x⟫_ℝ ≤ c - a := by
  have hconvx : Convex ℝ {q : H × ℝ | g q.1 ≤ ((q.2 : ℝ) : EReal)} := hg.2.2.1
  have key : 0 ≤ (c - a - ⟪u - x, z - x⟫_ℝ) := by
    refine mpc_nonneg_of_forall (M := ‖u - x‖ ^ 2 / 2) (by positivity) ?_
    intro t ht0 ht1
    have hxe : (x, a) ∈ {q : H × ℝ | g q.1 ≤ ((q.2 : ℝ) : EReal)} := by
      simp only [Set.mem_ofPred_eq, hgx, le_refl]
    have hue : (u, c) ∈ {q : H × ℝ | g q.1 ≤ ((q.2 : ℝ) : EReal)} := by
      simp only [Set.mem_ofPred_eq, hgu, le_refl]
    have hconv := hconvx hxe hue (a := 1 - t) (b := t) (by linarith) ht0.le (by ring)
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hconv
    have hpr := hp ((1 - t) • x + t • u)
    rw [hgx] at hpr
    have h2 := hpr.trans (add_le_add le_rfl hconv)
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    have heq : (1 - t) • x + t • u - z = t • (u - x) - (z - x) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [heq, norm_sub_rev x z, norm_sub_sq_real (t • (u - x)) (z - x), norm_smul,
      real_inner_smul_left] at h2
    have hn : (‖t‖ * ‖u - x‖) ^ 2 = t ^ 2 * ‖u - x‖ ^ 2 := by
      rw [mul_pow, Real.norm_eq_abs, sq_abs]
    rw [hn] at h2
    by_contra hneg'
    have hneg := not_le.mp hneg'
    have : t * (c - a - ⟪u - x, z - x⟫_ℝ + t * (‖u - x‖ ^ 2 / 2)) < 0 :=
      mul_neg_of_pos_of_neg ht0 hneg
    nlinarith
  linarith

open MoreauProx.Characterization in open scoped InnerProductSpace in
/-- A prox map of a `Γ₀` function contracts distances. -/
theorem mpc_nonexp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (g : H → EReal) (hg : GammaZero g) (hp : ∀ z, IsProx g z (p z)) (z z' : H) :
    ‖p z - p z'‖ ≤ ‖z - z'‖ := by
  obtain ⟨a, ha⟩ := mpc_prox_finite g hg z (p z) (hp z)
  obtain ⟨a', ha'⟩ := mpc_prox_finite g hg z' (p z') (hp z')
  have h1 := mpc_varineq g hg z (p z) a ha (hp z) (p z') a' ha'
  have h2 := mpc_varineq g hg z' (p z') a' ha' (hp z') (p z) a ha
  have hsq : ‖p z - p z'‖ ^ 2 ≤ ⟪p z - p z', z - z'⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
    have c1 := real_inner_comm (p z) (p z')
    have c2 := real_inner_comm (p z) z'
    have c3 := real_inner_comm (p z') z
    have c4 := real_inner_comm (p z) z
    have c5 := real_inner_comm (p z') z'
    linarith
  have hcs := real_inner_le_norm (p z - p z') (z - z')
  by_contra hc
  have hc' := not_le.mp hc
  nlinarith [norm_nonneg (z - z'), norm_nonneg (p z - p z')]

open scoped InnerProductSpace in
/-- A real function with a subgradient selection everywhere is convex. -/
theorem mpc_convex_of_subgrad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (φ : H → ℝ) (p : H → H) (hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u) :
    ConvexOn ℝ Set.univ φ := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h1 := hs (a • x + b • y) x
  have h2 := hs (a • x + b • y) y
  have hv : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
    have e : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y))
        = (a • x + b • y) - (a + b) • (a • x + b • y) := by
      rw [smul_sub, smul_sub, add_smul]; abel
    rw [e, hab, one_smul, sub_self]
  have e : a * ⟪x - (a • x + b • y), p (a • x + b • y)⟫_ℝ
      + b * ⟪y - (a • x + b • y), p (a • x + b • y)⟫_ℝ = 0 := by
    rw [← real_inner_smul_left, ← real_inner_smul_left, ← inner_add_left, hv, inner_zero_left]
  simp only [smul_eq_mul]
  have hm : (a + b) * φ (a • x + b • y) = φ (a • x + b • y) := by rw [hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

open MoreauProx.Characterization in open scoped InnerProductSpace in
/-- Forward direction, subgradient half: a prox map selects subgradients of a convex function. -/
theorem mpc_forward_subgrad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (g : H → EReal) (hg : GammaZero g) (hp : ∀ z, IsProx g z (p z)) :
    ∃ φ : H → ℝ, ConvexOn ℝ Set.univ φ ∧
      ∀ z : H, p z ∈ subgrad (fun u => ((φ u : ℝ) : EReal)) z := by
  have hγ : ∀ z, g (p z) = (((g (p z)).toReal : ℝ) : EReal) := by
    intro z
    obtain ⟨a, ha⟩ := mpc_prox_finite g hg z (p z) (hp z)
    rw [ha, EReal.toReal_coe]
  let φ : H → ℝ := fun z => ⟪p z, z⟫_ℝ - ‖p z‖ ^ 2 / 2 - (g (p z)).toReal
  have hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u := by
    intro z u
    have h := hp u (p z)
    rw [hγ u, hγ z, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [norm_sub_sq_real, norm_sub_sq_real] at h
    simp only [φ, inner_sub_left]
    have c1 := real_inner_comm (p z) u
    have c2 := real_inner_comm (p z) z
    have c3 := real_inner_comm (p u) u
    linarith
  refine ⟨φ, mpc_convex_of_subgrad φ p hs, fun z => ?_⟩
  refine ⟨EReal.coe_ne_bot _, EReal.coe_ne_top _, fun u => ?_⟩
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  exact hs z u

open scoped InnerProductSpace in
/-- Descent lemma: a convex function whose subgradient selection is nonexpansive
is majorized by its tangent plus `½‖w - z‖²`. -/
theorem mpc_descent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (φ : H → ℝ) (hL : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖)
    (hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u) (z w : H) :
    φ w - φ z - ⟪w - z, p z⟫_ℝ ≤ ‖w - z‖ ^ 2 / 2 := by
  have step : ∀ n : ℕ, ∀ z w : H,
      φ w - φ z - ⟪w - z, p z⟫_ℝ ≤ (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * ‖w - z‖ ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro z w
      have h1 := hs w z
      have h2 : ⟪z - w, p w⟫_ℝ = -⟪w - z, p w⟫_ℝ := by rw [← inner_neg_left, neg_sub]
      have h3 : ⟪w - z, p w - p z⟫_ℝ = ⟪w - z, p w⟫_ℝ - ⟪w - z, p z⟫_ℝ :=
        inner_sub_right _ _ _
      have h4 := real_inner_le_norm (w - z) (p w - p z)
      have h5 := hL w z
      have h6 := norm_nonneg (w - z)
      have h7 : ‖w - z‖ * ‖p w - p z‖ ≤ ‖w - z‖ * ‖w - z‖ := mul_le_mul_of_nonneg_left h5 h6
      have h8 : (1 / 2 + (1 / 2 : ℝ) ^ (0 + 1)) * ‖w - z‖ ^ 2 = ‖w - z‖ * ‖w - z‖ := by ring
      rw [h8]
      linarith
    | succ n ih =>
      intro z w
      have hmz : (z + (1 / 2 : ℝ) • (w - z)) - z = (1 / 2 : ℝ) • (w - z) := by abel
      have hwm : w - (z + (1 / 2 : ℝ) • (w - z)) = (1 / 2 : ℝ) • (w - z) := by
        have : w - (z + (1 / 2 : ℝ) • (w - z)) = (w - z) - (1 / 2 : ℝ) • (w - z) := by abel
        rw [this]
        nth_rewrite 1 [← one_smul ℝ (w - z)]
        rw [← sub_smul]
        norm_num
      have nhalf : ‖(1 / 2 : ℝ) • (w - z)‖ = ‖w - z‖ / 2 := by
        rw [norm_smul]; norm_num; ring
      have h1 := ih z (z + (1 / 2 : ℝ) • (w - z))
      have h2 := ih (z + (1 / 2 : ℝ) • (w - z)) w
      rw [hmz, nhalf] at h1
      rw [hwm, nhalf] at h2
      have hsplit : ⟪w - z, p z⟫_ℝ = ⟪(1 / 2 : ℝ) • (w - z), p z⟫_ℝ
          + ⟪(1 / 2 : ℝ) • (w - z), p z⟫_ℝ := by
        rw [← inner_add_left, ← add_smul]; norm_num
      have hcross : ⟪(1 / 2 : ℝ) • (w - z), p (z + (1 / 2 : ℝ) • (w - z)) - p z⟫_ℝ
          ≤ ‖w - z‖ ^ 2 / 4 := by
        have ha := real_inner_le_norm ((1 / 2 : ℝ) • (w - z))
          (p (z + (1 / 2 : ℝ) • (w - z)) - p z)
        have hb := hL (z + (1 / 2 : ℝ) • (w - z)) z
        rw [hmz, nhalf] at hb
        rw [nhalf] at ha
        have hc := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ ‖w - z‖ / 2)
        nlinarith
      rw [inner_sub_right] at hcross
      have hpow : (1 / 2 : ℝ) ^ (n + 1 + 1) = (1 / 2 : ℝ) ^ (n + 1) / 2 := by
        rw [pow_succ]; ring
      rw [hpow]
      have hid : (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * (‖w - z‖ / 2) ^ 2
          + (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * (‖w - z‖ / 2) ^ 2 + ‖w - z‖ ^ 2 / 4
          = (1 / 2 + (1 / 2 : ℝ) ^ (n + 1) / 2) * ‖w - z‖ ^ 2 := by ring
      rw [hsplit]
      linarith
  have ht : Filter.Tendsto (fun n : ℕ => (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * ‖w - z‖ ^ 2)
      Filter.atTop (nhds ((1 / 2 + 0) * ‖w - z‖ ^ 2)) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (Filter.tendsto_add_atTop_nat 1)
    exact (h0.const_add (1 / 2)).mul_const _
  have hlim := ge_of_tendsto' ht (fun n => step n z w)
  linarith

open scoped InnerProductSpace in
/-- Baillon–Haddad type co-coercivity inequality. -/
theorem mpc_cocoercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (φ : H → ℝ) (hL : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖)
    (hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u) (z w : H) :
    φ z + ⟪w - z, p z⟫_ℝ + ‖p w - p z‖ ^ 2 / 2 ≤ φ w := by
  have h1 := hs z (w - (p w - p z))
  have h2 := mpc_descent p φ hL hs w (w - (p w - p z))
  have e1 : w - (p w - p z) - z = (w - z) - (p w - p z) := by abel
  have e2 : w - (p w - p z) - w = -(p w - p z) := by abel
  rw [e1, inner_sub_left] at h1
  rw [e2, inner_neg_left, norm_neg] at h2
  have e3 : ‖p w - p z‖ ^ 2 = ⟪p w - p z, p w⟫_ℝ - ⟪p w - p z, p z⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_right]
  linarith

open MoreauProx.Characterization in open scoped InnerProductSpace in
/-- Converse direction: a nonexpansive subgradient selection of a convex function is a prox map. -/
theorem mpc_converse {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (φ : H → ℝ) (hL : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖)
    (hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u) : IsProxMap p := by
  let G : H → ℝ := fun z => ⟪p z, z⟫_ℝ - φ z - ‖p z‖ ^ 2 / 2
  let A : H → H → ℝ := fun z x => G z + ⟪x - p z, z - p z⟫_ℝ
  have hkey : ∀ z w, A z (p w) ≤ G w := by
    intro z w
    have h := mpc_cocoercive p φ hL hs w z
    rw [norm_sub_sq_real] at h
    simp only [A, G]
    simp only [inner_sub_left, inner_sub_right] at h ⊢
    have c1 := real_inner_comm (p w) z
    have c2 := real_inner_comm (p w) (p z)
    have c3 := real_inner_comm (p w) w
    have c4 := real_inner_self_eq_norm_sq (p z)
    have c5 := real_inner_comm (p z) z
    linarith
  have hAself : ∀ w, A w (p w) = G w := by
    intro w; simp only [A, sub_self, inner_zero_left, add_zero]
  let g : H → EReal := fun x => ⨆ z, ((A z x : ℝ) : EReal)
  have hgA : ∀ z x, ((A z x : ℝ) : EReal) ≤ g x := fun z x =>
    le_iSup (fun z => ((A z x : ℝ) : EReal)) z
  have hgp : ∀ w, g (p w) = ((G w : ℝ) : EReal) := by
    intro w
    apply le_antisymm
    · exact iSup_le fun z => EReal.coe_le_coe_iff.mpr (hkey z w)
    · have := hgA w (p w)
      rw [hAself w] at this
      exact this
  refine ⟨g, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    have := hgA 0 x
    rw [hx, le_bot_iff] at this
    exact EReal.coe_ne_bot _ this
  · exact ⟨p 0, by rw [hgp 0]; exact EReal.coe_ne_top _⟩
  · show Convex ℝ {q : H × ℝ | g q.1 ≤ ((q.2 : ℝ) : EReal)}
    intro q1 hq1 q2 hq2 a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hq1 hq2 ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    refine iSup_le fun z => ?_
    have h1 := (hgA z q1.1).trans hq1
    have h2 := (hgA z q2.1).trans hq2
    rw [EReal.coe_le_coe_iff] at h1 h2 ⊢
    have hlin : A z (a • q1.1 + b • q2.1) = a * A z q1.1 + b * A z q2.1 := by
      simp only [A]
      have hv : a • q1.1 + b • q2.1 - p z = a • (q1.1 - p z) + b • (q2.1 - p z) := by
        have e : a • (q1.1 - p z) + b • (q2.1 - p z)
            = a • q1.1 + b • q2.1 - (a + b) • p z := by
          rw [smul_sub, smul_sub, add_smul]; abel
        rw [e, hab, one_smul]
      rw [hv, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      linear_combination (-G z) * hab
    rw [hlin]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  · apply lowerSemicontinuous_iSup
    intro z
    apply Continuous.lowerSemicontinuous
    exact continuous_coe_real_ereal.comp (by fun_prop)
  · intro w u
    rw [hgp w]
    refine le_trans ?_ (add_le_add le_rfl (hgA w u))
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    simp only [A]
    have e : u - w = (u - p w) - (w - p w) := by abel
    rw [e, norm_sub_rev (p w) w, norm_sub_sq_real (u - p w) (w - p w)]
    nlinarith [sq_nonneg ‖u - p w‖]

open MoreauProx.Characterization in open scoped InnerProductSpace in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (p : H → H) :
    IsProxMap p ↔
      (ContractsDistances (fun z => ({p z} : Set H)) ∧
        ∃ φ : H → ℝ, ConvexOn ℝ Set.univ φ ∧
          ∀ z : H, p z ∈ subgrad (fun u => ((φ u : ℝ) : EReal)) z) := by
  constructor
  · rintro ⟨g, hg, hp⟩
    refine ⟨?_, mpc_forward_subgrad p g hg hp⟩
    intro z z' x x' hx hx'
    rw [Set.mem_singleton_iff] at hx hx'
    subst hx hx'
    exact mpc_nonexp p g hg hp z z'
  · rintro ⟨hC, φ, -, hφ⟩
    have hL : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖ := fun z w =>
      hC z w (p z) (p w) (Set.mem_singleton _) (Set.mem_singleton _)
    have hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u := by
      intro z u
      obtain ⟨-, -, h3⟩ := hφ z
      have := h3 u
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at this
      exact this
    exact mpc_converse p φ hL hs
