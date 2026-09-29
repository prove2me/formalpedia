-- Prove2me | solution 1 for MoreauProx.Characterization.prox_nonexpansive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:54:34.307729+00:00
-- url     : https://prove2.me/submissions/a9bc8098-d44b-4ff3-b88e-82d958abd4be

import Mathlib
import Definitions.Def_MoreauProx_Characterization_Prox

open scoped InnerProductSpace
open MoreauProx.Characterization

/-- Moreau 1965, Proposition 3.a: for `f ∈ Γ₀(H)` the proximal objective
`Φ(u) = ½‖u − z‖² + f(u)` attains a strict minimum. -/
private theorem prox_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (htop : ∃ x, f x ≠ ⊤)
    (hconv : Convex ℝ {p : H × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)})
    (hlsc : LowerSemicontinuous f) (z : H) :
    ∃ x : H, ∀ u : H, u ≠ x →
      ((‖x - z‖ ^ 2 / 2 : ℝ) : EReal) + f x < ((‖u - z‖ ^ 2 / 2 : ℝ) : EReal) + f u := by
  classical
  set E : Set (H × ℝ) := {p : H × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} with hE
  set A : Set H := {u : H | f u ≠ ⊤} with hA
  set g : H → ℝ := fun u => (f u).toReal with hg
  have hgf : ∀ u ∈ A, ((g u : ℝ) : EReal) = f u := by
    intro u hu
    simp only [hA, Set.mem_setOf_eq] at hu
    simp only [hg]
    exact EReal.coe_toReal hu (hbot u)
  have hmemE : ∀ (u : H) (r : ℝ), ((u, r) ∈ E) ↔ (u ∈ A ∧ g u ≤ r) := by
    intro u r
    constructor
    · intro h
      simp only [hE, Set.mem_setOf_eq] at h
      have hne : u ∈ A := by
        simp only [hA, Set.mem_setOf_eq]
        intro htopu
        rw [htopu] at h
        exact absurd h (by simp)
      refine ⟨hne, ?_⟩
      rw [← hgf u hne] at h
      exact EReal.coe_le_coe_iff.mp h
    · rintro ⟨hu, hle⟩
      simp only [hE, Set.mem_setOf_eq]
      rw [← hgf u hu]
      exact EReal.coe_le_coe_iff.mpr hle
  -- convexity of `g` on its domain
  have hconvA : ∀ a ∈ A, ∀ b ∈ A, ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 →
      (s • a + t • b) ∈ A ∧ g (s • a + t • b) ≤ s * g a + t * g b := by
    intro a ha b hb s t hs ht hst
    have h1 : ((a, g a) : H × ℝ) ∈ E := (hmemE a (g a)).mpr ⟨ha, le_refl _⟩
    have h2 : ((b, g b) : H × ℝ) ∈ E := (hmemE b (g b)).mpr ⟨hb, le_refl _⟩
    have h3 := hconv h1 h2 hs ht hst
    have h4 : s • ((a, g a) : H × ℝ) + t • ((b, g b) : H × ℝ)
        = (s • a + t • b, s * g a + t * g b) := by
      simp [Prod.ext_iff]
    rw [h4] at h3
    exact (hmemE _ _).mp h3
  obtain ⟨x₀, hx₀'⟩ := htop
  have hx₀ : x₀ ∈ A := hx₀'
  -- the epigraph is closed
  have hEclosed : IsClosed E := by
    have hc : IsClosed {p : H × EReal | f p.1 ≤ p.2} := hlsc.isClosed_epigraph
    have hmap : Continuous (fun p : H × ℝ => (p.1, ((p.2 : ℝ) : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact hc.preimage hmap
  -- separate a point below the graph from the epigraph
  have hp₀ : ((x₀, g x₀ - 1) : H × ℝ) ∉ E := by
    intro h
    have := ((hmemE x₀ (g x₀ - 1)).mp h).2
    linarith
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Disjoint (Metric.ball ((x₀, g x₀ - 1) : H × ℝ) ε) E := by
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hEclosed.isOpen_compl _ hp₀
    exact ⟨ε, hε, Set.disjoint_left.mpr fun p hp => hsub hp⟩
  obtain ⟨L, s₀, hL1, hL2⟩ :=
    geometric_hahn_banach_open (convex_ball _ _) Metric.isOpen_ball hconv hball
  set lam : ℝ := L (0, 1) with hlamdef
  set φ : H → ℝ := fun u => L (u, 0) with hφ
  have hLdec : ∀ (u : H) (r : ℝ), L (u, r) = φ u + r * lam := by
    intro u r
    have h : ((u, r) : H × ℝ) = (u, 0) + r • ((0, 1) : H × ℝ) := by simp
    rw [h, map_add, map_smul]
    simp [hφ, hlamdef]
  have hcenter : L ((x₀, g x₀ - 1) : H × ℝ) < s₀ := hL1 _ (Metric.mem_ball_self hε)
  have hx₀E : ((x₀, g x₀) : H × ℝ) ∈ E := (hmemE x₀ (g x₀)).mpr ⟨hx₀, le_refl _⟩
  have hlampos : 0 < lam := by
    have h1 := hL2 _ hx₀E
    rw [hLdec] at hcenter h1
    nlinarith [hcenter, h1]
  have hminor : ∀ u ∈ A, s₀ ≤ φ u + g u * lam := by
    intro u hu
    have h := hL2 _ ((hmemE u (g u)).mpr ⟨hu, le_refl _⟩)
    rwa [hLdec] at h
  -- the objective
  set ψ : H → ℝ := fun u => ‖u - z‖ ^ 2 / 2 + g u with hψ
  set K : ℝ := ‖L‖ with hK
  have hKnn : 0 ≤ K := norm_nonneg L
  have hφbd : ∀ u : H, φ u ≤ K * ‖u‖ := by
    intro u
    have h := L.le_opNorm ((u, 0) : H × ℝ)
    have h2 : ‖((u, 0) : H × ℝ)‖ = ‖u‖ := by simp [Prod.norm_def]
    rw [h2] at h
    have h3 : φ u ≤ ‖L (u, 0)‖ := by
      simp only [hφ, Real.norm_eq_abs]
      exact le_abs_self _
    simp only [hφ, hK]
    linarith [h, h3]
  have hlb : ∀ u ∈ A, (s₀ - K * ‖z‖ - K ^ 2 / (2 * lam)) / lam ≤ ψ u := by
    intro u hu
    rw [div_le_iff₀ hlampos]
    have h1 := hminor u hu
    have h2 := hφbd u
    have h3 : ‖u‖ ≤ ‖u - z‖ + ‖z‖ := by
      have := norm_add_le (u - z) z
      simpa using this
    have h4 : φ u ≤ K * (‖u - z‖ + ‖z‖) := le_trans h2 (mul_le_mul_of_nonneg_left h3 hKnn)
    have hid : K ^ 2 / (2 * lam) - K * ‖u - z‖ + (‖u - z‖ ^ 2 / 2) * lam
        = (‖u - z‖ * lam - K) ^ 2 / (2 * lam) := by
      field_simp
      ring
    have hid2 : (0:ℝ) ≤ (‖u - z‖ * lam - K) ^ 2 / (2 * lam) := by positivity
    have hgl : s₀ - K * (‖u - z‖ + ‖z‖) ≤ g u * lam := by linarith
    have hexp : ψ u * lam = (‖u - z‖ ^ 2 / 2) * lam + g u * lam := by
      simp only [hψ]; ring
    rw [hexp]
    linarith
  -- the infimum
  set W : Set ℝ := ψ '' A with hW
  have hWne : W.Nonempty := ⟨ψ x₀, ⟨x₀, hx₀, rfl⟩⟩
  have hWbdd : BddBelow W := by
    refine ⟨(s₀ - K * ‖z‖ - K ^ 2 / (2 * lam)) / lam, ?_⟩
    rintro y ⟨u, hu, rfl⟩
    exact hlb u hu
  set m : ℝ := sInf W with hm
  have hmle : ∀ u ∈ A, m ≤ ψ u := fun u hu => csInf_le hWbdd ⟨u, hu, rfl⟩
  have hmapprox : ∀ ε' : ℝ, 0 < ε' → ∃ u ∈ A, ψ u < m + ε' := by
    intro ε' hε'
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_csInf_lt hWne (by linarith : sInf W < m + ε')
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨u, hu, hylt⟩
  -- strong convexity at midpoints
  have hmid : ∀ a ∈ A, ∀ b ∈ A, (((1:ℝ)/2) • a + ((1:ℝ)/2) • b ∈ A ∧
      ψ (((1:ℝ)/2) • a + ((1:ℝ)/2) • b) ≤ (ψ a + ψ b) / 2 - ‖a - b‖ ^ 2 / 8) := by
    intro a ha b hb
    obtain ⟨hmemA, hgle⟩ :=
      hconvA a ha b hb (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨hmemA, ?_⟩
    have hnorm : ‖((1:ℝ)/2) • a + ((1:ℝ)/2) • b - z‖ ^ 2 / 2
        = (‖a - z‖ ^ 2 / 2 + ‖b - z‖ ^ 2 / 2) / 2 - ‖a - b‖ ^ 2 / 8 := by
      have hpar := parallelogram_law_with_norm ℝ (a - z) (b - z)
      have h1 : ((1:ℝ)/2) • a + ((1:ℝ)/2) • b - z = ((1:ℝ)/2) • ((a - z) + (b - z)) := by
        rw [smul_add]; module
      have h2 : (a - z) - (b - z) = a - b := by abel
      rw [h1, norm_smul]
      rw [h2] at hpar
      simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
      nlinarith [hpar]
    simp only [hψ]
    rw [hnorm]
    linarith
  have hsep : ∀ a ∈ A, ∀ b ∈ A, ‖a - b‖ ^ 2 ≤ 8 * ((ψ a + ψ b) / 2 - m) := by
    intro a ha b hb
    obtain ⟨hmA, hle⟩ := hmid a ha b hb
    have := hmle _ hmA
    linarith
  -- a minimising sequence
  have hseq : ∀ k : ℕ, ∃ u ∈ A, ψ u < m + 1 / ((k : ℝ) + 1) := by
    intro k
    exact hmapprox _ (by positivity)
  choose u huA hulr using hseq
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε' hε'
    obtain ⟨N, hN⟩ := exists_nat_gt (8 / ε' ^ 2)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hulr n
    have h2 := hulr N
    have h3 := hsep (u n) (huA n) (u N) (huA N)
    have hmn := hmle _ (huA n)
    have hmN := hmle _ (huA N)
    have hNR : (0:ℝ) < (N : ℝ) + 1 := by positivity
    have hnR : ((N : ℝ) + 1) ≤ ((n : ℝ) + 1) := by
      have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      linarith
    have hinv : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hNR hnR
    have hlt : 8 / ((N : ℝ) + 1) < ε' ^ 2 := by
      rw [div_lt_iff₀ hNR]
      have : 8 / ε' ^ 2 < (N : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < ε' ^ 2)] at this
      linarith
    have hsq : ‖u n - u N‖ ^ 2 < ε' ^ 2 := by
      have hb : 8 * ((ψ (u n) + ψ (u N)) / 2 - m) ≤ 8 / ((N : ℝ) + 1) := by
        have hh : (ψ (u n) + ψ (u N)) / 2 - m
            < (1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1)) / 2 := by linarith
        have h5 : (1 / ((n : ℝ) + 1) + 1 / ((N : ℝ) + 1)) / 2 ≤ 1 / ((N : ℝ) + 1) := by
          linarith
        have h6 : (8:ℝ) / ((N : ℝ) + 1) = 8 * (1 / ((N : ℝ) + 1)) := by ring
        rw [h6]
        linarith
      linarith
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (u n - u N), hε', hsq]
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limit is a minimiser
  have hψtend : Filter.Tendsto (fun k => ψ (u k)) Filter.atTop (nhds m) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun k => hmle _ (huA k)) (fun k => (hulr k).le)
    have hone : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using tendsto_const_nhds.add hone
  have hcont : Continuous (fun y : H => ‖y - z‖ ^ 2 / 2) := by fun_prop
  have hnormtend :
      Filter.Tendsto (fun k => ‖u k - z‖ ^ 2 / 2) Filter.atTop (nhds (‖x - z‖ ^ 2 / 2)) :=
    (hcont.tendsto x).comp hx
  obtain ⟨c, hc⟩ : ∃ y : ℝ, y = m - ‖x - z‖ ^ 2 / 2 := ⟨_, rfl⟩
  have hgtend : Filter.Tendsto (fun k => g (u k)) Filter.atTop (nhds c) := by
    have h := hψtend.sub hnormtend
    simp only [hψ, hc] at h ⊢
    simpa using h
  have hfx : f x ≤ ((c : ℝ) : EReal) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨c', hcc', hc'lt⟩ : ∃ c' : ℝ, c < c' ∧ ((c' : ℝ) : EReal) < f x := by
      rcases eq_or_ne (f x) ⊤ with hT | hT
      · exact ⟨c + 1, by linarith, by rw [hT]; exact EReal.coe_lt_top _⟩
      · have hfb : (((f x).toReal : ℝ) : EReal) = f x := EReal.coe_toReal hT (hbot x)
        have hcb : c < (f x).toReal := by
          rw [← hfb] at hcon
          exact EReal.coe_lt_coe_iff.mp hcon
        refine ⟨(c + (f x).toReal) / 2, by linarith, ?_⟩
        have hlt2 : (((c + (f x).toReal) / 2 : ℝ) : EReal) < (((f x).toReal : ℝ) : EReal) :=
          EReal.coe_lt_coe_iff.mpr (by linarith)
        rwa [hfb] at hlt2
    have hev2 : ∀ᶠ k in Filter.atTop, ((c' : ℝ) : EReal) < f (u k) :=
      hx.eventually (hlsc x _ hc'lt)
    have hev3 : ∀ᶠ k in Filter.atTop, c' < g (u k) := by
      filter_upwards [hev2] with k hk
      rw [← hgf _ (huA k)] at hk
      exact EReal.coe_lt_coe_iff.mp hk
    have hev4 : ∀ᶠ k in Filter.atTop, g (u k) < c' := hgtend.eventually_lt_const hcc'
    obtain ⟨k, hk1, hk2⟩ := (hev3.and hev4).exists
    linarith
  have hxA : x ∈ A := by
    simp only [hA, Set.mem_setOf_eq]
    intro hT
    rw [hT] at hfx
    exact absurd hfx (by simp)
  have hgxle : g x ≤ c := by
    rw [← hgf x hxA] at hfx
    exact EReal.coe_le_coe_iff.mp hfx
  have hψx : ψ x = m := by
    have h1 : ψ x ≤ m := by
      simp only [hψ]
      simp only [hc] at hgxle
      linarith
    have h2 := hmle x hxA
    linarith
  -- strictness
  refine ⟨x, fun v hv => ?_⟩
  have hΦ : ∀ w ∈ A, ((‖w - z‖ ^ 2 / 2 : ℝ) : EReal) + f w = ((ψ w : ℝ) : EReal) := by
    intro w hw
    rw [← hgf w hw]
    simp only [hψ]
    rw [← EReal.coe_add]
  rw [hΦ x hxA]
  by_cases hvA : v ∈ A
  · rw [hΦ v hvA]
    refine EReal.coe_lt_coe_iff.mpr ?_
    rcases lt_or_eq_of_le (hmle v hvA) with h | h
    · rw [hψx]; exact h
    · exfalso
      obtain ⟨hmA, hle⟩ := hmid v hvA x hxA
      have hpos : 0 < ‖v - x‖ ^ 2 :=
        pow_pos (norm_pos_iff.mpr (sub_ne_zero_of_ne hv)) 2
      have := hmle _ hmA
      rw [hψx, ← h] at hle
      linarith
  · have hT : f v = ⊤ := by
      simp only [hA, Set.mem_setOf_eq, not_not] at hvA
      exact hvA
    rw [hT]
    rw [EReal.add_top_of_ne_bot (by simp)]
    exact EReal.coe_lt_top _

/-- `prox f z` really is a proximal point when `f ∈ Γ₀(H)`. -/
private theorem prox_spec {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (z : H) : IsProx f z (prox f z) := by
  have hex : ∃ x, IsProx f z x := by
    obtain ⟨x, hx⟩ := prox_core f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 z
    refine ⟨x, fun u => ?_⟩
    by_cases h : u = x
    · rw [h]
    · exact (hx u h).le
  have heq : prox f z = hex.choose := by
    unfold prox
    exact dif_pos hex
  rw [heq]
  exact hex.choose_spec

/-- At a proximal point the value of `f` is finite. -/
private theorem prox_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (z x : H) (hx : IsProx f z x) : f x ≠ ⊤ := by
  obtain ⟨x₀, hx₀⟩ := hf.2.1
  intro hxt
  have h := hx x₀
  rw [hxt, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)] at h
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f x₀ = (r : EReal) :=
    ⟨(f x₀).toReal, (EReal.coe_toReal hx₀ (hf.1 x₀)).symm⟩
  rw [hr, ← EReal.coe_add] at h
  exact EReal.coe_ne_top _ (top_le_iff.mp h)

/-- Convexity of `f` in segment form, at points where `f` is finite. -/
private theorem seg_convex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (a b : H) (ga gb : ℝ)
    (ha : f a = (ga : EReal)) (hb : f b = (gb : EReal)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1 - t) • a + t • b) ≤ (((1 - t) * ga + t * gb : ℝ) : EReal) := by
  have hma : (a, ga) ∈ {p : H × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
    simp only [Set.mem_setOf_eq, ha]
    exact le_refl _
  have hmb : (b, gb) ∈ {p : H × ℝ | f p.1 ≤ ((p.2 : ℝ) : EReal)} := by
    simp only [Set.mem_setOf_eq, hb]
    exact le_refl _
  have hmem := hf.2.2.1 hma hmb (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  have hsm : ((1 - t) • (a, ga) + t • (b, gb) : H × ℝ)
      = ((1 - t) • a + t • b, (1 - t) * ga + t * gb) := by
    simp [Prod.ext_iff]
  rw [hsm] at hmem
  exact hmem

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) :
    (∀ z z' : H, ‖prox f z - prox f z'‖ ≤ ‖z - z'‖) ∧ Continuous (prox f) := by
  have hne : ∀ z z' : H, ‖prox f z - prox f z'‖ ≤ ‖z - z'‖ := by
    intro z z'
    obtain ⟨x, hxdef⟩ : ∃ y : H, y = prox f z := ⟨_, rfl⟩
    obtain ⟨x', hx'def⟩ : ∃ y : H, y = prox f z' := ⟨_, rfl⟩
    have hx : IsProx f z x := by rw [hxdef]; exact prox_spec f hf z
    have hx' : IsProx f z' x' := by rw [hx'def]; exact prox_spec f hf z'
    obtain ⟨gx, hgx⟩ : ∃ r : ℝ, f x = (r : EReal) :=
      ⟨(f x).toReal, (EReal.coe_toReal (prox_finite f hf z x hx) (hf.1 x)).symm⟩
    obtain ⟨gx', hgx'⟩ : ∃ r : ℝ, f x' = (r : EReal) :=
      ⟨(f x').toReal, (EReal.coe_toReal (prox_finite f hf z' x' hx') (hf.1 x')).symm⟩
    rw [← hxdef, ← hx'def, norm_sub_rev]
    -- one-step inequality from minimality at the two interpolants
    have hstep : ∀ t : ℝ, 0 < t → t ≤ 1 →
        0 ≤ inner ℝ ((x - z) - (x' - z')) (x' - x) + t * ‖x' - x‖ ^ 2 := by
      intro t ht0 ht1
      have hp : (1 - t) • x + t • x' - z = (x - z) + t • (x' - x) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      have hq : (1 - t) • x' + t • x - z' = (x' - z') - t • (x' - x) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      have hc1 := seg_convex f hf x x' gx gx' hgx hgx' t ht0.le ht1
      have hc2 := seg_convex f hf x' x gx' gx hgx' hgx t ht0.le ht1
      have h1 : ((‖x - z‖ ^ 2 / 2 : ℝ) : EReal) + f x
          ≤ ((‖(1 - t) • x + t • x' - z‖ ^ 2 / 2 : ℝ) : EReal) + f ((1 - t) • x + t • x') :=
        hx _
      have h2 : ((‖x' - z'‖ ^ 2 / 2 : ℝ) : EReal) + f x'
          ≤ ((‖(1 - t) • x' + t • x - z'‖ ^ 2 / 2 : ℝ) : EReal) + f ((1 - t) • x' + t • x) :=
        hx' _
      have r1 : ‖x - z‖ ^ 2 / 2 + gx
          ≤ ‖(1 - t) • x + t • x' - z‖ ^ 2 / 2 + ((1 - t) * gx + t * gx') := by
        have hh : ((‖x - z‖ ^ 2 / 2 : ℝ) : EReal) + (gx : EReal)
            ≤ ((‖(1 - t) • x + t • x' - z‖ ^ 2 / 2 : ℝ) : EReal)
              + (((1 - t) * gx + t * gx' : ℝ) : EReal) := by
          rw [← hgx]
          exact le_trans h1 (add_le_add (le_refl _) hc1)
        rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hh
        exact hh
      have r2 : ‖x' - z'‖ ^ 2 / 2 + gx'
          ≤ ‖(1 - t) • x' + t • x - z'‖ ^ 2 / 2 + ((1 - t) * gx' + t * gx) := by
        have hh : ((‖x' - z'‖ ^ 2 / 2 : ℝ) : EReal) + (gx' : EReal)
            ≤ ((‖(1 - t) • x' + t • x - z'‖ ^ 2 / 2 : ℝ) : EReal)
              + (((1 - t) * gx' + t * gx : ℝ) : EReal) := by
          rw [← hgx']
          exact le_trans h2 (add_le_add (le_refl _) hc2)
        rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hh
        exact hh
      have e1 : ‖(x - z) + t • (x' - x)‖ ^ 2
          = ‖x - z‖ ^ 2 + 2 * t * inner ℝ (x - z) (x' - x) + t ^ 2 * ‖x' - x‖ ^ 2 := by
        rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht0]
        ring
      have e2 : ‖(x' - z') - t • (x' - x)‖ ^ 2
          = ‖x' - z'‖ ^ 2 - 2 * t * inner ℝ (x' - z') (x' - x) + t ^ 2 * ‖x' - x‖ ^ 2 := by
        rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht0]
        ring
      rw [hp, e1] at r1
      rw [hq, e2] at r2
      have hi : inner ℝ ((x - z) - (x' - z')) (x' - x)
          = inner ℝ (x - z) (x' - x) - inner ℝ (x' - z') (x' - x) := inner_sub_left _ _ _
      rw [hi]
      have hmul : t * 0 ≤ t * ((inner ℝ (x - z) (x' - x) - inner ℝ (x' - z') (x' - x))
          + t * ‖x' - x‖ ^ 2) := by
        rw [mul_zero]
        nlinarith [r1, r2]
      exact le_of_mul_le_mul_left hmul ht0
    -- rewrite the inner product and take `t → 0`
    have hid : inner ℝ ((x - z) - (x' - z')) (x' - x)
        = -‖x' - x‖ ^ 2 - inner ℝ (z - z') (x' - x) := by
      have hsplit : inner ℝ ((x - z) - (x' - z')) (x' - x)
          = inner ℝ (-(x' - x)) (x' - x) - inner ℝ (z - z') (x' - x) := by
        rw [show (x - z) - (x' - z') = -(x' - x) - (z - z') from by abel, inner_sub_left]
      have hnn : inner ℝ (-(x' - x)) (x' - x) = -‖x' - x‖ ^ 2 := by
        rw [inner_neg_left, real_inner_self_eq_norm_sq]
      rw [hsplit, hnn]
    have hb : -inner ℝ (z - z') (x' - x) ≤ ‖z - z'‖ * ‖x' - x‖ := by
      have h1 := abs_real_inner_le_norm (z - z') (x' - x)
      have h2 : -inner ℝ (z - z') (x' - x) ≤ |inner ℝ (z - z') (x' - x)| := neg_le_abs _
      linarith
    have hmain : ∀ t : ℝ, 0 < t → t ≤ 1 →
        ‖x' - x‖ ^ 2 ≤ ‖z - z'‖ * ‖x' - x‖ + t * ‖x' - x‖ ^ 2 := by
      intro t ht0 ht1
      have h := hstep t ht0 ht1
      rw [hid] at h
      linarith
    have hsq : ‖x' - x‖ ^ 2 ≤ ‖z - z'‖ * ‖x' - x‖ := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hden : (0:ℝ) < ‖x' - x‖ ^ 2 + 1 := by positivity
      have ht0 : 0 < min 1 (ε / (‖x' - x‖ ^ 2 + 1)) := lt_min one_pos (by positivity)
      have ht1 : min 1 (ε / (‖x' - x‖ ^ 2 + 1)) ≤ 1 := min_le_left _ _
      have htb : min 1 (ε / (‖x' - x‖ ^ 2 + 1)) * ‖x' - x‖ ^ 2 ≤ ε := by
        have h1 : min 1 (ε / (‖x' - x‖ ^ 2 + 1)) ≤ ε / (‖x' - x‖ ^ 2 + 1) := min_le_right _ _
        calc min 1 (ε / (‖x' - x‖ ^ 2 + 1)) * ‖x' - x‖ ^ 2
            ≤ (ε / (‖x' - x‖ ^ 2 + 1)) * ‖x' - x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ ≤ ε := by
              rw [div_mul_eq_mul_div, div_le_iff₀ hden]
              nlinarith [hε.le, sq_nonneg ‖x' - x‖]
      have := hmain _ ht0 ht1
      linarith
    rcases eq_or_lt_of_le (norm_nonneg (x' - x)) with h0 | h0
    · rw [← h0]
      exact norm_nonneg _
    · nlinarith [hsq, h0]
  refine ⟨hne, ?_⟩
  have hlip : LipschitzWith 1 (prox f) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm]
    simpa using hne a b
  exact hlip.continuous
