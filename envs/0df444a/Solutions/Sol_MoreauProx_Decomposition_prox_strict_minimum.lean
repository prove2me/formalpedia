-- Prove2me | solution 1 for MoreauProx.Decomposition.prox_strict_minimum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T02:57:27.428464+00:00
-- url     : https://prove2.me/submissions/37ce33ff-645f-4606-8148-cf5e4fa8770a

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality

open MoreauProx.Decomposition

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

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → EReal) (hf : GammaZero f) (z : H) :
    ∃ x : H, ∀ u : H, u ≠ x → proxObjective f z x < proxObjective f z u := by
  simp only [proxObjective]
  exact prox_core f hf.ne_bot hf.exists_ne_top hf.convex_epigraph hf.lowerSemicontinuous z
