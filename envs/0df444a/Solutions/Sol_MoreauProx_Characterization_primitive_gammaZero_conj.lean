-- Prove2me | solution 1 for MoreauProx.Characterization.primitive_gammaZero_conj
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:01:57.482432+00:00
-- url     : https://prove2.me/submissions/fe810f0f-f469-4543-a0bb-5873fea0065f

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Calculus.Gradient.Basic
import Definitions.Def_MoreauProx_Characterization_Prox

section
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
theorem moreau_strict_minimum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (z : H) :
    ∃ x : H, ∀ u : H, u ≠ x →
      ((‖x - z‖ ^ 2 / 2 : ℝ) : EReal) + f x < ((‖u - z‖ ^ 2 / 2 : ℝ) : EReal) + f u :=
  prox_core f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 z
end

section

set_option autoImplicit false

/-- If `0 ≤ K + t * M` for all `t ∈ (0, 1]` with `M ≥ 0`, then `0 ≤ K`. -/
theorem mdp_nonneg_of_forall {K M : ℝ} (hM : 0 ≤ M)
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

/-- A sum of two extended reals equal to a real forces both summands to be real. -/
theorem mdp_add_eq_coe {p q : EReal} {r : ℝ} (h : p + q = (r : EReal)) :
    ∃ a b : ℝ, p = (a : EReal) ∧ q = (b : EReal) ∧ a + b = r := by
  induction p using EReal.rec with
  | bot => simp at h
  | top =>
    induction q using EReal.rec with
    | bot => simp at h
    | top => simp at h
    | coe b => simp at h
  | coe a =>
    induction q using EReal.rec with
    | bot => simp at h
    | top => simp at h
    | coe b => exact ⟨a, b, rfl, rfl, by exact_mod_cast h⟩

open MoreauProx.Characterization in open scoped InnerProductSpace in
/-- Fenchel–Young, easy direction. -/
theorem mdp_fy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (u y : H) :
    ((⟪u, y⟫_ℝ : ℝ) : EReal) - f u ≤ conj f y :=
  le_iSup (fun x => ((⟪x, y⟫_ℝ : ℝ) : EReal) - f x) u

open MoreauProx.Characterization in
/-- A proximal point of a `Γ₀` function has a finite value. -/
theorem mdp_prox_finite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (z x : H) (hp : IsProx f z x) :
    ∃ a : ℝ, f x = (a : EReal) := by
  obtain ⟨x0, hx0⟩ := hf.2.1
  have h := hp x0
  have hne : f x ≠ ⊤ := by
    intro htop
    rw [htop, EReal.coe_add_top] at h
    have hc := (EReal.coe_toReal hx0 (hf.1 x0)).symm
    rw [hc, ← EReal.coe_add, top_le_iff] at h
    exact EReal.coe_ne_top _ h
  exact ⟨(f x).toReal, (EReal.coe_toReal hne (hf.1 x)).symm⟩

open MoreauProx.Characterization in open scoped InnerProductSpace in
/-- Variational inequality from minimality of the proximal objective and convexity. -/
theorem mdp_varineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (z x : H) (a : ℝ) (hfx : f x = (a : EReal))
    (hp : IsProx f z x) (u : H) (c : ℝ) (hfu : f u = (c : EReal)) :
    ⟪u - x, z - x⟫_ℝ ≤ c - a := by
  have key : 0 ≤ (c - a - ⟪u - x, z - x⟫_ℝ) := by
    refine mdp_nonneg_of_forall (M := ‖u - x‖ ^ 2 / 2) (by positivity) ?_
    intro t ht0 ht1
    have hxe : (x, a) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
      simp only [Set.mem_ofPred_eq, hfx, le_refl]
    have hue : (u, c) ∈ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)} := by
      simp only [Set.mem_ofPred_eq, hfu, le_refl]
    have hconv := (hf.2.2.1) hxe hue (a := 1 - t) (b := t) (by linarith) ht0.le
      (by ring)
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hconv
    have hpr := hp ((1 - t) • x + t • u)
    change ((‖x - z‖ ^ 2 / 2 : ℝ) : EReal) + f x ≤ _ at hpr
    rw [hfx] at hpr
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
/-- The conjugate at `z - x` is bounded by the Fenchel–Young value. -/
theorem mdp_conj_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : GammaZero f) (z x : H) (a : ℝ) (hfx : f x = (a : EReal))
    (hp : IsProx f z x) :
    conj f (z - x) ≤ ((⟪x, z - x⟫_ℝ - a : ℝ) : EReal) := by
  unfold conj
  refine iSup_le fun u => ?_
  have hne := hf.1 u
  induction hfu : f u using EReal.rec with
  | bot => exact absurd hfu hne
  | top => simp
  | coe c =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have := mdp_varineq f hf z x a hfx hp u c hfu
    rw [inner_sub_left] at this
    linarith

open MoreauProx.Characterization in open scoped InnerProductSpace in
theorem moreau_decomposition {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) (x y z : H) :
    (z = x + y ∧ f x + g y = ((⟪x, y⟫_ℝ : ℝ) : EReal)) ↔ (IsProx f z x ∧ IsProx g z y) := by
  subst hg
  constructor
  · rintro ⟨rfl, hsum⟩
    obtain ⟨a, b, hfx, hgy, hab⟩ := mdp_add_eq_coe hsum
    refine ⟨fun u => ?_, fun v => ?_⟩
    · change ((‖x - (x + y)‖ ^ 2 / 2 : ℝ) : EReal) + f x ≤ _
      rw [hfx]
      have hne := hf.1 u
      induction hfu : f u using EReal.rec with
      | bot => exact absurd hfu hne
      | top => simp
      | coe c =>
        have hfy := mdp_fy f u y
        rw [hfu, hgy, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hfy
        rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
        have e1 : x - (x + y) = -y := by abel
        have e2 : u - (x + y) = (u - x) - y := by abel
        rw [e1, e2, norm_neg, norm_sub_sq_real]
        have e3 : ⟪u, y⟫_ℝ = ⟪u - x, y⟫_ℝ + ⟪x, y⟫_ℝ := by rw [inner_sub_left]; ring
        nlinarith [sq_nonneg ‖u - x‖]
    · change ((‖y - (x + y)‖ ^ 2 / 2 : ℝ) : EReal) + conj f y ≤ _
      rw [hgy]
      have hfy := mdp_fy f x v
      rw [hfx, ← EReal.coe_sub] at hfy
      refine le_trans ?_ (add_le_add le_rfl hfy)
      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have e1 : y - (x + y) = -x := by abel
      have e2 : v - (x + y) = (v - y) - x := by abel
      rw [e1, e2, norm_neg, norm_sub_sq_real]
      have e3 : ⟪x, v⟫_ℝ = ⟪v - y, x⟫_ℝ + ⟪x, y⟫_ℝ := by
        rw [inner_sub_left, real_inner_comm x v, real_inner_comm x y]; ring
      nlinarith [sq_nonneg ‖v - y‖]
  · rintro ⟨hpx, hpy⟩
    obtain ⟨a, hfx⟩ := mdp_prox_finite f hf z x hpx
    have hgw := mdp_conj_le f hf z x a hfx hpx
    have hgw' := mdp_fy f x (z - x)
    rw [hfx, ← EReal.coe_sub] at hgw'
    have hgweq : conj f (z - x) = ((⟪x, z - x⟫_ℝ - a : ℝ) : EReal) := le_antisymm hgw hgw'
    have hgy := mdp_fy f x y
    rw [hfx, ← EReal.coe_sub] at hgy
    have h1 := hpy (z - x)
    rw [hgweq] at h1
    have h2 := (add_le_add le_rfl hgy).trans h1
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
    have e1 : z - x - z = -x := by abel
    have e2 : y - z = (y - (z - x)) - x := by abel
    rw [e1, e2, norm_neg, norm_sub_sq_real] at h2
    have e3 : ⟪x, y⟫_ℝ = ⟪y - (z - x), x⟫_ℝ + ⟪x, z - x⟫_ℝ := by
      rw [inner_sub_left, real_inner_comm x y, real_inner_comm x (z - x)]; ring
    have h3 : ‖y - (z - x)‖ ^ 2 ≤ 0 := by nlinarith
    have h4 : ‖y - (z - x)‖ = 0 := by
      have := sq_nonneg ‖y - (z - x)‖
      have h5 : ‖y - (z - x)‖ ^ 2 = 0 := le_antisymm h3 this
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
    have hyw : y = z - x := sub_eq_zero.mp (norm_eq_zero.mp h4)
    refine ⟨by rw [hyw]; abel, ?_⟩
    rw [hyw, hgweq, hfx, ← EReal.coe_add]
    congr 1
    ring
end

namespace MoreauProof
open MoreauProx.Characterization
open scoped InnerProductSpace Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem prox_spec (f : H → EReal) (z : H) (h : ∃ x, IsProx f z x) :
    IsProx f z (prox f z) := by
  rw [prox, dif_pos h]
  exact h.choose_spec

theorem prox_spec_of_gamma (f : H → EReal) (hf : GammaZero f) (z : H) :
    IsProx f z (prox f z) := by
  apply prox_spec
  obtain ⟨x, hx⟩ := moreau_strict_minimum f hf z
  refine ⟨x, fun u => ?_⟩
  by_cases h : u = x
  · subst u; exact le_rfl
  · exact (hx u h).le

theorem dual_pair (f : H → EReal) (hf : GammaZero f) (z : H) :
    z = prox f z + prox (conj f) z ∧
      f (prox f z) + conj f (prox (conj f) z) =
        ((⟪prox f z, prox (conj f) z⟫_ℝ : ℝ) : EReal) := by
  have hp := prox_spec_of_gamma f hf z
  obtain ⟨a, ha⟩ := mdp_prox_finite f hf z (prox f z) hp
  have hge : conj f (z - prox f z) = ((⟪prox f z, z - prox f z⟫_ℝ - a : ℝ) : EReal) := by
    apply le_antisymm (mdp_conj_le f hf z (prox f z) a ha hp)
    have h := mdp_fy f (prox f z) (z - prox f z)
    simpa [ha, ← EReal.coe_sub] using h
  have hpair : z = prox f z + (z - prox f z) ∧
      f (prox f z) + conj f (z - prox f z) =
        ((⟪prox f z, z - prox f z⟫_ℝ : ℝ) : EReal) := by
    refine ⟨by abel, ?_⟩
    rw [ha, hge, ← EReal.coe_add]
    congr 1
    ring
  have hq := ((moreau_decomposition f (conj f) hf rfl _ _ z).mp hpair).2
  exact (moreau_decomposition f (conj f) hf rfl _ _ z).mpr
    ⟨hp, prox_spec (conj f) z ⟨_, hq⟩⟩

theorem value_coe (f : H → EReal) (hf : GammaZero f) (z : H) :
    f (prox f z) = ((f (prox f z)).toReal : EReal) := by
  obtain ⟨a, ha⟩ := mdp_prox_finite f hf z _ (prox_spec_of_gamma f hf z)
  simp [ha]

theorem dual_value_coe (f : H → EReal) (hf : GammaZero f) (z : H) :
    conj f (prox (conj f) z) = ((conj f (prox (conj f) z)).toReal : EReal) := by
  obtain ⟨a, b, ha, hb, _⟩ := mdp_add_eq_coe (dual_pair f hf z).2
  simp [hb]

theorem primitive_dual (f : H → EReal) (hf : GammaZero f) (z : H) :
    primitive f (conj f) z = ⟪prox (conj f) z, z⟫_ℝ -
      ‖prox (conj f) z‖ ^ 2 / 2 - (conj f (prox (conj f) z)).toReal := by
  have h := (dual_pair f hf z).2
  rw [value_coe f hf z, dual_value_coe f hf z, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
  have he : ⟪prox (conj f) z,z⟫_ℝ = ⟪prox (conj f) z,prox f z⟫_ℝ + ‖prox (conj f) z‖^2 := by
    calc
      _ = ⟪prox (conj f) z,prox f z + prox (conj f) z⟫_ℝ :=
        congrArg (fun u => ⟪prox (conj f) z,u⟫_ℝ) (dual_pair f hf z).1
      _ = _ := by rw [inner_add_right, real_inner_self_eq_norm_sq]
  simp only [primitive]
  have hc := real_inner_comm (prox (conj f) z) (prox f z)
  linarith

theorem primitive_subgrad (f : H → EReal) (hf : GammaZero f) (z w : H) :
    primitive f (conj f) z + ⟪w - z, prox (conj f) z⟫_ℝ ≤ primitive f (conj f) w := by
  have hp : IsProx (conj f) w (prox (conj f) w) :=
    ((moreau_decomposition f (conj f) hf rfl _ _ w).mp (dual_pair f hf w)).2
  have h := hp (prox (conj f) z)
  rw [dual_value_coe f hf w, dual_value_coe f hf z,
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  rw [norm_sub_sq_real, norm_sub_sq_real] at h
  rw [primitive_dual f hf z, primitive_dual f hf w, inner_sub_left]
  have c := real_inner_comm w (prox (conj f) z)
  have c' := real_inner_comm z (prox (conj f) z)
  linarith

theorem primitive_upper (f : H → EReal) (hf : GammaZero f) (z w : H) :
    primitive f (conj f) w - primitive f (conj f) z - ⟪w-z, prox (conj f) z⟫_ℝ ≤
      ‖w-z‖ ^ 2 / 2 := by
  have h := prox_spec_of_gamma f hf w (prox f z)
  rw [value_coe f hf w, value_coe f hf z,
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  have hw : prox f w - w = -prox (conj f) w := by
    conv_lhs => arg 2; rw [(dual_pair f hf w).1]
    abel
  have hz : prox f z - w = -(prox (conj f) z + (w-z)) := by
    conv_rhs => arg 1; arg 2; arg 2; rw [(dual_pair f hf z).1]
    abel
  rw [hw, hz, norm_neg, norm_neg, norm_add_sq_real] at h
  have hc := real_inner_comm (prox (conj f) z) (w-z)
  simp only [primitive]
  linarith

theorem primitive_gradient (f : H → EReal) (hf : GammaZero f) (z : H) :
    HasGradientAt (primitive f (conj f)) (prox (conj f) z) z := by
  rw [hasGradientAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds z hε] with w hw
  have hn : ‖w-z‖ < ε := by simpa [dist_eq_norm] using hw
  have hlo := primitive_subgrad f hf z w
  have hhi := primitive_upper f hf z w
  have hc := real_inner_comm (prox (conj f) z) (w-z)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  nlinarith [norm_nonneg (w-z)]

end MoreauProof

namespace MoreauProof
open MoreauProx.Characterization
open scoped InnerProductSpace Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem conj_ne_bot (f : H → EReal) (hf : GammaZero f) (y : H) : conj f y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hf.2.1
  have h := mdp_fy f x y
  rw [← EReal.coe_toReal hx (hf.1 x), ← EReal.coe_sub] at h
  intro hy
  rw [hy, le_bot_iff] at h
  exact EReal.coe_ne_bot _ h

theorem conj_convex (f : H → EReal) (hbot : ∀ x, f x ≠ ⊥) : EConvex (conj f) := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hp hq ⊢
  apply iSup_le
  intro x
  by_cases hx : f x = ⊤
  · simp [hx]
  · have he := (EReal.coe_toReal hx (hbot x)).symm
    have h1 := (mdp_fy f x p.1).trans hp
    have h2 := (mdp_fy f x q.1).trans hq
    rw [he, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h1 h2 ⊢
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hc : (a+b) * (f x).toReal = (f x).toReal := by rw [hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

theorem conj_lsc (f : H → EReal) (hbot : ∀ x, f x ≠ ⊥) : LowerSemicontinuous (conj f) := by
  apply lowerSemicontinuous_iSup
  intro x
  by_cases hx : f x = ⊤
  · have he : (fun y : H => ((⟪x,y⟫_ℝ : ℝ) : EReal) - f x) = fun _ => ⊥ := by
      funext y; simp [hx]
    rw [he]
    exact continuous_const.lowerSemicontinuous
  · have he := (EReal.coe_toReal hx (hbot x)).symm
    have he' : (fun y : H => ((⟪x,y⟫_ℝ : ℝ) : EReal) - f x) =
        fun y => ((⟪x,y⟫_ℝ - (f x).toReal : ℝ) : EReal) := by
      funext y; rw [he, ← EReal.coe_sub]; simp
    rw [he']
    exact (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous

theorem conj_gamma (f : H → EReal) (hf : GammaZero f) : GammaZero (conj f) := by
  refine ⟨conj_ne_bot f hf, ?_, conj_convex f hf.1, conj_lsc f hf.1⟩
  refine ⟨prox (conj f) 0, ?_⟩
  rw [dual_value_coe f hf 0]
  exact EReal.coe_ne_top _

theorem affine_bound (f : H → EReal) (hf : GammaZero f) :
    ∃ (y : H) (b : ℝ), ∀ u, ((⟪u,y⟫_ℝ + b : ℝ) : EReal) ≤ f u := by
  let y := prox (conj f) 0
  let b := -(conj f y).toReal
  refine ⟨y,b,fun u => ?_⟩
  have h := mdp_fy f u y
  have he := dual_value_coe f hf 0
  by_cases hu : f u = ⊤
  · simp [hu]
  · have hfu := (EReal.coe_toReal hu (hf.1 u)).symm
    rw [hfu, he, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    rw [hfu, EReal.coe_le_coe_iff]
    change ⟪u,y⟫_ℝ + -(conj f y).toReal ≤ (f u).toReal
    linarith

theorem affine_support_below (f : H → EReal) (hf : GammaZero f) (x : H) (a : ℝ)
    (hxa : (a : EReal) < f x) :
    ∃ (y : H) (b : ℝ), a < ⟪x,y⟫_ℝ + b ∧
      ∀ u, ((⟪u,y⟫_ℝ + b : ℝ) : EReal) ≤ f u := by
  let E : Set (H × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}
  have hclosed : IsClosed E :=
    hf.2.2.2.isClosed_epigraph.preimage
      (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  obtain ⟨L,s,hs,hL⟩ := geometric_hahn_banach_point_closed hf.2.2.1 hclosed
    (show (x,a) ∉ E from not_le.mpr hxa)
  let lam := L (0,1)
  let φ : H →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ H ℝ)
  have hdec (u : H) (r : ℝ) : L (u,r) = φ u + r * lam := by
    have he : (u,r) = (u,0) + r • ((0,1) : H × ℝ) := by simp
    rw [he, map_add, map_smul]
    simp [φ, lam]
  obtain ⟨u₀, hu₀⟩ := hf.2.1
  let c := (f u₀).toReal
  have hfc : f u₀ = (c : EReal) := (EReal.coe_toReal hu₀ (hf.1 u₀)).symm
  have hlam : 0 ≤ lam := by
    by_contra hneg
    have hn := not_le.mp hneg
    have hlt := hL (u₀, c + (|s - φ u₀ - c * lam| + 1) / (-lam)) (by
      change f u₀ ≤ _
      rw [hfc, EReal.coe_le_coe_iff]
      have := div_nonneg (show 0 ≤ |s - φ u₀ - c * lam| + 1 by positivity) (neg_nonneg.mpr hn.le)
      linarith)
    rw [hdec] at hlt
    have he : ((|s - φ u₀ - c * lam| + 1) / (-lam)) * lam =
        -(|s - φ u₀ - c * lam| + 1) := by field_simp [hn.ne]
    rw [add_mul, he] at hlt
    have := le_abs_self (s - φ u₀ - c * lam)
    have := neg_abs_le (s - φ u₀ - c * lam)
    linarith
  obtain ⟨y₀,b₀,hbase⟩ := affine_bound f hf
  let D := a - ⟪x,y₀⟫_ℝ - b₀
  let δ := (s - L (x,a)) / (2 * (|D|+1))
  have hden : 0 < 2 * (|D|+1) := by positivity
  have hδ : 0 < δ := div_pos (sub_pos.mpr hs) hden
  have hδeq : δ * (2 * (|D|+1)) = s - L (x,a) := by
    dsimp [δ]
    exact div_mul_cancel₀ _ hden.ne'
  have hgap : L (x,a) + δ * (a - ⟪x,y₀⟫_ℝ) < s + δ * b₀ := by
    have h := le_abs_self D
    have hh : δ * D ≤ δ * |D| := mul_le_mul_of_nonneg_left h hδ.le
    dsimp [D] at hh hδeq
    nlinarith [abs_nonneg (a - ⟪x,y₀⟫_ℝ-b₀)]
  let μ := lam + δ
  have hμ : 0 < μ := add_pos_of_nonneg_of_pos hlam hδ
  let ψ : H →L[ℝ] ℝ := (-μ⁻¹) • (φ - δ • InnerProductSpace.toDual ℝ H y₀)
  let y := (InnerProductSpace.toDual ℝ H).symm ψ
  let b := (s + δ * b₀) / μ
  have hy (u : H) : ⟪u,y⟫_ℝ = -(φ u - δ * ⟪u,y₀⟫_ℝ) / μ := by
    rw [real_inner_comm y u]
    change ⟪(InnerProductSpace.toDual ℝ H).symm ψ,u⟫_ℝ = _
    rw [InnerProductSpace.toDual_symm_apply]
    simp only [ψ, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      InnerProductSpace.toDual_apply_apply, smul_eq_mul]
    have hc := real_inner_comm u y₀
    rw [hc]
    ring
  refine ⟨y,b,?_,fun u => ?_⟩
  · rw [hy]
    dsimp [b]
    rw [← add_div, lt_div_iff₀ hμ]
    rw [hdec] at hgap
    dsimp [μ] at *
    nlinarith
  · by_cases hu : f u = ⊤
    · simp [hu]
    · have he := (EReal.coe_toReal hu (hf.1 u)).symm
      have hl := hL (u,(f u).toReal) (by change f u ≤ _; rw [he]; simp)
      have hb := hbase u
      rw [he, EReal.coe_le_coe_iff] at hb ⊢
      rw [hdec] at hl
      rw [hy]
      dsimp [b]
      rw [← add_div, div_le_iff₀ hμ]
      dsimp [μ]
      nlinarith [mul_le_mul_of_nonneg_left hb hδ.le]

theorem biconj (f : H → EReal) (hf : GammaZero f) : conj (conj f) = f := by
  funext x
  apply le_antisymm
  · apply iSup_le
    intro y
    by_cases hx : f x = ⊤
    · simp [hx]
    · by_cases hy : conj f y = ⊤
      · simp [hy]
      · have hx' := (EReal.coe_toReal hx (hf.1 x)).symm
        have hy' := (EReal.coe_toReal hy (conj_ne_bot f hf y)).symm
        have hh := mdp_fy f x y
        rw [hx',hy',← EReal.coe_sub,EReal.coe_le_coe_iff] at hh
        rw [hx',hy',← EReal.coe_sub,EReal.coe_le_coe_iff]
        have hc := real_inner_comm x y
        linarith
  · by_contra hn
    have hlt : conj (conj f) x < f x := not_le.mp hn
    obtain ⟨a,ha,hax⟩ := EReal.exists_between_coe_real hlt
    obtain ⟨y,b,hab,hbound⟩ := affine_support_below f hf x a hax
    have hconj : conj f y ≤ ((-b : ℝ) : EReal) := by
      apply iSup_le
      intro u
      by_cases hu : f u = ⊤
      · simp [hu]
      · have he := (EReal.coe_toReal hu (hf.1 u)).symm
        have h := hbound u
        rw [he,EReal.coe_le_coe_iff] at h
        rw [he,← EReal.coe_sub,EReal.coe_le_coe_iff]
        linarith
    have ht : conj f y ≠ ⊤ := by
      intro h; rw [h] at hconj
      exact EReal.coe_ne_top _ (top_le_iff.mp hconj)
    have he := (EReal.coe_toReal ht (conj_ne_bot f hf y)).symm
    rw [he,EReal.coe_le_coe_iff] at hconj
    have hh := mdp_fy (conj f) y x
    rw [he,← EReal.coe_sub] at hh
    have hbig : (a : EReal) < ((⟪y,x⟫_ℝ - (conj f y).toReal : ℝ) : EReal) := by
      rw [EReal.coe_lt_coe_iff]
      have hc := real_inner_comm x y
      linarith
    exact (not_lt_of_ge (hh.trans ha.le)) hbig

end MoreauProof

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


namespace MoreauProof
open MoreauProx.Characterization
open scoped InnerProductSpace Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem primitive_gamma (f : H → EReal) (hf : GammaZero f) :
    GammaZero (fun z => ((primitive f (conj f) z : ℝ) : EReal)) := by
  refine ⟨fun _ => EReal.coe_ne_bot _, ⟨0,EReal.coe_ne_top _⟩, ?_, ?_⟩
  · have hc := mpc_convex_of_subgrad (primitive f (conj f)) (prox (conj f))
      (primitive_subgrad f hf)
    intro p hp q hq a b ha hb hab
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul, EReal.coe_le_coe_iff] at hp hq ⊢
    have hh := hc.2 (Set.mem_univ p.1) (Set.mem_univ q.1) ha hb hab
    simp only [smul_eq_mul] at hh
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb))
  · apply Continuous.lowerSemicontinuous
    apply continuous_coe_real_ereal.comp
    exact continuous_iff_continuousAt.mpr (fun z => (primitive_gradient f hf z).differentiableAt.continuousAt)

theorem primitive_le (f : H → EReal) (hf : GammaZero f) (z u : H) (a : ℝ)
    (hu : f u = (a : EReal)) : primitive f (conj f) z ≤ ‖u-z‖^2/2 + a := by
  have h := prox_spec_of_gamma f hf z u
  rw [value_coe f hf z, hu, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  have he : prox f z - z = -prox (conj f) z := by
    conv_lhs => arg 2; rw [(dual_pair f hf z).1]
    abel
  rw [he, norm_neg] at h
  exact h

theorem primitive_conjugate (f : H → EReal) (hf : GammaZero f) (y : H) :
    conj (fun z => ((primitive f (conj f) z : ℝ) : EReal)) y =
      conj f y + ((‖y‖^2/2 : ℝ) : EReal) := by
  apply le_antisymm
  · by_cases hy : conj f y = ⊤
    · simp [hy]
    · have hy' := (EReal.coe_toReal hy (conj_ne_bot f hf y)).symm
      apply iSup_le
      intro z
      rw [hy', ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      have hh := mdp_fy f (prox f z) y
      rw [value_coe f hf z, hy', ← EReal.coe_sub, EReal.coe_le_coe_iff] at hh
      have he : ⟪z,y⟫_ℝ = ⟪prox f z,y⟫_ℝ + ⟪prox (conj f) z,y⟫_ℝ := by
        calc
          _ = ⟪prox f z + prox (conj f) z,y⟫_ℝ :=
            congrArg (fun u => ⟪u,y⟫_ℝ) (dual_pair f hf z).1
          _ = _ := inner_add_left _ _ _
      have hn := sq_nonneg ‖prox (conj f) z-y‖
      rw [norm_sub_sq_real] at hn
      simp only [primitive]
      linarith
  · apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mp
    apply iSup_le
    intro u
    by_cases hu : f u = ⊤
    · simp [hu]
    · have hu' := (EReal.coe_toReal hu (hf.1 u)).symm
      apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mpr
      rw [hu', ← EReal.coe_sub, ← EReal.coe_add]
      have hh := mdp_fy (fun z => ((primitive f (conj f) z : ℝ) : EReal)) (u+y) y
      rw [← EReal.coe_sub] at hh
      apply le_trans ?_ hh
      rw [EReal.coe_le_coe_iff]
      have hl := primitive_le f hf (u+y) u (f u).toReal hu'
      have he : u-(u+y) = -y := by abel
      rw [he,norm_neg] at hl
      rw [inner_add_left,real_inner_self_eq_norm_sq]
      linarith

end MoreauProof

open MoreauProx.Characterization
open scoped InnerProductSpace
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f g : H → EReal) (hf : GammaZero f) (hg : g = conj f) :
    GammaZero (fun z => ((primitive f g z : ℝ) : EReal)) ∧
      conj (fun z => ((primitive f g z : ℝ) : EReal)) =
        fun y => g y + ((‖y‖ ^ 2 / 2 : ℝ) : EReal) := by
  subst g
  exact ⟨MoreauProof.primitive_gamma f hf,funext (MoreauProof.primitive_conjugate f hf)⟩
