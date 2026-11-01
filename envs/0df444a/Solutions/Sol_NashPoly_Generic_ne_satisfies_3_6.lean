-- Prove2me | solution 1 for NashPoly.Generic.ne_satisfies_3_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:36:25.863236+00:00
-- url     : https://prove2.me/submissions/c0c3bf0a-bb48-491a-a125-5fb9e31797d8

import Mathlib
import Definitions.Def_NashPoly_Generic_MultiplierExpr

open MvPolynomial

namespace Sol36Aux

noncomputable def gradCLM {σ : Type} [Fintype σ] (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    (σ → ℝ) →L[ℝ] ℝ :=
  ∑ k, (eval z (pderiv k p)) • ContinuousLinearMap.proj k

theorem gradCLM_apply {σ : Type} [Fintype σ] (p : MvPolynomial σ ℝ) (z e : σ → ℝ) :
    gradCLM p z e = ∑ k, eval z (pderiv k p) * e k := by
  simp [gradCLM]

theorem hasStrictFDerivAt_eval {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    HasStrictFDerivAt (fun v => eval v p) (gradCLM p z) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : gradCLM (C a : MvPolynomial σ ℝ) z = 0 := by
      ext e; simp [gradCLM_apply]
    rw [this]
    simpa using hasStrictFDerivAt_const (a) z
  | add p q hp hq =>
    have := hp.add hq
    have h2 : gradCLM (p + q) z = gradCLM p z + gradCLM q z := by
      ext e; simp [gradCLM_apply, add_mul, Finset.sum_add_distrib]
    rw [h2]
    have key : (fun v : σ → ℝ => eval v (p + q)) = fun v => eval v p + eval v q := by
      ext v; simp
    rw [key]; exact this
  | mul_X p k hp =>
    have hX : HasStrictFDerivAt (fun v : σ → ℝ => v k) (ContinuousLinearMap.proj k : (σ → ℝ) →L[ℝ] ℝ) z :=
      (ContinuousLinearMap.proj k : (σ → ℝ) →L[ℝ] ℝ).hasStrictFDerivAt
    have := hp.mul hX
    have h2 : gradCLM (p * X k) z = eval z p • (ContinuousLinearMap.proj k : (σ → ℝ) →L[ℝ] ℝ) + z k • gradCLM p z := by
      ext e
      simp [gradCLM_apply, pderiv_X, Pi.single_apply, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, apply_ite (eval z), mul_ite]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
    have key : (fun v : σ → ℝ => eval v (p * X k)) = fun v => eval v p * v k := by
      ext v; simp
    rw [key]; exact this

/-- A curve in a level set of a submersion, with prescribed tangent. -/
theorem exists_curve {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (Ψ : E → F) (Ψ' : E →L[ℝ] F) (z : E) (hΨ : HasStrictFDerivAt Ψ Ψ' z)
    (hsurj : Ψ'.range = ⊤) (d : E) (hd : Ψ' d = 0) :
    ∃ c : ℝ → E, c 0 = z ∧ HasDerivAt c d 0 ∧ ∀ᶠ t in nhds (0 : ℝ), Ψ (c t) = Ψ z := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl ((Ψ' : E →ₗ[ℝ] F).ker)
  let Pl : E →ₗ[ℝ] (Ψ' : E →ₗ[ℝ] F).ker := Submodule.projectionOnto _ C hC
  let P : E →L[ℝ] (Ψ' : E →ₗ[ℝ] F).ker := LinearMap.toContinuousLinearMap Pl
  have hPker : P.ker = C := Submodule.ker_projectionOnto hC
  have hPrange : P.range = ⊤ := Submodule.range_projectionOnto hC
  let φ : ImplicitFunctionData ℝ E F ((Ψ' : E →ₗ[ℝ] F).ker) :=
    { leftFun := Ψ
      leftDeriv := Ψ'
      rightFun := P
      rightDeriv := P
      pt := z
      hasStrictFDerivAt_leftFun := hΨ
      hasStrictFDerivAt_rightFun := P.hasStrictFDerivAt
      range_leftDeriv := hsurj
      range_rightDeriv := hPrange
      isCompl_ker := by rw [hPker]; exact hC }
  have hderiv := φ.hasStrictFDerivAt_implicitFunction (Submodule.subtypeL _)
    (by ext x; simp only [φ, P, Pl]; simp) (by ext x; simp [φ])
  let x : (Ψ' : E →ₗ[ℝ] F).ker := ⟨d, hd⟩
  let γ := φ.implicitFunction (φ.leftFun φ.pt)
  refine ⟨fun t => γ (P z + t • x), ?_, ?_, ?_⟩
  · simp only [zero_smul, add_zero]
    exact φ.implicitFunction_apply_image.self_of_nhds
  · have hlin : HasDerivAt (fun t : ℝ => P z + t • x) x 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const x).const_add (P z)
    have h0 : P z + (0 : ℝ) • x = φ.rightFun φ.pt := by simp [φ]
    have hd' := hderiv.hasFDerivAt
    rw [← h0] at hd'
    exact hd'.comp_hasDerivAt (0 : ℝ) hlin
  · have hT : Filter.Tendsto (fun t : ℝ => (φ.leftFun φ.pt, P z + t • x)) (nhds 0)
        (nhds (φ.prodFun φ.pt)) := by
      rw [ImplicitFunctionData.prodFun_apply]
      refine Filter.Tendsto.prodMk_nhds tendsto_const_nhds ?_
      have : Continuous fun t : ℝ => P z + t • x := by fun_prop
      simpa [φ] using this.tendsto 0
    filter_upwards [hT.eventually φ.leftFun_implicitFunction] with t ht
    exact ht


theorem right_lt_of_deriv_neg {h : ℝ → ℝ} {a : ℝ} (hd : HasDerivAt h a 0) (ha : a < 0) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), h t < h 0 := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp hd
  have h2 : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, slope h 0 t < 0 := h1.eventually (Iio_mem_nhds ha)
  have h3 : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) {0}ᶜ :=
    nhdsWithin_mono _ (fun t ht => ne_of_gt ht)
  filter_upwards [h3 h2, self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field] at ht
  have htp : (0 : ℝ) < t - 0 := by simpa using htpos
  have := (div_neg_iff.mp ht)
  rcases this with ⟨_, h4⟩ | ⟨h4, _⟩
  · linarith
  · linarith

theorem right_gt_of_deriv_pos {h : ℝ → ℝ} {a : ℝ} (hd : HasDerivAt h a 0) (ha : 0 < a) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), h 0 < h t := by
  have := right_lt_of_deriv_neg hd.neg (by linarith)
  filter_upwards [this] with t ht
  simp at ht; linarith

theorem sum_extend {m' : ℕ} {M : Type} [AddCommMonoid M] [Module ℝ M] (S : Finset (Fin m'))
    (Λ : S → ℝ) (a : Fin m' → M) :
    ∑ s : S, Λ s • a s = ∑ j, (if h : j ∈ S then Λ ⟨j, h⟩ else 0) • a j := by
  rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by simp [hj])]
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [s.2]

section KKT

variable {n' m' : ℕ} (g : Fin m' → MvPolynomial (Fin n') ℝ) (z : Fin n' → ℝ)

noncomputable def cmap (S : Finset (Fin m')) : (Fin n' → ℝ) → (S → ℝ) :=
  fun v s => eval v (g s)

noncomputable def cder (S : Finset (Fin m')) : (Fin n' → ℝ) →L[ℝ] (S → ℝ) :=
  ContinuousLinearMap.pi fun s => gradCLM (g s) z

theorem cmap_deriv (S : Finset (Fin m')) : HasStrictFDerivAt (cmap g S) (cder g z S) z :=
  hasStrictFDerivAt_pi.2 fun s => hasStrictFDerivAt_eval (g s) z

def LICQ : Prop :=
  ∀ c : Fin m' → ℝ, (∀ j, c j * eval z (g j) = 0) → (∑ j, c j • gradCLM (g j) z = 0) → c = 0

def Xset (E : Finset (Fin m')) : Set (Fin n' → ℝ) :=
  {v | (∀ j ∈ E, eval v (g j) = 0) ∧ ∀ j ∉ E, 0 ≤ eval v (g j)}

theorem cder_surj (hL : LICQ g z) (S : Finset (Fin m')) (hS : ∀ j ∈ S, eval z (g j) = 0) :
    (cder g z S).range = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  set Λ : S → ℝ := fun s => f (fun t => if s = t then 1 else 0) with hΛ
  set c : Fin m' → ℝ := fun j => if h : j ∈ S then Λ ⟨j, h⟩ else 0 with hc
  have hfe : ∀ e, f (cder g z S e) = 0 := fun e => hle ⟨e, rfl⟩
  have hsum0 : ∑ j, c j • gradCLM (g j) z = 0 := by
    rw [← sum_extend S Λ (fun j => gradCLM (g j) z)]
    ext e
    have := hfe e
    rw [LinearMap.pi_apply_eq_sum_univ] at this
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [cder, hΛ, mul_comm]
  have hcz : ∀ j, c j * eval z (g j) = 0 := by
    intro j
    by_cases h : j ∈ S
    · rw [hS j h, mul_zero]
    · simp [hc, h]
  have := hL c hcz hsum0
  apply LinearMap.ext
  intro y
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hcs : c s = 0 := by rw [this]; rfl
  simp only [hc, s.2, dif_pos] at hcs
  simp [hΛ] at hcs
  simp [hcs]

theorem kkt_exists_mult (E : Finset (Fin m')) (φ : (Fin n' → ℝ) → ℝ)
    (φ' : (Fin n' → ℝ) →L[ℝ] ℝ) (hφ : HasStrictFDerivAt φ φ' z) (hz : z ∈ Xset g E)
    (hmin : IsMinOn φ (Xset g E) z) (hL : LICQ g z) :
    ∃ μ : Fin m' → ℝ, φ' = ∑ j, μ j • gradCLM (g j) z ∧ ∀ j, μ j * eval z (g j) = 0 := by
  classical
  set A : Finset (Fin m') := Finset.univ.filter (fun j => eval z (g j) = 0) with hA
  have hev : ∀ᶠ v in nhds z, ∀ j, j ∉ A → 0 < eval v (g j) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j ∈ A
    · exact Filter.Eventually.of_forall (fun _ h => absurd hj h)
    have hpos : 0 < eval z (g j) := by
      have hjE : j ∉ E := fun hE => hj (by simp [hA, hz.1 j hE])
      exact lt_of_le_of_ne (hz.2 j hjE) (fun h => hj (by simp [hA, h.symm]))
    have := (continuous_eval (g j)).continuousAt.eventually (lt_mem_nhds hpos)
    filter_upwards [this] with v hv _ using hv
  have hextr : IsLocalExtrOn φ {v | ∀ s : A, (fun (s : A) v => eval v (g s)) s v =
      (fun (s : A) v => eval v (g s)) s z} z := by
    left
    show ∀ᶠ v in nhdsWithin z _, φ z ≤ φ v
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with v hv hvs
    refine isMinOn_iff.mp hmin v ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have hjA : j ∈ A := by simp [hA, hz.1 j hj]
      have := hvs ⟨j, hjA⟩
      simp only at this
      rw [this]; exact hz.1 j hj
    · by_cases hjA : j ∈ A
      · have := hvs ⟨j, hjA⟩
        simp only at this
        rw [this]; exact hz.2 j hj
      · exact (hv j hjA).le
  obtain ⟨Λ, Λ₀, hne, hsum⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt
    (fun s => hasStrictFDerivAt_eval (g s) z) hφ
  set Λe : Fin m' → ℝ := fun j => if h : j ∈ A then Λ ⟨j, h⟩ else 0 with hΛe
  have hsum' : ∑ j, Λe j • gradCLM (g j) z + Λ₀ • φ' = 0 := by
    rw [← sum_extend A Λ (fun j => gradCLM (g j) z)]; exact hsum
  have hΛez : ∀ j, Λe j * eval z (g j) = 0 := by
    intro j
    by_cases h : j ∈ A
    · have : eval z (g j) = 0 := by simpa [hA] using h
      rw [this, mul_zero]
    · simp [hΛe, h]
  by_cases h0 : Λ₀ = 0
  · exfalso
    apply hne
    have hz0 : ∑ j, Λe j • gradCLM (g j) z = 0 := by simpa [h0] using hsum'
    have := hL Λe hΛez hz0
    have hΛ0 : Λ = 0 := by
      ext s
      have := congrFun this s
      simpa [hΛe, s.2] using this
    rw [hΛ0, h0]; rfl
  · refine ⟨fun j => -Λe j / Λ₀, ?_, fun j => ?_⟩
    · ext e
      have := congrArg (fun L => L e) hsum'
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply] at this ⊢
      have h2 : ∑ j, -Λe j / Λ₀ * gradCLM (g j) z e = -(∑ j, Λe j * gradCLM (g j) z e) / Λ₀ := by
        rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [h2]
      field_simp
      linarith
    · have := hΛez j
      simp only
      rw [div_mul_eq_mul_div, neg_mul, this]; simp

theorem kkt_sign (E : Finset (Fin m')) (φ : (Fin n' → ℝ) → ℝ)
    (φ' : (Fin n' → ℝ) →L[ℝ] ℝ) (hφ : HasStrictFDerivAt φ φ' z) (hz : z ∈ Xset g E)
    (hmin : IsMinOn φ (Xset g E) z) (hL : LICQ g z) (μ : Fin m' → ℝ)
    (hμ : φ' = ∑ j, μ j • gradCLM (g j) z) (hcomp : ∀ j, μ j * eval z (g j) = 0)
    (j0 : Fin m') (hj0 : j0 ∉ E) : 0 ≤ μ j0 := by
  classical
  by_contra hneg
  push Not at hneg
  set A : Finset (Fin m') := Finset.univ.filter (fun j => eval z (g j) = 0) with hA
  have hgj0 : eval z (g j0) = 0 := by
    have := hcomp j0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hneg.ne
    · exact h
  have hj0A : j0 ∈ A := by simp [hA, hgj0]
  have hAz : ∀ j ∈ A, eval z (g j) = 0 := fun j hj => by simpa [hA] using hj
  set S := A.erase j0 with hSdef
  have hSz : ∀ j ∈ S, eval z (g j) = 0 := fun j hj => hAz j (Finset.mem_of_mem_erase hj)
  obtain ⟨d, hd⟩ := LinearMap.range_eq_top.mp (cder_surj g z hL A hAz)
    (fun s : A => if (s : Fin m') = j0 then (1 : ℝ) else 0)
  have hdA : ∀ j (hj : j ∈ A), gradCLM (g j) z d = if j = j0 then 1 else 0 := by
    intro j hj
    have := congrFun hd ⟨j, hj⟩
    simpa [cder] using this
  have hdS : cder g z S d = 0 := by
    ext s
    have hsA : (s : Fin m') ∈ A := Finset.mem_of_mem_erase s.2
    have hsne : (s : Fin m') ≠ j0 := Finset.ne_of_mem_erase s.2
    have := hdA s hsA
    simp only [cder, ContinuousLinearMap.pi_apply, Pi.zero_apply]
    rw [this, if_neg hsne]
  have hφd : φ' d = μ j0 := by
    rw [hμ]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j0 (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ _) h)]
    · rw [hdA j0 hj0A, if_pos rfl, mul_one]
    by_cases hjA : j ∈ A
    · rw [hdA j hjA, if_neg hj, mul_zero]
    · have hμj : μ j = 0 := by
        have h1 := hcomp j
        have h2 : eval z (g j) ≠ 0 := fun h => hjA (by simp [hA, h])
        exact (mul_eq_zero.mp h1).resolve_right h2
      simp [hμj]
  obtain ⟨c, hc0, hcd, hcev⟩ := exists_curve (cmap g S) (cder g z S) z (cmap_deriv g z S)
    (cder_surj g z hL S hSz) d hdS
  have hφc : HasDerivAt (fun t => φ (c t)) (φ' d) 0 := by
    have h1 := hφ.hasFDerivAt
    rw [← hc0] at h1
    exact h1.comp_hasDerivAt (0 : ℝ) hcd
  have hgc : HasDerivAt (fun t => eval (c t) (g j0)) 1 0 := by
    have h1 : HasFDerivAt (fun v => eval v (g j0)) (gradCLM (g j0) z) (c 0) := by
      rw [hc0]; exact (hasStrictFDerivAt_eval (g j0) z).hasFDerivAt
    have := h1.comp_hasDerivAt (0 : ℝ) hcd
    rwa [hdA j0 hj0A, if_pos rfl] at this
  have hcont : Filter.Tendsto c (nhds 0) (nhds z) := by
    have := hcd.continuousAt.tendsto
    rwa [hc0] at this
  have hev : ∀ᶠ v in nhds z, ∀ j, j ∉ A → 0 < eval v (g j) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hj : j ∈ A
    · exact Filter.Eventually.of_forall (fun _ h => absurd hj h)
    have hpos : 0 < eval z (g j) := by
      have hjE : j ∉ E := fun hE => hj (by simp [hA, hz.1 j hE])
      exact lt_of_le_of_ne (hz.2 j hjE) (fun h => hj (by simp [hA, h.symm]))
    have := (continuous_eval (g j)).continuousAt.eventually (lt_mem_nhds hpos)
    filter_upwards [this] with v hv _ using hv
  have e1 := right_lt_of_deriv_neg hφc (by rw [hφd]; exact hneg)
  have e2 := right_gt_of_deriv_pos hgc one_pos
  have e3 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), cmap g S (c t) = cmap g S z :=
    nhdsWithin_le_nhds hcev
  have e4 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ j, j ∉ A → 0 < eval (c t) (g j) :=
    nhdsWithin_le_nhds (hcont.eventually hev)
  obtain ⟨t, h1, h2, h3, h4⟩ := (e1.and (e2.and (e3.and e4))).exists
  rw [hc0] at h1 h2
  have hmem : c t ∈ Xset g E := by
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have hjA : j ∈ A := by simp [hA, hz.1 j hj]
      have hjne : j ≠ j0 := fun h => hj0 (h ▸ hj)
      have hjS : j ∈ S := Finset.mem_erase.mpr ⟨hjne, hjA⟩
      have := congrFun h3 ⟨j, hjS⟩
      simp only [cmap] at this
      rw [this]; exact hSz j hjS
    · by_cases hjA : j ∈ A
      · by_cases hjne : j = j0
        · subst hjne; rw [hgj0] at h2; exact h2.le
        · have hjS : j ∈ S := Finset.mem_erase.mpr ⟨hjne, hjA⟩
          have := congrFun h3 ⟨j, hjS⟩
          simp only [cmap] at this
          rw [this, hSz j hjS]
      · exact (h4 j hjA).le
  have := isMinOn_iff.mp hmin _ hmem
  linarith

end KKT


theorem gradCLM_single {σ : Type} [Fintype σ] [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (z : σ → ℝ) (k : σ) : gradCLM p z (Pi.single k 1) = eval z (pderiv k p) := by
  simp [gradCLM_apply, Pi.single_apply]

open NashPoly.Generic

variable {N : ℕ} {n : Fin N → ℕ}

theorem repl_same (y : Var n → ℝ) (i : Fin N) (v : Fin (n i) → ℝ) (k : Fin (n i)) :
    repl y i v ⟨i, k⟩ = v k := by
  simp [repl]

theorem repl_ne (y : Var n → ℝ) (i j : Fin N) (h : j ≠ i) (v : Fin (n i) → ℝ) (k : Fin (n j)) :
    repl y i v ⟨j, k⟩ = y ⟨j, k⟩ := by
  simp [repl, Function.update_of_ne h]

theorem repl_blk (x : Var n → ℝ) (i : Fin N) : repl x i (blk x i) = x := by
  funext w
  rcases w with ⟨j, k⟩
  by_cases h : j = i
  · subst h; rw [repl_same]; rfl
  · rw [repl_ne _ _ _ h]

noncomputable def replLin (i : Fin N) : (Fin (n i) → ℝ) →ₗ[ℝ] (Var n → ℝ) where
  toFun e := repl 0 i e
  map_add' e e' := by
    funext w; rcases w with ⟨j, k⟩
    by_cases h : j = i
    · subst h; simp [repl_same]
    · simp [repl_ne _ _ _ h]
  map_smul' c e := by
    funext w; rcases w with ⟨j, k⟩
    by_cases h : j = i
    · subst h; simp [repl_same]
    · simp [repl_ne _ _ _ h]

theorem hasStrictFDerivAt_repl (x : Var n → ℝ) (i : Fin N) (z : Fin (n i) → ℝ) :
    HasStrictFDerivAt (fun v => repl x i v) (LinearMap.toContinuousLinearMap (replLin i)) z := by
  have h := (LinearMap.toContinuousLinearMap (replLin (n := n) i)).hasStrictFDerivAt.const_add
    (repl x i 0) (x := z)
  have key : (fun v => repl x i v) =
      fun v => repl x i 0 + (LinearMap.toContinuousLinearMap (replLin (n := n) i)) v := by
    funext v w
    rcases w with ⟨j, k⟩
    by_cases hj : j = i
    · subst hj
      simp [replLin, repl_same]
    · simp [replLin, repl_ne _ _ _ hj]
  rw [key]; exact h

end Sol36Aux

open Sol36Aux NashPoly.Generic Matrix in
theorem solution {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (hH : ∀ i, H i * Gmat (P.g i) = 1) :
    P.NESet ⊆ P.GSet H := by
  classical
  intro x hx i
  set z := blk x i with hzdef
  set Lc := LinearMap.toContinuousLinearMap (replLin (n := n) i) with hLc
  set φ' := (gradCLM (P.f i) x).comp Lc with hφ'
  have hφ : HasStrictFDerivAt (fun v => eval (repl x i v) (P.f i)) φ' z := by
    have h1 : HasStrictFDerivAt (fun v => eval v (P.f i)) (gradCLM (P.f i) x) (repl x i z) := by
      rw [hzdef, repl_blk]; exact hasStrictFDerivAt_eval _ _
    exact h1.comp z (hasStrictFDerivAt_repl x i z)
  have hφ'_single : ∀ k, φ' (Pi.single k 1) = P.gradf i x k := by
    intro k
    simp only [hφ', ContinuousLinearMap.comp_apply, hLc, LinearMap.coe_toContinuousLinearMap']
    rw [gradCLM_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
    · simp only [replLin, LinearMap.coe_mk, AddHom.coe_mk, repl_same]
      simp [Pi.single_apply, NEP.gradf]
    · intro j _ hj
      refine Finset.sum_eq_zero fun k' _ => ?_
      simp [replLin, repl_ne _ _ _ hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hzX : z ∈ Xset (P.g i) (P.E i) := hx.1 i
  have hmin : IsMinOn (fun v => eval (repl x i v) (P.f i)) (Xset (P.g i) (P.E i)) z := by
    refine isMinOn_iff.mpr fun v hv => ?_
    simp only [hzdef, repl_blk]
    exact hx.2 i v hv
  -- the matrices at z
  set Hz := (H i).map (eval z) with hHz
  set Gz := (Gmat (P.g i)).map (eval z) with hGz
  have hHG : Hz * Gz = 1 := by
    rw [hHz, hGz, ← Matrix.map_mul, hH i]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hGz_inl : ∀ (c : Fin (m i) → ℝ) k,
      (Gz *ᵥ c) (Sum.inl k) = ∑ j, c j * eval z (pderiv k (P.g i j)) := by
    intro c k
    simp [hGz, Gmat, Matrix.mulVec, dotProduct, mul_comm]
  have hGz_inr : ∀ (c : Fin (m i) → ℝ) j', (Gz *ᵥ c) (Sum.inr j') = eval z (P.g i j') * c j' := by
    intro c j'
    simp [hGz, Gmat, Matrix.mulVec, dotProduct, apply_ite (eval z), ite_mul]
  have hL : LICQ (P.g i) z := by
    intro c hc hsum
    have h0 : Gz *ᵥ c = 0 := by
      funext r
      rcases r with k | j'
      · rw [hGz_inl]
        have := congrArg (fun L => L (Pi.single k 1)) hsum
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          gradCLM_single, ContinuousLinearMap.zero_apply] at this
        simpa using this
      · rw [hGz_inr, mul_comm]; simpa using hc j'
    calc c = (Hz * Gz) *ᵥ c := by rw [hHG, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  obtain ⟨μ, hμ, hcomp⟩ := kkt_exists_mult (P.g i) z (P.E i) _ φ' hφ hzX hmin hL
  have hsign : ∀ j ∉ P.E i, 0 ≤ μ j := fun j hj =>
    kkt_sign (P.g i) z (P.E i) _ φ' hφ hzX hmin hL μ hμ hcomp j hj
  have hgrad : ∀ k, P.gradf i x k = ∑ j, μ j * eval z (pderiv k (P.g i j)) := by
    intro k
    rw [← hφ'_single, hμ]
    simp [gradCLM_single]
  have hfhat : P.fhat i x = Gz *ᵥ μ := by
    funext r
    rcases r with k | j'
    · rw [hGz_inl]; simp [NEP.fhat, hgrad]
    · rw [hGz_inr]
      simp only [NEP.fhat, Sum.elim_inr, Pi.zero_apply]
      rw [mul_comm]; exact (hcomp j').symm
  have hlam : ∀ j, P.lam H i x j = μ j := by
    intro j
    have : P.lam H i x j = (Hz *ᵥ P.fhat i x) j := by
      simp [NEP.lam, hHz, Matrix.mulVec, dotProduct, hzdef]
    rw [this, hfhat, Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
  refine ⟨fun k => ?_, (hx.1 i).1, fun j _ => ?_, (hx.1 i).2, fun j hj => ?_⟩
  · rw [hgrad k]
    simp only [hlam, NEP.gradg]
    rw [sub_eq_zero]
  · rw [hlam]; exact hcomp j
  · rw [hlam]; exact hsign j hj
