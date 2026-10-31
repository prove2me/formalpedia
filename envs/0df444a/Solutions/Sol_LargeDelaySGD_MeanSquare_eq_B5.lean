-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.eq_B5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:00:50.982979+00:00
-- url     : https://prove2.me/submissions/9d3a311d-02be-428b-b4ff-36bc857c3525

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Theorems.Thm_LargeDelaySGD_MeanSquare_remark_1
import Theorems.Thm_LargeDelaySGD_MeanSquare_jensen_bound
import Theorems.Thm_LargeDelaySGD_MeanSquare_eq_B4
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory LargeDelaySGD.MeanSquare

namespace LDSInfra

section Generic
variable {Ω E Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace Ξ]

lemma indep_integral (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (Y : Ω → E) (Z : Ω → Ξ) (hY : Measurable Y) (hZ : Measurable Z)
    (hind : IndepFun Y Z P) (hlaw : P.map Z = μ) (h : E × Ξ → ℝ) (hh : Measurable h) (C : ℝ)
    (hint : ∀ y, Integrable (fun ξ => h (y, ξ)) μ) (hC : ∀ y, ∫ ξ, ‖h (y, ξ)‖ ∂μ ≤ C) :
    Integrable (fun a => h (Y a, Z a)) P ∧
      ∫ a, h (Y a, Z a) ∂P = ∫ a, (∫ ξ, h (Y a, ξ) ∂μ) ∂P := by
  have hmap : P.map (fun a => (Y a, Z a)) = (P.map Y).prod μ := by
    rw [← hlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mp hind
  have hYZ : Measurable (fun a => (Y a, Z a)) := hY.prodMk hZ
  have hprod : Integrable h ((P.map Y).prod μ) := by
    rw [integrable_prod_iff hh.aestronglyMeasurable]
    refine ⟨ae_of_all _ hint, ?_⟩
    refine (integrable_const C).mono' ?_ (ae_of_all _ ?_)
    · exact (hh.norm.stronglyMeasurable.integral_prod_right' (ν := μ)).aestronglyMeasurable
    · intro y
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hC y
  have hint2 : Integrable h (P.map (fun a => (Y a, Z a))) := by rw [hmap]; exact hprod
  refine ⟨(integrable_map_measure hh.aestronglyMeasurable hYZ.aemeasurable).mp hint2, ?_⟩
  rw [← integral_map hYZ.aemeasurable hh.aestronglyMeasurable, hmap, integral_prod h hprod]
  have hm2 : StronglyMeasurable (fun y => ∫ ξ, h (y, ξ) ∂μ) :=
    hh.stronglyMeasurable.integral_prod_right'
  rw [integral_map hY.aemeasurable hm2.aestronglyMeasurable]

/-- `σ(ω_0, …, ω_n)`. -/
def mF (ω : ℕ → Ω → Ξ) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ i ∈ Set.Iic n, MeasurableSpace.comap (ω i) ‹MeasurableSpace Ξ›

lemma mF_le (ω : ℕ → Ω → Ξ) (hωm : ∀ i, Measurable (ω i)) (n : ℕ) :
    mF ω n ≤ ‹MeasurableSpace Ω› := by
  unfold mF
  exact iSup₂_le fun i _ => (hωm i).comap_le

lemma mF_mono (ω : ℕ → Ω → Ξ) {m n : ℕ} (h : m ≤ n) : mF ω m ≤ mF ω n := by
  unfold mF
  exact biSup_mono (fun i hi => le_trans (Set.mem_Iic.mp hi) h)

lemma comap_le_mF (ω : ℕ → Ω → Ξ) {i n : ℕ} (h : i ≤ n) :
    MeasurableSpace.comap (ω i) ‹MeasurableSpace Ξ› ≤ mF ω n := by
  unfold mF
  exact le_biSup (fun j => MeasurableSpace.comap (ω j) ‹MeasurableSpace Ξ›) (Set.mem_Iic.mpr h)

lemma indep_next (P : Measure Ω) [IsProbabilityMeasure P] (ω : ℕ → Ω → Ξ)
    (hωm : ∀ i, Measurable (ω i)) (hind : iIndepFun ω P) (n : ℕ)
    (Y : Ω → E) (hY : Measurable[mF ω n] Y) : IndepFun Y (ω (n + 1)) P := by
  have hi := (iIndepFun_iff_iIndep _ _ _).mp hind
  have hI := indep_iSup_of_disjoint (fun i => (hωm i).comap_le) hi
    (S := Set.Iic n) (T := {n + 1}) (by simp)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
  · have := hY.comap_le
    unfold mF at this
    exact this
  exact le_biSup (fun j => MeasurableSpace.comap (ω j) ‹MeasurableSpace Ξ›)
    (Set.mem_singleton (n + 1))

end Generic

section Model
variable {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]

lemma adapted (μ : Measure Ξ) (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal)
    (hA1 : Assumption1 F μ B L) (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n)
    (ω : ℕ → Ω → Ξ) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X) :
    ∀ n k, k ≤ n → Measurable[mF ω n] (X k) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    have : X 0 = fun _ => x₀ := funext hX.1
    rw [this]
    exact measurable_const
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · exact (ih k (by omega)).mono (mF_mono ω (by omega)) le_rfl
    · have hk' : k = n + 1 := by omega
      subst hk'
      have hXn : Measurable[mF ω (n + 1)] (X n) :=
        (ih n le_rfl).mono (mF_mono ω (by omega)) le_rfl
      have hXs : Measurable[mF ω (n + 1)] (X (s n)) :=
        (ih (s n) (hs n)).mono (mF_mono ω (by omega)) le_rfl
      have hω' : Measurable[mF ω (n + 1)] (ω (n + 1)) :=
        Measurable.of_comap_le (comap_le_mF ω le_rfl)
      have hG : Measurable[mF ω (n + 1)]
          (fun a => stochGrad F (X (s n) a) (ω (n + 1) a)) :=
        hA1.measurable_grad.comp (hXs.prodMk hω')
      have : X (n + 1) = fun a => X n a - α (n + 1) • stochGrad F (X (s n) a) (ω (n + 1) a) :=
        funext (hX.2 n)
      rw [this]
      exact hXn.sub (hG.const_smul (α (n + 1)))

lemma measurable_X (μ : Measure Ξ) (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal)
    (hA1 : Assumption1 F μ B L) (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n)
    (ω : ℕ → Ω → Ξ) (hωm : ∀ i, Measurable (ω i)) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X) (n : ℕ) :
    Measurable (X n) :=
  (adapted μ F B L hA1 α s hs ω x₀ X hX n n le_rfl).mono (mF_le ω hωm n) le_rfl

/-- `E ψ(X_{s n}, ω_{n+1}) = E ∫ ψ(X_{s n}, ξ) dμ` for a test function `ψ` of the noise. -/
lemma step_integral (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n)
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X) (n : ℕ)
    (k : ℕ) (hk : k ≤ n)
    (ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (C : ℝ) (hint : ∀ x y, Integrable (fun ξ => ψ x (stochGrad F y ξ)) μ)
    (hC : ∀ x y, ∫ ξ, ‖ψ x (stochGrad F y ξ)‖ ∂μ ≤ C) :
    Integrable (fun a => ψ (X n a) (stochGrad F (X k a) (ω (n + 1) a))) P ∧
      ∫ a, ψ (X n a) (stochGrad F (X k a) (ω (n + 1) a)) ∂P
        = ∫ a, (∫ ξ, ψ (X n a) (stochGrad F (X k a) ξ) ∂μ) ∂P := by
  have had := adapted μ F B L hA1 α s hs ω x₀ X hX n
  have hY : Measurable[mF ω n] (fun a => (X n a, X k a)) :=
    (had n le_rfl).prodMk (had k hk)
  have hind := indep_next P ω hω.measurable hω.indep n _ hY
  have hYm : Measurable (fun a => (X n a, X k a)) := hY.mono (mF_le ω hω.measurable n) le_rfl
  have hh : Measurable (fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × Ξ =>
      ψ p.1.1 (stochGrad F p.1.2 p.2)) := by
    have h1 : Measurable (fun p : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) × Ξ =>
        (p.1.2, p.2)) := (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have h2 := hA1.measurable_grad.comp h1
    exact hψ.comp ((measurable_fst.comp measurable_fst).prodMk h2)
  exact indep_integral P μ (fun a => (X n a, X k a)) (ω (n + 1)) hYm (hω.measurable _) hind
    (hω.law _) _ hh C (fun y => hint y.1 y.2) (fun y => hC y.1 y.2)


lemma X_sub (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (α : ℕ → ℝ) (s : ℕ → ℕ) (ω : ℕ → Ω → Ξ) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X) (k : ℕ) :
    ∀ n, k ≤ n → ∀ a, X n a = X k a -
      ∑ r ∈ Finset.Ico k n, α (r + 1) • stochGrad F (X (s r) a) (ω (r + 1) a) := by
  intro n hkn
  induction n, hkn using Nat.le_induction with
  | base => intro a; simp
  | succ n hkn ih =>
    intro a
    rw [hX.2 n a, ih a, Finset.sum_Ico_succ_top hkn]
    abel

lemma G_norm (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n)
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X)
    (Bbar : ℝ) (hBbar : ∀ x, ∫ ξ, ‖stochGrad F x ξ‖ ∂μ ≤ Bbar) (r : ℕ) :
    Integrable (fun a => ‖stochGrad F (X (s r) a) (ω (r + 1) a)‖) P ∧
      ∫ a, ‖stochGrad F (X (s r) a) (ω (r + 1) a)‖ ∂P ≤ Bbar := by
  have h := step_integral μ P F B L hA1 α s hs ω hω x₀ X hX r (s r) (hs r)
    (fun _ v => ‖v‖) measurable_snd.norm Bbar
    (fun _ y => ((hA1.memLp y).integrable (by norm_num)).norm)
    (fun _ y => by simpa using hBbar y)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  calc ∫ a, (∫ ξ, ‖stochGrad F (X (s r) a) ξ‖ ∂μ) ∂P ≤ ∫ _a, Bbar ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun a => integral_nonneg fun _ => norm_nonneg _)
          (integrable_const _) (ae_of_all _ fun a => hBbar _)
    _ = Bbar := by simp

end Model

end LDSInfra

namespace LDSInfra

lemma remainder_f {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : NNReal)
    (hf : ∀ x, HasGradientAt f (gradient f x) x) (hLip : LipschitzWith L (gradient f))
    (x h : EuclideanSpace ℝ (Fin d)) :
    |f (x + h) - f x - inner ℝ (gradient f x) h| ≤ L * ‖h‖ ^ 2 := by
  set g := gradient f with hg
  have hcont : Continuous (fun t : ℝ => inner ℝ (g (x + t • h)) h) := by
    have : Continuous (fun t : ℝ => g (x + t • h)) :=
      hLip.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    exact this.inner continuous_const
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => f (x + t • h)) (inner ℝ (g (x + t • h)) h) t := by
    intro t _
    have hl : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have := (hf (x + t • h)).hasFDerivAt.comp_hasDerivAt t hl
    exact this
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
  simp only [zero_smul, add_zero, one_smul] at hftc
  rw [← hftc]
  have hconst : inner ℝ (g x) h = ∫ t in (0:ℝ)..1, inner ℝ (g x) h := by simp
  rw [hconst, ← intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
    intervalIntegrable_const]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := L * ‖h‖ ^ 2) (f := fun t => inner ℝ (g (x + t • h)) h - inner ℝ (g x) h) ?_
  · simpa using this
  intro t ht
  simp only [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at ht
  rw [← inner_sub_left]
  calc ‖inner ℝ (g (x + t • h) - g x) h‖ ≤ ‖g (x + t • h) - g x‖ * ‖h‖ := norm_inner_le_norm _ _
    _ ≤ (L * ‖(x + t • h) - x‖) * ‖h‖ := by
        gcongr
        exact hLip.norm_sub_le _ _
    _ = L * (|t| * ‖h‖) * ‖h‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    _ ≤ L * (1 * ‖h‖) * ‖h‖ := by
        have : |t| ≤ 1 := by rw [abs_of_pos ht.1]; exact ht.2
        have hL : (0:ℝ) ≤ L := L.2
        gcongr
    _ = L * ‖h‖ ^ 2 := by ring

end LDSInfra

open LDSInfra in
theorem solution {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ)
    (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X)
    (Bbar : ℝ) (hBbar : ∀ x, ∫ ξ, ‖stochGrad F x ξ‖ ∂μ ≤ Bbar) :
    ∀ n, Integrable (fun a => objective F μ (X n a)) P ∧
      Integrable (fun a => ‖gradient (objective F μ) (X n a)‖ ^ 2) P ∧
      ∫ a, objective F μ (X (n + 1) a) ∂P - ∫ a, objective F μ (X n a) ∂P ≤
        -α (n + 1) * ∫ a, ‖gradient (objective F μ) (X n a)‖ ^ 2 ∂P
          + L * Bbar * Real.sqrt B * α (n + 1) * ∑ r ∈ Finset.Ico (s n) n, α (r + 1)
          + L * Real.sqrt B * α (n + 1) ^ 2 + 4 * L * B * α (n + 1) ^ 2 := by
  obtain ⟨-, hgradG, hLip⟩ := LargeDelaySGD.MeanSquare.remark_1 μ F B L hA1
  have hJ := LargeDelaySGD.MeanSquare.jensen_bound μ F B L hA1
  have hB4 := LargeDelaySGD.MeanSquare.eq_B4 μ P F B L hA1 α s hs hα ω hω x₀ X hX Bbar hBbar
  set f := objective F μ with hfdef
  set g := gradient f with hg
  have hgeq : ∀ y, g y = ∫ ξ, stochGrad F y ξ ∂μ := fun y => (hgradG y).gradient
  have hf : ∀ x, HasGradientAt f (g x) x := fun x => by rw [hgeq x]; exact hgradG x
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x =>
    (hf x).differentiableAt.continuousAt
  have hc : Continuous g := hLip.continuous
  have hB : 0 ≤ B := le_trans (sq_nonneg _) (hJ 0)
  have hgB : ∀ x, ‖g x‖ ≤ Real.sqrt B := fun x => Real.le_sqrt_of_sq_le (hJ x)
  have hL0 : (0:ℝ) ≤ L := L.2
  have hBbar0 : 0 ≤ Bbar := le_trans (integral_nonneg fun _ => norm_nonneg _) (hBbar 0)
  have hmX := measurable_X μ F B L hA1 α s hs ω hω.measurable x₀ X hX
  -- second moment and inner-product identities for the stochastic gradient G_n
  have hsq : ∀ n, Integrable (fun a => ‖stochGrad F (X (s n) a) (ω (n + 1) a)‖ ^ 2) P ∧
      ∫ a, ‖stochGrad F (X (s n) a) (ω (n + 1) a)‖ ^ 2 ∂P ≤ B := by
    intro n
    have h := step_integral μ P F B L hA1 α s hs ω hω x₀ X hX n (s n) (hs n)
      (fun _ v => ‖v‖ ^ 2) (measurable_snd.norm.pow_const 2) B
      (fun _ y => (hA1.memLp y).integrable_norm_pow (by norm_num))
      (fun _ y => by simpa using hA1.second_moment y)
    refine ⟨h.1, ?_⟩
    rw [h.2]
    calc ∫ a, (∫ ξ, ‖stochGrad F (X (s n) a) ξ‖ ^ 2 ∂μ) ∂P ≤ ∫ _a, B ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun a => integral_nonneg fun _ => by positivity)
            (integrable_const _) (ae_of_all _ fun a => hA1.second_moment _)
      _ = B := by simp
  have hip : ∀ n, Integrable (fun a => inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a))) P ∧
      ∫ a, inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a)) ∂P
        = ∫ a, inner ℝ (g (X n a)) (g (X (s n) a)) ∂P := by
    intro n
    have h := step_integral μ P F B L hA1 α s hs ω hω x₀ X hX n (s n) (hs n)
      (fun x v => inner ℝ (g x) v)
      ((hc.measurable.comp measurable_fst).inner measurable_snd) (Real.sqrt B * Bbar)
      (fun x y => (innerSL ℝ (g x)).integrable_comp ((hA1.memLp y).integrable (by norm_num)))
      (fun x y => by
        calc ∫ ξ, ‖inner ℝ (g x) (stochGrad F y ξ)‖ ∂μ
            ≤ ∫ ξ, Real.sqrt B * ‖stochGrad F y ξ‖ ∂μ := by
              apply integral_mono
              · exact ((innerSL ℝ (g x)).integrable_comp
                  ((hA1.memLp y).integrable (by norm_num))).norm
              · exact ((hA1.memLp y).integrable (by norm_num)).norm.const_mul _
              · intro ξ
                calc ‖inner ℝ (g x) (stochGrad F y ξ)‖ ≤ ‖g x‖ * ‖stochGrad F y ξ‖ :=
                      norm_inner_le_norm _ _
                  _ ≤ Real.sqrt B * ‖stochGrad F y ξ‖ := by gcongr; exact hgB x
          _ = Real.sqrt B * ∫ ξ, ‖stochGrad F y ξ‖ ∂μ := integral_const_mul _ _
          _ ≤ Real.sqrt B * Bbar := by gcongr; exact hBbar y)
    refine ⟨h.1, ?_⟩
    rw [h.2]
    congr 1
    funext a
    rw [hgeq (X (s n) a)]
    exact integral_inner ((hA1.memLp _).integrable (by norm_num)) _
  -- integrability of ‖∇f(X_n)‖²
  have hint2 : ∀ n, Integrable (fun a => ‖g (X n a)‖ ^ 2) P := by
    intro n
    refine (integrable_const B).mono' ?_ (ae_of_all _ fun a => ?_)
    · exact ((hc.measurable.comp (hmX n)).norm.pow_const 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hJ _
  -- one-step pointwise Taylor bound
  have hstep : ∀ n a, |f (X (n + 1) a) - f (X n a)
      + α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a))|
      ≤ L * α (n + 1) ^ 2 * ‖stochGrad F (X (s n) a) (ω (n + 1) a)‖ ^ 2 := by
    intro n a
    have h := remainder_f f L (fun x => hf x) hLip (X n a)
      (-(α (n + 1) • stochGrad F (X (s n) a) (ω (n + 1) a)))
    rw [← sub_eq_add_neg, ← hX.2 n a, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos (hα _)] at h
    have e : f (X (n + 1) a) - f (X n a)
        + α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a))
        = f (X (n + 1) a) - f (X n a)
          - -(α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a))) := by ring
    rw [e]
    refine h.trans (le_of_eq ?_)
    ring
  -- integrability of f(X_n)
  have hfint : ∀ n, Integrable (fun a => f (X n a)) P := by
    intro n
    induction n with
    | zero =>
      have : (fun a => f (X 0 a)) = fun _ => f x₀ := funext fun a => by rw [hX.1 a]
      rw [this]; exact integrable_const _
    | succ n ih =>
      have hdom : Integrable (fun a => α (n + 1) * Real.sqrt B *
          ‖stochGrad F (X (s n) a) (ω (n + 1) a)‖ +
          L * α (n + 1) ^ 2 * ‖stochGrad F (X (s n) a) (ω (n + 1) a)‖ ^ 2) P :=
        ((G_norm μ P F B L hA1 α s hs ω hω x₀ X hX Bbar hBbar n).1.const_mul _).add
          ((hsq n).1.const_mul _)
      have hdiff : Integrable (fun a => f (X (n + 1) a) - f (X n a)) P := by
        refine hdom.mono' ?_ (ae_of_all _ fun a => ?_)
        · exact ((hfc.measurable.comp (hmX _)).sub
            (hfc.measurable.comp (hmX _))).aestronglyMeasurable
        · have h1 := hstep n a
          have h2 : |α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a))|
              ≤ α (n + 1) * Real.sqrt B * ‖stochGrad F (X (s n) a) (ω (n + 1) a)‖ := by
            rw [abs_mul, abs_of_pos (hα _), mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (hα _).le
            calc |inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a))|
                ≤ ‖g (X n a)‖ * ‖stochGrad F (X (s n) a) (ω (n + 1) a)‖ :=
                  abs_real_inner_le_norm _ _
              _ ≤ Real.sqrt B * ‖stochGrad F (X (s n) a) (ω (n + 1) a)‖ := by
                  gcongr; exact hgB _
          rw [Real.norm_eq_abs]
          have := abs_sub_abs_le_abs_sub
            (f (X (n + 1) a) - f (X n a)
              + α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a)))
            (α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a)))
          have h3 : |f (X (n + 1) a) - f (X n a)| ≤
              |f (X (n + 1) a) - f (X n a)
                + α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a))|
              + |α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a))| := by
            have := abs_sub (f (X (n + 1) a) - f (X n a)
              + α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a)))
              (α (n + 1) * inner ℝ (g (X n a)) (stochGrad F (X (s n) a) (ω (n + 1) a)))
            simpa using this
          linarith
      refine (ih.add hdiff).congr (ae_of_all _ fun a => ?_)
      simp
  intro n
  refine ⟨hfint n, hint2 n, ?_⟩
  set G : Ω → EuclideanSpace ℝ (Fin d) := fun a => stochGrad F (X (s n) a) (ω (n + 1) a) with hG
  -- pointwise descent
  have hpt : ∀ a, f (X (n + 1) a) - f (X n a) ≤
      -(α (n + 1) * inner ℝ (g (X n a)) (G a)) + L * α (n + 1) ^ 2 * ‖G a‖ ^ 2 := by
    intro a
    have := hstep n a
    have := le_abs_self (f (X (n + 1) a) - f (X n a)
      + α (n + 1) * inner ℝ (g (X n a)) (G a))
    simp only [hG] at *
    linarith
  have hI1 : Integrable (fun a => -(α (n + 1) * inner ℝ (g (X n a)) (G a))) P :=
    ((hip n).1.const_mul _).neg
  have hI2 : Integrable (fun a => L * α (n + 1) ^ 2 * ‖G a‖ ^ 2) P := (hsq n).1.const_mul _
  have hmain : ∫ a, objective F μ (X (n + 1) a) ∂P - ∫ a, objective F μ (X n a) ∂P ≤
      -(α (n + 1) * ∫ a, inner ℝ (g (X n a)) (g (X (s n) a)) ∂P) + L * α (n + 1) ^ 2 * B := by
    rw [← integral_sub (hfint _) (hfint _)]
    calc ∫ a, (f (X (n + 1) a) - f (X n a)) ∂P
        ≤ ∫ a, (-(α (n + 1) * inner ℝ (g (X n a)) (G a)) + L * α (n + 1) ^ 2 * ‖G a‖ ^ 2) ∂P :=
          integral_mono ((hfint _).sub (hfint _)) (hI1.add hI2) hpt
      _ = -(α (n + 1) * ∫ a, inner ℝ (g (X n a)) (G a) ∂P)
            + L * α (n + 1) ^ 2 * ∫ a, ‖G a‖ ^ 2 ∂P := by
          rw [integral_add hI1 hI2, integral_neg, integral_const_mul, integral_const_mul]
      _ ≤ _ := by
          rw [(hip n).2]
          gcongr
          exact (hsq n).2
  -- lower bound for the inner product term
  have hinner_int : Integrable (fun a => inner ℝ (g (X n a)) (g (X (s n) a))) P := by
    refine (integrable_const B).mono' ?_ (ae_of_all _ fun a => ?_)
    · exact ((hc.measurable.comp (hmX n)).inner
        (hc.measurable.comp (hmX (s n)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      calc |inner ℝ (g (X n a)) (g (X (s n) a))| ≤ ‖g (X n a)‖ * ‖g (X (s n) a)‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ Real.sqrt B * Real.sqrt B := by
            gcongr
            · exact hgB _
            · exact hgB _
        _ = B := Real.mul_self_sqrt hB
  have hlow : ∫ a, ‖g (X n a)‖ ^ 2 ∂P - Real.sqrt B *
      ∫ a, ‖g (X (s n) a) - g (X n a)‖ ∂P ≤ ∫ a, inner ℝ (g (X n a)) (g (X (s n) a)) ∂P := by
    rw [← integral_const_mul, ← integral_sub (hint2 n) ((hB4 n).1.const_mul _)]
    apply integral_mono ((hint2 n).sub ((hB4 n).1.const_mul _)) hinner_int
    intro a
    have e : inner ℝ (g (X n a)) (g (X (s n) a))
        = ‖g (X n a)‖ ^ 2 + inner ℝ (g (X n a)) (g (X (s n) a) - g (X n a)) := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]; ring
    have h2 : |inner ℝ (g (X n a)) (g (X (s n) a) - g (X n a))|
        ≤ Real.sqrt B * ‖g (X (s n) a) - g (X n a)‖ := by
      calc _ ≤ ‖g (X n a)‖ * ‖g (X (s n) a) - g (X n a)‖ := abs_real_inner_le_norm _ _
        _ ≤ _ := by gcongr; exact hgB _
    simp only [Pi.sub_apply]
    rw [e]
    linarith [neg_abs_le (inner ℝ (g (X n a)) (g (X (s n) a) - g (X n a)))]
  have hB4n := (hB4 n).2
  have hsqB : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB
  have hsB0 := Real.sqrt_nonneg B
  have ha := hα (n + 1)
  have hsum0 : 0 ≤ ∑ r ∈ Finset.Ico (s n) n, α (r + 1) :=
    Finset.sum_nonneg fun r _ => (hα _).le
  have hD0 : 0 ≤ ∫ a, ‖g (X (s n) a) - g (X n a)‖ ∂P := integral_nonneg fun _ => norm_nonneg _
  -- combine
  have hc1 : -(α (n + 1) * ∫ a, inner ℝ (g (X n a)) (g (X (s n) a)) ∂P)
      ≤ -α (n + 1) * ∫ a, ‖g (X n a)‖ ^ 2 ∂P
        + α (n + 1) * Real.sqrt B * (L * Bbar * ∑ r ∈ Finset.Ico (s n) n, α (r + 1)) := by
    have := mul_le_mul_of_nonneg_left hlow ha.le
    have h4 : Real.sqrt B * ∫ a, ‖g (X (s n) a) - g (X n a)‖ ∂P ≤
        Real.sqrt B * (L * Bbar * ∑ r ∈ Finset.Ico (s n) n, α (r + 1)) :=
      mul_le_mul_of_nonneg_left hB4n hsB0
    nlinarith
  have hc2 : L * α (n + 1) ^ 2 * B ≤ L * Real.sqrt B * α (n + 1) ^ 2 + 4 * L * B * α (n + 1) ^ 2 := by
    have : 0 ≤ L * Real.sqrt B * α (n + 1) ^ 2 := by positivity
    have : 0 ≤ L * B * α (n + 1) ^ 2 := by positivity
    nlinarith
  have : α (n + 1) * Real.sqrt B * (L * Bbar * ∑ r ∈ Finset.Ico (s n) n, α (r + 1))
      = L * Bbar * Real.sqrt B * α (n + 1) * ∑ r ∈ Finset.Ico (s n) n, α (r + 1) := by ring
  linarith
