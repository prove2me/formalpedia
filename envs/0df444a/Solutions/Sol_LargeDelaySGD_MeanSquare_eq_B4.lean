-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.eq_B4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:56:45.270987+00:00
-- url     : https://prove2.me/submissions/aa17d1b8-4683-4772-8102-afc6d566e916

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model
import Theorems.Thm_LargeDelaySGD_MeanSquare_remark_1
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

open LDSInfra in
theorem solution {d : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (B : ℝ) (L : NNReal) (hA1 : Assumption1 F μ B L)
    (α : ℕ → ℝ) (s : ℕ → ℕ)
    (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (ω : ℕ → Ω → Ξ) (hω : IIDNoise P μ ω) (x₀ : EuclideanSpace ℝ (Fin d))
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : IsDASGD F α s ω x₀ X)
    (Bbar : ℝ) (hBbar : ∀ x, ∫ ξ, ‖stochGrad F x ξ‖ ∂μ ≤ Bbar) :
    ∀ n, Integrable (fun a => ‖gradient (objective F μ) (X (s n) a) -
        gradient (objective F μ) (X n a)‖) P ∧
      ∫ a, ‖gradient (objective F μ) (X (s n) a) - gradient (objective F μ) (X n a)‖ ∂P ≤
        L * Bbar * ∑ r ∈ Finset.Ico (s n) n, α (r + 1) := by
  intro n
  obtain ⟨-, -, hLip⟩ := LargeDelaySGD.MeanSquare.remark_1 μ F B L hA1
  set g := gradient (objective F μ) with hg
  set G : ℕ → Ω → EuclideanSpace ℝ (Fin d) :=
    fun r a => stochGrad F (X (s r) a) (ω (r + 1) a) with hGdef
  have hGn := G_norm μ P F B L hA1 α s hs ω hω x₀ X hX Bbar hBbar
  have hmX := measurable_X μ F B L hA1 α s hs ω hω.measurable x₀ X hX
  have hpt : ∀ a, ‖g (X (s n) a) - g (X n a)‖ ≤
      ∑ r ∈ Finset.Ico (s n) n, (L : ℝ) * α (r + 1) * ‖G r a‖ := by
    intro a
    have hsub := X_sub F α s ω x₀ X hX (s n) n (hs n) a
    calc ‖g (X (s n) a) - g (X n a)‖ ≤ L * ‖X (s n) a - X n a‖ := hLip.norm_sub_le _ _
      _ = L * ‖∑ r ∈ Finset.Ico (s n) n, α (r + 1) • G r a‖ := by
          rw [hsub]; simp [hGdef]
      _ ≤ L * ∑ r ∈ Finset.Ico (s n) n, ‖α (r + 1) • G r a‖ := by
          gcongr; exact norm_sum_le _ _
      _ = ∑ r ∈ Finset.Ico (s n) n, (L : ℝ) * α (r + 1) * ‖G r a‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hα _)]
          ring
  have hintS : Integrable (fun a => ∑ r ∈ Finset.Ico (s n) n, (L : ℝ) * α (r + 1) * ‖G r a‖) P :=
    integrable_finset_sum _ fun r _ => (hGn r).1.const_mul _
  have hmeas : AEStronglyMeasurable (fun a => ‖g (X (s n) a) - g (X n a)‖) P := by
    have hc : Continuous g := hLip.continuous
    exact (((hc.measurable.comp (hmX _)).sub (hc.measurable.comp (hmX _))).norm).aestronglyMeasurable
  have hint : Integrable (fun a => ‖g (X (s n) a) - g (X n a)‖) P :=
    hintS.mono' hmeas (ae_of_all _ fun a => by rw [norm_norm]; exact hpt a)
  refine ⟨hint, ?_⟩
  calc ∫ a, ‖g (X (s n) a) - g (X n a)‖ ∂P
      ≤ ∫ a, ∑ r ∈ Finset.Ico (s n) n, (L : ℝ) * α (r + 1) * ‖G r a‖ ∂P :=
        integral_mono hint hintS hpt
    _ = ∑ r ∈ Finset.Ico (s n) n, (L : ℝ) * α (r + 1) * ∫ a, ‖G r a‖ ∂P := by
        rw [integral_finset_sum _ fun r _ => (hGn r).1.const_mul _]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [integral_const_mul]
    _ ≤ ∑ r ∈ Finset.Ico (s n) n, (L : ℝ) * α (r + 1) * Bbar := by
        gcongr with r hr
        · have : (0:ℝ) ≤ L := L.2
          have := hα (r + 1)
          positivity
        · exact (hGn r).2
    _ = L * Bbar * ∑ r ∈ Finset.Ico (s n) n, α (r + 1) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
