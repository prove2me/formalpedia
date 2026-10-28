-- Prove2me | solution 1 for InfoRelaxTS.Asymptotic.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:50:46.136065+00:00
-- url     : https://prove2.me/submissions/29656839-ab6a-4454-9aaa-3417ca2439a7

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open InfoRelaxTS InfoRelaxTS.Asymptotic
open scoped ENNReal

namespace IRS3

variable {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

lemma measurable_iid (κ : Kernel Θ ℝ) [IsMarkovKernel κ] :
    Measurable (fun θ => Measure.infinitePi (fun _ : ℕ => κ θ)) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      (fun _ => by simp)) ?_
  rintro S ⟨s, t, ht, rfl⟩
  have ht' : ∀ i ∈ s, MeasurableSet (t i) := fun i _ => ht i (Set.mem_univ i)
  have : (fun θ => Measure.infinitePi (fun _ : ℕ => κ θ) ((s : Set ℕ).pi t)) =
      fun θ => ∏ i ∈ s, κ θ (t i) := funext fun θ => Measure.infinitePi_pi _ ht'
  rw [this]
  exact Finset.measurable_prod _ (fun i _ => κ.measurable_coe (ht i (Set.mem_univ i)))

noncomputable def iidK (κ : Kernel Θ ℝ) [IsMarkovKernel κ] : Kernel Θ (ℕ → ℝ) :=
  ⟨fun θ => Measure.infinitePi (fun _ => κ θ), measurable_iid κ⟩

instance (κ : Kernel Θ ℝ) [IsMarkovKernel κ] : IsMarkovKernel (iidK κ) :=
  ⟨fun θ => by simp only [iidK, Kernel.coe_mk]; infer_instance⟩

noncomputable def armK (κ : Kernel Θ ℝ) [IsMarkovKernel κ] : Kernel Θ (Θ × (ℕ → ℝ)) :=
  Kernel.deterministic id measurable_id ×ₖ iidK κ

instance (κ : Kernel Θ ℝ) [IsMarkovKernel κ] : IsMarkovKernel (armK κ) := by
  unfold armK; infer_instance

lemma armK_apply (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (θ : Θ) :
    armK κ θ = (Measure.dirac θ).prod (Measure.infinitePi fun _ : ℕ => κ θ) := by
  rw [armK, Kernel.prod_apply, Kernel.deterministic_apply]; rfl

lemma I_eq (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)] (P : Fin K → Kernel Y Θ)
    (y : Fin K → Y) : I R P y = Measure.pi fun a => armK (R a) ∘ₘ P a (y a) := by
  unfold I
  congr 1
  funext a
  congr 1
  funext θ
  rw [armK_apply]

instance (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)] (P : Fin K → Kernel Y Θ)
    [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y) : IsProbabilityMeasure (I R P y) := by
  rw [I_eq]
  haveI : ∀ a, IsProbabilityMeasure (armK (R a) ∘ₘ P a (y a)) := fun a => inferInstance
  infer_instance

lemma map_theta (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)] (P : Fin K → Kernel Y Θ)
    [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y) :
    (I R P y).map (fun ω a => (ω a).1) = priorLaw P y := by
  rw [I_eq]
  haveI : ∀ a, SigmaFinite ((armK (R a) ∘ₘ P a (y a)).map Prod.fst) := fun a => by
    haveI := Measure.isProbabilityMeasure_map (μ := armK (R a) ∘ₘ P a (y a)) measurable_fst.aemeasurable
    infer_instance
  rw [Measure.pi_map_pi (fun a => measurable_fst.aemeasurable)]
  unfold priorLaw
  congr 1
  funext a
  rw [Measure.map_comp _ _ measurable_fst]
  have : (armK (R a)).map Prod.fst = Kernel.deterministic id measurable_id := by
    rw [← Kernel.fst_eq, armK, Kernel.fst_prod]
  rw [this, Measure.deterministic_comp_eq_map, Measure.map_id]

lemma measurable_mu (R : Fin K → Kernel Θ ℝ) (a : Fin K) : Measurable (Monotone.mu R a) :=
  (StronglyMeasurable.integral_kernel (κ := R a) (f := fun r : ℝ => r)
    stronglyMeasurable_id).measurable

lemma measurable_muBar (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ) (a : Fin K) :
    Measurable (Monotone.muBar R P a) :=
  (StronglyMeasurable.integral_kernel (κ := P a) (f := Monotone.mu R a)
    (measurable_mu R a).stronglyMeasurable).measurable

lemma measurable_yseq (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (y : Fin K → Y) (a : Fin K) (n : ℕ) :
    Measurable (fun ω : Outcome K Θ => yseq U y a ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have h2 : Measurable (fun ω : Outcome K Θ => (ω a).2 n) :=
      (measurable_pi_apply n).comp (measurable_snd.comp (measurable_pi_apply a))
    exact (hU a).comp (ih.prodMk h2)

lemma measurable_muHat (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (y : Fin K → Y) (a : Fin K) (n : ℕ) :
    Measurable (fun ω : Outcome K Θ => muHat R P U y a n ω) :=
  (measurable_muBar R P a).comp (measurable_yseq U hU y a n)

lemma measurable_theta : Measurable (fun (ω : Outcome K Θ) (a : Fin K) => (ω a).1) :=
  measurable_pi_lambda _ fun a => measurable_fst.comp (measurable_pi_apply a)

end IRS3

namespace IRS5

variable {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- Sample mean of the first `n` rewards. -/
noncomputable def avg (n : ℕ) (r : ℕ → ℝ) : ℝ := (∑ i ∈ Finset.range n, r i) / (n : ℝ)

lemma measurable_avg (n : ℕ) : Measurable (avg n) := by
  unfold avg
  exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).div_const _

lemma slln_iid (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable (fun r : ℝ => r) μ) :
    ∀ᵐ r ∂(Measure.infinitePi fun _ : ℕ => μ),
      Tendsto (fun n => avg n r) atTop (𝓝 (∫ x, x ∂μ)) := by
  set π := Measure.infinitePi fun _ : ℕ => μ
  have hmp : ∀ i, MeasurePreserving (fun r : ℕ → ℝ => r i) π μ := fun i =>
    measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i
  have hint : Integrable (fun r : ℕ → ℝ => r 0) π := by
    exact (hmp 0).integrable_comp_of_integrable hμ
  have hind : iIndepFun (fun i (r : ℕ → ℝ) => r i) π :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hident : ∀ i, IdentDistrib (fun r : ℕ → ℝ => r i) (fun r => r 0) π π := fun i =>
    ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      by rw [(hmp i).map_eq, (hmp 0).map_eq]⟩
  have h := strong_law_ae_real (fun i (r : ℕ → ℝ) => r i) hint (fun i j hij => hind.indepFun hij) hident
  have hE : ∫ r, r 0 ∂π = ∫ x, x ∂μ := by
    rw [← (hmp 0).map_eq]
    exact (integral_map (μ := π) (φ := fun r : ℕ → ℝ => r 0) (measurable_pi_apply 0).aemeasurable
      (f := fun x : ℝ => x) aestronglyMeasurable_id).symm
  filter_upwards [h] with r hr
  rw [hE] at hr
  exact hr

end IRS5

namespace IRS5

open IRS3

variable {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- The law of one arm's outcome `(θ, (R_n))` under the belief `z`. -/
noncomputable def nu (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) (z : Y) :
    Measure (Θ × (ℕ → ℝ)) :=
  armK κ ∘ₘ Pk z

instance (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) [IsMarkovKernel Pk] (z : Y) :
    IsProbabilityMeasure (nu κ Pk z) := by
  unfold nu; infer_instance

lemma lintegral_nu (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) (z : Y)
    {G : Θ × (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G x ∂(nu κ Pk z) = ∫⁻ θ, ∫⁻ r, G (θ, r) ∂(iidK κ θ) ∂(Pk z) := by
  unfold nu
  rw [Measure.lintegral_bind (armK κ).aemeasurable hG.aemeasurable]
  refine lintegral_congr fun θ => ?_
  rw [armK_apply, Measure.dirac_prod, lintegral_map hG measurable_prodMk_left]
  rfl

lemma slln_nu (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) [IsMarkovKernel Pk] (z : Y)
    (hint : Integrable (fun r : ℝ => r) (κ ∘ₘ Pk z)) :
    ∀ᵐ x ∂(nu κ Pk z), Tendsto (fun n => avg n x.2) atTop (𝓝 (∫ r, r ∂κ x.1)) := by
  have hm : Measurable (fun θ => ∫ r, r ∂κ θ) :=
    (StronglyMeasurable.integral_kernel (κ := κ) (f := fun r : ℝ => r)
      stronglyMeasurable_id).measurable
  have hS : MeasurableSet {x : Θ × (ℕ → ℝ) |
      Tendsto (fun n => avg n x.2 - ∫ r, r ∂κ x.1) atTop (𝓝 0)} :=
    measurableSet_tendsto (𝓝 0) fun n =>
      ((measurable_avg n).comp measurable_snd).sub (hm.comp measurable_fst)
  have h1 : ∀ᵐ θ ∂(Pk z), Integrable (fun r : ℝ => r) (κ θ) :=
    ((Measure.integrable_comp_iff hint.1).1 hint).1
  have h2 : ∀ᵐ x ∂(nu κ Pk z),
      Tendsto (fun n => avg n x.2 - ∫ r, r ∂κ x.1) atTop (𝓝 0) := by
    unfold nu
    refine Measure.ae_comp_of_ae_ae hS ?_
    filter_upwards [h1] with θ hθ
    rw [armK_apply, Measure.dirac_prod, ae_map_iff measurable_prodMk_left.aemeasurable hS]
    filter_upwards [slln_iid (κ θ) hθ] with r hr
    simpa using hr.sub_const (∫ r, r ∂κ θ)
  filter_upwards [h2] with x hx
  simpa using hx.add_const (∫ r, r ∂κ x.1)

/-- One-step Bayes rule for functions, from conjugacy on rectangles. -/
lemma bayes_step (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) [IsMarkovKernel Pk]
    (u : Y → ℝ → Y) (hu : Measurable (Function.uncurry u))
    (hc : ∀ (z : Y) (A : Set ℝ) (B : Set Θ), MeasurableSet A → MeasurableSet B →
      ∫⁻ θ in B, κ θ A ∂(Pk z) = ∫⁻ r in A, Pk (u z r) B ∂(κ ∘ₘ Pk z))
    (z : Y) {F : Θ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ θ, ∫⁻ s, F (θ, s) ∂κ θ ∂Pk z = ∫⁻ s, ∫⁻ θ, F (θ, s) ∂Pk (u z s) ∂(κ ∘ₘ Pk z) := by
  have huz : Measurable (u z) := hu.comp measurable_prodMk_left
  set η : Kernel ℝ Θ := Pk.comap (u z) huz
  have hmeas : Pk z ⊗ₘ κ = ((κ ∘ₘ Pk z) ⊗ₘ η).map Prod.swap := by
    haveI : IsProbabilityMeasure (((κ ∘ₘ Pk z) ⊗ₘ η).map Prod.swap) :=
      Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
    rintro _ ⟨B, hB, A, hA, rfl⟩
    simp only [Set.mem_setOf_eq] at hA hB
    rw [Measure.compProd_apply_prod hB hA, Measure.map_apply measurable_swap (hB.prod hA),
      Set.preimage_swap_prod, Measure.compProd_apply_prod hA hB]
    exact hc z A B hA hB
  rw [← Measure.lintegral_compProd hF, hmeas, lintegral_map hF measurable_swap,
    Measure.lintegral_compProd (f := fun a => F a.swap) (hF.comp measurable_swap)]
  rfl

lemma map_update_infinitePi (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    ((Measure.infinitePi fun _ : ℕ => μ).prod μ).map
      (fun p : (ℕ → ℝ) × ℝ => Function.update p.1 n p.2) =
      Measure.infinitePi fun _ : ℕ => μ := by
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  have hpre : (fun p : (ℕ → ℝ) × ℝ => Function.update p.1 n p.2) ⁻¹' ((s : Set ℕ).pi t) =
      ((s.erase n : Set ℕ).pi t) ×ˢ (if n ∈ s then t n else Set.univ) := by
    ext ⟨r, x⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_erase]
    constructor
    · intro h
      refine ⟨fun i ⟨hin, his⟩ => ?_, ?_⟩
      · have := h i his
        rwa [Function.update_of_ne hin] at this
      · split_ifs with hn
        · have := h n hn
          rwa [Function.update_self] at this
        · exact Set.mem_univ _
    · rintro ⟨h1, h2⟩ i hi
      by_cases hin : i = n
      · subst hin
        rw [Function.update_self]
        rwa [if_pos hi] at h2
      · rw [Function.update_of_ne hin]
        exact h1 i ⟨hin, hi⟩
  rw [Measure.map_apply measurable_update' (MeasurableSet.pi (Set.to_countable _)
    fun i _ => ht i), hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun i _ => ht i)]
  split_ifs with hn
  · exact Finset.prod_erase_mul s (fun i => μ (t i)) hn
  · rw [measure_univ, mul_one, Finset.erase_eq_of_notMem hn]

lemma lintegral_resample (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ)
    {f : (ℕ → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, f r ∂(Measure.infinitePi fun _ : ℕ => μ) =
      ∫⁻ r, ∫⁻ s, f (Function.update r n s) ∂μ ∂(Measure.infinitePi fun _ : ℕ => μ) := by
  have h := (lintegral_prod (μ := Measure.infinitePi fun _ : ℕ => μ) (ν := μ)
    (fun p : (ℕ → ℝ) × ℝ => f (Function.update p.1 n p.2))
    (hf.comp measurable_update').aemeasurable).symm
  rw [h, ← lintegral_map hf measurable_update', map_update_infinitePi]

end IRS5

namespace IRS5

open IRS3

variable {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- Belief after the first `n` rewards of `r`, starting from `z` (8). -/
def ys (u : Y → ℝ → Y) (z : Y) : ℕ → (ℕ → ℝ) → Y
  | 0, _ => z
  | n + 1, r => u (ys u z n r) (r n)

lemma measurable_ys (u : Y → ℝ → Y) (hu : Measurable (Function.uncurry u)) (z : Y) (n : ℕ) :
    Measurable (ys u z n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hu.comp (ih.prodMk (measurable_pi_apply n))

lemma ys_congr (u : Y → ℝ → Y) (z : Y) (n : ℕ) {r r' : ℕ → ℝ} (h : ∀ i < n, r i = r' i) :
    ys u z n r = ys u z n r' := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ys]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

lemma ys_update_succ (u : Y → ℝ → Y) (z : Y) (n : ℕ) (r : ℕ → ℝ) (s : ℝ) :
    ys u z (n + 1) (Function.update r n s) = u (ys u z n r) s := by
  simp only [ys, Function.update_self]
  rw [ys_congr u z n (r := Function.update r n s) (r' := r)
    (fun i hi => Function.update_of_ne (by omega) _ _)]

/-- `G` depends on the reward sequence only through its first `n` entries. -/
def DepOn (n : ℕ) (G : Θ × (ℕ → ℝ) → ℝ≥0∞) : Prop :=
  ∀ θ (r r' : ℕ → ℝ), (∀ i < n, r i = r' i) → G (θ, r) = G (θ, r')

lemma measurable_post (Pk : Kernel Y Θ) [IsMarkovKernel Pk] (g : (ℕ → ℝ) → Y) (hg : Measurable g)
    {G : Θ × (ℕ → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    Measurable (fun r : ℕ → ℝ => ∫⁻ θ', G (θ', r) ∂Pk (g r)) := by
  have := Measurable.lintegral_kernel_prod_right (κ := Pk.comap g hg)
    (f := fun r θ' => G (θ', r)) (hG.comp measurable_swap)
  simpa [Kernel.comap_apply] using this

lemma measurable_resampled (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (n : ℕ) {G : Θ × (ℕ → ℝ) → ℝ≥0∞}
    (hG : Measurable G) :
    Measurable (fun x : Θ × (ℕ → ℝ) => ∫⁻ s, G (x.1, Function.update x.2 n s) ∂κ x.1) := by
  have := Measurable.lintegral_kernel_prod_right (κ := κ.comap Prod.fst measurable_fst)
    (f := fun x s => G (x.1, Function.update x.2 n s))
    (hG.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_update'.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  simpa [Kernel.comap_apply] using this

/-- The posterior of `θ` after `n` rewards is `Pk (ys n)`: conditional-law identity for
nonnegative functions of `θ` and of the first `n` rewards. -/
theorem posterior_n (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) [IsMarkovKernel Pk]
    (u : Y → ℝ → Y) (hu : Measurable (Function.uncurry u))
    (hc : ∀ (z : Y) (A : Set ℝ) (B : Set Θ), MeasurableSet A → MeasurableSet B →
      ∫⁻ θ in B, κ θ A ∂(Pk z) = ∫⁻ r in A, Pk (u z r) B ∂(κ ∘ₘ Pk z))
    (z : Y) (n : ℕ) :
    ∀ G : Θ × (ℕ → ℝ) → ℝ≥0∞, Measurable G → DepOn n G →
      ∫⁻ x, G x ∂(nu κ Pk z) = ∫⁻ x, ∫⁻ θ', G (θ', x.2) ∂Pk (ys u z n x.2) ∂(nu κ Pk z) := by
  induction n with
  | zero =>
    intro G hG hdep
    have hpost := measurable_post Pk (ys u z 0) (measurable_ys u hu z 0) hG
    rw [lintegral_nu κ Pk z hG, lintegral_nu κ Pk z
      (G := fun x => ∫⁻ θ', G (θ', x.2) ∂Pk (ys u z 0 x.2)) (hpost.comp measurable_snd)]
    have h0 : ∀ θ r, G (θ, r) = G (θ, 0) := fun θ r => hdep θ r 0 (fun i hi => absurd hi (by omega))
    simp only [ys]
    simp_rw [h0, lintegral_const, measure_univ, mul_one]
    rw [lintegral_const, measure_univ, mul_one]
  | succ n ih =>
    intro G hG hdep
    set H : Θ × (ℕ → ℝ) → ℝ≥0∞ := fun x => ∫⁻ s, G (x.1, Function.update x.2 n s) ∂κ x.1
      with hH
    have hHm : Measurable H := measurable_resampled κ n hG
    set K : (ℕ → ℝ) → ℝ≥0∞ := fun r => ∫⁻ θ'', G (θ'', r) ∂Pk (ys u z (n + 1) r) with hK
    have hKm : Measurable K := measurable_post Pk (ys u z (n + 1)) (measurable_ys u hu z _) hG
    set H' : Θ × (ℕ → ℝ) → ℝ≥0∞ := fun x => ∫⁻ s, K (Function.update x.2 n s) ∂κ x.1
      with hH'
    have hH'm : Measurable H' := measurable_resampled κ n (G := fun x => K x.2)
      (hKm.comp measurable_snd)
    have hupd : ∀ (r r' : ℕ → ℝ) (s : ℝ), (∀ i < n, r i = r' i) →
        ∀ i < n + 1, Function.update r n s i = Function.update r' n s i := by
      intro r r' s h i hi
      by_cases hin : i = n
      · subst hin; simp
      · rw [Function.update_of_ne hin, Function.update_of_ne hin]; exact h i (by omega)
    have hKdep : ∀ r r' : ℕ → ℝ, (∀ i < n + 1, r i = r' i) → K r = K r' := by
      intro r r' h
      simp only [hK]
      rw [ys_congr u z (n + 1) h]
      exact lintegral_congr fun θ'' => hdep θ'' r r' h
    have hHdep : DepOn n H := fun θ r r' h => by
      simp only [hH]
      exact lintegral_congr fun s => hdep θ _ _ (hupd r r' s h)
    have hH'dep : DepOn n H' := fun θ r r' h => by
      simp only [hH']
      exact lintegral_congr fun s => hKdep _ _ (hupd r r' s h)
    -- (i) resample coordinate `n`
    have e1 : ∫⁻ x, G x ∂(nu κ Pk z) = ∫⁻ x, H x ∂(nu κ Pk z) := by
      rw [lintegral_nu κ Pk z hG, lintegral_nu κ Pk z hHm]
      refine lintegral_congr fun θ => ?_
      exact lintegral_resample (κ θ) n (f := fun r => G (θ, r)) (hG.comp measurable_prodMk_left)
    -- (iii) one Bayes step, pointwise
    have e3 : ∀ x : Θ × (ℕ → ℝ), ∫⁻ θ', H (θ', x.2) ∂Pk (ys u z n x.2) =
        ∫⁻ θ', H' (θ', x.2) ∂Pk (ys u z n x.2) := by
      intro x
      set z' := ys u z n x.2
      have hF : Measurable (fun p : Θ × ℝ => G (p.1, Function.update x.2 n p.2)) :=
        hG.comp (measurable_fst.prodMk ((measurable_update (f := x.2)).comp measurable_snd))
      have hb := bayes_step κ Pk u hu hc z' hF
      calc ∫⁻ θ', H (θ', x.2) ∂Pk z'
          = ∫⁻ s, ∫⁻ θ, G (θ, Function.update x.2 n s) ∂Pk (u z' s) ∂(κ ∘ₘ Pk z') := hb
        _ = ∫⁻ s, K (Function.update x.2 n s) ∂(κ ∘ₘ Pk z') := by
            refine lintegral_congr fun s => ?_
            simp only [hK, ys_update_succ]
            rfl
        _ = ∫⁻ θ', ∫⁻ s, K (Function.update x.2 n s) ∂κ θ' ∂Pk z' :=
            Measure.lintegral_bind κ.aemeasurable
              ((hKm.comp (measurable_update (f := x.2))).aemeasurable)
        _ = ∫⁻ θ', H' (θ', x.2) ∂Pk z' := rfl
    -- (v) resample back
    have e5 : ∫⁻ x, H' x ∂(nu κ Pk z) = ∫⁻ x, K x.2 ∂(nu κ Pk z) := by
      rw [lintegral_nu κ Pk z hH'm, lintegral_nu κ Pk z (G := fun x => K x.2)
        (hKm.comp measurable_snd)]
      refine lintegral_congr fun θ => ?_
      exact (lintegral_resample (κ θ) n hKm).symm
    rw [e1, ih H hHm hHdep]
    simp_rw [e3]
    rw [← ih H' hH'm hH'dep, e5]

end IRS5

namespace IRS5

open IRS3

variable {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- Restriction of the reward sequence to its first `n` entries. -/
def restr (n : ℕ) (x : Θ × (ℕ → ℝ)) : Fin n → ℝ := fun i => x.2 i

/-- Extension by zero of a finite reward vector. -/
noncomputable def ext0 (n : ℕ) (v : Fin n → ℝ) : ℕ → ℝ :=
  fun i => if h : i < n then v ⟨i, h⟩ else 0

lemma measurable_restr (n : ℕ) : Measurable (restr (Θ := Θ) n) :=
  measurable_pi_lambda _ fun i => (measurable_pi_apply (i : ℕ)).comp measurable_snd

lemma measurable_ext0 (n : ℕ) : Measurable (ext0 n) := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i < n
  · simp only [ext0, h, dite_true]; exact measurable_pi_apply _
  · simp only [ext0, h, dite_false]; exact measurable_const

lemma ext0_restr (n : ℕ) (x : Θ × (ℕ → ℝ)) : ∀ i < n, ext0 n (restr n x) i = x.2 i := by
  intro i hi
  simp [ext0, restr, hi]

/-- The natural filtration of the observed rewards. -/
def filt : Filtration ℕ (inferInstance : MeasurableSpace (Θ × (ℕ → ℝ))) where
  seq n := MeasurableSpace.comap (restr n) inferInstance
  mono' := by
    intro i j hij
    have hfac : restr (Θ := Θ) i = (fun v : Fin j → ℝ => fun k : Fin i => v ⟨k, by omega⟩) ∘
        restr j := rfl
    show MeasurableSpace.comap (restr i) _ ≤ MeasurableSpace.comap (restr j) _
    rw [hfac, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (measurable_pi_lambda _ fun k => measurable_pi_apply _).comap_le
  le' n := (measurable_restr n).comap_le

/-- A measurable function of the first `n` rewards is `filt n`-measurable. -/
lemma measurable_filt (n : ℕ) {β : Type*} [MeasurableSpace β] {f : (ℕ → ℝ) → β}
    (hf : Measurable f) (hdep : ∀ r r' : ℕ → ℝ, (∀ i < n, r i = r' i) → f r = f r') :
    Measurable[filt (Θ := Θ) n] (fun x : Θ × (ℕ → ℝ) => f x.2) := by
  have : (fun x : Θ × (ℕ → ℝ) => f x.2) = (f ∘ ext0 n) ∘ restr n := by
    funext x
    exact (hdep _ _ (ext0_restr n x)).symm
  rw [this]
  exact (hf.comp (measurable_ext0 n)).comp (comap_measurable _)

lemma filt_set (n : ℕ) {A : Set (Θ × (ℕ → ℝ))} (hA : MeasurableSet[filt n] A) :
    ∃ A' : Set (ℕ → ℝ), MeasurableSet A' ∧
      (∀ r r' : ℕ → ℝ, (∀ i < n, r i = r' i) → (r ∈ A' ↔ r' ∈ A')) ∧ A = Prod.snd ⁻¹' A' := by
  obtain ⟨B, hB, rfl⟩ := hA
  refine ⟨(fun r : ℕ → ℝ => fun i : Fin n => r i) ⁻¹' B,
    (measurable_pi_lambda _ fun i => measurable_pi_apply _) hB, fun r r' h => ?_, rfl⟩
  have : (fun i : Fin n => r i) = fun i : Fin n => r' i := funext fun i => h i i.2
  simp only [Set.mem_preimage, this]

end IRS5

namespace IRS5

open IRS3

variable {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- Conditional mean reward `μ(θ)`. -/
noncomputable def muK (κ : Kernel Θ ℝ) (θ : Θ) : ℝ := ∫ r, r ∂κ θ

lemma measurable_muK (κ : Kernel Θ ℝ) : Measurable (muK κ) :=
  (StronglyMeasurable.integral_kernel (κ := κ) (f := fun r : ℝ => r)
    stronglyMeasurable_id).measurable

/-- Posterior predictive mean after `n` rewards. -/
noncomputable def fseq (κ : Kernel Θ ℝ) (Pk : Kernel Y Θ) (u : Y → ℝ → Y) (z : Y) (n : ℕ)
    (r : ℕ → ℝ) : ℝ :=
  ∫ θ, muK κ θ ∂Pk (ys u z n r)

lemma measurable_fseq (κ : Kernel Θ ℝ) (Pk : Kernel Y Θ) (u : Y → ℝ → Y)
    (hu : Measurable (Function.uncurry u)) (z : Y) (n : ℕ) :
    Measurable (fseq κ Pk u z n) := by
  have : Measurable (fun z' => ∫ θ, muK κ θ ∂Pk z') :=
    (StronglyMeasurable.integral_kernel (κ := Pk) (f := muK κ)
      (measurable_muK κ).stronglyMeasurable).measurable
  exact this.comp (measurable_ys u hu z n)

lemma integrable_muK (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) [IsMarkovKernel Pk]
    (z : Y) (hint : Integrable (fun r : ℝ => r) (κ ∘ₘ Pk z)) : Integrable (muK κ) (Pk z) := by
  have h := ((Measure.integrable_comp_iff hint.1).1 hint).2
  refine h.mono (measurable_muK κ).aestronglyMeasurable (Eventually.of_forall fun θ => ?_)
  exact (norm_integral_le_integral_norm _).trans (le_abs_self _)

lemma map_fst_nu (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) [IsMarkovKernel Pk]
    (z : Y) : (nu κ Pk z).map Prod.fst = Pk z := by
  unfold nu
  rw [Measure.map_comp _ _ measurable_fst]
  have : (armK κ).map Prod.fst = Kernel.deterministic id measurable_id := by
    rw [← Kernel.fst_eq, armK, Kernel.fst_prod]
  rw [this, Measure.deterministic_comp_eq_map, Measure.map_id]

lemma integrable_g (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) [IsMarkovKernel Pk]
    (z : Y) (hint : Integrable (fun r : ℝ => r) (κ ∘ₘ Pk z)) :
    Integrable (fun x : Θ × (ℕ → ℝ) => muK κ x.1) (nu κ Pk z) := by
  have : Integrable (muK κ) ((nu κ Pk z).map Prod.fst) := by
    rw [map_fst_nu]; exact integrable_muK κ Pk z hint
  exact this.comp_measurable measurable_fst

lemma setLIntegral_post (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ) [IsMarkovKernel Pk]
    (u : Y → ℝ → Y) (hu : Measurable (Function.uncurry u))
    (hc : ∀ (z : Y) (A : Set ℝ) (B : Set Θ), MeasurableSet A → MeasurableSet B →
      ∫⁻ θ in B, κ θ A ∂(Pk z) = ∫⁻ r in A, Pk (u z r) B ∂(κ ∘ₘ Pk z))
    (z : Y) (n : ℕ) (A' : Set (ℕ → ℝ)) (hA' : MeasurableSet A')
    (hdep : ∀ r r' : ℕ → ℝ, (∀ i < n, r i = r' i) → (r ∈ A' ↔ r' ∈ A'))
    {h : Θ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x in Prod.snd ⁻¹' A', h x.1 ∂(nu κ Pk z) =
      ∫⁻ x in Prod.snd ⁻¹' A', ∫⁻ θ, h θ ∂Pk (ys u z n x.2) ∂(nu κ Pk z) := by
  have hA : MeasurableSet (Prod.snd ⁻¹' A' : Set (Θ × (ℕ → ℝ))) := measurable_snd hA'
  rw [← lintegral_indicator hA, ← lintegral_indicator hA]
  have hG : Measurable ((Prod.snd ⁻¹' A').indicator (fun x : Θ × (ℕ → ℝ) => h x.1)) :=
    (hh.comp measurable_fst).indicator hA
  have hdepG : DepOn n ((Prod.snd ⁻¹' A').indicator (fun x : Θ × (ℕ → ℝ) => h x.1)) := by
    intro θ r r' hrr
    have h2 := hdep r r' hrr
    by_cases h1 : r ∈ A'
    · simp [Set.indicator, h1, h2.mp h1]
    · simp [Set.indicator, h1, (not_congr h2).mp h1]
  rw [posterior_n κ Pk u hu hc z n _ hG hdepG]
  refine lintegral_congr fun x => ?_
  by_cases hx : x.2 ∈ A'
  · simp [Set.indicator, hx]
  · simp [Set.indicator, hx]

/-- The posterior predictive mean is a version of the conditional expectation of `μ(θ)` given
the first `n` rewards. -/
theorem fseq_ae_eq_condExp (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ)
    [IsMarkovKernel Pk] (u : Y → ℝ → Y) (hu : Measurable (Function.uncurry u))
    (hc : ∀ (z : Y) (A : Set ℝ) (B : Set Θ), MeasurableSet A → MeasurableSet B →
      ∫⁻ θ in B, κ θ A ∂(Pk z) = ∫⁻ r in A, Pk (u z r) B ∂(κ ∘ₘ Pk z))
    (z : Y) (hint : Integrable (fun r : ℝ => r) (κ ∘ₘ Pk z)) (n : ℕ) :
    (fun x : Θ × (ℕ → ℝ) => fseq κ Pk u z n x.2) =ᵐ[nu κ Pk z]
      (nu κ Pk z)[fun x => muK κ x.1 | filt n] := by
  set ν := nu κ Pk z
  have hgi := integrable_g κ Pk z hint
  have hmK := measurable_muK κ
  -- finiteness of the posterior absolute moment
  set Nrm : Θ → ℝ≥0∞ := fun θ => ENNReal.ofReal ‖muK κ θ‖ with hNrm
  have hNm : Measurable Nrm := (hmK.norm).ennreal_ofReal
  have hpostN : Measurable (fun r : ℕ → ℝ => ∫⁻ θ, Nrm θ ∂Pk (ys u z n r)) :=
    measurable_post Pk (ys u z n) (measurable_ys u hu z n) (G := fun p => Nrm p.1)
      (hNm.comp measurable_fst)
  have hfinN : ∫⁻ x, ∫⁻ θ, Nrm θ ∂Pk (ys u z n x.2) ∂ν ≠ ∞ := by
    have h := setLIntegral_post κ Pk u hu hc z n Set.univ MeasurableSet.univ
      (fun _ _ _ => Iff.rfl) hNm
    simp only [Set.preimage_univ, Measure.restrict_univ] at h
    rw [← h]
    have := hgi.2
    rw [HasFiniteIntegral] at this
    simp_rw [hNrm, ofReal_norm_eq_enorm]
    exact this.ne
  have haeN : ∀ᵐ x ∂ν, ∫⁻ θ, Nrm θ ∂Pk (ys u z n x.2) < ∞ :=
    ae_lt_top (hpostN.comp measurable_snd) hfinN
  have haeI : ∀ᵐ x ∂ν, Integrable (muK κ) (Pk (ys u z n x.2)) := by
    filter_upwards [haeN] with x hx
    refine ⟨hmK.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simpa [hNrm, Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using hx
  -- measurability and integrability of the candidate
  have hfm : Measurable[filt n] (fun x : Θ × (ℕ → ℝ) => fseq κ Pk u z n x.2) :=
    measurable_filt n (measurable_fseq κ Pk u hu z n)
      (fun r r' h => by simp only [fseq]; rw [ys_congr u z n h])
  have hfm0 : Measurable (fun x : Θ × (ℕ → ℝ) => fseq κ Pk u z n x.2) :=
    (measurable_fseq κ Pk u hu z n).comp measurable_snd
  have hfi : Integrable (fun x : Θ × (ℕ → ℝ) => fseq κ Pk u z n x.2) ν := by
    have hb := integrable_toReal_of_lintegral_ne_top
      (hpostN.comp measurable_snd).aemeasurable hfinN
    refine hb.mono' hfm0.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    exact norm_integral_le_lintegral_norm _
  refine ae_eq_condExp_of_forall_setIntegral_eq (filt.le n) hgi
    (fun s _ _ => hfi.integrableOn) ?_ hfm.stronglyMeasurable.aestronglyMeasurable
  intro s hs _
  obtain ⟨A', hA', hdep, rfl⟩ := filt_set n hs
  set S : Set (Θ × (ℕ → ℝ)) := Prod.snd ⁻¹' A'
  set mp : Θ → ℝ≥0∞ := fun θ => ENNReal.ofReal (muK κ θ) with hmp
  set mn : Θ → ℝ≥0∞ := fun θ => ENNReal.ofReal (-muK κ θ) with hmn
  have hmpm : Measurable mp := hmK.ennreal_ofReal
  have hmnm : Measurable mn := hmK.neg.ennreal_ofReal
  have hPp : Measurable (fun r : ℕ → ℝ => ∫⁻ θ, mp θ ∂Pk (ys u z n r)) :=
    measurable_post Pk (ys u z n) (measurable_ys u hu z n) (G := fun p => mp p.1)
      (hmpm.comp measurable_fst)
  have hPn : Measurable (fun r : ℕ → ℝ => ∫⁻ θ, mn θ ∂Pk (ys u z n r)) :=
    measurable_post Pk (ys u z n) (measurable_ys u hu z n) (G := fun p => mn p.1)
      (hmnm.comp measurable_fst)
  have hle_p : ∀ r, ∫⁻ θ, mp θ ∂Pk (ys u z n r) ≤ ∫⁻ θ, Nrm θ ∂Pk (ys u z n r) :=
    fun r => lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
      (Real.norm_eq_abs _).ge)
  have hle_n : ∀ r, ∫⁻ θ, mn θ ∂Pk (ys u z n r) ≤ ∫⁻ θ, Nrm θ ∂Pk (ys u z n r) :=
    fun r => lintegral_mono fun θ => ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans
      (Real.norm_eq_abs _).ge)
  have hfinP : ∫⁻ x, ∫⁻ θ, mp θ ∂Pk (ys u z n x.2) ∂ν ≠ ∞ :=
    ne_top_of_le_ne_top hfinN (lintegral_mono fun x => hle_p x.2)
  have hfinM : ∫⁻ x, ∫⁻ θ, mn θ ∂Pk (ys u z n x.2) ∂ν ≠ ∞ :=
    ne_top_of_le_ne_top hfinN (lintegral_mono fun x => hle_n x.2)
  have hIp : Integrable (fun x : Θ × (ℕ → ℝ) => (∫⁻ θ, mp θ ∂Pk (ys u z n x.2)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top (hPp.comp measurable_snd).aemeasurable hfinP
  have hIn : Integrable (fun x : Θ × (ℕ → ℝ) => (∫⁻ θ, mn θ ∂Pk (ys u z n x.2)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top (hPn.comp measurable_snd).aemeasurable hfinM
  -- the candidate as a difference of two nonnegative parts
  have hsplit : (fun x : Θ × (ℕ → ℝ) => fseq κ Pk u z n x.2) =ᵐ[ν]
      fun x => (∫⁻ θ, mp θ ∂Pk (ys u z n x.2)).toReal - (∫⁻ θ, mn θ ∂Pk (ys u z n x.2)).toReal := by
    filter_upwards [haeI] with x hx
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hx
  have hpf : ∀ᵐ x ∂ν, ∫⁻ θ, mp θ ∂Pk (ys u z n x.2) < ∞ := by
    filter_upwards [haeN] with x hx using lt_of_le_of_lt (hle_p x.2) hx
  have hnf : ∀ᵐ x ∂ν, ∫⁻ θ, mn θ ∂Pk (ys u z n x.2) < ∞ := by
    filter_upwards [haeN] with x hx using lt_of_le_of_lt (hle_n x.2) hx
  rw [setIntegral_congr_ae (measurable_snd hA') (hsplit.mono fun x hx _ => hx),
    integral_sub hIp.integrableOn hIn.integrableOn,
    integral_toReal (f := fun x : Θ × (ℕ → ℝ) => ∫⁻ θ, mp θ ∂Pk (ys u z n x.2))
      (hPp.comp measurable_snd).aemeasurable.restrict (ae_restrict_of_ae hpf),
    integral_toReal (f := fun x : Θ × (ℕ → ℝ) => ∫⁻ θ, mn θ ∂Pk (ys u z n x.2))
      (hPn.comp measurable_snd).aemeasurable.restrict (ae_restrict_of_ae hnf),
    ← setLIntegral_post κ Pk u hu hc z n A' hA' hdep hmpm,
    ← setLIntegral_post κ Pk u hu hc z n A' hA' hdep hmnm,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi.integrableOn]

end IRS5

namespace IRS5

open IRS3

variable {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

lemma avg_congr (n : ℕ) {r r' : ℕ → ℝ} (h : ∀ i < n, r i = r' i) : avg n r = avg n r' := by
  unfold avg
  rw [Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.1 hi)]

/-- Lévy's upward theorem applied to the posterior predictive means. -/
theorem fseq_tendsto (κ : Kernel Θ ℝ) [IsMarkovKernel κ] (Pk : Kernel Y Θ)
    [IsMarkovKernel Pk] (u : Y → ℝ → Y) (hu : Measurable (Function.uncurry u))
    (hc : ∀ (z : Y) (A : Set ℝ) (B : Set Θ), MeasurableSet A → MeasurableSet B →
      ∫⁻ θ in B, κ θ A ∂(Pk z) = ∫⁻ r in A, Pk (u z r) B ∂(κ ∘ₘ Pk z))
    (z : Y) (hint : Integrable (fun r : ℝ => r) (κ ∘ₘ Pk z)) :
    ∀ᵐ x ∂(nu κ Pk z), Tendsto (fun n => fseq κ Pk u z n x.2) atTop (𝓝 (muK κ x.1)) := by
  set ν := nu κ Pk z
  set g : Θ × (ℕ → ℝ) → ℝ := fun x => muK κ x.1 with hg
  set g' : Θ × (ℕ → ℝ) → ℝ := fun x => limsup (fun n => avg n x.2) atTop with hg'
  have hmeas : ∀ n, Measurable[⨆ n, (filt (Θ := Θ) n : MeasurableSpace (Θ × (ℕ → ℝ)))]
      (fun x : Θ × (ℕ → ℝ) => avg n x.2) := fun n =>
    (measurable_filt n (measurable_avg n) (fun r r' h => avg_congr n h)).mono
      (le_iSup (fun n => (filt (Θ := Θ) n : MeasurableSpace (Θ × (ℕ → ℝ)))) n) le_rfl
  have hg'm : StronglyMeasurable[⨆ n, (filt (Θ := Θ) n : MeasurableSpace (Θ × (ℕ → ℝ)))] g' := by
    have : Measurable[⨆ n, (filt (Θ := Θ) n : MeasurableSpace (Θ × (ℕ → ℝ)))] g' := by
      let _ : MeasurableSpace (Θ × (ℕ → ℝ)) :=
        ⨆ n, (filt (Θ := Θ) n : MeasurableSpace (Θ × (ℕ → ℝ)))
      exact Measurable.limsup hmeas
    exact this.stronglyMeasurable
  have hslln := slln_nu κ Pk z hint
  have hgg' : g =ᵐ[ν] g' := by
    filter_upwards [hslln] with x hx
    exact hx.limsup_eq.symm
  have hgi := integrable_g κ Pk z hint
  have hg'i : Integrable g' ν := hgi.congr hgg'
  have hlevy := hg'i.tendsto_ae_condExp (ℱ := filt) hg'm
  have hce : ∀ n, ν[g' | filt n] =ᵐ[ν] fun x => fseq κ Pk u z n x.2 := fun n =>
    (condExp_congr_ae hgg'.symm).trans (fseq_ae_eq_condExp κ Pk u hu hc z hint n).symm
  filter_upwards [hlevy, hgg', ae_all_iff.2 hce] with x h1 h2 h3
  have e : muK κ x.1 = g' x := h2
  rw [e]
  exact h1.congr fun n => h3 n

end IRS5

lemma IRS5.yseq_eq {K : ℕ} {Θ Y : Type*} (U : Fin K → Y → ℝ → Y) (y : Fin K → Y) (a : Fin K)
    (ω : Outcome K Θ) (n : ℕ) : yseq U y a ω n = IRS5.ys (U a) (y a) n (ω a).2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [yseq, IRS5.ys, ih]

open IRS3 IRS5 in
theorem solution {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (hconj : IsConjugate R P U) (y : Fin K → Y) (a : Fin K)
    (hint : Integrable (fun r : ℝ => r) ((R a) ∘ₘ (P a (y a)))) :
    ∀ᵐ ω ∂(I R P y),
      Tendsto (fun n => muHat R P U y a n ω) atTop (𝓝 (Monotone.mu R a (ω a).1)) ∧
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, (ω a).2 i) / (n : ℝ)) atTop
        (𝓝 (Monotone.mu R a (ω a).1)) := by
  have hc : ∀ (z : Y) (A : Set ℝ) (B : Set Θ), MeasurableSet A → MeasurableSet B →
      ∫⁻ θ in B, R a θ A ∂(P a z) = ∫⁻ r in A, P a (U a z r) B ∂(R a ∘ₘ P a z) :=
    fun z A B hA hB => hconj a z A B hA hB
  have harm : ∀ᵐ x ∂(nu (R a) (P a) (y a)),
      Tendsto (fun n => fseq (R a) (P a) (U a) (y a) n x.2) atTop (𝓝 (muK (R a) x.1)) ∧
      Tendsto (fun n => avg n x.2) atTop (𝓝 (∫ r, r ∂(R a) x.1)) :=
    (fseq_tendsto (R a) (P a) (U a) (hU a) hc (y a) hint).and (slln_nu (R a) (P a) (y a) hint)
  haveI : ∀ b, IsProbabilityMeasure (armK (R b) ∘ₘ P b (y b)) := fun b => inferInstance
  have hmp := measurePreserving_eval (μ := fun b => armK (R b) ∘ₘ P b (y b)) a
  have hpi : ∀ᵐ ω ∂(Measure.pi fun b => armK (R b) ∘ₘ P b (y b)),
      Tendsto (fun n => fseq (R a) (P a) (U a) (y a) n (ω a).2) atTop
        (𝓝 (muK (R a) (ω a).1)) ∧
      Tendsto (fun n => avg n (ω a).2) atTop (𝓝 (∫ r, r ∂(R a) (ω a).1)) := by
    have h0 : ∀ᵐ x ∂((Measure.pi fun b => armK (R b) ∘ₘ P b (y b)).map (Function.eval a)),
        Tendsto (fun n => fseq (R a) (P a) (U a) (y a) n x.2) atTop (𝓝 (muK (R a) x.1)) ∧
        Tendsto (fun n => avg n x.2) atTop (𝓝 (∫ r, r ∂(R a) x.1)) := by
      rw [hmp.map_eq]; exact harm
    exact ae_of_ae_map (measurable_pi_apply a).aemeasurable h0
  rw [I_eq]
  filter_upwards [hpi] with ω hω
  have e : ∀ n, muHat R P U y a n ω = fseq (R a) (P a) (U a) (y a) n (ω a).2 := fun n => by
    simp only [muHat, Monotone.muBar, fseq, muK, IRS5.yseq_eq]
    rfl
  refine ⟨?_, hω.2⟩
  simp_rw [e]
  exact hω.1
