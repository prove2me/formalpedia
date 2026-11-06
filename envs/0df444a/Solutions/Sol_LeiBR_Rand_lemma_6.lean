-- Prove2me | solution 1 for LeiBR.Rand.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:37:10.807238+00:00
-- url     : https://prove2.me/submissions/7014100a-99f0-4d7d-b787-2fc77bdecea6

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1
import Definitions.Def_LeiBR_Rand_SA
import Definitions.Def_LeiBR_Rand_Algorithm2
import Definitions.Def_LeiBR_Rand_Constants
open MeasureTheory ProbabilityTheory

namespace LeiBR2AuxL6

lemma mid_strong {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {X : Set E}
    (hX : Convex ℝ X) {g : E → ℝ} (hg : ConvexOn ℝ X g) {mu : ℝ} (hmu : 0 ≤ mu) {c u z : E}
    (hu : u ∈ X) (hz : z ∈ X)
    (hmin : IsMinOn (fun y => g y + mu / 2 * ‖y - c‖ ^ 2) X u) :
    mu / 4 * ‖z - u‖ ^ 2 ≤ (g z + mu / 2 * ‖z - c‖ ^ 2) - (g u + mu / 2 * ‖u - c‖ ^ 2) := by
  set m : E := (1/2 : ℝ) • u + (1/2 : ℝ) • z with hm
  have hmX : m ∈ X := hX hu hz (by norm_num) (by norm_num) (by norm_num)
  have hgm : g m ≤ (1/2 : ℝ) • g u + (1/2 : ℝ) • g z :=
    hg.2 hu hz (by norm_num) (by norm_num) (by norm_num)
  have hmin' := hmin hmX
  simp only [Set.mem_ofPred_eq] at hmin'
  have hpar := parallelogram_law_with_norm ℝ (u - c) (z - c)
  have h1 : u - c + (z - c) = (2:ℝ) • (m - c) := by
    rw [hm]; module
  have h2 : u - c - (z - c) = -(z - u) := by abel
  rw [h1, h2, norm_neg, norm_smul] at hpar
  simp only [smul_eq_mul] at hgm
  have : ‖(2:ℝ)‖ = 2 := by norm_num
  rw [this] at hpar
  nlinarith [sq_nonneg ‖z - u‖]

lemma proj_lip {m : ℕ} {X : Set (EuclideanSpace ℝ (Fin m))} (hX : Convex ℝ X)
    {Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hP : SpectralProjGrad.Shared.IsProjOnto X Pr) : LipschitzWith 2 Pr := by
  have key : ∀ z y, y ∈ X → (2:ℝ) / 4 * ‖y - Pr z‖ ^ 2 ≤
      (0 + 2 / 2 * ‖y - z‖ ^ 2) - (0 + 2 / 2 * ‖Pr z - z‖ ^ 2) := by
    intro z y hy
    refine mid_strong (g := fun _ => (0:ℝ)) hX (convexOn_const 0 hX) (by norm_num) (hP z).1 hy ?_
    intro w hw
    simp only [Set.mem_ofPred_eq]
    have := (hP z).2 w hw
    rw [norm_sub_rev z, norm_sub_rev z] at this
    have h0 : 0 ≤ ‖Pr z - z‖ := norm_nonneg _
    nlinarith
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  have k1 := key z (Pr z') (hP z').1
  have k2 := key z' (Pr z) (hP z).1
  rw [dist_eq_norm, dist_eq_norm]
  have hid : ‖Pr z' - z‖^2 - ‖Pr z - z‖^2 + ‖Pr z - z'‖^2 - ‖Pr z' - z'‖^2
      = 2 * inner ℝ (Pr z - Pr z') (z - z') := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, real_inner_comm]; ring
  have hcs := real_inner_le_norm (Pr z - Pr z') (z - z')
  rw [norm_sub_rev (Pr z') (Pr z)] at k1
  have hsq : ‖Pr z - Pr z'‖ ^ 2 ≤ 2 * ‖Pr z - Pr z'‖ * ‖z - z'‖ := by nlinarith
  push_cast
  rcases (norm_nonneg (Pr z - Pr z')).eq_or_lt with h | h
  · rw [← h]; positivity
  · nlinarith


open LeiBR.Rand in
lemma feas_update {N : ℕ} {n : Fin N → ℕ} (G : Game N n) {y : LeiBR.Sync.Profile n}
    (hy : G.Feasible y) (i : Fin N) {z : LeiBR.Sync.Strat n i} (hz : z ∈ G.X i) :
    G.Feasible (Function.update y i z) := by
  intro j
  by_cases h : j = i
  · subst h; simpa using hz
  · rw [Function.update_of_ne h]; exact hy j

open LeiBR.Rand in
lemma xhat_contOn {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    {μξ : Measure (EuclideanSpace ℝ (Fin d))}
    {ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ}
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i} {M : Fin N → ℝ}
    (hA1 : Assumption1 G μξ ψ gψ M) {mu : ℝ} (hmu : 0 < mu)
    {xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n} (hxhat : IsProxBR G mu xhat) (i : Fin N) :
    ContinuousOn (fun y => xhat y i) {y | G.Feasible y} := by
  set S : Set (LeiBR.Sync.Profile n) := {y | G.Feasible y} with hSdef
  have hS : S = Set.univ.pi G.X := by
    ext y; simp [hSdef, Game.Feasible]
  have hSc : IsCompact S := hS ▸ isCompact_univ_pi hA1.compact
  obtain ⟨U, -, hSU, hsm⟩ := hA1.smooth
  have hfc : ContinuousOn (G.f i) S := ((hsm i).continuousOn).mono hSU
  let h : LeiBR.Sync.Profile n × LeiBR.Sync.Strat n i → ℝ :=
    fun p => G.f i (Function.update p.1 i p.2) + mu / 2 * ‖p.2 - p.1 i‖ ^ 2
  have hK : IsCompact (S ×ˢ G.X i) := hSc.prod (hA1.compact i)
  have hcont : ContinuousOn h (S ×ˢ G.X i) := by
    refine ContinuousOn.add ?_ (Continuous.continuousOn (by fun_prop))
    refine hfc.comp (Continuous.update continuous_fst i continuous_snd).continuousOn ?_
    intro p hp
    exact feas_update G hp.1 i hp.2
  have huc := (Metric.uniformContinuousOn_iff).1 (hK.uniformContinuousOn_of_continuous hcont)
  refine Metric.continuousOn_iff.2 fun y hy ε hε => ?_
  obtain ⟨δ, hδ, hδh⟩ := huc (mu * ε ^ 2 / 4) (by positivity)
  refine ⟨δ, hδ, fun y' hy' hd => ?_⟩
  have hu := (hxhat y hy i).1
  have hu' := (hxhat y' hy' i).1
  have hcv : ∀ y0, y0 ∈ S → ConvexOn ℝ (G.X i) (fun z => G.f i (Function.update y0 i z)) := by
    intro y0 hy0
    obtain ⟨V, -, hXV, hc⟩ := hA1.convexOn i y0 hy0
    exact hc.subset hXV (hA1.convex i)
  have sc1 := mid_strong (hA1.convex i) (hcv y hy) hmu.le hu hu' (hxhat y hy i).2
  have sc2 := mid_strong (hA1.convex i) (hcv y' hy') hmu.le hu' hu (hxhat y' hy' i).2
  have d1 := hδh (y, xhat y' i) ⟨hy, hu'⟩ (y', xhat y' i) ⟨hy', hu'⟩
    (by rw [Prod.dist_eq]; simp; rw [dist_comm]; exact hd)
  have d2 := hδh (y', xhat y i) ⟨hy', hu⟩ (y, xhat y i) ⟨hy, hu⟩
    (by rw [Prod.dist_eq]; simp; exact hd)
  simp only [h, Real.dist_eq] at d1 d2
  rw [abs_lt] at d1 d2
  rw [dist_eq_norm]
  rw [norm_sub_rev (xhat y i) (xhat y' i)] at sc2
  have hsq : ‖xhat y' i - xhat y i‖ ^ 2 < ε ^ 2 := by
    have : mu * ‖xhat y' i - xhat y i‖ ^ 2 < mu * ε ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_left this hmu.le
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq


open LeiBR.Rand in
lemma saIter_mem {m : ℕ} {X : Set (EuclideanSpace ℝ (Fin m))}
    {Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)} (hP : ∀ z, Pr z ∈ X)
    (dir : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (mu : ℝ)
    {z1 : EuclideanSpace ℝ (Fin m)} (hz1 : z1 ∈ X) : ∀ t, saIter Pr dir mu z1 t ∈ X
  | 0 => hz1
  | 1 => hz1
  | (_ + 2) => hP _


section
open LeiBR.Rand
variable {N : ℕ} {n : Fin N → ℕ}

lemma cdAt {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : LeiBR.Sync.Profile n} (hx : x ∈ U) : ContDiffAt ℝ 2 f x :=
  hf.contDiffAt (hU.mem_nhds hx)

lemma hasD1 {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : LeiBR.Sync.Profile n} (hx : x ∈ U) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((cdAt hU hf hx).differentiableAt (by norm_num)).hasFDerivAt

lemma hasD2 {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : LeiBR.Sync.Profile n} (hx : x ∈ U) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
  (((cdAt hU hf hx).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt

lemma symmD2 {f : LeiBR.Sync.Profile n → ℝ} {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : LeiBR.Sync.Profile n} (hx : x ∈ U) (v w : LeiBR.Sync.Profile n) :
    fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v :=
  (cdAt hU hf hx).isSymmSndFDerivAt (by simp) v w

lemma hess_eq (g : LeiBR.Sync.Profile n → ℝ) (x : LeiBR.Sync.Profile n) (i j : Fin N)
    (u : LeiBR.Sync.Strat n i) (v : LeiBR.Sync.Strat n j) :
    hessBlock g x i j u v = fderiv ℝ (fderiv ℝ g) x (Pi.single i u) (Pi.single j v) := by
  simp [hessBlock, blockEmb]

lemma path_deriv (x : LeiBR.Sync.Profile n) (i : Fin N) (a v : LeiBR.Sync.Strat n i) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Function.update x i (a + s • v)) (Pi.single i v) s := by
  have h1 : HasDerivAt (fun s : ℝ => a + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add a
  have h2 := (hasFDerivAt_update (𝕜 := ℝ) x (a + s • v)).comp_hasDerivAt s h1
  have e : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (LeiBR.Sync.Strat n i)))) v
      = Pi.single i v := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e] at h2
  exact h2


lemma pi_single_apply (i : Fin N) (v : LeiBR.Sync.Strat n i) :
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (LeiBR.Sync.Strat n i)))) v
      = (Pi.single i v : LeiBR.Sync.Profile n) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma foc {d : ℕ} (G : Game N n) {μξ : Measure (EuclideanSpace ℝ (Fin d))}
    {ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ}
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i} {M : Fin N → ℝ}
    (hA1 : Assumption1 G μξ ψ gψ M) {mu : ℝ}
    {xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n} (hxhat : IsProxBR G mu xhat)
    {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U) (hSU : {x | G.Feasible x} ⊆ U) (i : Fin N)
    (hf : ContDiffOn ℝ 2 (G.f i) U)
    (y : LeiBR.Sync.Profile n) (hy : G.Feasible y) (z : LeiBR.Sync.Strat n i) (hz : z ∈ G.X i) :
    0 ≤ fderiv ℝ (G.f i) (Function.update y i (xhat y i)) (Pi.single i (z - xhat y i)) +
      mu * inner ℝ (xhat y i - y i) (z - xhat y i) := by
  have hu := (hxhat y hy i).1
  have hP : Function.update y i (xhat y i) ∈ U := by
    apply hSU
    intro j
    by_cases h : j = i
    · subst h; simpa using hu
    · rw [Function.update_of_ne h]; exact hy j
  have h1 := (hasD1 hU hf hP).comp (xhat y i) (hasFDerivAt_update (𝕜 := ℝ) y (xhat y i))
  have h2 := (((hasFDerivAt_id (𝕜 := ℝ) (xhat y i)).sub_const (y i)).norm_sq).const_mul (mu / 2)
  have h := h1.add h2
  have hmin := (hxhat y hy i).2.localize
  have hseg : segment ℝ (xhat y i) (xhat y i + (z - xhat y i)) ⊆ G.X i := by
    rw [add_sub_cancel]; exact (hA1.convex i).segment_subset hu hz
  have := hmin.hasFDerivWithinAt_nonneg h.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset hseg)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, pi_single_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at this
  convert this using 2
  simp only [id]
  ring


end


lemma proj_toward {m : ℕ} {X : Set (EuclideanSpace ℝ (Fin m))} (hX : Convex ℝ X)
    {Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hP : SpectralProjGrad.Shared.IsProjOnto X Pr) (w x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ X) :
    ‖Pr w - x‖ ≤ ‖w - x‖ := by
  have hu := (hP w).1
  have hinf : ‖w - Pr w‖ = ⨅ v : X, ‖w - (v : EuclideanSpace ℝ (Fin m))‖ := by
    haveI : Nonempty X := ⟨⟨_, hu⟩⟩
    refine le_antisymm (le_ciInf fun v => (hP w).2 v v.2) ?_
    have hbdd : BddBelow (Set.range fun v : X => ‖w - (v : EuclideanSpace ℝ (Fin m))‖) := by
      refine ⟨0, ?_⟩
      rintro r ⟨v, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbdd (⟨Pr w, hu⟩ : X)
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hX hu).1 hinf x hx
  have hexp : ‖w - x‖ ^ 2 = ‖w - Pr w‖ ^ 2 + ‖Pr w - x‖ ^ 2 - 2 * inner ℝ (w - Pr w) (x - Pr w) := by
    have : w - x = (w - Pr w) + (Pr w - x) := by abel
    rw [this, norm_add_sq_real]
    have : inner ℝ (w - Pr w) (Pr w - x) = - inner ℝ (w - Pr w) (x - Pr w) := by
      rw [← inner_neg_right, neg_sub]
    rw [this]; ring
  have h1 : ‖Pr w - x‖ ^ 2 ≤ ‖w - x‖ ^ 2 := by nlinarith [sq_nonneg ‖w - Pr w‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

lemma freeze {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {β E : Type*} [MeasurableSpace β] [MeasurableSpace E] (μξ : Measure E) [IsProbabilityMeasure μξ]
    (W : Ω → β) (ξ : Ω → E) (hW : Measurable W) (hξ : Measurable ξ) (hind : IndepFun W ξ P)
    (hlaw : P.map ξ = μξ) (h : β × E → ℝ) (hh : Measurable h) (B : Set β) (hB : MeasurableSet B)
    (hWB : ∀ ω, W ω ∈ B) (C : ℝ) (hint : ∀ w ∈ B, Integrable (fun s => h (w, s)) μξ)
    (hbd : ∀ w ∈ B, ∫ s, ‖h (w, s)‖ ∂μξ ≤ C) :
    Integrable (fun ω => h (W ω, ξ ω)) P ∧
      ∫ ω, h (W ω, ξ ω) ∂P = ∫ ω, (∫ s, h (W ω, s) ∂μξ) ∂P ∧
      Integrable (fun ω => ∫ s, h (W ω, s) ∂μξ) P := by
  have hmap : P.map (fun ω => (W ω, ξ ω)) = (P.map W).prod μξ := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hξ.aemeasurable).1 hind, hlaw]
  haveI : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hae : ∀ᵐ w ∂(P.map W), w ∈ B := (ae_map_iff hW.aemeasurable hB).2 (ae_of_all _ hWB)
  have hsm : StronglyMeasurable fun w => ∫ s, ‖h (w, s)‖ ∂μξ :=
    StronglyMeasurable.integral_prod_right (f := fun w s => ‖h (w, s)‖) hh.norm.stronglyMeasurable
  have hI : Integrable h ((P.map W).prod μξ) := by
    rw [integrable_prod_iff hh.aestronglyMeasurable]
    refine ⟨hae.mono fun w hw => hint w hw, ?_⟩
    refine Integrable.of_bound hsm.aestronglyMeasurable C (hae.mono fun w hw => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact hbd w hw
  have hpm : Measurable fun ω => (W ω, ξ ω) := hW.prodMk hξ
  have hI' : Integrable h (P.map fun ω => (W ω, ξ ω)) := by rw [hmap]; exact hI
  have hsm2 : StronglyMeasurable fun w => ∫ s, h (w, s) ∂μξ :=
    StronglyMeasurable.integral_prod_right (f := fun w s => h (w, s)) hh.stronglyMeasurable
  refine ⟨(integrable_map_measure hh.aestronglyMeasurable hpm.aemeasurable).1 hI', ?_, ?_⟩
  swap
  · refine Integrable.of_bound (hsm2.comp_measurable hW).aestronglyMeasurable C (ae_of_all _ fun ω => ?_)
    exact (norm_integral_le_integral_norm _).trans (hbd _ (hWB ω))
  calc ∫ ω, h (W ω, ξ ω) ∂P = ∫ q, h q ∂(P.map fun ω => (W ω, ξ ω)) :=
        (integral_map hpm.aemeasurable hh.aestronglyMeasurable).symm
    _ = ∫ q, h q ∂((P.map W).prod μξ) := by rw [hmap]
    _ = ∫ w, ∫ s, h (w, s) ∂μξ ∂(P.map W) := integral_prod h hI
    _ = ∫ ω, (∫ s, h (W ω, s) ∂μξ) ∂P := integral_map hW.aemeasurable hsm2.aestronglyMeasurable


lemma indep_past {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (k : ℕ) {E : Type*} [MeasurableSpace E] (s : ℕ → Ω → E)
    (hs : ∀ t, Measurable (s t)) (hiid : iIndepFun (fun t => s (t + 1)) P)
    (hind : Indep (⨆ t, MeasurableSpace.comap (s (t + 1)) inferInstance) (F k) P) (m : ℕ) :
    Indep (MeasurableSpace.comap (s (m + 1)) inferInstance)
      (F k ⊔ ⨆ l ∈ Set.Iio m, MeasurableSpace.comap (s (l + 1)) inferInstance) P := by
  set ℋ := ⨆ l ∈ Set.Iio m, MeasurableSpace.comap (s (l + 1)) inferInstance with hℋ
  set 𝒞 := MeasurableSpace.comap (s (m + 1)) inferInstance with h𝒞
  have hiid' := (iIndepFun_iff_iIndep _ _ _).1 hiid
  have hle : ∀ l, MeasurableSpace.comap (s (l + 1)) inferInstance ≤ mΩ := fun l => (hs (l + 1)).comap_le
  have hdisj : Disjoint (Set.Iio m) ({m} : Set ℕ) := by
    rw [Set.disjoint_singleton_right]; simp
  have hHC : Indep ℋ 𝒞 P := by
    have := indep_iSup_of_disjoint hle hiid' hdisj
    simpa [hℋ, h𝒞] using this
  have hℋle : ℋ ≤ ⨆ t, MeasurableSpace.comap (s (t + 1)) inferInstance :=
    iSup₂_le fun l _ => le_iSup (fun t => MeasurableSpace.comap (s (t + 1)) inferInstance) l
  have h𝒞le : 𝒞 ≤ ⨆ t, MeasurableSpace.comap (s (t + 1)) inferInstance :=
    le_iSup (fun t => MeasurableSpace.comap (s (t + 1)) inferInstance) m
  set p2 : Set (Set Ω) := {S | ∃ A B, MeasurableSet[F k] A ∧ MeasurableSet[ℋ] B ∧ S = A ∩ B} with hp2
  have hp2pi : IsPiSystem p2 := by
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ -
    exact ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', by ext; simp; tauto⟩
  have hgen : F k ⊔ ℋ = MeasurableSpace.generateFrom p2 := by
    refine le_antisymm (sup_le ?_ ?_) ?_
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom ⟨A, Set.univ, hA, MeasurableSet.univ, by simp⟩
    · intro B hB
      exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, B, MeasurableSet.univ, hB, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨A, B, hA, hB, rfl⟩
      exact (le_sup_left (a := F k) (b := ℋ) _ hA).inter (le_sup_right (a := F k) (b := ℋ) _ hB)
  refine IndepSets.indep (hs (m + 1)).comap_le (sup_le (F.le k) (iSup₂_le fun l _ => hle l))
    (@MeasurableSpace.isPiSystem_measurableSet Ω 𝒞) hp2pi
    (MeasurableSpace.generateFrom_measurableSet).symm hgen ?_
  rw [IndepSets_iff]
  rintro C _ hC ⟨A, B, hA, hB, rfl⟩
  have e1 : P (C ∩ (A ∩ B)) = P ((B ∩ C) ∩ A) := by congr 1; ext; simp; tauto
  have h1 := (Indep_iff _ _ _).1 hind (B ∩ C) A ((hℋle _ hB).inter (h𝒞le _ hC)) hA
  have h2 := (Indep_iff _ _ _).1 hHC B C hB hC
  have h3 := (Indep_iff _ _ _).1 hind B A (hℋle _ hB) hA
  have e2 : P (A ∩ B) = P (B ∩ A) := by rw [Set.inter_comm]
  rw [e1, h1, h2, e2, h3]
  ring


section grad
open LeiBR.Rand
variable {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n) {μξ : Measure (EuclideanSpace ℝ (Fin d))}
    {ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ}
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i} {M : Fin N → ℝ}
    (hA1 : Assumption1 G μξ ψ gψ M)
    {U : Set (LeiBR.Sync.Profile n)} (hU : IsOpen U) (hSU : {x | G.Feasible x} ⊆ U) (i : Fin N)
    (hf : ContDiffOn ℝ 2 (G.f i) U)
include hA1 hU hSU hf

lemma grad_inner (y : LeiBR.Sync.Profile n) (hy : G.Feasible y) (z : LeiBR.Sync.Strat n i)
    (hz : z ∈ G.X i) (v : LeiBR.Sync.Strat n i) :
    inner ℝ (∫ s, gψ i (Function.update y i z) s ∂μξ) v =
      fderiv ℝ (G.f i) (Function.update y i z) (Pi.single i v) := by
  have hyz := feas_update G hy i hz
  have hu := (hA1.unbiased i (Function.update y i z) hyz).2
  simp only [Function.update_idem, Function.update_self] at hu
  rw [← hu]
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]
  have h1 : HasFDerivAt (fun z' => G.f i (Function.update y i z')) _ z :=
    (hasD1 hU hf (hSU hyz)).comp z (hasFDerivAt_update (𝕜 := ℝ) y z)
  rw [h1.fderiv]
  simp only [ContinuousLinearMap.comp_apply, pi_single_apply]

lemma grad_mono (y : LeiBR.Sync.Profile n) (hy : G.Feasible y) (a z : LeiBR.Sync.Strat n i)
    (ha : a ∈ G.X i) (hz : z ∈ G.X i) :
    fderiv ℝ (G.f i) (Function.update y i a) (Pi.single i (z - a)) ≤
      fderiv ℝ (G.f i) (Function.update y i z) (Pi.single i (z - a)) := by
  obtain ⟨V, -, hXV, hcv⟩ := hA1.convexOn i y hy
  have hcX := hcv.subset hXV (hA1.convex i)
  set γ : ℝ → LeiBR.Sync.Strat n i := fun s => a + s • (z - a) with hγ
  have hγX : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ G.X i := fun s hs =>
    (hA1.convex i).add_smul_sub_mem ha hz hs
  set k : ℝ → ℝ := fun s => G.f i (Function.update y i (γ s)) with hk
  have hkconv : ConvexOn ℝ (Set.Icc 0 1) k := by
    refine ⟨convex_Icc _ _, fun s hs t ht p q hp hq hpq => ?_⟩
    have hγlin : γ (p • s + q • t) = p • γ s + q • γ t := by
      simp only [hγ, smul_eq_mul]
      rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hpq, one_smul,
        add_smul]
    have := hcX.2 (hγX s hs) (hγX t ht) hp hq hpq
    simp only [hk, smul_eq_mul] at this ⊢
    rw [show p * s + q * t = p • s + q • t by simp, hγlin]
    exact this
  have hkd : ∀ s ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt k (fderiv ℝ (G.f i) (Function.update y i (γ s)) (Pi.single i (z - a))) s := by
    intro s hs
    exact (hasD1 hU hf (hSU (feas_update G hy i (hγX s hs)))).comp_hasDerivAt s
      (path_deriv y i a (z - a) s)
  have hmono := hkconv.monotoneOn_deriv fun s hs => (hkd s hs).differentiableAt
  have h01 := hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  rw [(hkd 0 (Set.left_mem_Icc.2 zero_le_one)).deriv, (hkd 1 (Set.right_mem_Icc.2 zero_le_one)).deriv] at h01
  simpa [hγ] using h01

lemma strong_ineq {mu : ℝ} {xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n}
    (hxhat : IsProxBR G mu xhat) (y : LeiBR.Sync.Profile n) (hy : G.Feasible y)
    (z : LeiBR.Sync.Strat n i) (hz : z ∈ G.X i) :
    mu * ‖z - xhat y i‖ ^ 2 ≤
      inner ℝ (∫ s, gψ i (Function.update y i z) s ∂μξ + mu • (z - y i)) (z - xhat y i) := by
  have hxh := (hxhat y hy i).1
  have h1 := foc G hA1 hxhat hU hSU i hf y hy z hz
  have h2 := grad_mono G hA1 hU hSU i hf y hy (xhat y i) z hxh hz
  rw [inner_add_left, grad_inner G hA1 hU hSU i hf y hy z hz, real_inner_smul_left]
  have e : inner ℝ (z - y i) (z - xhat y i) = inner ℝ (xhat y i - y i) (z - xhat y i) + ‖z - xhat y i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← inner_add_left]; congr 1; abel
  rw [e]
  nlinarith

end grad


section inner
open LeiBR.Rand
variable {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n) {μξ : Measure (EuclideanSpace ℝ (Fin d))}
    {ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ}
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i} {M : Fin N → ℝ}
    (hA1 : Assumption1 G μξ ψ gψ M) (i : Fin N) (mu : ℝ) (hmu : 0 < mu)
    (yy : LeiBR.Sync.Profile n) (hyy : G.Feasible yy) (zz xx : LeiBR.Sync.Strat n i)
    (hzz : zz ∈ G.X i) (hxx : xx ∈ G.X i) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
include hA1 hmu hyy hzz hxx ha0 ha1

lemma gs_facts : Measurable (fun s => gψ i (Function.update yy i zz) s) ∧
    Integrable (fun s => gψ i (Function.update yy i zz) s) μξ ∧
    Integrable (fun s => ‖gψ i (Function.update yy i zz) s‖ ^ 2) μξ ∧
    ∫ s, ‖gψ i (Function.update yy i zz) s‖ ^ 2 ∂μξ ≤ M i ^ 2 := by
  have hpf := feas_update G hyy i hzz
  exact ⟨(hA1.gψ_meas i).comp (measurable_const.prodMk measurable_id), (hA1.unbiased i _ hpf).1,
    (hA1.moment i _ hpf).1, (hA1.moment i _ hpf).2⟩

lemma dist_le (u v : LeiBR.Sync.Strat n i) (hu : u ∈ G.X i) (hv : v ∈ G.X i) :
    ‖u - v‖ ≤ Metric.diam (G.X i) := by
  rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem (hA1.compact i).isBounded hu hv

lemma inner_facts :
    Integrable (fun s => a * inner ℝ (saDir gψ mu i yy s zz) (zz - xx)) μξ ∧
    ∫ s, ‖a * inner ℝ (saDir gψ mu i yy s zz) (zz - xx)‖ ∂μξ ≤
      ((1 + M i ^ 2) / 2 + mu * Metric.diam (G.X i)) * Metric.diam (G.X i) ∧
    ∫ s, a * inner ℝ (saDir gψ mu i yy s zz) (zz - xx) ∂μξ =
      a * inner ℝ (∫ s, gψ i (Function.update yy i zz) s ∂μξ + mu • (zz - yy i)) (zz - xx) := by
  haveI := hA1.prob
  obtain ⟨hgm, hgi, hg2i, hg2⟩ := gs_facts G hA1 i mu hmu yy hyy zz xx hzz hxx a ha0 ha1
  set D := Metric.diam (G.X i)
  have hd1 : ‖zz - xx‖ ≤ D := dist_le G hA1 i mu hmu yy hyy zz xx hzz hxx a ha0 ha1 zz xx hzz hxx
  have hd2 : ‖zz - yy i‖ ≤ D := dist_le G hA1 i mu hmu yy hyy zz xx hzz hxx a ha0 ha1 zz (yy i) hzz (hyy i)
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have hmeas : Measurable fun s => a * inner ℝ (saDir gψ mu i yy s zz) (zz - xx) := by
    unfold saDir; fun_prop
  have hbd : ∀ s, ‖a * inner ℝ (saDir gψ mu i yy s zz) (zz - xx)‖ ≤
      (‖gψ i (Function.update yy i zz) s‖ + mu * D) * D := by
    intro s
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ha0]
    calc a * ‖inner ℝ (saDir gψ mu i yy s zz) (zz - xx)‖
        ≤ 1 * (‖saDir gψ mu i yy s zz‖ * ‖zz - xx‖) :=
          mul_le_mul ha1 (norm_inner_le_norm _ _) (norm_nonneg _) zero_le_one
      _ ≤ (‖gψ i (Function.update yy i zz) s‖ + mu * D) * D := by
          rw [one_mul]
          refine mul_le_mul ?_ hd1 (norm_nonneg _) (by positivity)
          unfold saDir
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hmu]
          gcongr
  have hbi : Integrable (fun s => (‖gψ i (Function.update yy i zz) s‖ + mu * D) * D) μξ :=
    (hgi.norm.add (integrable_const _)).mul_const _
  have hI : Integrable (fun s => a * inner ℝ (saDir gψ mu i yy s zz) (zz - xx)) μξ :=
    hbi.mono' hmeas.aestronglyMeasurable (ae_of_all _ hbd)
  refine ⟨hI, ?_, ?_⟩
  · have hnorm1 : ∫ s, ‖gψ i (Function.update yy i zz) s‖ ∂μξ ≤ (1 + M i ^ 2) / 2 := by
      have h1 : ∀ s, ‖gψ i (Function.update yy i zz) s‖ ≤ (1 + ‖gψ i (Function.update yy i zz) s‖ ^ 2) / 2 :=
        fun s => by nlinarith [sq_nonneg (‖gψ i (Function.update yy i zz) s‖ - 1)]
      calc ∫ s, ‖gψ i (Function.update yy i zz) s‖ ∂μξ
          ≤ ∫ s, (1 + ‖gψ i (Function.update yy i zz) s‖ ^ 2) / 2 ∂μξ :=
            integral_mono hgi.norm (((integrable_const 1).add hg2i).div_const 2) h1
        _ = (1 + ∫ s, ‖gψ i (Function.update yy i zz) s‖ ^ 2 ∂μξ) / 2 := by
            rw [integral_div, integral_add (integrable_const 1) hg2i]; simp
        _ ≤ (1 + M i ^ 2) / 2 := by linarith
    calc ∫ s, ‖a * inner ℝ (saDir gψ mu i yy s zz) (zz - xx)‖ ∂μξ
        ≤ ∫ s, (‖gψ i (Function.update yy i zz) s‖ + mu * D) * D ∂μξ :=
          integral_mono hI.norm hbi hbd
      _ = (∫ s, ‖gψ i (Function.update yy i zz) s‖ ∂μξ + mu * D) * D := by
          rw [integral_mul_const, integral_add hgi.norm (integrable_const _)]; simp
      _ ≤ ((1 + M i ^ 2) / 2 + mu * D) * D := by gcongr
  · rw [integral_const_mul]
    congr 1
    have : (fun s => inner ℝ (saDir gψ mu i yy s zz) (zz - xx)) =
        fun s => inner ℝ (zz - xx) (gψ i (Function.update yy i zz) s + mu • (zz - yy i)) := by
      funext s; unfold saDir; rw [real_inner_comm]
    rw [this, integral_inner (f := fun s => gψ i (Function.update yy i zz) s + mu • (zz - yy i))
      (hgi.add (integrable_const _)) (zz - xx), real_inner_comm,
      integral_add hgi (integrable_const _)]
    simp

lemma sq_facts :
    Integrable (fun s => a * ‖saDir gψ mu i yy s zz‖ ^ 2) μξ ∧
    ∫ s, ‖a * ‖saDir gψ mu i yy s zz‖ ^ 2‖ ∂μξ ≤
      2 * M i ^ 2 + 2 * mu ^ 2 * Metric.diam (G.X i) ^ 2 ∧
    ∫ s, a * ‖saDir gψ mu i yy s zz‖ ^ 2 ∂μξ ≤
      a * (2 * M i ^ 2 + 2 * mu ^ 2 * Metric.diam (G.X i) ^ 2) := by
  haveI := hA1.prob
  obtain ⟨hgm, hgi, hg2i, hg2⟩ := gs_facts G hA1 i mu hmu yy hyy zz xx hzz hxx a ha0 ha1
  set D := Metric.diam (G.X i)
  have hd2 : ‖zz - yy i‖ ≤ D := dist_le G hA1 i mu hmu yy hyy zz xx hzz hxx a ha0 ha1 zz (yy i) hzz (hyy i)
  have hmeas : Measurable fun s => a * ‖saDir gψ mu i yy s zz‖ ^ 2 := by
    unfold saDir; fun_prop
  have hpt : ∀ s, ‖saDir gψ mu i yy s zz‖ ^ 2 ≤
      2 * ‖gψ i (Function.update yy i zz) s‖ ^ 2 + 2 * mu ^ 2 * D ^ 2 := by
    intro s
    unfold saDir
    have h1 := norm_add_le (gψ i (Function.update yy i zz) s) (mu • (zz - yy i))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hmu] at h1
    have h2 : mu * ‖zz - yy i‖ ≤ mu * D := mul_le_mul_of_nonneg_left hd2 hmu.le
    have h3 : 0 ≤ ‖gψ i (Function.update yy i zz) s + mu • (zz - yy i)‖ := norm_nonneg _
    have h4 : ‖gψ i (Function.update yy i zz) s + mu • (zz - yy i)‖ ≤
        ‖gψ i (Function.update yy i zz) s‖ + mu * D := h1.trans (by linarith)
    have h5 := pow_le_pow_left₀ h3 h4 2
    have hD0 : 0 ≤ mu * D := by have := Metric.diam_nonneg (s := G.X i); positivity
    nlinarith [sq_nonneg (‖gψ i (Function.update yy i zz) s‖ - mu * D)]
  have hbi : Integrable (fun s => 2 * ‖gψ i (Function.update yy i zz) s‖ ^ 2 + 2 * mu ^ 2 * D ^ 2) μξ :=
    (hg2i.const_mul 2).add (integrable_const _)
  have hbd : ∀ s, ‖a * ‖saDir gψ mu i yy s zz‖ ^ 2‖ ≤
      2 * ‖gψ i (Function.update yy i zz) s‖ ^ 2 + 2 * mu ^ 2 * D ^ 2 := by
    intro s
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc a * ‖saDir gψ mu i yy s zz‖ ^ 2 ≤ 1 * ‖saDir gψ mu i yy s zz‖ ^ 2 :=
          mul_le_mul_of_nonneg_right ha1 (sq_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hpt s
  have hI : Integrable (fun s => a * ‖saDir gψ mu i yy s zz‖ ^ 2) μξ :=
    hbi.mono' hmeas.aestronglyMeasurable (ae_of_all _ hbd)
  have hint_b : ∫ s, (2 * ‖gψ i (Function.update yy i zz) s‖ ^ 2 + 2 * mu ^ 2 * D ^ 2) ∂μξ ≤
      2 * M i ^ 2 + 2 * mu ^ 2 * D ^ 2 := by
    rw [integral_add (hg2i.const_mul 2) (integrable_const _), integral_const_mul]
    simp; linarith
  refine ⟨hI, (integral_mono hI.norm hbi hbd).trans hint_b, ?_⟩
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ ha0
  have hsq : Integrable (fun s => ‖saDir gψ mu i yy s zz‖ ^ 2) μξ :=
    hbi.mono' (by unfold saDir; fun_prop) (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt s)
  exact (integral_mono hsq hbi hpt).trans hint_b

end inner


open LeiBR.Rand in
lemma step_meas {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (i : Fin N)
    {Pr : LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i} (hPr : Measurable Pr)
    {gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i}
    (hg : Measurable (Function.uncurry (gψ i))) (mu c : ℝ)
    {y : Ω → LeiBR.Sync.Profile n} (hy : Measurable y) {zz : Ω → LeiBR.Sync.Strat n i} (hz : Measurable zz)
    {ξ : Ω → EuclideanSpace ℝ (Fin d)} (hξ : Measurable ξ) :
    Measurable fun ω => Pr (zz ω - c • saDir gψ mu i (y ω) (ξ ω) (zz ω)) := by
  have hyi : Measurable fun ω => y ω i := (measurable_pi_apply i).comp hy
  have hupd : Measurable fun ω => Function.update (y ω) i (zz ω) := measurable_update'.comp (hy.prodMk hz)
  have hgg : Measurable fun ω => gψ i (Function.update (y ω) i (zz ω)) (ξ ω) := hg.comp (hupd.prodMk hξ)
  have hdir : Measurable fun ω => saDir gψ mu i (y ω) (ξ ω) (zz ω) := hgg.add ((hz.sub hyi).const_smul mu)
  exact hPr.comp (hz.sub (hdir.const_smul c))

lemma meas4 {Ω : Type*} [MeasurableSpace Ω] {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] {a : Ω → α} {b : Ω → β} {c : Ω → γ} {e : Ω → δ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (he : Measurable e) :
    Measurable fun ω => (a ω, b ω, c ω, e ω) := ha.prodMk (hb.prodMk (hc.prodMk he))


lemma arith_step (a0 I1 I2 γ mu M2 D Q PA r : ℝ) (hmu : 0 < mu) (hr2 : 2 ≤ r) (hγr : γ = 1 / (mu * r))
    (hQ : Q = 2 * M2 / mu ^ 2 + 2 * D ^ 2) (hQ0 : 0 ≤ Q) (hPA : 0 ≤ PA) (ha0 : 0 ≤ a0)
    (hI1 : mu * a0 ≤ I1) (hI2 : I2 ≤ (2 * M2 + 2 * mu ^ 2 * D ^ 2) * PA) (ih : a0 ≤ Q / r * PA) :
    a0 - 2 * γ * I1 + γ ^ 2 * I2 ≤ Q / (r + 1) * PA := by
  have hr0 : 0 < r := by linarith
  have hγ0 : 0 ≤ γ := by rw [hγr]; positivity
  have e1 : 2 * γ * mu = 2 / r := by rw [hγr]; field_simp
  have e2 : γ ^ 2 * (2 * M2 + 2 * mu ^ 2 * D ^ 2) = Q / r ^ 2 := by
    rw [hγr, hQ]; field_simp
  have k1 : 2 * γ * (mu * a0) ≤ 2 * γ * I1 := mul_le_mul_of_nonneg_left hI1 (by positivity)
  have k2 : γ ^ 2 * I2 ≤ γ ^ 2 * ((2 * M2 + 2 * mu ^ 2 * D ^ 2) * PA) :=
    mul_le_mul_of_nonneg_left hI2 (by positivity)
  have k3 : 2 * γ * (mu * a0) = 2 / r * a0 := by rw [← e1]; ring
  have k4 : γ ^ 2 * ((2 * M2 + 2 * mu ^ 2 * D ^ 2) * PA) = Q / r ^ 2 * PA := by rw [← e2]; ring
  have hcoef : 0 ≤ 1 - 2 / r := by rw [sub_nonneg, div_le_one hr0]; exact hr2
  have k5 : (1 - 2 / r) * a0 ≤ (1 - 2 / r) * (Q / r * PA) := mul_le_mul_of_nonneg_left ih hcoef
  have k6 : (1 - 2 / r) * (Q / r * PA) + Q / r ^ 2 * PA = Q * (r - 1) / r ^ 2 * PA := by
    field_simp; ring
  have k7 : Q * (r - 1) / r ^ 2 ≤ Q / (r + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have k8 := mul_le_mul_of_nonneg_right k7 hPA
  have k9 : a0 - 2 * γ * I1 + γ ^ 2 * I2 ≤ (1 - 2 / r) * a0 + Q / r ^ 2 * PA := by
    have : (1 - 2 / r) * a0 = a0 - 2 / r * a0 := by ring
    linarith
  linarith

end LeiBR2AuxL6

open LeiBR.Rand LeiBR2AuxL6

theorem solution {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (G.X i) (proj i))
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) (k : ℕ)
    (y : Ω → LeiBR.Sync.Profile n) (hy_meas : StronglyMeasurable[F k] y) (hy_feas : ∀ ω, G.Feasible (y ω))
    (s : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hs_meas : ∀ t, Measurable (s t))
    (hs_law : ∀ t, Measure.map (s (t + 1)) P = μξ) (hs_iid : iIndepFun (fun t => s (t + 1)) P)
    (hs_indep : Indep (⨆ t, MeasurableSpace.comap (s (t + 1)) inferInstance) (F k) P)
    (i : Fin N) (t : ℕ) (ht : 1 ≤ t) :
    P[fun ω => ‖saIter (proj i) (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) t
        - xhat (y ω) i‖ ^ 2 | F k] ≤ᵐ[P] fun _ => Qconst G M mu i / ((t : ℝ) + 1) := by
  haveI := hA1.prob
  obtain ⟨U, hUo, hSU, hsm⟩ := hA1.smooth
  have hf := hsm i
  set Q := Qconst G M mu i with hQdef
  set D := Metric.diam (G.X i) with hDdef
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have hM := hA1.M_pos i
  have hQ0 : 0 ≤ Q := by rw [hQdef]; unfold Qconst; positivity
  have hdist : ∀ u v : LeiBR.Sync.Strat n i, u ∈ G.X i → v ∈ G.X i → ‖u - v‖ ≤ D := fun u v hu hv => by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem (hA1.compact i).isBounded hu hv
  set z : ℕ → Ω → LeiBR.Sync.Strat n i := fun m ω =>
    saIter (proj i) (fun t' z => saDir gψ mu i (y ω) (s t' ω) z) mu (y ω i) m with hzdef
  set xh : Ω → LeiBR.Sync.Strat n i := fun ω => xhat (y ω) i with hxhdef
  have hzX : ∀ m ω, z m ω ∈ G.X i := fun m ω =>
    saIter_mem (fun w => (hproj i w).1) _ _ (hy_feas ω i) m
  have hxhX : ∀ ω, xh ω ∈ G.X i := fun ω => (hxhat (y ω) (hy_feas ω) i).1
  -- measurability
  have hym : Measurable[F k] y := hy_meas.measurable
  have hprojm : Measurable (proj i) := (proj_lip (hA1.convex i) (hproj i)).continuous.measurable
  have hxhm : Measurable[F k] xh := by
    have hc := (xhat_contOn G hA1 hmu hxhat i).domRestrict
    have hm : Measurable[F k] fun ω : Ω => (⟨y ω, hy_feas ω⟩ : {y | G.Feasible y}) := hym.subtype_mk
    exact @Measurable.comp Ω {y | G.Feasible y} _ (F k) _ _ _ _ hc.measurable hm
  set 𝒢 : ℕ → MeasurableSpace Ω := fun m =>
    F k ⊔ ⨆ l ∈ Set.Iio m, MeasurableSpace.comap (s (l + 1)) inferInstance with h𝒢def
  have h𝒢mono : ∀ m, 𝒢 m ≤ 𝒢 (m + 1) := fun m =>
    sup_le_sup_left (iSup₂_le fun l hl => le_iSup₂ (f := fun l (_ : l ∈ Set.Iio (m + 1)) =>
      MeasurableSpace.comap (s (l + 1)) inferInstance) l
      (Set.mem_Iio.2 ((Set.mem_Iio.1 hl).trans (Nat.lt_succ_self m)))) _
  have h𝒢le : ∀ m, 𝒢 m ≤ mΩ := fun m =>
    sup_le (F.le k) (iSup₂_le fun l _ => (hs_meas (l + 1)).comap_le)
  have hFk𝒢 : ∀ m, F k ≤ 𝒢 m := fun m => le_sup_left
  have hs𝒢 : ∀ m, Measurable[𝒢 (m + 1)] (s (m + 1)) := fun m =>
    Measurable.of_comap_le ((le_iSup₂ (f := fun l (_ : l ∈ Set.Iio (m + 1)) =>
      MeasurableSpace.comap (s (l + 1)) inferInstance) m (Set.mem_Iio.2 (Nat.lt_succ_self m))).trans le_sup_right)
  have hzm : ∀ m, Measurable[𝒢 m] (z (m + 1)) := by
    intro m
    induction m with
    | zero => exact ((measurable_pi_apply i).comp hym).mono (hFk𝒢 0) le_rfl
    | succ m ih =>
      exact @step_meas Ω (𝒢 (m + 1)) N n d i (proj i) hprojm gψ (hA1.gψ_meas i) mu
        (1 / (mu * (((m + 1 : ℕ) : ℝ) + 1))) y (hym.mono (hFk𝒢 _) le_rfl) (z (m + 1))
        (ih.mono (h𝒢mono m) le_rfl) (s (m + 1)) (hs𝒢 m)
  have hzm' : ∀ m, Measurable (z (m + 1)) := fun m => (hzm m).mono (h𝒢le m) le_rfl
  have hym' : Measurable y := hym.mono (F.le k) le_rfl
  have hxhm' : Measurable xh := hxhm.mono (F.le k) le_rfl
  have hrec : ∀ A, MeasurableSet[F k] A → ∀ m : ℕ,
      ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2 ∂P ≤ Q / ((m : ℝ) + 2) * P.real A := by
    intro A hA m
    have hAm : MeasurableSet A := F.le k _ hA
    have hind01 : ∀ ω, A.indicator (1 : Ω → ℝ) ω = 0 ∨ A.indicator (1 : Ω → ℝ) ω = 1 := fun ω => by
      by_cases h : ω ∈ A <;> simp [h]
    have hind0 : ∀ ω, 0 ≤ A.indicator (1 : Ω → ℝ) ω := fun ω => by
      rcases hind01 ω with h | h <;> rw [h] <;> norm_num
    have hind1 : ∀ ω, A.indicator (1 : Ω → ℝ) ω ≤ 1 := fun ω => by
      rcases hind01 ω with h | h <;> rw [h] <;> norm_num
    have hindm : Measurable[F k] (A.indicator (1 : Ω → ℝ)) := measurable_const.indicator hA
    have hindm' : Measurable (A.indicator (1 : Ω → ℝ)) := measurable_const.indicator hAm
    have hintc : ∀ c : ℝ, ∫ ω, A.indicator (1 : Ω → ℝ) ω * c ∂P = c * P.real A := by
      intro c
      simp_rw [mul_comm _ c]
      rw [integral_const_mul, integral_indicator_one hAm]
    have hXint : ∀ m : ℕ, Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2) P := by
      intro m
      refine Integrable.of_bound ((hindm'.mul (((hzm' m).sub hxhm').norm.pow_const 2))).aestronglyMeasurable
        (D ^ 2) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hind0 ω) (sq_nonneg _))]
      calc A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2 ≤ 1 * D ^ 2 :=
            mul_le_mul (hind1 ω) (pow_le_pow_left₀ (norm_nonneg _) (hdist _ _ (hzX _ ω) (hxhX ω)) 2)
              (sq_nonneg _) zero_le_one
        _ = D ^ 2 := one_mul _
    have hPA : 0 ≤ P.real A := measureReal_nonneg
    induction m with
    | zero =>
      have h1 : ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (0 + 1) ω - xh ω‖ ^ 2 ∂P ≤
          ∫ ω, A.indicator (1 : Ω → ℝ) ω * D ^ 2 ∂P :=
        integral_mono (hXint 0) (hindm'.mul_const _ |>.aestronglyMeasurable |> fun h =>
          Integrable.of_bound h (D ^ 2) (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hind0 ω) (sq_nonneg _))]
            exact (mul_le_of_le_one_left (sq_nonneg _) (hind1 ω))))
          (fun ω => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hdist _ _ (hzX _ ω) (hxhX ω)) 2) (hind0 ω))
      rw [hintc] at h1
      refine h1.trans ?_
      have : D ^ 2 ≤ Q / ((0 : ℕ) + 2 : ℝ) := by
        rw [hQdef]; unfold Qconst; push_cast
        rw [le_div_iff₀ (by norm_num)]
        have : 0 ≤ 2 * M i ^ 2 / mu ^ 2 := by positivity
        rw [← hDdef]; linarith
      exact mul_le_mul_of_nonneg_right this hPA
    | succ m ih =>
      set γ : ℝ := 1 / (mu * (((m + 1 : ℕ) : ℝ) + 1)) with hγ
      have hγ0 : 0 ≤ γ := by positivity
      set Gd : Ω → LeiBR.Sync.Strat n i := fun ω => saDir gψ mu i (y ω) (s (m + 1) ω) (z (m + 1) ω)
        with hGd
      have hz2 : ∀ ω, z (m + 1 + 1) ω = proj i (z (m + 1) ω - γ • Gd ω) := fun ω => rfl
      have hpt : ∀ ω, ‖z (m + 1 + 1) ω - xh ω‖ ^ 2 ≤ ‖z (m + 1) ω - xh ω‖ ^ 2
          - 2 * γ * inner ℝ (Gd ω) (z (m + 1) ω - xh ω) + γ ^ 2 * ‖Gd ω‖ ^ 2 := by
        intro ω
        rw [hz2]
        have h1 := proj_toward (hA1.convex i) (hproj i) (z (m + 1) ω - γ • Gd ω) (xh ω) (hxhX ω)
        have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        have e : z (m + 1) ω - γ • Gd ω - xh ω = (z (m + 1) ω - xh ω) - γ • Gd ω := by abel
        rw [e, norm_sub_sq_real (z (m + 1) ω - xh ω) (γ • Gd ω), norm_smul, inner_smul_right,
          real_inner_comm, Real.norm_eq_abs, abs_of_nonneg hγ0, mul_pow] at h2
        linarith
      -- freezing
      set W : Ω → ℝ × LeiBR.Sync.Profile n × LeiBR.Sync.Strat n i × LeiBR.Sync.Strat n i :=
        fun ω => (A.indicator (1 : Ω → ℝ) ω, y ω, z (m + 1) ω, xh ω) with hW
      have hWm : Measurable[𝒢 m] W :=
        @meas4 Ω (𝒢 m) _ _ _ _ _ _ _ _ _ _ _ _ (hindm.mono (hFk𝒢 m) le_rfl) (hym.mono (hFk𝒢 m) le_rfl)
          (hzm m) (hxhm.mono (hFk𝒢 m) le_rfl)
      have hWm' : Measurable W := hWm.mono (h𝒢le m) le_rfl
      have hindW : IndepFun W (s (m + 1)) P := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_left (indep_past P F k s hs_meas hs_iid hs_indep m).symm hWm.comap_le
      set B : Set (ℝ × LeiBR.Sync.Profile n × LeiBR.Sync.Strat n i × LeiBR.Sync.Strat n i) :=
        Prod.fst ⁻¹' Set.Icc 0 1 ∩ ((fun w => w.2.1) ⁻¹' Set.univ.pi G.X ∩
          ((fun w => w.2.2.1) ⁻¹' G.X i ∩ (fun w => w.2.2.2) ⁻¹' G.X i)) with hB
      have hBm : MeasurableSet B :=
        (measurable_fst measurableSet_Icc).inter ((measurable_snd.fst
          (MeasurableSet.univ_pi fun j => (hA1.closed j).measurableSet)).inter
          ((measurable_snd.snd.fst (hA1.closed i).measurableSet).inter
            (measurable_snd.snd.snd (hA1.closed i).measurableSet)))
      have hWB : ∀ ω, W ω ∈ B := fun ω =>
        ⟨⟨hind0 ω, hind1 ω⟩, Set.mem_univ_pi.2 (hy_feas ω), hzX _ ω, hxhX ω⟩
      have hBfeas : ∀ w ∈ B, G.Feasible w.2.1 := fun w hw => Set.mem_univ_pi.1 hw.2.1
      have hG : Measurable fun q : (ℝ × LeiBR.Sync.Profile n × LeiBR.Sync.Strat n i × LeiBR.Sync.Strat n i) ×
          EuclideanSpace ℝ (Fin d) => saDir gψ mu i q.1.2.1 q.2 q.1.2.2.1 :=
        ((hA1.gψ_meas i).comp ((measurable_update'.comp (measurable_fst.snd.fst.prodMk
          measurable_fst.snd.snd.fst)).prodMk measurable_snd)).add
          ((measurable_fst.snd.snd.fst.sub ((measurable_pi_apply i).comp measurable_fst.snd.fst)).const_smul mu)
      set h1 : (ℝ × LeiBR.Sync.Profile n × LeiBR.Sync.Strat n i × LeiBR.Sync.Strat n i) ×
          EuclideanSpace ℝ (Fin d) → ℝ :=
        fun q => q.1.1 * inner ℝ (saDir gψ mu i q.1.2.1 q.2 q.1.2.2.1) (q.1.2.2.1 - q.1.2.2.2) with hh1
      set h2 : (ℝ × LeiBR.Sync.Profile n × LeiBR.Sync.Strat n i × LeiBR.Sync.Strat n i) ×
          EuclideanSpace ℝ (Fin d) → ℝ :=
        fun q => q.1.1 * ‖saDir gψ mu i q.1.2.1 q.2 q.1.2.2.1‖ ^ 2 with hh2
      have hh1m : Measurable h1 :=
        measurable_fst.fst.mul (hG.inner (measurable_fst.snd.snd.fst.sub measurable_fst.snd.snd.snd))
      have hh2m : Measurable h2 := measurable_fst.fst.mul (hG.norm.pow_const 2)
      have F1 := freeze P μξ W (s (m + 1)) hWm' (hs_meas _) hindW (hs_law m) h1 hh1m B hBm hWB _
        (fun w hw => (inner_facts G hA1 i mu hmu w.2.1 (hBfeas w hw) w.2.2.1 w.2.2.2 hw.2.2.1 hw.2.2.2
          w.1 hw.1.1 hw.1.2).1)
        (fun w hw => (inner_facts G hA1 i mu hmu w.2.1 (hBfeas w hw) w.2.2.1 w.2.2.2 hw.2.2.1 hw.2.2.2
          w.1 hw.1.1 hw.1.2).2.1)
      have F2 := freeze P μξ W (s (m + 1)) hWm' (hs_meas _) hindW (hs_law m) h2 hh2m B hBm hWB _
        (fun w hw => (sq_facts G hA1 i mu hmu w.2.1 (hBfeas w hw) w.2.2.1 w.2.2.2 hw.2.2.1 hw.2.2.2
          w.1 hw.1.1 hw.1.2).1)
        (fun w hw => (sq_facts G hA1 i mu hmu w.2.1 (hBfeas w hw) w.2.2.1 w.2.2.2 hw.2.2.1 hw.2.2.2
          w.1 hw.1.1 hw.1.2).2.1)
      have hI1 : mu * ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2 ∂P ≤
          ∫ ω, A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω) ∂P := by
        have e : ∫ ω, A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω) ∂P =
            ∫ ω, h1 (W ω, s (m + 1) ω) ∂P := rfl
        rw [e, F1.2.1, ← integral_const_mul]
        refine integral_mono ((hXint m).const_mul mu) F1.2.2 fun ω => ?_
        have hw := hWB ω
        rw [(inner_facts G hA1 i mu hmu (y ω) (hy_feas ω) (z (m + 1) ω) (xh ω) (hzX _ ω) (hxhX ω)
          _ (hind0 ω) (hind1 ω)).2.2]
        have := strong_ineq G hA1 hUo hSU i hf hxhat (y ω) (hy_feas ω) (z (m + 1) ω) (hzX _ ω)
        calc mu * (A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2)
            = A.indicator (1 : Ω → ℝ) ω * (mu * ‖z (m + 1) ω - xhat (y ω) i‖ ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left this (hind0 ω)
      have hI2 : ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2 ∂P ≤
          (2 * M i ^ 2 + 2 * mu ^ 2 * D ^ 2) * P.real A := by
        have e : ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2 ∂P = ∫ ω, h2 (W ω, s (m + 1) ω) ∂P := rfl
        rw [e, F2.2.1, ← hintc]
        refine integral_mono F2.2.2 ((integrable_const _).bdd_mul hindm'.aestronglyMeasurable
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hind0 ω)]; exact hind1 ω)) fun ω => ?_
        exact (sq_facts G hA1 i mu hmu (y ω) (hy_feas ω) (z (m + 1) ω) (xh ω) (hzX _ ω) (hxhX ω)
          _ (hind0 ω) (hind1 ω)).2.2
      have hmono : ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1 + 1) ω - xh ω‖ ^ 2 ∂P ≤
          ∫ ω, (A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2
            - 2 * γ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω))
            + γ ^ 2 * (A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2)) ∂P := by
        have hiY : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω)) P :=
          F1.1
        have hiZ : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2) P := F2.1
        refine integral_mono (hXint (m + 1)) (((hXint m).sub (hiY.const_mul (2 * γ))).add
          (hiZ.const_mul (γ ^ 2))) fun ω => ?_
        have := mul_le_mul_of_nonneg_left (hpt ω) (hind0 ω)
        simp only at this ⊢
        nlinarith [this]
      have hiY : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω)) P :=
        F1.1
      have hiZ : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2) P := F2.1
      rw [integral_add (f := fun ω => A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2
            - 2 * γ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω)))
          (g := fun ω => γ ^ 2 * (A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2))
          ((hXint m).sub (hiY.const_mul _)) (hiZ.const_mul _),
        integral_sub (f := fun ω => A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2)
          (g := fun ω => 2 * γ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω)))
          (hXint m) (hiY.const_mul _), integral_const_mul, integral_const_mul] at hmono
      -- arithmetic
      have ha0nn : 0 ≤ ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2 ∂P :=
        integral_nonneg fun ω => mul_nonneg (hind0 ω) (sq_nonneg _)
      have hr2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
      have hγr : γ = 1 / (mu * ((m : ℝ) + 2)) := by rw [hγ]; push_cast; ring
      have hQe : Q = 2 * M i ^ 2 / mu ^ 2 + 2 * D ^ 2 := by rw [hQdef, hDdef]; rfl
      have := arith_step _ _ _ γ mu (M i ^ 2) D Q (P.real A) ((m : ℝ) + 2) hmu hr2 hγr hQe hQ0 hPA ha0nn
        hI1 hI2 ih
      have hc : (((m + 1 : ℕ) : ℝ) + 2) = (m : ℝ) + 2 + 1 := by push_cast; ring
      rw [hc]
      exact hmono.trans this
  -- conclusion
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hfi : Integrable (fun ω => ‖z (m + 1) ω - xh ω‖ ^ 2) P := by
    refine Integrable.of_bound (((hzm' m).sub hxhm').norm.pow_const 2).aestronglyMeasurable (D ^ 2)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdist _ _ (hzX _ ω) (hxhX ω)) 2
  refine ae_of_ae_trim (F.le k) ?_
  have hint1 : Integrable (P[fun ω => ‖z (m + 1) ω - xh ω‖ ^ 2 | F k]) (P.trim (F.le k)) :=
    integrable_condExp.trim (F.le k) stronglyMeasurable_condExp
  have hint2 : Integrable (fun _ : Ω => Q / (((m + 1 : ℕ) : ℝ) + 1)) (P.trim (F.le k)) := integrable_const _
  refine ae_le_of_forall_setIntegral_le hint1 hint2 fun S hS _ => ?_
  rw [← setIntegral_trim (F.le k) stronglyMeasurable_condExp hS,
    ← setIntegral_trim (F.le k) stronglyMeasurable_const hS, setIntegral_condExp (F.le k) hfi hS,
    setIntegral_const]
  have h := hrec S hS m
  have e : (fun ω => S.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2) =
      S.indicator (fun ω => ‖z (m + 1) ω - xh ω‖ ^ 2) := by
    funext ω; by_cases hω : ω ∈ S <;> simp [hω]
  rw [e, integral_indicator (F.le k _ hS)] at h
  have hc : Q / ((m : ℝ) + 2) = Q / (((m + 1 : ℕ) : ℝ) + 1) := by push_cast; ring_nf
  rw [hc] at h
  rw [smul_eq_mul, mul_comm]
  exact h
