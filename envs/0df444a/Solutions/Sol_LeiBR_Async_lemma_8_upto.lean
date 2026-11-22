-- Prove2me | solution 1 for LeiBR.Async.lemma_8_upto
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:14:32.822229+00:00
-- url     : https://prove2.me/submissions/abfbc61e-3434-426e-870e-23cd121c26d6

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Definitions.Def_LeiBR_Async_Algorithm

namespace LeiBRAsyncL8Upto

open MeasureTheory
open LeiBR.Sync (Strat Profile)
open LeiBR.Async

/-- A projection onto a nonempty closed convex set is 1-Lipschitz, hence continuous. -/
lemma proj_continuous {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin m))} (hK : Convex ℝ K)
    {p : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hp : SpectralProjGrad.Shared.IsProjOnto K p) : Continuous p := by
  have vi : ∀ z, ∀ w ∈ K, inner ℝ (z - p z) (w - p z) ≤ 0 := by
    intro z
    have hmem := (hp z).1
    have : ‖z - p z‖ = ⨅ w : K, ‖z - w‖ := by
      have : Nonempty K := ⟨⟨p z, hmem⟩⟩
      have hbdd : BddBelow (Set.range fun w : K => ‖z - (w : EuclideanSpace ℝ (Fin m))‖) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨w, rfl⟩
        exact norm_nonneg _
      apply le_antisymm
      · exact le_ciInf fun w => (hp z).2 w w.2
      · exact ciInf_le hbdd (⟨p z, hmem⟩ : K)
    exact (norm_eq_iInf_iff_real_inner_le_zero hK hmem).1 this
  have lip : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖ := by
    intro z w
    have h1 := vi z (p w) (hp w).1
    have h2 := vi w (p z) (hp z).1
    have key : ‖p z - p w‖ ^ 2 ≤ inner ℝ (z - w) (p z - p w) := by
      have e : inner ℝ (z - w) (p z - p w) - ‖p z - p w‖ ^ 2
          = - inner ℝ (z - p z) (p w - p z) - inner ℝ (w - p w) (p z - p w) := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_comm]
        ring
      linarith
    have cs := real_inner_le_norm (z - w) (p z - p w)
    by_cases h0 : ‖p z - p w‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hpos : 0 < ‖p z - p w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  exact (LipschitzWith.of_dist_le_mul (K := 1) fun z w => by
    simpa [dist_eq_norm] using lip z w).continuous

/-- Projection onto a convex set does not increase distance to any point in the set. -/
lemma proj_toward {m : ℕ} {K : Set (EuclideanSpace ℝ (Fin m))} (hK : Convex ℝ K)
    {Pr : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    (hP : SpectralProjGrad.Shared.IsProjOnto K Pr) (w x : EuclideanSpace ℝ (Fin m)) (hx : x ∈ K) :
    ‖Pr w - x‖ ≤ ‖w - x‖ := by
  have hu := (hP w).1
  have hinf : ‖w - Pr w‖ = ⨅ v : K, ‖w - (v : EuclideanSpace ℝ (Fin m))‖ := by
    have : Nonempty K := ⟨⟨_, hu⟩⟩
    refine le_antisymm (le_ciInf fun v => (hP w).2 v v.2) ?_
    have hbdd : BddBelow (Set.range fun v : K => ‖w - (v : EuclideanSpace ℝ (Fin m))‖) := by
      refine ⟨0, ?_⟩
      rintro r ⟨v, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbdd (⟨Pr w, hu⟩ : K)
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hK hu).1 hinf x hx
  have hexp : ‖w - x‖ ^ 2 = ‖w - Pr w‖ ^ 2 + ‖Pr w - x‖ ^ 2 - 2 * inner ℝ (w - Pr w) (x - Pr w) := by
    have : w - x = (w - Pr w) + (Pr w - x) := by abel
    rw [this, norm_add_sq_real]
    have : inner ℝ (w - Pr w) (Pr w - x) = - inner ℝ (w - Pr w) (x - Pr w) := by
      rw [← inner_neg_right, neg_sub]
    rw [this]; ring
  have h1 : ‖Pr w - x‖ ^ 2 ≤ ‖w - x‖ ^ 2 := by nlinarith [sq_nonneg ‖w - Pr w‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- Quadratic growth at a minimizer of a `μ`-strongly convex proximal objective. -/
lemma mid_strong {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E}
    (hK : Convex ℝ K) {g : E → ℝ} (hg : ConvexOn ℝ K g) {mu : ℝ} (hmu : 0 ≤ mu) {c u z : E}
    (hu : u ∈ K) (hz : z ∈ K)
    (hmin : IsMinOn (fun y => g y + mu / 2 * ‖y - c‖ ^ 2) K u) :
    mu / 4 * ‖z - u‖ ^ 2 ≤ (g z + mu / 2 * ‖z - c‖ ^ 2) - (g u + mu / 2 * ‖u - c‖ ^ 2) := by
  set m : E := (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • z with hm
  have hmK : m ∈ K := hK hu hz (by norm_num) (by norm_num) (by norm_num)
  have hgm : g m ≤ (1 / 2 : ℝ) • g u + (1 / 2 : ℝ) • g z :=
    hg.2 hu hz (by norm_num) (by norm_num) (by norm_num)
  have hmin' := hmin hmK
  simp only [Set.mem_ofPred_eq] at hmin'
  have hpar := parallelogram_law_with_norm ℝ (u - c) (z - c)
  have h1 : u - c + (z - c) = (2 : ℝ) • (m - c) := by
    rw [hm]; module
  have h2 : u - c - (z - c) = -(z - u) := by abel
  rw [h1, h2, norm_neg, norm_smul] at hpar
  simp only [smul_eq_mul] at hgm
  have : ‖(2 : ℝ)‖ = 2 := by norm_num
  rw [this] at hpar
  nlinarith [sq_nonneg ‖z - u‖]

variable {N : ℕ} {n : Fin N → ℕ}

lemma feas_update {X : ∀ i, Set (Strat n i)} {y : Profile n} (hy : y ∈ profileSet X)
    (i : Fin N) {z : Strat n i} (hz : z ∈ X i) :
    Function.update y i z ∈ profileSet X := by
  refine Set.mem_univ_pi.2 fun l => ?_
  by_cases h : l = i
  · subst h; simpa using hz
  · rw [Function.update_of_ne h]; exact Set.mem_univ_pi.1 hy l

/-- The proximal best-response coordinate `y ↦ x̂_i(y)` is continuous on `X`. -/
lemma xhat_contOn (X : ∀ i, Set (Strat n i)) (f : Fin N → Profile n → ℝ)
    (hA1 : Assumption1ab X f) {μ : ℝ} (hμ : 0 < μ)
    {xhat : Profile n → Profile n} (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (i : Fin N) :
    ContinuousOn (fun y => xhat y i) (profileSet X) := by
  set S : Set (Profile n) := profileSet X with hSdef
  have hSc : IsCompact S := isCompact_univ_pi hA1.compact
  obtain ⟨U, hU, hsm, hcvx⟩ := hA1.smooth
  have hSU : S ⊆ Set.univ.pi U := Set.pi_mono fun l _ => (hU l).2.2
  have hfc : ContinuousOn (f i) S := ((hsm i).continuousOn).mono hSU
  let h : Profile n × Strat n i → ℝ :=
    fun p => f i (Function.update p.1 i p.2) + μ / 2 * ‖p.2 - p.1 i‖ ^ 2
  have hK : IsCompact (S ×ˢ X i) := hSc.prod (hA1.compact i)
  have hcont : ContinuousOn h (S ×ˢ X i) := by
    refine ContinuousOn.add ?_ (Continuous.continuousOn (by fun_prop))
    refine hfc.comp (Continuous.update continuous_fst i continuous_snd).continuousOn ?_
    intro p hp
    exact feas_update hp.1 i hp.2
  have huc := (Metric.uniformContinuousOn_iff).1 (hK.uniformContinuousOn_of_continuous hcont)
  refine Metric.continuousOn_iff.2 fun y hy ε hε => ?_
  obtain ⟨δ, hδ, hδh⟩ := huc (μ * ε ^ 2 / 4) (by positivity)
  refine ⟨δ, hδ, fun y' hy' hd => ?_⟩
  have hu := (hxhat y hy i).1
  have hu' := (hxhat y' hy' i).1
  have hcv : ∀ y0 ∈ S, ConvexOn ℝ (X i) (fun z => f i (Function.update y0 i z)) :=
    fun y0 hy0 => (hcvx i y0 hy0).subset (hU i).2.2 (hA1.convex i)
  have sc1 := mid_strong (hA1.convex i) (hcv y hy) hμ.le hu hu' (hxhat y hy i).2
  have sc2 := mid_strong (hA1.convex i) (hcv y' hy') hμ.le hu' hu (hxhat y' hy' i).2
  have d1 := hδh (y, xhat y' i) ⟨hy, hu'⟩ (y', xhat y' i) ⟨hy', hu'⟩
    (by rw [Prod.dist_eq]; simp; rw [dist_comm]; exact hd)
  have d2 := hδh (y', xhat y i) ⟨hy', hu⟩ (y, xhat y i) ⟨hy, hu⟩
    (by rw [Prod.dist_eq]; simp; exact hd)
  simp only [h, Real.dist_eq] at d1 d2
  rw [abs_lt] at d1 d2
  rw [dist_eq_norm]
  rw [norm_sub_rev (xhat y i) (xhat y' i)] at sc2
  have hsq : ‖xhat y' i - xhat y i‖ ^ 2 < ε ^ 2 := by
    have : μ * ‖xhat y' i - xhat y i‖ ^ 2 < μ * ε ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_left this hμ.le
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

lemma meas_step {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (i : Fin N)
    (pr : Strat n i → Strat n i) (hpr : Continuous pr)
    (g : Profile n → EuclideanSpace ℝ (Fin d) → Strat n i)
    (hg : Measurable (Function.uncurry g))
    (y : Ω → Profile n) (hy : Measurable y) (z : Ω → Strat n i) (hz : Measurable z)
    (s : Ω → EuclideanSpace ℝ (Fin d)) (hs : Measurable s) (c μ : ℝ) :
    Measurable (fun ω => pr (z ω - c • (g (Function.update (y ω) i (z ω)) (s ω)
      + μ • (z ω - y ω i)))) := by
  have hu : Measurable (fun ω => Function.update (y ω) i (z ω)) :=
    measurable_update'.comp (hy.prodMk hz)
  have hgg : Measurable (fun ω => g (Function.update (y ω) i (z ω)) (s ω)) :=
    hg.comp (hu.prodMk hs)
  have hyi : Measurable (fun ω => y ω i) := (measurable_pi_apply i).comp hy
  exact hpr.measurable.comp (hz.sub ((hgg.add ((hz.sub hyi).const_smul μ)).const_smul c))

lemma saPath_ss {d : ℕ}
    (proj : ∀ i, Strat n i → Strat n i)
    (gψ : ∀ i, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (μ : ℝ) (i : Fin N)
    (y : Profile n) (ξ : ℕ → EuclideanSpace ℝ (Fin d)) (m : ℕ) :
    saPath proj gψ μ i y ξ (m + 2) =
      proj i (saPath proj gψ μ i y ξ (m + 1) -
        (1 / (μ * ((m : ℝ) + 2))) •
          (gψ i (Function.update y i (saPath proj gψ μ i y ξ (m + 1))) (ξ (m + 1)) +
            μ • (saPath proj gψ μ i y ξ (m + 1) - y i))) := rfl

lemma saPath_mem {d : ℕ} (X : ∀ i, Set (Strat n i))
    (proj : ∀ i, Strat n i → Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (gψ : ∀ i, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (μ : ℝ) (i : Fin N)
    {y : Profile n} (hy : y ∈ profileSet X) (ξ : ℕ → EuclideanSpace ℝ (Fin d)) :
    ∀ t, saPath proj gψ μ i y ξ t ∈ X i
  | 0 => Set.mem_univ_pi.1 hy i
  | 1 => Set.mem_univ_pi.1 hy i
  | _ + 2 => (hproj i _).1

lemma cdAt {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) : ContDiffAt ℝ 2 f x :=
  hf.contDiffAt (hU.mem_nhds hx)

lemma hasD1 {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((cdAt hU hf hx).differentiableAt (by norm_num)).hasFDerivAt

lemma path_deriv (x : Profile n) (i : Fin N) (a v : Strat n i) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Function.update x i (a + s • v)) (Pi.single i v) s := by
  have h1 : HasDerivAt (fun s : ℝ => a + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add a
  have h2 := (hasFDerivAt_update (𝕜 := ℝ) x (a + s • v)).comp_hasDerivAt s h1
  have e : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Strat n i)))) v
      = Pi.single i v := by
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e] at h2
  exact h2

lemma pi_single_apply (i : Fin N) (v : Strat n i) :
    (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (Strat n i)))) v
      = (Pi.single i v : Profile n) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma foc {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (i : Fin N) {Xi : Set (Strat n i)} (hXi : Convex ℝ Xi) {mu : ℝ} (y : Profile n)
    {u : Strat n i} (hu : u ∈ Xi) (hP : Function.update y i u ∈ U)
    (hmin : IsMinOn (fun z : Strat n i => f (Function.update y i z) + mu / 2 * ‖z - y i‖ ^ 2) Xi u)
    (z : Strat n i) (hz : z ∈ Xi) :
    0 ≤ fderiv ℝ f (Function.update y i u) (Pi.single i (z - u)) +
      mu * inner ℝ (u - y i) (z - u) := by
  have h1 := (hasD1 hU hf hP).comp u (hasFDerivAt_update (𝕜 := ℝ) y u)
  have h2 := (((hasFDerivAt_id (𝕜 := ℝ) u).sub_const (y i)).norm_sq).const_mul (mu / 2)
  have h := h1.add h2
  have hmin := hmin.localize
  have hseg : segment ℝ u (u + (z - u)) ⊆ Xi := by
    rw [add_sub_cancel]; exact hXi.segment_subset hu hz
  have := hmin.hasFDerivWithinAt_nonneg h.hasFDerivWithinAt
    (mem_posTangentConeAt_of_segment_subset hseg)
  simp only [ContinuousLinearMap.comp_apply, pi_single_apply,
    innerSL_apply_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, FunLike.coe_add, FunLike.coe_smul,
    Pi.add_apply, Pi.smul_apply] at this
  convert this using 2
  simp only [id]
  ring

lemma grad_inner {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (i : Fin N) (y : Profile n) (z : Strat n i)
    (hP : Function.update y i z ∈ U) (v : Strat n i) :
    inner ℝ (partialGrad f i (Function.update y i z)) v =
      fderiv ℝ f (Function.update y i z) (Pi.single i v) := by
  unfold partialGrad gradient
  simp only [Function.update_idem, Function.update_self]
  rw [InnerProductSpace.toDual_symm_apply]
  have h1 : HasFDerivAt (fun z' => f (Function.update y i z')) _ z :=
    (hasD1 hU hf hP).comp z (hasFDerivAt_update (𝕜 := ℝ) y z)
  rw [h1.fderiv]
  simp only [ContinuousLinearMap.comp_apply, pi_single_apply]

lemma grad_mono {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (i : Fin N) {Xi : Set (Strat n i)} (hXi : Convex ℝ Xi)
    (y : Profile n) (hyU : ∀ w ∈ Xi, Function.update y i w ∈ U)
    (hcX : ConvexOn ℝ Xi (fun z => f (Function.update y i z)))
    (a z : Strat n i) (ha : a ∈ Xi) (hz : z ∈ Xi) :
    fderiv ℝ f (Function.update y i a) (Pi.single i (z - a)) ≤
      fderiv ℝ f (Function.update y i z) (Pi.single i (z - a)) := by
  set γ : ℝ → Strat n i := fun s => a + s • (z - a) with hγ
  have hγX : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ Xi := fun s hs => hXi.add_smul_sub_mem ha hz hs
  set k : ℝ → ℝ := fun s => f (Function.update y i (γ s)) with hk
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
  have hkd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt k (fderiv ℝ f (Function.update y i (γ s)) (Pi.single i (z - a))) s := by
    intro s hs
    exact (hasD1 hU hf (hyU _ (hγX s hs))).comp_hasDerivAt s (path_deriv y i a (z - a) s)
  have hmono := hkconv.monotoneOn_deriv fun s hs => (hkd s hs).differentiableAt
  have h01 := hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  rw [(hkd 0 (Set.left_mem_Icc.2 zero_le_one)).deriv,
    (hkd 1 (Set.right_mem_Icc.2 zero_le_one)).deriv] at h01
  simpa [hγ] using h01

/-- Strong monotonicity at the proximal best response. -/
lemma strong_ineq {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (i : Fin N) {Xi : Set (Strat n i)} (hXi : Convex ℝ Xi) {mu : ℝ}
    (y : Profile n) (hyU : ∀ w ∈ Xi, Function.update y i w ∈ U)
    (hcX : ConvexOn ℝ Xi (fun z => f (Function.update y i z)))
    {u : Strat n i} (hu : u ∈ Xi)
    (hmin : IsMinOn (fun z : Strat n i => f (Function.update y i z) + mu / 2 * ‖z - y i‖ ^ 2) Xi u)
    (z : Strat n i) (hz : z ∈ Xi) :
    mu * ‖z - u‖ ^ 2 ≤
      inner ℝ (partialGrad f i (Function.update y i z) + mu • (z - y i)) (z - u) := by
  have h1 := foc hU hf i hXi y hu (hyU u hu) hmin z hz
  have h2 := grad_mono hU hf i hXi y hyU hcX u z hu hz
  rw [inner_add_left, grad_inner hU hf i y z (hyU z hz), real_inner_smul_left]
  have e : inner ℝ (z - y i) (z - u) = inner ℝ (u - y i) (z - u) + ‖z - u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← inner_add_left]; congr 1; abel
  rw [e]
  nlinarith

lemma arith_step (a0 I1 I2 γ mu M2 D Q PA r : ℝ) (hmu : 0 < mu) (hr2 : 2 ≤ r) (hγr : γ = 1 / (mu * r))
    (hQ : Q = 2 * M2 / mu ^ 2 + 2 * D ^ 2) (hQ0 : 0 ≤ Q) (hPA : 0 ≤ PA)
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

end LeiBRAsyncL8Upto

open MeasureTheory LeiBR.Async LeiBRAsyncL8Upto in
theorem solution {Ω : Type*} (Fk : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (M : Fin N → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (hgψ : ∀ i, Measurable (Function.uncurry (gψ i)))
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (i : Fin N) (j : ℕ) (hFk : Fk ≤ mΩ) (G : ℕ → MeasurableSpace Ω)
    (hG : ∀ t, t ≤ j → G t ≤ mΩ) (hFG : Fk ≤ G 1) (hGmono : ∀ t, G t ≤ G (t + 1))
    (y : Ω → LeiBR.Sync.Profile n) (hy : Measurable[Fk] y) (hyX : ∀ ω, y ω ∈ profileSet X)
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hξ : ∀ t, t < j → Measurable[G (t + 1)] (ξ t))
    (horacle : IsSAOracle P f gψ proj μ M i y ξ G j) :
    ∀ t, 1 ≤ t → t ≤ j →
      P[fun ω => ‖saPath proj gψ μ i (y ω) (fun s => ξ s ω) t - xhat (y ω) i‖ ^ 2 | Fk]
        ≤ᵐ[P] fun _ => LeiBR.Sync.Qconst X M μ i / ((t : ℝ) + 1) := by
  -- unpack Assumption 1(a)-(b)
  obtain ⟨V, hV, hsm, hcvx⟩ := hA1.smooth
  set U : Set (LeiBR.Sync.Profile n) := Set.univ.pi V with hUdef
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun l _ => (hV l).1
  set S : Set (LeiBR.Sync.Profile n) := profileSet X with hSdef
  have hSU : S ⊆ U := Set.pi_mono fun l _ => (hV l).2.2
  have hf : ContDiffOn ℝ 2 (f i) U := hsm i
  have hXicv : Convex ℝ (X i) := hA1.convex i
  set Q := LeiBR.Sync.Qconst X M μ i with hQdef
  set D := Metric.diam (X i) with hDdef
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have hQ0 : 0 ≤ Q := by rw [hQdef]; unfold LeiBR.Sync.Qconst; positivity
  have hdist : ∀ u v : LeiBR.Sync.Strat n i, u ∈ X i → v ∈ X i → ‖u - v‖ ≤ D :=
    fun u v hu hv => by
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem (hA1.compact i).isBounded hu hv
  have hpc : Continuous (proj i) := proj_continuous hXicv (hproj i)
  set z : ℕ → Ω → LeiBR.Sync.Strat n i :=
    fun m ω => saPath proj gψ μ i (y ω) (fun s => ξ s ω) m with hzdef
  set xh : Ω → LeiBR.Sync.Strat n i := fun ω => xhat (y ω) i with hxhdef
  have hzX : ∀ m ω, z m ω ∈ X i := fun m ω => saPath_mem X proj hproj gψ μ i (hyX ω) _ m
  have hxhX : ∀ ω, xh ω ∈ X i := fun ω => (hxhat (y ω) (hyX ω) i).1
  have hyU : ∀ ω, ∀ w ∈ X i, Function.update (y ω) i w ∈ U :=
    fun ω w hw => hSU (feas_update (hyX ω) i hw)
  have hcX : ∀ ω, ConvexOn ℝ (X i) (fun w => f i (Function.update (y ω) i w)) :=
    fun ω => (hcvx i (y ω) (hyX ω)).subset (hV i).2.2 hXicv
  -- σ-algebra monotonicity & measurability
  have hFGm : ∀ m : ℕ, Fk ≤ G (m + 1) := by
    intro m
    induction m with
    | zero => exact hFG
    | succ m ih => exact ih.trans (hGmono (m + 1))
  have hym' : Measurable y := hy.mono hFk le_rfl
  have hxhm : Measurable[Fk] xh := by
    have hc : ContinuousOn (fun w => xhat w i) S := xhat_contOn X f hA1 hμ hxhat i
    have hc' := hc.domRestrict
    have hm : Measurable[Fk] fun ω : Ω => (⟨y ω, hyX ω⟩ : S) := hy.subtype_mk
    exact @Measurable.comp Ω S _ Fk _ _ _ _ hc'.measurable hm
  have hxhm' : Measurable xh := hxhm.mono hFk le_rfl
  have hzm : ∀ m : ℕ, m + 1 ≤ j → Measurable[G (m + 1)] (z (m + 1)) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact (@measurable_pi_apply _ _ _ i).comp (hy.mono hFG le_rfl)
    | succ m ih =>
      intro hm
      have hz := (ih (by omega)).mono (hGmono (m + 1)) le_rfl
      have hy' : Measurable[G (m + 2)] y := hy.mono (hFGm (m + 1)) le_rfl
      have hs : Measurable[G (m + 2)] (ξ (m + 1)) := hξ (m + 1) (by omega)
      exact @meas_step N n Ω (G (m + 2)) d i (proj i) hpc (gψ i) (hgψ i)
        y hy' (z (m + 1)) hz (ξ (m + 1)) hs (1 / (μ * ((m : ℝ) + 2))) μ
  have hzm' : ∀ m : ℕ, m + 1 ≤ j → Measurable (z (m + 1)) :=
    fun m hm => (hzm m hm).mono (hG (m + 1) hm) le_rfl
  -- sampled gradient (only needed for m + 1 < j, where ξ (m + 1) is G (m + 2)-measurable ≤ mΩ)
  set Gs : ℕ → Ω → LeiBR.Sync.Strat n i :=
    fun m ω => gψ i (Function.update (y ω) i (z m ω)) (ξ m ω) with hGs
  have hGm : ∀ m : ℕ, m + 1 < j → Measurable (Gs (m + 1)) := fun m hm =>
    (hgψ i).comp ((measurable_update'.comp (hym'.prodMk (hzm' m (by omega)))).prodMk
      ((hξ (m + 1) hm).mono (hG (m + 2) (by omega)) le_rfl))
  have hGi : ∀ m : ℕ, m + 1 < j → Integrable (Gs (m + 1)) P := by
    intro m hm
    have hG2I := (horacle (m + 1) (by omega) (by omega)).1
    refine Integrable.mono' (((integrable_const (1 : ℝ)).add hG2I).div_const 2)
      (hGm m hm).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := sq_nonneg (‖Gs (m + 1) ω‖ - 1)
    simp only [Pi.add_apply]
    nlinarith
  -- integrated recursion over any Fk-measurable set A
  have hrec : ∀ A, MeasurableSet[Fk] A → ∀ m : ℕ, m + 1 ≤ j →
      ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2 ∂P ≤
        Q / ((m : ℝ) + 2) * P.real A := by
    intro A hA m
    have hAm : MeasurableSet A := hFk _ hA
    have hind0 : ∀ ω, 0 ≤ A.indicator (1 : Ω → ℝ) ω := fun ω => by
      by_cases h : ω ∈ A <;> simp [h]
    have hind1 : ∀ ω, A.indicator (1 : Ω → ℝ) ω ≤ 1 := fun ω => by
      by_cases h : ω ∈ A <;> simp [h]
    have hindm : Measurable[Fk] (A.indicator (1 : Ω → ℝ)) := measurable_const.indicator hA
    have hindm' : Measurable (A.indicator (1 : Ω → ℝ)) := measurable_const.indicator hAm
    have hintc : ∀ c : ℝ, ∫ ω, A.indicator (1 : Ω → ℝ) ω * c ∂P = c * P.real A := by
      intro c
      simp_rw [mul_comm _ c]
      rw [integral_const_mul, integral_indicator_one hAm]
    have hindI : ∀ c : ℝ, Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * c) P := fun c =>
      (integrable_const c).bdd_mul hindm'.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hind0 ω)]; exact hind1 ω)
    have hXint : ∀ m : ℕ, m + 1 ≤ j →
        Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2) P := by
      intro m hm
      refine Integrable.of_bound
        ((hindm'.mul (((hzm' m hm).sub hxhm').norm.pow_const 2))).aestronglyMeasurable
        (D ^ 2) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hind0 ω) (sq_nonneg _))]
      calc A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2 ≤ 1 * D ^ 2 :=
            mul_le_mul (hind1 ω)
              (pow_le_pow_left₀ (norm_nonneg _) (hdist _ _ (hzX _ ω) (hxhX ω)) 2)
              (sq_nonneg _) zero_le_one
        _ = D ^ 2 := one_mul _
    have hPA : 0 ≤ P.real A := measureReal_nonneg
    induction m with
    | zero =>
      intro hmj
      have h1 : ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (0 + 1) ω - xh ω‖ ^ 2 ∂P ≤
          ∫ ω, A.indicator (1 : Ω → ℝ) ω * D ^ 2 ∂P :=
        integral_mono (hXint 0 hmj) (hindI _)
          (fun ω => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hdist _ _ (hzX _ ω) (hxhX ω)) 2) (hind0 ω))
      rw [hintc] at h1
      refine h1.trans ?_
      have : D ^ 2 ≤ Q / ((0 : ℕ) + 2 : ℝ) := by
        rw [hQdef]; unfold LeiBR.Sync.Qconst; push_cast
        rw [le_div_iff₀ (by norm_num)]
        have : 0 ≤ 2 * M i ^ 2 / μ ^ 2 := by positivity
        rw [← hDdef]; linarith
      exact mul_le_mul_of_nonneg_right this hPA
    | succ m ih =>
      intro hmj
      have hm1j : m + 1 ≤ j := by omega
      have hm1lt : m + 1 < j := by omega
      have ih := ih hm1j
      set γ : ℝ := 1 / (μ * ((m : ℝ) + 2)) with hγ
      have hγ0 : 0 ≤ γ := by positivity
      set Gd : Ω → LeiBR.Sync.Strat n i := fun ω => Gs (m + 1) ω + μ • (z (m + 1) ω - y ω i) with hGd
      have hz2 : ∀ ω, z (m + 1 + 1) ω = proj i (z (m + 1) ω - γ • Gd ω) := fun ω => rfl
      have hpt : ∀ ω, ‖z (m + 1 + 1) ω - xh ω‖ ^ 2 ≤ ‖z (m + 1) ω - xh ω‖ ^ 2
          - 2 * γ * inner ℝ (Gd ω) (z (m + 1) ω - xh ω) + γ ^ 2 * ‖Gd ω‖ ^ 2 := by
        intro ω
        rw [hz2]
        have h1 := proj_toward hXicv (hproj i) (z (m + 1) ω - γ • Gd ω) (xh ω) (hxhX ω)
        have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        have e : z (m + 1) ω - γ • Gd ω - xh ω = (z (m + 1) ω - xh ω) - γ • Gd ω := by abel
        rw [e, norm_sub_sq_real (z (m + 1) ω - xh ω) (γ • Gd ω), norm_smul, inner_smul_right,
          real_inner_comm, Real.norm_eq_abs, abs_of_nonneg hγ0, mul_pow] at h2
        linarith
      have hor := horacle (m + 1) (by omega) hm1j
      have hGI := hGi m hm1lt
      have hG2I := hor.1
      have hunb := hor.2.1
      have hvar := hor.2.2
      have hGle : G (m + 1) ≤ mΩ := hG (m + 1) hm1j
      have hyi : Measurable fun ω => y ω i := (measurable_pi_apply i).comp hym'
      have hdy : ∀ ω, ‖z (m + 1) ω - y ω i‖ ≤ D := fun ω =>
        hdist _ _ (hzX _ ω) (Set.mem_univ_pi.1 (hyX ω) i)
      have hdw : ∀ ω, ‖z (m + 1) ω - xh ω‖ ≤ D := fun ω => hdist _ _ (hzX _ ω) (hxhX ω)
      -- w = 1_A (z - x̂), measurable for G (m + 1)
      set w : Ω → LeiBR.Sync.Strat n i := fun ω => A.indicator (1 : Ω → ℝ) ω • (z (m + 1) ω - xh ω) with hw
      have hwm : StronglyMeasurable[G (m + 1)] w :=
        ((hindm.mono (hFGm m) le_rfl).smul ((hzm m hm1j).sub (hxhm.mono (hFGm m) le_rfl))).stronglyMeasurable
      have hwb : ∀ ω, ‖w ω‖ ≤ D := fun ω => by
        simp only [hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hind0 ω)]
        calc A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ≤ 1 * D :=
              mul_le_mul (hind1 ω) (hdw ω) (norm_nonneg _) zero_le_one
          _ = D := one_mul _
      have hwm' : Measurable w := (hwm.mono hGle).measurable
      have hinnG : Integrable (fun ω => inner ℝ (w ω) (Gs (m + 1) ω)) P := by
        refine Integrable.mono' (hGI.norm.const_mul D) (hwm'.inner (hGm m hm1lt)).aestronglyMeasurable
          (ae_of_all _ fun ω => ?_)
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hwb ω) (norm_nonneg _))
      -- unbiasedness: ∫ ⟨w, Gs⟩ = ∫ ⟨w, ∇⟩
      have hunbI : ∫ ω, inner ℝ (w ω) (Gs (m + 1) ω) ∂P =
          ∫ ω, inner ℝ (w ω) (partialGrad (f i) i (Function.update (y ω) i (z (m + 1) ω))) ∂P := by
        rw [← integral_condExp hGle]
        have hpull := condExp_bilin_of_stronglyMeasurable_left (m := G (m + 1)) (μ := P)
          (innerSL ℝ) hwm (f := w) (g := Gs (m + 1)) hinnG hGI
        refine integral_congr_ae ?_
        filter_upwards [hpull, hunb] with ω h1 h2
        refine h1.trans ?_
        show inner ℝ (w ω) _ = _
        rw [h2]
      -- the strong-monotonicity integral
      have hI1 : μ * ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2 ∂P ≤
          ∫ ω, A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω) ∂P := by
        have e1 : ∀ ω, A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω) =
            inner ℝ (w ω) (Gs (m + 1) ω) +
              μ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (z (m + 1) ω - y ω i) (z (m + 1) ω - xh ω)) := by
          intro ω
          simp only [hw, hGd, inner_add_left, real_inner_smul_left, real_inner_smul_right,
            real_inner_comm (Gs (m + 1) ω)]
          ring
        have hdetI : Integrable (fun ω => μ * (A.indicator (1 : Ω → ℝ) ω *
            inner ℝ (z (m + 1) ω - y ω i) (z (m + 1) ω - xh ω))) P := by
          have hmeas_det : Measurable fun ω => μ * (A.indicator (1 : Ω → ℝ) ω *
              inner ℝ (z (m + 1) ω - y ω i) (z (m + 1) ω - xh ω)) :=
            measurable_const.mul (hindm'.mul (((hzm' m hm1j).sub hyi).inner ((hzm' m hm1j).sub hxhm')))
          refine Integrable.of_bound hmeas_det.aestronglyMeasurable
            (μ * (D * D)) (ae_of_all _ fun ω => ?_)
          rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_pos hμ, Real.norm_eq_abs,
            abs_of_nonneg (hind0 ω)]
          refine mul_le_mul_of_nonneg_left ?_ hμ.le
          calc A.indicator (1 : Ω → ℝ) ω * ‖inner ℝ (z (m + 1) ω - y ω i) (z (m + 1) ω - xh ω)‖
              ≤ 1 * (D * D) := mul_le_mul (hind1 ω)
                ((norm_inner_le_norm _ _).trans (mul_le_mul (hdy ω) (hdw ω) (norm_nonneg _) hD0))
                (norm_nonneg _) zero_le_one
            _ = D * D := one_mul _
        have hcI : Integrable (fun ω => inner ℝ (w ω) (P[Gs (m + 1) | G (m + 1)] ω)) P := by
          refine Integrable.mono'
            ((integrable_condExp (f := Gs (m + 1)) (m := G (m + 1)) (μ := P)).norm.const_mul D)
            (hwm'.aestronglyMeasurable.inner
              (((stronglyMeasurable_condExp (f := Gs (m + 1)) (m := G (m + 1))
                (μ := P)).mono hGle).aestronglyMeasurable))
            (ae_of_all _ fun ω => ?_)
          rw [Real.norm_eq_abs]
          exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (hwb ω) (norm_nonneg _))
        have hgI : Integrable (fun ω => inner ℝ (w ω)
            (partialGrad (f i) i (Function.update (y ω) i (z (m + 1) ω)))) P := by
          refine hcI.congr ?_
          filter_upwards [hunb] with ω h
          show inner ℝ (w ω) _ = inner ℝ (w ω) _
          rw [h]
        simp_rw [e1]
        rw [integral_add hinnG hdetI, hunbI, ← integral_add hgI hdetI, ← integral_const_mul]
        refine integral_mono ((hXint m hm1j).const_mul μ) (hgI.add hdetI) fun ω => ?_
        have hs := strong_ineq hUo hf i hXicv (y ω) (hyU ω) (hcX ω) (hxhX ω)
          (hxhat (y ω) (hyX ω) i).2 (z (m + 1) ω) (hzX _ ω)
        have e2 : inner ℝ (w ω) (partialGrad (f i) i (Function.update (y ω) i (z (m + 1) ω))) +
            μ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (z (m + 1) ω - y ω i) (z (m + 1) ω - xh ω)) =
            A.indicator (1 : Ω → ℝ) ω * inner ℝ (partialGrad (f i) i
              (Function.update (y ω) i (z (m + 1) ω)) + μ • (z (m + 1) ω - y ω i))
              (z (m + 1) ω - xh ω) := by
          simp only [hw, inner_add_left, real_inner_smul_left]
          rw [real_inner_comm (z (m + 1) ω - xh ω)
            (partialGrad (f i) i (Function.update (y ω) i (z (m + 1) ω)))]
          ring
        rw [e2]
        calc μ * (A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2)
            = A.indicator (1 : Ω → ℝ) ω * (μ * ‖z (m + 1) ω - xhat (y ω) i‖ ^ 2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hs (hind0 ω)
      -- second moment
      have hGd2 : ∀ ω, ‖Gd ω‖ ^ 2 ≤ 2 * ‖Gs (m + 1) ω‖ ^ 2 + 2 * μ ^ 2 * D ^ 2 := by
        intro ω
        have h1 := norm_add_le (Gs (m + 1) ω) (μ • (z (m + 1) ω - y ω i))
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at h1
        have h2 : μ * ‖z (m + 1) ω - y ω i‖ ≤ μ * D := mul_le_mul_of_nonneg_left (hdy ω) hμ.le
        have h4 : ‖Gd ω‖ ≤ ‖Gs (m + 1) ω‖ + μ * D := h1.trans (by linarith)
        have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
        have hD0' : 0 ≤ μ * D := by positivity
        nlinarith [sq_nonneg (‖Gs (m + 1) ω‖ - μ * D)]
      have hGdm : Measurable Gd := (hGm m hm1lt).add (((hzm' m hm1j).sub hyi).const_smul μ)
      have hiZ : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2) P := by
        refine Integrable.mono' ((hG2I.const_mul 2).add (integrable_const (2 * μ ^ 2 * D ^ 2)))
          (hindm'.mul (hGdm.norm.pow_const 2)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hind0 ω) (sq_nonneg _))]
        calc A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2 ≤ 1 * ‖Gd ω‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (hind1 ω) (sq_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact hGd2 ω
      have hAG : ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖Gs (m + 1) ω‖ ^ 2 ∂P ≤ M i ^ 2 * P.real A := by
        have hAGi : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ‖Gs (m + 1) ω‖ ^ 2) P :=
          hG2I.bdd_mul hindm'.aestronglyMeasurable
            (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hind0 ω)]; exact hind1 ω)
        rw [← integral_condExp hGle, ← hintc]
        have hpull := condExp_mul_of_stronglyMeasurable_left (m := G (m + 1))
          (μ := P) (f := A.indicator (1 : Ω → ℝ)) (g := fun ω => ‖Gs (m + 1) ω‖ ^ 2)
          ((hindm.mono (hFGm m) le_rfl).stronglyMeasurable) hAGi hG2I
        refine integral_mono_ae integrable_condExp (hindI _) ?_
        filter_upwards [hpull, hvar] with ω h1 h2
        have h1' : (P[fun ω => A.indicator (1 : Ω → ℝ) ω * ‖Gs (m + 1) ω‖ ^ 2 | G (m + 1)]) ω =
            A.indicator (1 : Ω → ℝ) ω * (P[fun ω => ‖Gs (m + 1) ω‖ ^ 2 | G (m + 1)]) ω := h1
        rw [h1']
        exact mul_le_mul_of_nonneg_left h2 (hind0 ω)
      have hI2 : ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2 ∂P ≤
          (2 * M i ^ 2 + 2 * μ ^ 2 * D ^ 2) * P.real A := by
        have hAGi : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ‖Gs (m + 1) ω‖ ^ 2) P :=
          hG2I.bdd_mul hindm'.aestronglyMeasurable
            (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hind0 ω)]; exact hind1 ω)
        calc ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2 ∂P
            ≤ ∫ ω, (2 * (A.indicator (1 : Ω → ℝ) ω * ‖Gs (m + 1) ω‖ ^ 2) +
                A.indicator (1 : Ω → ℝ) ω * (2 * μ ^ 2 * D ^ 2)) ∂P := by
              refine integral_mono hiZ ((hAGi.const_mul 2).add (hindI _)) fun ω => ?_
              have := mul_le_mul_of_nonneg_left (hGd2 ω) (hind0 ω)
              simp only
              nlinarith
          _ = 2 * ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖Gs (m + 1) ω‖ ^ 2 ∂P +
                (2 * μ ^ 2 * D ^ 2) * P.real A := by
              rw [integral_add (hAGi.const_mul 2) (hindI _), integral_const_mul, hintc]
          _ ≤ 2 * (M i ^ 2 * P.real A) + (2 * μ ^ 2 * D ^ 2) * P.real A := by linarith
          _ = (2 * M i ^ 2 + 2 * μ ^ 2 * D ^ 2) * P.real A := by ring
      have hiY : Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω *
          inner ℝ (Gd ω) (z (m + 1) ω - xh ω)) P := by
        refine Integrable.mono' ((hGI.norm.add (integrable_const (μ * D))).mul_const D)
          (hindm'.mul (hGdm.inner ((hzm' m hm1j).sub hxhm'))).aestronglyMeasurable
          (ae_of_all _ fun ω => ?_)
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hind0 ω)]
        have hGdn : ‖Gd ω‖ ≤ ‖Gs (m + 1) ω‖ + μ * D := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
          linarith [mul_le_mul_of_nonneg_left (hdy ω) hμ.le]
        calc A.indicator (1 : Ω → ℝ) ω * ‖inner ℝ (Gd ω) (z (m + 1) ω - xh ω)‖
            ≤ 1 * ((‖Gs (m + 1) ω‖ + μ * D) * D) :=
              mul_le_mul (hind1 ω) ((norm_inner_le_norm _ _).trans
                (mul_le_mul hGdn (hdw ω) (norm_nonneg _) (by positivity))) (norm_nonneg _) zero_le_one
          _ = _ := by simp
      have hmono : ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1 + 1) ω - xh ω‖ ^ 2 ∂P ≤
          ∫ ω, (A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2
            - 2 * γ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω))
            + γ ^ 2 * (A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2)) ∂P := by
        refine integral_mono (hXint (m + 1) hmj) (((hXint m hm1j).sub (hiY.const_mul (2 * γ))).add
          (hiZ.const_mul (γ ^ 2))) fun ω => ?_
        have := mul_le_mul_of_nonneg_left (hpt ω) (hind0 ω)
        simp only at this ⊢
        nlinarith [this]
      rw [integral_add (f := fun ω => A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2
            - 2 * γ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω)))
          (g := fun ω => γ ^ 2 * (A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2))
          ((hXint m hm1j).sub (hiY.const_mul _)) (hiZ.const_mul _),
        integral_sub (f := fun ω => A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2)
          (g := fun ω => 2 * γ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω)))
          (hXint m hm1j) (hiY.const_mul _), integral_const_mul, integral_const_mul] at hmono
      have hr2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
      have hQe : Q = 2 * M i ^ 2 / μ ^ 2 + 2 * D ^ 2 := by rw [hQdef, hDdef]; rfl
      have := arith_step _ _ _ γ μ (M i ^ 2) D Q (P.real A) ((m : ℝ) + 2) hμ hr2 hγ hQe hQ0 hPA
        hI1 hI2 ih
      have hc : (((m + 1 : ℕ) : ℝ) + 2) = (m : ℝ) + 2 + 1 := by push_cast; ring
      rw [hc]
      exact hmono.trans this
  -- conclusion
  intro t ht1 htj
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hfi : Integrable (fun ω => ‖z (m + 1) ω - xh ω‖ ^ 2) P := by
    refine Integrable.of_bound (((hzm' m htj).sub hxhm').norm.pow_const 2).aestronglyMeasurable (D ^ 2)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdist _ _ (hzX _ ω) (hxhX ω)) 2
  refine ae_of_ae_trim hFk ?_
  have hint1 : Integrable (P[fun ω => ‖z (m + 1) ω - xh ω‖ ^ 2 | Fk]) (P.trim hFk) :=
    integrable_condExp.trim hFk stronglyMeasurable_condExp
  have hint2 : Integrable (fun _ : Ω => Q / (((m + 1 : ℕ) : ℝ) + 1)) (P.trim hFk) :=
    integrable_const _
  refine ae_le_of_forall_setIntegral_le hint1 hint2 fun S' hS' _ => ?_
  rw [← setIntegral_trim hFk stronglyMeasurable_condExp hS',
    ← setIntegral_trim hFk stronglyMeasurable_const hS', setIntegral_condExp hFk hfi hS',
    setIntegral_const]
  have h := hrec S' hS' m htj
  have e : (fun ω => S'.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2) =
      S'.indicator (fun ω => ‖z (m + 1) ω - xh ω‖ ^ 2) := by
    funext ω; by_cases hω : ω ∈ S' <;> simp [hω]
  rw [e, integral_indicator (hFk _ hS')] at h
  have hc : Q / ((m : ℝ) + 2) = Q / (((m + 1 : ℕ) : ℝ) + 1) := by push_cast; ring_nf
  rw [hc] at h
  rw [smul_eq_mul, mul_comm]
  exact h
