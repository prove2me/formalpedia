-- Prove2me | solution 1 for LeiBR.Sync.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T12:07:07.106871+00:00
-- url     : https://prove2.me/submissions/a35c2588-9ef5-483c-8fc5-7892f61fef2a

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame
import Definitions.Def_LeiBR_Sync_Algorithm1
import Theorems.Thm_LeiBR_Sync_eq_5

open MeasureTheory

namespace LeiBRSL3
open LeiBR.Sync

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

variable {N : ℕ} {n : Fin N → ℕ}

lemma meas_step {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (i : Fin N)
    (pr : Strat n i → Strat n i) (hpr : Continuous pr)
    (g : Profile n → EuclideanSpace ℝ (Fin d) → Strat n i)
    (hg : Measurable (fun p : Profile n × EuclideanSpace ℝ (Fin d) => g p.1 p.2))
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

lemma saIter_ss {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (G : E → S → E) (μ : ℝ) (yi : E) (ξ : ℕ → S) (t : ℕ) :
    saIter proj G μ yi ξ (t + 2) = proj (saIter proj G μ yi ξ (t + 1) -
      (1 / (μ * ((t : ℝ) + 2))) • (G (saIter proj G μ yi ξ (t + 1)) (ξ (t + 1)) +
        μ • (saIter proj G μ yi ξ (t + 1) - yi))) := rfl

lemma comap_le_infoField {Ω : Type*} {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (k l : ℕ) (hl : l < k) (i : Fin N)
    (t : ℕ) (ht : 1 ≤ t ∧ t ≤ j i l) :
    MeasurableSpace.comap (ξs l i t) inferInstance ≤ infoField j ξs k := by
  unfold infoField
  refine le_trans ?_ (le_iSup _ l)
  refine le_trans ?_ (le_iSup _ hl)
  refine le_trans ?_ (le_iSup _ i)
  refine le_trans ?_ (le_iSup _ t)
  exact le_iSup (fun _ : (1 ≤ t ∧ t ≤ j i l) => MeasurableSpace.comap (ξs l i t) inferInstance) ht

lemma infoField_mono {Ω : Type*} {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) {k k' : ℕ} (h : k ≤ k') :
    infoField j ξs k ≤ infoField j ξs k' := by
  conv_lhs => unfold infoField
  refine iSup_le fun l => iSup_le fun hl => iSup_le fun i => iSup_le fun t => iSup_le fun ht => ?_
  exact comap_le_infoField j ξs k' l (lt_of_lt_of_le hl h) i t ht

lemma infoField_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hξs : ∀ k (i : Fin N) t, Measurable (ξs k i t)) (k : ℕ) :
    infoField j ξs k ≤ mΩ := by
  unfold infoField
  refine iSup_le fun l => iSup_le fun _ => iSup_le fun i => iSup_le fun t => iSup_le fun _ => ?_
  exact measurable_iff_comap_le.1 (hξs l i t)

lemma syncSA_meas {Ω : Type*} {d : ℕ} (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (hpc : ∀ i, Continuous (proj i))
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i)
    (hgψ : ∀ i : Fin N,
      Measurable (fun p : Profile n × EuclideanSpace ℝ (Fin d) => gψ i p.1 p.2)) (μ : ℝ)
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (x0 : Profile n) :
    ∀ k, Measurable[infoField j ξs k] (syncSA proj gψ μ j ξs x0 k) := by
  intro k
  induction k with
  | zero => exact @measurable_const _ _ _ (infoField j ξs 0) _
  | succ k ih =>
    have ih' : Measurable[infoField j ξs (k + 1)] (syncSA proj gψ μ j ξs x0 k) :=
      Measurable.mono ih (infoField_mono j ξs (Nat.le_succ k)) le_rfl
    have key : ∀ i : Fin N, ∀ t, t ≤ j i k →
        Measurable[infoField j ξs (k + 1)] (saZ proj gψ μ j ξs x0 k i t) := by
      intro i t
      induction t using Nat.strong_induction_on with
      | _ t iht =>
        intro ht
        match t, iht, ht with
        | 0, _, _ => exact (@measurable_pi_apply _ _ _ i).comp ih'
        | 1, _, _ => exact (@measurable_pi_apply _ _ _ i).comp ih'
        | t + 2, iht, ht =>
          have hz := iht (t + 1) (by omega) (by omega)
          have hs : Measurable[infoField j ξs (k + 1)] (ξs k i (t + 1)) :=
            measurable_iff_comap_le.2
              (comap_le_infoField j ξs (k + 1) k (Nat.lt_succ_self k) i (t + 1) ⟨by omega, by omega⟩)
          exact @meas_step N n Ω (infoField j ξs (k + 1)) d i (proj i) (hpc i) (gψ i) (hgψ i)
            (syncSA proj gψ μ j ξs x0 k) ih' (saZ proj gψ μ j ξs x0 k i (t + 1)) hz
            (ξs k i (t + 1)) hs (1 / (μ * ((t : ℝ) + 2))) μ
    exact @measurable_pi_lambda _ _ _ (infoField j ξs (k + 1)) _ _
      (fun i => key i (j i k) le_rfl)

lemma syncSA_mem {Ω : Type*} {d : ℕ} (X : ∀ i : Fin N, Set (Strat n i))
    (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (hproj : ∀ i : Fin N, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (μ : ℝ)
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (x0 : Profile n)
    (hx0 : x0 ∈ stratSet X) : ∀ k ω, syncSA proj gψ μ j ξs x0 k ω ∈ stratSet X := by
  intro k
  induction k with
  | zero => intro ω; exact hx0
  | succ k ih =>
    intro ω
    simp only [stratSet, Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    show saIter _ _ μ _ _ (j i k) ∈ X i
    match j i k with
    | 0 => exact (Set.mem_univ_pi.1 (ih ω)) i
    | 1 => exact (Set.mem_univ_pi.1 (ih ω)) i
    | t + 2 => rw [saIter_ss]; exact (hproj i _).1


lemma cdAt {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) : ContDiffAt ℝ 2 f x :=
  hf.contDiffAt (hU.mem_nhds hx)

lemma hasD1 {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((cdAt hU hf hx).differentiableAt (by norm_num)).hasFDerivAt

lemma hasD2 {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
  (((cdAt hU hf hx).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt

lemma symmD2 {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {x : Profile n} (hx : x ∈ U) (v w : Profile n) :
    fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ (fderiv ℝ f) x w v :=
  (cdAt hU hf hx).isSymmSndFDerivAt (by simp) v w

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

lemma mvt {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) {S : Set (Profile n)} (hS : Convex ℝ S) (hSU : S ⊆ U)
    {P P' : Profile n} (hP : P ∈ S) (hP' : P' ∈ S) (V : Profile n) :
    ∃ Q ∈ S, fderiv ℝ f P' V - fderiv ℝ f P V = fderiv ℝ (fderiv ℝ f) Q (P' - P) V := by
  set γ : ℝ → Profile n := fun s => P + s • (P' - P) with hγ
  have hγS : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ S := fun s hs => hS.add_smul_sub_mem hP hP' hs
  have hγd : ∀ s, HasDerivAt γ (P' - P) s := fun s => by
    have := ((hasDerivAt_id s).smul_const (P' - P)).const_add P
    simp only [id, one_smul] at this
    exact this
  have hcont : ContinuousOn (fun s => fderiv ℝ f (γ s) V) (Set.Icc 0 1) := by
    have h1 : ContinuousOn (fun s => fderiv ℝ f (γ s)) (Set.Icc 0 1) :=
      (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp
        (Continuous.continuousOn (by fun_prop)) (fun s hs => hSU (hγS s hs))
    exact h1.clm_apply continuousOn_const
  have hder : ∀ s ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun s => fderiv ℝ f (γ s) V)
      (fderiv ℝ (fderiv ℝ f) (γ s) (P' - P) V) s := by
    intro s hs
    have hc := (hasD2 hU hf (hSU (hγS s (Set.Ioo_subset_Icc_self hs)))).comp_hasDerivAt s (hγd s)
    have := hc.clm_apply (hasDerivAt_const s V)
    simpa using this
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope _ _ zero_lt_one hcont hder
  refine ⟨γ c, hγS c (Set.Ioo_subset_Icc_self hc), ?_⟩
  rw [hceq]
  simp [hγ]



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
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, pi_single_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul] at this
  convert this using 2
  simp only [id]
  ring


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


lemma saZ_mem {Ω : Type*} {d : ℕ} (X : ∀ i : Fin N, Set (Strat n i))
    (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (hproj : ∀ i : Fin N, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (μ : ℝ)
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (x0 : Profile n)
    (hx0 : x0 ∈ stratSet X) (k : ℕ) (i : Fin N) (t : ℕ) (ω : Ω) :
    saZ proj gψ μ j ξs x0 k i t ω ∈ X i := by
  have hy := Set.mem_univ_pi.1 (syncSA_mem X proj hproj gψ μ j ξs x0 hx0 k ω) i
  unfold saZ
  match t with
  | 0 => exact hy
  | 1 => exact hy
  | t + 2 => rw [saIter_ss]; exact (hproj i _).1

lemma infoField_le_inner {Ω : Type*} {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (k : ℕ) (i : Fin N) (t : ℕ) :
    infoField j ξs k ≤ innerField j ξs k i t := le_sup_left

lemma comap_le_inner {Ω : Type*} {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (k : ℕ) (i : Fin N) (t s : ℕ)
    (hs : 1 ≤ s ∧ s < t) :
    MeasurableSpace.comap (ξs k i s) inferInstance ≤ innerField j ξs k i t := by
  unfold innerField
  refine le_trans ?_ le_sup_right
  refine le_trans ?_ (le_iSup _ s)
  exact le_iSup (fun _ : (1 ≤ s ∧ s < t) => MeasurableSpace.comap (ξs k i s) inferInstance) hs

lemma inner_mono {Ω : Type*} {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (k : ℕ) (i : Fin N) {t t' : ℕ}
    (h : t ≤ t') : innerField j ξs k i t ≤ innerField j ξs k i t' := by
  conv_lhs => unfold innerField
  refine sup_le (infoField_le_inner j ξs k i t') ?_
  refine iSup_le fun s => iSup_le fun hs => ?_
  exact comap_le_inner j ξs k i t' s ⟨hs.1, lt_of_lt_of_le hs.2 h⟩

lemma inner_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} (j : Fin N → ℕ → ℕ)
    (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hξs : ∀ k (i : Fin N) t, Measurable (ξs k i t)) (k : ℕ) (i : Fin N) (t : ℕ) :
    innerField j ξs k i t ≤ mΩ := by
  unfold innerField
  refine sup_le (infoField_le j ξs hξs k) ?_
  refine iSup_le fun s => iSup_le fun _ => ?_
  exact measurable_iff_comap_le.1 (hξs k i s)

lemma saZ_meas {Ω : Type*} {d : ℕ} (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (hpc : ∀ i, Continuous (proj i))
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i)
    (hgψ : ∀ i : Fin N,
      Measurable (fun p : Profile n × EuclideanSpace ℝ (Fin d) => gψ i p.1 p.2)) (μ : ℝ)
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d)) (x0 : Profile n)
    (k : ℕ) (i : Fin N) :
    ∀ m : ℕ, Measurable[innerField j ξs k i (m + 1)] (saZ proj gψ μ j ξs x0 k i (m + 1)) := by
  have hy : Measurable[innerField j ξs k i 0] (syncSA proj gψ μ j ξs x0 k) :=
    Measurable.mono (syncSA_meas proj hpc gψ hgψ μ j ξs x0 k) (infoField_le_inner j ξs k i 0) le_rfl
  intro m
  induction m with
  | zero =>
    exact (@measurable_pi_apply _ _ _ i).comp (hy.mono (inner_mono j ξs k i (by omega)) le_rfl)
  | succ m ih =>
    have hz := ih.mono (inner_mono j ξs k i (by omega : m + 1 ≤ m + 1 + 1)) le_rfl
    have hs : Measurable[innerField j ξs k i (m + 1 + 1)] (ξs k i (m + 1)) :=
      measurable_iff_comap_le.2 (comap_le_inner j ξs k i (m + 1 + 1) (m + 1) ⟨by omega, by omega⟩)
    exact @meas_step N n Ω (innerField j ξs k i (m + 1 + 1)) d i (proj i) (hpc i) (gψ i) (hgψ i)
      (syncSA proj gψ μ j ξs x0 k) (hy.mono (inner_mono j ξs k i (by omega)) le_rfl)
      (saZ proj gψ μ j ξs x0 k i (m + 1)) hz (ξs k i (m + 1)) hs (1 / (μ * ((m : ℝ) + 2))) μ

lemma grad_inner {f : Profile n → ℝ} {U : Set (Profile n)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (i : Fin N) (y : Profile n) (z : Strat n i)
    (hP : Function.update y i z ∈ U) (v : Strat n i) :
    inner ℝ (partialGrad (fun _ => f) i (Function.update y i z)) v =
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
  have hγX : ∀ s ∈ Set.Icc (0:ℝ) 1, γ s ∈ Xi := fun s hs => hXi.add_smul_sub_mem ha hz hs
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
  have hkd : ∀ s ∈ Set.Icc (0:ℝ) 1,
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
      inner ℝ (partialGrad (fun _ => f) i (Function.update y i z) + mu • (z - y i)) (z - u) := by
  have h1 := foc hU hf i hXi y hu (hyU u hu) hmin z hz
  have h2 := grad_mono hU hf i hXi y hyU hcX u z hu hz
  rw [inner_add_left, grad_inner hU hf i y z (hyU z hz), real_inner_smul_left]
  have e : inner ℝ (z - y i) (z - u) = inner ℝ (u - y i) (z - u) + ‖z - u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← inner_add_left]; congr 1; abel
  rw [e]
  nlinarith

end LeiBRSL3

open LeiBR.Sync LeiBRSL3 in
theorem solution
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (hproj : ∀ i : Fin N, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (hgψ : ∀ i : Fin N,
      Measurable (fun p : Profile n × EuclideanSpace ℝ (Fin d) => gψ i p.1 p.2))
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hξs : ∀ k (i : Fin N) t, Measurable (ξs k i t))
    (x0 : Profile n) (hx0 : x0 ∈ stratSet X)
    (k : ℕ) (i : Fin N)
    (hint : ∀ t : ℕ, 1 ≤ t → t ≤ j i k →
      Integrable (fun ω => ‖gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i
        (saZ proj gψ μ j ξs x0 k i t ω)) (ξs k i t ω)‖ ^ 2) P)
    (hunb : ∀ t : ℕ, 1 ≤ t → t ≤ j i k →
      P[fun ω => gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i
          (saZ proj gψ μ j ξs x0 k i t ω)) (ξs k i t ω) | innerField j ξs k i t]
        =ᵐ[P] fun ω => partialGrad (payoff P ξ ψ) i
          (Function.update (syncSA proj gψ μ j ξs x0 k ω) i (saZ proj gψ μ j ξs x0 k i t ω)))
    (hvar : ∀ t : ℕ, 1 ≤ t → t ≤ j i k →
      P[fun ω => ‖gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i
          (saZ proj gψ μ j ξs x0 k i t ω)) (ξs k i t ω)‖ ^ 2 | innerField j ξs k i t]
        ≤ᵐ[P] fun _ => M i ^ 2) :
    ∀ t : ℕ, 1 ≤ t → t ≤ j i k →
      P[fun ω => ‖saZ proj gψ μ j ξs x0 k i t ω - xhat (syncSA proj gψ μ j ξs x0 k ω) i‖ ^ 2 |
          infoField j ξs k] ≤ᵐ[P] fun _ => Qconst X M μ i / ((t : ℝ) + 1) := by
  -- unpack Assumption 1
  have hMpos : 0 < M i := (hA1.2.choose_spec.2.2.2.2.2 i).1
  have hX := hA1.1
  obtain ⟨V, hV, -, hsm, hcvx, -, -⟩ := hA1.2
  set U : Set (Profile n) := Set.univ.pi V with hUdef
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun j _ => (hV j).1
  set S : Set (Profile n) := stratSet X with hSdef
  have hSU : S ⊆ U := Set.pi_mono fun j _ => (hV j).2.2
  set f := payoff P ξ ψ i with hfdef
  have hf : ContDiffOn ℝ 2 f U := hsm i
  have hXicv : Convex ℝ (X i) := (hX i).2.2.1
  set Q := Qconst X M μ i with hQdef
  set D := Metric.diam (X i) with hDdef
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have hQ0 : 0 ≤ Q := by rw [hQdef]; unfold Qconst; positivity
  have hdist : ∀ u v : Strat n i, u ∈ X i → v ∈ X i → ‖u - v‖ ≤ D := fun u v hu hv => by
    rw [← dist_eq_norm]; exact Metric.dist_le_diam_of_mem (hX i).2.1.isBounded hu hv
  have hpc : ∀ i, Continuous (proj i) := fun i => proj_continuous (hX i).2.2.1 (hproj i)
  set y : Ω → Profile n := syncSA proj gψ μ j ξs x0 k with hydef
  set z : ℕ → Ω → Strat n i := fun m ω => saZ proj gψ μ j ξs x0 k i m ω with hzdef
  set xh : Ω → Strat n i := fun ω => xhat (y ω) i with hxhdef
  have hyS : ∀ ω, y ω ∈ S := syncSA_mem X proj hproj gψ μ j ξs x0 hx0 k
  have hzX : ∀ m ω, z m ω ∈ X i := fun m ω => saZ_mem X proj hproj gψ μ j ξs x0 hx0 k i m ω
  have hxhX : ∀ ω, xh ω ∈ X i := fun ω => (hxhat (y ω) (hyS ω) i).1
  have hyU : ∀ ω, ∀ w ∈ X i, Function.update (y ω) i w ∈ U := by
    intro ω w hw
    refine hSU (Set.mem_univ_pi.2 fun l => ?_)
    by_cases h : l = i
    · subst h; simpa using hw
    · rw [Function.update_of_ne h]; exact Set.mem_univ_pi.1 (hyS ω) l
  have hcX : ∀ ω, ConvexOn ℝ (X i) (fun w => f (Function.update (y ω) i w)) := fun ω =>
    (hcvx i (y ω) (hyS ω)).subset (hV i).2.2 hXicv
  -- measurability
  have hFle : (infoField j ξs k) ≤ mΩ := infoField_le j ξs hξs k
  have hym : Measurable[(infoField j ξs k)] y := syncSA_meas proj hpc gψ hgψ μ j ξs x0 k
  have hym' : Measurable y := hym.mono hFle le_rfl
  have hxhm : Measurable[(infoField j ξs k)] xh := by
    have hc : ContinuousOn (fun w => xhat w i) S := by
      refine (LipschitzOnWith.of_dist_le_mul
        (K := Real.toNNReal (∑ l, |Gamma X (payoff P ξ ψ) μ i l|)) fun w hw w' hw' => ?_).continuousOn
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
      refine (eq_5 P ξ X ψ gψ M hA1 μ hμ xhat hxhat w' hw' w hw i).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun l _ => ?_
      refine (le_abs_self _ |> fun h => mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact norm_le_pi_norm (w - w') l
    have hc' := hc.domRestrict
    have hm : Measurable[(infoField j ξs k)] fun ω : Ω => (⟨y ω, hyS ω⟩ : S) := hym.subtype_mk
    exact @Measurable.comp Ω S _ (infoField j ξs k) _ _ _ _ hc'.measurable hm
  have hxhm' : Measurable xh := hxhm.mono hFle le_rfl
  have h𝒢le : ∀ m, (innerField j ξs k i m) ≤ mΩ := fun m => inner_le j ξs hξs k i m
  have hFG : ∀ m, (infoField j ξs k) ≤ (innerField j ξs k i m) := fun m => infoField_le_inner j ξs k i m
  have hzm : ∀ m, Measurable[(innerField j ξs k i (m + 1))] (z (m + 1)) := saZ_meas proj hpc gψ hgψ μ j ξs x0 k i
  have hzm' : ∀ m, Measurable (z (m + 1)) := fun m => (hzm m).mono (h𝒢le _) le_rfl
  -- sampled gradient
  set Gs : ℕ → Ω → Strat n i := fun m ω => gψ i (Function.update (y ω) i (z m ω)) (ξs k i m ω)
    with hGs
  have hGm : ∀ m, Measurable (Gs (m + 1)) := fun m =>
    (hgψ i).comp ((measurable_update'.comp (hym'.prodMk (hzm' m))).prodMk (hξs k i (m + 1)))
  have hGi : ∀ m, m + 1 ≤ j i k → Integrable (Gs (m + 1)) P := by
    intro m hm
    refine Integrable.mono' (((integrable_const (1 : ℝ)).add (hint (m + 1) (by omega) hm)).div_const 2)
      (hGm m).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := sq_nonneg (‖Gs (m + 1) ω‖ - 1)
    simp only [Pi.add_apply]
    nlinarith
  have hrec : ∀ A, MeasurableSet[(infoField j ξs k)] A → ∀ m : ℕ, m + 1 ≤ j i k →
      ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2 ∂P ≤
        Q / ((m : ℝ) + 2) * P.real A := by
    intro A hA m
    have hAm : MeasurableSet A := hFle _ hA
    have hind01 : ∀ ω, A.indicator (1 : Ω → ℝ) ω = 0 ∨ A.indicator (1 : Ω → ℝ) ω = 1 :=
      fun ω => by by_cases h : ω ∈ A <;> simp [h]
    have hind0 : ∀ ω, 0 ≤ A.indicator (1 : Ω → ℝ) ω := fun ω => by
      rcases hind01 ω with h | h <;> rw [h] <;> norm_num
    have hind1 : ∀ ω, A.indicator (1 : Ω → ℝ) ω ≤ 1 := fun ω => by
      rcases hind01 ω with h | h <;> rw [h] <;> norm_num
    have hindm : Measurable[(infoField j ξs k)] (A.indicator (1 : Ω → ℝ)) := measurable_const.indicator hA
    have hindm' : Measurable (A.indicator (1 : Ω → ℝ)) := measurable_const.indicator hAm
    have hintc : ∀ c : ℝ, ∫ ω, A.indicator (1 : Ω → ℝ) ω * c ∂P = c * P.real A := by
      intro c
      simp_rw [mul_comm _ c]
      rw [integral_const_mul, integral_indicator_one hAm]
    have hindI : ∀ c : ℝ, Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * c) P := fun c =>
      (integrable_const c).bdd_mul hindm'.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hind0 ω)]; exact hind1 ω)
    have hXint : ∀ m : ℕ,
        Integrable (fun ω => A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2) P := by
      intro m
      refine Integrable.of_bound
        ((hindm'.mul (((hzm' m).sub hxhm').norm.pow_const 2))).aestronglyMeasurable
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
      intro _
      have h1 : ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (0 + 1) ω - xh ω‖ ^ 2 ∂P ≤
          ∫ ω, A.indicator (1 : Ω → ℝ) ω * D ^ 2 ∂P :=
        integral_mono (hXint 0) (hindI _)
          (fun ω => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hdist _ _ (hzX _ ω) (hxhX ω)) 2) (hind0 ω))
      rw [hintc] at h1
      refine h1.trans ?_
      have : D ^ 2 ≤ Q / ((0 : ℕ) + 2 : ℝ) := by
        rw [hQdef]; unfold Qconst; push_cast
        rw [le_div_iff₀ (by norm_num)]
        have : 0 ≤ 2 * M i ^ 2 / μ ^ 2 := by positivity
        rw [← hDdef]; linarith
      exact mul_le_mul_of_nonneg_right this hPA
    | succ m ih =>
      intro hmj
      have ih := ih (by omega)
      set γ : ℝ := 1 / (μ * ((m : ℝ) + 2)) with hγ
      have hγ0 : 0 ≤ γ := by positivity
      set Gd : Ω → Strat n i := fun ω => Gs (m + 1) ω + μ • (z (m + 1) ω - y ω i) with hGd
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
      have hj1 : m + 1 ≤ j i k := by omega
      have hGI := hGi m hj1
      have hG2I := hint (m + 1) (by omega) hj1
      have hyi : Measurable fun ω => y ω i := (measurable_pi_apply i).comp hym'
      have hdy : ∀ ω, ‖z (m + 1) ω - y ω i‖ ≤ D := fun ω =>
        hdist _ _ (hzX _ ω) (Set.mem_univ_pi.1 (hyS ω) i)
      have hdw : ∀ ω, ‖z (m + 1) ω - xh ω‖ ≤ D := fun ω => hdist _ _ (hzX _ ω) (hxhX ω)
      -- w = 1_A (z - x̂), measurable for (innerField j ξs k i (m+1))
      set w : Ω → Strat n i := fun ω => A.indicator (1 : Ω → ℝ) ω • (z (m + 1) ω - xh ω) with hw
      have hwm : StronglyMeasurable[(innerField j ξs k i (m + 1))] w :=
        ((hindm.mono (hFG _) le_rfl).smul ((hzm m).sub (hxhm.mono (hFG _) le_rfl))).stronglyMeasurable
      have hwb : ∀ ω, ‖w ω‖ ≤ D := fun ω => by
        simp only [hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hind0 ω)]
        calc A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ≤ 1 * D :=
              mul_le_mul (hind1 ω) (hdw ω) (norm_nonneg _) zero_le_one
          _ = D := one_mul _
      have hwm' : Measurable w := (hwm.mono (h𝒢le _)).measurable
      have hinnG : Integrable (fun ω => inner ℝ (w ω) (Gs (m + 1) ω)) P := by
        refine Integrable.mono' (hGI.norm.const_mul D) (hwm'.inner (hGm m)).aestronglyMeasurable
          (ae_of_all _ fun ω => ?_)
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hwb ω) (norm_nonneg _))
      -- unbiasedness: ∫ ⟨w, G⟩ = ∫ ⟨w, ∇⟩
      have hunbI : ∫ ω, inner ℝ (w ω) (Gs (m + 1) ω) ∂P =
          ∫ ω, inner ℝ (w ω) (partialGrad (payoff P ξ ψ) i
            (Function.update (y ω) i (z (m + 1) ω))) ∂P := by
        rw [← integral_condExp (h𝒢le (m + 1))]
        have hpull := condExp_bilin_of_stronglyMeasurable_left (m := (innerField j ξs k i (m + 1))) (μ := P)
          (innerSL ℝ) hwm (f := w) (g := Gs (m + 1)) hinnG hGI
        refine integral_congr_ae ?_
        have hu := hunb (m + 1) (by omega) hj1
        filter_upwards [hpull, hu] with ω h1 h2
        refine h1.trans ?_
        show inner ℝ (w ω) _ = _
        rw [h2]
      -- the strong-monotonicity integral
      have hgrad_eq : ∀ ω, partialGrad (payoff P ξ ψ) i (Function.update (y ω) i (z (m + 1) ω)) =
          partialGrad (fun _ => f) i (Function.update (y ω) i (z (m + 1) ω)) := fun ω => rfl
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
          refine Integrable.of_bound (by fun_prop : Measurable fun ω => μ * (A.indicator (1 : Ω → ℝ) ω *
            inner ℝ (z (m + 1) ω - y ω i) (z (m + 1) ω - xh ω))).aestronglyMeasurable
            (μ * (D * D)) (ae_of_all _ fun ω => ?_)
          rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_pos hμ, Real.norm_eq_abs,
            abs_of_nonneg (hind0 ω)]
          refine mul_le_mul_of_nonneg_left ?_ hμ.le
          calc A.indicator (1 : Ω → ℝ) ω * ‖inner ℝ (z (m + 1) ω - y ω i) (z (m + 1) ω - xh ω)‖
              ≤ 1 * (D * D) := mul_le_mul (hind1 ω)
                ((norm_inner_le_norm _ _).trans (mul_le_mul (hdy ω) (hdw ω) (norm_nonneg _) hD0))
                (norm_nonneg _) zero_le_one
            _ = D * D := one_mul _
        have hcI : Integrable (fun ω => inner ℝ (w ω)
            (P[Gs (m + 1) | innerField j ξs k i (m + 1)] ω)) P := by
          refine Integrable.mono' ((integrable_condExp (f := Gs (m + 1)) (m := innerField j ξs k i (m + 1)) (μ := P)).norm.const_mul D)
            (hwm'.aestronglyMeasurable.inner
              (((stronglyMeasurable_condExp (f := Gs (m + 1)) (m := innerField j ξs k i (m + 1))
                (μ := P)).mono (h𝒢le _)).aestronglyMeasurable))
            (ae_of_all _ fun ω => ?_)
          rw [Real.norm_eq_abs]
          exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (hwb ω) (norm_nonneg _))
        have hgI : Integrable (fun ω => inner ℝ (w ω) (partialGrad (payoff P ξ ψ) i
            (Function.update (y ω) i (z (m + 1) ω)))) P := by
          refine hcI.congr ?_
          filter_upwards [hunb (m + 1) (by omega) hj1] with ω h
          show inner ℝ (w ω) _ = inner ℝ (w ω) _
          rw [h]
        simp_rw [e1]
        rw [integral_add hinnG hdetI, hunbI, ← integral_add hgI hdetI, ← integral_const_mul]
        refine integral_mono ((hXint m).const_mul μ) (hgI.add hdetI) fun ω => ?_
        have hs := strong_ineq hUo hf i hXicv (y ω) (hyU ω) (hcX ω) (hxhX ω)
          (hxhat (y ω) (hyS ω) i).2 (z (m + 1) ω) (hzX _ ω)
        have e2 : inner ℝ (w ω) (partialGrad (payoff P ξ ψ) i
              (Function.update (y ω) i (z (m + 1) ω))) +
            μ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (z (m + 1) ω - y ω i) (z (m + 1) ω - xh ω)) =
            A.indicator (1 : Ω → ℝ) ω * inner ℝ (partialGrad (fun _ => f) i
              (Function.update (y ω) i (z (m + 1) ω)) + μ • (z (m + 1) ω - y ω i))
              (z (m + 1) ω - xh ω) := by
          have hpg : partialGrad (payoff P ξ ψ) i (Function.update (y ω) i (z (m + 1) ω)) =
              partialGrad (fun _ => f) i (Function.update (y ω) i (z (m + 1) ω)) := rfl
          rw [hpg]
          simp only [hw, inner_add_left, real_inner_smul_left, real_inner_smul_right]
          rw [real_inner_comm (z (m + 1) ω - xh ω)
            (partialGrad (fun _ => f) i (Function.update (y ω) i (z (m + 1) ω)))]
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
      have hGdm : Measurable Gd := (hGm m).add (((hzm' m).sub hyi).const_smul μ)
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
        rw [← integral_condExp (h𝒢le (m + 1)), ← hintc]
        have hpull := condExp_mul_of_stronglyMeasurable_left (m := innerField j ξs k i (m + 1))
          (μ := P) (f := A.indicator (1 : Ω → ℝ)) (g := fun ω => ‖Gs (m + 1) ω‖ ^ 2)
          ((hindm.mono (hFG _) le_rfl).stronglyMeasurable) hAGi hG2I
        have hv := hvar (m + 1) (by omega) hj1
        refine integral_mono_ae (integrable_condExp) (hindI _) ?_
        filter_upwards [hpull, hv] with ω h1 h2
        have h1' : (P[fun ω => A.indicator (1 : Ω → ℝ) ω * ‖Gs (m + 1) ω‖ ^ 2 |
            innerField j ξs k i (m + 1)]) ω = A.indicator (1 : Ω → ℝ) ω *
              (P[fun ω => ‖Gs (m + 1) ω‖ ^ 2 | innerField j ξs k i (m + 1)]) ω := h1
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
          (hindm'.mul (hGdm.inner ((hzm' m).sub hxhm'))).aestronglyMeasurable
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
        refine integral_mono (hXint (m + 1)) (((hXint m).sub (hiY.const_mul (2 * γ))).add
          (hiZ.const_mul (γ ^ 2))) fun ω => ?_
        have := mul_le_mul_of_nonneg_left (hpt ω) (hind0 ω)
        simp only at this ⊢
        nlinarith [this]
      rw [integral_add (f := fun ω => A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2
            - 2 * γ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω)))
          (g := fun ω => γ ^ 2 * (A.indicator (1 : Ω → ℝ) ω * ‖Gd ω‖ ^ 2))
          ((hXint m).sub (hiY.const_mul _)) (hiZ.const_mul _),
        integral_sub (f := fun ω => A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2)
          (g := fun ω => 2 * γ * (A.indicator (1 : Ω → ℝ) ω * inner ℝ (Gd ω) (z (m + 1) ω - xh ω)))
          (hXint m) (hiY.const_mul _), integral_const_mul, integral_const_mul] at hmono
      have ha0nn : 0 ≤ ∫ ω, A.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2 ∂P :=
        integral_nonneg fun ω => mul_nonneg (hind0 ω) (sq_nonneg _)
      have hr2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by have : (0:ℝ) ≤ m := Nat.cast_nonneg m; linarith
      have hQe : Q = 2 * M i ^ 2 / μ ^ 2 + 2 * D ^ 2 := by rw [hQdef, hDdef]; rfl
      have := arith_step _ _ _ γ μ (M i ^ 2) D Q (P.real A) ((m : ℝ) + 2) hμ hr2 hγ hQe hQ0 hPA
        ha0nn hI1 hI2 ih
      have hc : (((m + 1 : ℕ) : ℝ) + 2) = (m : ℝ) + 2 + 1 := by push_cast; ring
      rw [hc]
      exact hmono.trans this
  -- conclusion
  intro t ht1 htj
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
  have hfi : Integrable (fun ω => ‖z (m + 1) ω - xh ω‖ ^ 2) P := by
    refine Integrable.of_bound (((hzm' m).sub hxhm').norm.pow_const 2).aestronglyMeasurable (D ^ 2)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdist _ _ (hzX _ ω) (hxhX ω)) 2
  refine ae_of_ae_trim hFle ?_
  have hint1 : Integrable (P[fun ω => ‖z (m + 1) ω - xh ω‖ ^ 2 | infoField j ξs k])
      (P.trim hFle) :=
    integrable_condExp.trim hFle stronglyMeasurable_condExp
  have hint2 : Integrable (fun _ : Ω => Q / (((m + 1 : ℕ) : ℝ) + 1)) (P.trim hFle) :=
    integrable_const _
  refine ae_le_of_forall_setIntegral_le hint1 hint2 fun S' hS' _ => ?_
  rw [← setIntegral_trim hFle stronglyMeasurable_condExp hS',
    ← setIntegral_trim hFle stronglyMeasurable_const hS', setIntegral_condExp hFle hfi hS',
    setIntegral_const]
  have h := hrec S' hS' m htj
  have e : (fun ω => S'.indicator (1 : Ω → ℝ) ω * ‖z (m + 1) ω - xh ω‖ ^ 2) =
      S'.indicator (fun ω => ‖z (m + 1) ω - xh ω‖ ^ 2) := by
    funext ω; by_cases hω : ω ∈ S' <;> simp [hω]
  rw [e, integral_indicator (hFle _ hS')] at h
  have hc : Q / ((m : ℝ) + 2) = Q / (((m + 1 : ℕ) : ℝ) + 1) := by push_cast; ring_nf
  rw [hc] at h
  rw [smul_eq_mul, mul_comm]
  exact h
