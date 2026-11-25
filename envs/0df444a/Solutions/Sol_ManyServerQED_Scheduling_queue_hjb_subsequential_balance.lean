-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_subsequential_balance
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T20:57:44.956719+00:00
-- url     : https://prove2.me/submissions/40f18668-7719-4120-92a3-be625b0463e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_finite_horizon_balance
import Theorems.Thm_ManyServerQED_Scheduling_queue_discounted_cost_tails
import Theorems.Thm_ManyServerQED_Scheduling_scp_joint_state_measurable
import Mathlib

open MeasureTheory Filter Topology Set
open scoped ENNReal

private theorem approximate_nonnegative_cost {U : ℕ → ℝ≥0∞} {V : ℕ → ℕ → ℝ≥0∞}
    {L : ℕ → ℝ≥0∞} (hL : ∀ t, L t < ⊤)
    (hV : ∀ t, Tendsto (V t) atTop (𝓝 (L t)))
    (hMono : ∀ t s, t ≤ s → ∀ᶠ n in atTop, V t n ≤ V s n)
    (hLo : ∀ t, ∀ᶠ n in atTop, V t n ≤ U n)
    (hAp : ∀ ε > 0, ∃ t, ∀ᶠ n in atTop, U n ≤ V t n + ε) :
    ∃ l, l < ⊤ ∧ Tendsto U atTop (𝓝 l) ∧ Monotone L ∧ Tendsto L atTop (𝓝 l) := by
  let l := ⨆ t, L t
  have hmono : Monotone L := by
    intro t s hts
    exact le_of_tendsto_of_tendsto (hV t) (hV s) (hMono t s hts)
  have hLo' : l ≤ liminf U atTop := by
    apply iSup_le
    intro t
    simpa only [(hV t).liminf_eq] using liminf_le_liminf (hLo t)
  have hLS (ε : ℝ≥0∞) (hε : 0 < ε) :
      ∃ t, limsup U atTop ≤ L t + ε := by
    obtain ⟨t,ht⟩ := hAp ε hε
    exact ⟨t, (limsup_le_limsup ht).trans_eq (((hV t).add tendsto_const_nhds).limsup_eq)⟩
  have hFin : limsup U atTop < ⊤ := by
    obtain ⟨t,ht⟩ := hLS 1 zero_lt_one
    exact ht.trans_lt (ENNReal.add_lt_top.2 ⟨hL t, ENNReal.one_lt_top⟩)
  have hlfin : l < ⊤ := (hLo'.trans liminf_le_limsup).trans_lt hFin
  have hHi : limsup U atTop ≤ l := by
    by_contra! h
    obtain ⟨l',hl',ε,hε,hs⟩ := ENNReal.exists_add_lt_of_add_lt (by simpa using h :
      l + 0 < limsup U atTop)
    obtain ⟨t,ht⟩ := hLS ε hε
    exact (not_le_of_gt hs) (ht.trans (add_le_add_left (le_iSup L t |>.trans hl'.le) _))
  exact ⟨l,hlfin,tendsto_of_le_liminf_of_limsup_le hLo' hHi,hmono,tendsto_atTop_iSup hmono⟩

private theorem split_discounted_cost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : Ω → ℝ → ℝ≥0∞) (hm : Measurable (Function.uncurry (fun ω t => c ω (max 0 t))))
    (T : ℕ) :
    (∫⁻ ω, ∫⁻ t in Ioi (0:ℝ), c ω t ∂volume ∂P) =
      (∫⁻ ω, ∫⁻ t in Ioc (0:ℝ) (T:ℝ), c ω t ∂volume ∂P) +
        ∫⁻ ω, ∫⁻ t in Ioi (T:ℝ), c ω t ∂volume ∂P := by
  have he : Ioc (0:ℝ) (T:ℝ) ∪ Ioi (T:ℝ) = Ioi (0:ℝ) := by
    ext t
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (⟨h,_⟩ | h)
      · exact h
      · exact (Nat.cast_nonneg T).trans_lt h
    · intro h
      rcases le_or_gt t (T:ℝ) with ht | ht
      · exact Or.inl ⟨h,ht⟩
      · exact Or.inr ht
  have hd : Disjoint (Ioc (0:ℝ) (T:ℝ)) (Ioi (T:ℝ)) := by
    rw [Set.disjoint_left]
    exact fun t ht hu => (not_le_of_gt hu) ht.2
  let C (ω : Ω) := ∫⁻ t in Ioc (0:ℝ) (T:ℝ), c ω t ∂volume
  let D (ω : Ω) := ∫⁻ t in Ioi (T:ℝ), c ω t ∂volume
  have hC : Measurable C := by
    have hm' := Measurable.lintegral_prod_right (ν := volume.restrict (Ioc (0:ℝ) (T:ℝ))) hm
    convert hm' using 1
    funext ω
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp [max_eq_right ht.1.le]
  have hD : Measurable D := by
    have hm' := Measurable.lintegral_prod_right (ν := volume.restrict (Ioi (T:ℝ))) hm
    convert hm' using 1
    funext ω
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht' : (T:ℝ) < t := mem_Ioi.1 ht
    simp [max_eq_right ((Nat.cast_nonneg T).trans ht'.le)]
  calc
    _ = ∫⁻ ω, C ω + D ω ∂P := by
      apply lintegral_congr
      intro ω
      rw [← he,lintegral_union measurableSet_Ioi hd]
    _ = _ := lintegral_add_left hC _

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
open scoped NNReal
private theorem sum_Xhat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (n : ℕ) (X : Ω → ℝ → Fin k → ℝ) (ω : Ω) (t : ℝ) :
    ∑ j, M.Xhat n X ω t j = (∑ j, X ω t j - n) / Real.sqrt n := by
  unfold SystemSequence.Xhat
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have : ∑ i, M.rho i = 1 := M.sum_rho
  rw [this, one_mul]

private theorem scheduling_integrand_eq {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (n : ℕ) (hn : 1 ≤ n) (u0 : Fin k → ℝ) (X Ψ : Ω → ℝ → Fin k → ℝ) (ω : Ω) (t : ℝ)
    (hnn : ∀ i, 0 ≤ X ω t i - Ψ ω t i)
    (hwc : max (∑ i, X ω t i - n) 0 = ∑ i, (X ω t i - Ψ ω t i)) :
    Lt (Phihat n X Ψ ω t) (M.Psihat n Ψ ω t) =
      costOfTilde Lt (M.Xhat n X ω t) (uProc n u0 X Ψ ω t) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hPhi : Phihat n X Ψ ω t = max (∑ j, M.Xhat n X ω t j) 0 • uProc n u0 X Ψ ω t := by
    rw [sum_Xhat]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Phihat, uProc]
    split_ifs with hpos
    · rw [max_eq_left (div_nonneg hpos.le hsn.le)]
      field_simp
    · push Not at hpos
      rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg hpos hsn.le), zero_mul]
      have h0 : ∑ i, (X ω t i - Ψ ω t i) = 0 := by rw [← hwc, max_eq_right hpos]
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)] at h0
      rw [h0 i (Finset.mem_univ _), zero_div]
  unfold costOfTilde
  rw [← hPhi]
  congr 1
  funext i
  simp only [SystemSequence.Psihat, Pi.sub_apply, SystemSequence.Xhat, Phihat]
  ring



set_option maxHeartbeats 1500000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n))
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    :
    ∀ s : ℕ → ℕ, Tendsto s atTop atTop →
      ∃ r : ℕ → ℕ, Tendsto r atTop atTop ∧ ∃ g : ℝ, 0 ≤ g ∧
        Tendsto (fun j => M.queueCostL (costOfTilde Lt) γ (s (r j)) u0 (X (s (r j))) (Ψ (s (r j))))
          atTop (𝓝 (ENNReal.ofReal (f x + g))) ∧
        (UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i *
            grad f (M.Xhat n (X n) ω s) i +
          costOfTilde Lt (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (X n) ω s)
            (grad f (M.Xhat n (X n) ω s)))])
      (fun _ => 0) → g = 0) := by
  intro s hs
  obtain ⟨r,hr,C,F,G,hCFG,hF,hCV,hGap⟩ :=
    queue_hjb_finite_horizon_balance M Lt ϱ mL mU γ hA2 hA3 hγ u0 hu0 X0 x hX0 X Ψ hpol f hf hHJB s hs
  have hM (n : ℕ) (hn : 1 ≤ n) :
      Measurable (fun z : Ω × ℝ≥0 => X n z.1 z.2) ∧
       Measurable (fun z : Ω × ℝ≥0 => Ψ n z.1 z.2) :=
    scp_joint_state_measurable M n (X0 n) (X n) (Ψ n) (hpol n hn).1
  obtain ⟨N,hTail⟩ := queue_discounted_cost_tails M Lt ϱ mL mU γ hA2 hA3 hγ u0 hu0 X0 x hX0 X Ψ
    hpol (fun n hn => (hM n hn).1) (fun n hn => (hM n hn).2)
  let score (n : ℕ) (ω : Ω) (t : ℝ) :=
    ENNReal.ofReal (Real.exp (-γ*t) * costOfTilde Lt (M.Xhat n (X n) ω t) (uProc n u0 (X n) (Ψ n) ω t))
  have hScore (n : ℕ) (hn : 1 ≤ n) :
      Measurable (Function.uncurry (fun ω t => score n ω (max 0 t))) := by
    let q (z : Ω × ℝ) : Ω × ℝ≥0 := (z.1,z.2.toNNReal)
    have hq : Measurable q := measurable_fst.prodMk measurable_snd.real_toNNReal
    have hX := (hM n hn).1.comp hq
    have hP := (hM n hn).2.comp hq
    have hΦ : Measurable (fun z : Ω × ℝ => Phihat n (X n) (Ψ n) z.1 z.2.toNNReal) := by
      apply measurable_pi_lambda
      intro i
      exact (((measurable_pi_apply i).comp hX).sub ((measurable_pi_apply i).comp hP)).div_const _
    have hΨ : Measurable (fun z : Ω × ℝ => M.Psihat n (Ψ n) z.1 z.2.toNNReal) := by
      apply measurable_pi_lambda
      intro i
      exact (((measurable_pi_apply i).comp hP).sub_const (M.rho i * n)).div_const _
    have hCost := hA2.tilde_cont.measurable.comp (hΦ.prodMk hΨ)
    have hExp : Measurable (fun z : Ω × ℝ => Real.exp (-γ * max 0 z.2)) :=
      (((measurable_const.max measurable_snd).const_mul (-γ)).exp)
    have h := (hExp.mul hCost).ennreal_ofReal
    convert h using 1
    funext z
    dsimp only [score, Function.uncurry]
    have ht : max 0 z.2 = (z.2.toNNReal:ℝ) := by
      rw [Real.coe_toNNReal', max_comm]
    change ENNReal.ofReal (Real.exp (-γ * max 0 z.2) *
        costOfTilde Lt (M.Xhat n (X n) z.1 (max 0 z.2))
          (uProc n u0 (X n) (Ψ n) z.1 (max 0 z.2))) =
        ENNReal.ofReal (Real.exp (-γ * max 0 z.2) *
          Lt (Phihat n (X n) (Ψ n) z.1 z.2.toNNReal) (M.Psihat n (Ψ n) z.1 z.2.toNNReal))
    rw [ht, scheduling_integrand_eq M Lt n hn u0 (X n) (Ψ n) z.1 z.2.toNNReal
      (fun i => (hpol n hn).1.controlled.phi_nonneg z.1 z.2.toNNReal i z.2.toNNReal.2)
      ((hpol n hn).2.2 z.1 z.2.toNNReal z.2.toNNReal.2)]
  let U (j : ℕ) := M.queueCostL (costOfTilde Lt) γ (s (r j)) u0 (X (s (r j))) (Ψ (s (r j)))
  let V (T j : ℕ) := ∫⁻ ω, ∫⁻ t in Ioc (0:ℝ) (T:ℝ), score (s (r j)) ω t ∂volume ∂M.P
  let L (T : ℕ) := ENNReal.ofReal (C T)
  have hv (T : ℕ) : Tendsto (V T) atTop (𝓝 (L T)) := hCV T
  have hUeq (j : ℕ) (T : ℕ) (hj : 1 ≤ s (r j)) :
      U j = V T j + ∫⁻ ω, ∫⁻ t in Ioi (T:ℝ), score (s (r j)) ω t ∂volume ∂M.P :=
    split_discounted_cost M.P (score (s (r j))) (hScore _ hj) T
  have hMono (T S : ℕ) (hTS : T ≤ S) : ∀ᶠ j in atTop, V T j ≤ V S j := by
    apply Eventually.of_forall
    intro j
    exact lintegral_mono (fun ω => lintegral_mono_set (Ioc_subset_Ioc_right (by exact_mod_cast hTS)))
  have hlo (T : ℕ) : ∀ᶠ j in atTop, V T j ≤ U j := by
    apply Eventually.of_forall
    intro j
    exact lintegral_mono (fun ω => lintegral_mono_set Ioc_subset_Ioi_self)
  have hAp (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ T, ∀ᶠ j in atTop, U j ≤ V T j + ε := by
    obtain ⟨T,hT⟩ := hTail ε hε
    refine ⟨T,?_⟩
    have hsr := hs.comp hr
    filter_upwards [(tendsto_atTop.1 hsr) (max N 1)] with j hj
    rw [hUeq j T ((le_max_right _ _).trans hj)]
    exact add_le_add_right (hT (s (r j)) ((le_max_left _ _).trans hj)).le _
  obtain ⟨l,hl,hlU,hlMono,hlT⟩ := approximate_nonnegative_cost
    (fun T => ENNReal.ofReal_lt_top) hv hMono hlo hAp
  have hlower (T : ℕ) : f x - F T ≤ l.toReal := by
    have hLT : L T ≤ l := ge_of_tendsto hlT ((eventually_ge_atTop T).mono
      (fun j hj => hlMono hj))
    have hreal := ENNReal.toReal_mono hl.ne hLT
    change (ENNReal.ofReal (C T)).toReal ≤ l.toReal at hreal
    rw [ENNReal.toReal_ofReal (hCFG T).1] at hreal
    linarith [(hCFG T).2.1, (hCFG T).2.2]
  have hreal : f x ≤ l.toReal := by
    have ht : Tendsto (fun T => f x - F T) atTop (𝓝 (f x - 0)) := tendsto_const_nhds.sub hF
    simpa only [sub_zero] using le_of_tendsto ht (Eventually.of_forall hlower)
  let g := l.toReal - f x
  have hg : 0 ≤ g := sub_nonneg.mpr hreal
  have hl' : ENNReal.ofReal (f x + g) = l := by
    rw [show f x + g = l.toReal by dsimp [g]; linarith, ENNReal.ofReal_toReal hl.ne]
  refine ⟨r,hr,g,hg,?_,?_⟩
  · rw [hl']; exact hlU
  · intro h49
    have hCX : Tendsto C atTop (𝓝 (f x - 0)) := by
      have ht : Tendsto (fun T => f x - F T) atTop (𝓝 (f x - 0)) := tendsto_const_nhds.sub hF
      apply ht.congr
      intro T
      rw [(hCFG T).2.2, hGap h49 T, add_zero]
    rw [sub_zero] at hCX
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hCX
    have hlf : l = ENNReal.ofReal (f x) := tendsto_nhds_unique hlT ht
    have hfx : 0 ≤ f x :=
      ge_of_tendsto hCX (Eventually.of_forall (fun T => (hCFG T).1))
    unfold g
    rw [hlf, ENNReal.toReal_ofReal hfx, sub_self]
