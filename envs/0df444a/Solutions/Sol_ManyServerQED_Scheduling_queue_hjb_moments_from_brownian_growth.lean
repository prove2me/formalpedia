-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_moments_from_brownian_growth
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:44:49.944463+00:00
-- url     : https://prove2.me/submissions/3c6589dc-8510-4264-9dcf-081df556c179

import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_filtered_brownian_coordinate_supremum_moment
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 2200000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] {P : Measure Ω}
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) (F : Filtration ℝ≥0 d.mΩ')
    (hW : IsStdFBrownian d.Q F d.noise) (r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (a : ℝ) (ha : 0 < a)
    (hGrowth : ∀ T : ℝ≥0, ∀ᵐ ω ∂d.Q, ∀ t ≤ T,
      ENNReal.ofReal (l1norm (d.state t ω)) ≤
        ENNReal.ofReal ((k:ℝ)*(1+a*(T:ℝ))^2) *
          (ENNReal.ofReal ((k:ℝ)*a*(1+(T:ℝ))) +
            ∑ i, ENNReal.ofReal (r i) * (⨆ u : Iic T, ENNReal.ofReal |d.noise u.1 ω i|))) :
    (∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ j : ℕ, ∀ t : ℝ≥0,
      Integrable (fun ω => l1norm (d.state t ω)^p) d.Q ∧
      (∫ ω, l1norm (d.state t ω)^p ∂d.Q) ≤ c*(1+(t:ℝ)^j)) ∧
    (∀ (T : ℝ≥0) (q : ℕ), ∃ V : d.Ω' → ℝ, Integrable V d.Q ∧
      ∀ᵐ ω ∂d.Q, ∀ t ≤ T, l1norm (d.state t ω)^q ≤ V ω) := by
  classical
  letI : IsProbabilityMeasure d.Q := d.isProb
  have hX (t : ℝ≥0) : Measurable (d.state t) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply _).comp (d.limit_meas t))
  have hC (ω : d.Ω') : Continuous (fun t => d.noise t ω) := by
    apply continuous_pi
    intro i
    exact (continuous_apply _).comp
      ((d.limit_cont ω).comp_continuous continuous_subtype_val (fun t => t.2))
  have hRes (q : ℕ) : ∃ C > (0:ℝ), ∀ T : ℝ≥0,
      ∃ M : d.Ω' → ℝ, Integrable M d.Q ∧
        (∀ᵐ ω ∂d.Q, ∀ t ≤ T, l1norm (d.state t ω)^q ≤ M ω) ∧
        (∫ ω, M ω ∂d.Q) ≤ C*(1+(T:ℝ))^(4*(q+2)) := by
    let p := q+2
    have hp : 1 < p := by dsimp [p]; omega
    have h0 : 0 < p := Nat.zero_lt_of_lt hp
    have hp' : p = (p-1)+1 := by omega
    have hk : 0 < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
    let S (T : ℝ≥0) (i : Fin k) (ω : d.Ω') := ⨆ u : Iic T, ENNReal.ofReal |d.noise u.1 ω i|
    have hE (i : Fin k) := filtered_brownian_coordinate_supremum_moment F d.noise hW hC i p hp
    choose C hCn hCb using hE
    let A := (k:ℝ)*(1+a)^2
    let B := 1+(k:ℝ)*a+∑ i, r i
    let K := (A*B)^p*((k:ℝ)+1)^(p-1)
    have hA : 0 < A := by dsimp [A]; positivity
    have hBr : 0 ≤ ∑ i, r i := Finset.sum_nonneg (fun i _ => (hr i).le)
    have hB : 0 < B := by dsimp [B]; positivity
    have hK : 0 < K := by dsimp [K]; positivity
    have hCsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hCn i)
    refine ⟨1+K*(1+∑ i, C i),by positivity,?_⟩
    intro T
    let U (i : Fin k) (ω : d.Ω') := (S T i ω).toReal
    have hUm (i : Fin k) : Measurable (U i) := (hCb i T).1.ennreal_toReal
    have hUn (i : Fin k) (ω : d.Ω') : 0 ≤ U i ω := ENNReal.toReal_nonneg
    have hSf (i : Fin k) : ∀ᵐ ω ∂d.Q, S T i ω ≠ ⊤ := by
      have hI : (∫⁻ ω, S T i ω^p ∂d.Q) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hCb i T).2
      filter_upwards [ae_lt_top ((hCb i T).1.pow_const _) hI] with ω hω
      intro h
      change S T i ω^p < ⊤ at hω
      rw [h,ENNReal.top_pow h0.ne'] at hω
      exact (lt_irrefl ⊤) hω
    have hUi (i : Fin k) :
        Integrable (fun ω => U i ω^p) d.Q ∧
        (∫ ω, U i ω^p ∂d.Q) ≤ C i*(1+(T:ℝ))^p := by
      have hL : (∫⁻ ω, ENNReal.ofReal (U i ω^p) ∂d.Q) ≤
          ENNReal.ofReal (C i*(1+(T:ℝ))^p) := by
        refine (lintegral_mono fun ω => ?_).trans (hCb i T).2
        rw [ENNReal.ofReal_pow (hUn i ω)]
        apply pow_le_pow_left'
        change ENNReal.ofReal (S T i ω).toReal ≤ S T i ω
        by_cases ht : S T i ω = ⊤
        · rw [ht]
          exact le_top
        · rw [ENNReal.ofReal_toReal ht]
      have hUi : Integrable (fun ω => U i ω^p) d.Q := by
        refine ⟨((hUm i).pow_const _).aestronglyMeasurable,?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        simp_rw [Real.enorm_eq_ofReal (pow_nonneg (hUn i _) _)]
        exact hL.trans_lt ENNReal.ofReal_lt_top
      refine ⟨hUi,?_⟩
      have hn : (0:ℝ) ≤ ∫ ω, U i ω ^ p ∂d.Q :=
        integral_nonneg (fun ω => pow_nonneg (hUn i ω) _)
      rw [← ofReal_integral_eq_lintegral_ofReal hUi (Eventually.of_forall fun ω =>
        pow_nonneg (hUn i ω) _)] at hL
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity [hCn i])).1 hL
    let M (ω : d.Ω') := 1 + K*(1+(T:ℝ))^(3*p)*(1+∑ i, U i ω^p)
    have hMi : Integrable M d.Q := (integrable_const _).add
      (((integrable_const _).add (integrable_finsetSum _ (fun i _ => (hUi i).1))).const_mul _)
    have hDom : ∀ᵐ ω ∂d.Q, ∀ t ≤ T, l1norm (d.state t ω)^q ≤ M ω := by
      filter_upwards [hGrowth T,ae_all_iff.2 hSf] with ω hω hF
      intro t ht
      have he := hω t ht
      change ENNReal.ofReal (l1norm (d.state t ω)) ≤
        ENNReal.ofReal ((k:ℝ)*(1+a*(T:ℝ))^2) *
          (ENNReal.ofReal ((k:ℝ)*a*(1+(T:ℝ))) + ∑ i, ENNReal.ofReal (r i)*S T i ω) at he
      have heq (i : Fin k) : S T i ω = ENNReal.ofReal (U i ω) := (ENNReal.ofReal_toReal (hF i)).symm
      simp_rw [heq] at he
      have hR : (∑ i, ENNReal.ofReal (r i) * ENNReal.ofReal (U i ω)) =
          ENNReal.ofReal (∑ i, r i*U i ω) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hr i).le (hUn i ω))]
        exact Finset.sum_congr rfl (fun i _ => (ENNReal.ofReal_mul (hr i).le).symm)
      have ht0 : 0 ≤ (T:ℝ) := T.2
      rw [hR,← ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg (fun i _ =>
        mul_nonneg (hr i).le (hUn i ω))),← ENNReal.ofReal_mul (by positivity)] at he
      have hnR : 0 ≤ ∑ i, r i*U i ω := Finset.sum_nonneg (fun i _ =>
        mul_nonneg (hr i).le (hUn i ω))
      have he' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 he
      have hsumU : 0 ≤ ∑ i, U i ω := Finset.sum_nonneg (fun i _ => hUn i ω)
      have hxx : l1norm (d.state t ω) ≤ (A*B)*(1+(T:ℝ))^3*(1+∑ i, U i ω) := by
        refine he'.trans ?_
        have hA' : (k:ℝ)*(1+a*(T:ℝ))^2 ≤ A*(1+(T:ℝ))^2 := by
          dsimp [A]
          rw [mul_assoc,← mul_pow]
          gcongr
          nlinarith
        have hB' (i : Fin k) : r i ≤ B := by
          have h := Finset.single_le_sum (fun j _ => (hr j).le) (Finset.mem_univ i)
          dsimp [B]
          linarith [mul_nonneg hk.le ha.le]
        have hS' : ∑ i, r i*U i ω ≤ B*(∑ i, U i ω) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hB' i) (hUn i ω))
        have hB0 : (k:ℝ)*a ≤ B := by dsimp [B]; linarith [hBr]
        have hB1 : (k:ℝ)*a*(1+(T:ℝ)) + ∑ i, r i*U i ω ≤ (B*(1+(T:ℝ)))*(1+∑ i, U i ω) := by
          have h := mul_le_mul_of_nonneg_right hB0 (by positivity : 0 ≤ 1+(T:ℝ))
          have hb := mul_nonneg (mul_nonneg hB.le ht0) hsumU
          nlinarith
        have hnon : 0 ≤ (k:ℝ)*a*(1+(T:ℝ)) + ∑ i, r i*U i ω :=
          add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => mul_nonneg (hr i).le (hUn i ω))
        refine (mul_le_mul hA' hB1 hnon (by positivity)).trans_eq ?_
        ring
      have hn : 0 ≤ l1norm (d.state t ω) := Finset.sum_nonneg (fun i _ => abs_nonneg _)
      have hpq : l1norm (d.state t ω)^q ≤ 1+l1norm (d.state t ω)^p := by
        rcases le_total (l1norm (d.state t ω)) 1 with h | h
        · exact (pow_le_one₀ hn h).trans (le_add_of_nonneg_right (pow_nonneg hn _))
        · exact (pow_le_pow_right₀ h (by omega : q ≤ p)).trans (le_add_of_nonneg_left zero_le_one)
      let term (i : Option (Fin k)) : ℝ := Option.elim i 1 (fun i => U i ω)
      have hJ := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := term)
        (fun i _ => by cases i with | none => exact zero_le_one | some i => exact hUn i ω) (p-1)
      have hJes : (1+∑ i, U i ω)^p ≤ ((k:ℝ)+1)^(p-1)*(1+∑ i, U i ω^p) := by
        rw [← hp'] at hJ
        simpa [term,Fintype.sum_option,add_comm] using hJ
      refine hpq.trans (add_le_add_right ((pow_le_pow_left₀ hn hxx _).trans ?_) 1)
      rw [mul_pow,mul_pow,← pow_mul]
      dsimp [M,K]
      have h := mul_le_mul_of_nonneg_left hJes (by positivity :
        0 ≤ (A*B)^p*(1+(T:ℝ))^(3*p))
      convert h using 1 <;> ring
    refine ⟨M,hMi,hDom,?_⟩
    have ht0 : 0 ≤ (T:ℝ) := T.2
    have hInt : (∫ ω, M ω ∂d.Q) = 1+K*(1+(T:ℝ))^(3*p)*(1+∑ i, ∫ ω, U i ω^p ∂d.Q) := by
      let f (ω : d.Ω') : ℝ := ∑ i, U i ω^p
      have hf : Integrable f d.Q := integrable_finsetSum _ (fun i _ => (hUi i).1)
      let g (ω : d.Ω') : ℝ := 1+f ω
      have hg : Integrable g d.Q := (integrable_const _).add hf
      let c := K*(1+(T:ℝ))^(3*p)
      change (∫ ω, (fun _ : d.Ω' => (1:ℝ)) ω + (fun ω => c*g ω) ω ∂d.Q) = _
      rw [integral_add (integrable_const _) (hg.const_mul _),integral_const_mul]
      change (∫ _ : d.Ω', (1:ℝ) ∂d.Q)+c*(∫ ω, (fun _ : d.Ω' => (1:ℝ)) ω+f ω ∂d.Q) = _
      rw [integral_add (integrable_const _) hf]
      dsimp only [f,c]
      rw [integral_finsetSum _ (fun i _ => (hUi i).1)]
      simp
    rw [hInt]
    have hU := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hUi i).2)
    rw [← Finset.sum_mul] at hU
    have hP : 1 ≤ (1+(T:ℝ))^p := one_le_pow₀ (by linarith [ht0])
    have hQ : 1 ≤ (1+(T:ℝ))^(4*p) := one_le_pow₀ (by linarith [ht0])
    calc
      _ ≤ 1+K*(1+(T:ℝ))^(3*p)*((1+∑ i, C i)*(1+(T:ℝ))^p) := by
        apply add_le_add_right
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [add_mul,one_mul]
        linarith
      _ = 1+K*(1+∑ i, C i)*(1+(T:ℝ))^(4*p) := by
        rw [show 4*p = 3*p+p by omega,pow_add]
        ring
      _ ≤ (1+K*(1+∑ i, C i))*(1+(T:ℝ))^(4*p) := by rw [add_mul,one_mul]; linarith
  refine ⟨?_,?_⟩
  · intro q
    obtain ⟨C,hC,h⟩ := hRes q
    let j := 4*(q+2)
    refine ⟨C*2^j,by positivity,j,?_⟩
    intro t
    obtain ⟨V,hV,hDom,hBound⟩ := h t
    have hn : ∀ ω, 0 ≤ l1norm (d.state t ω)^q := fun ω =>
      pow_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) _
    have h' : ∀ᵐ ω ∂d.Q, l1norm (d.state t ω)^q ≤ V ω :=
      hDom.mono (fun ω h => h t le_rfl)
    have hm := ((continuous_finsetSum Finset.univ (fun i _ =>
      (continuous_apply i).abs)).measurable.comp (hX t)).pow_const q
    have hInt : Integrable (fun ω => l1norm (d.state t ω)^q) d.Q :=
      hV.mono' hm.aestronglyMeasurable (h'.mono fun ω h => by rwa [Real.norm_of_nonneg (hn ω)])
    refine ⟨hInt,(integral_mono_ae hInt hV h').trans (hBound.trans ?_)⟩
    have hT : (1+(t:ℝ))^j ≤ 2^j*(1+(t:ℝ)^j) := by
      rcases le_total (t:ℝ) 1 with h | h
      · apply (pow_le_pow_left₀ (by positivity) (by linarith : 1+(t:ℝ) ≤ 2) j).trans
        exact le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (pow_nonneg t.2 j))
      · have hP := pow_le_pow_left₀ (by positivity) (by linarith : 1+(t:ℝ) ≤ 2*(t:ℝ)) j
        rw [mul_pow] at hP
        exact hP.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
    exact (mul_le_mul_of_nonneg_left hT hC.le).trans_eq (by ring)
  · intro T q
    obtain ⟨C,hC,h⟩ := hRes q
    obtain ⟨V,hV,hdom,_⟩ := h T
    exact ⟨V,hV,hdom⟩
