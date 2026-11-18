-- Prove2me | solution 1 for LocalOccupancyIS.Glauber.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:59:26.914434+00:00
-- url     : https://prove2.me/submissions/9a10f5e9-eb4b-4838-8693-094bdd4354da

import Definitions.Def_LocalOccupancyIS_Glauber_Parameters
import Definitions.Def_LocalOccupancyIS_Glauber_Dynamics
import Theorems.Thm_SinkhornHall_lemma_1_1
import Definitions.Def_LocalOccupancyIS_Glauber_Execution
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_9
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_7
import Theorems.Thm_LocalOccupancyIS_Glauber_lemma_5

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma lambert_exists {x : ℝ} (hx : 0 ≤ x) : ∃ w : ℝ, 0 ≤ w ∧ w*Real.exp w = x := by
  have hc : ContinuousOn (fun w : ℝ => w*Real.exp w) (Set.Icc 0 x) := by fun_prop
  have h0 : (0:ℝ)*Real.exp 0 ≤ x := by simpa using hx
  have h1 : x ≤ x*Real.exp x := by
    have hh := Real.one_le_exp hx
    nlinarith
  have hi := intermediate_value_Icc hx hc
  obtain ⟨w,hw,he⟩ := hi ⟨h0,h1⟩
  exact ⟨w,hw.1,he⟩

lemma lambert_facts {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ RiskBalancingMNL.lambertW x ∧
      RiskBalancingMNL.lambertW x * Real.exp (RiskBalancingMNL.lambertW x) = x := by
  unfold RiskBalancingMNL.lambertW
  rw [dif_pos (lambert_exists hx)]
  exact Classical.choose_spec (lambert_exists hx)

lemma lambert_pos {x : ℝ} (hx : 0 < x) : 0 < RiskBalancingMNL.lambertW x := by
  have hh := lambert_facts hx.le
  rcases eq_or_lt_of_le hh.1 with he | he
  · rw [← he] at hh
    simp at hh
    linarith
  · exact he

lemma mul_exp_strictMonoOn : StrictMonoOn (fun w : ℝ => w*Real.exp w) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  calc
    x*Real.exp x < y*Real.exp x := mul_lt_mul_of_pos_right hxy (Real.exp_pos _)
    _ ≤ y*Real.exp y := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hxy.le) hy

lemma lambert_lt_of_lt {x D : ℝ} (hx : 0 ≤ x) (hD : 0 < D) (h : x < D*Real.exp D) :
    RiskBalancingMNL.lambertW x < D := by
  have hh := lambert_facts hx
  by_contra hn
  have hle : D ≤ RiskBalancingMNL.lambertW x := le_of_not_gt hn
  have hm := mul_exp_strictMonoOn.monotoneOn hD.le hh.1 hle
  rw [hh.2] at hm
  linarith

lemma gamma_optimizer_identity {Δ lam c : ℝ} (hΔ : 0 < Δ) (hlam : 0 < lam) (hc : 0 < c) :
    Gamma Δ lam c = Δ/(c*optimizer Δ lam c) := by
  have hp : 0 < p lam := div_pos hlam (by positivity)
  have hx : 0 < p lam*Δ/c := div_pos (mul_pos hp hΔ) hc
  have hz : 0 < optimizer Δ lam c := lambert_pos hx
  have he := (lambert_facts hx.le).2
  change optimizer Δ lam c * Real.exp (optimizer Δ lam c) = p lam*Δ/c at he
  have he' : Real.exp (optimizer Δ lam c) = p lam*Δ/(c*optimizer Δ lam c) := by
    apply (eq_div_iff (mul_ne_zero hc.ne' hz.ne')).mpr
    have hh := (eq_div_iff hc.ne').mp he
    nlinarith
  unfold Gamma beta gamma
  rw [he']
  field_simp
  <;> ring

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma scale_pos (t : ℕ) {b : ℝ} (hb : 0 ≤ b) : 0 < scale t b :=
  Real.rpow_pos_of_pos (by linarith) _

lemma scale_one_le {t : ℕ} (ht : 1 ≤ t) {b : ℝ} (hb : 0 ≤ b) : 1 ≤ scale t b := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hden : 0 < 2*(t:ℝ)-1 := by linarith
  unfold scale
  exact Real.one_le_rpow (by linarith) (by positivity)

lemma exp_D {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    Real.exp (D Δ t b) = Δ/scale t b := by
  unfold D rho
  exact Real.exp_log (div_pos hΔ (scale_pos t hb))

lemma degree_scale_exp {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    Δ = scale t b*Real.exp (D Δ t b) := by
  rw [exp_D hΔ hb]
  field_simp [(scale_pos t hb).ne']

lemma D_large_basic {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    8 ≤ D Δ t b ∧ 0 < D Δ t b ∧ 1 ≤ D Δ t b := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hh : 8 ≤ 8*Real.exp 1*t := by nlinarith [mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr ht')]
  constructor
  · exact hh.trans hD
  · constructor <;> linarith

lemma fugacity_pos {Δ b : ℝ} {t : ℕ} (hb : 0 ≤ b) (hD : 0 < D Δ t b) :
    0 < fugacity Δ t b := by
  unfold fugacity
  exact one_div_pos.mpr (mul_pos (scale_pos t hb) (pow_pos hD _))

lemma fugacity_le_inv_D {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 1 ≤ D Δ t b) : fugacity Δ t b ≤ 1/D Δ t b := by
  have hD0 : 0 < D Δ t b := by linarith
  have hr : 1 ≤ 2*t-1 := by omega
  have hp : D Δ t b ≤ D Δ t b^(2*t-1) := by
    exact le_self_pow₀ hD (by omega)
  have hs := scale_one_le ht hb
  have hden : D Δ t b ≤ scale t b*D Δ t b^(2*t-1) := by
    have hh := mul_le_mul_of_nonneg_right hs (pow_nonneg hD0.le (2*t-1))
    nlinarith
  exact div_le_div_of_nonneg_left (by norm_num) hD0 hden

lemma correction_exponent_bounds {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 ≤ 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ∧
    4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ≤ 2 := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hD0 := (D_large_basic ht hD).2.1
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbase : 1 ≤ 4*Real.exp 1 := by linarith
  have hInv : 0 ≤ 1/(t:ℝ) := by positivity
  have hpow : (4*Real.exp 1)^(1-1/(t:ℝ)) ≤ 4*Real.exp 1 := by
    calc
      _ ≤ (4*Real.exp 1)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = _ := Real.rpow_one _
  constructor
  · positivity
  · apply (div_le_iff₀ hD0).mpr
    have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*(t:ℝ) by positivity)
    nlinarith

lemma correction_bounds {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 < correction Δ t b ∧ correction Δ t b ≤ 1 ∧
      (correction Δ t b)⁻¹ ≤ Real.exp 2 := by
  have hh := correction_exponent_bounds ht hD
  unfold correction
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · exact Real.exp_le_one_iff.mpr (by linarith)
  · rw [← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)

lemma fugacity_degree {Δ b : ℝ} {t : ℕ} (hΔ : 0 < Δ) (hb : 0 ≤ b) :
    fugacity Δ t b*Δ = Real.exp (D Δ t b)/D Δ t b^(2*t-1) := by
  conv_lhs =>
    rhs
    rw [degree_scale_exp (t := t) hΔ hb]
  unfold fugacity
  field_simp [(scale_pos t hb).ne']

lemma optimizer_bounds {Δ b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 < optimizer Δ (fugacity Δ t b) (correction Δ t b) ∧
      optimizer Δ (fugacity Δ t b) (correction Δ t b) < D Δ t b := by
  have hΔ0 : 0 < Δ := by linarith
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have hlam := fugacity_pos hb hD0
  have hc := correction_bounds ht hD
  have hp : 0 < p (fugacity Δ t b) := div_pos hlam (by positivity)
  have hx : 0 < p (fugacity Δ t b)*Δ/correction Δ t b := div_pos (mul_pos hp hΔ0) hc.1
  constructor
  · exact lambert_pos hx
  · apply lambert_lt_of_lt hx.le hD0
    have hpLam : p (fugacity Δ t b) ≤ fugacity Δ t b := by
      unfold p
      exact div_le_self hlam.le (by linarith)
    have hpow : D Δ t b ≤ D Δ t b^(2*t-1) := le_self_pow₀ hD1 (by omega)
    have hLamDeg : fugacity Δ t b*Δ ≤ Real.exp (D Δ t b)/D Δ t b := by
      rw [fugacity_degree hΔ0 hb]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hD0 hpow
    have hxbound : p (fugacity Δ t b)*Δ/correction Δ t b ≤
        (Real.exp (D Δ t b)/D Δ t b)*Real.exp 2 := by
      rw [div_eq_mul_inv]
      have hpΔ := mul_le_mul_of_nonneg_right hpLam hΔ0.le
      exact mul_le_mul (hpΔ.trans hLamDeg) hc.2.2 (inv_nonneg.mpr hc.1.le)
        (div_nonneg (Real.exp_pos _).le hD0.le)
    have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
    have hDge : 8*Real.exp 1 ≤ D Δ t b := by
      have hh := mul_le_mul_of_nonneg_left ht' (show 0 ≤ 8*Real.exp 1 by positivity)
      linarith
    have he : 0 < Real.exp 1 := Real.exp_pos _
    have he2 : Real.exp 2 = (Real.exp 1)^2 := by
      rw [show (2:ℝ) = 1+1 by norm_num, Real.exp_add, pow_two]
    have hsq : Real.exp 2 < D Δ t b*D Δ t b := by rw [he2]; nlinarith
    have hratio : Real.exp 2/D Δ t b < D Δ t b := (div_lt_iff₀ hD0).mpr hsq
    calc
      _ ≤ _ := hxbound
      _ = Real.exp (D Δ t b)*(Real.exp 2/D Δ t b) := by ring
      _ < Real.exp (D Δ t b)*D Δ t b := mul_lt_mul_of_pos_left hratio (Real.exp_pos _)
      _ = _ := by ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma empty_hardcore (G : SimpleGraph V) : MarkovMixing.IsHardcore G (fun _ => false) := by
  intro v w h
  simp

instance stateNonempty (G : SimpleGraph V) : Nonempty (State G) :=
  ⟨⟨_, empty_hardcore G⟩⟩

lemma hcWeight_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : V → Bool) : 0 ≤ MarkovMixing.hardcoreWeight G lam σ := by
  unfold MarkovMixing.hardcoreWeight
  split_ifs
  · exact le_of_lt (pow_pos hlam _)
  · rfl

lemma hcPartition_pos (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) : 0 < ∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ := by
  apply Finset.sum_pos'
  · intro σ hσ
    exact hcWeight_nonneg G hlam σ
  · refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
    simp [MarkovMixing.hardcoreWeight, empty_hardcore]

lemma hcLaw_pos (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) : 0 < HardCoreBochner.hcLaw G lam σ := by
  apply div_pos _ (hcPartition_pos G hlam)
  simp only [MarkovMixing.hardcoreWeight, if_pos σ.property]
  exact pow_pos hlam _

lemma hcLaw_dist (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) : MarkovMixing.IsDist (HardCoreBochner.hcLaw G lam) := by
  constructor
  · intro σ; exact (hcLaw_pos G hlam σ).le
  · unfold HardCoreBochner.hcLaw MarkovMixing.hardcoreDist
    rw [← Finset.sum_div]
    have heq : (∑ σ : State G, MarkovMixing.hardcoreWeight G lam σ.val) =
        ∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ := by
      calc
        _ = ∑ σ ∈ Finset.univ.filter (MarkovMixing.IsHardcore G),
            MarkovMixing.hardcoreWeight G lam σ :=
          (Finset.sum_subtype _ (by simp) _).symm
        _ = _ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro σ _
          by_cases hs : MarkovMixing.IsHardcore G σ <;>
            simp [hs, MarkovMixing.hardcoreWeight]
    rw [heq, div_self (ne_of_gt (hcPartition_pos G hlam))]

lemma heatBath_stochastic (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) : MarkovMixing.IsStochastic (heatBath G lam A) := by
  classical
  have hp := hcLaw_pos G hlam
  have hden (σ : State G) : 0 < ∑ ζ : State G,
      if ∀ v ∉ A, ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0 := by
    apply Finset.sum_pos'
    · intro ζ _
      split_ifs
      · exact (hp ζ).le
      · rfl
    · exact ⟨σ, Finset.mem_univ _, by simpa using hp σ⟩
  constructor
  · intro σ τ
    unfold heatBath
    split_ifs
    · exact (div_pos (hp τ) (hden σ)).le
    · rfl
  · intro σ
    unfold heatBath
    simp_rw [show ∀ (c : Prop) [Decidable c] (a b : ℝ), (if c then a / b else 0) = (if c then a else 0) / b from fun c _ a b => by split_ifs <;> simp]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (hden σ))

lemma push_dist {Ω : Type} [Fintype Ω] {ν : Ω → ℝ} {K : Matrix Ω Ω ℝ}
    (hν : MarkovMixing.IsDist ν) (hK : MarkovMixing.IsStochastic K) :
    MarkovMixing.IsDist (push ν K) := by
  constructor
  · intro y
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hν.1 x) (hK.1 x y))
  · change (∑ y, ∑ x, ν x * K x y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hK.2, mul_one]
    exact hν.2

lemma finite_pinsker {Ω : Type} [Fintype Ω] [Nonempty Ω] {ν μ : Ω → ℝ}
    (hν : MarkovMixing.IsDist ν) (hμ : MarkovMixing.IsDist μ) (hd : Dominated ν μ) :
    2 * tv ν μ ^ 2 ≤ kl ν μ := by
  classical
  have h := SinkhornHall.lemma_1_1 ν μ hν.1 hμ.1 (hν.2.trans hμ.2.symm)
  have hn : ¬ ∃ x, μ x = 0 ∧ 0 < ν x := by
    rintro ⟨x, hx, hv⟩
    have := hd x hv.ne'
    linarith
  rw [SinkhornHall.klDiv, if_neg hn, hν.2] at h
  have he : kl ν μ = ∑ x, ν x * Real.log (ν x / μ x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ν x = 0 <;> simp [hx]
  rw [he]
  have hr : (∑ x, |ν x - μ x|) ^ 2 / 2 ≤ ∑ x, ν x * Real.log (ν x / μ x) := by
    exact_mod_cast h
  unfold tv
  nlinarith

lemma heatBath_dominated (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) {ν : State G → ℝ}
    (hν : MarkovMixing.IsDist ν) : Dominated ν (push ν (heatBath G lam A)) := by
  classical
  intro σ hσ
  have hd : 0 < ∑ ζ : State G,
      if ∀ v ∉ A, ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0 := by
    apply Finset.sum_pos'
    · intro ζ _
      split_ifs
      · exact (hcLaw_pos G hlam ζ).le
      · rfl
    · exact ⟨σ, Finset.mem_univ _, by simpa using hcLaw_pos G hlam σ⟩
  have hdiag : 0 < heatBath G lam A σ σ := by
    simpa [heatBath] using div_pos (hcLaw_pos G hlam σ) hd
  have hσpos : 0 < ν σ := lt_of_le_of_ne (hν.1 σ) (Ne.symm hσ)
  have hstoch := heatBath_stochastic G hlam A
  exact (mul_pos hσpos hdiag).trans_le
    (Finset.single_le_sum (fun x _ => mul_nonneg (hν.1 x) (hstoch.1 x σ)) (Finset.mem_univ σ))

lemma kl_eq_sum {Ω : Type} [Fintype Ω] (ν μ : Ω → ℝ) :
    kl ν μ = ∑ x, ν x * Real.log (ν x / μ x) := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ν x = 0 <;> simp [hx]


end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma full_fiber_sum (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (σ : State G) (u : V) :
    (∑ ζ : State G, if ∀ v, v ≠ u → ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0) =
    ∑ ζ ∈ Finset.univ.filter (fun ζ : V → Bool => ∀ v, v ≠ u → ζ v = σ.val v),
      MarkovMixing.hardcoreDist G lam ζ := by
  classical
  calc
    _ = ∑ ζ ∈ Finset.univ.filter (MarkovMixing.IsHardcore G),
        if ∀ v, v ≠ u → ζ v = σ.val v then MarkovMixing.hardcoreDist G lam ζ else 0 := by
      exact (Finset.sum_subtype (p := MarkovMixing.IsHardcore G)
        (Finset.univ.filter (MarkovMixing.IsHardcore G)) (by intro ζ; simp)
        (fun ζ => if ∀ v, v ≠ u → ζ v = σ.val v then MarkovMixing.hardcoreDist G lam ζ else 0)).symm
    _ = _ := by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ζ _
      by_cases hz : MarkovMixing.IsHardcore G ζ
      · simp [hz]
      · simp [hz, MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight]

lemma scan_eq (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    K G lam = (Fintype.card V : ℝ)⁻¹ • ∑ u, P G lam u := by
  classical
  ext σ τ
  simp only [K, HardCoreBochner.hcChain, MarkovMixing.subChain, MarkovMixing.glauber,
    Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [P, heatBath, Finset.mem_singleton]
  rw [full_fiber_sum]
  rfl

lemma scan_stochastic [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) : MarkovMixing.IsStochastic (K G lam) := by
  classical
  rw [scan_eq]
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  constructor
  · intro σ τ
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    change 0 ≤ (Fintype.card V : ℝ)⁻¹ * ∑ u, P G lam u σ τ
    exact mul_nonneg (inv_nonneg.mpr hn.le)
      (Finset.sum_nonneg (fun u _ => (heatBath_stochastic G hlam {u}).1 σ τ))
  · intro σ
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    change (∑ τ, (Fintype.card V : ℝ)⁻¹ * ∑ u, P G lam u σ τ) = 1
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hrow (u : V) : ∑ τ, P G lam u σ τ = 1 := (heatBath_stochastic G hlam {u}).2 σ
    simp_rw [hrow]
    simp [hn.ne']

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma update_false_hardcore (G : SimpleGraph V) {σ : V → Bool}
    (hσ : MarkovMixing.IsHardcore G σ) (u : V) :
    MarkovMixing.IsHardcore G (Function.update σ u false) := by
  intro v w hvw
  by_cases hv : v = u
  · subst v; simp
  by_cases hw : w = u
  · subst w; simp
  simpa [Function.update_of_ne hv, Function.update_of_ne hw] using hσ v w hvw

lemma update_true_hardcore (G : SimpleGraph V) [DecidableRel G.Adj] {σ : V → Bool}
    (hσ : MarkovMixing.IsHardcore G σ) (u : V)
    (hu : ∀ v ∈ G.neighborFinset u, σ v = false) :
    MarkovMixing.IsHardcore G (Function.update σ u true) := by
  intro v w hvw
  by_cases hv : v = u
  · subst v
    have hw : w ≠ u := G.ne_of_adj hvw.symm
    simp [Function.update_of_ne hw, hu w (by simpa using hvw)]
  by_cases hw : w = u
  · subst w
    simp [Function.update_of_ne hv, hu v (by simpa using hvw.symm)]
  simpa [Function.update_of_ne hv, Function.update_of_ne hw] using hσ v w hvw

lemma spin_hardcore (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G)
    (u : V) (coin : Bool) : MarkovMixing.IsHardcore G (updateSpin G σ.val u coin) := by
  unfold updateSpin
  split_ifs with h
  · cases coin
    · exact update_false_hardcore G σ.property u
    · exact update_true_hardcore G σ.property u h
  · exact update_false_hardcore G σ.property u

lemma size_update_true (σ : V → Bool) (u : V) :
    size (Function.update σ u true) = size (Function.update σ u false) + 1 := by
  classical
  have hset : (Finset.univ.filter (fun v => Function.update σ u true v = true)) =
      insert u (Finset.univ.filter (fun v => Function.update σ u false v = true)) := by
    ext v
    by_cases hv : v = u <;> simp [hv, Function.update_of_ne]
  have hu : u ∉ Finset.univ.filter (fun v => Function.update σ u false v = true) := by simp
  unfold size
  rw [hset, Finset.card_insert_of_notMem hu]

lemma exterior_two (σ τ : V → Bool) (u : V)
    (he : ∀ v, v ≠ u → τ v = σ v) :
    τ = Function.update σ u false ∨ τ = Function.update σ u true := by
  have hu : τ = Function.update σ u (τ u) := by
    ext v
    by_cases hv : v = u
    · simp [hv]
    · simp [Function.update_of_ne hv, he v hv]
  cases h : τ u
  · exact Or.inl (hu.trans (by rw [h]))
  · exact Or.inr (hu.trans (by rw [h]))

lemma full_fiber_two (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (σ : State G) (u : V) :
    (∑ ζ ∈ Finset.univ.filter (fun ζ : V → Bool => ∀ v, v ≠ u → ζ v = σ.val v),
      MarkovMixing.hardcoreDist G lam ζ) =
      MarkovMixing.hardcoreDist G lam (Function.update σ.val u false) +
      MarkovMixing.hardcoreDist G lam (Function.update σ.val u true) := by
  classical
  have he : Finset.univ.filter (fun ζ : V → Bool => ∀ v, v ≠ u → ζ v = σ.val v) =
      {Function.update σ.val u false, Function.update σ.val u true} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact exterior_two σ.val τ u
    · rintro (rfl | rfl) v hv <;> exact Function.update_of_ne hv _ _
  have hne : Function.update σ.val u false ≠ Function.update σ.val u true := by
    intro h
    have := congrFun h u
    simp at this
  rw [he, Finset.sum_pair hne]

lemma raw_true_iff (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G) (u : V) :
    MarkovMixing.IsHardcore G (Function.update σ.val u true) ↔
      ∀ v ∈ G.neighborFinset u, σ.val v = false := by
  constructor
  · intro h v hv
    have huv : G.Adj u v := by simpa using hv
    have hne : v ≠ u := G.ne_of_adj huv.symm
    have hh := h u v huv
    simp only [Function.update_self, Function.update_of_ne hne] at hh
    cases he : σ.val v <;> simp_all
  · exact update_true_hardcore G σ.property u

lemma raw_true_law (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (σ : State G) (u : V) :
    MarkovMixing.hardcoreDist G lam (Function.update σ.val u true) =
      if ∀ v ∈ G.neighborFinset u, σ.val v = false then
        lam * MarkovMixing.hardcoreDist G lam (Function.update σ.val u false) else 0 := by
  classical
  have h0 := update_false_hardcore G σ.property u
  by_cases h : ∀ v ∈ G.neighborFinset u, σ.val v = false
  · rw [if_pos h]
    have h1 := (raw_true_iff G σ u).mpr h
    simp only [MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight, if_pos h0, if_pos h1]
    change lam ^ size (Function.update σ.val u true) / _ = lam * (lam ^ size (Function.update σ.val u false) / _)
    rw [size_update_true, pow_succ]
    ring
  · rw [if_neg h]
    have h1 : ¬ MarkovMixing.IsHardcore G (Function.update σ.val u true) :=
      mt (raw_true_iff G σ u).mp h
    simp [MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight, h1]

lemma single_site_formula (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ τ : State G) (u : V) :
    P G lam u σ τ =
      (if τ.val = updateSpin G σ.val u true then p lam else 0) +
      (if τ.val = updateSpin G σ.val u false then 1-p lam else 0) := by
  classical
  have h0 := update_false_hardcore G σ.property u
  have hpos : 0 < MarkovMixing.hardcoreDist G lam (Function.update σ.val u false) :=
    hcLaw_pos G hlam ⟨_,h0⟩
  have hne : Function.update σ.val u false ≠ Function.update σ.val u true := by
    intro he
    have := congrFun he u
    simp at this
  have h0ext : ∀ v, v ≠ u → Function.update σ.val u false v = σ.val v := by
    intro v hv; exact Function.update_of_ne hv _ _
  have h1ext : ∀ v, v ≠ u → Function.update σ.val u true v = σ.val v := by
    intro v hv; exact Function.update_of_ne hv _ _
  unfold P heatBath
  simp only [Finset.mem_singleton]
  rw [full_fiber_sum, full_fiber_two, raw_true_law]
  simp only [updateSpin, HardCoreBochner.hcLaw]
  by_cases hu : ∀ v ∈ G.neighborFinset u, σ.val v = false
  · simp only [if_pos hu]
    by_cases he0 : τ.val = Function.update σ.val u false
    · have he1 : τ.val ≠ Function.update σ.val u true := he0 ▸ hne
      simp only [he0, if_pos h0ext, if_neg hne, ite_true, p, zero_add]
      field_simp [hpos.ne', show (1+lam) ≠ 0 by positivity]
      <;> ring
    · by_cases he1 : τ.val = Function.update σ.val u true
      · simp only [he1, if_pos h1ext, if_neg (Ne.symm hne), ite_true, p, add_zero]
        rw [raw_true_law, if_pos hu]
        field_simp [hpos.ne', show (1+lam) ≠ 0 by positivity]
        <;> ring
      · have he : ¬ ∀ v, v ≠ u → τ.val v = σ.val v :=
          fun h => (exterior_two σ.val τ.val u h).elim he0 he1
        simp only [if_neg he, if_neg he0, if_neg he1, add_zero]
  · simp only [if_neg hu]
    by_cases he0 : τ.val = Function.update σ.val u false
    · simp only [he0, if_pos h0ext, ite_true, add_zero]
      rw [div_self hpos.ne']
      ring
    · have he1 : τ.val ≠ Function.update σ.val u true := by
        intro he
        have h := (raw_true_iff G σ u).mp (he ▸ τ.property)
        exact hu h
      have he : ¬ ∀ v, v ≠ u → τ.val v = σ.val v :=
        fun h => (exterior_two σ.val τ.val u h).elim he0 he1
      simp only [if_neg he, if_neg he0, add_zero]

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {Ω : Type} [Fintype Ω]

lemma tv_nonneg (ν μ : Ω → ℝ) : 0 ≤ tv ν μ := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

lemma tv_symm (ν μ : Ω → ℝ) : tv ν μ = tv μ ν := by
  unfold tv
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

lemma tv_triangle (ν μ ρ : Ω → ℝ) : tv ν ρ ≤ tv ν μ + tv μ ρ := by
  unfold tv
  have h := Finset.sum_le_sum (s := Finset.univ) (fun (x : Ω) _ => abs_sub_le (ν x) (μ x) (ρ x))
  rw [Finset.sum_add_distrib] at h
  linarith

lemma tv_contraction (ν μ : Ω → ℝ) {K : Matrix Ω Ω ℝ}
    (hK : MarkovMixing.IsStochastic K) : tv (push ν K) (push μ K) ≤ tv ν μ := by
  unfold tv
  suffices (∑ y, |push ν K y - push μ K y|) ≤ ∑ x, |ν x - μ x| by linarith
  calc
    _ ≤ ∑ y, ∑ x, |ν x - μ x| * K x y := by
      apply Finset.sum_le_sum
      intro y _
      change |(∑ x, ν x * K x y) - ∑ x, μ x * K x y| ≤ _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ x, |ν x * K x y - μ x * K x y| := Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← sub_mul, abs_mul, abs_of_nonneg (hK.1 x y)]
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hK.2, mul_one]

lemma expectation_tv {ν μ : Ω → ℝ} (hν : MarkovMixing.IsDist ν)
    (hμ : MarkovMixing.IsDist μ) (f : Ω → ℝ) {L : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ L) :
    |expectation ν f - expectation μ f| ≤ L * tv ν μ := by
  have heq : expectation ν f - expectation μ f = ∑ x, (ν x - μ x) * (f x - L/2) := by
    unfold expectation
    simp_rw [sub_mul, mul_sub]
    simp_rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hν.2, hμ.2]
    ring
  rw [heq]
  calc
    _ ≤ ∑ x, |(ν x - μ x) * (f x - L/2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |ν x - μ x| * (L/2) := by
      apply Finset.sum_le_sum
      intro x _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply abs_le.mpr
      constructor <;> linarith [(hf x).1, (hf x).2]
    _ = _ := by rw [← Finset.sum_mul]; unfold tv; ring

lemma push_push (ν : Ω → ℝ) (K L : Matrix Ω Ω ℝ) : push (push ν K) L = push ν (K*L) := by
  exact Matrix.vecMul_vecMul ν K L

lemma word_append {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (w w' : List V) :
    word G lam (w ++ w') = word G lam w * word G lam w' := by
  simp [word]

lemma word_stochastic {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) (w : List V) :
    MarkovMixing.IsStochastic (word G lam w) := by
  classical
  induction w with
  | nil =>
    constructor
    · intro σ τ
      simp only [word, List.map_nil, List.prod_nil, Matrix.one_apply]
      split_ifs <;> norm_num
    · intro σ
      simp [word, Matrix.one_apply]
  | cons u w ih =>
    have hP := heatBath_stochastic G hlam {u}
    change MarkovMixing.IsStochastic (P G lam u * word G lam w)
    constructor
    · intro σ τ
      exact Finset.sum_nonneg fun ζ _ => mul_nonneg (hP.1 σ ζ) (ih.1 ζ τ)
    · intro σ
      change (∑ τ, ∑ ζ, P G lam u σ ζ * word G lam w ζ τ) = 1
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ih.2, mul_one]
      exact hP.2 σ

lemma tv_word_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam)
    (ν : State G → ℝ) (w : List V) :
    tv ν (push ν (word G lam w)) ≤ (w.map (fun u => tv ν (push ν (P G lam u)))).sum := by
  classical
  induction w with
  | nil => simp [word, push, tv, Matrix.vecMul_one]
  | cons u w ih =>
    change tv ν (push ν (P G lam u * word G lam w)) ≤ _
    rw [← push_push]
    calc
      _ ≤ tv ν (push ν (word G lam w)) +
          tv (push ν (word G lam w)) (push (push ν (P G lam u)) (word G lam w)) := tv_triangle _ _ _
      _ ≤ (w.map (fun u => tv ν (push ν (P G lam u)))).sum + tv ν (push ν (P G lam u)) :=
        add_le_add ih (tv_contraction _ _ (word_stochastic G hlam w))
      _ = _ := by simp; ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma size_sum (σ : V → Bool) : (size σ : ℝ) = ∑ v, if σ v = true then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp [size]

lemma nbrSize_sum (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (σ : V → Bool) :
    (nbrSize G u σ : ℝ) = ∑ v, if G.Adj u v then (if σ v = true then 1 else 0) else 0 := by
  classical
  conv_rhs => rw [← Finset.sum_filter]
  have he : Finset.univ.filter (G.Adj u) = G.neighborFinset u := by ext v; simp
  rw [he, ← Finset.sum_filter]
  simp [nbrSize]

lemma nbrSize_zero (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (σ : V → Bool) :
    nbrSize G u σ = 0 ↔ ∀ v ∈ G.neighborFinset u, σ v = false := by
  simp only [nbrSize, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h v hv
    cases hs : σ v <;> simp_all
  · intro h v hv
    simp [h v hv]

lemma degree_sum_bound (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ}
    (hΔ : DegreeBound G Δ) (σ : V → Bool) :
    (∑ u, (nbrSize G u σ : ℝ)) ≤ Δ * size σ := by
  classical
  simp_rw [nbrSize_sum]
  rw [Finset.sum_comm, size_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : σ v = true
  · simp only [hv, ite_true, mul_one]
    have heq : (∑ u : V, if G.Adj u v then (1 : ℝ) else 0) = G.degree v := by
      simp_rw [G.adj_comm (v := v)]
      rw [← Finset.sum_filter]
      simp [← SimpleGraph.mem_neighborFinset]
    rw [heq]
    exact_mod_cast hΔ v
  · simp [hv]

lemma site_occupancy (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) (u : V) :
    (∑ τ : State G, P G lam u σ τ * (if τ.val u = true then (1 : ℝ) else 0)) =
      p lam * (if nbrSize G u σ.val = 0 then 1 else 0) := by
  classical
  let s0 : State G := ⟨updateSpin G σ.val u false, spin_hardcore G σ u false⟩
  let s1 : State G := ⟨updateSpin G σ.val u true, spin_hardcore G σ u true⟩
  have he0 (τ : State G) : (τ.val = updateSpin G σ.val u false) ↔ τ = s0 := by
    constructor
    · intro ht; apply Subtype.ext; exact ht
    · exact congrArg Subtype.val
  have he1 (τ : State G) : (τ.val = updateSpin G σ.val u true) ↔ τ = s1 := by
    constructor
    · intro ht; apply Subtype.ext; exact ht
    · exact congrArg Subtype.val
  simp_rw [single_site_formula G hlam, he0, he1, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [s0, s1, updateSpin, Function.update_self]
  by_cases h : ∀ v ∈ G.neighborFinset u, σ.val v = false
  · simp only [if_pos h, (nbrSize_zero G u σ.val).mpr h, ite_true, Bool.false_eq_true, ite_false, mul_one, mul_zero, add_zero]
  · have hz : nbrSize G u σ.val ≠ 0 := mt (nbrSize_zero G u σ.val).mp h
    simp only [if_neg h, if_neg hz, Bool.false_eq_true, ite_false, mul_zero, add_zero]

lemma expected_site_occupancy (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (u : V) :
    expectation (push ν (P G lam u)) (fun σ => if σ.val u = true then 1 else 0) =
      p lam * expectation ν (fun σ => if nbrSize G u σ.val = 0 then 1 else 0) := by
  unfold expectation
  change (∑ τ, (∑ σ, ν σ * P G lam u σ τ) * _) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, site_occupancy G hlam]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

/-- The two feasible outputs of a heat-bath proposal. -/
def spinState (G : SimpleGraph V) [DecidableRel G.Adj] (σ : State G) (u : V) (coin : Bool) : State G :=
  ⟨updateSpin G σ.val u coin, spin_hardcore G σ u coin⟩

lemma single_site_average (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) (u : V) (f : State G → ℝ) :
    (∑ τ : State G, P G lam u σ τ * f τ) =
      p lam * f (spinState G σ u true) + (1-p lam) * f (spinState G σ u false) := by
  classical
  have he (coin : Bool) (τ : State G) : (τ.val = updateSpin G σ.val u coin) ↔ τ = spinState G σ u coin := by
    constructor
    · intro ht; apply Subtype.ext; exact ht
    · exact congrArg Subtype.val
  simp_rw [single_site_formula G hlam, he, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma expectation_push {Ω : Type} [Fintype Ω] (ν : Ω → ℝ) (K : Matrix Ω Ω ℝ) (f : Ω → ℝ) :
    expectation (push ν K) f = ∑ σ, ν σ * ∑ τ, K σ τ * f τ := by
  unfold expectation
  change (∑ τ, (∑ σ, ν σ * K σ τ) * f τ) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]

lemma p_pos {lam : ℝ} (hlam : 0 < lam) : 0 < p lam := by
  exact div_pos hlam (by positivity)

lemma one_sub_p_pos {lam : ℝ} (hlam : 0 < lam) : 0 < 1-p lam := by
  unfold p
  have h : 0 < 1+lam := by positivity
  apply sub_pos.mpr
  exact (div_lt_one h).mpr (by linarith)

/-- Indicator that every vertex in A is unoccupied. -/
def emptyOn (G : SimpleGraph V) (A : Finset V) (σ : State G) : ℝ :=
  if ∀ v ∈ A, σ.val v = false then 1 else 0

lemma emptyOn_nonneg (G : SimpleGraph V) (A : Finset V) (σ : State G) : 0 ≤ emptyOn G A σ := by
  unfold emptyOn; split_ifs <;> norm_num

lemma emptyOn_false_update (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : State G) (u : V) (A : Finset V) :
    emptyOn G A (spinState G σ u false) = emptyOn G (A.erase u) σ := by
  have he : (∀ v ∈ A, (spinState G σ u false).val v = false) ↔ ∀ v ∈ A.erase u, σ.val v = false := by
    constructor
    · intro h v hv
      obtain ⟨hvu,hvA⟩ := Finset.mem_erase.mp hv
      simpa [spinState, updateSpin, Function.update_of_ne hvu] using h v hvA
    · intro h v hv
      by_cases hvu : v = u
      · subst v; simp [spinState, updateSpin]
      · simpa [spinState, updateSpin, Function.update_of_ne hvu] using h v (Finset.mem_erase.mpr ⟨hvu,hv⟩)
  simp only [emptyOn, he]

lemma emptyOn_outside_update (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : State G) (u : V) (A : Finset V) (hu : u ∉ A) (coin : Bool) :
    emptyOn G A (spinState G σ u coin) = emptyOn G A σ := by
  have he : (∀ v ∈ A, (spinState G σ u coin).val v = false) ↔ ∀ v ∈ A, σ.val v = false := by
    have hvu (v : V) (hv : v ∈ A) : v ≠ u := by intro h; exact hu (h ▸ hv)
    simp only [spinState, updateSpin]
    constructor <;> intro h v hv <;> simpa [Function.update_of_ne (hvu v hv)] using h v hv
  simp only [emptyOn, he]

lemma emptyOn_step_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν) (u : V) (A : Finset V) :
    (1-p lam) * expectation ν (emptyOn G (A.erase u)) ≤
      expectation (push ν (P G lam u)) (emptyOn G A) := by
  rw [expectation_push]
  simp_rw [single_site_average G hlam, emptyOn_false_update]
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hh : 0 ≤ p lam * emptyOn G A (spinState G σ u true) :=
    mul_nonneg (p_pos hlam).le (emptyOn_nonneg G A _)
  nlinarith [hν.1 σ]

lemma emptyOn_step_outside (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (u : V) (A : Finset V) (hu : u ∉ A) :
    expectation (push ν (P G lam u)) (emptyOn G A) = expectation ν (emptyOn G A) := by
  rw [expectation_push]
  simp_rw [single_site_average G hlam, emptyOn_outside_update G _ u A hu]
  apply Finset.sum_congr rfl
  intro σ _
  ring

lemma emptyOn_word_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν)
    (w : List V) (A : Finset V) (hcover : A ⊆ w.toFinset) :
    (1-p lam)^A.card ≤ expectation (push ν (word G lam w)) (emptyOn G A) := by
  classical
  induction w using List.reverseRecOn generalizing A with
  | nil =>
    have hA : A = ∅ := by simpa using hcover
    subst A
    simp [word, push, emptyOn, expectation, hν.2]
  | append_singleton w u ih =>
    rw [word_append]
    simp only [word, List.map_singleton, List.prod_singleton]
    rw [← push_push]
    by_cases hu : u ∈ A
    · have hc : A.erase u ⊆ w.toFinset := by
        intro v hv
        have hvA := (Finset.mem_erase.mp hv).2
        have hmem := hcover hvA
        simpa [List.toFinset_append, Finset.mem_union, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_singleton, (Finset.mem_erase.mp hv).1] using hmem
      have hh := mul_le_mul_of_nonneg_left (ih (A.erase u) hc) (one_sub_p_pos hlam).le
      have hcA : A.card = (A.erase u).card+1 := by simpa using (Finset.card_erase_add_one hu).symm
      rw [hcA, pow_succ]
      refine le_trans ?_ (emptyOn_step_lower G hlam _ (push_dist hν (word_stochastic G hlam w)) u A)
      simpa [mul_comm] using hh
    · have hc : A ⊆ w.toFinset := by
        intro v hv
        have hmem := hcover hv
        have hvu : v ≠ u := by intro h; exact hu (h ▸ hv)
        simpa [List.toFinset_append, Finset.mem_union, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_singleton, hvu] using hmem
      rw [emptyOn_step_outside G hlam _ u A hu]
      exact ih A hc

lemma point_dist {Ω : Type} [Fintype Ω] [DecidableEq Ω] (x : Ω) : MarkovMixing.IsDist (point x) := by
  constructor
  · intro y; unfold point; split_ifs <;> norm_num
  · simp [point]

lemma site_step_outside (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) {u v : V} (hvu : v ≠ u) :
    expectation (push ν (P G lam u)) (fun σ => if σ.val v = true then (1 : ℝ) else 0) =
      expectation ν (fun σ => if σ.val v = true then 1 else 0) := by
  rw [expectation_push]
  simp_rw [single_site_average G hlam]
  simp only [spinState, updateSpin, Function.update_of_ne hvu]
  apply Finset.sum_congr rfl
  intro σ _
  ring

lemma site_word_outside (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (w : List V) {v : V} (hv : v ∉ w) :
    expectation (push ν (word G lam w)) (fun σ => if σ.val v = true then (1 : ℝ) else 0) =
      expectation ν (fun σ => if σ.val v = true then 1 else 0) := by
  induction w generalizing ν with
  | nil => simp [word, push]
  | cons u w ih =>
    have hparts : v ≠ u ∧ v ∉ w := by simpa using hv
    have hvu := hparts.1
    have hvw := hparts.2
    change expectation (push ν (P G lam u * word G lam w)) _ = _
    rw [← push_push, ih _ hvw, site_step_outside G hlam _ hvu]

lemma q_power (lam : ℝ) (hlam : 0 < lam) (k : ℕ) :
    (1-p lam)^k = (1+lam)^(-(k:ℝ)) := by
  have hq : 1-p lam = 1/(1+lam) := by unfold p; field_simp <;> ring
  rw [hq, Real.rpow_neg (by positivity), Real.rpow_natCast, one_div_pow]
  simp only [one_div]

lemma second_sweep_marginal (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (ν : State G → ℝ) (hν : MarkovMixing.IsDist ν)
    (w₁ w₂ : List V) (h₁ : IsSweep Finset.univ w₁) (h₂ : IsSweep Finset.univ w₂) (v : V) :
    p lam * (1+lam)^(-(G.degree v:ℝ)) ≤
      expectation (push ν (word G lam (w₁++w₂))) (fun σ => if σ.val v = true then 1 else 0) := by
  classical
  have hmem : v ∈ w₂ := by
    rw [← List.mem_toFinset, h₂.2]
    exact Finset.mem_univ _
  obtain ⟨pre,post,hw⟩ := List.mem_iff_append.mp hmem
  have hpost : v ∉ post := by
    have hh := h₂.1
    rw [hw] at hh
    exact (List.nodup_cons.mp (List.nodup_append.mp hh).2.1).1
  have he : w₁++w₂ = ((w₁++pre)++[v])++post := by rw [hw]; simp [List.append_assoc]
  rw [he, word_append, ← push_push, site_word_outside G hlam _ post hpost,
    word_append, ← push_push]
  simp only [word, List.map_singleton, List.prod_singleton]
  rw [expected_site_occupancy G hlam]
  have hcover : G.neighborFinset v ⊆ (w₁++pre).toFinset := by
    intro u hu
    simp [List.toFinset_append, h₁.2]
  have hh := emptyOn_word_lower G hlam ν hν (w₁++pre) (G.neighborFinset v) hcover
  have hevent : emptyOn G (G.neighborFinset v) =
      (fun σ : State G => if nbrSize G v σ.val = 0 then (1:ℝ) else 0) := by
    ext σ
    simp only [emptyOn, nbrSize_zero]
  rw [hevent, q_power lam hlam] at hh
  exact mul_le_mul_of_nonneg_left hh (p_pos hlam).le

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma heatBath_reversible (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (A : Finset V)
    (σ τ : State G) :
    HardCoreBochner.hcLaw G lam σ * heatBath G lam A σ τ =
      HardCoreBochner.hcLaw G lam τ * heatBath G lam A τ σ := by
  classical
  by_cases he : ∀ v ∉ A, τ.val v = σ.val v
  · have he' : ∀ v ∉ A, σ.val v = τ.val v := fun v hv => (he v hv).symm
    have hden : (∑ ζ : State G, if ∀ v ∉ A, ζ.val v = σ.val v then HardCoreBochner.hcLaw G lam ζ else 0) =
        ∑ ζ : State G, if ∀ v ∉ A, ζ.val v = τ.val v then HardCoreBochner.hcLaw G lam ζ else 0 := by
      apply Finset.sum_congr rfl
      intro ζ _
      have hiff : (∀ v ∉ A, ζ.val v = σ.val v) ↔ ∀ v ∉ A, ζ.val v = τ.val v := by
        constructor
        · intro h v hv; exact (h v hv).trans (he' v hv)
        · intro h v hv; exact (h v hv).trans (he v hv)
      simp only [hiff]
    simp only [heatBath, if_pos he, if_pos he', hden]
    ring
  · have he' : ¬∀ v ∉ A, σ.val v = τ.val v :=
      fun h => he (fun v hv => (h v hv).symm)
    simp [heatBath, he, he']

lemma heatBath_stationary (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (A : Finset V) :
    push (HardCoreBochner.hcLaw G lam) (heatBath G lam A) = HardCoreBochner.hcLaw G lam := by
  ext τ
  change (∑ σ, HardCoreBochner.hcLaw G lam σ * heatBath G lam A σ τ) = _
  simp_rw [heatBath_reversible G lam A, ← Finset.mul_sum, (heatBath_stochastic G hlam A).2 τ, mul_one]

lemma word_stationary (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (w : List V) :
    push (HardCoreBochner.hcLaw G lam) (word G lam w) = HardCoreBochner.hcLaw G lam := by
  induction w with
  | nil => simp [word, push]
  | cons u w ih =>
    change push _ (P G lam u * word G lam w) = _
    rw [← push_push]
    simp only [P]
    rw [heatBath_stationary G hlam {u}, ih]

lemma point_mixture_expectation (G : SimpleGraph V) [DecidableRel G.Adj] (ν : State G → ℝ)
    (K : Matrix (State G) (State G) ℝ) (f : State G → ℝ) :
    expectation (push ν K) f = ∑ σ, ν σ * expectation (push (point σ) K) f := by
  rw [expectation_push]
  apply Finset.sum_congr rfl
  intro σ _
  simp [push, Matrix.vecMul, dotProduct, point, expectation]

lemma equilibrium_occupancy_bound (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) :
    p lam * Fintype.card V * (1+lam)^(-avgDegree G) ≤ occupiedMean G lam := by
  classical
  let w := (Finset.univ : Finset V).toList
  have hw : IsSweep Finset.univ w := ⟨Finset.nodup_toList _, by simp [w]⟩
  have hi (I : State G) : p lam * Fintype.card V * (1+lam)^(-avgDegree G) ≤
      expectation (push (point I) (word G lam (w++w))) (fun σ => size σ.val) := by
    have hh := LocalOccupancyIS.Glauber.lemma_9 G (avgDegree G) lam hlam le_rfl w w hw hw I
    exact hh.2.2.trans hh.2.1
  let π := HardCoreBochner.hcLaw G lam
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun I _ =>
    mul_le_mul_of_nonneg_left (hi I) (hcLaw_pos G hlam I).le)
  rw [← Finset.sum_mul, (hcLaw_dist G hlam).2, one_mul] at hh
  rw [← point_mixture_expectation, word_stationary G hlam] at hh
  exact hh

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma weight_product (lam : ℝ) (σ : V → Bool) :
    lam ^ size σ = ∏ v, if σ v = true then lam else 1 := by
  simp [size, Finset.prod_ite]

lemma partition_upper (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) :
    (∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ) ≤ (1+lam) ^ Fintype.card V := by
  calc
    _ ≤ ∑ σ : V → Bool, lam ^ size σ := by
      apply Finset.sum_le_sum
      intro σ _
      unfold MarkovMixing.hardcoreWeight
      split_ifs
      · rfl
      · exact (pow_pos hlam _).le
    _ = _ := by
      simp_rw [weight_product]
      calc
        _ = ∏ _ : V, ∑ b : Bool, if b = true then lam else 1 :=
          (Fintype.prod_sum (fun (_ : V) (b : Bool) => if b = true then lam else 1)).symm
        _ = _ := by simp [Fintype.sum_bool, add_comm]

lemma hcLaw_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) :
    (min 1 lam) ^ Fintype.card V / (1+lam) ^ Fintype.card V ≤
      HardCoreBochner.hcLaw G lam σ := by
  have hn : min 1 lam ^ Fintype.card V ≤ lam ^ size σ.val := by
    rw [weight_product]
    calc
      _ = ∏ _ : V, min 1 lam := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod
        · intro _ _; exact le_min (by norm_num) hlam.le
        · intro v _
          split_ifs
          · exact min_le_right _ _
          · exact min_le_left _ _
  change _ ≤ MarkovMixing.hardcoreWeight G lam σ.val / _
  rw [MarkovMixing.hardcoreWeight, if_pos σ.property]
  exact div_le_div₀ (pow_pos hlam _).le hn
    (hcPartition_pos G hlam) (partition_upper G hlam)

lemma hcLaw_log_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) (σ : State G) :
    -entropyBound (Fintype.card V) lam ≤ Real.log (HardCoreBochner.hcLaw G lam σ) := by
  have hm : 0 < min 1 lam := lt_min (by norm_num) hlam
  have hp : 0 < 1 + lam := by positivity
  have h := Real.log_le_log (div_pos (pow_pos hm _) (pow_pos hp _)) (hcLaw_lower G hlam σ)
  rw [Real.log_div (pow_pos hm _).ne' (pow_pos hp _).ne', Real.log_pow, Real.log_pow] at h
  unfold entropyBound
  rw [Real.log_div hp.ne' hm.ne']
  linarith

lemma initial_entropy_bound (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ}
    (hlam : 0 < lam) {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) :
    kl ν (HardCoreBochner.hcLaw G lam) ≤ entropyBound (Fintype.card V) lam := by
  classical
  rw [kl_eq_sum]
  calc
    _ ≤ ∑ σ, ν σ * entropyBound (Fintype.card V) lam := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hz : ν σ = 0
      · simp [hz]
      · have hn : 0 < ν σ := lt_of_le_of_ne (hν.1 σ) (Ne.symm hz)
        have hle : ν σ ≤ 1 := by
          rw [← hν.2]
          exact Finset.single_le_sum (fun (x : State G) _ => hν.1 x) (Finset.mem_univ σ)
        apply mul_le_mul_of_nonneg_left _ hn.le
        rw [Real.log_div hn.ne' (hcLaw_pos G hlam σ).ne']
        have hlν : Real.log (ν σ) ≤ 0 := Real.log_nonpos hn.le hle
        have hlπ := hcLaw_log_lower G hlam σ
        linarith
    _ = _ := by rw [← Finset.sum_mul, hν.2, one_mul]

lemma mul_log_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log (x/y) = x * Real.log x - x * Real.log y := by
  by_cases hz : x = 0
  · simp [hz]
  · rw [Real.log_div hz hy.ne']; ring

lemma kl_mixture {Ω U : Type} [Fintype Ω] [Fintype U]
    (π : Ω → ℝ) (hπ : ∀ x, 0 < π x) (μ : U → Ω → ℝ)
    (hμ : ∀ u x, 0 ≤ μ u x) (w : U → ℝ) (hw : ∀ u, 0 ≤ w u) (hs : ∑ u, w u = 1) :
    kl (fun x => ∑ u, w u * μ u x) π ≤ ∑ u, w u * kl (μ u) π := by
  classical
  simp_rw [kl_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hm : 0 ≤ ∑ u, w u * μ u x :=
    Finset.sum_nonneg (fun u _ => mul_nonneg (hw u) (hμ u x))
  rw [mul_log_div hm (hπ x)]
  have hj := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
    (w := w) (p := fun u => μ u x) (fun u _ => hw u) hs (fun u _ => hμ u x)
  simp only [smul_eq_mul] at hj
  calc
    _ ≤ (∑ u, w u * (μ u x * Real.log (μ u x))) - (∑ u, w u * μ u x) * Real.log (π x) :=
      sub_le_sub_right hj _
    _ = _ := by
      simp_rw [mul_log_div (hμ _ x) (hπ x), mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
      rw [Finset.sum_mul]

lemma push_scan [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ)
    (ν : State G → ℝ) (σ : State G) :
    push ν (K G lam) σ = (Fintype.card V : ℝ)⁻¹ * ∑ u, push ν (P G lam u) σ := by
  rw [scan_eq]
  change (∑ τ, ν τ * ((Fintype.card V : ℝ)⁻¹ • ∑ u, P G lam u) τ σ) = _
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  change (∑ τ, ν τ * ((Fintype.card V : ℝ)⁻¹ * P G lam u τ σ)) =
    (Fintype.card V : ℝ)⁻¹ * ∑ τ, ν τ * P G lam u τ σ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

lemma scan_entropy_drop [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {lam : ℝ} (hlam : 0 < lam) {ν : State G → ℝ} (hν : MarkovMixing.IsDist ν) :
    (2 / (Fintype.card V : ℝ)) * ∑ u, tv ν (push ν (P G lam u)) ^ 2 ≤
      kl ν (HardCoreBochner.hcLaw G lam) - kl (push ν (K G lam)) (HardCoreBochner.hcLaw G lam) := by
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hw : (∑ _ : V, (Fintype.card V : ℝ)⁻¹) = 1 := by simp [hn.ne']
  have hm := kl_mixture (HardCoreBochner.hcLaw G lam) (hcLaw_pos G hlam)
    (fun u => push ν (P G lam u))
    (fun u x => (push_dist hν (heatBath_stochastic G hlam {u})).1 x)
    (fun _ => (Fintype.card V : ℝ)⁻¹) (fun _ => inv_nonneg.mpr hn.le) hw
  have hm0 : (fun x => ∑ u, (Fintype.card V : ℝ)⁻¹ * push ν (P G lam u) x) = push ν (K G lam) := by
    ext x
    rw [← Finset.mul_sum, push_scan]
  rw [hm0, ← Finset.mul_sum] at hm
  have hloc (u : V) :
      2 * tv ν (push ν (P G lam u)) ^ 2 ≤
        kl ν (HardCoreBochner.hcLaw G lam) - kl (push ν (P G lam u)) (HardCoreBochner.hcLaw G lam) := by
    have hh := (LocalOccupancyIS.Glauber.lemma_7 G lam hlam u ν hν).2.2
      (P G lam u) (by simp)
    rw [hh.2.2.1]
    exact hh.2.2.2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hloc u)
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [← Finset.mul_sum] at hsum
  have hsum' := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
  have hcancel : (Fintype.card V : ℝ)⁻¹ * Fintype.card V = 1 := inv_mul_cancel₀ hn.ne'
  calc
    _ = (Fintype.card V : ℝ)⁻¹ * (2 * ∑ u, tv ν (push ν (P G lam u)) ^ 2) := by ring
    _ ≤ _ := hsum'
    _ = kl ν (HardCoreBochner.hcLaw G lam) - (Fintype.card V : ℝ)⁻¹ *
        ∑ u, kl (push ν (P G lam u)) (HardCoreBochner.hcLaw G lam) := by
      rw [mul_sub, ← mul_assoc, hcancel, one_mul]
    _ ≤ _ := sub_le_sub_left hm _

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

lemma partition_eq_full (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    partition G lam = ∑ σ : V → Bool, MarkovMixing.hardcoreWeight G lam σ := by
  classical
  unfold partition
  calc
    _ = ∑ σ ∈ Finset.univ.filter (MarkovMixing.IsHardcore G), lam ^ size σ :=
      (Finset.sum_subtype _ (by simp) _).symm
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro σ _
      rfl

lemma partition_pos (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) :
    0 < partition G lam := by rw [partition_eq_full]; exact hcPartition_pos G hlam

lemma hcLaw_partition (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (σ : State G) :
    HardCoreBochner.hcLaw G lam σ = lam ^ size σ.val / partition G lam := by
  rw [partition_eq_full]
  simp [HardCoreBochner.hcLaw, MarkovMixing.hardcoreDist, MarkovMixing.hardcoreWeight, σ.property, size]

lemma occupiedMean_ratio (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) :
    occupiedMean G lam = (∑ σ : State G, (size σ.val : ℝ)*lam^size σ.val) / partition G lam := by
  unfold occupiedMean expectation
  simp_rw [hcLaw_partition, div_mul_eq_mul_div, mul_comm (lam ^ _) (size _ : ℝ)]
  rw [Finset.sum_div]

lemma power_cross_nonneg {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (a b : ℕ) :
    0 ≤ ((a:ℝ)-b)*(y^a*x^b-x^a*y^b) := by
  have hy : 0 < y := hx.trans_le hxy
  rcases le_total a b with hab | hba
  · obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hab
    have hpow : x^c ≤ y^c := pow_le_pow_left₀ hx.le hxy c
    have hcross : y^a*x^(a+c)-x^a*y^(a+c) ≤ 0 := by
      calc
        _ = x^a*y^a*(x^c-y^c) := by rw [pow_add, pow_add]; ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hpow)
    exact mul_nonneg_of_nonpos_of_nonpos (by push_cast; linarith : (a:ℝ)-(a+c:ℕ) ≤ 0) hcross
  · obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hba
    have hpow : x^c ≤ y^c := pow_le_pow_left₀ hx.le hxy c
    have hcross : 0 ≤ y^(b+c)*x^b-x^(b+c)*y^b := by
      calc
        _ = x^b*y^b*(y^c-x^c) := by rw [pow_add, pow_add]; ring
        _ ≥ 0 := mul_nonneg (by positivity) (sub_nonneg.mpr hpow)
    exact mul_nonneg (by push_cast; linarith : (0:ℝ) ≤ (b+c:ℕ)-b) hcross

lemma finite_gibbs_comparison {Ω : Type} [Fintype Ω] (f : Ω → ℕ)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (∑ i, (f i:ℝ)*x^(f i)) * (∑ i, y^(f i)) ≤
      (∑ i, (f i:ℝ)*y^(f i)) * (∑ i, x^(f i)) := by
  have hh : 0 ≤ ∑ i : Ω, ∑ j : Ω,
      ((f i:ℝ)-f j)*(y^(f i)*x^(f j)-x^(f i)*y^(f j)) := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun j _ => power_cross_nonneg hx hxy (f i) (f j))
  have he : (∑ i : Ω, ∑ j : Ω,
      ((f i:ℝ)-f j)*(y^(f i)*x^(f j)-x^(f i)*y^(f j))) =
      2*((∑ i, (f i:ℝ)*y^(f i))*(∑ i,x^(f i)) -
        (∑ i,(f i:ℝ)*x^(f i))*(∑ i,y^(f i))) := by
    calc
      _ = ∑ i : Ω, ∑ j : Ω,
          (((f i:ℝ)*y^(f i))*x^(f j) - ((f i:ℝ)*x^(f i))*y^(f j) -
           y^(f i)*((f j:ℝ)*x^(f j)) + x^(f i)*((f j:ℝ)*y^(f j))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        ring
  rw [he] at hh
  linarith

lemma occupiedMean_mono (G : SimpleGraph V) [DecidableRel G.Adj] {x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) : occupiedMean G x ≤ occupiedMean G y := by
  rw [occupiedMean_ratio, occupiedMean_ratio]
  apply (div_le_div_iff₀ (partition_pos G hx) (partition_pos G (hx.trans_le hxy))).mpr
  exact finite_gibbs_comparison (fun σ : State G => size σ.val) hx hxy

lemma avgDegree_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] : 0 ≤ avgDegree G := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)

lemma log_partition_upper (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) :
    Real.log (partition G lam) ≤ Fintype.card V*lam := by
  have hp : 0 < 1+lam := by positivity
  have hZ : partition G lam ≤ (1+lam)^Fintype.card V := by rw [partition_eq_full]; exact partition_upper G hlam
  have hh := Real.log_le_log (partition_pos G hlam) hZ
  rw [Real.log_pow] at hh
  have hlog : Real.log (1+lam) ≤ lam := by
    have h := Real.log_le_sub_one_of_pos hp
    linarith
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)
  exact hh.trans hm

lemma occupancy_exp_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) :
    lam*Fintype.card V*Real.exp (-(avgDegree G+1)*lam) ≤ occupiedMean G lam := by
  have hp : 0 < 1+lam := by positivity
  have hd : 0 ≤ avgDegree G+1 := by linarith [avgDegree_nonneg G]
  have heq : p lam*Fintype.card V*(1+lam)^(-avgDegree G) =
      lam*Fintype.card V*Real.exp (-(avgDegree G+1)*Real.log (1+lam)) := by
    have hex : -(avgDegree G+1)*Real.log (1+lam) =
        Real.log (1+lam)*(-avgDegree G) + -Real.log (1+lam) := by ring
    rw [hex, Real.exp_add, Real.exp_neg, Real.exp_log hp, Real.rpow_def_of_pos hp]
    unfold p
    ring
  have hlog : Real.log (1+lam) ≤ lam := by
    have h := Real.log_le_sub_one_of_pos hp
    linarith
  have hex := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hd))
  have hm := mul_le_mul_of_nonneg_left hex (show 0 ≤ lam*Fintype.card V by positivity)
  rw [← heq] at hm
  exact hm.trans (equilibrium_occupancy_bound G hlam)

lemma occupancy_min_lower (G : SimpleGraph V) [DecidableRel G.Adj] {lam : ℝ} (hlam : 0 < lam) :
    (1/Real.exp 1) * min (lam*Fintype.card V) (Fintype.card V/(avgDegree G+1)) ≤ occupiedMean G lam := by
  let y := min lam (1/(avgDegree G+1))
  have hd : 0 < avgDegree G+1 := by linarith [avgDegree_nonneg G]
  have hy : 0 < y := lt_min hlam (by positivity)
  have hylam : y ≤ lam := min_le_left _ _
  have hyd : (avgDegree G+1)*y ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right lam (1/(avgDegree G+1))) hd.le
    simpa [y, hd.ne'] using hh
  have hex : Real.exp (-1) ≤ Real.exp (-(avgDegree G+1)*y) := Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left hex (show 0 ≤ y*Fintype.card V by positivity)
  have hh := hm.trans ((occupancy_exp_lower G hy).trans (occupiedMean_mono G hy hylam))
  have heq : y*Fintype.card V*Real.exp (-1) =
      (1/Real.exp 1) * min (lam*Fintype.card V) (Fintype.card V/(avgDegree G+1)) := by
    dsimp [y]
    rw [Real.exp_neg, min_mul_of_nonneg _ _ (Nat.cast_nonneg (Fintype.card V) : (0:ℝ) ≤ _)]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq] at hh
  exact hh

lemma partition_empty (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (hk : Fintype.card V = 0) :
    partition G lam = 1 := by
  haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hk
  simp [partition, size]
  exact Fintype.card_eq_one_iff.mpr ⟨(⟨_,empty_hardcore G⟩ : State G), fun _ => Subsingleton.elim _ _⟩

lemma occupiedMean_empty (G : SimpleGraph V) [DecidableRel G.Adj] (lam : ℝ) (hk : Fintype.card V = 0) :
    occupiedMean G lam = 0 := by
  haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hk
  simp [occupiedMean, expectation, size]

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma cutoff_div_scale {Δ b : ℝ} {t : ℕ} (hb : 0 ≤ b) :
    cutoff Δ t b/scale t b = 4*Real.exp 1*D Δ t b^(2*t) := by
  unfold cutoff
  field_simp [(scale_pos t hb).ne']
  <;> ring

lemma cutoff_ge_scale {Δ b : ℝ} {t : ℕ} (hb : 0 ≤ b) (hD : 1 ≤ D Δ t b) :
    scale t b ≤ cutoff Δ t b := by
  have hs := scale_pos t hb
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hpow : 1 ≤ D Δ t b^(2*t) := one_le_pow₀ hD
  unfold cutoff
  have hh := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*Real.exp 1*scale t b by positivity)
  nlinarith

lemma degree_parameter_identity {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 0 < D Δ t b) :
    4*(t:ℝ)*fugacity Δ t b*scale t b*(cutoff Δ t b/scale t b)^(1-1/(t:ℝ)) =
      4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b := by
  have hs := scale_pos t hb
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hr : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*t)]
    norm_num
  rw [cutoff_div_scale hb]
  unfold fugacity
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow, Real.log_one]
  rw [hr]
  push_cast
  field_simp
  <;> ring

lemma small_graph_degree_bound {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b) (hsmall : (Fintype.card V:ℝ) ≤ cutoff Δ t b) :
    fugacity Δ t b*(avgDegree F+1) ≤
      4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hs := scale_pos t hb
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have hlam := fugacity_pos hb hD0
  have ha : 0 ≤ 1-1/(t:ℝ) := by
    have hh : 1/(t:ℝ) ≤ 1 := (div_le_one (by linarith : (0:ℝ) < t)).mpr ht'
    linarith
  have hdeg := (LocalOccupancyIS.Glauber.lemma_5 F t ht b hb hk hd 0 (fun _ => 0) (by simp)).2
  have hM : 1 ≤ cutoff Δ t b/scale t b := (le_div_iff₀ hs).mpr (by simpa using cutoff_ge_scale hb hD1)
  have hmax : max 1 (((Fintype.card V:ℝ)/scale t b)^(1-1/(t:ℝ))) ≤
      (cutoff Δ t b/scale t b)^(1-1/(t:ℝ)) := by
    apply max_le
    · exact Real.one_le_rpow hM ha
    · exact Real.rpow_le_rpow (div_nonneg (Nat.cast_nonneg _) hs.le)
        (div_le_div_of_nonneg_right hsmall hs.le) ha
  have hm := mul_le_mul_of_nonneg_left hmax (show 0 ≤ 4*(t:ℝ)*scale t b by positivity)
  have hm' := mul_le_mul_of_nonneg_left (hdeg.trans hm) hlam.le
  calc
    _ ≤ fugacity Δ t b*(4*(t:ℝ)*scale t b*(cutoff Δ t b/scale t b)^(1-1/(t:ℝ))) := hm'
    _ = _ := by rw [← degree_parameter_identity ht hb hD0]; ring

lemma small_graph_occupancy {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b) (hsmall : (Fintype.card V:ℝ) ≤ cutoff Δ t b) :
    correction Δ t b*fugacity Δ t b*Fintype.card V ≤ occupiedMean F (fugacity Δ t b) := by
  have hD0 := (D_large_basic ht hD).2.1
  have hlam := fugacity_pos hb hD0
  have hh := small_graph_degree_bound F ht hb hD hk hd hsmall
  have he := Real.exp_le_exp.mpr (neg_le_neg hh)
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ fugacity Δ t b*Fintype.card V by positivity)
  have heq : Real.exp (-(fugacity Δ t b*(avgDegree F+1))) =
      Real.exp (-(avgDegree F+1)*fugacity Δ t b) := by congr 1; ring
  rw [heq] at hm
  have h := hm.trans (occupancy_exp_lower F hlam)
  simpa only [correction, mul_comm, mul_left_comm, mul_assoc] using h

lemma fugacity_cutoff {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 0 < D Δ t b) :
    fugacity Δ t b*cutoff Δ t b = 4*Real.exp 1*D Δ t b := by
  have hp : D Δ t b^(2*t) = D Δ t b^(2*t-1)*D Δ t b := by
    rw [← pow_succ]
    congr 1
    omega
  unfold fugacity cutoff
  rw [hp]
  field_simp [(scale_pos t hb).ne', (pow_pos hD (2*t-1)).ne']
  <;> ring

lemma degree_ratio_identity {k s T : ℝ} (hk : 0 < k) (hs : 0 < s) (hT : 0 < T) :
    k/(4*T*s*(k/s)^(1-1/T)) = (k/s)^(1/T)/(4*T) := by
  apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  ring

lemma large_graph_occupancy {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hk : 1 ≤ Fintype.card V) (hd : Density F t b) (hlarge : cutoff Δ t b ≤ (Fintype.card V:ℝ)) :
    2*D Δ t b ≤ occupiedMean F (fugacity Δ t b) := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) < t := by linarith
  have hs := scale_pos t hb
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have hlam := fugacity_pos hb hD0
  have hK : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hKs : 1 ≤ (Fintype.card V:ℝ)/scale t b := (le_div_iff₀ hs).mpr
    (by simpa using (cutoff_ge_scale hb hD1).trans hlarge)
  have ha : 0 ≤ 1-1/(t:ℝ) := by
    have hh := (div_le_one ht0).mpr ht'
    linarith
  have hpow1 := Real.one_le_rpow hKs ha
  have hdeg := (LocalOccupancyIS.Glauber.lemma_5 F t ht b hb hk hd 0 (fun _ => 0) (by simp)).2
  change avgDegree F+1 ≤ 4*(t:ℝ)*scale t b*max 1 (((Fintype.card V:ℝ)/scale t b)^(1-1/(t:ℝ))) at hdeg
  rw [max_eq_right hpow1] at hdeg
  have hratio : (cutoff Δ t b/scale t b)^(1/(t:ℝ))/(4*t) ≤
      (Fintype.card V:ℝ)/(avgDegree F+1) := by
    have hR := Real.rpow_le_rpow
      (div_nonneg (le_trans hs.le (cutoff_ge_scale hb hD1)) hs.le)
      (div_le_div_of_nonneg_right hlarge hs.le) (show 0 ≤ 1/(t:ℝ) by positivity)
    have hR' := div_le_div_of_nonneg_right hR (show 0 ≤ 4*(t:ℝ) by positivity)
    have hd0 : 0 < avgDegree F+1 := by linarith [avgDegree_nonneg F]
    have hi := div_le_div_of_nonneg_left hK.le hd0 hdeg
    rw [degree_ratio_identity hK hs ht0] at hi
    exact hR'.trans hi
  have hcut : (cutoff Δ t b/scale t b)^(1/(t:ℝ)) =
      (4*Real.exp 1)^(1/(t:ℝ))*D Δ t b^2 := by
    rw [cutoff_div_scale hb, Real.mul_rpow (by positivity) (pow_nonneg hD0.le _), ← Real.rpow_natCast_mul hD0.le]
    have he : (2*t:ℕ)*(1/(t:ℝ)) = (2:ℝ) := by push_cast; field_simp
    rw [he, Real.rpow_two]
  rw [hcut] at hratio
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hcbase : 1 ≤ (4*Real.exp 1)^(1/(t:ℝ)) := Real.one_le_rpow (by linarith) (by positivity)
  have hratio2 : 2*Real.exp 1*D Δ t b ≤ (Fintype.card V:ℝ)/(avgDegree F+1) := by
    have hDmul := mul_le_mul_of_nonneg_right hD hD0.le
    have hpowmul := mul_le_mul_of_nonneg_right hcbase (sq_nonneg (D Δ t b))
    have hr := (div_le_iff₀ (show (0:ℝ) < 4*t by positivity)).mp hratio
    nlinarith
  have hLam : 2*Real.exp 1*D Δ t b ≤ fugacity Δ t b*Fintype.card V := by
    have hh := mul_le_mul_of_nonneg_left hlarge hlam.le
    rw [fugacity_cutoff ht hb hD0] at hh
    nlinarith [Real.exp_pos 1]
  have hmin := le_min hLam hratio2
  have hh := mul_le_mul_of_nonneg_left hmin (show 0 ≤ 1/Real.exp 1 by positivity)
  have heq : 1/Real.exp 1*(2*Real.exp 1*D Δ t b) = 2*D Δ t b := by field_simp
  rw [heq] at hh
  exact hh.trans (occupancy_min_lower F hlam)

lemma occupancy_tangent {lam c w Z E : ℝ} (hlam : 0 < lam) (hc : 0 < c)
    (hw : 0 ≤ w) (hZ : 0 < Z) (hE : c*Real.log Z ≤ E) :
    1 ≤ beta lam w*p lam/Z + gamma c w*E := by
  have hp : 0 < p lam := div_pos hlam (by positivity)
  have hw1 : 0 < 1+w := by linarith
  have hmain : 1 ≤ (Real.exp (w-Real.log Z)+Real.log Z)/(1+w) := by
    apply (le_div_iff₀ hw1).mpr
    have hh := Real.add_one_le_exp (w-Real.log Z)
    linarith
  have hm := mul_le_mul_of_nonneg_left hE (show 0 ≤ 1/(c*(1+w)) by positivity)
  have heq : beta lam w*p lam/Z = Real.exp (w-Real.log Z)/(1+w) := by
    unfold beta
    rw [Real.exp_sub, Real.exp_log hZ]
    field_simp
    <;> ring
  rw [heq]
  unfold gamma
  have hcancel : 1/(c*(1+w))*(c*Real.log Z) = Real.log Z/(1+w) := by field_simp
  rw [hcancel] at hm
  rw [add_div] at hmain
  linarith

end
end LocalOccupancyIS.Glauber

open scoped BigOperators
namespace LocalOccupancyIS.Glauber
noncomputable section

lemma parameter_local_occupancy {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Δ b : ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hb : 0 ≤ b) (hd : HereditaryDensity G t b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) {w : ℝ} (hw : 0 ≤ w) (hwD : w ≤ D Δ t b) :
    LocalOccupancy G (fugacity Δ t b) (beta (fugacity Δ t b) w) (gamma (correction Δ t b) w) := by
  classical
  let lam := fugacity Δ t b
  let c := correction Δ t b
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have hlam : 0 < lam := fugacity_pos hb hD0
  have hc : 0 < c := (correction_bounds ht hD).1
  have hc1 : c ≤ 1 := (correction_bounds ht hD).2.1
  have hp : 0 < p lam := p_pos hlam
  have hw1 : 0 < 1+w := by linarith
  refine ⟨div_pos (Real.exp_pos _) (mul_pos hp hw1), one_div_pos.mpr (mul_pos hc hw1), ?_⟩
  intro u A hA
  let F := G.induce (↑A : Set V)
  have hF : Density F t b := hd u A hA
  by_cases hzero : Fintype.card (↑(↑A : Set V)) = 0
  · rw [partition_empty F lam hzero, occupiedMean_empty F lam hzero]
    have hh := occupancy_tangent (E := 0) (Z := 1) hlam hc hw (by norm_num) (by simp)
    simpa using hh
  · have hk : 1 ≤ Fintype.card (↑(↑A : Set V)) := by omega
    by_cases hsmall : (Fintype.card (↑(↑A : Set V)) : ℝ) ≤ cutoff Δ t b
    · have hh := small_graph_occupancy F ht hb hD hk hF hsmall
      have hlog := mul_le_mul_of_nonneg_left (log_partition_upper F hlam) hc.le
      have hE : c*Real.log (partition F lam) ≤ occupiedMean F lam := by
        change c*lam*Fintype.card (↑(↑A : Set V)) ≤ occupiedMean F lam at hh
        nlinarith
      exact occupancy_tangent hlam hc hw (partition_pos F hlam) hE
    · have hh := large_graph_occupancy F ht hb hD hk hF (le_of_lt (lt_of_not_ge hsmall))
      have hden : c*(1+w) ≤ 2*D Δ t b := by
        have hm := mul_le_mul_of_nonneg_right hc1 hw1.le
        nlinarith
      have hgamma : 1 ≤ gamma c w*occupiedMean F lam := by
        have heq : gamma c w*occupiedMean F lam = occupiedMean F lam/(c*(1+w)) := by unfold gamma; ring
        rw [heq]
        apply (le_div_iff₀ (mul_pos hc hw1)).mpr
        simpa using hden.trans hh
      have hZpos := partition_pos F hlam
      have hfirst : 0 ≤ beta lam w*p lam/partition F lam := by
        unfold beta
        positivity
      linarith

lemma proposition6_finite {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {Δ b : ℝ} {t : ℕ}
    (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b) (hd : HereditaryDensity G t b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    (∀ w : ℝ, 0 ≤ w → w ≤ D Δ t b →
      LocalOccupancy G (fugacity Δ t b) (beta (fugacity Δ t b) w) (gamma (correction Δ t b) w)) ∧
    0 < optimizer Δ (fugacity Δ t b) (correction Δ t b) ∧
    optimizer Δ (fugacity Δ t b) (correction Δ t b) < D Δ t b ∧
    Gamma Δ (fugacity Δ t b) (correction Δ t b) =
      Δ/(correction Δ t b*optimizer Δ (fugacity Δ t b) (correction Δ t b)) := by
  have hz := optimizer_bounds hΔ ht hb hD
  refine ⟨fun w hw hwD => parameter_local_occupancy G ht hb hd hD hw hwD, hz.1, hz.2, ?_⟩
  exact gamma_optimizer_identity (by linarith) (fugacity_pos hb (D_large_basic ht hD).2.1)
    (correction_bounds ht hD).1

end
end LocalOccupancyIS.Glauber

namespace LocalOccupancyIS.Glauber
noncomputable section

lemma log_D_one_le {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) : 1 ≤ Real.log (D Δ t b) := by
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hh : Real.exp 1 ≤ D Δ t b := by nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 8*Real.exp 1) (sub_nonneg.mpr ht')]
  have hlog := Real.log_le_log he hh
  simpa only [Real.log_exp] using hlog

lemma optimizer_log_identity {Δ b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    let z := optimizer Δ (fugacity Δ t b) (correction Δ t b)
    Real.log z+z = D Δ t b-((2*t-1:ℕ):ℝ)*Real.log (D Δ t b)-Real.log (1+fugacity Δ t b)+
      4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b := by
  dsimp only
  let lam := fugacity Δ t b
  let c := correction Δ t b
  let z := optimizer Δ lam c
  have hΔ0 : 0 < Δ := by linarith
  have hD0 := (D_large_basic ht hD).2.1
  have hlam : 0 < lam := fugacity_pos hb hD0
  have hc : 0 < c := (correction_bounds ht hD).1
  have hz : 0 < z := (optimizer_bounds hΔ ht hb hD).1
  have hp : 0 < p lam := div_pos hlam (by positivity)
  have he := (lambert_facts (div_pos (mul_pos hp hΔ0) hc).le).2
  change z*Real.exp z = p lam*Δ/c at he
  have hlog := congrArg Real.log he
  rw [Real.log_mul hz.ne' (Real.exp_pos z).ne', Real.log_exp] at hlog
  have hpEq : p lam*Δ/c = (Real.exp (D Δ t b)/D Δ t b^(2*t-1))/(1+lam)/c := by
    rw [← fugacity_degree hΔ0 hb]
    change (lam/(1+lam))*Δ/c = (lam*Δ)/(1+lam)/c
    ring
  rw [hpEq] at hlog
  rw [Real.log_div (div_pos (div_pos (Real.exp_pos _) (pow_pos hD0 _)) (by positivity)).ne' hc.ne',
    Real.log_div (div_pos (Real.exp_pos _) (pow_pos hD0 _)).ne' (by positivity),
    Real.log_div (Real.exp_pos _).ne' (pow_pos hD0 _).ne', Real.log_exp, Real.log_pow] at hlog
  have hcLog : Real.log c = -(4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b) := by
    exact Real.log_exp _
  rw [hcLog] at hlog
  simpa only [sub_neg_eq_add] using hlog

lemma optimizer_lower {Δ b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    D Δ t b-3*(t:ℝ)*Real.log (D Δ t b) ≤
      optimizer Δ (fugacity Δ t b) (correction Δ t b) := by
  let lam := fugacity Δ t b
  let z := optimizer Δ lam (correction Δ t b)
  have hD0 := (D_large_basic ht hD).2.1
  have hD1 := (D_large_basic ht hD).2.2
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hlam : 0 < lam := fugacity_pos hb hD0
  have hz := optimizer_bounds hΔ ht hb hD
  have hlogz : Real.log z ≤ Real.log (D Δ t b) := Real.log_le_log hz.1 hz.2.le
  have hLam : lam ≤ 1/D Δ t b := fugacity_le_inv_D ht hb hD1
  have hlogLam : Real.log (1+lam) ≤ 1/D Δ t b := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+lam)
    linarith
  have ha := (correction_exponent_bounds ht hD).1
  have hlogD := log_D_one_le ht hD
  have hinv : 1/D Δ t b ≤ 1 := (div_le_one hD0).mpr hD1
  have htlog : 1 ≤ (t:ℝ)*Real.log (D Δ t b) := by nlinarith
  have he := optimizer_log_identity hΔ ht hb hD
  have hr : ((2*t-1:ℕ):ℝ) = 2*(t:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ 2*t)]; norm_num
  rw [hr] at he
  change Real.log z+z = _ at he
  change D Δ t b-3*(t:ℝ)*Real.log (D Δ t b) ≤ z
  nlinarith

lemma correction_exponent_relative {Δ b : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hD : 8*Real.exp 1*t ≤ D Δ t b) :
    0 ≤ 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ∧
      4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/D Δ t b ≤ 16*Real.exp 1*relativeError Δ t b := by
  have hD0 := (D_large_basic ht hD).2.1
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hlog := log_D_one_le ht hD
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hInv : 0 ≤ 1/(t:ℝ) := by positivity
  have hpow : (4*Real.exp 1)^(1-1/(t:ℝ)) ≤ 4*Real.exp 1 := by
    calc
      _ ≤ (4*Real.exp 1)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = _ := Real.rpow_one _
  refine ⟨(correction_exponent_bounds ht hD).1, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 4*(t:ℝ) by positivity)
  have htlog : (t:ℝ) ≤ t*Real.log (D Δ t b) := by nlinarith
  have hm' := mul_le_mul_of_nonneg_left htlog (show 0 ≤ 16*Real.exp 1 by positivity)
  have hnum : 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ)) ≤ 16*Real.exp 1*((t:ℝ)*Real.log (D Δ t b)) := by nlinarith
  have hh := div_le_div_of_nonneg_right hnum hD0.le
  change _ ≤ 16*Real.exp 1*((t:ℝ)*Real.log (D Δ t b)/D Δ t b)
  calc
    _ ≤ (16*Real.exp 1*((t:ℝ)*Real.log (D Δ t b)))/D Δ t b := hh
    _ = _ := by ring

lemma quantitative_gamma_error {Δ b : ℝ} {t : ℕ} (hΔ : 1 ≤ Δ) (ht : 1 ≤ t) (hb : 0 ≤ b)
    (hD : 8*Real.exp 1*t ≤ D Δ t b)
    (hsmall : relativeError Δ t b ≤ 1/(4*(16*Real.exp 1+3))) :
    |Gamma Δ (fugacity Δ t b) (correction Δ t b)*D Δ t b/Δ-1| ≤
      (4*(16*Real.exp 1+3))*relativeError Δ t b := by
  let d := D Δ t b
  let z := optimizer Δ (fugacity Δ t b) (correction Δ t b)
  let c := correction Δ t b
  let a := 4*(t:ℝ)*(4*Real.exp 1)^(1-1/(t:ℝ))/d
  let e := relativeError Δ t b
  let C := 16*Real.exp 1+3
  let E := C*e
  have hd : 0 < d := (D_large_basic ht hD).2.1
  have hz : 0 < z := (optimizer_bounds hΔ ht hb hD).1
  have hzd : z ≤ d := (optimizer_bounds hΔ ht hb hD).2.le
  have hc : 0 < c := (correction_bounds ht hD).1
  have hc1 : c ≤ 1 := (correction_bounds ht hD).2.1
  have he : 0 ≤ e := by
    dsimp [e, relativeError]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith [log_D_one_le ht hD])) hd.le
  have hC : 0 < C := by dsimp [C]; positivity
  have hE : 0 ≤ E := mul_nonneg hC.le he
  have hEsmall : E ≤ 1/4 := by
    have hh := (le_div_iff₀ (show (0:ℝ) < 4*(16*Real.exp 1+3) by positivity)).mp hsmall
    change e*(4*C) ≤ 1 at hh
    dsimp [E]
    linarith
  have ha0 : 0 ≤ a := (correction_exponent_relative ht hD).1
  have ha : a+3*e ≤ E := by
    have hh := (correction_exponent_relative ht hD).2
    change a ≤ 16*Real.exp 1*e at hh
    dsimp [E, C]
    linarith
  have hca : 1-a ≤ c := by
    have hh := Real.add_one_le_exp (-a)
    exact (by simpa [c, correction, a, d, add_comm] using hh)
  have hzlow : d*(1-3*e) ≤ z := by
    have hh := optimizer_lower hΔ ht hb hD
    change d-3*(t:ℝ)*Real.log d ≤ z at hh
    dsimp [d] at hh
    dsimp [e, relativeError, d]
    convert hh using 1 <;> field_simp [(D_large_basic ht hD).2.1.ne'] <;> ring
  have hap : 0 ≤ 1-a := by linarith
  have hep : 0 ≤ 1-3*e := by linarith
  have hprod := mul_le_mul hca hzlow (mul_nonneg hd.le hep) hc.le
  have hprodextra : 0 ≤ d*a*(3*e) := by positivity
  have hcz : d*(1-E) ≤ c*z := by
    have hreplace := mul_le_mul_of_nonneg_left ha hd.le
    nlinarith
  have hhalf : d/2 ≤ c*z := by nlinarith
  have hupper : c*z ≤ d := by
    have hh := mul_nonneg hz.le (sub_nonneg.mpr hc1)
    nlinarith
  have hczpos : 0 < c*z := mul_pos hc hz
  have hfrac : 1 ≤ d/(c*z) := (le_div_iff₀ hczpos).mpr (by simpa using hupper)
  have hΔ0 : 0 < Δ := by linarith
  have hGam := gamma_optimizer_identity hΔ0 (fugacity_pos hb hd) hc
  have hEq : Gamma Δ (fugacity Δ t b) (correction Δ t b)*D Δ t b/Δ = d/(c*z) := by
    rw [hGam]
    change (Δ/(c*z))*d/Δ = d/(c*z)
    field_simp
  rw [hEq, abs_of_nonneg (sub_nonneg.mpr hfrac)]
  have hsub : d/(c*z)-1 = (d-c*z)/(c*z) := by field_simp <;> ring
  rw [hsub]
  apply (div_le_iff₀ hczpos).mpr
  change d-c*z ≤ (4*C*e)*(c*z)
  rw [show 4*C*e = 4*E by dsimp [E]; ring]
  have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 4*E by positivity)
  nlinarith [mul_nonneg hd.le hE]

lemma admissible_eventually_regime (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ)
    (h : AdmissibleReal Δ t b) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ i in Filter.atTop, 8*Real.exp 1*t i ≤ D (Δ i) (t i) (b i) ∧
      relativeError (Δ i) (t i) (b i) ≤ c := by
  have hsmall := h.2.2.eventually (Iio_mem_nhds (lt_min hc (show 0 < 1/(8*Real.exp 1) by positivity)))
  have hlarge := h.2.1.eventually_ge_atTop (Real.exp 1)
  filter_upwards [hsmall, hlarge] with i hi hDi
  have ht : (1:ℝ) ≤ t i := by exact_mod_cast (h.1 i).2.1
  have hDpos : 0 < D (Δ i) (t i) (b i) := (Real.exp_pos 1).trans_le hDi
  have hlog : 1 ≤ Real.log (D (Δ i) (t i) (b i)) := by
    have hh := Real.log_le_log (Real.exp_pos 1) hDi
    simpa only [Real.log_exp] using hh
  have hi1 : relativeError (Δ i) (t i) (b i) < 1/(8*Real.exp 1) := hi.trans_le (min_le_right _ _)
  have hi2 : relativeError (Δ i) (t i) (b i) ≤ c := (hi.trans_le (min_le_left _ _)).le
  refine ⟨?_,hi2⟩
  unfold relativeError at hi1
  have hh := (div_lt_iff₀ hDpos).mp hi1
  have hh' := mul_lt_mul_of_pos_left hh (show 0 < 8*Real.exp 1 by positivity)
  have hcancel : (8*Real.exp 1)*(1/(8*Real.exp 1)*D (Δ i) (t i) (b i)) = D (Δ i) (t i) (b i) := by field_simp
  rw [hcancel] at hh'
  have htmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8*Real.exp 1*(t i:ℝ) by positivity)
  nlinarith

lemma proposition6_asymptotic :
    ∃ A : ℝ, 0 < A ∧ ∀ (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ), AdmissibleReal Δ t b →
      ∀ᶠ i in Filter.atTop,
        |Gamma (Δ i) (fugacity (Δ i) (t i) (b i)) (correction (Δ i) (t i) (b i)) *
          D (Δ i) (t i) (b i) / Δ i - 1| ≤ A * relativeError (Δ i) (t i) (b i) := by
  refine ⟨4*(16*Real.exp 1+3), by positivity, ?_⟩
  intro Δ t b h
  have hh := admissible_eventually_regime Δ t b h
    (c := 1/(4*(16*Real.exp 1+3))) (by positivity)
  filter_upwards [hh] with i hi
  exact quantitative_gamma_error (h.1 i).1 (h.1 i).2.1 (h.1 i).2.2 hi.1 hi.2

end
end LocalOccupancyIS.Glauber

open LocalOccupancyIS.Glauber

theorem solution :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (Δ : ℝ) (t : ℕ) (b : ℝ), 1 ≤ Δ → 1 ≤ t → 0 ≤ b → (∀ v, (G.degree v : ℝ) ≤ Δ) →
      HereditaryDensity G t b → 8 * Real.exp 1 * t ≤ D Δ t b →
      let lam := fugacity Δ t b
      let c := correction Δ t b
      let z := optimizer Δ lam c
      (∀ w : ℝ, 0 ≤ w → w ≤ D Δ t b → LocalOccupancy G lam (beta lam w) (gamma c w)) ∧
      0 < z ∧ z < D Δ t b ∧ Gamma Δ lam c = Δ / (c*z)) ∧
    (∃ A : ℝ, 0 < A ∧ ∀ (Δ : ℕ → ℝ) (t : ℕ → ℕ) (b : ℕ → ℝ), AdmissibleReal Δ t b →
      ∀ᶠ i in Filter.atTop,
        |Gamma (Δ i) (fugacity (Δ i) (t i) (b i)) (correction (Δ i) (t i) (b i)) *
          D (Δ i) (t i) (b i) / Δ i - 1| ≤ A * relativeError (Δ i) (t i) (b i)) := by
  refine ⟨?_, proposition6_asymptotic⟩
  intro V _ _ G _ Δ t b hΔ ht hb hdeg hd hD
  exact proposition6_finite G hΔ ht hb hd hD
