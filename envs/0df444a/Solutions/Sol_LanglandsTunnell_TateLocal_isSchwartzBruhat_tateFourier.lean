-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e1db065c-ee53-5a5f-9d37-f2a7051d71b4

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "IsSchwartzBruhat IsSchwartzBruhat.zero tateFourier tateFourier_zero_fun"
namespace SchwartzBruhatFourier
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem exists_valued_eq (k : ℤ) :
    ∃ t : v.adicCompletion K, t ≠ 0 ∧ Valued.v t = WithZero.exp k := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hp : Valued.v ((algebraMap (𝓞 K) K π : K) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hπ]
  have hp0 : ((algebraMap (𝓞 K) K π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  refine ⟨((Units.mk0 _ hp0 ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K),
    Units.ne_zero _, ?_⟩
  rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, map_zpow₀, hp, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem isOpen_ball (k : ℤ) :
    IsOpen {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  obtain ⟨t, ht0, htv⟩ := exists_valued_eq v k
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
  have hset : {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (fun y => y * t⁻¹) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
    rw [mul_inv_le_iff₀ (zero_lt_iff.mpr hvt), one_mul, htv]
  rw [hset]
  exact (continuous_id.mul continuous_const).isOpen_preimage _ (Valued.isOpen_valuationSubring _)

private theorem ball_mem_nhds (x : v.adicCompletion K) (k : ℤ) :
    (fun z => z - x) ⁻¹' {w : v.adicCompletion K | Valued.v w ≤ WithZero.exp k} ∈ nhds x := by
  have hc : Continuous fun z : v.adicCompletion K => z - x := continuous_id.sub continuous_const
  refine (hc.isOpen_preimage _ (isOpen_ball v k)).mem_nhds ?_
  simp only [Set.mem_preimage, sub_self, Set.mem_setOf_eq, map_zero]
  exact zero_le'

private theorem exists_ball_subset {U : Set (v.adicCompletion K)} {x : v.adicCompletion K}
    (hU : U ∈ nhds x) : ∃ k : ℤ, ∀ z, Valued.v (z - x) ≤ WithZero.exp k → z ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hU
  obtain ⟨r, s, hr, hs, hrs⟩ := Valuation.exists_div_eq_of_unit Valued.v γ
  have hw0 : Valued.v (r / s) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr
      (div_ne_zero ((Valuation.ne_zero_iff _).mp hr.ne') ((Valuation.ne_zero_iff _).mp hs.ne'))
  refine ⟨WithZero.log (Valued.v (r / s)) - 1, fun z hz => hγ ?_⟩
  rw [Set.mem_setOf_eq, ← hrs, ← Valuation.map_div, Valuation.restrict_lt_iff]
  calc Valued.v (z - x) ≤ WithZero.exp (WithZero.log (Valued.v (r / s)) - 1) := hz
    _ < WithZero.exp (WithZero.log (Valued.v (r / s))) := WithZero.exp_lt_exp.mpr (by omega)
    _ = Valued.v (r / s) := WithZero.exp_log hw0

private theorem exists_translation_invariant {f : v.adicCompletion K → ℂ} (hf : IsSchwartzBruhat f) :
    ∃ d : ℤ, ∀ x t : v.adicCompletion K, Valued.v t ≤ WithZero.exp d → f (t + x) = f x := by
  have hloc : ∀ x : v.adicCompletion K,
      ∃ k : ℤ, ∀ z, Valued.v (z - x) ≤ WithZero.exp k → f z = f x := fun x =>
    exists_ball_subset v ((hf.1.isOpen_fiber (f x)).mem_nhds (show f x = f x from rfl))
  choose k hk using hloc
  obtain ⟨s, -, hs⟩ := hf.2.isCompact.elim_nhds_subcover
    (fun x => (fun z => z - x) ⁻¹' {w : v.adicCompletion K | Valued.v w ≤ WithZero.exp (k x)})
    (fun x _ => ball_mem_nhds v x (k x))
  obtain ⟨M, hM⟩ := (s.image fun x => -k x).exists_le
  have hd : ∀ x ∈ s, -M ≤ k x := by
    intro x hx
    have h1 : -k x ≤ M := hM _ (Finset.mem_image_of_mem (fun x => -k x) hx)
    omega

  have key : ∀ z ∈ tsupport f, ∀ w : v.adicCompletion K,
      Valued.v (w - z) ≤ WithZero.exp (-M) → f w = f z := by
    intro z hz w hw
    obtain ⟨x, hxs, hzx⟩ := Set.mem_iUnion₂.mp (hs hz)
    have hzx' : Valued.v (z - x) ≤ WithZero.exp (k x) := hzx
    have hwx : Valued.v (w - x) ≤ WithZero.exp (k x) := by
      rw [show w - x = w - z + (z - x) by ring]
      exact (Valuation.map_add_le_max' _ (w - z) (z - x)).trans
        (max_le (hw.trans (WithZero.exp_le_exp.mpr (hd x hxs))) hzx')
    rw [hk x w hwx, hk x z hzx']
  refine ⟨-M, fun x t ht => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact key x hx (t + x) (by rw [add_sub_cancel_right]; exact ht)
  · by_cases hxt : t + x ∈ tsupport f
    · refine (key (t + x) hxt x ?_).symm
      rw [show x - (t + x) = -t by ring, Valuation.map_neg]
      exact ht
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxt]

private theorem exists_support_subset_ball {f : v.adicCompletion K → ℂ} (hf : HasCompactSupport f) :
    ∃ R : ℤ, ∀ x, f x ≠ 0 → Valued.v x ≤ WithZero.exp R := by
  have hcover : tsupport f ⊆ ⋃ j : ℤ, {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp j} := by
    intro x _
    refine Set.mem_iUnion.mpr ?_
    by_cases h0 : Valued.v x = 0
    · exact ⟨0, by show Valued.v x ≤ WithZero.exp 0; rw [h0]; exact zero_le'⟩
    · exact ⟨WithZero.log (Valued.v x),
        show Valued.v x ≤ WithZero.exp (WithZero.log (Valued.v x)) from (WithZero.exp_log h0).ge⟩
  obtain ⟨s, hs⟩ := hf.isCompact.elim_finite_subcover
    (fun j : ℤ => {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp j}) (fun j => isOpen_ball v j)
    hcover
  obtain ⟨R, hR⟩ := s.exists_le
  refine ⟨R, fun x hx => ?_⟩
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hs (subset_tsupport f (Function.mem_support.mpr hx)))
  exact le_trans (show Valued.v x ≤ WithZero.exp j from hxj) (WithZero.exp_le_exp.mpr (hR j hj))

private theorem tateFourier_add_eq [MeasurableSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    {f : v.adicCompletion K → ℂ} {n R : ℤ}
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hR : ∀ x, f x ≠ 0 → Valued.v x ≤ WithZero.exp R) (y s : v.adicCompletion K)
    (hs : Valued.v s ≤ WithZero.exp (n - R)) : tateFourier ψ μ f (s + y) = tateFourier ψ μ f y := by
  have hpt : ∀ x, f x * ψ (x * (s + y)) = f x * ψ (x * y) := by
    intro x
    by_cases hfx : f x = 0
    · rw [hfx, zero_mul, zero_mul]
    · have hxs : ψ (x * s) = 1 := by
        apply hψn
        rw [map_mul]
        calc Valued.v x * Valued.v s ≤ WithZero.exp R * WithZero.exp (n - R) :=
              mul_le_mul' (hR x hfx) hs
          _ = WithZero.exp n := by rw [← WithZero.exp_add]; congr 1; ring
      rw [mul_add, AddChar.map_add_eq_mul, hxs, one_mul]
  unfold tateFourier
  simp_rw [hpt]

private theorem tateFourier_eq_zero [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) {f : v.adicCompletion K → ℂ} {n d : ℤ}
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (hd : ∀ x t : v.adicCompletion K, Valued.v t ≤ WithZero.exp d → f (t + x) = f x)
    (y : v.adicCompletion K) (hy : WithZero.exp (n + 1 - d) ≤ Valued.v y) :
    tateFourier ψ μ f y = 0 := by
  obtain ⟨x₁, hx₁, hne⟩ := hψn'
  have hvy0 : Valued.v y ≠ 0 := by
    intro h0
    rw [h0] at hy
    exact WithZero.exp_ne_zero (le_antisymm hy zero_le')
  have hy0 : y ≠ 0 := (Valuation.ne_zero_iff _).mp hvy0
  have htd : Valued.v (x₁ * y⁻¹) ≤ WithZero.exp d := by
    rw [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.mpr hvy0)]
    calc Valued.v x₁ ≤ WithZero.exp (n + 1) := hx₁
      _ = WithZero.exp d * WithZero.exp (n + 1 - d) := by rw [← WithZero.exp_add]; congr 1; ring
      _ ≤ WithZero.exp d * Valued.v y := mul_le_mul_right hy _
  have hty : x₁ * y⁻¹ * y = x₁ := by rw [inv_mul_cancel_right₀ hy0]
  have hpt : ∀ x, f (x₁ * y⁻¹ + x) * ψ ((x₁ * y⁻¹ + x) * y) = ψ x₁ * (f x * ψ (x * y)) := by
    intro x
    rw [hd x _ htd, add_mul, AddChar.map_add_eq_mul, hty]
    ring
  have htrans : tateFourier ψ μ f y = ψ x₁ * tateFourier ψ μ f y := by
    unfold tateFourier
    calc ∫ x, f x * ψ (x * y) ∂μ
        = ∫ x, f (x₁ * y⁻¹ + x) * ψ ((x₁ * y⁻¹ + x) * y) ∂μ :=
          (integral_add_left_eq_self (fun x => f x * ψ (x * y)) (x₁ * y⁻¹)).symm
      _ = ∫ x, ψ x₁ * (f x * ψ (x * y)) ∂μ := by simp_rw [hpt]
      _ = ψ x₁ * ∫ x, f x * ψ (x * y) ∂μ := integral_const_mul _ _
  have hprod : ((1 : ℂ) - ψ x₁) * tateFourier ψ μ f y = 0 := by
    rw [sub_mul, one_mul, ← htrans, sub_self]
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr (Ne.symm hne))

end LanglandsTunnell.TateLocal.SchwartzBruhatFourier

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier.LanglandsTunnell.TateLocal in
theorem solution (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (f : v.adicCompletion K → ℂ) (hf : IsSchwartzBruhat f) :
    IsSchwartzBruhat (tateFourier ψ μ f) := by
  by_cases hf0 : ∀ x, f x = 0
  · have hfz : f = 0 := funext fun x => hf0 x
    rw [hfz, tateFourier_zero_fun]
    exact IsSchwartzBruhat.zero
  obtain ⟨x₀, hx₀⟩ := not_forall.mp hf0
  obtain ⟨R, hR⟩ := LanglandsTunnell.TateLocal.SchwartzBruhatFourier.exists_support_subset_ball v hf.2
  obtain ⟨d, hd⟩ := LanglandsTunnell.TateLocal.SchwartzBruhatFourier.exists_translation_invariant v hf
  refine ⟨?_, ?_⟩
  ·
    refine (IsLocallyConstant.iff_exists_open _).mpr fun y => ?_
    have hc : Continuous fun z : v.adicCompletion K => z - y := continuous_id.sub continuous_const
    refine ⟨_, hc.isOpen_preimage _
        (LanglandsTunnell.TateLocal.SchwartzBruhatFourier.isOpen_ball v (n - R)),
      mem_of_mem_nhds (LanglandsTunnell.TateLocal.SchwartzBruhatFourier.ball_mem_nhds v y (n - R)),
      fun z hz => ?_⟩
    have h := LanglandsTunnell.TateLocal.SchwartzBruhatFourier.tateFourier_add_eq v μ ψ hψn hR y
      (z - y) hz
    rwa [sub_add_cancel] at h
  ·

    obtain ⟨c, hc0, hcv⟩ :=
      LanglandsTunnell.TateLocal.SchwartzBruhatFourier.exists_valued_eq v (d + d - (n + 1))
    have hg : Continuous fun x : v.adicCompletion K => c⁻¹ * (x - x₀) :=
      continuous_const.mul (continuous_id.sub continuous_const)
    refine HasCompactSupport.of_support_subset_isCompact (hf.2.isCompact.image hg) ?_
    intro y hy
    have hyS : Valued.v y ≤ WithZero.exp (n + 1 - d) := by
      by_contra hlt
      exact Function.mem_support.mp hy
        (LanglandsTunnell.TateLocal.SchwartzBruhatFourier.tateFourier_eq_zero v μ ψ hψn' hd y
          (not_le.mp hlt).le)
    have hcy : Valued.v (c * y) ≤ WithZero.exp d := by
      rw [map_mul, hcv]
      calc WithZero.exp (d + d - (n + 1)) * Valued.v y
          ≤ WithZero.exp (d + d - (n + 1)) * WithZero.exp (n + 1 - d) := mul_le_mul_right hyS _
        _ = WithZero.exp d := by rw [← WithZero.exp_add]; congr 1; ring
    refine ⟨c * y + x₀, subset_tsupport f ?_, ?_⟩
    · show f (c * y + x₀) ≠ 0
      rw [hd x₀ (c * y) hcy]
      exact hx₀
    · show c⁻¹ * (c * y + x₀ - x₀) = y
      rw [add_sub_cancel_right, inv_mul_cancel_left₀ hc0]

end S_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier (solution)
