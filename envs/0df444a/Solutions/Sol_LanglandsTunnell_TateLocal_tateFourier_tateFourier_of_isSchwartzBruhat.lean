-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.tateFourier_tateFourier_of_isSchwartzBruhat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/05092327-0fe4-5637-b6e2-166f44768c31

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_Completion_Finite
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le
import Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_indicator_setOf_valued_sub_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_of_isSchwartzBruhat
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel Filter Topology
open scoped Pointwise

noncomputable section

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "IsSchwartzBruhat tateFourier tateFourier_indicator_setOf_valued_sub_le tateFourier_tateFourier_indicator_setOf_valued_sub_le"
namespace FourierSB
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ)  : v.adicCompletion K) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem ball_eq_smul_integers (k : ℤ) :
    {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) • (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have hu : Valued.v ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp k := by
    rw [valued_uniformizerUnit_zpow, neg_neg]
  have hu' : Valued.v ((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-k) :=
    valued_uniformizerUnit_zpow v k
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_smul_set, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro hx
    refine ⟨((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) * x, ?_, ?_⟩
    · rw [map_mul, hu']
      calc WithZero.exp (-k) * Valued.v x ≤ WithZero.exp (-k) * WithZero.exp k := mul_le_mul_right hx _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    · rw [Units.smul_def, smul_eq_mul, ← mul_assoc, ← Units.val_mul, zpow_neg, inv_mul_cancel, Units.val_one, one_mul]
  · rintro ⟨y, hy, rfl⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, hu]
    calc WithZero.exp k * Valued.v y ≤ WithZero.exp k * 1 := mul_le_mul_right hy _
      _ = WithZero.exp k := mul_one _

private theorem isCompact_ball (k : ℤ) : IsCompact {x  : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  rw [ball_eq_smul_integers v k]; exact (isCompactAdicCompletionIntegers K v).smul _

private theorem isOpen_ball (k : ℤ) : IsOpen {x  : v.adicCompletion K | Valued.v x ≤ WithZero.exp k} := by
  rw [ball_eq_smul_integers v k]; exact (isOpenAdicCompletionIntegers K v).smul _

private theorem ball_at_eq_image (a  : v.adicCompletion K) (k : ℤ) :
    {x  : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp k} = (fun t => a + t) '' {t  : v.adicCompletion K | Valued.v t ≤ WithZero.exp k} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h; exact ⟨x - a, h, by abel⟩
  · rintro ⟨t, ht, rfl⟩; simpa using ht

private theorem isCompact_ball_at (a  : v.adicCompletion K) (k : ℤ) : IsCompact {x  : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp k} := by
  rw [ball_at_eq_image v a k]; exact (isCompact_ball v k).image (continuous_const.add continuous_id)

private theorem isOpen_ball_at (a  : v.adicCompletion K) (k : ℤ) : IsOpen {x  : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp k} := by
  rw [ball_at_eq_image v a k]; exact isOpenMap_add_left a _ (isOpen_ball v k)

private theorem measurableSet_ball_at [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] (a  : v.adicCompletion K) (k : ℤ) :
    MeasurableSet {x  : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp k} :=
  (isCompact_ball_at v a k).isClosed.measurableSet

private theorem exists_ball_subset {V : Set (v.adicCompletion K)} (hV : V ∈ 𝓝 (0  : v.adicCompletion K)) :
    ∃ M : ℕ, {t  : v.adicCompletion K | Valued.v t ≤ WithZero.exp (-(M : ℤ))} ⊆ V := by
  set ϖ : v.adicCompletion K := ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) with hϖ
  have hϖv : Valued.v ϖ ≤ WithZero.exp (-1) := (valued_uniformizerUnit K v).le
  have htend : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := Valued.tendsto_zero_pow_of_le_exp_neg_one hϖv

  set W : Set (v.adicCompletion K) := interior V with hW
  have hW0 : (0  : v.adicCompletion K) ∈ W := mem_interior_iff_mem_nhds.mpr hV
  set nn : Set ((v.adicCompletion K) × (v.adicCompletion K)) := (fun p  : v.adicCompletion K × (v.adicCompletion K) => p.1 * p.2) ⁻¹' W with hnn
  have hnno : IsOpen nn := isOpen_interior.preimage continuous_mul
  have hsub : ({0} : Set (v.adicCompletion K)) ×ˢ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ⊆ nn := by
    rintro ⟨a, b⟩ ⟨ha, -⟩
    obtain rfl : a = 0 := ha
    show (0 : v.adicCompletion K) * b ∈ W
    rw [zero_mul]; exact hW0
  obtain ⟨U₁, U₂, hU₁, hU₂, h0, hO, hprod⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompactAdicCompletionIntegers K v) hnno hsub
  have h0' : (0  : v.adicCompletion K) ∈ U₁ := h0 rfl
  obtain ⟨M, hM⟩ := (htend.eventually_mem (hU₁.mem_nhds h0')).exists
  refine ⟨M, fun t ht => ?_⟩

  have hϖM : Valued.v (ϖ ^ M) = WithZero.exp (-(M : ℤ)) := by
    rw [hϖ, ← Units.val_pow_eq_pow_val, ← zpow_natCast, valued_uniformizerUnit_zpow]
  have hne : ϖ ^ M ≠ 0 := by rw [hϖ]; exact pow_ne_zero _ (Units.ne_zero _)
  have hint : (ϖ ^ M)⁻¹ * t ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hϖM]
    calc (WithZero.exp (-(M : ℤ)))⁻¹ * Valued.v t ≤ (WithZero.exp (-(M : ℤ)))⁻¹ * WithZero.exp (-(M : ℤ)) :=
          mul_le_mul_right ht _
      _ = 1 := inv_mul_cancel₀ WithZero.exp_ne_zero
  have hmem : (ϖ ^ M, (ϖ ^ M)⁻¹ * t) ∈ nn := hprod (Set.mk_mem_prod hM (hO hint))
  have : ϖ ^ M * ((ϖ ^ M)⁻¹ * t) ∈ W := hmem
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul] at this
  exact interior_subset this

private theorem exists_uniform {f  : v.adicCompletion K → ℂ} (hf : IsSchwartzBruhat f) :
    ∃ M : ℕ, ∀ x t  : v.adicCompletion K, Valued.v t ≤ WithZero.exp (-(M : ℤ)) → f (x + t) = f x := by
  set Kf : Set (v.adicCompletion K) := tsupport f with hKf
  have hK : IsCompact Kf := hf.2
  set F  : v.adicCompletion K × (v.adicCompletion K) → ℂ × ℂ := fun p => (f (p.1 + p.2), f p.1) with hF
  have hFlc : IsLocallyConstant F :=
    (hf.1.comp_continuous (continuous_fst.add continuous_snd)).prodMk (hf.1.comp_continuous continuous_fst)
  set Wset : Set ((v.adicCompletion K) × (v.adicCompletion K)) := F ⁻¹' {q : ℂ × ℂ | q.1 = q.2} with hWset
  have hWo : IsOpen Wset := hFlc _
  have hsub : Kf ×ˢ ({0} : Set (v.adicCompletion K)) ⊆ Wset := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    obtain rfl : t = 0 := ht
    simp [hWset, hF]
  obtain ⟨U₁, U₂, hU₁, hU₂, hKU, h0, hprod⟩ := generalized_tube_lemma hK isCompact_singleton hWo hsub
  have h0' : (0  : v.adicCompletion K) ∈ U₂ := h0 rfl
  obtain ⟨M, hM⟩ := exists_ball_subset v (hU₂.mem_nhds h0')
  refine ⟨M, fun x t ht => ?_⟩
  have key : ∀ y s  : v.adicCompletion K, y ∈ Kf → Valued.v s ≤ WithZero.exp (-(M : ℤ)) → f (y + s) = f y := by
    intro y s hy hs
    have : (y, s) ∈ Wset := hprod (Set.mk_mem_prod (hKU hy) (hM hs))
    simpa [hWset, hF] using this
  by_cases hx : x ∈ Kf
  · exact key x t hx ht
  by_cases hxt : x + t ∈ Kf
  · have hneg : Valued.v (-t) ≤ WithZero.exp (-(M : ℤ)) := by rwa [Valuation.map_neg]
    have := key (x + t) (-t) hxt hneg
    rw [add_neg_cancel_right] at this
    exact this.symm
  · have h1 : f x = 0 := by
      by_contra h; exact hx (subset_tsupport f (Function.mem_support.mpr h))
    have h2 : f (x + t) = 0 := by
      by_contra h; exact hxt (subset_tsupport f (Function.mem_support.mpr h))
    rw [h1, h2]

private def ballSubgroup (M : ℤ) : AddSubgroup (v.adicCompletion K) where
  carrier := {t | Valued.v t ≤ WithZero.exp (-M)}
  add_mem' {a b} ha hb := (Valuation.map_add_le_max' Valued.v a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa [Valuation.map_neg] using ha

private theorem mem_ballSubgroup (M : ℤ) (t  : v.adicCompletion K) : t ∈ ballSubgroup v M ↔ Valued.v t ≤ WithZero.exp (-M) := Iff.rfl

private theorem exists_decomposition {f  : v.adicCompletion K → ℂ} (hf : IsSchwartzBruhat f) :
    ∃ (M : ℤ) (S : Finset ((v.adicCompletion K) ⧸ ballSubgroup v M)),
      ∀ x  : v.adicCompletion K, f x = ∑ q ∈ S, f q.out * {x'  : v.adicCompletion K | Valued.v (x' - q.out) ≤ WithZero.exp (-M)}.indicator (fun _ => (1 : ℂ)) x := by
  classical
  obtain ⟨M, hM⟩ := exists_uniform v hf
  refine ⟨(M : ℤ), ?_⟩

  have hK : IsCompact (tsupport f) := hf.2
  obtain ⟨tfin, htfin⟩ := hK.elim_finite_subcover (fun a  : v.adicCompletion K => {x  : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-(M : ℤ))})
    (fun a => isOpen_ball_at v a _) (fun x _ => Set.mem_iUnion.mpr ⟨x, by simp⟩)
  refine ⟨tfin.image (QuotientAddGroup.mk  : v.adicCompletion K → (v.adicCompletion K) ⧸ ballSubgroup v M), fun x => ?_⟩

  have hind : ∀ q : (v.adicCompletion K) ⧸ ballSubgroup v M,
      {x'  : v.adicCompletion K | Valued.v (x' - q.out) ≤ WithZero.exp (-(M : ℤ))}.indicator (fun _ => (1 : ℂ)) x
        = if (QuotientAddGroup.mk x : (v.adicCompletion K) ⧸ ballSubgroup v M) = q then 1 else 0 := by
    intro q
    have hv : Valued.v (-x + q.out) = Valued.v (x - q.out) := by rw [← Valuation.map_neg, neg_add', neg_neg]
    have hiff : x ∈ {x'  : v.adicCompletion K | Valued.v (x' - q.out) ≤ WithZero.exp (-(M : ℤ))}
        ↔ (QuotientAddGroup.mk x : (v.adicCompletion K) ⧸ ballSubgroup v M) = q := by
      rw [Set.mem_setOf_eq, ← hv, ← mem_ballSubgroup, ← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
    by_cases h : (QuotientAddGroup.mk x : (v.adicCompletion K) ⧸ ballSubgroup v M) = q
    · rw [if_pos h, Set.indicator_of_mem (hiff.mpr h)]
    · rw [if_neg h, Set.indicator_of_notMem (fun hx => h (hiff.mp hx))]
  simp_rw [hind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

  have hval : f (QuotientAddGroup.mk x : (v.adicCompletion K) ⧸ ballSubgroup v M).out = f x := by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul (ballSubgroup v M) x
    rw [hh]
    exact hM x h ((mem_ballSubgroup v M _).mp h.2)
  split_ifs with hmem
  · exact hval.symm
  · by_contra hfx
    apply hmem
    have hxK : x ∈ tsupport f := subset_tsupport f (Function.mem_support.mpr hfx)
    obtain ⟨a, ha, hxa⟩ : ∃ a ∈ tfin, x ∈ {x'  : v.adicCompletion K | Valued.v (x' - a) ≤ WithZero.exp (-(M : ℤ))} := by
      simpa [Set.mem_iUnion] using htfin hxK
    refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
    rw [QuotientAddGroup.eq, mem_ballSubgroup, neg_add_eq_sub]
    exact hxa

private theorem continuous_of_level (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x  : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1) : Continuous ψ := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  have hev : (fun _  : v.adicCompletion K => ψ x₀) =ᶠ[𝓝 x₀] ψ := by
    have hU : {x  : v.adicCompletion K | Valued.v (x - x₀) ≤ WithZero.exp n} ∈ 𝓝 x₀ :=
      (isOpen_ball_at v x₀ n).mem_nhds (by simp)
    filter_upwards [hU] with x hx
    have : ψ x = ψ x₀ * ψ (x - x₀) := by rw [← AddChar.map_add_eq_mul, add_sub_cancel]
    rw [this, hψn _ hx, mul_one]
  exact continuousAt_const.congr hev

private theorem integrable_indicator_ball_mul [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (a  : v.adicCompletion K) (m : ℤ) {g  : v.adicCompletion K → ℂ} (hg : Continuous g) :
    Integrable (fun x => {x'  : v.adicCompletion K | Valued.v (x' - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x * g x) μ := by
  have hpt : (fun x => {x'  : v.adicCompletion K | Valued.v (x' - a) ≤ WithZero.exp (-m)}.indicator (fun _ => (1 : ℂ)) x * g x)
      = {x'  : v.adicCompletion K | Valued.v (x' - a) ≤ WithZero.exp (-m)}.indicator g := by
    funext x
    by_cases hx : x ∈ {x'  : v.adicCompletion K | Valued.v (x' - a) ≤ WithZero.exp (-m)}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  rw [hpt, integrable_indicator_iff (measurableSet_ball_at v a _)]
  exact hg.continuousOn.integrableOn_compact (isCompact_ball_at v a _)

end LanglandsTunnell.TateLocal.FourierSB

end

open MeasureTheory IsDedekindDomain NumberField

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_of_isSchwartzBruhat.LanglandsTunnell.TateLocal in

theorem solution (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (f : v.adicCompletion K → ℂ) (hf : IsSchwartzBruhat f) (x : v.adicCompletion K) :
    tateFourier ψ μ (tateFourier ψ μ f) x
      = (((Ideal.absNorm v.asIdeal : ℝ) ^ n
            * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ^ 2 : ℝ) : ℂ) * f (-x) := by
  classical
  have hψc : Continuous ψ := LanglandsTunnell.TateLocal.FourierSB.continuous_of_level v ψ n hψn
  obtain ⟨M, S, hdec⟩ := LanglandsTunnell.TateLocal.FourierSB.exists_decomposition v hf
  set C : ℂ := (((Ideal.absNorm v.asIdeal : ℝ) ^ n * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ^ 2 : ℝ) : ℂ) with hC
  set ind : ((v.adicCompletion K) ⧸ LanglandsTunnell.TateLocal.FourierSB.ballSubgroup v M) → (v.adicCompletion K) → ℂ :=
    fun q => {x'  : v.adicCompletion K | Valued.v (x' - q.out) ≤ WithZero.exp (-M)}.indicator (fun _ => (1 : ℂ)) with hind
  have hfdec : f = fun y => ∑ q ∈ S, f q.out * ind q y := funext hdec

  have hinner : ∀ y  : v.adicCompletion K, tateFourier ψ μ f y = ∑ q ∈ S, f q.out * tateFourier ψ μ (ind q) y := by
    intro y
    have hint : (fun x'  : v.adicCompletion K => f x' * ψ (x' * y))
        = fun x' => ∑ q ∈ S, f q.out * (ind q x' * ψ (x' * y)) := by
      funext x'; rw [hdec x', Finset.sum_mul]; simp only [hind, mul_assoc]
    show (∫ x', f x' * ψ (x' * y) ∂μ) = ∑ q ∈ S, f q.out * ∫ x', ind q x' * ψ (x' * y) ∂μ
    rw [hint, integral_finsetSum _ (fun q _ =>
      (LanglandsTunnell.TateLocal.FourierSB.integrable_indicator_ball_mul v μ q.out M (hψc.comp (continuous_id.mul continuous_const))).const_mul _)]
    simp_rw [integral_const_mul]

  have hball : ∀ q  : (v.adicCompletion K) ⧸ LanglandsTunnell.TateLocal.FourierSB.ballSubgroup v M, tateFourier ψ μ (ind q)
      = fun y => ψ (q.out * y) * ((μ.real {x  : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-M)} : ℝ) : ℂ)
          * {y'  : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + M)}.indicator (fun _ => (1 : ℂ)) y := by
    intro q; funext y
    exact tateFourier_indicator_setOf_valued_sub_le K v μ ψ n hψn hψn' q.out M y

  have houter : tateFourier ψ μ (tateFourier ψ μ f) x
      = ∑ q ∈ S, f q.out * tateFourier ψ μ (tateFourier ψ μ (ind q)) x := by
    have hint : (fun y  : v.adicCompletion K => tateFourier ψ μ f y * ψ (y * x))
        = fun y => ∑ q ∈ S, f q.out * (tateFourier ψ μ (ind q) y * ψ (y * x)) := by
      funext y; rw [hinner y, Finset.sum_mul]; simp_rw [mul_assoc]
    show (∫ y, tateFourier ψ μ f y * ψ (y * x) ∂μ) = ∑ q ∈ S, f q.out * ∫ y, tateFourier ψ μ (ind q) y * ψ (y * x) ∂μ
    rw [hint, integral_finsetSum _ (fun q _ => ?_)]
    · simp_rw [integral_const_mul]
    · refine Integrable.const_mul ?_ _
      simp only [hball q]
      have hcont : Continuous fun y  : v.adicCompletion K => ψ (q.out * y)
          * ((μ.real {x  : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-M)} : ℝ) : ℂ) * ψ (y * x) :=
        ((hψc.comp (continuous_const.mul continuous_id)).mul continuous_const).mul
          (hψc.comp (continuous_id.mul continuous_const))
      have h0ball : {y'  : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + M)}
          = {y'  : v.adicCompletion K | Valued.v (y' - 0) ≤ WithZero.exp (-(-(n + M)))} := by
        simp
      have := LanglandsTunnell.TateLocal.FourierSB.integrable_indicator_ball_mul v μ 0 (-(n + M)) hcont
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      rw [← h0ball]
      by_cases hy : y ∈ {y'  : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + M)}
      · simp only [Set.indicator_of_mem hy]; ring
      · simp only [Set.indicator_of_notMem hy]; ring
  rw [houter]

  have hF2 : ∀ q : (v.adicCompletion K) ⧸ LanglandsTunnell.TateLocal.FourierSB.ballSubgroup v M, tateFourier ψ μ (tateFourier ψ μ (ind q)) x
      = C * {x'  : v.adicCompletion K | Valued.v (x' + q.out) ≤ WithZero.exp (-M)}.indicator (fun _ => (1 : ℂ)) x := by
    intro q
    exact tateFourier_tateFourier_indicator_setOf_valued_sub_le K v μ ψ n hψn hψn' q.out M x
  simp_rw [hF2]
  have hneg : ∀ q  : (v.adicCompletion K) ⧸ LanglandsTunnell.TateLocal.FourierSB.ballSubgroup v M,
      {x'  : v.adicCompletion K | Valued.v (x' + q.out) ≤ WithZero.exp (-M)}.indicator (fun _ => (1 : ℂ)) x = ind q (-x) := by
    intro q
    have hv : Valued.v (-x - q.out) = Valued.v (x + q.out) := by rw [← Valuation.map_neg, neg_sub', neg_neg, sub_neg_eq_add]
    have hiff : x ∈ {x'  : v.adicCompletion K | Valued.v (x' + q.out) ≤ WithZero.exp (-M)}
        ↔ -x ∈ {x'  : v.adicCompletion K | Valued.v (x' - q.out) ≤ WithZero.exp (-M)} := by
      simp only [Set.mem_setOf_eq, hv]
    simp only [hind]
    by_cases hx : x ∈ {x'  : v.adicCompletion K | Valued.v (x' + q.out) ≤ WithZero.exp (-M)}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hiff.mp hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hiff.mpr h))]
  simp_rw [hneg]
  rw [hdec (-x), Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

end S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_of_isSchwartzBruhat
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_tateFourier_tateFourier_of_isSchwartzBruhat (solution)
