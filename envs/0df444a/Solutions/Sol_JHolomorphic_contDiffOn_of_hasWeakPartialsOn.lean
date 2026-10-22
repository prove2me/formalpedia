-- Prove2me | solution 1 for JHolomorphic.contDiffOn_of_hasWeakPartialsOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:44:08.164376+00:00
-- url     : https://prove2.me/submissions/3782812a-5ac6-416d-b4eb-c07563c2bf1b

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_contDiff_of_hasWeakPartialsOn_univ
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_univ_of_support_subset_closedBall
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_smul_left
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct



namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff

theorem contDiffOn_of_hasWeakPartialsOn_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p) (U : Set ℂ) (hU : IsOpen U)
    (u us ut uss ust uts utt : ℂ → E) (hu : ContinuousOn u U)
    (h1 : HasWeakPartialsOn U u us ut) (h2 : HasWeakPartialsOn U us uss ust)
    (h3 : HasWeakPartialsOn U ut uts utt)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp us (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ut (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp uss (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ust (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp uts (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp utt (ENNReal.ofReal p) (volume.restrict K)) :
    ContDiffOn ℝ 1 u U ∧
      ∀ᵐ z ∂(volume.restrict U), fderiv ℝ u z 1 = us z ∧ fderiv ℝ u z Complex.I = ut z := by
  set q := ENNReal.ofReal p with hq
  have hq1 : 1 ≤ q := by rw [hq]; exact ENNReal.one_le_ofReal.2 (by linarith)
  -- local integrability
  let Iloc : (ℂ → E) → Prop := fun g => ∀ K ⊆ U, IsCompact K → IntegrableOn g K
  let Lloc : (ℂ → E) → Prop := fun g => ∀ K ⊆ U, IsCompact K → MemLp g q (volume.restrict K)
  have hIL : ∀ g, Lloc g → Iloc g := by
    intro g hg K hK hKc
    haveI : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
    exact (hg K hK hKc).integrable hq1
  have Lus : Lloc us := fun K hK hKc => (hLp K hK hKc).1
  have Lut : Lloc ut := fun K hK hKc => (hLp K hK hKc).2.1
  have Luss : Lloc uss := fun K hK hKc => (hLp K hK hKc).2.2.1
  have Lust : Lloc ust := fun K hK hKc => (hLp K hK hKc).2.2.2.1
  have Luts : Lloc uts := fun K hK hKc => (hLp K hK hKc).2.2.2.2.1
  have Lutt : Lloc utt := fun K hK hKc => (hLp K hK hKc).2.2.2.2.2
  have Iu : Iloc u := fun K hK hKc => (hu.mono hK).integrableOn_compact hKc
  have Iadd : ∀ f g, Iloc f → Iloc g → Iloc (fun z => f z + g z) :=
    fun f g hf hg K hK hKc => (hf K hK hKc).add (hg K hK hKc)
  -- weak partials of a sum
  have hadd : ∀ f fs ft g gs gt : ℂ → E, HasWeakPartialsOn U f fs ft →
      HasWeakPartialsOn U g gs gt → Iloc f → Iloc fs → Iloc ft → Iloc g → Iloc gs → Iloc gt →
      HasWeakPartialsOn U (fun z => f z + g z) (fun z => fs z + gs z)
        (fun z => ft z + gt z) := by
    intro f fs ft g gs gt hf hg If Ifs Ift Ig Igs Igt φ hφ hφc hφU
    obtain ⟨a1, a2⟩ := hf φ hφ hφc hφU
    obtain ⟨b1, b2⟩ := hg φ hφ hφc hφU
    have I : ∀ k : ℂ → E, Iloc k → ∀ v : ℂ, Integrable (fun z => fderiv ℝ φ z v • k z) :=
      fun k hk v => integrable_smul_of_integrableOn_compact hk
        (fderiv_apply_isTestFunction hφ hφc hφU v).1.continuous.continuousOn
        (fderiv_apply_isTestFunction hφ hφc hφU v).2.1
        (fderiv_apply_isTestFunction hφ hφc hφU v).2.2
    have J : ∀ k : ℂ → E, Iloc k → Integrable (fun z => φ z • k z) :=
      fun k hk => integrable_smul_of_integrableOn_compact hk hφ.continuous.continuousOn hφc hφU
    constructor
    · simp only [smul_add]
      rw [integral_add (I f If 1) (I g Ig 1), integral_add (J fs Ifs) (J gs Igs), a1, b1, neg_add]
    · simp only [smul_add]
      rw [integral_add (I f If _) (I g Ig _), integral_add (J ft Ift) (J gt Igt), a2, b2,
        neg_add]
  -- the local statement
  have hloc : ∀ z₀ ∈ U, ∃ V, IsOpen V ∧ z₀ ∈ V ∧ ContDiffOn ℝ 1 u (U ∩ V) := by
    intro z₀ hz₀
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
    set R := ε / 4 with hR
    have hR0 : 0 < R := by positivity
    let χ : ContDiffBump z₀ := ⟨R, 2 * R, hR0, by linarith⟩
    set K := closedBall z₀ (2 * R) with hK
    have hKc : IsCompact K := isCompact_closedBall _ _
    have h3U : closedBall z₀ (3 * R) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
    have hKU : K ⊆ U := (closedBall_subset_closedBall (by linarith)).trans h3U
    -- cutoff functions supported in `K`
    let T : (ℂ → ℝ) → Prop := fun β => ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ K
    have Tχ : T χ := ⟨χ.contDiff, χ.hasCompactSupport, by rw [χ.tsupport_eq]⟩
    have Td : ∀ β, T β → ∀ v : ℂ, T (fun z => fderiv ℝ β z v) := fun β h v =>
      fderiv_apply_isTestFunction h.1 h.2.1 h.2.2 v
    have T0 : ∀ β, T β → ∀ z ∉ K, β z = 0 := fun β h z hz =>
      image_eq_zero_of_notMem_tsupport (fun h' => hz (h.2.2 h'))
    have T1 : ∀ β, T β → ContDiff ℝ 1 β := fun β h => h.1.of_le (WithTop.coe_le_coe.mpr le_top)
    have TI : ∀ β, T β → ∀ g, Iloc g → Iloc (fun z => β z • g z) := fun β h g hg K' hK' hK'c =>
      (hg K' hK' hK'c).continuousOn_smul h.1.continuous.continuousOn hK'c
    have TL : ∀ β, T β → ∀ g, Lloc g → MemLp (fun z => β z • g z) q volume := by
      intro β h g hg
      obtain ⟨M, hM⟩ := h.1.continuous.bounded_above_of_compact_support h.2.1
      have hgK := hg K hKU hKc
      have e : (fun z => β z • g z) = K.indicator (fun z => β z • g z) := by
        refine (Set.indicator_eq_self.2 fun z hz => ?_).symm
        by_contra hzK
        exact hz (by simp [T0 β h z hzK])
      rw [e, memLp_indicator_iff_restrict isClosed_closedBall.measurableSet]
      refine MemLp.of_le (hgK.const_smul M) (h.1.continuous.aestronglyMeasurable.smul hgK.1)
        (Eventually.of_forall fun z => ?_)
      rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs M]
      exact mul_le_mul_of_nonneg_right ((hM z).trans (le_abs_self M)) (norm_nonneg _)
    have Tuc : ∀ β, T β → Continuous (fun z => β z • u z) := by
      intro β h
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hz : z ∈ U
      · exact h.1.continuous.continuousAt.smul (hu.continuousAt (hU.mem_nhds hz))
      · have h0 : β =ᶠ[𝓝 z] 0 :=
          notMem_tsupport_iff_eventuallyEq.mp fun h' => hz (hKU (h.2.2 h'))
        have e : (fun _ : ℂ => (0 : E)) =ᶠ[𝓝 z] fun z => β z • u z := by
          filter_upwards [h0] with y hy
          simp [hy]
        exact continuousAt_const.congr e
    have TLu : ∀ β, T β → MemLp (fun z => β z • u z) q volume := fun β h =>
      (Tuc β h).memLp_of_hasCompactSupport h.2.1.smul_right
    -- the cutoff and its derivatives
    set χs : ℂ → ℝ := fun z => fderiv ℝ χ z 1 with hχs
    set χt : ℂ → ℝ := fun z => fderiv ℝ χ z Complex.I with hχt
    have Ts : T χs := Td _ Tχ 1
    have Tt : T χt := Td _ Tχ Complex.I
    have Tss : T (fun z => fderiv ℝ χs z 1) := Td _ Ts 1
    have Tst : T (fun z => fderiv ℝ χs z Complex.I) := Td _ Ts Complex.I
    have Tts : T (fun z => fderiv ℝ χt z 1) := Td _ Tt 1
    have Ttt : T (fun z => fderiv ℝ χt z Complex.I) := Td _ Tt Complex.I
    have Ius := hIL us Lus
    have Iut := hIL ut Lut
    have hint1 : ∀ K' ⊆ U, IsCompact K' →
        IntegrableOn u K' ∧ IntegrableOn us K' ∧ IntegrableOn ut K' := fun K' hK' hK'c =>
      ⟨Iu K' hK' hK'c, Ius K' hK' hK'c, Iut K' hK' hK'c⟩
    have hint2 : ∀ K' ⊆ U, IsCompact K' →
        IntegrableOn us K' ∧ IntegrableOn uss K' ∧ IntegrableOn ust K' := fun K' hK' hK'c =>
      ⟨Ius K' hK' hK'c, hIL uss Luss K' hK' hK'c, hIL ust Lust K' hK' hK'c⟩
    have hint3 : ∀ K' ⊆ U, IsCompact K' →
        IntegrableOn ut K' ∧ IntegrableOn uts K' ∧ IntegrableOn utt K' := fun K' hK' hK'c =>
      ⟨Iut K' hK' hK'c, hIL uts Luts K' hK' hK'c, hIL utt Lutt K' hK' hK'c⟩
    -- weak partials of the cut-off map and of its partials, on `U`
    have hv1 := HasWeakPartialsOn.smul_left hU (T1 _ Tχ) h1 hint1
    have hA := HasWeakPartialsOn.smul_left hU (T1 _ Ts) h1 hint1
    have hB := HasWeakPartialsOn.smul_left hU (T1 _ Tχ) h2 hint2
    have hA' := HasWeakPartialsOn.smul_left hU (T1 _ Tt) h1 hint1
    have hB' := HasWeakPartialsOn.smul_left hU (T1 _ Tχ) h3 hint3
    have hv2 := hadd _ _ _ _ _ _ hA hB (TI _ Ts u Iu)
      (Iadd _ _ (TI _ Tss u Iu) (TI _ Ts us Ius)) (Iadd _ _ (TI _ Tst u Iu) (TI _ Ts ut Iut))
      (TI _ Tχ us Ius) (Iadd _ _ (TI _ Ts us Ius) (TI _ Tχ uss (hIL uss Luss)))
      (Iadd _ _ (TI _ Tt us Ius) (TI _ Tχ ust (hIL ust Lust)))
    have hv3 := hadd _ _ _ _ _ _ hA' hB' (TI _ Tt u Iu)
      (Iadd _ _ (TI _ Tts u Iu) (TI _ Tt us Ius)) (Iadd _ _ (TI _ Ttt u Iu) (TI _ Tt ut Iut))
      (TI _ Tχ ut Iut) (Iadd _ _ (TI _ Ts ut Iut) (TI _ Tχ uts (hIL uts Luts)))
      (Iadd _ _ (TI _ Tt ut Iut) (TI _ Tχ utt (hIL utt Lutt)))
    -- all these maps vanish outside `K`
    have hsub : ∀ f : ℂ → E, (∀ z ∉ K, f z = 0) → Function.support f ⊆ K :=
      fun f hf z hz => by by_contra hzK; exact hz (hf z hzK)
    have Z : ∀ z ∉ K, χ z = 0 ∧ fderiv ℝ χ z 1 = 0 ∧ fderiv ℝ χ z Complex.I = 0 ∧
        fderiv ℝ χs z 1 = 0 ∧ fderiv ℝ χs z Complex.I = 0 ∧ fderiv ℝ χt z 1 = 0 ∧
        fderiv ℝ χt z Complex.I = 0 := fun z hz =>
      ⟨T0 _ Tχ z hz, T0 _ Ts z hz, T0 _ Tt z hz, T0 _ Tss z hz, T0 _ Tst z hz, T0 _ Tts z hz,
        T0 _ Ttt z hz⟩
    have hRR : 2 * R < 3 * R := by linarith
    have hR2 : 0 < 2 * R := by linarith
    have hu1 := HasWeakPartialsOn.univ_of_support_subset_closedBall hR2 hRR h3U hv1
      (hsub _ fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1])
      (hsub _ fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.1])
      (hsub _ fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.2.1])
    have hu2 := HasWeakPartialsOn.univ_of_support_subset_closedBall hR2 hRR h3U hv2
      (hsub _ fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.1])
      (hsub _ fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.1, (Z z hz).2.2.2.1])
      (hsub _ fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.1, (Z z hz).2.2.1,
        (Z z hz).2.2.2.2.1])
    have hu3 := HasWeakPartialsOn.univ_of_support_subset_closedBall hR2 hRR h3U hv3
      (hsub _ fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.2.1])
      (hsub _ fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.1, (Z z hz).2.2.1,
        (Z z hz).2.2.2.2.2.1])
      (hsub _ fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.2.1, (Z z hz).2.2.2.2.2.2])
    have hQ := contDiff_of_hasWeakPartialsOn_univ p hp (Tuc _ Tχ)
      (HasCompactSupport.intro hKc fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.1])
      (HasCompactSupport.intro hKc fun z hz => by simp [T0 _ Ts z hz, T0 _ Tt z hz, (Z z hz).1, (Z z hz).2.2.1])
      hu1 hu2 hu3
      ((TLu _ Ts).add (TL _ Tχ us Lus)) ((TLu _ Tt).add (TL _ Tχ ut Lut))
      (((TLu _ Tss).add (TL _ Ts us Lus)).add ((TL _ Ts us Lus).add (TL _ Tχ uss Luss)))
      (((TLu _ Tst).add (TL _ Ts ut Lut)).add ((TL _ Tt us Lus).add (TL _ Tχ ust Lust)))
      (((TLu _ Tts).add (TL _ Tt us Lus)).add ((TL _ Ts ut Lut).add (TL _ Tχ uts Luts)))
      (((TLu _ Ttt).add (TL _ Tt ut Lut)).add ((TL _ Tt ut Lut).add (TL _ Tχ utt Lutt)))
    refine ⟨ball z₀ R, isOpen_ball, mem_ball_self hR0, ?_⟩
    refine (hQ.contDiffOn.congr fun z hz => ?_).mono Set.inter_subset_right
    simp [χ.one_of_mem_closedBall (ball_subset_closedBall hz)]
  have hC1 : ContDiffOn ℝ 1 u U := contDiffOn_of_locally_contDiffOn hloc
  refine ⟨hC1, ?_⟩
  have hP := HasWeakPartialsOn.of_contDiffOn hU hC1
  have hdc : ∀ v : ℂ, ContinuousOn (fun z => fderiv ℝ u z v) U := fun v =>
    (hC1.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hae := HasWeakPartialsOn.ae_eq hU h1 hP fun K hK hKc =>
    ⟨hIL us Lus K hK hKc, hIL ut Lut K hK hKc, ((hdc 1).mono hK).integrableOn_compact hKc,
      ((hdc Complex.I).mono hK).integrableOn_compact hKc⟩
  filter_upwards [hae] with z hz
  exact ⟨hz.1.symm, hz.2.symm⟩

end JHolomorphic

open JHolomorphic

open MeasureTheory
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p) (U : Set ℂ) (hU : IsOpen U)
    (u us ut uss ust uts utt : ℂ → E) (hu : ContinuousOn u U)
    (h1 : HasWeakPartialsOn U u us ut) (h2 : HasWeakPartialsOn U us uss ust)
    (h3 : HasWeakPartialsOn U ut uts utt)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp us (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ut (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp uss (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp ust (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp uts (ENNReal.ofReal p) (volume.restrict K) ∧
      MemLp utt (ENNReal.ofReal p) (volume.restrict K)) :
    ContDiffOn ℝ 1 u U ∧
      ∀ᵐ z ∂(volume.restrict U), fderiv ℝ u z 1 = us z ∧ fderiv ℝ u z Complex.I = ut z :=
  contDiffOn_of_hasWeakPartialsOn_aux p hp U hU u us ut uss ust uts utt hu h1 h2 h3 hLp
