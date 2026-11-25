-- Prove2me | solution 1 for GlobalTheory.ZetaPole.zeta_simple_pole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:00:58.279175+00:00
-- url     : https://prove2.me/submissions/0d8e29ce-ccd2-4e4c-9001-ca0c08a50d9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaTotallyRealAtMostSimplePole
import Theorems.Thm_GlobalTheory_ZetaPole_tendsto_pow_mul
import Theorems.Thm_GlobalTheory_ZetaPole_bdd_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Filter Topology
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.ZetaPole
namespace GlobalTheory.ZetaPole
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (C C' : ClassGroup (NumberField.RingOfIntegers F)) (Z Z' : ℂ → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C' Z' →
    (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) →
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s =
        (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) →
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ ∀ s : ℂ, s ≠ 1 → Z s = R s / (s - 1) := by
  intro F _ _ _ C C' Z Z' hZ hZ' hfe
  set f := Module.finrank ℚ F
  have hdiff : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ Z s := fun s hs =>
    hZ.1.differentiableAt (isOpen_compl_singleton.mem_nhds hs)

  obtain ⟨L, hL⟩ := tendsto_pow_mul F C C' Z Z' hZ' hfe
  set h : ℂ → ℂ := fun s => (s - 1) ^ f * Z s
  have hHd : DifferentiableOn ℂ (Function.update h 1 (limUnder (𝓝[≠] 1) h)) Set.univ := by
    refine differentiableOn_update_limUnder_of_isLittleO Filter.univ_mem ?_ ?_
    · intro s hs
      have hs1 : s ≠ 1 := hs.2
      exact (((differentiableAt_id.sub_const 1).pow f).mul (hdiff s hs1)).differentiableWithinAt
    · exact ((hL.sub_const (h 1)).norm.isBoundedUnder_le).isLittleO_sub_self_inv
  set H := Function.update h 1 (limUnder (𝓝[≠] 1) h)
  have hHdf : Differentiable ℂ H := fun s => hHd.differentiableAt Filter.univ_mem
  have hHa : AnalyticAt ℂ H 1 := hHdf.analyticAt 1
  have hHh : ∀ s, s ≠ 1 → H s = (s - 1) ^ f * Z s := fun s hs => Function.update_of_ne hs _ _

  set g : ℂ → ℂ := fun s => (s - 1) * Z s
  have hpunct : ∀ {P : ℂ → Prop}, (∀ᶠ z in 𝓝 (1:ℂ), P z) → ∀ᶠ z in 𝓝[≠] (1:ℂ), P z ∧ z ≠ 1 := fun hP =>
    (eventually_nhdsWithin_of_eventually_nhds hP).and self_mem_nhdsWithin
  have hg : ∃ M, Tendsto g (𝓝[≠] 1) (𝓝 M) := by
    by_cases hz : ∀ᶠ z in 𝓝 (1:ℂ), H z = 0
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [hpunct hz] with z ⟨hz0, hz1⟩
      have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
      rw [hHh z hz1] at hz0
      have : Z z = 0 := (mul_eq_zero.mp hz0).resolve_left (pow_ne_zero _ hne)
      simp [g, this]
    · obtain ⟨n, G, hGa, hG1, hev⟩ := hHa.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
      rcases le_or_gt f (n + 1) with hfn | hfn
      · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hfn
        refine ⟨(1 - 1 : ℂ) ^ m * G 1, ?_⟩
        have hc : ContinuousAt (fun s : ℂ => (s - 1) ^ m * G s) 1 :=
          ((continuous_id.sub continuous_const).pow m).continuousAt.mul hGa.continuousAt
        refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [hpunct hev] with z ⟨hz0, hz1⟩
        have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
        rw [hHh z hz1, smul_eq_mul] at hz0
        apply mul_left_cancel₀ (pow_ne_zero f hne)
        simp only [g]
        calc (z - 1) ^ f * ((z - 1) ^ m * G z) = (z - 1) ^ (n + 1) * G z := by rw [hm]; ring
          _ = (z - 1) * ((z - 1) ^ f * Z z) := by rw [hz0]; ring
          _ = (z - 1) ^ f * ((z - 1) * Z z) := by ring
      · exfalso
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hfn

        have hev2 : ∀ᶠ z in 𝓝[≠] (1:ℂ), G z = (z - 1) ^ (k + 1) * g z := by
          filter_upwards [hpunct hev] with z ⟨hz0, hz1⟩
          have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
          rw [hHh z hz1, smul_eq_mul] at hz0
          apply mul_left_cancel₀ (pow_ne_zero n hne)
          simp only [g]
          calc (z - 1) ^ n * G z = (z - 1) ^ f * Z z := hz0.symm
            _ = (z - 1) ^ n * ((z - 1) ^ (k + 1) * ((z - 1) * Z z)) := by rw [hk]; ring
        have hreal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝[≠] (1:ℂ)) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have := (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
            simpa using this
          · filter_upwards [self_mem_nhdsWithin] with x hx
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro h
            have : x = 1 := by exact_mod_cast h
            exact (ne_of_gt (show (1:ℝ) < x from hx)) this
        have hG : Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 (G 1)) :=
          (hGa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).comp hreal
        obtain ⟨B, hB⟩ := bdd_right F C Z hZ
        have h0 : Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have hlim : Tendsto (fun x : ℝ => |x - 1| ^ (k + 1) * B) (𝓝[>] 1) (𝓝 0) := by
            have : Tendsto (fun x : ℝ => |x - 1| ^ (k + 1) * B) (𝓝 1) (𝓝 (|1 - 1| ^ (k + 1) * B)) :=
              (((continuous_id.sub continuous_const).abs.pow (k + 1)).mul continuous_const).tendsto 1
            simpa using this.mono_left nhdsWithin_le_nhds
          refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
          filter_upwards [hB, hreal.eventually hev2] with x hx hx2
          rw [hx2, norm_mul, norm_pow, show ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
            Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (by simpa [g] using hx) (by positivity)
        exact hG1 (tendsto_nhds_unique hG h0)

  obtain ⟨M, hM⟩ := hg
  refine ⟨Function.update g 1 (limUnder (𝓝[≠] 1) g), ?_, ?_⟩
  · have hRd : DifferentiableOn ℂ (Function.update g 1 (limUnder (𝓝[≠] 1) g)) Set.univ := by
      refine differentiableOn_update_limUnder_of_isLittleO Filter.univ_mem ?_ ?_
      · intro s hs
        have hs1 : s ≠ 1 := hs.2
        exact ((differentiableAt_id.sub_const 1).mul (hdiff s hs1)).differentiableWithinAt
      · exact ((hM.sub_const (g 1)).norm.isBoundedUnder_le).isLittleO_sub_self_inv
    exact fun s => hRd.differentiableAt Filter.univ_mem
  · intro s hs
    rw [Function.update_of_ne hs]
    simp only [g]
    field_simp [sub_ne_zero.mpr hs]
end GlobalTheory.ZetaPole
