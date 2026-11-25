-- Prove2me | solution 1 for GlobalTheory.CoordScale.measure_preimage_reindex_scale_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:20.444664+00:00
-- url     : https://prove2.me/submissions/cb5d1738-5ce2-4fbd-9f84-ed1933b7c64e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreimageReindexScaleComplexLe
import Theorems.Thm_GlobalTheory_CoordScale_sigmaFinite_smul
import Theorems.Thm_GlobalTheory_CoordScale_pi_smul_ne_top
import Theorems.Thm_GlobalTheory_CoordScale_measurePreserving_inv_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.CoordScale
open MeasureTheory
private theorem map_pi_reindex_eq_pi_of_map_eq {ι ι' β γ : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace β]
    [MeasurableSpace γ] (e : ι ≃ ι') (μ : Measure β) [SigmaFinite μ] (ν : ι → Measure γ)
    [∀ i, SigmaFinite (ν i)] (h : ι → β → γ) (hh : ∀ i, Measurable (h i))
    (hmap : ∀ i, Measure.map (h i) μ = ν i) :
    Measure.map (fun (x : ι' → β) (i : ι) => h i (x (e i))) (Measure.pi fun _ => μ) =
      Measure.pi ν := by
  have hm : Measurable (fun (x : ι' → β) (i : ι) => h i (x (e i))) :=
    measurable_pi_lambda _ (fun i => (hh i).comp (measurable_pi_apply (e i)))
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : ι' → β) (i : ι) => h i (x (e i))) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i' => h (e.symm i') ⁻¹' s (e.symm i')) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro hx i'
      have := hx (e.symm i')
      rwa [Equiv.apply_symm_apply] at this
    · intro hx i
      have := hx (e i)
      rwa [Equiv.symm_apply_apply] at this
  rw [hpre, Measure.pi_pi]
  refine (Finset.prod_congr rfl (fun i' _ => ?_)).trans (Equiv.prod_comp e.symm (fun i => ν i (s i)))
  rw [← hmap (e.symm i'), Measure.map_apply (hh _) (hs _)]
end GlobalTheory.CoordScale
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordScale
open MeasureTheory
namespace GlobalTheory.CoordScale
theorem _root_.solution : ∀ (ι ι' κ κ' : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ') (ρ c : ℝ) (d : κ → ℕ), 1 ≤ ρ → c ≤ 1 → ∀ A : Set (ι → κ → ℂ), MeasurableSet A → (MeasureTheory.Measure.pi fun _ : ι' => MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ((fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
  intro ι ι' κ κ' _ _ _ _ e f ρ c d hρ hc A hA
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  set C : ENNReal := ENNReal.ofReal c with hCdef
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have : SigmaFinite (C • (volume : Measure ℂ)) := sigmaFinite_smul _ hCt
  set w : κ → ENNReal := fun q => C * ENNReal.ofReal ((ρ ^ d q) ^ 2) with hwdef
  have hwt : ∀ q, w q ≠ ⊤ := fun q => ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  have : ∀ q, SigmaFinite (w q • (volume : Measure ℂ)) := fun q => sigmaFinite_smul _ (hwt q)
  have hin : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) =
      Measure.pi fun q : κ => w q • (volume : Measure ℂ) := by
    refine map_pi_reindex_eq_pi_of_map_eq f (C • (volume : Measure ℂ)) (fun q => w q • (volume : Measure ℂ))
      (fun q z => ((ρ : ℂ) ^ d q)⁻¹ * z) (fun q => measurable_id.const_mul _) (fun q => ?_)
    show Measure.map (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) (C • volume) = w q • volume
    have hfun : (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) = fun z => (((ρ ^ d q : ℝ) : ℂ))⁻¹ * z := by
      funext z
      rw [Complex.ofReal_pow]
    rw [Measure.map_smul, hfun, (measurePreserving_inv_mul (ρ ^ d q) (pow_pos hρ0 _)).map_eq,
      smul_smul]
  set K : ENNReal := ∏ q, w q with hKdef
  have hKt : K ≠ ⊤ := ENNReal.prod_ne_top (fun q _ => hwt q)
  have hin' : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) = K • (volume : Measure (κ → ℂ)) := by
    rw [hin, pi_smul_ne_top (fun _ => (volume : Measure ℂ)) w hwt]
    rfl
  have : SigmaFinite (K • (volume : Measure (κ → ℂ))) := sigmaFinite_smul _ hKt
  have hinm : Measurable (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) :=
    measurable_pi_lambda _ (fun q => (measurable_pi_apply (f q)).const_mul _)
  have hout : Measure.map (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q))
      (MeasureTheory.Measure.pi fun _ : ι' =>
        MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) =
      (K ^ Fintype.card ι) • (volume : Measure (ι → κ → ℂ)) := by
    have h1 := map_pi_reindex_eq_pi_of_map_eq e (Measure.pi fun _ : κ' => C • (volume : Measure ℂ))
      (fun _ : ι => K • (volume : Measure (κ → ℂ)))
      (fun _ (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) (fun _ => hinm) (fun _ => hin')
    refine h1.trans ?_
    rw [pi_smul_ne_top (fun _ : ι => (volume : Measure (κ → ℂ))) (fun _ => K) (fun _ => hKt),
      Finset.prod_const, Finset.card_univ]
    rfl
  have hgm : Measurable (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) :=
    measurable_pi_lambda _ (fun i => hinm.comp (measurable_pi_apply (e i)))
  rw [← Measure.map_apply hgm hA, hout, Measure.smul_apply, smul_eq_mul, mul_comm]
  have hC1 : C ≤ 1 := ENNReal.ofReal_le_one.mpr hc
  have hK1 : K ≤ ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) := by
    refine Finset.prod_le_prod' (fun q _ => ?_)
    calc w q = C * ENNReal.ofReal ((ρ ^ d q) ^ 2) := rfl
      _ ≤ 1 * ENNReal.ofReal ((ρ ^ d q) ^ 2) := by gcongr
      _ = ENNReal.ofReal ((ρ ^ d q) ^ 2) := one_mul _
  have hprod : ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) = ENNReal.ofReal (∏ q, (ρ ^ d q) ^ 2) :=
    (ENNReal.ofReal_prod_of_nonneg (fun q _ => by positivity)).symm
  have hreal : (∏ q, (ρ ^ d q) ^ 2) ^ Fintype.card ι = ρ ^ (2 * Fintype.card ι * ∑ q, d q) := by
    rw [Finset.prod_pow, Finset.prod_pow_eq_pow_sum, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hK2 : K ^ Fintype.card ι ≤ ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
    rw [← hreal, ENNReal.ofReal_pow (by positivity), ← hprod]
    exact pow_le_pow_left' hK1 _
  gcongr
end GlobalTheory.CoordScale
