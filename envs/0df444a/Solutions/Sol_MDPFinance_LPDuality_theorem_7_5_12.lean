-- Prove2me | solution 1 for MDPFinance.LPDuality.theorem_7_5_12
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:46:00.012519+00:00
-- url     : https://prove2.me/submissions/b234f8f5-6ca0-4351-8992-5c57181bd9a5

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_Discretization

open MeasureTheory ProbabilityTheory Filter Topology

set_option autoImplicit false

open MDPFinance.LPDuality in
/-- Counterexample model: states `ℕ`, one action, zero reward, deterministic jump to `0`. -/
noncomputable def cexM_40dc : MarkovDecisionModel ℕ Unit where
  D := Set.univ
  hD_meas := MeasurableSet.univ
  hD_graph := ⟨fun _ => (), measurable_const, fun _ => trivial⟩
  Q := Kernel.const _ (Measure.dirac 0)
  isMarkovQ := inferInstance
  r := fun _ => 0
  hr_meas := measurable_const
  β := 1 / 2
  hβ0 := by norm_num
  hβ1 := by norm_num

open MDPFinance.LPDuality in
/-- Grid data whose grid operator is the constant map to the unbounded function `x ↦ x`. -/
noncomputable def cexG_40dc : GridApprox cexM_40dc (Set.univ : Set (ℕ → ℝ)) where
  bG := fun _ => 1
  hbG_meas := measurable_const
  hbG_ge1 := fun _ => le_refl _
  TG := fun _ x => (x : ℝ)
  hTG_maps := fun _ _ => Set.mem_univ _

open MDPFinance.LPDuality in
theorem erealIntegral_zero_40dc (μ : Measure ℕ) : erealIntegral μ (fun _ => (0 : EReal)) = 0 := by
  simp [erealIntegral]

open MDPFinance.LPDuality in
theorem Jnpi_zero_40dc (π : ℕ → ℕ → Unit) (n : ℕ) :
    Jnpi cexM_40dc cexM_40dc.r π n = fun _ => 0 := by
  induction n generalizing π with
  | zero => funext x; rfl
  | succ n ih =>
    funext x
    simp only [Jnpi]
    rw [ih]
    rw [erealIntegral_zero_40dc]
    simp [cexM_40dc]

open MDPFinance.LPDuality in
theorem Jinf_zero_40dc (x : ℕ) : Jinf cexM_40dc x = ((0 : ℝ) : EReal) := by
  have hpol : IsPolicyOf cexM_40dc (fun _ _ => ()) :=
    fun _ => ⟨measurable_const, fun _ => trivial⟩
  have hpi : ∀ π, Jinfpi cexM_40dc cexM_40dc.r π x = 0 := by
    intro π
    unfold Jinfpi
    simp only [Jnpi_zero_40dc]
    exact Filter.limsup_const _
  unfold Jinf
  simp only [hpi, EReal.coe_zero]
  apply le_antisymm
  · exact iSup₂_le (fun _ _ => le_refl _)
  · exact le_iSup₂_of_le (f := fun (π : ℕ → ℕ → Unit) (_ : π ∈ {π | IsPolicyOf cexM_40dc π}) =>
      (0 : EReal)) (fun _ _ => ()) hpol (le_refl _)

open MDPFinance.LPDuality in
theorem bound_40dc : IsBoundingFunction cexM_40dc (fun _ => 1) 0 1 where
  hb_meas := measurable_const
  hb_nonneg := fun _ => zero_le_one
  hcr := le_refl _
  hαb := zero_le_one
  hr := fun xa _ => by simp [cexM_40dc]
  hQ := fun xa _ => by simp [cexM_40dc]

theorem unbdd_40dc (f : ℕ → ℝ) (hf : ∀ x : ℕ, (x : ℝ) - 1 ≤ f x) :
    ¬ BddAbove (Set.range f) := by
  rintro ⟨B, hB⟩
  have h1 := hB ⟨⌈B⌉₊ + 2, rfl⟩
  have h2 := hf (⌈B⌉₊ + 2)
  have h3 : B ≤ (⌈B⌉₊ : ℝ) := Nat.le_ceil B
  push_cast at h2
  linarith

open MDPFinance.LPDuality in
theorem n1_40dc : normG (fun _ : ℕ => (1 : ℝ)) (fun _ => (0 : ℝ) - 1) = 1 := by
  simp [normG]

open MDPFinance.LPDuality in
theorem n2_40dc : normG (fun _ : ℕ => (1 : ℝ)) (fun x => (x : ℝ) - 1) = 0 := by
  unfold normG
  apply Real.iSup_of_not_bddAbove
  apply unbdd_40dc
  intro x
  rw [div_one]
  exact le_abs_self _

open MDPFinance.LPDuality in
theorem n3_40dc : normG (fun _ : ℕ => (1 : ℝ)) (fun x => (0 : ℝ) - x) = 0 := by
  unfold normG
  apply Real.iSup_of_not_bddAbove
  apply unbdd_40dc
  intro x
  dsimp only
  rw [div_one, zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg x)]
  linarith

open MDPFinance.LPDuality in
theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb : M.β * αb < 1)
    (IMc : Set (E → ℝ)) (G : GridApprox M IMc) (αG : ℝ) (hαG : M.β * αG < 1)
    (hTG_lip : ∀ v ∈ IMc, ∀ w ∈ IMc,
      normG G.bG (fun x => G.TG v x - G.TG w x) ≤ M.β * αG * normG G.bG (fun x => v x - w x))
    (Jinfty : E → ℝ) (hJ : ∀ x, Jinf M x = (Jinfty x : EReal)) (hJinftymem : Jinfty ∈ IMc)
    (g : E → ℝ) (hg : g ∈ IMc),
    ∀ n : ℕ, normG G.bG (fun x => Jinfty x - (G.TG)^[n] g x) ≤
        (1 / (1 - M.β * αG)) * ((M.β * αG) ^ n * normG G.bG (fun x => G.TG g x - g x) +
          normG G.bG (fun x => Jinfty x - G.TG Jinfty x))) := by
  intro h
  have hlip : ∀ v ∈ (Set.univ : Set (ℕ → ℝ)), ∀ w ∈ (Set.univ : Set (ℕ → ℝ)),
      normG cexG_40dc.bG (fun x => cexG_40dc.TG v x - cexG_40dc.TG w x) ≤
        cexM_40dc.β * 0 * normG cexG_40dc.bG (fun x => v x - w x) := by
    intro v _ w _
    simp [normG, cexG_40dc]
  have key : normG (fun _ : ℕ => (1 : ℝ)) (fun _ => (0 : ℝ) - 1) ≤
      (1 / (1 - cexM_40dc.β * 0)) * ((cexM_40dc.β * 0) ^ 0 *
        normG (fun _ : ℕ => (1 : ℝ)) (fun x => (x : ℝ) - 1) +
        normG (fun _ : ℕ => (1 : ℝ)) (fun x => (0 : ℝ) - x)) :=
    h cexM_40dc (fun _ => 1) 0 1 bound_40dc (by norm_num [cexM_40dc]) Set.univ cexG_40dc 0
      (by simp) hlip (fun _ => 0) Jinf_zero_40dc (Set.mem_univ _) (fun _ => 1)
      (Set.mem_univ _) 0
  rw [n1_40dc, n2_40dc, n3_40dc] at key
  norm_num at key
