-- Prove2me | solution 1 for MDPFinance.Contracting.theorem_7_3_5
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:34:37.407907+00:00
-- url     : https://prove2.me/submissions/adfafcb4-84d4-44b1-89a4-9fbc0c69224b

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory ProbabilityTheory MDPFinance.Contracting

namespace ContrCex

noncomputable def M0 : MarkovDecisionModel Unit Bool where
  D := Prod.snd ⁻¹' {true}
  hD_meas := (measurableSet_singleton true).preimage measurable_snd
  hD_graph := ⟨fun _ => true, measurable_const, fun _ => rfl⟩
  Q := Kernel.const _ (Measure.dirac ())
  isMarkovQ := inferInstance
  r := fun _ => -1
  hr_meas := measurable_const
  β := 1 / 2
  hβ0 := by norm_num
  hβ1 := by norm_num

theorem Dx_eq (x : Unit) : M0.Dx x = {true} := by
  ext a
  simp [MarkovDecisionModel.Dx, M0]

theorem half_mul_nonpos (y : EReal) (hy : y ≤ 0) : ((1 / 2 : ℝ) : EReal) * y ≤ 0 := by
  induction y using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos (by norm_num)]; exact bot_le
  | top => exact absurd hy (by simp)
  | coe t =>
    rw [← EReal.coe_mul]
    have : t ≤ 0 := by exact_mod_cast hy
    exact_mod_cast (by nlinarith : (1 / 2 : ℝ) * t ≤ 0)

theorem eI_nonpos (μ : Measure Unit) (v : Unit → EReal) (hv : ∀ x, v x ≤ 0) :
    erealIntegral μ v ≤ 0 := by
  unfold erealIntegral
  have h0 : (∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) = 0 := by
    have : (fun x => (v x ⊔ 0).toENNReal) = fun _ => 0 := by
      funext x
      rw [sup_eq_right.mpr (hv x)]
      simp
    rw [this, lintegral_zero]
  rw [h0]
  simp only [EReal.coe_ennreal_zero, zero_add, EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

theorem J_nonpos : ∀ (n : ℕ) (π : ℕ → Unit → Bool) (x : Unit), Jnpi M0 M0.r π n x ≤ 0 := by
  intro n
  induction n with
  | zero => intro π x; exact le_rfl
  | succ n ih =>
    intro π x
    have h := half_mul_nonpos (erealIntegral (M0.Q (x, π 0 x)) (Jnpi M0 M0.r (fun k => π (k + 1)) n))
      (eI_nonpos _ _ (fun y => ih (fun k => π (k + 1)) y))
    show ((-1 : ℝ) : EReal) + ((1 / 2 : ℝ) : EReal) *
      erealIntegral (M0.Q (x, π 0 x)) (Jnpi M0 M0.r (fun k => π (k + 1)) n) ≤ 0
    calc _ ≤ ((-1 : ℝ) : EReal) + 0 := add_le_add le_rfl h
      _ ≤ 0 := by norm_num

theorem J_le (n : ℕ) (π : ℕ → Unit → Bool) (x : Unit) : Jnpi M0 M0.r π (n + 1) x ≤ -1 := by
  have h := half_mul_nonpos (erealIntegral (M0.Q (x, π 0 x)) (Jnpi M0 M0.r (fun k => π (k + 1)) n))
    (eI_nonpos _ _ (fun y => J_nonpos n (fun k => π (k + 1)) y))
  show ((-1 : ℝ) : EReal) + ((1 / 2 : ℝ) : EReal) *
    erealIntegral (M0.Q (x, π 0 x)) (Jnpi M0 M0.r (fun k => π (k + 1)) n) ≤ -1
  calc _ ≤ ((-1 : ℝ) : EReal) + 0 := add_le_add le_rfl h
    _ = -1 := by simp

theorem Jinf_le : Jinf M0 () ≤ -1 := by
  unfold Jinf
  refine iSup₂_le fun π _ => ?_
  unfold Jinfpi
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  rw [Filter.eventually_atTop]
  exact ⟨1, fun n hn => by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact J_le k π ()⟩

theorem T'_zero : T' M0 (fun _ => 0) () = 0 := by
  unfold T'
  have h1 : (⨆ (_ : true ∈ M0.Dx ()), M0.r ((), true) + M0.β * ∫ x', (fun _ => (0 : ℝ)) x'
      ∂(M0.Q ((), true))) = -1 := by
    rw [ciSup_pos (by rw [Dx_eq]; rfl)]
    simp [M0]
  have h2 : (⨆ (_ : false ∈ M0.Dx ()), M0.r ((), false) + M0.β * ∫ x', (fun _ => (0 : ℝ)) x'
      ∂(M0.Q ((), false))) = 0 := by
    have : ¬ false ∈ M0.Dx () := by rw [Dx_eq]; simp
    simp [this]
  apply le_antisymm
  · refine ciSup_le fun a => ?_
    cases a
    · rw [h2]
    · rw [h1]; norm_num
  · refine le_trans (le_of_eq h2.symm) (le_ciSup (f := fun a => ⨆ (_ : a ∈ M0.Dx ()),
      M0.r ((), a) + M0.β * ∫ x', (fun _ => (0 : ℝ)) x' ∂(M0.Q ((), a))) ?_ false)
    exact (Set.finite_range _).bddAbove

end ContrCex

open ContrCex in
theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb : M.β * αb < 1)
    (IMs : Set (E → ℝ)) (hIMsub : IMs ⊆ IBb b)
    (hIMclosed : ∀ (vn : ℕ → E → ℝ) (v : E → ℝ), (∀ n, vn n ∈ IMs) → v ∈ IBb b →
      Filter.Tendsto (fun n => normb b fun x => vn n x - v x) Filter.atTop (nhds 0) → v ∈ IMs)
    (Δ : Set (E → A))
    (h0 : (0 : E → ℝ) ∈ IMs) (hTmaps : ∀ v ∈ IMs, (fun x => T' M v x) ∈ IMs)
    (hmax : ∀ v ∈ IMs, ∃ f ∈ Δ, IsMaximizerOf M (fun x => (v x : EReal)) f),
    (∃ v ∈ IMs, (∀ x, Jinf M x = (v x : EReal)) ∧ (∀ x, T' M v x = v x) ∧
        ∀ x, Jinf M x = Jlim M x) ∧
      (∀ v ∈ IMs, (∀ x, T' M v x = v x) → ∀ x, (v x : EReal) = Jinf M x) ∧
      (∀ v ∈ IMs, (∀ x, T' M v x ≤ v x) → ∀ x, Jinf M x ≤ (v x : EReal)) ∧
      (∀ g ∈ IMs, ∀ n : ℕ,
        normb b (fun x => (Jinf M x).toReal - (T' M)^[n] g x) ≤
          (M.β * αb) ^ n / (1 - M.β * αb) * normb b (fun x => T' M g x - g x)) ∧
      ((∃ f ∈ Δ, IsMaximizerOf M (Jinf M) f) ∧
        ∀ fstar : E → A, IsMaximizerOf M (Jinf M) fstar →
          ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x)) := by
  intro h
  have hb : IsBoundingFunction M0 (fun _ => 1) 1 1 :=
    { hb_meas := measurable_const
      hb_nonneg := fun _ => zero_le_one
      hcr := zero_le_one
      hαb := zero_le_one
      hr := fun _ _ => by simp [M0]
      hQ := fun _ _ => by simp [M0] }
  have hIM : (Set.univ : Set (Unit → ℝ)) ⊆ IBb (fun _ => 1) := by
    intro v _
    refine ⟨fun s _ => ?_, |v ()|, abs_nonneg _, fun x => by simp⟩
    exact MeasurableSpace.measurableSet_top
  have hmax : ∀ v ∈ (Set.univ : Set (Unit → ℝ)), ∃ f ∈ (Set.univ : Set (Unit → Bool)),
      IsMaximizerOf M0 (fun x => (v x : EReal)) f := by
    intro v _
    refine ⟨fun _ => true, Set.mem_univ _, ⟨measurable_const, fun _ => rfl⟩, ?_⟩
    funext x
    unfold T
    rw [Dx_eq, iSup_singleton]
  have H := (h M0 (fun _ => 1) 1 1 hb (by show (1 / 2 : ℝ) * 1 < 1; norm_num) Set.univ hIM
    (fun _ _ _ _ _ => Set.mem_univ _) Set.univ (Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    hmax).2.1 (fun _ => 0) (Set.mem_univ _) (fun x => by cases x; exact T'_zero) ()
  have := Jinf_le
  rw [← H] at this
  have h2 : ((0 : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) := by
    refine this.trans (le_of_eq ?_)
    norm_num
  have h3 : (0 : ℝ) ≤ -1 := EReal.coe_le_coe_iff.mp h2
  norm_num at h3

#print axioms solution
