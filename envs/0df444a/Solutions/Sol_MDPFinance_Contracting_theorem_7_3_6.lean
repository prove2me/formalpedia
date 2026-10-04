-- Prove2me | solution 1 for MDPFinance.Contracting.theorem_7_3_6
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:35:16.161313+00:00
-- url     : https://prove2.me/submissions/825ca7e4-5a6b-462c-a642-f1b63e4f6720

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_MDPFinance_Contracting_LsSet

open MeasureTheory ProbabilityTheory MDPFinance.Contracting

namespace ContrCex736

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

theorem mcp_const {X : Type} [TopologicalSpace X] (a : X) :
    MapClusterPt a Filter.atTop (fun _ : ℕ => a) := by
  unfold MapClusterPt
  rw [Filter.map_const]
  exact ClusterPt.of_le_nhds (pure_le_nhds a)

end ContrCex736

open ContrCex736 in
theorem solution : ¬ (∀ {E A : Type} [MeasurableSpace E] [MeasurableSpace A] [TopologicalSpace E]
    [BorelSpace E] [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [StandardBorelSpace E] [TopologicalSpace A] [BorelSpace A]
    [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A] [StandardBorelSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ)
    (hb : IsBoundingFunction M b cr αb) (hbcont : Continuous b) (hαb : M.β * αb < 1)
    (hDcompact : ∀ x, IsCompact (M.Dx x)) (hDcont : ContinuousSetValued M.Dx)
    (hQcont : ∀ v ∈ IBb b, Continuous v →
      ContinuousOn (fun p : E × A => ∫ x', v x' ∂(M.Q p)) M.D)
    (hrcont : ContinuousOn M.r M.D),
    (∃ v : E → ℝ, Continuous v ∧ v ∈ IBb b ∧ (∀ x, Jinf M x = (v x : EReal)) ∧
        ∀ x, Jinf M x = Jlim M x) ∧
      (∀ v ∈ IBb b, Continuous v → (∀ x, T' M v x = v x) → ∀ x, (v x : EReal) = Jinf M x) ∧
      (∀ x, (LsSeq fun n => Dstar M (Jn M M.r n) x).Nonempty ∧
        LsSeq (fun n => Dstar M (Jn M M.r n) x) ⊆ Dstar M (Jinf M) x) ∧
      (∃ fstar : E → A, IsDecisionRuleOf M fstar ∧
        (∀ x, fstar x ∈ LsSeq fun n => Dstar M (Jn M M.r n) x) ∧
        ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x)) := by
  intro h
  have hb : IsBoundingFunction M0 (fun _ => 1) 1 1 :=
    { hb_meas := measurable_const
      hb_nonneg := fun _ => zero_le_one
      hcr := zero_le_one
      hαb := zero_le_one
      hr := fun _ _ => by simp [M0]
      hQ := fun _ _ => by simp [M0] }
  have hD : ContinuousSetValued M0.Dx := by
    refine ⟨fun x xs _ as has => ⟨true, by rw [Dx_eq]; rfl, ?_⟩, fun x xs _ a ha =>
      ⟨fun _ => a, fun n => by rw [Dx_eq] at ha ⊢; exact ha, mcp_const a⟩⟩
    have : as = fun _ => true := by
      funext n
      have := has n
      rw [Dx_eq] at this
      exact this
    rw [this]
    exact mcp_const true
  have hv0 : (fun _ : Unit => (0 : ℝ)) ∈ IBb (fun _ : Unit => (1 : ℝ)) :=
    ⟨measurable_const, 0, le_rfl, fun x => by simp⟩
  have H := (h M0 (fun _ => 1) 1 1 hb continuous_const
    (by show (1 / 2 : ℝ) * 1 < 1; norm_num)
    (fun x => by rw [Dx_eq]; exact isCompact_singleton) hD
    (fun v _ _ => by
      show ContinuousOn (fun p : Unit × Bool => ∫ x', v x' ∂(Measure.dirac ())) _
      exact continuousOn_const)
    (by show ContinuousOn (fun _ : Unit × Bool => (-1 : ℝ)) _; exact continuousOn_const)).2.1
    (fun _ => 0) hv0 continuous_const (fun x => by cases x; exact T'_zero) ()
  have := Jinf_le
  rw [← H] at this
  have h2 : ((0 : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) := by
    refine this.trans (le_of_eq ?_)
    norm_num
  have h3 : (0 : ℝ) ≤ -1 := EReal.coe_le_coe_iff.mp h2
  norm_num at h3

#print axioms solution
