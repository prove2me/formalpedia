-- Prove2me | solution 1 for MDPFinance.BayesianModels.theorem_5_4_10
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:54:18.343993+00:00
-- url     : https://prove2.me/submissions/b64a3e1c-5be7-45ca-aa6d-b61d7f5bf933

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior
import Definitions.Def_MDPFinance_BayesianModels_SuffStat
import Definitions.Def_MDPFinance_BayesianModels_InfoModel
import Definitions.Def_MDPFinance_BayesianModels_Operators
import Definitions.Def_MDPFinance_BayesianModels_StructureAssumption
import Definitions.Def_MDPFinance_BayesianModels_BoundingFunction
import Definitions.Def_MDPFinance_BayesianModels_Orders

open MeasureTheory ProbabilityTheory MDPFinance.BayesianModels

namespace BayesCex

noncomputable def M0 : BayesModel Unit ℝ Bool ℝ where
  D := Prod.snd ⁻¹' {true}
  hD_meas := (measurableSet_singleton true).preimage measurable_snd
  hD_sel := ⟨fun _ => true, measurable_const, fun _ => rfl⟩
  TX := fun _ _ _ => ()
  hTX_meas := measurable_const
  nu := Measure.dirac 0
  hnu_sigmaFinite := inferInstance
  qZ := fun _ _ _ _ => 1
  hqZ_meas := measurable_const
  hqZ_nonneg := fun _ _ _ _ => zero_le_one
  hqZ_prob := fun _ _ _ => by simp
  Q0 := Measure.dirac 0
  isProbQ0 := inferInstance
  r := fun _ => 0
  hr_meas := measurable_const
  g := fun _ => 0
  hg_meas := measurable_const
  β := 1
  hβ0 := one_pos
  hβ1 := le_rfl

theorem ratio (C : Set ℝ) (hC : MeasurableSet C) :
    Measure.dirac (0 : ℝ) C = (∫⁻ θ in C, ENNReal.ofReal 1 ∂(Measure.dirac (0 : ℝ))) /
      (∫⁻ θ, ENNReal.ofReal 1 ∂(Measure.dirac (0 : ℝ))) := by
  simp [Measure.restrict_apply_univ]

noncomputable def Pf0 : M0.Posterior where
  mu := fun _ _ _ _ => Measure.dirac 0
  hmu_prob := fun _ _ _ _ => inferInstance
  hmu_dep := fun _ _ _ _ _ _ _ _ _ _ => rfl
  hmu0 := fun _ _ _ => rfl
  hmu_meas := fun _ _ _ => measurable_const
  hmu_rec := fun _ _ _ _ _ _ C hC => ratio C hC

noncomputable def S0 : SuffStat M0 Pf0 Unit where
  t := fun _ _ _ _ => ()
  ht_meas := fun _ => measurable_const
  ht_dep := fun _ _ _ _ _ _ _ _ _ _ => rfl
  muHat := Kernel.const Unit (Measure.dirac 0)
  hmuHat_prob := fun _ => by simp only [Kernel.const_apply]; infer_instance
  ht_suff := fun _ _ _ _ _ _ => rfl

def Ph : Unit → Unit → Bool → ℝ → Unit := fun _ _ _ _ => ()

noncomputable def μR : Measure (Unit × Unit) :=
  ((Measure.dirac (0 : ℝ)).bind fun θ =>
    (Measure.dirac (0 : ℝ)).withDensity fun z => ENNReal.ofReal 1).map fun z => ((), ())

noncomputable def Im0 : InfoModel M0 Pf0 S0 Ph where
  Qhat := Kernel.const _ μR
  hQhat := fun _ _ _ => rfl

theorem InfoR_zero (x : Unit) (i : Unit) (a : Bool) : InfoR S0 x i a = 0 := by
  unfold InfoR erealIntegral
  simp [M0]

theorem InfoG_zero (e : Unit × Unit) : InfoG S0 e = 0 := by
  unfold InfoG erealIntegral
  simp [M0]

theorem dirac_wd : Measure.dirac (0 : ℝ) =
    (Measure.dirac (0 : ℝ)).withDensity (fun _ => ENNReal.ofReal 1) := by
  simp

end BayesCex

open BayesCex in
theorem solution : ¬ (∀ {EX A I : Type} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace I] [Preorder EX] [Preorder I] [Nonempty A]
    (M : BayesModel EX ℝ A ℝ) (Pf : M.Posterior) (S : SuffStat M Pf I)
    (Phihat : EX → I → A → ℝ → I) (hSeq : S.IsSequential Phihat) (Im : InfoModel M Pf S Phihat)
    (qZbar : ℝ → A → ℝ → ℝ) (hqZ : ∀ x θ a z, M.qZ x θ a z = qZbar θ a z) (phat : I → ℝ → ℝ)
    (hphat : ∀ i, S.muHat i = M.Q0.withDensity fun θ => ENNReal.ofReal (phat i θ))
    (hI_order : ∀ i i' : I, i ≤ i' ↔ LRMeasure M.Q0 (S.muHat i) (S.muHat i'))
    (hPhihat_bayes : ∀ x i a z,
      0 < (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) →
      (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) < ⊤ →
      ∀ C : Set ℝ, MeasurableSet C →
        S.muHat (Phihat x i a z) C =
          (∫⁻ θ in C, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)) /
            (∫⁻ θ, ENNReal.ofReal (qZbar θ a z) ∂(S.muHat i)))
    (b : EX × I → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction (InfoD M) (fun ea => Im.Qhat ea)
      (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) (InfoG S) b cr cg αb)
    (Δ : Set (EX × I → A))
    (hD_incr : ∀ x x' : EX, x ≤ x' → M.Dx x ⊆ M.Dx x')
    (hqZ_lr : ∀ θ θ' a, θ ≤ θ' → LikelihoodRatioOrder (qZbar θ a) (qZbar θ' a))
    (hTX_incr : ∀ a, MonotoneOn (fun p : EX × ℝ => M.TX p.1 a p.2) {p | a ∈ M.Dx p.1})
    (hr_incr : ∀ a, MonotoneOn (fun p : ℝ × EX => M.r (p.2, p.1, a)) {p | a ∈ M.Dx p.2})
    (hg_incr : Monotone fun p : ℝ × EX => M.g (p.2, p.1))
    (hmax : ∀ v : EX × I → EReal, Monotone v → v ∈ IBbPlus b →
      ∃ f ∈ Δ, IsMaximizerOf (InfoD M) (fun ea => Im.Qhat ea)
        (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) M.β v f),
    StructureAssumptionOf (InfoD M) (fun ea => Im.Qhat ea)
      (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) (InfoG S) M.β
      {v : EX × I → EReal | v ∈ IBbPlus b ∧ Monotone v} Δ) := by
  intro h
  have hb : IsUpperBoundingFunction (InfoD M0) (fun ea => Im0.Qhat ea)
      (fun ea => InfoR S0 ea.1.1 ea.1.2 ea.2) (InfoG S0) (fun _ => 0) 0 0 0 :=
    { hb_meas := measurable_const
      hb_nonneg := fun _ => le_rfl
      hcr := le_rfl
      hcg := le_rfl
      hαb := le_rfl
      hr := fun xa _ => by rw [InfoR_zero]; simp
      hg := fun x => by rw [InfoG_zero]; simp
      hQ := fun _ _ => by simp }
  have hLR : LRMeasure M0.Q0 (S0.muHat ()) (S0.muHat ()) :=
    ⟨fun _ => 1, fun _ => 1, measurable_const, measurable_const, fun _ => zero_le_one,
      fun _ => zero_le_one, dirac_wd, dirac_wd, fun _ _ _ => le_rfl⟩
  have hmax : ∀ v : Unit × Unit → EReal, Monotone v → v ∈ IBbPlus (fun _ : Unit × Unit => (0:ℝ)) →
      ∃ f ∈ (Set.univ : Set (Unit × Unit → Bool)), IsMaximizerOf (InfoD M0)
        (fun ea => Im0.Qhat ea) (fun ea => InfoR S0 ea.1.1 ea.1.2 ea.2) M0.β v f := by
    intro v _ _
    refine ⟨fun _ => true, Set.mem_univ _, ⟨measurable_const, fun _ => rfl⟩, ?_⟩
    funext x
    unfold MDPFinance.BayesianModels.Top
    have hs : {a | (x, a) ∈ InfoD M0} = {true} := by
      ext a; simp [InfoD, BayesModel.Dx, M0]
    rw [hs, iSup_singleton]
  have H := h M0 Pf0 S0 Ph ⟨measurable_const, fun _ _ _ _ => rfl⟩ Im0 (fun _ _ _ => 1)
    (fun _ _ _ _ => rfl) (fun _ _ => 1) (fun _ => dirac_wd) (fun _ _ => ⟨fun _ => hLR, fun _ => le_rfl⟩)
    (fun _ _ _ _ _ _ C hC => ratio C hC) (fun _ => 0) 0 0 0 hb Set.univ
    (fun _ _ _ => le_rfl) (fun _ _ _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ _ => le_rfl)
    (fun _ _ _ _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hmax
  have := (H.2.1 (Set.mem_univ (fun _ : Unit × Unit => false))).2 ((), ())
  simp [InfoD, BayesModel.Dx, M0] at this

#print axioms solution
