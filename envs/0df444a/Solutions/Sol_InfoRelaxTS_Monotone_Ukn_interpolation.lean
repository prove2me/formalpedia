-- Prove2me | solution 1 for InfoRelaxTS.Monotone.Ukn_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T14:14:09.238229+00:00
-- url     : https://prove2.me/submissions/b0bb3470-4b93-4959-b95c-081f790d8726

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting
set_option autoImplicit false

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set MeasurableSpace
open scoped ENNReal

namespace BanditLaw

variable {Θ : Type*} [MeasurableSpace Θ]

lemma measurable_iid (R : Kernel Θ ℝ) [IsMarkovKernel R] :
    Measurable (fun θ => Measure.infinitePi (fun _ : ℕ => R θ)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp))
  rintro _ ⟨s,t,ht,rfl⟩
  have hv (θ : Θ) : Measure.infinitePi (fun _ : ℕ => R θ) ((s : Set ℕ).pi t) =
      ∏ i ∈ s, R θ (t i) :=
    Measure.infinitePi_pi (fun _ : ℕ => R θ) (s := s) (t := t)
      (fun i _ => ht i (mem_univ i))
  simp_rw [hv]
  exact Finset.measurable_prod s (fun i _ => R.measurable_coe (ht i (mem_univ i)))

noncomputable def iidKernel (R : Kernel Θ ℝ) [IsMarkovKernel R] : Kernel Θ (ℕ → ℝ) where
  toFun θ := Measure.infinitePi (fun _ : ℕ => R θ)
  measurable' := measurable_iid R

instance iidKernel_markov (R : Kernel Θ ℝ) [IsMarkovKernel R] : IsMarkovKernel (iidKernel R) :=
  ⟨fun _ => by change IsProbabilityMeasure (Measure.infinitePi _); infer_instance⟩

lemma arm_law (R : Kernel Θ ℝ) [IsMarkovKernel R] (ν : Measure Θ) [IsProbabilityMeasure ν] :
    (ν.bind fun θ => (Measure.dirac θ).prod (Measure.infinitePi fun _ : ℕ => R θ)) =
      ν ⊗ₘ iidKernel R := by
  rw [Measure.compProd_eq_comp_prod]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall fun θ => by
    rw [Kernel.prod_apply,Kernel.id_apply]; rfl

open InfoRelaxTS.Monotone
variable {K : ℕ} {Y : Type*} [MeasurableSpace Y]

lemma outcome_law (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y) :
    I R P y = Measure.pi (fun a => (P a (y a)) ⊗ₘ iidKernel (R a)) := by
  unfold I
  congr 1
  funext a
  exact arm_law _ _

theorem outcome_probability (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y) :
    IsProbabilityMeasure (I R P y) := by
  rw [outcome_law]
  infer_instance

lemma arm_marginal (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y) (a : Fin K) :
    (I R P y).map (fun ω => ω a) = (P a (y a)) ⊗ₘ iidKernel (R a) := by
  rw [outcome_law]
  exact (measurePreserving_eval _ a).map_eq

lemma parameter_marginal (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y) (a : Fin K) :
    (I R P y).map (fun ω => (ω a).1) = P a (y a) := by
  calc
    _ = ((I R P y).map (fun ω => ω a)).map Prod.fst :=
      (Measure.map_map (μ := I R P y) measurable_fst (measurable_pi_apply a)).symm
    _ = _ := by rw [arm_marginal]; exact Measure.fst_compProd _ _

lemma iid_marginal (R : Kernel Θ ℝ) [IsMarkovKernel R] (n : ℕ) :
    (iidKernel R).map (fun r => r n) = R := by
  ext θ s hs
  rw [Kernel.map_apply _ (measurable_pi_apply n)]
  change (Measure.infinitePi (fun _ : ℕ => R θ)).map (fun r => r n) s = _
  rw [Measure.infinitePi_map_eval]

lemma reward_marginal (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y)
    (a : Fin K) (n : ℕ) :
    (I R P y).map (fun ω => (ω a).2 n) = pred R P a (y a) := by
  have hs : (I R P y).map (fun ω => (ω a).2) = iidKernel (R a) ∘ₘ P a (y a) := by
    calc
      _ = ((I R P y).map (fun ω => ω a)).map Prod.snd :=
        (Measure.map_map (μ := I R P y) measurable_snd (measurable_pi_apply a)).symm
      _ = _ := by rw [arm_marginal]; exact Measure.snd_compProd _ _
  calc
    _ = ((I R P y).map (fun ω => (ω a).2)).map (fun r => r n) :=
      (Measure.map_map (μ := I R P y) (measurable_pi_apply n)
        ((measurable_pi_apply a).snd)).symm
    _ = _ := by
      rw [hs,Measure.map_comp _ _ (measurable_pi_apply n),iid_marginal]
      rfl

theorem reward_integrable [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (y : Fin K → Y)
    (a : Fin K) (n : ℕ) : Integrable (fun ω => (ω a).2 n) (I R P y) := by
  have hi := hM.integrable a (y a)
  rw [← reward_marginal R P y a n] at hi
  have hm : Measurable (fun ω : Outcome K Θ => (ω a).2 n) := by fun_prop
  exact (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable hm.aemeasurable).mp hi

end BanditLaw
#print axioms BanditLaw.outcome_probability
#print axioms BanditLaw.reward_integrable

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BanditBayesStep
variable {Θ Y H : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
  [Nonempty Θ] [MeasurableSpace Y] [MeasurableSpace H]

lemma conjugate_joint
    (R : Kernel Θ ℝ) [IsMarkovKernel R]
    (P : Kernel Y Θ) [IsMarkovKernel P] (U : Y → ℝ → Y)
    (hU : Measurable (Function.uncurry U))
    (hconj : ∀ y, (fun r => P (U y r)) =ᵐ[R ∘ₘ P y] posterior R (P y))
    (y : Y) :
    ((P y) ⊗ₘ R).map Prod.swap =
      (R ∘ₘ P y) ⊗ₘ P.comap (U y) (hU.comp measurable_prodMk_left) := by
  let : IsMarkovKernel (P.comap (U y) (hU.comp measurable_prodMk_left)) :=
    Kernel.IsMarkovKernel.comap P _
  rw [← compProd_posterior_eq_map_swap]
  exact Measure.compProd_congr (hconj y).symm

/-- Bayes updating commutes with mixing over an arbitrary measurable history.
The next observation is sampled from the same latent parameter. -/
theorem history_update
    (ν : Measure H) [IsProbabilityMeasure ν]
    (R : Kernel Θ ℝ) [IsMarkovKernel R]
    (P : Kernel Y Θ) [IsMarkovKernel P] (U : Y → ℝ → Y)
    (hU : Measurable (Function.uncurry U))
    (hconj : ∀ y, (fun r => P (U y r)) =ᵐ[R ∘ₘ P y] posterior R (P y))
    (b : H → Y) (hb : Measurable b) :
    ((ν ⊗ₘ P.comap b hb) ⊗ₘ R.comap Prod.snd measurable_snd).map
        (fun z : (H × Θ) × ℝ => ((z.1.1,z.2),z.1.2)) =
      (ν ⊗ₘ (R ∘ₖ P).comap b hb) ⊗ₘ
        P.comap (fun z : H × ℝ => U (b z.1) z.2)
          (hU.comp ((hb.comp measurable_fst).prodMk measurable_snd)) := by
  let : IsMarkovKernel
      (P.comap (fun z : H × ℝ => U (b z.1) z.2)
        (hU.comp ((hb.comp measurable_fst).prodMk measurable_snd))) :=
    Kernel.IsMarkovKernel.comap P _
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop)]
  rw [Measure.lintegral_compProd (by fun_prop),
    Measure.lintegral_compProd (by fun_prop),
    Measure.lintegral_compProd (by fun_prop),
    Measure.lintegral_compProd (by fun_prop)]
  apply lintegral_congr
  intro h
  have he := congrArg
    (fun η : Measure (ℝ × Θ) => ∫⁻ z, f ((h,z.1),z.2) ∂η)
    (conjugate_joint R P U hU hconj (b h))
  let : IsMarkovKernel (P.comap (U (b h)) (hU.comp measurable_prodMk_left)) :=
    Kernel.IsMarkovKernel.comap P _
  rw [lintegral_map (by fun_prop) measurable_swap,
    Measure.lintegral_compProd (by fun_prop),
    Measure.lintegral_compProd (by fun_prop)] at he
  simpa only [Kernel.comap,Kernel.coe_mk,Kernel.comp_apply,Prod.swap_prod_mk] using he

/-- An induction step on actual observations: if the current history has posterior
`P (b h)` and the next reward is conditionally sampled from `R θ`, the enlarged
history has posterior `P (U (b h) r)`. Both input distribution identities are
explicit hypotheses. -/
theorem observed_history_update {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Kernel Θ ℝ) [IsMarkovKernel R]
    (P : Kernel Y Θ) [IsMarkovKernel P] (U : Y → ℝ → Y)
    (hU : Measurable (Function.uncurry U))
    (hconj : ∀ y, (fun r => P (U y r)) =ᵐ[R ∘ₘ P y] posterior R (P y))
    (b : H → Y) (hb : Measurable b)
    (X : Ω → H) (Z : Ω → Θ) (W : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hW : Measurable W)
    (hjoint : μ.map (fun ω => (X ω,Z ω)) = μ.map X ⊗ₘ P.comap b hb)
    (hnext : μ.map (fun ω => ((X ω,Z ω),W ω)) =
      μ.map (fun ω => (X ω,Z ω)) ⊗ₘ R.comap Prod.snd measurable_snd) :
    condDistrib Z (fun ω => (X ω,W ω)) μ =ᵐ[μ.map (fun ω => (X ω,W ω))]
      (fun z => P (U (b z.1) z.2)) := by
  let : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  let κ := P.comap (fun z : H × ℝ => U (b z.1) z.2)
    (hU.comp ((hb.comp measurable_fst).prodMk measurable_snd))
  let : IsMarkovKernel κ := Kernel.IsMarkovKernel.comap P _
  have hfactor : μ.map (fun ω => ((X ω,W ω),Z ω)) =
      (μ.map X ⊗ₘ (R ∘ₖ P).comap b hb) ⊗ₘ κ := by
    calc
      _ = (μ.map (fun ω => ((X ω,Z ω),W ω))).map
          (fun z : (H × Θ) × ℝ => ((z.1.1,z.2),z.1.2)) :=
        (Measure.map_map (by fun_prop) ((hX.prodMk hZ).prodMk hW)).symm
      _ = _ := by rw [hnext,hjoint]; exact history_update (μ.map X) R P U hU hconj b hb
  have hmarg : μ.map (fun ω => (X ω,W ω)) =
      μ.map X ⊗ₘ (R ∘ₖ P).comap b hb := by
    calc
      _ = (μ.map (fun ω => ((X ω,W ω),Z ω))).map Prod.fst :=
        (Measure.map_map measurable_fst ((hX.prodMk hW).prodMk hZ)).symm
      _ = _ := by rw [hfactor]; exact Measure.fst_compProd _ _
  have he : μ.map (fun ω => ((X ω,W ω),Z ω)) =
      μ.map (fun ω => (X ω,W ω)) ⊗ₘ κ := by rw [hmarg]; exact hfactor
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (hX.prodMk hW) hZ he

lemma iid_prefix (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun r (i : Fin n) => r i) =
      Measure.pi (fun _ : Fin n => ν) := by
  have hi : iIndepFun (fun i : ℕ => fun r : ℕ → ℝ => r i)
      (Measure.infinitePi (fun _ : ℕ => ν)) :=
    iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)
  have hf := iIndepFun.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective hi
  have hm (i : Fin n) : AEMeasurable (fun r : ℕ → ℝ => r i)
      (Measure.infinitePi (fun _ : ℕ => ν)) := (measurable_pi_apply (i : ℕ)).aemeasurable
  rw [iIndepFun.map_fun_eq_pi_map hm hf]
  simp only [Measure.infinitePi_map_eval]

lemma iid_prefix_extension (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map
        (fun r => ((fun i : Fin n => r i),r n)) =
      (Measure.pi (fun _ : Fin n => ν)).prod ν := by
  have hi : iIndepFun (fun i : ℕ => fun r : ℕ → ℝ => r i)
      (Measure.infinitePi (fun _ : ℕ => ν)) :=
    iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)
  have hd : Disjoint (Finset.range n) {n} := by simp
  have hp := hi.indepFun_finset (Finset.range n) {n} hd (fun _ => by fun_prop)
  have hm₁ : Measurable
      (fun x : (↑(Finset.range n) → ℝ) => fun i : Fin n => x ⟨i,by simp⟩) := by fun_prop
  have hm₂ : Measurable (fun x : (↑({n} : Finset ℕ) → ℝ) => x ⟨n,by simp⟩) := by
    fun_prop
  have hh := hp.comp hm₁ hm₂
  have he := hh.map_prod_eq_prod_map_map (by
    change AEMeasurable (fun r : ℕ → ℝ => fun i : Fin n => r i) _
    exact (show Measurable (fun r : ℕ → ℝ => fun i : Fin n => r i) from
      measurable_pi_lambda _ (fun i => measurable_pi_apply (i : ℕ))).aemeasurable) (by
    change AEMeasurable (fun r : ℕ → ℝ => r n) _
    exact (measurable_pi_apply n).aemeasurable)
  simpa only [Function.comp_def,iid_prefix,Measure.infinitePi_map_eval] using he

/-- The actual one-arm outcome law has the required conditional sampling
identity for every finite reward prefix. -/
theorem arm_history_next
    (ν : Measure Θ) [IsProbabilityMeasure ν]
    (R : Kernel Θ ℝ) [IsMarkovKernel R] (n : ℕ) :
    (ν ⊗ₘ BanditLaw.iidKernel R).map
        (fun z => (((fun i : Fin n => z.2 i),z.1),z.2 n)) =
      ((ν ⊗ₘ BanditLaw.iidKernel R).map
        (fun z => ((fun i : Fin n => z.2 i),z.1))) ⊗ₘ
          R.comap Prod.snd measurable_snd := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun z : (Θ × (ℕ → ℝ)) × ℝ =>
      f (((fun i : Fin n => z.1.2 i),z.1.1),z.2)) := by fun_prop
  have hmi := hm.lintegral_kernel_prod_right'
    (κ := R.comap Prod.fst measurable_fst)
  rw [lintegral_map hf (by fun_prop),Measure.lintegral_compProd (by fun_prop),
    Measure.lintegral_compProd hf,
    lintegral_map (by fun_prop) (by fun_prop),
    Measure.lintegral_compProd (by
      simpa only [Kernel.comap,Kernel.coe_mk] using hmi)]
  apply lintegral_congr
  intro θ
  change (∫⁻ (r : ℕ → ℝ), f (((fun i : Fin n => r i),θ),r n)
      ∂Measure.infinitePi (fun _ : ℕ => R θ)) =
    ∫⁻ (r : ℕ → ℝ), (∫⁻ (t : ℝ), f (((fun i : Fin n => r i),θ),t) ∂(R θ))
      ∂Measure.infinitePi (fun _ : ℕ => R θ)
  calc
    _ = ∫⁻ z : (Fin n → ℝ) × ℝ, f ((z.1,θ),z.2)
        ∂((Measure.infinitePi (fun _ : ℕ => R θ)).map
          (fun r => ((fun i : Fin n => r i),r n))) :=
      (lintegral_map (by fun_prop) (by fun_prop)).symm
    _ = ∫⁻ z : (Fin n → ℝ) × ℝ, f ((z.1,θ),z.2)
        ∂((Measure.pi (fun _ : Fin n => R θ)).prod (R θ)) := by
      rw [iid_prefix_extension]
    _ = ∫⁻ (h : Fin n → ℝ), (∫⁻ (t : ℝ), f ((h,θ),t) ∂(R θ))
        ∂Measure.pi (fun _ : Fin n => R θ) := lintegral_prod _ (by fun_prop)
    _ = _ := by
      rw [← iid_prefix (R θ) n]
      exact lintegral_map (by fun_prop) (by fun_prop)

theorem arm_posterior_step
    (R : Kernel Θ ℝ) [IsMarkovKernel R]
    (P : Kernel Y Θ) [IsMarkovKernel P] (U : Y → ℝ → Y)
    (hU : Measurable (Function.uncurry U))
    (hconj : ∀ y, (fun r => P (U y r)) =ᵐ[R ∘ₘ P y] posterior R (P y))
    (y : Y) (n : ℕ) (b : (Fin n → ℝ) → Y) (hb : Measurable b)
    (hjoint : ((P y) ⊗ₘ BanditLaw.iidKernel R).map
        (fun z => ((fun i : Fin n => z.2 i),z.1)) =
      (((P y) ⊗ₘ BanditLaw.iidKernel R).map
        (fun z => (fun i : Fin n => z.2 i))) ⊗ₘ P.comap b hb) :
    condDistrib (Prod.fst : Θ × (ℕ → ℝ) → Θ)
        (fun z => ((fun i : Fin n => z.2 i),z.2 n))
        ((P y) ⊗ₘ BanditLaw.iidKernel R) =ᵐ[
          ((P y) ⊗ₘ BanditLaw.iidKernel R).map
            (fun z => ((fun i : Fin n => z.2 i),z.2 n))]
      (fun z => P (U (b z.1) z.2)) := by
  exact observed_history_update ((P y) ⊗ₘ BanditLaw.iidKernel R) R P U hU hconj b hb
    (fun z => (fun i : Fin n => z.2 i)) Prod.fst (fun z => z.2 n)
    (by fun_prop) measurable_fst (by fun_prop) hjoint (arm_history_next (P y) R n)

end BanditBayesStep
#print axioms BanditBayesStep.history_update
#print axioms BanditBayesStep.observed_history_update
#print axioms BanditBayesStep.iid_prefix_extension
#print axioms BanditBayesStep.arm_history_next
#print axioms BanditBayesStep.arm_posterior_step

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open InfoRelaxTS.Monotone

namespace BanditHistory
variable {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

@[instance_reducible]
def history (N : Fin K → ℕ) : MeasurableSpace (Outcome K Θ) :=
  ⨆ a : Fin K, ⨆ i : ℕ, ⨆ _ : i < N a,
    MeasurableSpace.comap (fun ω : Outcome K Θ => (ω a).2 i) inferInstance

lemma history_le (N : Fin K → ℕ) : history (Θ := Θ) N ≤ MeasurableSpace.pi := by
  apply iSup_le
  intro a
  apply iSup_le
  intro i
  apply iSup_le
  intro _
  exact measurable_iff_comap_le.mp (by fun_prop)

lemma reward_measurable (N : Fin K → ℕ) (a : Fin K) (i : ℕ) (hi : i < N a) :
    Measurable[history N] (fun ω : Outcome K Θ => (ω a).2 i) := by
  apply measurable_iff_comap_le.mpr
  exact le_iSup_of_le a (le_iSup_of_le i (le_iSup_of_le hi le_rfl))

lemma yseq_measurable (U : Fin K → Y → ℝ → Y)
    (hU : ∀ a, Measurable (Function.uncurry (U a))) (y : Fin K → Y)
    (N : Fin K → ℕ) (a : Fin K) (n : ℕ) (hn : n ≤ N a) :
    Measurable[history (Θ := Θ) N] (yseq U y a n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (hU a).comp ((ih (by omega)).prodMk (reward_measurable N a n (by omega)))

lemma muBar_measurable (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ) (a : Fin K) :
    Measurable (muBar R P a) := by
  have hm : StronglyMeasurable (mu R a) := stronglyMeasurable_id.integral_kernel
  exact hm.integral_kernel.measurable

lemma muHat_measurable (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (y : Fin K → Y) (N : Fin K → ℕ) (a : Fin K) (n : ℕ) (hn : n ≤ N a) :
    Measurable[history N] (muHat R P U y a n : Outcome K Θ → ℝ) :=
  (muBar_measurable R P a).comp (yseq_measurable U hU y N a n hn)

lemma S_measurable (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (y : Fin K → Y) (N : Fin K → ℕ) (a : Fin K) (n : ℕ) (hn : n ≤ N a+1) :
    Measurable[history N] (S R P U y a n : Outcome K Θ → ℝ) := by
  exact Finset.measurable_sum _ (fun i hi =>
    muHat_measurable R P U hU y N a i (by have := Finset.mem_range.mp hi; omega))

def levels (k : Fin K) (n T : ℕ) (a : Fin K) : ℕ := if a=k then n else T-1

lemma alloc_le (T : ℕ) (m : Fin K → ℕ) (hm : m ∈ allocs K T) (a : Fin K) :
    m a ≤ T := by
  have hs : ∑ i, m i = T := by simpa [allocs,Finset.Nat.mem_antidiagonalTuple] using hm
  rw [← hs]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (m i)) (Finset.mem_univ a)

lemma coefficients_measurable (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (y : Fin K → Y) (k : Fin K) (n T : ℕ) (m : Fin K → ℕ) (hm : m ∈ allocs K T) :
    Measurable[history (levels k n T)] (fun ω : Outcome K Θ =>
      (∑ a ∈ Finset.univ.filter (· < k), S R P U y a (m a) ω) +
        S R P U y k (min (m k) n) ω +
        (∑ a ∈ Finset.univ.filter (k < ·), (m a : ℝ)*muHat R P U y a (T-1) ω)) := by
  apply Measurable.add
  · apply Measurable.add
    · apply Finset.measurable_sum
      intro a ha
      have hak := (Finset.mem_filter.mp ha).2
      apply S_measurable R P U hU
      have := alloc_le T m hm a
      simp only [levels,if_neg (ne_of_lt hak)]
      omega
    · apply S_measurable R P U hU
      simpa [levels] using (min_le_right (m k) n).trans (Nat.le_succ n)
  · apply Finset.measurable_sum
    intro a ha
    have hak := (Finset.mem_filter.mp ha).2
    apply Measurable.const_mul
    apply muHat_measurable R P U hU
    simp [levels,ne_of_gt hak]

end BanditHistory
#print axioms BanditHistory.coefficients_measurable

open MeasureTheory ProbabilityTheory
open InfoRelaxTS.Monotone
open scoped ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace BanditFiniteHistory
variable {Θ Y : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
  [Nonempty Θ] [MeasurableSpace Y]

def belief (U : Y → ℝ → Y) (y : Y) : (n : ℕ) → (Fin n → ℝ) → Y
  | 0, _ => y
  | n+1, h => U (belief U y n (fun i => h i.castSucc)) (h (Fin.last n))

lemma belief_measurable (U : Y → ℝ → Y) (hU : Measurable (Function.uncurry U)) (y : Y) (n : ℕ) :
    Measurable (belief U y n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hU.comp ((ih.comp (by fun_prop)).prodMk (measurable_pi_apply _))

lemma snoc_prefix (r : ℕ → ℝ) (n : ℕ) :
    Fin.snoc (fun i : Fin n => r i) (r n) = fun i : Fin (n+1) => r i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

lemma map_left_compProd {H J Z : Type*} [MeasurableSpace H] [MeasurableSpace J] [MeasurableSpace Z]
    (ν : Measure H) [IsProbabilityMeasure ν] (Q : Kernel J Z) [IsMarkovKernel Q]
    (f : H → J) (hf : Measurable f) :
    (ν ⊗ₘ Q.comap f hf).map (fun z => (f z.1,z.2)) = ν.map f ⊗ₘ Q := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.compProd_apply (hs.preimage (by fun_prop)), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

lemma arm_joint
    (R : Kernel Θ ℝ) [IsMarkovKernel R]
    (P : Kernel Y Θ) [IsMarkovKernel P] (U : Y → ℝ → Y)
    (hU : Measurable (Function.uncurry U))
    (hconj : ∀ y, (fun r => P (U y r)) =ᵐ[R ∘ₘ P y] posterior R (P y))
    (y : Y) (n : ℕ) :
    ((P y) ⊗ₘ BanditLaw.iidKernel R).map (fun z => ((fun i : Fin n => z.2 i),z.1)) =
      (((P y) ⊗ₘ BanditLaw.iidKernel R).map (fun z => (fun i : Fin n => z.2 i))) ⊗ₘ
        P.comap (belief U y n) (belief_measurable U hU y n) := by
  let μ := (P y) ⊗ₘ BanditLaw.iidKernel R
  induction n with
  | zero =>
    let e : Fin 0 → ℝ := fun i => Fin.elim0 i
    have he : (fun z : Θ × (ℕ → ℝ) => (fun i : Fin 0 => z.2 i)) = fun _ => e := by
      funext z; exact Subsingleton.elim _ _
    have he2 : (fun z : Θ × (ℕ → ℝ) => ((fun i : Fin 0 => z.2 i),z.1)) =
        (fun θ => (e,θ)) ∘ Prod.fst := by
      funext z; simp only [Function.comp_apply]; congr 1; exact Subsingleton.elim _ _
    rw [he,he2,← Measure.map_map (by fun_prop) measurable_fst,
      show ((P y) ⊗ₘ BanditLaw.iidKernel R).map Prod.fst = P y from Measure.fst_compProd _ _,
      Measure.map_const,measure_univ,one_smul]
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs,Measure.dirac_compProd_apply hs]
    rfl
  | succ n ih =>
    let X : Θ × (ℕ → ℝ) → (Fin n → ℝ) × ℝ := fun z => ((fun i => z.2 i),z.2 n)
    have hX : Measurable X := by fun_prop
    let f : ((Fin n → ℝ) × ℝ) → (Fin (n+1) → ℝ) := fun z => Fin.snoc z.1 z.2
    have hf : Measurable f := by fun_prop
    let Q := P.comap (belief U y (n+1)) (belief_measurable U hU y (n+1))
    let : IsMarkovKernel Q := Kernel.IsMarkovKernel.comap P _
    have hcd := BanditBayesStep.arm_posterior_step R P U hU hconj y n
      (belief U y n) (belief_measurable U hU y n) ih
    have hj : μ.map (fun z => (X z,z.1)) = (μ.map X) ⊗ₘ Q.comap f hf := by
      rw [← compProd_map_condDistrib (by fun_prop : AEMeasurable (Prod.fst : Θ × (ℕ → ℝ) → Θ) μ)]
      apply Measure.compProd_congr
      simpa [Q,Kernel.comap,Kernel.coe_mk,f,belief] using hcd
    let : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
    have hmap := congrArg (fun η : Measure (((Fin n → ℝ) × ℝ) × Θ) =>
      η.map (fun z => (f z.1,z.2))) hj
    rw [Measure.map_map (by fun_prop) (by fun_prop),map_left_compProd,
      Measure.map_map hf hX] at hmap
    simpa only [Function.comp_def,X,f,snoc_prefix,μ,Q] using hmap

lemma arm_condDistrib
    (R : Kernel Θ ℝ) [IsMarkovKernel R]
    (P : Kernel Y Θ) [IsMarkovKernel P] (U : Y → ℝ → Y)
    (hU : Measurable (Function.uncurry U))
    (hconj : ∀ y, (fun r => P (U y r)) =ᵐ[R ∘ₘ P y] posterior R (P y))
    (y : Y) (n : ℕ) :
    condDistrib (Prod.fst : Θ × (ℕ → ℝ) → Θ) (fun z => (fun i : Fin n => z.2 i))
        ((P y) ⊗ₘ BanditLaw.iidKernel R) =ᵐ[
          ((P y) ⊗ₘ BanditLaw.iidKernel R).map (fun z => (fun i : Fin n => z.2 i))]
      (fun h => P (belief U y n h)) :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (by fun_prop) measurable_fst
    (arm_joint R P U hU hconj y n)

lemma arm_condMean
    (R : Kernel Θ ℝ) [IsMarkovKernel R]
    (P : Kernel Y Θ) [IsMarkovKernel P] (U : Y → ℝ → Y)
    (hU : Measurable (Function.uncurry U))
    (hconj : ∀ y, (fun r => P (U y r)) =ᵐ[R ∘ₘ P y] posterior R (P y))
    (y : Y) (n : ℕ) (F : Θ → ℝ) (hF : StronglyMeasurable F) (hi : Integrable F (P y)) :
    ((P y) ⊗ₘ BanditLaw.iidKernel R)[fun z => F z.1 |
      MeasurableSpace.comap (fun z : Θ × (ℕ → ℝ) => (fun i : Fin n => z.2 i)) inferInstance]
      =ᵐ[(P y) ⊗ₘ BanditLaw.iidKernel R]
      (fun z => ∫ θ, F θ ∂P (belief U y n (fun i => z.2 i))) := by
  let μ := (P y) ⊗ₘ BanditLaw.iidKernel R
  have hi' : Integrable (fun z : Θ × (ℕ → ℝ) => F z.1) μ := by
    have he : μ.map Prod.fst = P y := Measure.fst_compProd _ _
    have h : Integrable F (μ.map Prod.fst) := by rw [he]; exact hi
    exact h.comp_measurable measurable_fst
  have hc := condExp_ae_eq_integral_condDistrib (μ := μ)
    (by fun_prop : Measurable (fun z : Θ × (ℕ → ℝ) => (fun i : Fin n => z.2 i)))
    measurable_fst.aemeasurable hF hi'
  have hp := ae_of_ae_map (μ := μ) (f := fun z : Θ × (ℕ → ℝ) => (fun i : Fin n => z.2 i))
    (by fun_prop) (arm_condDistrib R P U hU hconj y n)
  apply hc.trans
  filter_upwards [hp] with z hz
  rw [hz]


lemma product_joint {A B H : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace H]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (X : A → H) (Z : A → Θ) (hX : Measurable X) (hZ : Measurable Z)
    (Q : Kernel H Θ) [IsMarkovKernel Q]
    (hj : μ.map (fun z => (X z,Z z)) = μ.map X ⊗ₘ Q) :
    (μ.prod ν).map (fun z => ((X z.1,z.2),Z z.1)) =
      ((μ.prod ν).map (fun z => (X z.1,z.2))) ⊗ₘ Q.comap Prod.fst measurable_fst := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun z : (A × B) × Θ => f ((X z.1.1,z.1.2),z.2)) := by fun_prop
  have hmi := hm.lintegral_kernel_prod_right' (κ := Q.comap (fun z : A × B => X z.1) (by fun_prop))
  rw [lintegral_map hf (by fun_prop),Measure.lintegral_compProd hf,
    lintegral_map (by fun_prop) (by fun_prop),lintegral_prod _ (by fun_prop),
    lintegral_prod _ (by simpa only [Kernel.comap,Kernel.coe_mk,Function.uncurry_def] using hmi.aemeasurable)]
  conv_lhs => rw [lintegral_lintegral_swap (by fun_prop)]
  conv_rhs => rw [lintegral_lintegral_swap
    (by simpa only [Kernel.comap,Kernel.coe_mk,Function.uncurry_def] using hmi.aemeasurable)]
  apply lintegral_congr
  intro b
  have he := congrArg (fun η : Measure (H × Θ) => ∫⁻ z, f ((z.1,b),z.2) ∂η) hj
  rw [lintegral_map (by fun_prop) (hX.prodMk hZ),Measure.lintegral_compProd (by fun_prop),
    lintegral_map (by fun_prop) hX] at he
  exact he

lemma transported_joint {Ω A H : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure A) [IsProbabilityMeasure ν]
    (e : Ω → A) (he : Measurable e) (hmap : μ.map e = ν)
    (X : A → H) (Z : A → Θ) (hX : Measurable X) (hZ : Measurable Z)
    (Q : Kernel H Θ) [IsMarkovKernel Q]
    (hj : ν.map (fun z => (X z,Z z)) = ν.map X ⊗ₘ Q) :
    μ.map (fun z => (X (e z),Z (e z))) = μ.map (fun z => X (e z)) ⊗ₘ Q := by
  rw [← hmap,Measure.map_map (hX.prodMk hZ) he,Measure.map_map hX he] at hj
  exact hj

def enlarged {K : ℕ} (a : Fin (K+1)) (n : ℕ) (ω : Outcome (K+1) Θ) :
    (Fin n → ℝ) × (Fin K → Θ × (ℕ → ℝ)) :=
  ((fun i => (ω a).2 i), fun j => ω (a.succAbove j))

lemma enlarged_measurable {K : ℕ} (a : Fin (K+1)) (n : ℕ) :
    Measurable (enlarged (Θ := Θ) a n) := by unfold enlarged; fun_prop

lemma enlarged_joint {K : ℕ}
    (R : Fin (K+1) → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin (K+1) → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin (K+1) → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (y : Fin (K+1) → Y) (a : Fin (K+1)) (n : ℕ) :
    (I R P y).map (fun ω => (enlarged a n ω,(ω a).1)) =
      (I R P y).map (enlarged a n) ⊗ₘ
        (P a).comap (fun z => belief (U a) (y a) n z.1)
          ((belief_measurable (U a) (hM.meas a) (y a) n).comp measurable_fst) := by
  let : IsProbabilityMeasure (I R P y) := BanditLaw.outcome_probability R P y
  let ν := fun b => P b (y b) ⊗ₘ BanditLaw.iidKernel (R b)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K+1) => Θ × (ℕ → ℝ)) a
  have he : (I R P y).map e = (ν a).prod (Measure.pi (fun j => ν (a.succAbove j))) := by
    rw [BanditLaw.outcome_law]
    exact (measurePreserving_piFinSuccAbove ν a).map_eq
  let X : Θ × (ℕ → ℝ) → (Fin n → ℝ) := fun z i => z.2 i
  let Q := (P a).comap (belief (U a) (y a) n) (belief_measurable (U a) (hM.meas a) (y a) n)
  let : IsMarkovKernel Q := Kernel.IsMarkovKernel.comap (P a) _
  have hj := arm_joint (R a) (P a) (U a) (hM.meas a) (hM.conj a) (y a) n
  have hp := product_joint (ν a) (Measure.pi (fun j => ν (a.succAbove j))) X Prod.fst
    (by fun_prop) measurable_fst Q hj
  have ht := transported_joint (I R P y) _ e e.measurable he
    (fun z => (X z.1,z.2)) (fun z => z.1.1) (by fun_prop) (by fun_prop)
    (Q.comap Prod.fst measurable_fst) hp
  exact ht

lemma belief_yseq {K : ℕ} (U : Fin K → Y → ℝ → Y) (y : Fin K → Y) (a : Fin K)
    (n : ℕ) (ω : Outcome K Θ) :
    belief (U a) (y a) n (fun i => (ω a).2 i) = yseq U y a n ω := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [belief,yseq,Fin.val_castSucc,Fin.val_last] using congrArg (fun b => U a b ((ω a).2 n)) ih

lemma enlarged_condMean {K : ℕ}
    (R : Fin (K+1) → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin (K+1) → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin (K+1) → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (y : Fin (K+1) → Y) (a : Fin (K+1)) (n : ℕ) :
    (I R P y)[fun ω => mu R a (ω a).1 |
      MeasurableSpace.comap (enlarged (Θ := Θ) a n) inferInstance] =ᵐ[I R P y]
      muHat R P U y a n := by
  let : IsProbabilityMeasure (I R P y) := BanditLaw.outcome_probability R P y
  have hm : StronglyMeasurable (mu R a) := stronglyMeasurable_id.integral_kernel
  have hi : Integrable (mu R a) (P a (y a)) := by
    have h := hM.integrable a (y a)
    change Integrable id ((R a) ∘ₘ (P a (y a))) at h
    rw [Measure.comp_eq_comp_const_apply] at h
    exact h.integral_comp
  have hi' : Integrable (fun ω : Outcome (K+1) Θ => mu R a (ω a).1) (I R P y) := by
    rw [← BanditLaw.parameter_marginal R P y a] at hi
    exact hi.comp_measurable (by fun_prop)
  have hcd := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (enlarged_measurable a n)
    (by fun_prop : Measurable (fun ω : Outcome (K+1) Θ => (ω a).1))
    (enlarged_joint R P U hM y a n)
  have hp := ae_of_ae_map (enlarged_measurable (Θ := Θ) a n).aemeasurable hcd
  have hc := condExp_ae_eq_integral_condDistrib (μ := I R P y) (enlarged_measurable a n)
    ((measurable_pi_apply a).fst.aemeasurable) hm hi'
  apply hc.trans
  filter_upwards [hp] with ω hω
  rw [hω]
  change (∫ θ, mu R a θ ∂P a (belief (U a) (y a) n (fun i => (ω a).2 i))) = _
  rw [belief_yseq]
  rfl

lemma history_le_enlarged {K : ℕ} (a : Fin (K+1)) (N : Fin (K+1) → ℕ) :
    BanditHistory.history (Θ := Θ) N ≤ MeasurableSpace.comap (enlarged a (N a)) inferInstance := by
  let G := MeasurableSpace.comap (enlarged (Θ := Θ) a (N a)) inferInstance
  have hG : Measurable[G] (enlarged (Θ := Θ) a (N a)) :=
    measurable_iff_comap_le.mpr le_rfl
  apply iSup_le
  intro b
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  apply measurable_iff_comap_le.mp
  change Measurable[G] (fun ω : Outcome (K+1) Θ => (ω b).2 i)
  by_cases hba : b=a
  · subst b
    have h := (measurable_pi_apply (⟨i,hi⟩ : Fin (N a))).comp hG.fst
    exact h
  · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hba
    subst b
    have h := (measurable_pi_apply i).comp (((measurable_pi_apply j).comp hG.snd).snd)
    exact h

lemma posterior_history_succ {K : ℕ}
    (R : Fin (K+1) → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin (K+1) → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin (K+1) → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (y : Fin (K+1) → Y) (a : Fin (K+1)) (N : Fin (K+1) → ℕ) :
    (I R P y)[fun ω => mu R a (ω a).1 | BanditHistory.history N] =ᵐ[I R P y]
      muHat R P U y a (N a) := by
  let : IsProbabilityMeasure (I R P y) := BanditLaw.outcome_probability R P y
  have hg := enlarged_condMean R P U hM y a (N a)
  have hi : Integrable (muHat R P U y a (N a)) (I R P y) := integrable_condExp.congr hg
  have ht := condExp_condExp_of_le (μ := I R P y)
    (f := fun ω : Outcome (K+1) Θ => mu R a (ω a).1)
    (history_le_enlarged (Θ := Θ) a N) (enlarged_measurable (Θ := Θ) a (N a)).comap_le
  have hc := condExp_congr_ae (m := BanditHistory.history N) hg
  have hm := BanditHistory.muHat_measurable R P U hM.meas y N a (N a) le_rfl
  have he := condExp_of_stronglyMeasurable (BanditHistory.history_le N) hm.stronglyMeasurable hi
  exact ht.symm.trans (hc.trans (Filter.EventuallyEq.of_eq he))

lemma posterior_history {K : ℕ}
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (y : Fin K → Y) (a : Fin K) (N : Fin K → ℕ) :
    (I R P y)[fun ω => mu R a (ω a).1 | BanditHistory.history N] =ᵐ[I R P y]
      muHat R P U y a (N a) := by
  cases K with
  | zero => exact Fin.elim0 a
  | succ K => exact posterior_history_succ R P U hM y a N
end BanditFiniteHistory
#print axioms BanditFiniteHistory.arm_joint

#print axioms BanditFiniteHistory.arm_condMean

#print axioms BanditFiniteHistory.product_joint

#print axioms BanditFiniteHistory.enlarged_condMean

#print axioms BanditFiniteHistory.posterior_history

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace MonotoneJensen
lemma below (φ : ℝ → ℝ) (hφ : Monotone φ) (c : ℝ) (hc : c+φ c ≤ 0) (x : ℝ) :
    max (c+φ x) 0 ≤ max (x+φ x) 0 := by
  by_cases hx : x ≤ c
  · have h := hφ hx
    rw [max_eq_right (show c+φ x ≤ 0 by linarith)]
    exact le_max_right _ _
  · exact max_le_max (by linarith [lt_of_not_ge hx]) le_rfl
lemma above (φ : ℝ → ℝ) (hφ : Monotone φ) (c : ℝ) (hc : 0 ≤ c+φ c) (x : ℝ) :
    max (c+φ x) 0 ≤ max (x+φ x) 0-x+c := by
  by_cases hx : x ≤ c
  · apply max_le
    · have h := le_max_left (x+φ x) 0;linarith
    · have h := le_max_right (x+φ x) 0;linarith
  · have h := hφ (le_of_not_ge hx)
    rw [max_eq_left (show 0 ≤ c+φ x by linarith),max_eq_left (show 0 ≤ x+φ x by linarith)]
    linarith
end MonotoneJensen

namespace MonotoneJensen
lemma conditional {Ω : Type*} {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (φ : ℝ → Ω → ℝ) (hmono : ∀ ω, Monotone fun x => φ x ω)
    (hmeas : ∀ x, Measurable[mH] (φ x))
    (hjoint : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mH) _ (Function.uncurry φ))
    (X : Ω → ℝ) (hX : Integrable X μ) :
    ∫⁻ ω, ENNReal.ofReal (max ((μ[X | mH]) ω + φ (X ω) ω) 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω + φ (X ω) ω) 0) ∂μ := by
  let c := μ[X | mH]
  let A := fun ω => max (X ω+φ (X ω) ω) 0
  let B := fun ω => max (c ω+φ (X ω) ω) 0
  let S := {ω | 0 ≤ c ω+φ (c ω) ω}
  let Z := S.indicator (fun ω => X ω-c ω)
  have hId : @Measurable Ω Ω mΩ mH id := measurable_id'' hmH
  have hcH : Measurable[mH] c := stronglyMeasurable_condExp.measurable
  have hφc : Measurable[mH] (fun ω => φ (c ω) ω) := hjoint.comp (hcH.prodMk measurable_id)
  have hS : MeasurableSet[mH] S := measurableSet_le measurable_const (hcH.add hφc)
  have hjfull : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mΩ) _ (Function.uncurry φ) :=
    hjoint.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono hmH)) le_rfl
  have hφx : AEMeasurable (fun ω => φ (X ω) ω) μ :=
    hjfull.comp_aemeasurable (hX.aemeasurable.prodMk aemeasurable_id)
  have hc : Integrable c μ := integrable_condExp
  have hAm : AEStronglyMeasurable A μ := ((hX.aemeasurable.add hφx).max aemeasurable_const).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B μ := ((hc.aemeasurable.add hφx).max aemeasurable_const).aestronglyMeasurable
  have hZn : Integrable Z μ := (hX.sub hc).indicator (hmH S hS)
  have hZint : (∫ ω, Z ω ∂μ)=0 := by
    dsimp [Z]
    rw [integral_indicator (hmH S hS),integral_sub hX.integrableOn hc.integrableOn,
      setIntegral_condExp hmH hX hS]
    ring
  have hbound (ω) : B ω ≤ A ω-Z ω := by
    by_cases hs : ω ∈ S
    · rw [show Z ω=X ω-c ω from Set.indicator_of_mem hs _]
      have h := above (fun x => φ x ω) (hmono ω) (c ω) hs (X ω)
      dsimp [A,B]
      linarith
    · rw [show Z ω=0 from Set.indicator_of_notMem hs _,sub_zero]
      exact below (fun x => φ x ω) (hmono ω) (c ω) (le_of_not_ge hs) (X ω)
  change (∫⁻ ω, ENNReal.ofReal (B ω) ∂μ) ≤ ∫⁻ ω, ENNReal.ofReal (A ω) ∂μ
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (A ω) ∂μ)=⊤
  · rw [htop];exact le_top
  have hAn : 0 ≤ᵐ[μ] A := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hBn : 0 ≤ᵐ[μ] B := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hAi := (lintegral_ofReal_ne_top_iff_integrable hAm hAn).mp htop
  have hBi : Integrable B μ := (hAi.sub hZn).mono' hBm (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right (c ω+φ (X ω) ω) 0)]
    exact hbound ω)
  have hInt := integral_mono_ae hBi (hAi.sub hZn) (Filter.Eventually.of_forall hbound)
  have hcancel : (∫ ω, (A-Z) ω ∂μ)=∫ ω, A ω ∂μ := by
    change (∫ ω, A ω-Z ω ∂μ)=∫ ω, A ω ∂μ
    rw [integral_sub hAi hZn,hZint,sub_zero]
  rw [hcancel] at hInt
  rw [← ofReal_integral_eq_lintegral_ofReal hBi hBn,← ofReal_integral_eq_lintegral_ofReal hAi hAn]
  exact ENNReal.ofReal_le_ofReal hInt
end MonotoneJensen
namespace MonotoneJensen
lemma integrable_iSup {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun ω => ⨆ i, f i ω) μ := by
  classical
  have h : Integrable (Finset.univ.sup' Finset.univ_nonempty f) μ :=
    Finset.sup'_induction Finset.univ_nonempty f (p := fun g => Integrable g μ)
      (fun a ha b hb => ha.sup hb) (fun i _ => hf i)
  convert h using 1
  funext ω
  simp only [Finset.sup'_apply,Finset.sup'_univ_eq_ciSup]
lemma split_sup {ι : Type*} [Fintype ι] [Nonempty ι] (P : ι → Prop) [DecidablePred P]
    [Nonempty {i // P i}] [Nonempty {i // ¬P i}] (a b : ι → ℝ) (c : ℝ) :
    (⨆ i, if P i then a i else c+b i)=max (⨆ i : {i // P i},a i) (c+⨆ i : {i // ¬P i},b i) := by
  have hbound (f : ι → ℝ) : BddAbove (Set.range f) := (Set.finite_range _).bddAbove
  apply le_antisymm
  · apply ciSup_le
    intro i
    split_ifs with hi
    · have h : a i ≤ ⨆ j : {j // P j}, a j :=
        le_ciSup (f := fun j : {j // P j} => a j) (Set.finite_range _).bddAbove ⟨i,hi⟩
      exact h.trans (le_max_left _ _)
    · have h : b i ≤ ⨆ j : {j // ¬P j}, b j :=
        le_ciSup (f := fun j : {j // ¬P j} => b j) (Set.finite_range _).bddAbove ⟨i,hi⟩
      exact (add_le_add_right h c).trans (le_max_right _ _)
  · apply max_le
    · apply ciSup_le
      intro i
      have h := le_ciSup (hbound (fun i => if P i then a i else c+b i)) i.val
      simpa only [if_pos i.property] using h
    · apply (le_sub_iff_add_le').mp
      apply ciSup_le
      intro i
      have h := le_ciSup (hbound (fun i => if P i then a i else c+b i)) i.val
      rw [if_neg i.property] at h
      linarith
lemma max_shift (a b c : ℝ) : max a (c+b)=max (c+(b-a)) 0+a := by
  by_cases h : a ≤ c+b
  · rw [max_eq_right h,max_eq_left (show 0 ≤ c+(b-a) by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_right (show c+(b-a) ≤ 0 by linarith)]
    ring
lemma nat_step (i n : ℕ) : ((i-n : ℕ) : ℝ) =
    (if n+1 ≤ i then (1 : ℝ) else 0)+((i-n-1 : ℕ) : ℝ) := by
  by_cases hi : n+1 ≤ i
  · rw [if_pos hi]
    have h : i-n=(i-n-1)+1 := by omega
    calc
      ((i-n : ℕ) : ℝ) = ((i-n-1+1 : ℕ) : ℝ) := congrArg Nat.cast h
      _ = 1+((i-n-1 : ℕ) : ℝ) := by push_cast; ring
  · have h : i ≤ n := by omega
    simp [Nat.sub_eq_zero_of_le h,hi]
lemma finite_max_nonempty {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (w : ι → ℕ) (C : ι → Ω → ℝ) (hCmeas : ∀ i, Measurable[mH] (C i))
    (hCint : ∀ i, Integrable (C i) μ) (X : Ω → ℝ) (hX : Integrable X μ) (n : ℕ)
    [Nonempty {i // w i ≤ n}] [Nonempty {i // ¬ w i ≤ n}] :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
      (μ[X|mH]) ω*(if n+1 ≤ w i then (1 : ℝ) else 0)+((w i-n-1 : ℕ) : ℝ)*X ω+C i ω) ∂μ) ≤
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
      ((w i-n : ℕ) : ℝ)*X ω+C i ω) ∂μ := by
  classical
  let P := fun i : ι => w i ≤ n
  let L := fun ω => ⨆ i : {i // P i}, C i ω
  let U := fun z ω => ⨆ i : {i // ¬P i}, ((w i.val-n-1 : ℕ) : ℝ)*z+C i ω
  let φ := fun z ω => U z ω-L ω
  have hmono : ∀ ω, Monotone fun z => φ z ω := by
    intro ω a b hab
    apply sub_le_sub_right
    apply ciSup_le
    intro i
    apply le_trans _ (le_ciSup (Set.finite_range _).bddAbove i)
    have h := mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg (w i.val-n-1) : (0 : ℝ) ≤ _)
    linarith
  have hLm : Measurable[mH] L := Measurable.iSup (fun i => hCmeas i)
  have hφm : ∀ z, Measurable[mH] (φ z) := by
    intro z
    exact (Measurable.iSup (fun i : {i // ¬P i} =>
      (measurable_const (a := ((w i.val-n-1 : ℕ) : ℝ)*z)).add (hCmeas i))).sub hLm
  have hφjoint : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mH) _ (Function.uncurry φ) := by
    letI := mH
    exact (Measurable.iSup (fun i : {i // ¬P i} =>
      (measurable_const.mul measurable_fst).add ((hCmeas i).comp measurable_snd))).sub (hLm.comp measurable_snd)
  have hLi : Integrable L μ := integrable_iSup μ _ (fun i => hCint i)
  have hUi : Integrable (fun ω => U (X ω) ω) μ := integrable_iSup μ _
    (fun i => (hX.const_mul ((w i.val-n-1 : ℕ) : ℝ)).add (hCint i))
  have hφi : Integrable (fun ω => φ (X ω) ω) μ := hUi.sub hLi
  have hc : Integrable (μ[X|mH]) μ := integrable_condExp
  have hAi : Integrable (fun ω => max (X ω+φ (X ω) ω) 0) μ := (hX.add hφi).sup (integrable_const 0)
  have hBi : Integrable (fun ω => max ((μ[X|mH]) ω+φ (X ω) ω) 0) μ := (hc.add hφi).sup (integrable_const 0)
  have hineq := conditional hmH μ φ hmono hφm hφjoint X hX
  rw [← ofReal_integral_eq_lintegral_ofReal hBi (Filter.Eventually.of_forall fun _ => le_max_right _ _),
    ← ofReal_integral_eq_lintegral_ofReal hAi (Filter.Eventually.of_forall fun _ => le_max_right _ _)] at hineq
  have hreal : (∫ ω, max ((μ[X|mH]) ω+φ (X ω) ω) 0 ∂μ) ≤ ∫ ω, max (X ω+φ (X ω) ω) 0 ∂μ := by
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)).mp hineq
  have hsplit (z c : ℝ) (ω : Ω) :
      Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
        c*(if n+1 ≤ w i then (1 : ℝ) else 0)+((w i-n-1 : ℕ) : ℝ)*z+C i ω)
        = max (c+φ z ω) 0+L ω := by
    rw [Finset.sup'_univ_eq_ciSup]
    have hfun : (fun i : ι => c*(if n+1 ≤ w i then (1 : ℝ) else 0)+((w i-n-1 : ℕ) : ℝ)*z+C i ω)=
        (fun i => if P i then C i ω else c+((w i-n-1 : ℕ) : ℝ)*z+C i ω) := by
      funext i
      by_cases hi : P i
      · have hle : w i ≤ n := hi
        simp [hi,show ¬n+1 ≤ w i by omega,Nat.sub_eq_zero_of_le hle]
      · have hle : n+1 ≤ w i := by dsimp [P] at hi;omega
        simp [hi,hle]
    rw [hfun]
    have he := split_sup P (fun i => C i ω) (fun i => ((w i-n-1 : ℕ) : ℝ)*z+C i ω) c
    simpa only [add_assoc] using he.trans (max_shift (L ω) (U z ω) c)
  have horig (ω : Ω) : Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
      ((w i-n : ℕ) : ℝ)*X ω+C i ω)=max (X ω+φ (X ω) ω) 0+L ω := by
    rw [← hsplit (X ω) (X ω) ω]
    congr 1
    funext i
    rw [nat_step]
    ring
  simp_rw [hsplit,horig]
  rw [integral_add hBi hLi,integral_add hAi hLi]
  linarith
end MonotoneJensen
open MonotoneJensen

theorem allocation_max_step {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (w : ι → ℕ) (C : ι → Ω → ℝ) (hCmeas : ∀ i, Measurable[mH] (C i))
    (hCint : ∀ i, Integrable (C i) μ) (X : Ω → ℝ) (hX : Integrable X μ) (n : ℕ) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
      (μ[X|mH]) ω*(if n+1 ≤ w i then (1 : ℝ) else 0)+((w i-n-1 : ℕ) : ℝ)*X ω+C i ω) ∂μ) ≤
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
      ((w i-n : ℕ) : ℝ)*X ω+C i ω) ∂μ := by
  classical
  by_cases hL : Nonempty {i // w i ≤ n}
  · letI := hL
    by_cases hU : Nonempty {i // ¬w i ≤ n}
    · letI := hU
      exact finite_max_nonempty hmH μ w C hCmeas hCint X hX n
    · have hall : ∀ i, w i ≤ n := by
        intro i
        by_contra hi
        exact hU ⟨⟨i,hi⟩⟩
      have hno : ∀ i, ¬n+1 ≤ w i := by intro i; have := hall i; omega
      simp only [if_neg (hno _),mul_zero,zero_add,Nat.sub_eq_zero_of_le (hall _),
        Nat.zero_sub,Nat.cast_zero,zero_mul,zero_add,le_refl]
  · have hall : ∀ i, n+1 ≤ w i := by
      intro i
      by_contra hi
      exact hL ⟨⟨i,by omega⟩⟩
    let F : ι → Ω → ℝ := fun i ω => ((w i-n-1 : ℕ) : ℝ)*X ω+C i ω
    let J := fun ω => Finset.univ.sup' Finset.univ_nonempty (fun i : ι => F i ω)
    have hJ : Integrable J μ := by
      simpa only [J,Finset.sup'_univ_eq_ciSup] using integrable_iSup μ F
        (fun i => (hX.const_mul ((w i-n-1 : ℕ) : ℝ)).add (hCint i))
    have hshift (c : ℝ) (ω : Ω) :
        Finset.univ.sup' Finset.univ_nonempty (fun i : ι => c+F i ω) = c+J ω :=
      (Finset.add_sup' Finset.univ (fun i : ι => F i ω) c Finset.univ_nonempty).symm
    have hl (ω : Ω) : Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
        (μ[X|mH]) ω*(if n+1 ≤ w i then (1 : ℝ) else 0)+((w i-n-1 : ℕ) : ℝ)*X ω+C i ω) =
        (μ[X|mH]) ω+J ω := by
      simp only [if_pos (hall _),mul_one]
      simpa only [F,add_assoc] using hshift ((μ[X|mH]) ω) ω
    have hr (ω : Ω) : Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
        ((w i-n : ℕ) : ℝ)*X ω+C i ω) = X ω+J ω := by
      rw [← hshift (X ω) ω]
      congr 1
      funext i
      rw [nat_step (w i) n,if_pos (hall i)]
      dsimp [F]
      ring
    simp_rw [hl,hr]
    rw [integral_add integrable_condExp hJ,integral_add hX hJ,integral_condExp hmH]

namespace BanditReduction
open InfoRelaxTS.Monotone
lemma sup_subtype {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ)
    [Nonempty {a // a ∈ s}] :
    Finset.univ.sup' Finset.univ_nonempty (fun a : {a // a ∈ s} => f a) = s.sup' hs f := by
  classical
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    exact Finset.le_sup' f a.property
  · apply Finset.sup'_le
    intro a ha
    exact Finset.le_sup' (fun a : {a // a ∈ s} => f a) (Finset.mem_univ ⟨a,ha⟩)

variable {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
noncomputable def coeff (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) (y : Fin K → Y) (k : Fin K) (n T : ℕ)
    (m : Fin K → ℕ) (ω : Outcome K Θ) : ℝ :=
  (∑ a ∈ Finset.univ.filter (· < k), S R P U y a (m a) ω) +
    S R P U y k (min (m k) n) ω +
    (∑ a ∈ Finset.univ.filter (k < ·), (m a : ℝ)*muHat R P U y a (T-1) ω)

lemma actual_step (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (U : Fin K → Y → ℝ → Y) (y : Fin K → Y)
    (k : Fin K) (n T : ℕ) (H : MeasurableSpace (Outcome K Θ))
    (hH : H ≤ MeasurableSpace.pi) [IsProbabilityMeasure (I R P y)]
    (hX : Integrable (muHat R P U y k (T-1)) (I R P y))
    (hCmeas : ∀ m ∈ allocs K T, Measurable[H] (coeff R P U y k n T m))
    (hCint : ∀ m ∈ allocs K T, Integrable (coeff R P U y k n T m) (I R P y))
    (hmean : (I R P y)[muHat R P U y k (T-1)|H] =ᵐ[I R P y] muHat R P U y k n) :
    Ukn R P U k (n+1) T y ≤ Ukn R P U k n T y := by
  classical
  let A := {m // m ∈ allocs K T}
  letI : Nonempty A := ⟨⟨(allocs_nonempty K T).choose,(allocs_nonempty K T).choose_spec⟩⟩
  have h := allocation_max_step hH (I R P y) (fun m : A => m.val k)
    (fun m : A => coeff R P U y k n T m) (fun m => hCmeas m m.property)
    (fun m => hCint m m.property) (muHat R P U y k (T-1)) hX n
  have hl (ω : Outcome K Θ) := sup_subtype (allocs K T) (allocs_nonempty K T)
    (fun m => ((I R P y)[muHat R P U y k (T-1)|H]) ω *
      (if n+1 ≤ m k then (1:ℝ) else 0) + ((m k-n-1 : ℕ):ℝ)*muHat R P U y k (T-1) ω +
      coeff R P U y k n T m ω)
  have hr (ω : Outcome K Θ) := sup_subtype (allocs K T) (allocs_nonempty K T)
    (fun m => ((m k-n : ℕ):ℝ)*muHat R P U y k (T-1) ω + coeff R P U y k n T m ω)
  have hleft := integral_congr_ae (μ := I R P y) (Filter.Eventually.of_forall hl)
  have hright := integral_congr_ae (μ := I R P y) (Filter.Eventually.of_forall hr)
  rw [hleft,hright] at h
  have old (ω : Outcome K Θ) (m : Fin K → ℕ) :
      ((m k-n : ℕ):ℝ)*muHat R P U y k (T-1) ω + coeff R P U y k n T m ω =
      (∑ a ∈ Finset.univ.filter (· < k), S R P U y a (m a) ω) +
      (S R P U y k (min (m k) n) ω + ((m k-n : ℕ):ℝ)*muHat R P U y k (T-1) ω) +
      (∑ a ∈ Finset.univ.filter (k < ·), (m a:ℝ)*muHat R P U y a (T-1) ω) := by
    unfold coeff; ring
  have nxt (ω : Outcome K Θ) (m : Fin K → ℕ) :
      muHat R P U y k n ω*(if n+1 ≤ m k then (1:ℝ) else 0) +
        ((m k-n-1 : ℕ):ℝ)*muHat R P U y k (T-1) ω + coeff R P U y k n T m ω =
      (∑ a ∈ Finset.univ.filter (· < k), S R P U y a (m a) ω) +
      (S R P U y k (min (m k) (n+1)) ω + ((m k-(n+1) : ℕ):ℝ)*muHat R P U y k (T-1) ω) +
      (∑ a ∈ Finset.univ.filter (k < ·), (m a:ℝ)*muHat R P U y a (T-1) ω) := by
    have hsub : m k-(n+1) = m k-n-1 := by omega
    rw [hsub]
    by_cases hm : n+1 ≤ m k
    · have hn : n ≤ m k := by omega
      simp only [if_pos hm,min_eq_right hm,min_eq_right hn,coeff,S,Finset.sum_range_succ,mul_one]
      ring
    · have hn : m k ≤ n := by omega
      simp only [if_neg hm,min_eq_left hn,min_eq_left (hn.trans (Nat.le_succ _)),mul_zero,zero_add,coeff]
      ring
  have heq : (∫ ω, (allocs K T).sup' (allocs_nonempty K T) (fun m =>
      ((I R P y)[muHat R P U y k (T-1)|H]) ω * (if n+1 ≤ m k then (1:ℝ) else 0) +
      ((m k-n-1 : ℕ):ℝ)*muHat R P U y k (T-1) ω + coeff R P U y k n T m ω) ∂I R P y) =
        Ukn R P U k (n+1) T y := by
    unfold Ukn
    apply integral_congr_ae
    filter_upwards [hmean] with ω hω
    apply Finset.sup'_congr (allocs_nonempty K T) rfl
    intro m _
    rw [hω,nxt]
  rw [heq] at h
  simpa only [old,Ukn] using h
end BanditReduction
#print axioms BanditReduction.actual_step

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InfoRelaxTS.Monotone
open BanditHistory

namespace BanditPosteriorReduction
variable {K : ℕ} [NeZero K] {Θ Y : Type*}
  [MeasurableSpace Θ] [StandardBorelSpace Θ] [Nonempty Θ] [MeasurableSpace Y]

lemma history_mono (N M : Fin K → ℕ) (hNM : ∀ a, N a ≤ M a) :
    history (Θ := Θ) N ≤ history M := by
  apply iSup_le
  intro a
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  exact le_iSup_of_le a (le_iSup_of_le i (le_iSup_of_le (hi.trans_le (hNM a)) le_rfl))

/-- This is the remaining finite-history posterior obligation, not an established theorem. -/
def PosteriorHistory (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (U : Fin K → Y → ℝ → Y) (y : Fin K → Y) : Prop :=
  ∀ (a : Fin K) (N : Fin K → ℕ),
    (I R P y)[fun ω => mu R a (ω a).1 | history N] =ᵐ[I R P y]
      muHat R P U y a (N a)

lemma posterior_integrable (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (U : Fin K → Y → ℝ → Y) (y : Fin K → Y)
    (hpost : PosteriorHistory R P U y) (a : Fin K) (n : ℕ) :
    Integrable (muHat R P U y a n) (I R P y) :=
  integrable_condExp.congr (hpost a (fun _ => n))

theorem interpolation_step_of_posterior
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (y : Fin K → Y)
    (hpost : PosteriorHistory R P U y) (k : Fin K) (n T : ℕ) (hn : n < T) :
    Ukn R P U k (n+1) T y ≤ Ukn R P U k n T y := by
  letI := BanditLaw.outcome_probability R P y
  have hi := posterior_integrable R P U y hpost
  have hS (a : Fin K) (j : ℕ) : Integrable (S R P U y a j) (I R P y) :=
    integrable_finsetSum _ (fun i _ => hi a i)
  have hC (m : Fin K → ℕ) : Integrable (BanditReduction.coeff R P U y k n T m) (I R P y) := by
    apply Integrable.add
    · apply Integrable.add
      · exact integrable_finsetSum _ (fun a _ => hS a (m a))
      · exact hS k (min (m k) n)
    · exact integrable_finsetSum _ (fun a _ => (hi a (T-1)).const_mul (m a : ℝ))
  have hsmall : history (Θ := Θ) (levels k n T) ≤ history (fun _ : Fin K => T-1) := by
    apply history_mono
    intro a
    dsimp [levels]
    split_ifs <;> omega
  have hmean : (I R P y)[muHat R P U y k (T-1)|history (levels k n T)] =ᵐ[I R P y]
      muHat R P U y k n := by
    have h1 := condExp_congr_ae (m := history (levels k n T)) (hpost k (fun _ => T-1)).symm
    have h2 := condExp_condExp_of_le (μ := I R P y)
      (f := fun ω => mu R k (ω k).1) hsmall (history_le (fun _ : Fin K => T-1))
    have h3 := hpost k (levels k n T)
    simpa [levels] using h1.trans (h2.trans h3)
  exact BanditReduction.actual_step R P U y k n T (history (levels k n T))
    (history_le _) (hi k (T-1))
    (fun m hm => coefficients_measurable R P U hM.meas y k n T m hm)
    (fun m _ => hC m) hmean
end BanditPosteriorReduction
#print axioms BanditPosteriorReduction.interpolation_step_of_posterior

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace BanditEndpoints
open InfoRelaxTS.Monotone
lemma split_sum {K : ℕ} (k : Fin K) (f : Fin K → ℝ) :
    (∑ a ∈ Finset.univ.filter (· < k), f a) + f k +
      (∑ a ∈ Finset.univ.filter (k < ·), f a) = ∑ a, f a := by
  classical
  have hs : f k = ∑ a : Fin K, if a=k then f a else 0 := by simp
  rw [hs,Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rcases lt_trichotomy a k with h|h|h <;> simp [h,ne_of_lt,ne_of_gt,not_lt_of_ge,le_of_lt]
lemma split_hybrid {K : ℕ} (k : Fin K) (f g : Fin K → ℝ) (c : ℝ) :
    (∑ a ∈ Finset.univ.filter (· < k), f a) + c +
      (∑ a ∈ Finset.univ.filter (k < ·), g a) =
        ∑ a, if a<k then f a else if a=k then c else g a := by
  classical
  have hs : c = ∑ a : Fin K, if a=k then c else 0 := by simp
  conv_lhs => rw [hs,Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rcases lt_trichotomy a k with h|h|h <;> simp [h,ne_of_lt,ne_of_gt,not_lt_of_ge,le_of_lt]
lemma allocation_bound {K T : ℕ} {m : Fin K → ℕ} (hm : m ∈ allocs K T) (a : Fin K) :
    m a ≤ T := by
  have hs := Finset.Nat.mem_antidiagonalTuple.mp hm
  rw [← hs]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
lemma allocation_linear_max {K : ℕ} [NeZero K] (T : ℕ) (f : Fin K → ℝ) :
    (allocs K T).sup' (allocs_nonempty K T) (fun m => ∑ a, (m a : ℝ)*f a) =
      (T : ℝ)*Finset.univ.sup' Finset.univ_nonempty f := by
  classical
  let M := Finset.univ.sup' Finset.univ_nonempty f
  apply le_antisymm
  · apply Finset.sup'_le
    intro m hm
    have hs : (∑ a, (m a : ℝ)) = T := by
      exact_mod_cast (Finset.Nat.mem_antidiagonalTuple.mp hm)
    calc
      (∑ a, (m a : ℝ)*f a) ≤ ∑ a, (m a : ℝ)*M := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (Finset.le_sup' f (Finset.mem_univ a)) (Nat.cast_nonneg _)
      _ = (T : ℝ)*M := by rw [← Finset.sum_mul,hs]
  · obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    have hm : Pi.single a T ∈ allocs K T := by simp [allocs,Finset.Nat.mem_antidiagonalTuple]
    apply le_trans _ (Finset.le_sup' (fun m : Fin K → ℕ => ∑ b, (m b : ℝ)*f b) hm)
    rw [ha]
    simp [Pi.single_apply]
variable {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]
lemma terminal (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (U : Fin K → Y → ℝ → Y) (T : ℕ) (y : Fin K → Y) :
    WVZ R P U T y = Ukn R P U ⟨K-1,Nat.sub_one_lt (NeZero.ne K)⟩ T T y := by
  classical
  let k : Fin K := ⟨K-1,Nat.sub_one_lt (NeZero.ne K)⟩
  have hlast (a : Fin K) : ¬ k < a := by
    change ¬ (K-1 < (a:ℕ))
    have ha := a.isLt
    omega
  have hzero : Finset.univ.filter (k < ·) = ∅ := by ext a; simp [hlast]
  unfold WVZ Ukn
  apply integral_congr_ae
  filter_upwards [] with ω
  apply Finset.sup'_congr (allocs_nonempty K T) rfl
  intro m hm
  change (∑ a, S R P U y a (m a) ω) =
    (∑ a ∈ Finset.univ.filter (· < k), S R P U y a (m a) ω) +
    (S R P U y k (min (m k) T) ω + ((m k-T:ℕ):ℝ)*muHat R P U y k (T-1) ω) +
    (∑ a ∈ Finset.univ.filter (k < ·), (m a:ℝ)*muHat R P U y a (T-1) ω)
  rw [min_eq_left (allocation_bound hm k),Nat.sub_eq_zero_of_le (allocation_bound hm k)]
  simp only [Nat.cast_zero,zero_mul,add_zero,hzero,Finset.sum_empty]
  have hs := split_sum k (fun a => S R P U y a (m a) ω)
  simpa only [hzero,Finset.sum_empty,add_zero] using hs.symm
lemma initial (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (U : Fin K → Y → ℝ → Y) (T : ℕ) (y : Fin K → Y) :
    WFH R P U T y = Ukn R P U 0 0 T y := by
  classical
  have hempty : Finset.univ.filter (fun a : Fin K => a < 0) = ∅ := by simp
  unfold WFH Ukn
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [← allocation_linear_max T (fun a => muHat R P U y a (T-1) ω)]
  apply Finset.sup'_congr (allocs_nonempty K T) rfl
  intro m _
  have hs := split_sum (0 : Fin K) (fun a => (m a : ℝ)*muHat R P U y a (T-1) ω)
  simpa [hempty,S] using hs.symm
lemma transition (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (U : Fin K → Y → ℝ → Y) (T : ℕ) (y : Fin K → Y)
    (k : Fin K) (hk : (k:ℕ)+1 < K) :
    Ukn R P U ⟨(k:ℕ)+1,hk⟩ 0 T y = Ukn R P U k T T y := by
  classical
  unfold Ukn
  apply integral_congr_ae
  filter_upwards [] with ω
  apply Finset.sup'_congr (allocs_nonempty K T) rfl
  intro m hm
  rw [min_eq_left (allocation_bound hm k),Nat.sub_eq_zero_of_le (allocation_bound hm k)]
  simp only [Nat.cast_zero,zero_mul,add_zero,Nat.min_zero,Nat.sub_zero,S,Finset.sum_range_zero,zero_add]
  rw [split_hybrid,split_hybrid]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hlt : a<k
  · have hn : a < (⟨(k:ℕ)+1,hk⟩ : Fin K) := by change (a:ℕ)<(k:ℕ)+1;exact Nat.lt_succ_of_lt hlt
    simp [hlt,hn]
  · by_cases he : a=k
    · subst a
      have hn : k < (⟨(k:ℕ)+1,hk⟩ : Fin K) := by change (k:ℕ)<(k:ℕ)+1;omega
      simp [hn]
    · have hn : ¬ a < (⟨(k:ℕ)+1,hk⟩ : Fin K) := by
        change ¬ (a:ℕ)<(k:ℕ)+1
        have hx : (a:ℕ) ≠ (k:ℕ) := by exact fun h => he (Fin.ext h)
        have hh : ¬ (a:ℕ)<(k:ℕ) := hlt
        omega
      simp only [if_neg hlt,if_neg he,if_neg hn]
      split_ifs with heq
      · subst a; rfl
      · rfl
end BanditEndpoints
#print axioms BanditEndpoints.terminal

#print axioms BanditEndpoints.initial

#print axioms BanditEndpoints.transition

open InfoRelaxTS.Monotone
theorem solution {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (T : ℕ) (y : Fin K → Y) :
    (∀ (k : Fin K) (n : ℕ), n < T → Ukn R P U k (n + 1) T y ≤ Ukn R P U k n T y) ∧
      WFH R P U T y = Ukn R P U 0 0 T y ∧
      WVZ R P U T y = Ukn R P U ⟨K - 1, Nat.sub_one_lt (NeZero.ne K)⟩ T T y ∧
      ∀ (k : Fin K) (hk : (k : ℕ) + 1 < K), Ukn R P U ⟨(k : ℕ) + 1, hk⟩ 0 T y = Ukn R P U k T T y  := by
  refine ⟨?_, BanditEndpoints.initial R P U T y, BanditEndpoints.terminal R P U T y, ?_⟩
  · intro k n hn
    exact BanditPosteriorReduction.interpolation_step_of_posterior R P U hM y
      (fun a N => BanditFiniteHistory.posterior_history R P U hM y a N) k n T hn
  · intro k hk
    exact BanditEndpoints.transition R P U T y k hk

#print axioms solution
