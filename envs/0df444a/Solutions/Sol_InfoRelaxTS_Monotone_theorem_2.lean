-- Prove2me | solution 1 for InfoRelaxTS.Monotone.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:23:51.29638+00:00
-- url     : https://prove2.me/submissions/88ff99b4-b67e-4bd5-bbcb-d89015dfd5f8

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting
import Theorems.Thm_InfoRelaxTS_Monotone_WTS_ge_WFH
import Theorems.Thm_InfoRelaxTS_Monotone_Ukn_interpolation
import Theorems.Thm_InfoRelaxTS_Monotone_lemma_2
import Theorems.Thm_InfoRelaxTS_Monotone_WTS_isSupersolution
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




set_option autoImplicit false
open MeasureTheory ProbabilityTheory InfoRelaxTS.Monotone

namespace IRSMono
variable {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

lemma prior_eq_map (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] (y : Fin K → Y) :
    (I R P y).map (fun ω a => (ω a).1) = prior P y := by
  rw [BanditLaw.outcome_law]
  have h : ∀ a, ((P a (y a)) ⊗ₘ BanditLaw.iidKernel (R a)).map Prod.fst = P a (y a) :=
    fun a => Measure.fst_compProd _ _
  rw [Measure.pi_map_pi (fun a => measurable_fst.aemeasurable)]
  simp only [h]
  rfl

lemma mu_integrable [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (a : Fin K) (ya : Y) :
    Integrable (mu R a) (P a ya) := by
  have h := hM.integrable a ya
  change Integrable id ((R a) ∘ₘ (P a ya)) at h
  rw [Measure.comp_eq_comp_const_apply] at h
  exact h.integral_comp

lemma mu_measurable (R : Fin K → Kernel Θ ℝ) (a : Fin K) : Measurable (mu R a) :=
  (stronglyMeasurable_id.integral_kernel (κ := R a)).measurable

lemma integrable_sup' {Ω ι : Type*} [MeasurableSpace Ω] (s : Finset ι) (hs : s.Nonempty)
    (μ : Measure Ω) (f : ι → Ω → ℝ) (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun ω => s.sup' hs (fun i => f i ω)) μ := by
  have h : Integrable (s.sup' hs f) μ :=
    Finset.sup'_induction hs f (p := fun g => Integrable g μ)
      (fun a ha b hb => ha.sup hb) hf
  convert h using 1
  funext ω
  simp only [Finset.sup'_apply]

theorem WTS_ge_WFH [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (T : ℕ) (y : Fin K → Y) :
    WFH R P U T y ≤ WTS R P T y := by
  letI := BanditLaw.outcome_probability R P y
  unfold WFH WTS
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg T)
  let μ := I R P y
  let F : Fin K → Outcome K Θ → ℝ := fun a ω => mu R a (ω a).1
  let M : Outcome K Θ → ℝ := fun ω => Finset.univ.sup' Finset.univ_nonempty (fun a => F a ω)
  have hHle : BanditHistory.history (Θ := Θ) (fun _ : Fin K => T - 1) ≤ MeasurableSpace.pi :=
    BanditHistory.history_le _
  have hF : ∀ a, Integrable (F a) μ := by
    intro a
    have hi := mu_integrable R P U hM a (y a)
    rw [← BanditLaw.parameter_marginal R P y a] at hi
    exact hi.comp_measurable (by fun_prop)
  have hMi : Integrable M μ := integrable_sup' _ _ μ F (fun a _ => hF a)
  have hpost : ∀ a, μ[F a | BanditHistory.history (Θ := Θ) (fun _ : Fin K => T - 1)] =ᵐ[μ] muHat R P U y a (T - 1) := fun a =>
    BanditFiniteHistory.posterior_history R P U hM y a (fun _ => T - 1)
  have hhat : ∀ a, Integrable (muHat R P U y a (T - 1)) μ := fun a =>
    integrable_condExp.congr (hpost a)
  have hmono : ∀ a, μ[F a | BanditHistory.history (Θ := Θ) (fun _ : Fin K => T - 1)] ≤ᵐ[μ] μ[M | BanditHistory.history (Θ := Θ) (fun _ : Fin K => T - 1)] := fun a =>
    condExp_mono (hF a) hMi (Filter.Eventually.of_forall fun ω =>
      Finset.le_sup' (fun b => F b ω) (Finset.mem_univ a))
  have hae : ∀ᵐ ω ∂μ, Finset.univ.sup' Finset.univ_nonempty
      (fun a => muHat R P U y a (T - 1) ω) ≤ μ[M | BanditHistory.history (Θ := Θ) (fun _ : Fin K => T - 1)] ω := by
    have h1 : ∀ᵐ ω ∂μ, ∀ a, μ[F a | BanditHistory.history (Θ := Θ) (fun _ : Fin K => T - 1)] ω = muHat R P U y a (T - 1) ω :=
      ae_all_iff.mpr hpost
    have h2 : ∀ᵐ ω ∂μ, ∀ a, μ[F a | BanditHistory.history (Θ := Θ) (fun _ : Fin K => T - 1)] ω ≤ μ[M | BanditHistory.history (Θ := Θ) (fun _ : Fin K => T - 1)] ω := ae_all_iff.mpr hmono
    filter_upwards [h1, h2] with ω h1 h2
    apply Finset.sup'_le
    intro a _
    rw [← h1 a]
    exact h2 a
  calc
    _ ≤ ∫ ω, μ[M | BanditHistory.history (Θ := Θ) (fun _ : Fin K => T - 1)] ω ∂μ :=
      integral_mono_ae (integrable_sup' _ _ μ _ (fun a _ => hhat a)) integrable_condExp hae
    _ = ∫ ω, M ω ∂μ := integral_condExp hHle
    _ = _ := by
      have hmeas : Measurable (fun ω : Outcome K Θ => fun a => (ω a).1) := by fun_prop
      rw [← prior_eq_map R P y, integral_map hmeas.aemeasurable]
      · have hm : Measurable (fun θ : Fin K → Θ =>
            Finset.univ.sup' Finset.univ_nonempty (fun a => mu R a (θ a))) := by
          have := Finset.measurable_sup' (Finset.univ_nonempty (α := Fin K))
            (f := fun a (θ : Fin K → Θ) => mu R a (θ a))
            (fun a _ => (mu_measurable R a).comp (measurable_pi_apply a))
          convert this using 1
          funext θ; simp only [Finset.sup'_apply]
        exact hm.aestronglyMeasurable

end IRSMono


set_option autoImplicit false
open MeasureTheory ProbabilityTheory InfoRelaxTS.Monotone

namespace IRSMono
variable {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- `𝔼_{y_a}[R_{a,1}] = μ̄_a(y_a)`. -/
lemma integral_pred (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) (a : Fin K) (ya : Y)
    (hi : Integrable (fun r : ℝ => r) (pred R P a ya)) :
    ∫ r, r ∂(pred R P a ya) = muBar R P a ya := by
  change Integrable id ((R a) ∘ₘ (P a ya)) at hi
  unfold pred muBar mu
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  exact ProbabilityTheory.Kernel.integral_comp hi

lemma count_zero {T : ℕ} (s : Fin T → Fin K) (a : Fin K) : count s 0 a = 0 := by
  simp [count]

lemma count_succ {T : ℕ} (s : Fin T → Fin K) (t : Fin T) (a : Fin K) :
    count s ((t : ℕ) + 1) a = count s t a + if s t = a then 1 else 0 := by
  classical
  unfold count
  have : (Finset.univ.filter fun t' : Fin T => (t' : ℕ) < (t : ℕ) + 1 ∧ s t' = a) =
      (Finset.univ.filter fun t' : Fin T => (t' : ℕ) < t ∧ s t' = a) ∪
        (Finset.univ.filter fun t' : Fin T => t' = t ∧ s t' = a) := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨Fin.ext h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨by omega, h2⟩
      · subst h1; exact ⟨by omega, h2⟩
  rw [this, Finset.card_union_of_disjoint]
  · congr 1
    by_cases h : s t = a
    · rw [if_pos h]
      rw [Finset.card_eq_one]
      exact ⟨t, by ext t'; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]; constructor
                   · exact fun h' => h'.1
                   · intro h'; subst h'; exact ⟨rfl, h⟩⟩
    · rw [if_neg h, Finset.card_eq_zero]
      ext t'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      intro h'; subst h'; exact h
  · rw [Finset.disjoint_left]
    intro t' h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h2.1] at h1
    exact lt_irrefl _ h1.1

lemma ybel_succ (U : Fin K → Y → ℝ → Y) (y : Fin K → Y) {T : ℕ} (s : Fin T → Fin K) (t : Fin T)
    (ω : Outcome K Θ) :
    ybel U y s ((t : ℕ) + 1) ω = Function.update (ybel U y s t ω) (s t)
      (U (s t) (ybel U y s t ω (s t)) ((ω (s t)).2 (count s t (s t)))) := by
  funext b
  unfold ybel
  rw [count_succ]
  by_cases h : s t = b
  · subst h
    simp [yseq]
  · rw [if_neg h, Function.update_of_ne (Ne.symm h)]
    simp

lemma ybel_zero (U : Fin K → Y → ℝ → Y) (y : Fin K → Y) {T : ℕ} (s : Fin T → Fin K)
    (ω : Outcome K Θ) : ybel U y s 0 ω = y := by
  funext b
  simp [ybel, count_zero, yseq]

/-- Each penalised payoff is at most the one-step decrease of `V̂` along the path. -/
lemma pay_le [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (Vhat : ℕ → (Fin K → Y) → ℝ) (hV : IsSupersolution R P U Vhat) (y : Fin K → Y)
    (T : ℕ) (s : Fin T → Fin K) (t : Fin T) (ω : Outcome K Θ) :
    pay R P U y Vhat T s t ω ≤
      Vhat (T - t) (ybel U y s t ω) - Vhat (T - ((t : ℕ) + 1)) (ybel U y s ((t : ℕ) + 1) ω) := by
  set y' := ybel U y s t ω
  set a := s t
  have hT : T - (t : ℕ) = (T - (t : ℕ) - 1) + 1 := by have := t.isLt; omega
  obtain ⟨hint, hle⟩ := hV.2 (T - (t : ℕ) - 1) y' a
  have hr := hM.integrable a (y' a)
  have hVi : Integrable (fun r => Vhat (T - (t : ℕ) - 1) (Function.update y' a (U a (y' a) r)))
      (pred R P a (y' a)) :=
    (hint.sub hr).congr (Filter.Eventually.of_forall fun r => by simp)
  have hsplit : ∫ r, (r + Vhat (T - (t : ℕ) - 1) (Function.update y' a (U a (y' a) r)))
      ∂(pred R P a (y' a)) = muBar R P a (y' a) +
        ∫ r, Vhat (T - (t : ℕ) - 1) (Function.update y' a (U a (y' a) r)) ∂(pred R P a (y' a)) := by
    rw [← integral_pred R P a (y' a) hr, ← integral_add hr hVi]
  rw [hsplit] at hle
  unfold pay
  have hmu : muHat R P U y a (count s t a) ω = muBar R P a (y' a) := rfl
  rw [← hT] at hle
  have h2 : T - ((t : ℕ) + 1) = T - (t : ℕ) - 1 := by omega
  rw [hmu, h2]
  linarith

/-- Lemma 2, pathwise part. -/
theorem innerMax_le [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (Vhat : ℕ → (Fin K → Y) → ℝ) (hV : IsSupersolution R P U Vhat) (T : ℕ) (y : Fin K → Y)
    (ω : Outcome K Θ) : innerMax R P U y Vhat T ω ≤ Vhat T y := by
  unfold innerMax
  apply Finset.sup'_le
  intro s _
  let f : ℕ → ℝ := fun t => Vhat (T - t) (ybel U y s t ω)
  calc
    (∑ t, pay R P U y Vhat T s t ω) ≤ ∑ t : Fin T, (f t - f ((t : ℕ) + 1)) :=
      Finset.sum_le_sum fun t _ => pay_le R P U hM Vhat hV y T s t ω
    _ = ∑ t ∈ Finset.range T, (f t - f (t + 1)) :=
      Fin.sum_univ_eq_sum_range (fun t => f t - f (t + 1)) T
    _ = f 0 - f T := Finset.sum_range_sub' f T
    _ = Vhat T y := by
      simp only [f, Nat.sub_zero, Nat.sub_self, ybel_zero, hV.1, sub_zero]

theorem lemma_2 [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (Vhat : ℕ → (Fin K → Y) → ℝ) (hV : IsSupersolution R P U Vhat) (T : ℕ) (y : Fin K → Y) :
    (∀ ω, innerMax R P U y Vhat T ω ≤ Vhat T y) ∧
      (Integrable (innerMax R P U y Vhat T) (I R P y) → penBound R P U Vhat T y ≤ Vhat T y) := by
  refine ⟨innerMax_le R P U hM Vhat hV T y, fun hint => ?_⟩
  letI := BanditLaw.outcome_probability R P y
  unfold penBound
  calc
    _ ≤ ∫ _ω, Vhat T y ∂(I R P y) :=
      integral_mono hint (integrable_const _) (innerMax_le R P U hM Vhat hV T y)
    _ = Vhat T y := by simp

end IRSMono


set_option autoImplicit false
open MeasureTheory ProbabilityTheory InfoRelaxTS.Monotone

namespace IRSMono
variable {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- The factor of the updated prior: the `b`-th coordinate of the product prior after arm `a`
observed `r`. -/
lemma upd_factor (P : Fin K → Kernel Y Θ) (y : Fin K → Y) (a : Fin K) (z : Y)
    (s : Fin K → Set Θ) (b : Fin K) :
    (P b (Function.update y a z b)) (s b) =
      Function.update (fun b => (P b (y b)) (s b)) a ((P a z) (s a)) b := by
  by_cases h : b = a
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- The product prior after updating arm `a` with the reward `r`, as a kernel in `r`. -/
noncomputable def updPrior (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (y : Fin K → Y) (a : Fin K) : Kernel ℝ (Fin K → Θ) where
  toFun r := prior P (Function.update y a (U a (y a) r))
  measurable' := by
    haveI : ∀ r : ℝ, IsProbabilityMeasure (prior P (Function.update y a (U a (y a) r))) :=
      fun r => by unfold prior; infer_instance
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm
      isPiSystem_pi
    rintro _ ⟨s, hs, rfl⟩
    have hv (r : ℝ) : prior P (Function.update y a (U a (y a) r)) (Set.univ.pi s) =
        ∏ b, Function.update (fun b => (P b (y b)) (s b)) a ((P a (U a (y a) r)) (s a)) b := by
      unfold prior
      rw [Measure.pi_pi]
      apply Finset.prod_congr rfl
      intro b _
      by_cases h : b = a
      · subst h; simp
      · simp [Function.update_of_ne h]
    simp_rw [hv]
    apply Finset.measurable_prod
    intro b _
    by_cases h : b = a
    · subst h
      simp only [Function.update_self]
      exact ((P b).measurable_coe (hs b (Set.mem_univ b))).comp
        ((hU b).comp measurable_prodMk_left)
    · simp only [Function.update_of_ne h]
      exact measurable_const

instance updPrior_markov (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hU : ∀ a, Measurable (Function.uncurry (U a)))
    (y : Fin K → Y) (a : Fin K) : IsMarkovKernel (updPrior P U hU y a) :=
  ⟨fun _ => by
    change IsProbabilityMeasure (Measure.pi _)
    infer_instance⟩

/-- Martingale property of the prior under the Bayes update (conjugacy):
`𝔼_{r ∼ pred}[𝒫(𝒰(y, a, r))] = 𝒫(y)`. -/
lemma updPrior_comp [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (y : Fin K → Y) (a : Fin K) :
    updPrior P U hM.meas y a ∘ₘ pred R P a (y a) = prior P y := by
  classical
  unfold prior
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.bind_apply (MeasurableSet.univ_pi hs) (Kernel.aemeasurable _)]
  have hv (r : ℝ) : updPrior P U hM.meas y a r (Set.univ.pi s) =
      (P a (U a (y a) r)) (s a) * ∏ b ∈ Finset.univ \ {a}, (P b (y b)) (s b) := by
    change prior P (Function.update y a (U a (y a) r)) (Set.univ.pi s) = _
    unfold prior
    rw [Measure.pi_pi]
    simp_rw [upd_factor P y a _ s]
    exact Finset.prod_update_of_mem (Finset.mem_univ a) (fun b => (P b (y b)) (s b))
      ((P a (U a (y a) r)) (s a))
  simp_rw [hv]
  have hmeas : Measurable (fun r => (P a (U a (y a) r)) (s a)) :=
    ((P a).measurable_coe (hs a)).comp ((hM.meas a).comp measurable_prodMk_left)
  rw [lintegral_mul_const _ hmeas]
  have hpost : ∫⁻ r, (P a (U a (y a) r)) (s a) ∂(pred R P a (y a)) = (P a (y a)) (s a) := by
    have hc := hM.conj a (y a)
    calc
      _ = ∫⁻ r, (posterior (R a) (P a (y a)) r) (s a) ∂(pred R P a (y a)) := by
        apply lintegral_congr_ae
        filter_upwards [hc] with r hr
        rw [hr]
      _ = (posterior (R a) (P a (y a)) ∘ₘ pred R P a (y a)) (s a) :=
        (Measure.bind_apply (hs a) (Kernel.aemeasurable _)).symm
      _ = _ := by
        unfold pred
        rw [posterior_comp_self]
  rw [hpost]
  have h2 := Finset.prod_update_of_mem (Finset.mem_univ a) (fun b => (P b (y b)) (s b))
    ((P a (y a)) (s a))
  simp only [Function.update_eq_self] at h2
  exact h2.symm

/-- `F(θ) = max_b μ_b(θ_b)`. -/
noncomputable def Fmax (R : Fin K → Kernel Θ ℝ) [NeZero K] (θ : Fin K → Θ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun b => mu R b (θ b))

lemma Fmax_measurable [NeZero K] (R : Fin K → Kernel Θ ℝ) : Measurable (Fmax R) := by
  have := Finset.measurable_sup' (Finset.univ_nonempty (α := Fin K))
    (f := fun b (θ : Fin K → Θ) => mu R b (θ b))
    (fun b _ => (mu_measurable R b).comp (measurable_pi_apply b))
  convert this using 1
  funext θ; simp only [Fmax, Finset.sup'_apply]

lemma mu_prior_integrable [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (y : Fin K → Y) (b : Fin K) :
    Integrable (fun θ : Fin K → Θ => mu R b (θ b)) (prior P y) := by
  have hi := mu_integrable R P U hM b (y b)
  have he : (prior P y).map (fun θ => θ b) = P b (y b) :=
    (measurePreserving_eval (fun b => P b (y b)) b).map_eq
  rw [← he] at hi
  exact hi.comp_measurable (measurable_pi_apply b)

lemma Fmax_integrable [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (y : Fin K → Y) :
    Integrable (Fmax R) (prior P y) :=
  integrable_sup' _ _ _ _ (fun b _ => mu_prior_integrable R P U hM y b)

lemma WTS_eq [NeZero K] (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ) (m : ℕ)
    (y : Fin K → Y) : WTS R P m y = (m : ℝ) * ∫ θ, Fmax R θ ∂(prior P y) := rfl

/-- The one-step martingale identity for `W^TS`. -/
lemma WTS_update [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (m : ℕ) (y : Fin K → Y)
    (a : Fin K) :
    Integrable (fun r => WTS R P m (Function.update y a (U a (y a) r))) (pred R P a (y a)) ∧
    ∫ r, WTS R P m (Function.update y a (U a (y a) r)) ∂(pred R P a (y a)) = WTS R P m y := by
  have hc := updPrior_comp R P U hM y a
  have hF : Integrable (Fmax R) (updPrior P U hM.meas y a ∘ₘ pred R P a (y a)) := by
    rw [hc]; exact Fmax_integrable R P U hM y
  rw [Measure.comp_eq_comp_const_apply] at hF
  have hi := hF.integral_comp
  have he := ProbabilityTheory.Kernel.integral_comp hF
  rw [← Measure.comp_eq_comp_const_apply, hc] at he
  simp only [Kernel.const_apply] at hi he
  constructor
  · exact hi.const_mul (m : ℝ)
  · simp_rw [WTS_eq]
    rw [integral_const_mul, he]
    rfl

theorem WTS_isSupersolution [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) :
    IsSupersolution R P U (fun m y' => WTS R P m y') := by
  refine ⟨fun y => by simp [WTS], fun T y a => ?_⟩
  obtain ⟨hi, he⟩ := WTS_update R P U hM T y a
  have hr := hM.integrable a (y a)
  refine ⟨hr.add hi, ?_⟩
  rw [integral_add hr hi, he, integral_pred R P a (y a) hr]
  have hmu : muBar R P a (y a) ≤ ∫ θ, Fmax R θ ∂(prior P y) := by
    have : muBar R P a (y a) = ∫ θ, mu R a (θ a) ∂(prior P y) := by
      have he : (prior P y).map (fun θ => θ a) = P a (y a) :=
        (measurePreserving_eval (fun b => P b (y b)) a).map_eq
      unfold muBar
      rw [← he, integral_map (measurable_pi_apply a).aemeasurable
        (mu_measurable R a).aestronglyMeasurable]
    rw [this]
    exact integral_mono (mu_prior_integrable R P U hM y a) (Fmax_integrable R P U hM y)
      (fun θ => Finset.le_sup' (fun b => mu R b (θ b)) (Finset.mem_univ a))
  simp only [WTS_eq, Nat.cast_add, Nat.cast_one]
  linarith

end IRSMono


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory InfoRelaxTS.Monotone

namespace IRSMono
variable {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- Posterior identity for a general test function of `θ_a`
(generalises `BanditFiniteHistory.enlarged_condMean`). -/
lemma enlarged_condF [StandardBorelSpace Θ] [Nonempty Θ] {K : ℕ}
    (R : Fin (K+1) → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin (K+1) → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin (K+1) → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (y : Fin (K+1) → Y) (a : Fin (K+1)) (n : ℕ) (F : Θ → ℝ) (hm : StronglyMeasurable F)
    (hi : Integrable F (P a (y a))) :
    (I R P y)[fun ω => F (ω a).1 |
      MeasurableSpace.comap (BanditFiniteHistory.enlarged (Θ := Θ) a n) inferInstance]
      =ᵐ[I R P y] fun ω => ∫ θ, F θ ∂(P a (yseq U y a n ω)) := by
  let : IsProbabilityMeasure (I R P y) := BanditLaw.outcome_probability R P y
  have hi' : Integrable (fun ω : Outcome (K+1) Θ => F (ω a).1) (I R P y) := by
    rw [← BanditLaw.parameter_marginal R P y a] at hi
    exact hi.comp_measurable (by fun_prop)
  have hcd := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (BanditFiniteHistory.enlarged_measurable a n)
    (by fun_prop : Measurable (fun ω : Outcome (K+1) Θ => (ω a).1))
    (BanditFiniteHistory.enlarged_joint R P U hM y a n)
  have hp := ae_of_ae_map (BanditFiniteHistory.enlarged_measurable (Θ := Θ) a n).aemeasurable hcd
  have hc := condExp_ae_eq_integral_condDistrib (μ := I R P y)
    (BanditFiniteHistory.enlarged_measurable a n)
    ((measurable_pi_apply a).fst.aemeasurable) hm hi'
  apply hc.trans
  filter_upwards [hp] with ω hω
  rw [hω]
  change (∫ θ, F θ ∂P a (BanditFiniteHistory.belief (U a) (y a) n (fun i => (ω a).2 i))) = _
  rw [BanditFiniteHistory.belief_yseq]

lemma post_integrable [StandardBorelSpace Θ] [Nonempty Θ] {K : ℕ}
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (y : Fin K → Y) (a : Fin K) (n : ℕ) (F : Θ → ℝ) (hm : StronglyMeasurable F)
    (hi : Integrable F (P a (y a))) :
    Integrable (fun ω => ∫ θ, F θ ∂(P a (yseq U y a n ω))) (I R P y) := by
  cases K with
  | zero => exact Fin.elim0 a
  | succ K => exact integrable_condExp.congr (enlarged_condF R P U hM y a n F hm hi)

variable {K : ℕ}

/-- The product prior as a kernel of the belief vector. -/
noncomputable def priorK (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] :
    Kernel (Fin K → Y) (Fin K → Θ) where
  toFun y' := prior P y'
  measurable' := by
    haveI : ∀ y' : Fin K → Y, IsProbabilityMeasure (prior P y') :=
      fun y' => by unfold prior; infer_instance
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm
      isPiSystem_pi
    rintro _ ⟨s, hs, rfl⟩
    have hv (y' : Fin K → Y) : prior P y' (Set.univ.pi s) = ∏ b, (P b (y' b)) (s b) := by
      unfold prior; rw [Measure.pi_pi]
    simp_rw [hv]
    exact Finset.measurable_prod _ fun b _ =>
      ((P b).measurable_coe (hs b (Set.mem_univ b))).comp (measurable_pi_apply b)

lemma WTS_measurable [NeZero K] (R : Fin K → Kernel Θ ℝ)
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)] (m : ℕ) :
    Measurable (fun y' => WTS R P m y') := by
  have h : Measurable (fun y' => ∫ θ, Fmax R θ ∂(priorK P y')) :=
    ((Fmax_measurable R).stronglyMeasurable.integral_kernel (κ := priorK P)).measurable
  exact h.const_mul _

lemma abs_sup'_le [NeZero K] (f : Fin K → ℝ) :
    |Finset.univ.sup' Finset.univ_nonempty f| ≤ ∑ b, |f b| := by
  rw [abs_le]
  constructor
  · have h1 : f 0 ≤ Finset.univ.sup' Finset.univ_nonempty f :=
      Finset.le_sup' f (Finset.mem_univ 0)
    have h2 : |f 0| ≤ ∑ b, |f b| :=
      Finset.single_le_sum (f := fun b => |f b|) (fun b _ => abs_nonneg _) (Finset.mem_univ 0)
    have h3 := neg_abs_le (f 0)
    linarith
  · apply Finset.sup'_le
    intro b _
    exact (le_abs_self _).trans
      (Finset.single_le_sum (f := fun b => |f b|) (fun b _ => abs_nonneg _) (Finset.mem_univ b))

lemma abs_WTS_le [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (m : ℕ) (y' : Fin K → Y) :
    |WTS R P m y'| ≤ (m : ℝ) * ∑ b, ∫ θ, |mu R b θ| ∂(P b (y' b)) := by
  rw [WTS_eq, abs_mul, Nat.abs_cast]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  have hb : ∀ b, Integrable (fun θ : Fin K → Θ => |mu R b (θ b)|) (prior P y') :=
    fun b => (mu_prior_integrable R P U hM y' b).abs
  calc
    |∫ θ, Fmax R θ ∂(prior P y')| ≤ ∫ θ, |Fmax R θ| ∂(prior P y') :=
      abs_integral_le_integral_abs
    _ ≤ ∫ θ, ∑ b, |mu R b (θ b)| ∂(prior P y') :=
      integral_mono (Fmax_integrable R P U hM y').abs (integrable_finsetSum _ fun b _ => hb b)
        (fun θ => abs_sup'_le _)
    _ = ∑ b, ∫ θ, |mu R b (θ b)| ∂(prior P y') := integral_finsetSum _ fun b _ => hb b
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      have he : (prior P y').map (fun θ => θ b) = P b (y' b) :=
        (measurePreserving_eval (fun b => P b (y' b)) b).map_eq
      rw [← he, integral_map (measurable_pi_apply b).aemeasurable
        ((mu_measurable R b).abs).aestronglyMeasurable]

lemma WTS_path_integrable [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (y : Fin K → Y) (m : ℕ)
    (N : Fin K → ℕ) :
    Integrable (fun ω : Outcome K Θ => WTS R P m (fun b => yseq U y b (N b) ω)) (I R P y) := by
  have hmeas : Measurable (fun ω : Outcome K Θ => fun b => yseq U y b (N b) ω) := by
    apply measurable_pi_lambda
    intro b
    exact (BanditHistory.yseq_measurable U hM.meas y N b (N b) le_rfl).mono
      (BanditHistory.history_le N) le_rfl
  have hbound : Integrable (fun ω : Outcome K Θ =>
      (m : ℝ) * ∑ b, ∫ θ, |mu R b θ| ∂(P b (yseq U y b (N b) ω))) (I R P y) := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro b _
    exact post_integrable R P U hM y b (N b) (fun θ => |mu R b θ|)
      (mu_measurable R b).abs.stronglyMeasurable (mu_integrable R P U hM b (y b)).abs
  refine Integrable.mono' hbound ((WTS_measurable R P m).comp hmeas).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]
    exact abs_WTS_le R P U hM m _

/-- The payoff with the `W^TS` penalty, after the martingale identity. -/
lemma pay_WTS_eq [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (y : Fin K → Y)
    (T : ℕ) (s : Fin T → Fin K) (t : Fin T) :
    pay R P U y (fun m y' => WTS R P m y') T s t = fun ω =>
      muHat R P U y (s t) (count s t (s t)) ω
        - WTS R P (T - (t : ℕ) - 1) (ybel U y s ((t : ℕ) + 1) ω)
        + WTS R P (T - (t : ℕ) - 1) (ybel U y s t ω) := by
  funext ω
  unfold pay
  rw [(WTS_update R P U hM (T - (t : ℕ) - 1) (ybel U y s t ω) (s t)).2]

theorem innerMax_WTS_integrable [NeZero K] [StandardBorelSpace Θ] [Nonempty Θ]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) (T : ℕ) (y : Fin K → Y) :
    Integrable (innerMax R P U y (fun m y' => WTS R P m y') T) (I R P y) := by
  have hpay : ∀ (s : Fin T → Fin K) (t : Fin T),
      Integrable (pay R P U y (fun m y' => WTS R P m y') T s t) (I R P y) := by
    intro s t
    rw [pay_WTS_eq R P U hM y T s t]
    refine Integrable.add (Integrable.sub ?_ ?_) ?_
    · exact integrable_condExp.congr
        (BanditFiniteHistory.posterior_history R P U hM y (s t) (fun _ => count s t (s t)))
    · exact WTS_path_integrable R P U hM y _ (fun b => count s ((t : ℕ) + 1) b)
    · exact WTS_path_integrable R P U hM y _ (fun b => count s t b)
  have h := integrable_sup' (Finset.univ : Finset (Fin T → Fin K)) Finset.univ_nonempty (I R P y)
    (fun s ω => ∑ t, pay R P U y (fun m y' => WTS R P m y') T s t ω)
    (fun s _ => by
      have := integrable_finsetSum (μ := I R P y) Finset.univ (fun t _ => hpay s t)
      convert this using 1)
  exact h

end IRSMono


open MeasureTheory ProbabilityTheory
theorem solution {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : InfoRelaxTS.Monotone.StandingAssumptions R P U)
    (T : ℕ) (y : Fin K → Y) :
    InfoRelaxTS.Monotone.WFH R P U T y ≤ InfoRelaxTS.Monotone.WTS R P T y ∧
      InfoRelaxTS.Monotone.WVZ R P U T y ≤ InfoRelaxTS.Monotone.WFH R P U T y ∧
      InfoRelaxTS.Monotone.WVEMax R P U T y ≤ InfoRelaxTS.Monotone.WTS R P T y := by
  refine ⟨InfoRelaxTS.Monotone.WTS_ge_WFH R P U hM T y, ?_, ?_⟩
  · obtain ⟨hstep, hFH, hVZ, htrans⟩ := InfoRelaxTS.Monotone.Ukn_interpolation R P U hM T y
    have hn : ∀ (k : Fin K) (n : ℕ), n ≤ T →
        InfoRelaxTS.Monotone.Ukn R P U k n T y ≤ InfoRelaxTS.Monotone.Ukn R P U k 0 T y := by
      intro k n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro h; exact (hstep k n (by omega)).trans (ih (by omega))
    have hk : ∀ (j : ℕ) (hj : j < K),
        InfoRelaxTS.Monotone.Ukn R P U ⟨j, hj⟩ T T y ≤ InfoRelaxTS.Monotone.Ukn R P U 0 0 T y := by
      intro j
      induction j with
      | zero =>
        intro hj
        have h0 : (⟨0, hj⟩ : Fin K) = 0 := Fin.ext (by simp)
        rw [h0]
        exact hn 0 T le_rfl
      | succ j ih =>
        intro hj
        calc
          _ ≤ InfoRelaxTS.Monotone.Ukn R P U ⟨j + 1, hj⟩ 0 T y := hn _ T le_rfl
          _ = InfoRelaxTS.Monotone.Ukn R P U ⟨j, by omega⟩ T T y := htrans ⟨j, by omega⟩ hj
          _ ≤ _ := ih (by omega)
    rw [hVZ, hFH]
    exact hk _ _
  · exact (InfoRelaxTS.Monotone.lemma_2 R P U hM _
      (InfoRelaxTS.Monotone.WTS_isSupersolution R P U hM) T y).2
      (IRSMono.innerMax_WTS_integrable R P U hM T y)
