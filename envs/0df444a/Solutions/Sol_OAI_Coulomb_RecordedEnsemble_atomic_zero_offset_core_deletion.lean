-- Prove2me | solution 1 for OAI.Coulomb.RecordedEnsemble.atomic_zero_offset_core_deletion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:20:35.804231+00:00
-- url     : https://prove2.me/submissions/7250fddf-6d4b-41af-bca6-bc054be04275

import Mathlib
import Definitions.Def_OAIQ062C008

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ColoredObservable
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

lemma tensorCut_selected_square {n : ℕ} (χ : Fin 2 → Space → ℝ)
    (hp : ∀ y, ∑ l, χ l y^2=1) (i : Fin n) (x : Configuration n) :
    (∑ p : Fin n → Fin 2, if p i=0 then (tensorCut χ p x)^2 else 0)=χ 0 (position x i)^2 := by
  have he (p : Fin n → Fin 2) :
      (if p i=0 then (tensorCut χ p x)^2 else 0)=
        (if p i=0 then χ 0 (position x i)^2 else 0)*
          ∏ j∈Finset.univ.erase i, χ (p j) (position x j)^2 := by
    unfold tensorCut
    rw [←Finset.prod_pow,←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  simp_rw [he]
  rw [sum_slot_product (fun j l => χ l (position x j)^2)
    (fun l => if l=0 then χ 0 (position x i)^2 else 0) i (fun j => hp _)]
  simp

lemma coloredObservable_measurable {n : ℕ} {F : Fin n → Configuration n → ℝ}
    (hF : ∀ i, Measurable (F i)) (p : Fin n → Fin 2) : Measurable (coloredObservable F p) := by
  apply Finset.measurable_fun_sum
  intro i hi
  by_cases h : p i=0 <;> simp only [h,ite_true,ite_false]
  · exact hF i
  · exact measurable_const

lemma coloredObservable_abs_le {n : ℕ} {F : Fin n → Configuration n → ℝ} {B : ℝ}
    (hB : 0≤B) (hb : ∀ i x, |F i x|≤B) (p : Fin n → Fin 2) (x : Configuration n) :
    |coloredObservable F p x|≤(n:ℝ)*B := by
  apply (Finset.abs_sum_le_sum_abs ..).trans
  have H : (∑ i : Fin n, |if p i=0 then F i x else 0|) ≤ ∑ _i : Fin n, B := by
    apply Finset.sum_le_sum
    intro i hi
    split_ifs
    · exact hb i x
    · exact (abs_zero).le.trans hB
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H

lemma tensorCut_colored_sum {n : ℕ} (χ : Fin 2 → Space → ℝ)
    (hp : ∀ y, ∑ l, χ l y^2=1) (F : Fin n → Configuration n → ℝ) (x : Configuration n) :
    (∑ p : Fin n → Fin 2, coloredObservable F p x*(tensorCut χ p x)^2)=
      ∑ i, χ 0 (position x i)^2*F i x := by
  simp only [coloredObservable,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have he (p : Fin n → Fin 2) : (if p i=0 then F i x else 0)*(tensorCut χ p x)^2=
      (if p i=0 then (tensorCut χ p x)^2 else 0)*F i x := by
    split_ifs <;> ring
  simp_rw [he]
  rw [←Finset.sum_mul,tensorCut_selected_square χ hp]

lemma potentialForm_colored_labelCut {n : ℕ} (u : H1Vector n)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ ∞ (χ l))
    (hp : ∀ y, ∑ l, χ l y^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b y, |fderiv ℝ (χ l) y (EuclideanSpace.single b 1)|≤D)
    (F : Fin n → Configuration n → ℝ) (hF : ∀ i, Measurable (F i))
    {B : ℝ} (hB : 0≤B) (hb : ∀ i x, |F i x|≤B) :
    (∑ p : Fin n → Fin 2, potentialForm (coloredObservable F p) (u.labelCut χ hχ hp D hD hd p))=
      potentialForm (fun x => ∑ i, χ 0 (position x i)^2*F i x) u := by
  unfold potentialForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [←integral_finsetSum _ (fun p _ => boundedObservable_integrable
    (u.labelCut χ hχ hp D hD hd p) (coloredObservable F p)
    (coloredObservable_measurable hF p) (coloredObservable_abs_le hB hb p) s)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change (∑ p, coloredObservable F p x*‖(tensorCut χ p x : ℂ)*u.value s x‖^2)=_
  simp only [norm_real_mul_sq,←mul_assoc,←Finset.sum_mul,tensorCut_colored_sum χ hp]

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_EnsembleCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma slice_ensemble_count_cauchy {P : Type*} [Fintype P]
    (m k : P → ℕ) (u : (p : P) → H1Vector (m p+k p))
    (F : (p : P) → Spins (m p) → Configuration (m p) → ℝ)
    (hF : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*F p s x))
    (hF2 : ∀ p s, Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2)) :
    (∑ p, (m p:ℝ)*sliceExpectation (u p) (F p))^2 ≤
      (∑ p, (m p:ℝ)^2*mass (u p))*(∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2)) := by
  let N : ℝ := ∑ p, (m p:ℝ)^2*mass (u p)
  let C : ℝ := ∑ p, (m p:ℝ)*sliceExpectation (u p) (F p)
  let H : ℝ := ∑ p, sliceExpectation (u p) (fun s x => (F p s x)^2)
  have hn (t : ℝ) : 0 ≤ N*(t*t)+(-2*C)*t+H := by
    have hp : 0 ≤ ∑ p, ∑ s : Spins (m p), ∫ x,
        mass ((u p).coreSlice s x)*(F p s x-t*(m p:ℝ))^2 :=
      Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun s _ =>
        integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
    have he (p) (s : Spins (m p)) :
        (∫ x, mass ((u p).coreSlice s x)*(F p s x-t*(m p:ℝ))^2) =
        (∫ x, mass ((u p).coreSlice s x)*(F p s x)^2)-
          (2*t*(m p:ℝ))*(∫ x, mass ((u p).coreSlice s x)*F p s x)+
            t^2*(m p:ℝ)^2*(∫ x, mass ((u p).coreSlice s x)) := by
      have hi : Integrable (fun x => mass ((u p).coreSlice s x)*(F p s x)^2-
          (2*t*(m p:ℝ))*(mass ((u p).coreSlice s x)*F p s x)) :=
        (hF2 p s).sub ((hF p s).const_mul (2*t*(m p:ℝ)))
      calc
        _ = ∫ x, (mass ((u p).coreSlice s x)*(F p s x)^2-
            (2*t*(m p:ℝ))*(mass ((u p).coreSlice s x)*F p s x))+
            (t^2*(m p:ℝ)^2)*mass ((u p).coreSlice s x) :=
          integral_congr_ae (Eventually.of_forall (fun x => by ring))
        _ = _ := by
          rw [integral_add hi ((mass_coreSlice_integrable (u p) s).const_mul _),
            integral_sub (hF2 p s) ((hF p s).const_mul _),integral_const_mul,integral_const_mul]
    simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,integral_mass_coreSlice] at hp
    have hc : (∑ p, 2*t*(m p:ℝ)*(∑ s : Spins (m p), ∫ x, mass ((u p).coreSlice s x)*F p s x))=2*t*C := by
      simp only [C,sliceExpectation,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring_nf
    have hN : (∑ p, t^2*(m p:ℝ)^2*mass (u p))=t^2*N := by
      simp only [N,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [hc,hN] at hp
    change 0 ≤ H-2*t*C+t^2*N at hp
    nlinarith
  have h := discrim_le_zero hn
  unfold discrim at h
  change C^2 ≤ N*H
  nlinarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_AnnularHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma atomicIMS_nonneg {n : ℕ} (ψ : H1Vector n) (y : Space) : 0 ≤ atomicIMS ψ y :=
  mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (expectedPopulation_nonneg _ _)

lemma exists_annular_history_targets : ∃ j : ℕ, 1 ≤ j ∧
    ∀ {u : ℝ}, 0<u → ∃ y : Fin j → Space,
      (∀ i, y i≠0) ∧
      (∀ i, AtomicScaleWindow (u/100000) (4^j) (y i)) ∧
      {x : Space | u/2<‖x‖ ∧ ‖x‖<4*u} ⊆ atomicPatchRegion y := by
  obtain ⟨t,ht,hcover⟩ := exists_atomic_annular_mesh (α:=(1/2:ℝ)) (β:=4) (by norm_num)
  let M := Fintype.card {z : Space // z∈t}
  let e := Fintype.equivFin {z : Space // z∈t}
  let v : Space := EuclideanSpace.single 0 1
  have hv : ‖v‖=1 := by simp [v]
  refine ⟨M+1,by omega,?_⟩
  intro u hu
  let y : Fin (M+1) → Space := Fin.snoc (fun i => u • (e.symm i).val) (u • v)
  have hybounds (i : Fin (M+1)) : u/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ 4*u := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [y,Fin.snoc_last,norm_smul,Real.norm_eq_abs,abs_of_pos hu,hv,mul_one]
      constructor <;> linarith
    · simp only [y,Fin.snoc_castSucc,norm_smul,Real.norm_eq_abs,abs_of_pos hu]
      have H := ht (e.symm i).val (e.symm i).property
      constructor <;> nlinarith [H.1,H.2]
  have hq : (4:ℝ) ≤ 4^(M+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ)≤4 by norm_num) (show 1≤M+1 by omega)
  refine ⟨y,(fun i => norm_pos_iff.mp (by linarith [(hybounds i).1])),?_,?_⟩
  · intro i
    apply AtomicScaleWindow.enlarge (q:=4) _ (by positivity) hq
    dsimp only [AtomicScaleWindow,atomicCellScale]
    constructor <;> linarith [(hybounds i).1,(hybounds i).2]
  · intro x hx
    have hn : ‖u⁻¹ • x‖=‖x‖/u := by simp [norm_smul,abs_of_pos hu,div_eq_mul_inv,mul_comm]
    have hlow : (1/2:ℝ) ≤ ‖u⁻¹ • x‖ := by rw [hn]; apply (le_div_iff₀ hu).mpr; linarith [hx.1]
    have hhigh : ‖u⁻¹ • x‖ ≤ 4 := by rw [hn]; exact (div_le_iff₀ hu).mpr hx.2.le
    obtain ⟨z,hz,hxz⟩ := hcover (u⁻¹ • x) hlow hhigh
    apply Set.mem_iUnion.mpr
    refine ⟨(e ⟨z,hz⟩).castSucc,?_⟩
    simp only [y,Fin.snoc_castSucc,Equiv.symm_apply_apply,Metric.mem_closedBall,dist_eq_norm]
    rw [atomicCellScale_smul hu.le]
    have hid : x-u • z=u • (u⁻¹ • x-z) := by simp [smul_sub,smul_smul,hu.ne']
    rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos hu]
    have H := mul_le_mul_of_nonneg_left hxz.le hu.le
    nlinarith [atomicCellScale_nonneg z]

lemma annularIMSCost_reserve {δ u C : ℝ} (hδ : 0≤δ) (hu : 0<u) (hC : 0≤C) :
    C*screenMass δ u/u^2 ≤ (C*(100000:ℝ)^3)*screenEnergy δ (u/100000) := by
  have ha : 0<u/100000 := by positivity
  have H : screenMass δ u ≤ (100000:ℝ)^3*screenMass δ (u/100000) :=
    screenMass_comparable hδ ha (by norm_num) (by linarith) (by linarith)
  have hm := screenMass_pos δ (u/100000)
  have hs := screenMass_scale δ ha
  have hnum : screenMass δ u ≤ (100000:ℝ)^3*(u*screenMass δ (u/100000)^2)*100000 := by
    have H1 := mul_le_mul_of_nonneg_right hs hm.le
    nlinarith
  rw [div_le_iff₀ (sq_pos_of_pos hu)]
  unfold screenEnergy
  have he : (C*(100000:ℝ)^3)*(screenMass δ (u/100000)^2/(u/100000))*u^2 =
      C*((100000:ℝ)^3*(u*screenMass δ (u/100000)^2)*100000) := by field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hnum hC

theorem annular_ensemble_positive_field : ∀ C₀ : ℝ, 0≤C₀ → ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ {u : ℝ}, 0<u → ∀ T : RecordedEnsemble n,
      T.Conserves ψ → T.CoreFermionic →
      T.OutSupported {x : Space | u/2<‖x‖ ∧ ‖x‖<4*u} →
      T.totalMass=mass ψ → T.totalForm S≤form S ψ+C₀*screenMass δ u/u^2 →
      ∀ y : Space, u/2≤‖y‖ → ‖y‖≤4*u →
      Real.sqrt (T.rawSquare S y (atomicCellScale y)) ≤ C*screenMass δ u/u := by
  intro C₀ hC₀
  obtain ⟨j,hj,Htargets⟩ := exists_annular_history_targets
  let P : ℝ := max 1 (max atomicCountConstant (C₀*(100000:ℝ)^3))
  have hP : 1≤P := le_max_left _ _
  have hPcount : atomicCountConstant≤P := (le_max_left _ _).trans (le_max_right _ _)
  have hPcost : C₀*(100000:ℝ)^3≤P := (le_max_right _ _).trans (le_max_right _ _)
  have hCrec : 0 ≤ atomicBudgetRecursionC := le_trans (by norm_num) atomicBudgetRecursionC_ge_four
  let C : ℝ := 2*atomicBudgetRecursionC^(j+2)*Real.sqrt P*(100000:ℝ)^4
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ u hu T hlaw hf hsupp hmass hform y hylo hyhi
  obtain ⟨ys,hys0,hys,hcover⟩ := Htargets hu
  let B := C₀*screenMass δ u/u^2
  let U : AtomicBudgetHistory S ψ B j := {
    ensemble := T
    target := ys
    nonzero := hys0
    law := hlaw
    fermionic := hf
    support := fun p => (hsupp p).mono_space hcover
    mass_eq := hmass
    energy := hform.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => atomicIMS_nonneg ψ (ys i)))) }
  have hB : B≤P*screenEnergy δ (u/100000) :=
    (annularIMSCost_reserve hδ hu hC₀).trans (mul_le_mul_of_nonneg_right hPcost (screenEnergy_pos δ (by positivity)).le)
  have hc (z : Space) (hz : z≠0) : localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2 := by
    exact (screenCountParameter_controls ψ hm δ hz).trans (mul_le_mul_of_nonneg_right
      ((screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ).trans hPcount) (sq_nonneg _))
  have hy : AtomicScaleWindow (u/100000) (4^j) y := by
    apply AtomicScaleWindow.enlarge (q:=4) _ (by positivity)
      (by simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ)≤4 by norm_num) hj)
    dsimp only [AtomicScaleWindow,atomicCellScale]
    constructor <;> linarith
  have H := U.positive_field S hatom ψ hm hE hstate hB hδ hP (by positivity) hc hys y hy
  have Hm : screenMass δ (u/100000) ≤ (100000:ℝ)^3*screenMass δ u :=
    screenMass_comparable hδ hu (by norm_num) le_rfl (by linarith)
  have Hu : screenFieldUnit δ P (u/100000) ≤ Real.sqrt P*(100000:ℝ)^4*screenMass δ u/u := by
    unfold screenFieldUnit
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Hm (Real.sqrt_nonneg _)) (by positivity)).trans_eq (by ring)
  exact H.trans ((mul_le_mul_of_nonneg_left Hu (by positivity)).trans_eq (by dsimp [C]; ring))

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ShellIMS
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

lemma measurableSet_imsShell (y : Space) (r : ℝ) : MeasurableSet (imsShell y r) := by
  exact ((isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
    (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)).measurableSet

lemma radialCut_fderiv_zero_inner (y : Space) {r : ℝ} (hr : 0 < r)
    (l : Fin 2) (x : Space) (hx : ‖x-y‖ < r) :
    fderiv ℝ (radialCut y r l) x = 0 := by
  have he : radialCut y r l =ᶠ[𝓝 x] (fun _ => if l=0 then (1:ℝ) else 0) := by
    have hh : ∀ᶠ z in 𝓝 x, ‖z-y‖ < r :=
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hx
    filter_upwards [hh] with z hz
    have hs : ‖r⁻¹ • (z-y)‖ ≤ 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_le_one₀ hr).2 hz.le
    simp only [radialCut,cutAngle,cutSeed_one _ hs,mul_one,
      Real.sin_pi_div_two,Real.cos_pi_div_two]
  rw [he.fderiv_eq]
  simp

lemma radialCut_gradient_shell_bound (y : Space) {r : ℝ} (hr : 0 < r)
    (b : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (radialCut y r l) x (EuclideanSpace.single b 1))^2) ≤
      (2*(radialCutCoefficient/r)^2) * (imsShell y r).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x ∈ imsShell y r
  · rw [indicator_of_mem hx,mul_one]
    calc
      _ ≤ ∑ _l : Fin 2, (radialCutCoefficient/r)^2 := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (div_nonneg radialCutCoefficient_pos.le hr.le)).2
            (radialCut_derivative_bound y hr l b x)
      _ = _ := by simp
  · rw [indicator_of_notMem hx,mul_zero]
    have hd : ∀ l : Fin 2, fderiv ℝ (radialCut y r l) x = 0 := by
      have hnot : ¬ (r ≤ ‖x-y‖ ∧ ‖x-y‖ ≤ 2*r) := hx
      by_cases hinner : ‖x-y‖ < r
      · exact fun l => radialCut_fderiv_zero_inner y hr l x hinner
      · have houter : 2*r < ‖x-y‖ := lt_of_not_ge (fun h => hnot ⟨le_of_not_gt hinner,h⟩)
        exact fun l => radialCut_fderiv_zero y hr l x houter
    simp only [hd,zero_apply,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,
      zero_pow,Finset.sum_const_zero,le_refl]

theorem form_radial_labelCut_shell {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (y : Space) {r : ℝ} (hr : 0 < r) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (radialCut y r) (radialCut_smooth y r)
      (radialCut_partition y r) (radialCutCoefficient/r) (div_nonneg radialCutCoefficient_pos.le hr.le)
      (radialCut_derivative_bound y hr) p)) ≤
      form S ψ+3*(radialCutCoefficient/r)^2*expectedPopulation ψ (imsShell y r) := by
  rw [form_labelCut]
  apply add_le_add_right
  let c : ℝ := 2*(radialCutCoefficient/r)^2
  have hi s i := population_integrable ψ (imsShell y r) (measurableSet_imsShell y r) s i
  have H (s : Spins n) (a : Fin n × Fin 3) :
      (∫ x, (∑ l, (fderiv ℝ (radialCut y r l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2) ≤
      c*(∫ x, (imsShell y r).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · filter_upwards [] with x
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
    · exact (hi s a.1).const_mul c
    · filter_upwards [] with x
      simpa only [c,mul_assoc] using mul_le_mul_of_nonneg_right
        (radialCut_gradient_shell_bound y hr a.2 (position x a.1)) (sq_nonneg ‖ψ.value s x‖)
  calc
    _ ≤ (1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, c*(∫ x,
          (imsShell y r).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun a _ => H s a))) (by norm_num)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ← Finset.mul_sum,expectedPopulation,c]
      ring

end Coulomb

end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_RawRMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma rawRMS_nonneg {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ) :
    0 ≤ rawRMS ψ f := Real.sqrt_nonneg _

lemma potentialForm_nonneg {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ potentialForm f ψ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun x => mul_nonneg (hf x) (sq_nonneg _)))

lemma rawRMS_sq {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ) :
    rawRMS ψ f ^ 2 = potentialForm (fun x => (f x)^2) ψ :=
  Real.sq_sqrt (potentialForm_nonneg ψ _ (fun _ => sq_nonneg _))

lemma potentialForm_bounded_cauchy {n : ℕ} (ψ : H1Vector n)
    (f g : Configuration n → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) :
    (potentialForm (fun x => f x*g x) ψ)^2 ≤
      potentialForm (fun x => (f x)^2) ψ * potentialForm (fun x => (g x)^2) ψ := by
  have hff s := boundedObservable_integrable ψ (fun x => (f x)^2) (hf.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2) s
  have hgg s := boundedObservable_integrable ψ (fun x => (g x)^2) (hg.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hC x) 2) s
  have hfg s := boundedObservable_integrable ψ (fun x => f x*g x) (hf.mul hg)
    (fun x => by rw [abs_mul]; exact mul_le_mul (hB x) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hB x))) s
  let A := potentialForm (fun x => (f x)^2) ψ
  let Q := potentialForm (fun x => (g x)^2) ψ
  let D := potentialForm (fun x => f x*g x) ψ
  have hn (t : ℝ) : 0 ≤ A*(t*t)+(-2*D)*t+Q := by
    have hp := potentialForm_nonneg ψ (fun x => (t*f x-g x)^2) (fun _ => sq_nonneg _)
    have he s : (∫ x, (t*f x-g x)^2*‖ψ.value s x‖^2) =
        t^2*(∫ x, (f x)^2*‖ψ.value s x‖^2)-
        (2*t)*(∫ x, (f x*g x)*‖ψ.value s x‖^2)+
        (∫ x, (g x)^2*‖ψ.value s x‖^2) := by
      have hi : Integrable (fun x => t^2*((f x)^2*‖ψ.value s x‖^2)-(2*t)*((f x*g x)*‖ψ.value s x‖^2)) :=
        ((hff s).const_mul (t^2)).sub ((hfg s).const_mul (2*t))
      calc
        _ = ∫ x, (t^2*((f x)^2*‖ψ.value s x‖^2)-(2*t)*((f x*g x)*‖ψ.value s x‖^2))+
            (g x)^2*‖ψ.value s x‖^2 := integral_congr_ae (Eventually.of_forall (fun _ => by ring))
        _ = _ := by
          rw [integral_add hi (hgg s),
            integral_sub ((hff s).const_mul _) ((hfg s).const_mul _),integral_const_mul,integral_const_mul]
    simp only [potentialForm,he,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hp
    change 0 ≤ t^2*A-2*t*D+Q at hp
    nlinarith
  have H := discrim_le_zero hn
  unfold discrim at H
  change D^2 ≤ A*Q
  nlinarith

lemma rawRMS_add {n : ℕ} (ψ : H1Vector n)
    (f g : Configuration n → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C) :
    rawRMS ψ (fun x => f x+g x) ≤ rawRMS ψ f+rawRMS ψ g := by
  have hff s := boundedObservable_integrable ψ (fun x => (f x)^2) (hf.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2) s
  have hgg s := boundedObservable_integrable ψ (fun x => (g x)^2) (hg.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hC x) 2) s
  have hfg s := boundedObservable_integrable ψ (fun x => f x*g x) (hf.mul hg)
    (fun x => by rw [abs_mul]; exact mul_le_mul (hB x) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hB x))) s
  have he : rawRMS ψ (fun x => f x+g x)^2 =
      rawRMS ψ f^2+2*potentialForm (fun x => f x*g x) ψ+rawRMS ψ g^2 := by
    simp only [rawRMS_sq,potentialForm]
    rw [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    have hi : Integrable (fun x => (f x)^2*‖ψ.value s x‖^2+2*((f x*g x)*‖ψ.value s x‖^2)) :=
      (hff s).add ((hfg s).const_mul 2)
    calc
      _ = ∫ x, ((f x)^2*‖ψ.value s x‖^2+2*((f x*g x)*‖ψ.value s x‖^2))+
          (g x)^2*‖ψ.value s x‖^2 := integral_congr_ae (Eventually.of_forall (fun _ => by ring))
      _ = _ := by rw [integral_add hi (hgg s),
        integral_add (hff s) ((hfg s).const_mul _),integral_const_mul]
  have hcs := potentialForm_bounded_cauchy ψ f g hf hg hB hC
  rw [←rawRMS_sq,←rawRMS_sq] at hcs
  have H : potentialForm (fun x => f x*g x) ψ ≤ rawRMS ψ f*rawRMS ψ g := by
    have hh : |potentialForm (fun x => f x*g x) ψ| ≤ rawRMS ψ f*rawRMS ψ g :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (rawRMS_nonneg ψ f) (rawRMS_nonneg ψ g))).mp
        (by simpa only [sq_abs,mul_pow] using hcs)
    exact (le_abs_self _).trans hh
  nlinarith [rawRMS_nonneg ψ f,rawRMS_nonneg ψ g,rawRMS_nonneg ψ (fun x => f x+g x)]

lemma rawRMS_const_mul {n : ℕ} (ψ : H1Vector n) (f : Configuration n → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : rawRMS ψ (fun x => c*f x)=c*rawRMS ψ f := by
  unfold rawRMS potentialForm
  have he : (∑ s : Spins n, ∫ x, (c*f x)^2*‖ψ.value s x‖^2)=
      c^2*(∑ s : Spins n, ∫ x, (f x)^2*‖ψ.value s x‖^2) := by
    simp only [mul_pow,mul_assoc,integral_const_mul,←Finset.mul_sum]
  rw [he,Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc]

lemma rawRMS_const {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) {c : ℝ} (hc : 0 ≤ c) :
    rawRMS ψ (fun _ => c)=c := by
  unfold rawRMS
  rw [potentialForm_const,hm,mul_one,Real.sqrt_sq hc]

lemma rawRMS_mono {n : ℕ} (ψ : H1Vector n)
    (f g : Configuration n → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x| ≤ B) (hC : ∀ x, |g x| ≤ C)
    (hf0 : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) : rawRMS ψ f ≤ rawRMS ψ g := by
  apply Real.sqrt_le_sqrt
  apply potentialForm_mono_bounded ψ _ _ (hf.pow_const 2) (hg.pow_const 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2)
    (fun x => by rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hC x) 2)
  exact fun x => pow_le_pow_left₀ (hf0 x) (hfg x) 2

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_RecordedStatistic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma arrayStatistic_measurable {n : ℕ} {χ : Space → ℝ} (hχ : Measurable χ) :
    Measurable (@arrayStatistic n χ) := by
  unfold arrayStatistic
  exact Finset.measurable_fun_sum _ (fun i _ => hχ.comp (continuous_position i).measurable)

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_RadialRMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma radialTailKernel_measurable (r : ℝ) : Measurable (radialTailKernel r) := by
  unfold radialTailKernel
  exact Measurable.ite (measurableSet_le measurable_const continuous_norm.measurable)
    continuous_norm.measurable.inv measurable_const

lemma radialTailStatistic_nonneg {n : ℕ} (r : ℝ) (x : Configuration n) :
    0 ≤ arrayStatistic (radialTailKernel r) x :=
  Finset.sum_nonneg (fun _ _ => radialTailKernel_nonneg _ _)

lemma radialTailStatistic_bound {n : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration n) :
    |arrayStatistic (radialTailKernel r) x| ≤ (n:ℝ)/r := by
  rw [abs_of_nonneg (radialTailStatistic_nonneg _ _)]
  calc
    _ ≤ ∑ _i : Fin n, r⁻¹ := Finset.sum_le_sum (fun i _ => radialTailKernel_le hr _)
    _ = _ := by simp [div_eq_mul_inv]

lemma radialTailStatistic_step {n : ℕ} {r : ℝ} (hr : 0 < r) (x : Configuration n) :
    arrayStatistic (radialTailKernel r) x ≤
      r⁻¹*localCount {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r} x+
      arrayStatistic (radialTailKernel (2*r)) x := by
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin n) _ => radialTailKernel_step hr (position x i))
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,arrayStatistic,localCount] using H

lemma radialTailRMS_step {n : ℕ} (ψ : H1Vector n) {r : ℝ} (hr : 0 < r) :
    rawRMS ψ (arrayStatistic (radialTailKernel r)) ≤
      Real.sqrt (localCountSecondMoment ψ {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r})/r+
      rawRMS ψ (arrayStatistic (radialTailKernel (2*r))) := by
  let A : Set Space := {z | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hb (x : Configuration n) : |r⁻¹*localCount A x| ≤ r⁻¹*(n:ℝ) := by
    rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr hr.le),abs_of_nonneg (localCount_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (localCount_le _ _) (inv_nonneg.mpr hr.le)
  have ht := radialTailStatistic_bound (n:=n) (show 0<2*r by positivity)
  have hsum (x : Configuration n) : |r⁻¹*localCount A x+arrayStatistic (radialTailKernel (2*r)) x| ≤
      r⁻¹*(n:ℝ)+(n:ℝ)/(2*r) := (abs_add_le _ _).trans (add_le_add (hb x) (ht x))
  have hm1 : Measurable (fun x : Configuration n => r⁻¹*localCount A x) := measurable_const.mul (localCount_measurable hA)
  have hm2 := arrayStatistic_measurable (n:=n) (radialTailKernel_measurable (2*r))
  calc
    _ ≤ rawRMS ψ (fun x => r⁻¹*localCount A x+arrayStatistic (radialTailKernel (2*r)) x) :=
      rawRMS_mono ψ _ _ (arrayStatistic_measurable (radialTailKernel_measurable r)) (hm1.add hm2)
        (radialTailStatistic_bound hr) hsum (radialTailStatistic_nonneg _) (radialTailStatistic_step hr)
    _ ≤ rawRMS ψ (fun x => r⁻¹*localCount A x)+rawRMS ψ (arrayStatistic (radialTailKernel (2*r))) :=
      rawRMS_add ψ _ _ hm1 hm2 hb ht
    _ = _ := by
      rw [rawRMS_const_mul ψ _ (inv_nonneg.mpr hr.le)]
      change r⁻¹ * Real.sqrt (localCountSecondMoment ψ A) + _ = _
      dsimp [A]
      ring

lemma radialTailRMS_cap {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1) {r : ℝ} (hr : 0 < r) :
    rawRMS ψ (arrayStatistic (radialTailKernel r)) ≤ (n:ℝ)/r := by
  calc
    _ ≤ rawRMS ψ (fun _ => (n:ℝ)/r) := rawRMS_mono ψ _ _
      (arrayStatistic_measurable (radialTailKernel_measurable r)) measurable_const
      (radialTailStatistic_bound hr) (fun _ => le_rfl)
      (radialTailStatistic_nonneg _) (fun x => (le_abs_self _).trans (radialTailStatistic_bound hr x))
    _ = _ := rawRMS_const ψ hm (by positivity)

theorem atomic_radial_tail_second_moment : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E+δ → 0 ≤ δ →
    ∀ {h : ℝ}, 0<h → rawRMS ψ (arrayStatistic (radialTailKernel h)) ≤ C*screenMass δ h/h := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=(1/2:ℝ)) (β:=4) (by norm_num) (by norm_num)
  refine ⟨4*Real.sqrt C,by positivity,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ h hh
  have hmean {r : ℝ} (hr : 0 < r) :
      Real.sqrt (localCountSecondMoment ψ {z : Space | (1/2:ℝ)*r < ‖z‖ ∧ ‖z‖ < 4*r}) ≤
        Real.sqrt C*screenMass δ r := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le,?_⟩
    rw [mul_pow,Real.sq_sqrt hC]
    exact H S hatom ψ hψ hm hE hstate hδ hr
  let K : ℝ := Real.sqrt C*screenMass δ h/h
  have hK : 0 ≤ K := by exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le) hh.le
  have hstep (j : ℕ) : rawRMS ψ (arrayStatistic (radialTailKernel ((2:ℝ)^j*h))) ≤ K*(3/4:ℝ)^j+
      rawRMS ψ (arrayStatistic (radialTailKernel ((2:ℝ)^(j+1)*h))) := by
    have hr : 0 < (2:ℝ)^j*h := by positivity
    have H1 := div_le_div_of_nonneg_right (hmean hr) hr.le
    have H2 := mul_le_mul_of_nonneg_left (screenMass_dyadic_bound hδ hh j) (Real.sqrt_nonneg C)
    have H3 : Real.sqrt (localCountSecondMoment ψ {z : Space | (1/2:ℝ)*((2:ℝ)^j*h) < ‖z‖ ∧ ‖z‖ < 4*((2:ℝ)^j*h)})/((2:ℝ)^j*h) ≤ K*(3/4:ℝ)^j := by
      calc
        _ ≤ Real.sqrt C*screenMass δ ((2:ℝ)^j*h)/((2:ℝ)^j*h) := H1
        _ ≤ K*(3/4:ℝ)^j := by simpa only [K,mul_div_assoc,mul_assoc] using H2
    have He : 2*((2:ℝ)^j*h)=(2:ℝ)^(j+1)*h := by rw [pow_succ]; ring
    exact (radialTailRMS_step ψ hr).trans (by rw [He]; exact add_le_add H3 le_rfl)
  have hfinite (N : ℕ) : rawRMS ψ (arrayStatistic (radialTailKernel h)) ≤
      K*(∑ j∈Finset.range N, (3/4:ℝ)^j)+rawRMS ψ (arrayStatistic (radialTailKernel ((2:ℝ)^N*h))) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have HS := add_le_add (le_refl (K*∑ j∈Finset.range N, (3/4:ℝ)^j)) (hstep N)
      refine ih.trans (HS.trans_eq ?_)
      rw [Finset.sum_range_succ]
      ring
  have hbound (N : ℕ) : rawRMS ψ (arrayStatistic (radialTailKernel h)) ≤ 4*K+((n:ℝ)/h)*(1/2:ℝ)^N := by
    have hs : (∑ j∈Finset.range N, (3/4:ℝ)^j) ≤ 4 := by
      have HH := geom_sum_mul_neg (3/4:ℝ) N
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 3/4) N]
    have ht := radialTailRMS_cap ψ hm (show 0 < (2:ℝ)^N*h by positivity)
    have he : (n:ℝ)/((2:ℝ)^N*h)=((n:ℝ)/h)*(1/2:ℝ)^N := by
      rw [div_pow,one_pow]
      field_simp
    exact (hfinite N).trans (by rw [←he]; nlinarith [mul_le_mul_of_nonneg_left hs hK])
  have hlim : Tendsto (fun N : ℕ => 4*K+(n:ℝ)/h*(1/2:ℝ)^N) atTop (𝓝 (4*K)) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1))) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have Hfinal := ge_of_tendsto' hlim hbound
  dsimp [K] at Hfinal
  exact Hfinal.trans_eq (by ring)

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_AnnularAddback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma measurableSet_addbackBand (h u : ℝ) : MeasurableSet {v : Space | h≤‖v‖ ∧ ‖v‖<8*u} :=
  (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
lemma annularAddbackKernel_measurable (h u : ℝ) : Measurable (annularAddbackKernel h u) :=
  (measurable_const.mul (measurable_const.indicator (measurableSet_addbackBand h u))).add
    (measurable_const.mul (radialTailKernel_measurable _))
lemma annularAddbackKernel_nonneg {u : ℝ} (hu : 0<u) (h : ℝ) (z : Space) :
    0≤annularAddbackKernel h u z := by
  exact add_nonneg (mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
    (mul_nonneg (by norm_num) (radialTailKernel_nonneg _ _))
lemma annularAddbackKernel_bound {u : ℝ} (hu : 0<u) (h : ℝ) (z : Space) :
    annularAddbackKernel h u z≤5001/u := by
  have hb : {v : Space | h≤‖v‖ ∧ ‖v‖<8*u}.indicator (fun _ => (1:ℝ)) z≤1 := by
    by_cases hz : h≤‖z‖ ∧ ‖z‖<8*u <;> simp [hz]
  have ht := radialTailKernel_le (show 0<8*u by positivity) z
  have H := add_le_add (mul_le_mul_of_nonneg_left hb (show 0≤5000/u by positivity))
    (mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤2 by norm_num))
  apply H.trans
  rw [mul_one]
  have he : 5000/u+2*(8*u)⁻¹=(5000+1/4)/u := by ring
  rw [he]
  exact div_le_div_of_nonneg_right (by norm_num) hu.le

lemma innerBall_subset_far {u h : ℝ} (hu : 0<u) (hh : h≤u/4) {y : Space} (hy : u/2≤‖y‖) :
    Metric.ball (0:Space) h ⊆ {z : Space | 40*atomicCellScale y≤‖z-y‖} := by
  intro z hz
  have hn : ‖z‖<h := by simpa only [Metric.mem_ball,dist_zero_right] using hz
  have ht : ‖y‖≤‖z-y‖+‖z‖ := by simpa only [dist_eq_norm,dist_zero_right,sub_zero,norm_sub_rev] using dist_triangle y z 0
  change 40*(‖y‖/100000) ≤ ‖z-y‖
  linarith

lemma annularAddbackKernel_coulomb {u h : ℝ} (hu : 0<u) {y z : Space}
    (hylo : u/2≤‖y‖) (hyhi : ‖y‖≤4*u) (hz : h≤‖z‖)
    (hfar : 40*atomicCellScale y≤‖z-y‖) :
    coulombKernel (z-y)≤annularAddbackKernel h u z := by
  by_cases hzu : ‖z‖<8*u
  · have hd : u/5000≤‖z-y‖ := by dsimp only [atomicCellScale] at hfar; linarith
    have H : coulombKernel (z-y)≤5000/u := by
      unfold coulombKernel
      apply (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0<u/5000) hd) (by positivity : 0<u/5000)).2 at hd
      simpa using hd
    unfold annularAddbackKernel
    rw [indicator_of_mem (show z∈{v : Space | h≤‖v‖ ∧ ‖v‖<8*u} from ⟨hz,hzu⟩),mul_one]
    exact H.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) (radialTailKernel_nonneg _ _)))
  · have hn : 8*u≤‖z‖ := le_of_not_gt hzu
    have hz0 : 0<‖z‖ := lt_of_lt_of_le (by positivity) hn
    have ht : ‖z‖≤‖z-y‖+‖y‖ := by simpa only [dist_eq_norm,dist_zero_right,sub_zero] using dist_triangle z y 0
    have hd : ‖z‖/2≤‖z-y‖ := by linarith
    have H : coulombKernel (z-y)≤2*‖z‖⁻¹ := by
      unfold coulombKernel
      have HH := (inv_le_inv₀ (lt_of_lt_of_le (by positivity : 0<‖z‖/2) hd) (by positivity : 0<‖z‖/2)).2 hd
      simpa [div_eq_mul_inv] using HH
    unfold annularAddbackKernel radialTailKernel
    rw [ite_eq_left hn,indicator_of_notMem (show z∉{v : Space | h≤‖v‖ ∧ ‖v‖<8*u} from fun h => hzu h.2),mul_zero,zero_add]
    exact H

lemma rawInnerField_addback {n : ℕ} {u h : ℝ} (hu : 0<u) (hh : h≤u/4) (V : ℝ)
    {y : Space} (hylo : u/2≤‖y‖) (hyhi : ‖y‖≤4*u) (x : Configuration n) :
    rawSignedField V (Metric.ball 0 h) y x ≤
      rawSignedField V {z : Space | 40*atomicCellScale y≤‖z-y‖} y x+
        arrayStatistic (annularAddbackKernel h u) x := by
  have H (i : Fin n) :
      (if position x i∈{z : Space | 40*atomicCellScale y≤‖z-y‖} then coulombKernel (position x i-y) else 0) ≤
        (if position x i∈Metric.ball 0 h then coulombKernel (position x i-y) else 0)+annularAddbackKernel h u (position x i) := by
    by_cases hi : position x i∈Metric.ball 0 h
    · rw [ite_eq_left hi,ite_eq_left (innerBall_subset_far hu hh hylo hi)]
      exact le_add_of_nonneg_right (annularAddbackKernel_nonneg hu h _)
    · rw [ite_eq_right hi]
      simp only [Set.mem_ofPred_eq]
      by_cases hf : 40*atomicCellScale y≤‖position x i-y‖
      · rw [ite_eq_left hf,zero_add]
        exact annularAddbackKernel_coulomb hu hylo hyhi
          (by simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hi) hf
      · rw [ite_eq_right hf,zero_add]
        exact annularAddbackKernel_nonneg hu h _
  have HH := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => H i)
  simp only [Finset.sum_add_distrib] at HH
  unfold rawSignedField restrictedOutPotential arrayStatistic
  linarith

lemma rawRMS_annularAddback {n : ℕ} (ψ : H1Vector n) {u : ℝ} (hu : 0<u) (h : ℝ) :
    rawRMS ψ (arrayStatistic (annularAddbackKernel h u)) ≤
      (5000/u)*Real.sqrt (localCountSecondMoment ψ {v : Space | h≤‖v‖ ∧ ‖v‖<8*u})+
        2*rawRMS ψ (arrayStatistic (radialTailKernel (8*u))) := by
  have he : arrayStatistic (annularAddbackKernel h u)=(fun x : Configuration n =>
      (5000/u)*localCount {v : Space | h≤‖v‖ ∧ ‖v‖<8*u} x+2*arrayStatistic (radialTailKernel (8*u)) x) := by
    funext x
    simp only [arrayStatistic,annularAddbackKernel,Finset.sum_add_distrib,←Finset.mul_sum,localCount]
  rw [he]
  have hb (x : Configuration n) : |(5000/u)*localCount {v : Space | h≤‖v‖ ∧ ‖v‖<8*u} x|≤(5000/u)*(n:ℝ) := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤5000/u),abs_of_nonneg (localCount_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (localCount_le _ _) (by positivity)
  have ht (x : Configuration n) : |2*arrayStatistic (radialTailKernel (8*u)) x|≤2*((n:ℝ)/(8*u)) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact mul_le_mul_of_nonneg_left (radialTailStatistic_bound (by positivity) x) (by norm_num)
  exact (rawRMS_add ψ _ _ (measurable_const.mul (localCount_measurable (measurableSet_addbackBand h u)))
    (measurable_const.mul (arrayStatistic_measurable (radialTailKernel_measurable _))) hb ht).trans_eq (by
      change rawRMS ψ (fun x => (5000/u)*localCount {v : Space | h≤‖v‖ ∧ ‖v‖<8*u} x)+
        rawRMS ψ (fun x => 2*arrayStatistic (radialTailKernel (8*u)) x) = _
      rw [rawRMS_const_mul ψ _ (by positivity),rawRMS_const_mul ψ _ (by norm_num)]
      rfl)

lemma screenMass_zero_mono {h r : ℝ} (hh : 0<h) (hr : h ≤ r) : screenMass 0 r ≤ screenMass 0 h := by
  simp only [screenMass,zero_mul,Real.sqrt_zero,add_zero,screenBaseMass]
  apply max_le_max _ le_rfl
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hh.le hr 3)

lemma dyadic_annulus_cover {h : ℝ} (hh : 0<h) (N : ℕ) :
    {z : Space | h≤‖z‖ ∧ ‖z‖<(2:ℝ)^N*h} ⊆
      ⋃ j : Fin N, {z : Space | (1/2:ℝ)*((2:ℝ)^j.val*h)<‖z‖ ∧ ‖z‖<4*((2:ℝ)^j.val*h)} := by
  induction N with
  | zero => intro z hz; simp only [pow_zero,one_mul] at hz; exact (not_lt_of_ge hz.1 hz.2).elim
  | succ N ih =>
    intro z hz
    by_cases ht : ‖z‖<(2:ℝ)^N*h
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (ih ⟨hz.1,ht⟩)
      exact Set.mem_iUnion.mpr ⟨j.castSucc,hj⟩
    · refine Set.mem_iUnion.mpr ⟨Fin.last N,?_⟩
      have hr : 0<(2:ℝ)^N*h := by positivity
      have H := hz.2
      simp only [pow_succ] at H
      constructor <;> simp only [Fin.val_last] <;> nlinarith [le_of_not_gt ht]

theorem atomic_dyadic_count_RMS : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
    ∀ {h : ℝ}, 0<h → ∀ N : ℕ,
      Real.sqrt (localCountSecondMoment ψ {z : Space | h≤‖z‖ ∧ ‖z‖<(2:ℝ)^N*h}) ≤
        C*N*screenMass 0 h := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=(1/2:ℝ)) (β:=4) (by norm_num) (by norm_num)
  refine ⟨Real.sqrt C,Real.sqrt_nonneg _,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate h hh N
  let A : Fin N → Set Space := fun j => {z | (1/2:ℝ)*((2:ℝ)^j.val*h)<‖z‖ ∧ ‖z‖<4*((2:ℝ)^j.val*h)}
  have hA (j) : MeasurableSet (A j) :=
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hc (j : Fin N) : localCountSecondMoment ψ (A j)≤C*(screenMass 0 h)^2 := by
    have hr : 0<(2:ℝ)^j.val*h := by positivity
    have hs : h≤(2:ℝ)^j.val*h := by nlinarith [(one_le_pow₀ (n:=j.val) (show (1:ℝ)≤2 by norm_num))]
    have HH := H S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate) (le_refl 0) hr
    exact HH.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (screenMass_pos _ _).le (screenMass_zero_mono hh hs) 2) hC)
  have HC := (localCountSecondMoment_cover ψ A hA (dyadic_annulus_cover hh N)).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hc j)) (by positivity))
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity [screenMass_pos 0 h],?_⟩
  apply HC.trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_pow,Real.sq_sqrt hC]
  ring

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalRMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma potentialForm_bounded_add {n : ℕ} (ψ : H1Vector n)
    (f g : Configuration n → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x|≤B) (hC : ∀ x, |g x|≤C) :
    potentialForm (fun x => f x+g x) ψ=potentialForm f ψ+potentialForm g ψ := by
  simp only [potentialForm,add_mul,integral_add (boundedObservable_integrable ψ f hf hB _)
    (boundedObservable_integrable ψ g hg hC _),Finset.sum_add_distrib]

lemma coreConditionalObservable_nonneg {m k : ℕ} (ψ : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : ∀ x, 0≤W x) (s : Spins m) (x : Configuration m) :
    0 ≤ coreConditionalObservable ψ W s x := potentialForm_nonneg _ _ (fun _ => hW _)

lemma coreConditionalObservable_mono {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Configuration (m+k) → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x|≤B) (hC : ∀ x, |g x|≤C) (hfg : ∀ x, f x≤g x)
    (s : Spins m) (x : Configuration m) :
    coreConditionalObservable ψ f s x ≤ coreConditionalObservable ψ g s x := by
  exact potentialForm_mono_bounded _ _ _
    (hf.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (hg.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (fun _ => hB _) (fun _ => hC _) (fun _ => hfg _)

lemma coreConditionalObservable_add {m k : ℕ} (ψ : H1Vector (m+k))
    (f g : Configuration (m+k) → ℝ) (hf : Measurable f) (hg : Measurable g)
    {B C : ℝ} (hB : ∀ x, |f x|≤B) (hC : ∀ x, |g x|≤C)
    (s : Spins m) (x : Configuration m) :
    coreConditionalObservable ψ (fun z => f z+g z) s x=
      coreConditionalObservable ψ f s x+coreConditionalObservable ψ g s x := by
  exact potentialForm_bounded_add _ _ _
    (hf.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (hg.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (fun _ => hB _) (fun _ => hC _)

lemma coreConditionalObservable_square_weight_integrable {m k : ℕ} (ψ : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0≤B)
    (hB : ∀ x, |W x|≤B) (s : Spins m) :
    Integrable (fun x => mass (ψ.coreSlice s x)*(coreConditionalObservable ψ W s x)^2) := by
  apply (mass_coreSlice_integrable ψ s).mul_bdd
    ((coreConditionalObservable_aestronglyMeasurable ψ W hW hB s).pow 2)
  filter_upwards [] with x
  change ‖(coreConditionalObservable ψ W s x)^2‖ ≤ B^2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
    (coreConditionalObservable_abs_le ψ W hW hB0 hB s x) 2

lemma potentialForm_normalized_square_le {n : ℕ} (ψ : H1Vector n)
    (W : Configuration n → ℝ) (hW : Measurable W) {B : ℝ} (hB : ∀ x, |W x|≤B) :
    (potentialForm W ψ.normalized)^2 ≤ potentialForm (fun x => (W x)^2) ψ.normalized := by
  have H := potentialForm_bounded_cauchy ψ.normalized W (fun _ => 1) hW measurable_const hB (fun _ => le_rfl)
  simp only [mul_one,one_pow,potentialForm_const,one_mul] at H
  exact H.trans (by nlinarith [mass_normalized_le_one ψ,
    potentialForm_nonneg ψ.normalized (fun x => (W x)^2) (fun _ => sq_nonneg _)])

lemma slice_conditional_square_le {m k : ℕ} (ψ : H1Vector (m+k))
    (W : Configuration (m+k) → ℝ) (hW : Measurable W) {B : ℝ} (hB0 : 0≤B)
    (hB : ∀ x, |W x|≤B) :
    sliceExpectation ψ (fun s x => (coreConditionalObservable ψ W s x)^2) ≤
      potentialForm (fun x => (W x)^2) ψ := by
  have hB2 (x) : |(W x)^2|≤B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  rw [←sliceExpectation_coreConditionalObservable ψ _ (hW.pow_const 2) hB2]
  apply sliceExpectation_mono_ae ψ _ _
    (coreConditionalObservable_square_weight_integrable ψ W hW hB0 hB)
    (coreConditionalObservable_weight_integrable ψ _ (hW.pow_const 2) (sq_nonneg _) hB2)
  intro s
  filter_upwards [] with x
  exact potentialForm_normalized_square_le _ _
    (hW.comp ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
    (fun _ => hB _)

namespace RecordedEnsemble
variable {n : ℕ}
lemma dataRMS_nonneg (T : RecordedEnsemble n) (F) : 0≤T.dataRMS F := Real.sqrt_nonneg _
lemma dataRMS_sq (T : RecordedEnsemble n) (F) :
    T.dataRMS F^2=∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2) :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    integral_nonneg (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _)))))

theorem Conserves.dataRMS_conditional_le {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) (W : Configuration n → ℝ) (hW : Measurable W)
    {B : ℝ} (hB0 : 0≤B) (hB : ∀ x, |W x|≤B) :
    T.dataRMS (fun p => coreConditionalObservable (T.vector p) (W ∘ reindexConfiguration (T.labels p))) ≤rawRMS ψ W := by
  apply Real.sqrt_le_sqrt
  have hB2 (x) : |(W x)^2|≤B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]; simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => slice_conditional_square_le (T.vector p)
    (W ∘ reindexConfiguration (T.labels p)) (hW.comp (reindexConfiguration_continuous _).measurable)
    hB0 (fun x => hB _))
  exact H.trans_eq (hT (fun x => (W x)^2) (hW.pow_const 2) ⟨B^2,hB2⟩)

end RecordedEnsemble
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_InnerFieldRMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

namespace RecordedEnsemble
variable {n : ℕ}

lemma Conserves.positive_addback_RMS {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) (W V A : Configuration n → ℝ)
    (hW : Measurable W) (hV : Measurable V) (hA : Measurable A)
    {BW BV BA : ℝ} (hBW : 0≤ BW) (hBV : 0≤ BV) (hBA : 0≤ BA)
    (hwb : ∀ x, |W x|≤ BW) (hvb : ∀ x, |V x|≤ BV) (hab : ∀ x, |A x|≤ BA)
    (ha0 : ∀ x, 0≤ A x) (hwa : ∀ x, W x≤ V x+A x) :
    T.dataRMS (fun p s x => max (coreConditionalObservable (T.vector p)
      (W ∘ reindexConfiguration (T.labels p)) s x) 0) ≤
      2*(T.dataRMS (fun p s x => max (coreConditionalObservable (T.vector p)
        (V ∘ reindexConfiguration (T.labels p)) s x) 0)+rawRMS ψ A) := by
  let F p := coreConditionalObservable (T.vector p) (W ∘ reindexConfiguration (T.labels p))
  let G p := coreConditionalObservable (T.vector p) (V ∘ reindexConfiguration (T.labels p))
  let H p := coreConditionalObservable (T.vector p) (A ∘ reindexConfiguration (T.labels p))
  have hsum (x) : |V x+A x|≤ BV+BA := (abs_add_le _ _).trans (add_le_add (hvb x) (hab x))
  have hh p s x : 0≤ H p s x := coreConditionalObservable_nonneg _ _ (fun _ => ha0 _) s x
  have hfg p s x : max (F p s x) 0≤ max (G p s x) 0+H p s x := by
    have he := coreConditionalObservable_add (T.vector p)
      (V ∘ reindexConfiguration (T.labels p)) (A ∘ reindexConfiguration (T.labels p))
      (hV.comp (reindexConfiguration_continuous (T.labels p)).measurable)
      (hA.comp (reindexConfiguration_continuous (T.labels p)).measurable) (fun _ => hvb _) (fun _ => hab _) s x
    have hm := coreConditionalObservable_mono (T.vector p)
      (W ∘ reindexConfiguration (T.labels p)) (fun x => (V ∘ reindexConfiguration (T.labels p)) x+(A ∘ reindexConfiguration (T.labels p)) x)
      (hW.comp (reindexConfiguration_continuous (T.labels p)).measurable)
      ((hV.add hA).comp (reindexConfiguration_continuous (T.labels p)).measurable)
      (fun _ => hwb _) (fun _ => hsum _) (fun _ => hwa _) s x
    rw [he] at hm
    exact max_le (hm.trans (add_le_add (le_max_left _ _) le_rfl))
      (add_nonneg (le_max_right _ _) (hh p s x))
  have hiG p s := coreConditionalObservable_positive_weight_integrable (T.vector p)
    (V ∘ reindexConfiguration (T.labels p))
    (hV.comp (reindexConfiguration_continuous (T.labels p)).measurable) hBV (fun _ => hvb _) s 2
  have hiH p s := coreConditionalObservable_square_weight_integrable (T.vector p)
    (A ∘ reindexConfiguration (T.labels p))
    (hA.comp (reindexConfiguration_continuous (T.labels p)).measurable) hBA (fun _ => hab _) s
  have hsq : (T.dataRMS (fun p s x => max (F p s x) 0))^2 ≤
      2*(T.dataRMS (fun p s x => max (G p s x) 0))^2+2*(T.dataRMS H)^2 := by
    simp only [dataRMS_sq,sliceExpectation]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s hs
    rw [←integral_const_mul,←integral_const_mul,←integral_add ((hiG p s).const_mul 2) ((hiH p s).const_mul 2)]
    apply integral_mono_ae
    · exact coreConditionalObservable_positive_weight_integrable (T.vector p)
        (W ∘ reindexConfiguration (T.labels p))
        (hW.comp (reindexConfiguration_continuous (T.labels p)).measurable) hBW (fun _ => hwb _) s 2
    · exact ((hiG p s).const_mul 2).add ((hiH p s).const_mul 2)
    · filter_upwards [] with x
      have Hsq : (max (F p s x) 0)^2≤2*(max (G p s x) 0)^2+2*(H p s x)^2 := by
        have H1 := pow_le_pow_left₀ (le_max_right (F p s x) 0) (hfg p s x) 2
        nlinarith [sq_nonneg (max (G p s x) 0-H p s x)]
      have H2 := mul_le_mul_of_nonneg_left Hsq (mass_nonneg ((T.vector p).coreSlice s x))
      nlinarith
  have hH := hT.dataRMS_conditional_le A hA hBA hab
  have hmG := T.dataRMS_nonneg (fun p s x => max (G p s x) 0)
  have hmH := T.dataRMS_nonneg H
  have hR := rawRMS_nonneg ψ A
  change T.dataRMS (fun p s x => max (F p s x) 0) ≤
    2*(T.dataRMS (fun p s x => max (G p s x) 0)+rawRMS ψ A)
  change T.dataRMS H ≤ rawRMS ψ A at hH
  nlinarith [T.dataRMS_nonneg (fun p s x => max (F p s x) 0)]

lemma innerSquare_nonneg {J : ℕ} (T : RecordedEnsemble n) (S : Nuclei J) (h : ℝ) (y : Space) :
    0≤ T.innerSquare S h y := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      integral_nonneg (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))

lemma Conserves.innerSquare_addback {J : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) (S : Nuclei J) {u h : ℝ} (hu : 0<u) (hh : h≤ u/4)
    {y : Space} (hylo : u/2≤‖y‖) (hyhi : ‖y‖≤4*u) :
    Real.sqrt (T.innerSquare S h y) ≤2*(Real.sqrt (T.rawSquare S y (atomicCellScale y))+
      rawRMS ψ (arrayStatistic (annularAddbackKernel h u))) := by
  have ha : 0<40*atomicCellScale y := by unfold atomicCellScale; linarith
  have hA : MeasurableSet {z : Space | 40*atomicCellScale y≤‖z-y‖} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hb0 : 0≤|attraction S y|+(n:ℝ)/(40*atomicCellScale y) := by positivity
  have hb1 (x : Configuration n) : |arrayStatistic (annularAddbackKernel h u) x| ≤ (n:ℝ)*(5001/u) := by
    unfold arrayStatistic
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => annularAddbackKernel_nonneg hu h _))]
    calc
      _ ≤ ∑ _i : Fin n, 5001/u := Finset.sum_le_sum (fun _ _ => annularAddbackKernel_bound hu h _)
      _ = _ := by simp
  have hb := rawSignedField_abs_le (n:=n) (attraction S y) _ y ha (fun _ hz => innerBall_subset_far hu hh hylo hz)
  have hj := rawSignedField_abs_le (n:=n) (attraction S y) _ y ha (fun _ hz => hz)
  have H := hT.positive_addback_RMS
    (rawSignedField (attraction S y) (Metric.ball 0 h) y)
    (rawSignedField (attraction S y) {z : Space | 40*atomicCellScale y≤‖z-y‖} y)
    (arrayStatistic (annularAddbackKernel h u))
    (rawSignedField_measurable _ measurableSet_ball y) (rawSignedField_measurable _ hA y)
    (arrayStatistic_measurable (annularAddbackKernel_measurable h u)) hb0 hb0 (by positivity)
    hb hj hb1 (fun _ => Finset.sum_nonneg (fun _ _ => annularAddbackKernel_nonneg hu h _))
    (rawInnerField_addback hu hh _ hylo hyhi)
  simpa only [dataRMS,innerSquare,rawSquare,Function.comp_def,rawSignedField_reindex] using H

end RecordedEnsemble
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_DyadicInnerRMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

theorem annular_dyadic_inner_field : ∀ C₀ : ℝ, 0≤C₀ → ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
    ∀ {t : ℝ}, 0<t → ∀ ell : ℕ, ∀ T : RecordedEnsemble n,
      T.Conserves ψ → T.CoreFermionic →
      T.OutSupported {x : Space | ((2:ℝ)^ell*t)/2<‖x‖ ∧ ‖x‖<4*((2:ℝ)^ell*t)} →
      T.totalMass=mass ψ → T.totalForm S≤form S ψ+C₀*screenMass 0 ((2:ℝ)^ell*t)/((2:ℝ)^ell*t)^2 →
      ∀ y : Space, ((2:ℝ)^ell*t)/2≤‖y‖ → ‖y‖≤4*((2:ℝ)^ell*t) →
      Real.sqrt (T.innerSquare S (t/4) y) ≤
        C*screenMass 0 (t/4)*((ell:ℝ)+1)/((2:ℝ)^ell*t) := by
  intro C₀ hC₀
  obtain ⟨Cs,hCs,Hs⟩ := annular_ensemble_positive_field C₀ hC₀
  obtain ⟨Cc,hCc,Hc⟩ := atomic_dyadic_count_RMS
  obtain ⟨Cr,hCr,Hr⟩ := atomic_radial_tail_second_moment
  refine ⟨10*(Cs+5000*Cc+2*Cr),by positivity,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate t ht ell T hlaw hf hsupp hmass hform y hylo hyhi
  let u : ℝ := (2:ℝ)^ell*t
  have hu : 0<u := by dsimp [u]; positivity
  have hpow : (1:ℝ)≤2^ell := one_le_pow₀ (by norm_num)
  have htu : t≤u := by dsimp [u]; nlinarith
  have hh : 0<t/4 := by positivity
  have hhu : t/4≤u := by linarith
  have hhu8 : t/4≤8*u := by linarith
  have Hs1 := Hs S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate)
    (le_refl 0) hu T hlaw hf hsupp hmass hform y hylo hyhi
  have Hs2 : Real.sqrt (T.rawSquare S y (atomicCellScale y))≤Cs*screenMass 0 (t/4)/u :=
    Hs1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (screenMass_zero_mono hh hhu) hCs) hu.le)
  have Hc1 := Hc S hatom ψ hψ hm hE hstate hh (ell+5)
  have hrad : (2:ℝ)^(ell+5)*(t/4)=8*u := by rw [pow_add]; norm_num; dsimp [u]; ring
  rw [hrad] at Hc1
  have Hr1 := Hr S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate) (le_refl 0) (show 0<8*u by positivity)
  have Hr2 : rawRMS ψ (arrayStatistic (radialTailKernel (8*u)))≤Cr*screenMass 0 (t/4)/u := by
    apply Hr1.trans
    calc
      _ ≤ Cr*screenMass 0 (t/4)/(8*u) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (screenMass_zero_mono hh hhu8) hCr) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hCr (screenMass_pos _ _).le) hu (by linarith)
  have Ha := rawRMS_annularAddback ψ hu (t/4)
  have Hab : rawRMS ψ (arrayStatistic (annularAddbackKernel (t/4) u)) ≤
      (5000/u)*(Cc*((ell:ℝ)+5)*screenMass 0 (t/4))+2*(Cr*screenMass 0 (t/4)/u) := by
    apply Ha.trans
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.cast_add,Nat.cast_ofNat] using Hc1
    · exact mul_le_mul_of_nonneg_left Hr2 (by norm_num)
  have HI := hlaw.innerSquare_addback S hu (show t/4≤u/4 by linarith) hylo hyhi
  have Hfin := HI.trans (mul_le_mul_of_nonneg_left (add_le_add Hs2 Hab) (by norm_num : (0:ℝ)≤2))
  apply Hfin.trans
  have hc : 0≤Cs+5000*Cc+2*Cr := by positivity
  have hel : 0≤(ell:ℝ) := by positivity
  have hcoeff : 2*(Cs+5000*Cc*((ell:ℝ)+5)+2*Cr) ≤
      10*(Cs+5000*Cc+2*Cr)*((ell:ℝ)+1) := by
    nlinarith [mul_nonneg hCs hel,mul_nonneg hCc hel,mul_nonneg hCr hel]
  have H := mul_le_mul_of_nonneg_right hcoeff (div_nonneg (screenMass_pos 0 (t/4)).le hu.le)
  convert H using 1 <;> ring

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WeightedInner
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma weightedInnerField_measurable {J n : ℕ} (S : Nuclei J) (h : ℝ)
    {w : Space → ℝ} (hw : Measurable w) : Measurable (@weightedInnerField J n S h w) := by
  unfold weightedInnerField
  apply Finset.measurable_fun_sum
  intro i hi
  have hp : Measurable (fun x : Configuration n => position x i) :=
    (continuous_position i).measurable
  have hc : Measurable (fun x : Configuration n => (x,position x i)) :=
    measurable_id.prodMk hp
  have hr : Measurable (fun x : Configuration n =>
      restrictedOutPotential x (Metric.ball 0 h) (position x i)) :=
    (restrictedOutPotential_joint_measurable (m:=n) (A:=Metric.ball (0:Space) h) measurableSet_ball).comp (f:=fun x : Configuration n => (x,position x i)) hc
  have ha : Measurable (fun x : Configuration n => attraction S (position x i)) :=
    (attraction_measurable S).comp hp
  exact (hw.comp hp).mul (ha.sub hr)

lemma weightedInnerField_reindex {J m n : ℕ} (S : Nuclei J) (h : ℝ) (w : Space → ℝ)
    (e : Fin m ≃ Fin n) (x : Configuration m) :
    weightedInnerField S h w (reindexConfiguration e x)=weightedInnerField S h w x := by
  simp only [weightedInnerField,rawSignedField_reindex]
  change (∑ i : Fin n, w (position x (e.symm i))*
    rawSignedField (attraction S (position x (e.symm i))) (Metric.ball 0 h) (position x (e.symm i)) x)=_
  exact Equiv.sum_comp e.symm (fun i : Fin m => w (position x i)*
    rawSignedField (attraction S (position x i)) (Metric.ball 0 h) (position x i) x)

lemma inner_shell_separation {u h : ℝ} (hu : 0<u) (hh : h ≤ u/2)
    {y : Space} (hy : u ≤ ‖y‖) (z : Space) (hz : z∈Metric.ball (0:Space) h) :
    u/2 ≤ ‖z-y‖ := by
  have hn : ‖z‖<h := by simpa only [Metric.mem_ball,dist_zero_right] using hz
  have H : ‖y‖ ≤ ‖z-y‖+‖z‖ := by
    simpa only [dist_eq_norm,sub_zero,norm_sub_rev] using dist_triangle y z 0
  apply (mul_le_mul_iff_right₀ hu).mp
  exact mul_le_mul_of_nonneg_left (by linarith only [hh, hy, hn, H]) hu.le

lemma weighted_raw_inner_abs_le {J n : ℕ} (S : Nuclei J) (hatom : ∀ j, S.position j=0)
    {u h : ℝ} (hu : 0<u) (hh : h ≤ u/2) {w : Space → ℝ}
    (hw : ∀ y, |w y| ≤ 1) (hws : ∀ y∉imsShell 0 u, w y=0)
    (y : Space) (x : Configuration n) :
    |w y*rawSignedField (attraction S y) (Metric.ball 0 h) y x| ≤
      totalCharge S/u+(n:ℝ)/(u/2) := by
  by_cases hy : y∈imsShell 0 u
  · have hyr : u ≤ ‖y‖ := by simpa only [imsShell,mem_ofPred_eq,sub_zero] using hy.1
    have HB := rawSignedField_abs_le (attraction S y) (Metric.ball 0 h) y
      (show 0<u/2 by positivity) (inner_shell_separation hu hh hyr) x
    have HA : attraction S y ≤ totalCharge S/u := attraction_le_totalCharge_div S hu y
      (fun j => by simpa only [hatom j,sub_zero] using hyr)
    rw [abs_of_nonneg (attraction_nonneg S y)] at HB
    rw [abs_mul]
    calc
      _ ≤ 1*|rawSignedField (attraction S y) (Metric.ball 0 h) y x| :=
        mul_le_mul_of_nonneg_right (hw y) (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using HB.trans (add_le_add HA le_rfl)
  · rw [hws y hy,zero_mul,abs_zero]
    exact add_nonneg (div_nonneg (totalCharge_nonneg S) hu.le) (by positivity)

lemma weightedInnerField_abs_le {J n : ℕ} (S : Nuclei J) (hatom : ∀ j, S.position j=0)
    {u h : ℝ} (hu : 0<u) (hh : h ≤ u/2) {w : Space → ℝ}
    (hw : ∀ y, |w y| ≤ 1) (hws : ∀ y∉imsShell 0 u, w y=0)
    (x : Configuration n) :
    |weightedInnerField S h w x| ≤ (n:ℝ)*(totalCharge S/u+(n:ℝ)/(u/2)) := by
  unfold weightedInnerField
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => weighted_raw_inner_abs_le S hatom hu hh hw hws (position x i) x)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H

lemma weightedInnerField_join_of_support {J m k : ℕ} (S : Nuclei J) (h : ℝ)
    {u : ℝ} {w : Space → ℝ} (hws : ∀ y∉imsShell 0 u, w y=0)
    (x : Configuration m) {z : Configuration k} (hz : z∈allPositions (imsShell 0 u)ᶜ) :
    weightedInnerField S h w (joinConfiguration m k (x,z))=
      ∑ i : Fin m, w (position x i)*rawSignedField (attraction S (position x i))
        (Metric.ball 0 h) (position x i) (joinConfiguration m k (x,z)) := by
  simp only [weightedInnerField,Fin.sum_univ_add,position_join_left,position_join_right]
  have he : (∑ i : Fin k, w (position z i)*rawSignedField (attraction S (position z i))
      (Metric.ball 0 h) (position z i) (joinConfiguration m k (x,z)))=0 := by
    exact Finset.sum_eq_zero (fun i _ => by rw [hws _ (hz i),zero_mul])
  rw [he,add_zero]

lemma potentialForm_const_mul_value {n : ℕ} (v : H1Vector n) (c : ℝ) (F : Configuration n → ℝ) :
    potentialForm (fun x => c*F x) v = c*potentialForm F v := by
  simp only [potentialForm,mul_assoc,integral_const_mul,Finset.mul_sum]

lemma conditional_weighted_inner_le {J m k : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) (v : H1Vector (m+k)) {u h : ℝ}
    (hu : 0<u) (hh : h ≤ u/2) {w : Space → ℝ} (hwm : Measurable w)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1) (hws : ∀ y∉imsShell 0 u, w y=0)
    (s : Spins m) (x : Configuration m) (hm : 0 < mass (v.coreSlice s x))
    (hcore : SpatiallySupported (v.coreSlice s x).normalized (imsShell 0 u)ᶜ)
    {M : ℝ} (hM : 0 ≤ M)
    (hcap : ∀ y, u ≤ ‖y‖ → ‖y‖ ≤ 2*u →
      max (recordedFarField S (v.coreSlice s x).normalized x (Metric.ball 0 h) y) 0 ≤ M) :
    coreConditionalObservable v (weightedInnerField S h w) s x ≤ (m:ℝ)*M := by
  let v₀ := (v.coreSlice s x).normalized
  let F (i : Fin m) (z : Configuration k) := w (position x i)*rawSignedField
    (attraction S (position x i)) (Metric.ball 0 h) (position x i) (joinConfiguration m k (x,z))
  have hwabs y : |w y| ≤ 1 := by rw [abs_of_nonneg (hw0 y)]; exact hw1 y
  have hFi i : Measurable (F i) := (hwm.comp measurable_const).mul
    ((rawSignedField_measurable _ measurableSet_ball _).comp
      ((joinConfiguration m k).continuous.measurable.comp (measurable_const.prodMk measurable_id)))
  have hFb i z : |F i z| ≤ totalCharge S/u+((m+k:ℕ):ℝ)/(u/2) :=
    weighted_raw_inner_abs_le S hatom hu hh hwabs hws _ _
  have he : coreConditionalObservable v (weightedInnerField S h w) s x=
      ∑ i : Fin m, potentialForm (F i) v₀ := by
    unfold coreConditionalObservable potentialForm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    rw [←integral_finsetSum _ (fun i _ => boundedObservable_integrable v₀ (F i) (hFi i) (hFb i) q)]
    apply integral_congr_ae
    filter_upwards [hcore q] with z hz
    by_cases hz' : z∈allPositions (imsShell 0 u)ᶜ
    · rw [weightedInnerField_join_of_support S h hws x hz',Finset.sum_mul]
    · rw [hz hz',norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero]
      exact (Finset.sum_eq_zero (fun _ _ => mul_zero _)).symm
  rw [he]
  calc
    _ ≤ ∑ _i : Fin m, M := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hwz : w (position x i)=0
      · simp only [F,hwz,zero_mul,potentialForm,integral_zero,Finset.sum_const_zero]
        exact hM
      · have hy : position x i∈imsShell 0 u := by by_contra h; exact hwz (hws _ h)
        have hyr : u ≤ ‖position x i‖ ∧ ‖position x i‖ ≤ 2*u := by
          simpa only [imsShell,mem_ofPred_eq,sub_zero] using hy
        have hhf := coreConditionalObservable_rawSignedField v (attraction S (position x i))
          measurableSet_ball (position x i) (show 0<u/2 by positivity)
          (inner_shell_separation hu hh hyr.1) s x hm
        have heq : potentialForm (F i) v₀ = w (position x i)*
            recordedFarField S v₀ x (Metric.ball 0 h) (position x i) := by
          rw [show F i=(fun z => w (position x i)*rawSignedField (attraction S (position x i))
            (Metric.ball 0 h) (position x i) (joinConfiguration m k (x,z))) from rfl,
            potentialForm_const_mul_value]
          exact congrArg (fun z => w (position x i)*z) hhf
        rw [heq]
        exact (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (hcap _ hyr.1 hyr.2)) (hw0 _)).trans
          ((mul_le_mul_of_nonneg_right (hw1 _) hM).trans_eq (one_mul _))
    _ = _ := by simp

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_AnnularCut
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

lemma cutAngle_inner (y : Space) {r : ℝ} (hr : 0 < r) {x : Space} (hx : ‖x-y‖ ≤ r) :
    cutAngle y r x=Real.pi/2 := by
  have hs : ‖r⁻¹ • (x-y)‖≤1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).2 hx
  simp [cutAngle,cutSeed_one _ hs]

lemma cutAngle_outer (y : Space) {r : ℝ} (hr : 0 < r) {x : Space} (hx : 2*r≤‖x-y‖) :
    cutAngle y r x=0 := by
  have hs : 2≤‖r⁻¹ • (x-y)‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact (le_inv_mul_iff₀ hr).2 (by simpa only [mul_comm] using hx)
  simp [cutAngle,cutSeed_zero _ hs]

lemma annularCut_core_zero {u : ℝ} (hu : 0<u) {x : Space} (hx : u≤‖x‖ ∧ ‖x‖≤2*u) :
    annularCut u 1 x=0 := by
  have h1 := cutAngle_inner 0 (by positivity : 0<2*u) (x:=x) (by simpa using hx.2)
  have h2 := cutAngle_outer 0 (by positivity : 0<u/2) (x:=x) (by simp only [sub_zero]; linarith [hx.1])
  simp only [annularCut,show (1:Fin 2)≠0 by decide,ite_false,annularAngle,h1,h2,sub_zero,Real.cos_pi_div_two]

lemma annularCut_out_zero {u : ℝ} (hu : 0<u) {x : Space} (hx : ‖x‖≤u/2 ∨ 4*u≤‖x‖) :
    annularCut u 0 x=0 := by
  have hz : annularAngle u x=0 := by
    rcases hx with hx|hx
    · have h1 := cutAngle_inner 0 (by positivity : 0<2*u) (x:=x) (by simpa using (show ‖x‖≤2*u by linarith))
      have h2 := cutAngle_inner 0 (by positivity : 0<u/2) (x:=x) (by simpa using hx)
      simp only [annularAngle,h1,h2,sub_self]
    · have h1 := cutAngle_outer 0 (by positivity : 0<2*u) (x:=x) (by simp only [sub_zero]; linarith)
      have h2 := cutAngle_outer 0 (by positivity : 0<u/2) (x:=x) (by simp only [sub_zero]; linarith)
      simp only [annularAngle,h1,h2,sub_self]
  simp [annularCut,hz]

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_AnnularIMS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

lemma measurableSet_annularBand (u : ℝ) : MeasurableSet (annularBand u) :=
  ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)).measurableSet

lemma annularAngle_zero {u : ℝ} (hu : 0<u) {x : Space} (hx : ‖x‖≤u/2 ∨ 4*u≤‖x‖) :
    annularAngle u x=0 := by
  rcases hx with hx|hx
  · have h1 := cutAngle_inner 0 (by positivity : 0<2*u) (x:=x) (by simp only [sub_zero]; linarith)
    have h2 := cutAngle_inner 0 (by positivity : 0<u/2) (x:=x) (by simpa using hx)
    simp only [annularAngle,h1,h2,sub_self]
  · have h1 := cutAngle_outer 0 (by positivity : 0<2*u) (x:=x) (by simp only [sub_zero]; linarith)
    have h2 := cutAngle_outer 0 (by positivity : 0<u/2) (x:=x) (by simp only [sub_zero]; linarith)
    simp only [annularAngle,h1,h2,sub_self]

lemma annularCut_derivative_zero {u : ℝ} (hu : 0<u) (l : Fin 2) {x : Space}
    (hx : x ∉ annularBand u) : fderiv ℝ (annularCut u l) x=0 := by
  have he : annularCut u l =ᶠ[𝓝 x] (fun _ => if l=0 then (0:ℝ) else 1) := by
    have hnot : ¬ (u/2 ≤ ‖x‖ ∧ ‖x‖ ≤ 4*u) := hx
    by_cases hi : ‖x‖ < u/2
    · have hn := (isOpen_lt continuous_norm continuous_const).mem_nhds hi
      filter_upwards [hn] with z hz
      simp only [annularCut,annularAngle_zero hu (Or.inl hz.le),Real.sin_zero,Real.cos_zero]
    · have ho : 4*u < ‖x‖ := lt_of_not_ge (fun h => hnot ⟨le_of_not_gt hi,h⟩)
      have hn := (isOpen_lt continuous_const continuous_norm).mem_nhds ho
      filter_upwards [hn] with z hz
      simp only [annularCut,annularAngle_zero hu (Or.inr hz.le),Real.sin_zero,Real.cos_zero]
  rw [he.fderiv_eq]
  simp

lemma annularCut_gradient_band_bound {u : ℝ} (hu : 0<u) (b : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (annularCut u l) x (EuclideanSpace.single b 1))^2) ≤
      (2*(3*radialCutCoefficient/u)^2)*(annularBand u).indicator (fun _ => (1:ℝ)) x := by
  by_cases hx : x∈annularBand u
  · rw [indicator_of_mem hx,mul_one]
    calc
      _ ≤ ∑ _l : Fin 2, (3*radialCutCoefficient/u)^2 := by
        apply Finset.sum_le_sum
        intro l hl
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (div_nonneg (mul_nonneg (by norm_num) radialCutCoefficient_pos.le) hu.le)).2 (annularCut_derivative_bound hu l b x)
      _ = _ := by simp
  · rw [indicator_of_notMem hx,mul_zero]
    simp only [annularCut_derivative_zero hu _ hx,zero_apply,ne_eq,OfNat.ofNat_ne_zero,
      not_false_eq_true,zero_pow,Finset.sum_const_zero,le_refl]

theorem form_annular_labelCut {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    {u : ℝ} (hu : 0<u) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (annularCut u) (annularCut_smooth u)
      (annularCut_partition u) (3*radialCutCoefficient/u) (div_nonneg (mul_nonneg (by norm_num) radialCutCoefficient_pos.le) hu.le)
      (annularCut_derivative_bound hu) p)) ≤
      form S ψ+3*(3*radialCutCoefficient/u)^2*expectedPopulation ψ (annularBand u) := by
  rw [form_labelCut]
  apply add_le_add_right
  let c : ℝ := 2*(3*radialCutCoefficient/u)^2
  have hi s i := population_integrable ψ (annularBand u) (measurableSet_annularBand u) s i
  have H (s : Spins n) (a : Fin n × Fin 3) :
      (∫ x, (∑ l, (fderiv ℝ (annularCut u l) (position x a.1) (EuclideanSpace.single a.2 1))^2)*‖ψ.value s x‖^2) ≤
      c*(∫ x, (annularBand u).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) := by
    rw [←integral_const_mul]
    apply integral_mono_of_nonneg
    · filter_upwards [] with x
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
    · exact (hi s a.1).const_mul c
    · filter_upwards [] with x
      simpa only [c,mul_assoc] using mul_le_mul_of_nonneg_right
        (annularCut_gradient_band_bound hu a.2 (position x a.1)) (sq_nonneg ‖ψ.value s x‖)
  calc
    _ ≤ (1/2:ℝ)*∑ s, ∑ a : Fin n × Fin 3, c*(∫ x,
          (annularBand u).indicator (fun _ => (1:ℝ)) (position x a.1)*‖ψ.value s x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun a _ => H s a))) (by norm_num)
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        ←Finset.mul_sum,expectedPopulation,c]
      ring

theorem exists_annular_recorded_ensemble {J n : ℕ} (S : Nuclei J)
    (ψ : H1Vector n) (hψ : Antisymmetric ψ) {u : ℝ} (hu : 0<u) :
    ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.OutFermionic ∧
      T.CoreSupported (imsShell 0 u)ᶜ ∧
      T.OutSupported {x : Space | u/2<‖x‖ ∧ ‖x‖<4*u} ∧
      T.totalMass=mass ψ ∧ T.totalForm S ≤ form S ψ+annularIMSCost ψ u := by
  obtain ⟨T,hc,hf,ho,hcs,hos,hm,he⟩ := RecordedEnsemble.binary_localization S ψ hψ
    (annularCut u) (annularCut_smooth u) (annularCut_partition u)
    (3*radialCutCoefficient/u) (div_nonneg (mul_nonneg (by norm_num) radialCutCoefficient_pos.le) hu.le) (annularCut_derivative_bound hu)
    {x : Space | u/2<‖x‖ ∧ ‖x‖<4*u} (imsShell 0 u)ᶜ
    (by
      intro z hz
      apply annularCut_out_zero hu
      by_cases hi : ‖z‖≤u/2
      · exact Or.inl hi
      · exact Or.inr (le_of_not_gt (fun h => hz ⟨lt_of_not_ge hi,h⟩)))
    (by
      intro z hz
      apply annularCut_core_zero hu
      simpa only [mem_compl_iff,not_not,imsShell,mem_ofPred_eq,sub_zero] using hz)
  refine ⟨T,hc,hf,ho,hcs,hos,hm,?_⟩
  rw [he]
  exact form_annular_labelCut S ψ hu

theorem exists_atomic_annular_IMS_bound : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ {u : ℝ}, 0<u → annularIMSCost ψ u ≤ C*screenMass δ u/u^2 := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=1/4) (β:=5) (by norm_num) (by norm_num)
  refine ⟨27*radialCutCoefficient^2*Real.sqrt C,by positivity,?_⟩
  intro J n S hatom ψ ha hm E δ hE hstate hδ u hu
  have hA : MeasurableSet {x : Space | (1/4:ℝ)*u<‖x‖ ∧ ‖x‖<5*u} :=
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hsub : annularBand u ⊆ {x : Space | (1/4:ℝ)*u<‖x‖ ∧ ‖x‖<5*u} := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hb := ((expectedPopulation_sq_le ψ (measurableSet_annularBand u) hm).trans
    (localCountSecondMoment_mono ψ hA hsub)).trans (H S hatom ψ ha hm hE hstate hδ hu)
  have hh : expectedPopulation ψ (annularBand u) ≤ Real.sqrt C*screenMass δ u := by
    rw [←Real.sq_sqrt hC,←mul_pow] at hb
    exact (sq_le_sq₀ (expectedPopulation_nonneg _ _) (mul_nonneg (Real.sqrt_nonneg C) (screenMass_pos _ _).le)).mp hb
  calc
    _ ≤ 3*(3*radialCutCoefficient/u)^2*(Real.sqrt C*screenMass δ u) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_InnerCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma innerLocalCap_nonneg {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Space) (a : ℝ) :
    0 ≤ innerLocalCap S v x h z a := Real.sqrt_nonneg _
lemma innerLocalCap_sq {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Space) {a : ℝ} (ha : 0<a) :
    (innerLocalCap S v x h z a)^2 =
      8*(∫ w, (max (recordedFarField S v x (Metric.ball 0 h) w) 0)^2*ballCloud z (2*a) 1 w) := by
  apply Real.sq_sqrt
  exact mul_nonneg (by norm_num) (integral_nonneg (fun w => mul_nonneg (sq_nonneg _)
    (uniformBall_nonneg (by positivity) zero_le_one (w-z))))
lemma innerLocalCap_le {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Space) {a : ℝ} (ha : 0<a)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-z‖) :
    innerLocalCap S v x h z a ≤ Real.sqrt (8*(totalCharge S/(2*a))^2) := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact positive_square_ballCloud_integral_le S _
    (recordedFarField_aestronglyMeasurable S v x measurableSet_ball)
    (recordedFarField_le_attraction S v x _) (by positivity) z (fun j => by nlinarith [hnuc j])
lemma innerLocalCap_normalized_slice_aestronglyMeasurable {J m k : ℕ} (S : Nuclei J)
    (v : H1Vector (m+k)) (s : Spins m) (h : ℝ) (z : Space) (a : ℝ) :
    AEStronglyMeasurable (fun x => innerLocalCap S (v.coreSlice s x).normalized x h z a) volume := by
  have hf := recordedFarField_normalized_slice_joint S v s (measurableSet_ball (x:=(0:Space)) (ε:=h))
  have H : AEStronglyMeasurable (fun p : Configuration m × Space =>
      (max (recordedFarField S (v.coreSlice s p.1).normalized p.1 (Metric.ball 0 h) p.2) 0)^2*
        ballCloud z (2*a) 1 p.2) (volume.prod volume) :=
    ((hf.sup aestronglyMeasurable_const).pow 2).mul
      ((ballCloud_measurable (2*a) 1 z).comp measurable_snd).aestronglyMeasurable
  exact Real.continuous_sqrt.comp_aestronglyMeasurable (H.integral_prod_right'.const_mul 8)
lemma innerLocalCap_weight_integrable {J m k : ℕ} (S : Nuclei J) (v : H1Vector (m+k))
    (s : Spins m) (h : ℝ) (z : Space) {a : ℝ} (ha : 0<a)
    (hnuc : ∀ j, 4*a ≤ ‖S.position j-z‖) (q : ℕ) :
    Integrable (fun x => mass (v.coreSlice s x)*(innerLocalCap S (v.coreSlice s x).normalized x h z a)^q) := by
  apply (mass_coreSlice_integrable v s).mul_bdd ((innerLocalCap_normalized_slice_aestronglyMeasurable S v s h z a).pow q)
  filter_upwards [] with x
  change ‖(innerLocalCap S (v.coreSlice s x).normalized x h z a)^q‖ ≤ (Real.sqrt (8*(totalCharge S/(2*a))^2))^q
  rw [Real.norm_of_nonneg (pow_nonneg (innerLocalCap_nonneg _ _ _ _ _ _) q)]
  exact pow_le_pow_left₀ (innerLocalCap_nonneg _ _ _ _ _ _) (innerLocalCap_le S _ x h z ha hnuc) q

lemma innerLocalCap_dominates {J m k : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z w : Space) {a : ℝ} (ha : 0<a)
    (hw : ‖w-z‖≤a) (hcore : ∀ q∈Metric.ball (0:Space) h, 4*a≤‖q-z‖)
    (hnuc : ∀ j, 4*a≤‖S.position j-z‖) :
    max (recordedFarField S v x (Metric.ball 0 h) w) 0 ≤ innerLocalCap S v x h z a := by
  apply (sq_le_sq₀ (le_max_right _ _) (innerLocalCap_nonneg _ _ _ _ _ _)).mp
  rw [innerLocalCap_sq S v x h z ha]
  exact recordedFarField_positive_submean_square S v x measurableSet_ball ha z w hw hcore hnuc

lemma sliceExpectation_innerLocalCap_sq {J m k : ℕ} (S : Nuclei J)
    (v : H1Vector (m+k)) (h : ℝ) (z : Space) {a : ℝ} (ha : 0<a)
    (hnuc : ∀ j, 4*a≤‖S.position j-z‖) :
    sliceExpectation v (fun s x => (innerLocalCap S (v.coreSlice s x).normalized x h z a)^2) =
      8*(∫ w, (sliceExpectation v (fun s x =>
        (max (recordedFarField S (v.coreSlice s x).normalized x (Metric.ball 0 h) w) 0)^2))*ballCloud z (2*a) 1 w) := by
  simp only [innerLocalCap_sq S _ _ h z ha]
  rw [sliceExpectation_const_mul,sliceExpectation_farSquare_ballCloud S v measurableSet_ball
    (by positivity) z (fun j => by nlinarith [hnuc j])]

namespace RecordedEnsemble
variable {n J : ℕ}
lemma innerSquare_eq_recorded (T : RecordedEnsemble n) (S : Nuclei J) (h : ℝ) (w : Space)
    {r : ℝ} (hr : 0 < r) (hsep : ∀ q∈Metric.ball (0:Space) h, r≤‖q-w‖) :
    T.innerSquare S h w = ∑ p, sliceExpectation (T.vector p) (fun s x =>
      (max (recordedFarField S ((T.vector p).coreSlice s x).normalized x (Metric.ball 0 h) w) 0)^2) := by
  unfold innerSquare sliceExpectation
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => coreConditionalObservable_raw_positive_weight (T.vector p)
    (attraction S w) measurableSet_ball w hr hsep s x)

theorem innerLocalCap_second_moment (T : RecordedEnsemble n) (S : Nuclei J)
    (h : ℝ) (z : Space) {a r K : ℝ} (ha : 0<a) (hr : 0 < r)
    (hnuc : ∀ j, 4*a≤‖S.position j-z‖)
    (hsep : ∀ w : Space, ‖w-z‖≤2*a → ∀ q∈Metric.ball (0:Space) h, r≤‖q-w‖)
    (hraw : ∀ w : Space, ‖w-z‖≤2*a → T.innerSquare S h w ≤ K) :
    (∑ p, sliceExpectation (T.vector p) (fun s x =>
      (innerLocalCap S ((T.vector p).coreSlice s x).normalized x h z a)^2)) ≤ 8*K := by
  let F := fun p w => sliceExpectation (T.vector p) (fun s x =>
    (max (recordedFarField S ((T.vector p).coreSlice s x).normalized x (Metric.ball 0 h) w) 0)^2)
  have hi p : Integrable (fun w => F p w*ballCloud z (2*a) 1 w) :=
    sliceFarSquare_ballCloud_integrable S (T.vector p) measurableSet_ball (by positivity) z (fun j => by nlinarith [hnuc j])
  have hb : Integrable (fun w => K*ballCloud z (2*a) 1 w) := (ballCloud_integrable _ _ _).const_mul K
  have hsum : (∫ w, ∑ p, F p w*ballCloud z (2*a) 1 w) ≤ K := by
    calc
      _ ≤ ∫ w, K*ballCloud z (2*a) 1 w := by
        apply integral_mono (integrable_finsetSum _ (fun p _ => hi p)) hb
        intro w
        change (∑ p, F p w*ballCloud z (2*a) 1 w) ≤ K*ballCloud z (2*a) 1 w
        rw [←Finset.sum_mul]
        by_cases hw : w-z ∈ Metric.ball (0:Space) (2*a)
        · have hd : ‖w-z‖≤2*a := (by simpa only [Metric.mem_ball,dist_zero_right] using hw : ‖w-z‖<2*a).le
          apply mul_le_mul_of_nonneg_right _ (uniformBall_nonneg (by positivity) zero_le_one (w-z))
          rw [←T.innerSquare_eq_recorded S h w hr (hsep w hd)]
          exact hraw w hd
        · simp only [ballCloud,uniformBall,indicator_of_notMem hw,mul_zero,le_refl]
      _ = K := by rw [integral_const_mul,ballCloud_mass (by positivity) 1 z,mul_one]
  calc
    _ = ∑ p, 8*(∫ w, F p w*ballCloud z (2*a) 1 w) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sliceExpectation_innerLocalCap_sq S (T.vector p) h z ha hnuc
    _ = 8*(∫ w, ∑ p, F p w*ballCloud z (2*a) 1 w) := by
      rw [←Finset.mul_sum,integral_finsetSum _ (fun p _ => hi p)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)
end RecordedEnsemble
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_InnerMeshCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma exists_inner_shell_mesh : ∃ M : ℕ, ∀ {u : ℝ}, 0<u → ∃ z : Fin M → Space,
    (∀ i, u≤‖z i‖ ∧ ‖z i‖≤2*u) ∧
    (∀ w : Space, u≤‖w‖ → ‖w‖≤2*u → ∃ i, ‖w-z i‖≤atomicCellScale (z i)) := by
  obtain ⟨t,ht,hcover⟩ := exists_atomic_annular_mesh (α:=1) (β:=2) (by norm_num)
  let e := Fintype.equivFin {z : Space // z∈t}
  refine ⟨Fintype.card {z : Space // z∈t},?_⟩
  intro u hu
  refine ⟨(fun i => u • (e.symm i).val),?_,?_⟩
  · intro i
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hu]
    have H := ht (e.symm i).val (e.symm i).property
    constructor <;> nlinarith [H.1,H.2]
  · intro w hw1 hw2
    have hn : ‖u⁻¹ • w‖=‖w‖/u := by simp [norm_smul,abs_of_pos hu,div_eq_mul_inv,mul_comm]
    obtain ⟨v,hv,Hv⟩ := hcover (u⁻¹ • w)
      (by rw [hn]; exact (one_le_div hu).mpr hw1)
      (by rw [hn]; exact (div_le_iff₀ hu).mpr hw2)
    refine ⟨e ⟨v,hv⟩,?_⟩
    simp only [Equiv.symm_apply_apply,atomicCellScale_smul hu.le]
    have he : w-u • v=u • (u⁻¹ • w-v) := by simp [smul_sub,smul_smul,hu.ne']
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hu]
    exact mul_le_mul_of_nonneg_left Hv.le hu.le

lemma innerMeshCap_nonneg {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) :
    0 ≤ innerMeshCap S v x h z := Real.sqrt_nonneg _
lemma innerMeshCap_sq {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) :
    (innerMeshCap S v x h z)^2=∑ i, (innerLocalCap S v x h (z i) (atomicCellScale (z i)))^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
lemma innerLocalCap_le_mesh {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) (i : Fin M) :
    innerLocalCap S v x h (z i) (atomicCellScale (z i)) ≤ innerMeshCap S v x h z := by
  apply (sq_le_sq₀ (innerLocalCap_nonneg _ _ _ _ _ _) (innerMeshCap_nonneg _ _ _ _ _)).mp
  rw [innerMeshCap_sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (innerLocalCap S v x h (z j) (atomicCellScale (z j)))) (Finset.mem_univ i)
lemma innerMeshCap_normalized_slice_aestronglyMeasurable {J m k M : ℕ} (S : Nuclei J)
    (v : H1Vector (m+k)) (s : Spins m) (h : ℝ) (z : Fin M → Space) :
    AEStronglyMeasurable (fun x => innerMeshCap S (v.coreSlice s x).normalized x h z) volume := by
  apply Real.continuous_sqrt.comp_aestronglyMeasurable
  exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
    (innerLocalCap_normalized_slice_aestronglyMeasurable S v s h _ _).pow 2)
lemma innerMeshCap_bound {J m k M : ℕ} (S : Nuclei J) (v : H1Vector k)
    (x : Configuration m) (h : ℝ) (z : Fin M → Space) (hz : ∀ i, z i≠0)
    (hnuc : ∀ i j, 4*atomicCellScale (z i)≤‖S.position j-z i‖) :
    innerMeshCap S v x h z ≤ Real.sqrt (∑ i, 8*(totalCharge S/(2*atomicCellScale (z i)))^2) := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i hi
  have H := innerLocalCap_le S v x h (z i) (atomicCellScale_pos (hz i)) (hnuc i)
  exact (pow_le_pow_left₀ (innerLocalCap_nonneg _ _ _ _ _ _) H 2).trans_eq (Real.sq_sqrt (by positivity))
lemma innerMeshCap_weight_integrable {J m k M : ℕ} (S : Nuclei J) (v : H1Vector (m+k))
    (s : Spins m) (h : ℝ) (z : Fin M → Space) (hz : ∀ i, z i≠0)
    (hnuc : ∀ i j, 4*atomicCellScale (z i)≤‖S.position j-z i‖) (q : ℕ) :
    Integrable (fun x => mass (v.coreSlice s x)*(innerMeshCap S (v.coreSlice s x).normalized x h z)^q) := by
  apply (mass_coreSlice_integrable v s).mul_bdd ((innerMeshCap_normalized_slice_aestronglyMeasurable S v s h z).pow q)
  filter_upwards [] with x
  change ‖(innerMeshCap S (v.coreSlice s x).normalized x h z)^q‖ ≤
    (Real.sqrt (∑ i, 8*(totalCharge S/(2*atomicCellScale (z i)))^2))^q
  rw [Real.norm_of_nonneg (pow_nonneg (innerMeshCap_nonneg _ _ _ _ _) q)]
  exact pow_le_pow_left₀ (innerMeshCap_nonneg _ _ _ _ _) (innerMeshCap_bound S _ x h z hz hnuc) q

namespace RecordedEnsemble
variable {n J : ℕ}

theorem exists_inner_shell_envelope : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j, S.position j=0) →
    ∀ (T : RecordedEnsemble n) {u h K : ℝ}, 0<u → h≤u/4 → 0≤K →
      (∀ w : Space, u/2≤‖w‖ → ‖w‖≤4*u → Real.sqrt (T.innerSquare S h w)≤K) →
      ∃ M : T.InnerEnvelope S h u, T.dataRMS M.value ≤ C*K := by
  obtain ⟨Q,HQ⟩ := exists_inner_shell_mesh
  refine ⟨Real.sqrt (8*(Q:ℝ)),Real.sqrt_nonneg _,?_⟩
  intro J n S hatom T u h K hu hh hK hpoint
  obtain ⟨z,hzbound,hcover⟩ := HQ hu
  have hz i : z i≠0 := norm_pos_iff.mp (hu.trans_le (hzbound i).1)
  have hnuc i j : 4*atomicCellScale (z i)≤‖S.position j-z i‖ := by
    rw [hatom j,zero_sub,norm_neg]
    unfold atomicCellScale
    linarith [norm_nonneg (z i)]
  have hcore i q (hq : q∈Metric.ball (0:Space) h) : 4*atomicCellScale (z i)≤‖q-z i‖ := by
    have hn : ‖q‖<h := by simpa only [Metric.mem_ball,dist_zero_right] using hq
    have H : ‖z i‖≤‖q-z i‖+‖q‖ := by simpa only [dist_eq_norm,sub_zero,norm_sub_rev] using dist_triangle (z i) q 0
    unfold atomicCellScale
    linarith [(hzbound i).1]
  let M : T.InnerEnvelope S h u := {
    value := fun p s x => innerMeshCap S ((T.vector p).coreSlice s x).normalized x h z
    nonneg := fun p s x => innerMeshCap_nonneg _ _ _ _ _
    measurable := fun p s => innerMeshCap_normalized_slice_aestronglyMeasurable S (T.vector p) s h z
    integrable := fun p s => by simpa only [pow_one] using innerMeshCap_weight_integrable S (T.vector p) s h z hz hnuc 1
    square_integrable := fun p s => innerMeshCap_weight_integrable S (T.vector p) s h z hz hnuc 2
    dominates := fun p s x w hw1 hw2 => by
      obtain ⟨i,hi⟩ := hcover w hw1 hw2
      exact (innerLocalCap_dominates S _ x h (z i) w (atomicCellScale_pos (hz i)) hi (hcore i) (hnuc i)).trans
        (innerLocalCap_le_mesh S _ x h z i) }
  refine ⟨M,?_⟩
  have hwbound i w (hw : ‖w-z i‖≤2*atomicCellScale (z i)) : u/2≤‖w‖ ∧ ‖w‖≤4*u := by
    have H1 : ‖z i‖≤‖w-z i‖+‖w‖ := by simpa only [dist_eq_norm,sub_zero,norm_sub_rev] using dist_triangle (z i) w 0
    have H2 : ‖w‖≤‖w-z i‖+‖z i‖ := by simpa only [dist_eq_norm,sub_zero] using dist_triangle w (z i) 0
    unfold atomicCellScale at hw
    constructor <;> linarith [(hzbound i).1,(hzbound i).2]
  have hsep i w (hw : ‖w-z i‖≤2*atomicCellScale (z i)) q (hq : q∈Metric.ball (0:Space) h) : u/4≤‖q-w‖ := by
    have hn : ‖q‖<h := by simpa only [Metric.mem_ball,dist_zero_right] using hq
    have H : ‖w‖≤‖q-w‖+‖q‖ := by simpa only [dist_eq_norm,sub_zero,norm_sub_rev] using dist_triangle w q 0
    linarith [(hwbound i w hw).1]
  have hic i : (∑ p, sliceExpectation (T.vector p) (fun s x =>
      (innerLocalCap S ((T.vector p).coreSlice s x).normalized x h (z i) (atomicCellScale (z i)))^2))≤8*K^2 := by
    apply T.innerLocalCap_second_moment S h (z i) (atomicCellScale_pos (hz i)) (show 0<u/4 by positivity)
      (hnuc i) (hsep i)
    intro w hw
    have H := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpoint w (hwbound i w hw).1 (hwbound i w hw).2) 2
    simpa only [Real.sq_sqrt (T.innerSquare_nonneg S h w)] using H
  have he : (T.dataRMS M.value)^2=∑ i, ∑ p, sliceExpectation (T.vector p) (fun s x =>
      (innerLocalCap S ((T.vector p).coreSlice s x).normalized x h (z i) (atomicCellScale (z i)))^2) := by
    rw [T.dataRMS_sq]
    simp only [M,innerMeshCap_sq,sliceExpectation,Finset.mul_sum]
    conv_lhs => arg 2; ext p; arg 2; ext s; rw [integral_finsetSum _ (fun i _ =>
      innerLocalCap_weight_integrable S (T.vector p) s h (z i) (atomicCellScale_pos (hz i)) (hnuc i) 2)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hic i)
  rw [←he] at H
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
  apply (sq_le_sq₀ (T.dataRMS_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hK)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity : (0:ℝ)≤8*Q)]
  nlinarith

end RecordedEnsemble
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_DeletionEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

theorem exists_atomic_deletion_envelope : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E →
    ∀ {t : ℝ}, 0<t → ∀ ell : ℕ,
      ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.OutFermionic ∧
        T.CoreSupported (imsShell 0 ((2:ℝ)^ell*t))ᶜ ∧
        T.OutSupported {x : Space | ((2:ℝ)^ell*t)/2<‖x‖ ∧ ‖x‖<4*((2:ℝ)^ell*t)} ∧
        T.totalMass=mass ψ ∧ T.totalForm S ≤ form S ψ+annularIMSCost ψ ((2:ℝ)^ell*t) ∧
        ∃ M : T.InnerEnvelope S (t/4) ((2:ℝ)^ell*t),
          T.dataRMS M.value ≤ C*screenMass 0 (t/4)*((ell:ℝ)+1)/((2:ℝ)^ell*t) := by
  obtain ⟨Ci,hCi,Hi⟩ := exists_atomic_annular_IMS_bound
  obtain ⟨Cf,hCf,Hf⟩ := annular_dyadic_inner_field Ci hCi
  obtain ⟨Cm,hCm,Hm⟩ := RecordedEnsemble.exists_inner_shell_envelope
  refine ⟨Cm*Cf,mul_nonneg hCm hCf,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate t ht ell
  have hu : 0 < (2:ℝ)^ell*t := by positivity
  obtain ⟨T,hc,hf,ho,hcs,hos,hmas,he⟩ := exists_annular_recorded_ensemble S ψ hψ hu
  have hcost := Hi S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate) (le_refl 0) hu
  have Hpoint := Hf S hatom ψ hψ hm hE hstate ht ell T hc hf hos hmas (he.trans (add_le_add le_rfl hcost))
  have hpow : (1:ℝ) ≤ 2^ell := one_le_pow₀ (by norm_num)
  have hh : t/4 ≤ ((2:ℝ)^ell*t)/4 := by nlinarith
  have hK : 0 ≤ Cf*screenMass 0 (t/4)*((ell:ℝ)+1)/((2:ℝ)^ell*t) := by
    exact div_nonneg (mul_nonneg (mul_nonneg hCf (screenMass_pos _ _).le) (by positivity)) hu.le
  obtain ⟨M,hM⟩ := Hm S hatom T hu hh hK Hpoint
  refine ⟨T,hc,hf,ho,hcs,hos,hmas,he,M,?_⟩
  exact hM.trans_eq (by ring)

end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma measurableSet_deletionShell (t : ℝ) (j : ℕ) : MeasurableSet (deletionShell t j) :=
  ((isClosed_le continuous_const continuous_norm).measurableSet).inter
    ((isOpen_lt continuous_norm continuous_const).measurableSet)

lemma deletionShellWeight_measurable {w : Space → ℝ} (hw : Measurable w) (t : ℝ) (j : ℕ) :
    Measurable (deletionShellWeight t w j) := hw.indicator (measurableSet_deletionShell t j)

lemma deletionShellWeight_nonneg {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (t : ℝ) (j : ℕ) (y : Space) :
    0 ≤ deletionShellWeight t w j y := by
  exact Set.indicator_nonneg (fun y _ => hw y) y

lemma deletionShellWeight_le_one {w : Space → ℝ} (hw : ∀ y, w y ≤ 1) (t : ℝ) (j : ℕ) (y : Space) :
    deletionShellWeight t w j y ≤ 1 := by
  unfold deletionShellWeight
  by_cases hy : y∈deletionShell t j
  · rw [indicator_of_mem hy]; exact hw y
  · rw [indicator_of_notMem hy]; norm_num

lemma deletionShellWeight_supported (t : ℝ) (w : Space → ℝ) (j : ℕ) (y : Space)
    (hy : y∉imsShell 0 ((2:ℝ)^j*t)) : deletionShellWeight t w j y=0 := by
  apply indicator_of_notMem
  intro H
  apply hy
  simp only [imsShell,mem_ofPred_eq,sub_zero]
  refine ⟨H.1,?_⟩
  have : (2:ℝ)^(j+1)*t=2*((2:ℝ)^j*t) := by rw [pow_succ]; ring
  rw [←this]
  exact H.2.le

lemma deletionShellWeight_sum {t : ℝ} (ht : 0<t) (w : Space → ℝ) (k : ℕ) (y : Space) :
    (∑ j ∈ Finset.range k, deletionShellWeight t w j y)=
      if t ≤ ‖y‖ ∧ ‖y‖ < (2:ℝ)^k*t then w y else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,ih]
    have hp : 1 ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have htk : t ≤ (2:ℝ)^k*t := by nlinarith
    have hnext : (2:ℝ)^k*t ≤ (2:ℝ)^(k+1)*t := by rw [pow_succ]; nlinarith
    simp only [deletionShellWeight,Set.indicator_apply,deletionShell,mem_ofPred_eq]
    split_ifs <;> simp_all <;> try omega
    all_goals nlinarith [mul_le_mul_of_nonneg_right hp ht.le, mul_le_mul_of_nonneg_right hnext ht.le]

lemma deletionShellWeight_sum_bound {t : ℝ} (ht : 0<t) {w : Space → ℝ}
    (hw : ∀ y, |w y| ≤ 1) (k : ℕ) (y : Space) :
    |∑ j ∈ Finset.range k, deletionShellWeight t w j y| ≤ 1 := by
  rw [deletionShellWeight_sum ht]
  split_ifs
  · exact hw y
  · norm_num

lemma deletion_geometric_sum (k : ℕ) :
    (∑ j ∈ Finset.range k, ((j:ℝ)+1)*(1/2:ℝ)^j) ≤ 4 := by
  have he : (∑ j ∈ Finset.range k, ((j:ℝ)+1)*(1/2:ℝ)^j)=
      4-(2*(k:ℝ)+4)*(1/2:ℝ)^k := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [Finset.sum_range_succ,ih,pow_succ,Nat.cast_add,Nat.cast_one]; ring
  rw [he]
  have H : 0 ≤ (2*(k:ℝ)+4)*(1/2:ℝ)^k := by positivity
  linarith

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WeightedExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma weighted_raw_inner_exterior_abs_le {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) {t h : ℝ} (ht : 0<t) (hh : h ≤ t/2)
    {w : Space → ℝ} (hw : ∀ y, |w y| ≤ 1) (hws : ∀ y, ‖y‖<t → w y=0)
    (y : Space) (x : Configuration n) :
    |w y*rawSignedField (attraction S y) (Metric.ball 0 h) y x| ≤
      totalCharge S/t+(n:ℝ)/(t/2) := by
  by_cases hy : t ≤ ‖y‖
  · have HB := rawSignedField_abs_le (attraction S y) (Metric.ball 0 h) y
      (show 0<t/2 by positivity) (inner_shell_separation ht hh hy) x
    have HA : attraction S y ≤ totalCharge S/t := attraction_le_totalCharge_div S ht y
      (fun j => by simpa only [hatom j,sub_zero] using hy)
    rw [abs_of_nonneg (attraction_nonneg S y)] at HB
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hw y) (abs_nonneg _)).trans
      (by simpa only [one_mul] using HB.trans (add_le_add HA le_rfl))
  · rw [hws y (lt_of_not_ge hy),zero_mul,abs_zero]
    exact add_nonneg (div_nonneg (totalCharge_nonneg S) ht.le) (by positivity)

lemma weightedInnerField_exterior_abs_le {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) {t h : ℝ} (ht : 0<t) (hh : h ≤ t/2)
    {w : Space → ℝ} (hw : ∀ y, |w y| ≤ 1) (hws : ∀ y, ‖y‖<t → w y=0)
    (x : Configuration n) :
    |weightedInnerField S h w x| ≤ (n:ℝ)*(totalCharge S/t+(n:ℝ)/(t/2)) := by
  unfold weightedInnerField
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    weighted_raw_inner_exterior_abs_le S hatom ht hh hw hws (position x i) x)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H

lemma potentialForm_bounded_tendsto {n : ℕ} (u : H1Vector n)
    {F : ℕ → Configuration n → ℝ} {G : Configuration n → ℝ} {B : ℝ}
    (hF : ∀ k, Measurable (F k)) (hb : ∀ k x, |F k x| ≤ B)
    (hlim : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (G x))) :
    Tendsto (fun k => potentialForm (F k) u) atTop (𝓝 (potentialForm G u)) := by
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => B*‖u.value s x‖^2)
  · intro k
    exact (hF k).aestronglyMeasurable.mul ((u.value_L2 s).aestronglyMeasurable.norm.pow 2)
  · exact ((u.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul B
  · intro k
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg ‖u.value s x‖)]
    exact mul_le_mul_of_nonneg_right (hb k x) (sq_nonneg _)
  · exact Eventually.of_forall (fun x => (hlim x).mul_const _)

lemma potentialForm_sum_values {n : ℕ} {ι : Type*} (u : H1Vector n)
    (s : Finset ι) (F : ι → Configuration n → ℝ)
    (hF : ∀ i∈s, ∀ q : Spins n, Integrable (fun x => F i x*‖u.value q x‖^2)) :
    potentialForm (fun x => ∑ i∈s, F i x) u=∑ i∈s, potentialForm (F i) u := by
  simp only [potentialForm,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  exact integral_finsetSum s (fun i hi => hF i hi q)

lemma weightedInnerField_sum_weights {J n : ℕ} {ι : Type*} (S : Nuclei J) (h : ℝ)
    (s : Finset ι) (w : ι → Space → ℝ) (x : Configuration n) :
    weightedInnerField S h (fun y => ∑ i∈s, w i y) x=
      ∑ i∈s, weightedInnerField S h (w i) x := by
  simp only [weightedInnerField,Finset.sum_mul]
  exact Finset.sum_comm

lemma deletionShellWeight_sum_supported {t : ℝ} (ht : 0<t) (w : Space → ℝ) (k : ℕ)
    (y : Space) (hy : ‖y‖<t) : (∑ j∈Finset.range k, deletionShellWeight t w j y)=0 := by
  rw [deletionShellWeight_sum ht]
  split_ifs with h
  · exact False.elim (not_le.mpr hy h.1)
  · rfl

lemma deletionShellWeight_sum_tendsto {t : ℝ} (ht : 0<t) {w : Space → ℝ}
    (hws : ∀ y, ‖y‖<t → w y=0) (y : Space) :
    Tendsto (fun k => ∑ j∈Finset.range k, deletionShellWeight t w j y) atTop (𝓝 (w y)) := by
  have H : Tendsto (fun k : ℕ => (2:ℝ)^k*t) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const ht
  have he := H.eventually (eventually_gt_atTop ‖y‖)
  by_cases hy : t ≤ ‖y‖
  · apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [he] with k hk
    rw [deletionShellWeight_sum ht,ite_eq_left ⟨hy,hk⟩]
  · have hy' : ‖y‖<t := lt_of_not_ge hy
    simp_rw [deletionShellWeight_sum_supported ht w _ y hy',hws y hy']
    exact tendsto_const_nhds

lemma weightedInnerField_shell_partial_tendsto {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j, S.position j=0) (u : H1Vector n) {t : ℝ} (ht : 0<t)
    {w : Space → ℝ} (hw : Measurable w) (hb : ∀ y, |w y| ≤ 1)
    (hws : ∀ y, ‖y‖<t → w y=0) :
    Tendsto (fun k => potentialForm (weightedInnerField S (t/4)
      (fun y => ∑ j∈Finset.range k, deletionShellWeight t w j y)) u)
      atTop (𝓝 (potentialForm (weightedInnerField S (t/4) w) u)) := by
  apply potentialForm_bounded_tendsto (B:=(n:ℝ)*(totalCharge S/t+(n:ℝ)/(t/2)))
  · intro k
    exact weightedInnerField_measurable S (t/4)
      (Finset.measurable_fun_sum _ (fun j _ => deletionShellWeight_measurable hw t j))
  · intro k x
    exact weightedInnerField_exterior_abs_le S hatom ht (by linarith)
      (deletionShellWeight_sum_bound ht hb k) (deletionShellWeight_sum_supported ht w k) x
  · intro x
    apply tendsto_finsetSum
    intro i hi
    exact (deletionShellWeight_sum_tendsto ht hws (position x i)).mul_const _

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_ShellSummable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical ContDiff Topology
noncomputable section
namespace Coulomb

theorem exists_atomic_imsShell_population_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ {u : ℝ}, 0<u → expectedPopulation ψ (imsShell 0 u) ≤ C*screenMass δ u := by
  obtain ⟨C,hC,H⟩ := atomic_annular_second_moment (α:=1/2) (β:=3) (by norm_num) (by norm_num)
  refine ⟨Real.sqrt C,Real.sqrt_nonneg C,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ u hu
  have hb := H S hatom ψ hψ hm hE hstate hδ hu
  have hA : MeasurableSet {x : Space | (1/2:ℝ)*u<‖x‖ ∧ ‖x‖<3*u} :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hsub : imsShell 0 u ⊆ {x : Space | (1/2:ℝ)*u<‖x‖ ∧ ‖x‖<3*u} := by
    intro x hx
    simp only [imsShell,mem_ofPred_eq,sub_zero] at hx ⊢
    constructor <;> linarith [hx.1,hx.2]
  have hp := expectedPopulation_sq_le ψ (measurableSet_imsShell 0 u) hm
  have hmom := localCountSecondMoment_mono ψ hA hsub
  have hw : 0≤ screenMass δ u := by
    dsimp only [screenMass]
    linarith [screenBaseMass_ge_one u, Real.sqrt_nonneg (δ*u)]
  have hs := Real.sq_sqrt hC
  have hprod := mul_nonneg (Real.sqrt_nonneg C) hw
  nlinarith [sq_nonneg (Real.sqrt C*screenMass δ u-expectedPopulation ψ (imsShell 0 u))]

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ExteriorCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

lemma exteriorCut_out_zero {t : ℝ} (ht : 0<t) {x : Space} (hx : ‖x‖≤t) : exteriorCut t 0 x=0 := by
  have H := cutAngle_inner 0 ht (x:=x) (by simpa only [sub_zero] using hx)
  simp [exteriorCut,radialCut,H]

lemma exteriorCut_core_zero {t : ℝ} (ht : 0<t) {x : Space} (hx : 2*t≤‖x‖) : exteriorCut t 1 x=0 := by
  have H := cutAngle_outer 0 ht (x:=x) (by simpa only [sub_zero] using hx)
  simp [exteriorCut,radialCut,H]

lemma exteriorCut_gradient_sum (t : ℝ) (b : Fin 3) (x : Space) :
    (∑ l : Fin 2, (fderiv ℝ (exteriorCut t l) x (EuclideanSpace.single b 1))^2)=
      ∑ l : Fin 2, (fderiv ℝ (radialCut 0 t l) x (EuclideanSpace.single b 1))^2 := by
  simp only [Fin.sum_univ_two,exteriorCut,ite_true,show (1:Fin 2)≠0 by decide,ite_false]
  exact add_comm ..

lemma form_exterior_labelCut_shell {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) {t : ℝ} (ht : 0<t) :
    (∑ p : Fin n → Fin 2, form S (ψ.labelCut (exteriorCut t) (exteriorCut_smooth t)
      (exteriorCut_partition t) (radialCutCoefficient/t) (div_nonneg radialCutCoefficient_pos.le ht.le)
        (exteriorCut_derivative_bound ht) p))≤
      form S ψ+3*(radialCutCoefficient/t)^2*expectedPopulation ψ (imsShell 0 t) := by
  have H := form_radial_labelCut_shell S ψ 0 ht
  rw [form_labelCut] at H ⊢
  simpa only [exteriorCut_gradient_sum] using H

theorem exists_atomic_exterior_IMS_bound : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j,S.position j=0) →
    ∀ ψ : H1Vector n, Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
    ∀ {t : ℝ} (ht : 0<t),
      (∑ p : Fin n → Fin 2, form S (ψ.labelCut (exteriorCut t) (exteriorCut_smooth t)
        (exteriorCut_partition t) (radialCutCoefficient/t) (div_nonneg radialCutCoefficient_pos.le ht.le)
          (exteriorCut_derivative_bound ht) p)) ≤
      form S ψ+C*(screenMass 0 t)/t^2 := by
  obtain ⟨C,hC,H⟩ := exists_atomic_imsShell_population_bound
  refine ⟨3*radialCutCoefficient^2*C,by positivity,?_⟩
  intro J n S hatom ψ hψ hm E hE he t ht
  have hc := H S hatom ψ hψ hm hE (by simpa using he) (le_refl 0) ht
  calc
    _ ≤ form S ψ+3*(radialCutCoefficient/t)^2*expectedPopulation ψ (imsShell 0 t) :=
      form_exterior_labelCut_shell S ψ ht
    _ ≤ form S ψ+3*(radialCutCoefficient/t)^2*(C*screenMass 0 t) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (show 0≤3*(radialCutCoefficient/t)^2 by positivity))
    _ = _ := by ring

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_WeightedDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb
namespace RecordedEnsemble

theorem Conserves.weightedInner_expectation_le {J n : ℕ} {T : RecordedEnsemble n}
    {ψ : H1Vector n} (hT : T.Conserves ψ) (S : Nuclei J) (hatom : ∀ j, S.position j=0)
    {u h : ℝ} (hu : 0<u) (hh : h ≤ u/2) {w : Space → ℝ} (hwm : Measurable w)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∀ y, w y ≤ 1) (hws : ∀ y∉imsShell 0 u, w y=0)
    (hcore : T.CoreSupported (imsShell 0 u)ᶜ) {A : Set Space} (hA : MeasurableSet A)
    (hout : T.OutSupported A) (M : T.InnerEnvelope S h u) :
    potentialForm (weightedInnerField S h w) ψ ≤
      Real.sqrt (localCountSecondMoment ψ A)*T.dataRMS M.value := by
  have hW := weightedInnerField_measurable (n:=n) S h hwm
  have hwabs y : |w y| ≤ 1 := by rw [abs_of_nonneg (hw0 y)]; exact hw1 y
  have hWB := weightedInnerField_abs_le (n:=n) S hatom hu hh hwabs hws
  have HT := hT (weightedInnerField S h w) hW ⟨_,hWB⟩
  simp only [Function.comp_def,weightedInnerField_reindex] at HT
  have Hlocal p : potentialForm (weightedInnerField S h w) (T.vector p) ≤
      (T.out p:ℝ)*sliceExpectation (T.vector p) (M.value p) := by
    have hWBp := weightedInnerField_abs_le (n:=T.out p+T.core p) S hatom hu hh hwabs hws
    have hWp := weightedInnerField_measurable (n:=T.out p+T.core p) S h hwm
    rw [←sliceExpectation_coreConditionalObservable (T.vector p) _ hWp hWBp]
    unfold sliceExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    rw [←integral_const_mul]
    apply integral_mono_ae (coreConditionalObservable_weight_integrable (T.vector p) _ hWp
      (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (div_nonneg (totalCharge_nonneg S) hu.le) (by positivity))) hWBp s)
      ((M.integrable p s).const_mul (T.out p:ℝ))
    filter_upwards [(hcore p).coreSlice s] with x hx
    by_cases hm : mass ((T.vector p).coreSlice s x)=0
    · simp only [hm,zero_mul,mul_zero,le_refl]
    · have H := conditional_weighted_inner_le S hatom (T.vector p) hu hh hwm hw0 hw1 hws s x
        (lt_of_le_of_ne (mass_nonneg _) (Ne.symm hm)) hx.normalized (M.nonneg p s x) (M.dominates p s x)
      have HH := mul_le_mul_of_nonneg_left H (mass_nonneg ((T.vector p).coreSlice s x))
      nlinarith
  have HB := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => Hlocal p)
  rw [HT] at HB
  apply HB.trans
  let R : ℝ := ∑ p, (T.out p:ℝ)*sliceExpectation (T.vector p) (M.value p)
  have hR : 0 ≤ R := Finset.sum_nonneg (fun p _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg (fun s _ => integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (M.nonneg p s x)))))
  have HC := slice_ensemble_count_cauchy T.out T.core T.vector M.value M.integrable M.square_integrable
  have ho := out_square_le hT hA hout
  have hsecond : 0 ≤ ∑ p, sliceExpectation (T.vector p) (fun s x => (M.value p s x)^2) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg
      (fun _ => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
  have HH := HC.trans (mul_le_mul_of_nonneg_right ho hsecond)
  change R^2 ≤ localCountSecondMoment ψ A*_ at HH
  have hN : 0 ≤ localCountSecondMoment ψ A := localCountSecondMoment_nonneg ψ A
  apply (sq_le_sq₀ hR (mul_nonneg (Real.sqrt_nonneg _) (T.dataRMS_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hN,T.dataRMS_sq]
  exact HH

end RecordedEnsemble

theorem atomic_weighted_shell_deletion : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j, S.position j=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E →
    ∀ {t : ℝ}, 0<t → ∀ ell : ℕ, ∀ w : Space → ℝ, Measurable w →
      (∀ y, 0 ≤ w y) → (∀ y, w y ≤ 1) →
      (∀ y∉imsShell 0 ((2:ℝ)^ell*t), w y=0) →
      potentialForm (weightedInnerField S (t/4) w) ψ ≤
        C*(screenMass 0 (t/4))^2*((ell:ℝ)+1)/((2:ℝ)^ell*t) := by
  obtain ⟨Cm,hCm,Hm⟩ := exists_atomic_deletion_envelope
  obtain ⟨Cc,hCc,Hc⟩ := atomic_annular_second_moment (α:=1/2) (β:=4) (by norm_num) (by norm_num)
  refine ⟨Real.sqrt Cc*Cm,mul_nonneg (Real.sqrt_nonneg _) hCm,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate t ht ell w hwm hw0 hw1 hws
  have hu : 0 < (2:ℝ)^ell*t := by positivity
  obtain ⟨T,hT,hf,ho,hcs,hos,hmas,he,M,hM⟩ := Hm S hatom ψ hψ hm hE hstate ht ell
  let A := {x : Space | ((2:ℝ)^ell*t)/2<‖x‖ ∧ ‖x‖<4*((2:ℝ)^ell*t)}
  have hA : MeasurableSet A := ((isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hpow : (1:ℝ) ≤ 2^ell := one_le_pow₀ (by norm_num)
  have htu : t/4 ≤ (2:ℝ)^ell*t := by nlinarith
  have H := hT.weightedInner_expectation_le S hatom hu (show t/4 ≤ ((2:ℝ)^ell*t)/2 by nlinarith)
    hwm hw0 hw1 hws hcs hA hos M
  have Hc1 : localCountSecondMoment ψ A ≤ Cc*(screenMass 0 ((2:ℝ)^ell*t))^2 := by
    simpa only [A,div_eq_mul_inv,one_mul,mul_comm (2:ℝ)⁻¹] using
      Hc S hatom ψ hψ hm hE (by simpa only [add_zero] using hstate) (le_refl 0) hu
  have Hc2 : Real.sqrt (localCountSecondMoment ψ A) ≤ Real.sqrt Cc*screenMass 0 (t/4) := by
    calc
      _ ≤ Real.sqrt (Cc*(screenMass 0 ((2:ℝ)^ell*t))^2) := Real.sqrt_le_sqrt Hc1
      _ = Real.sqrt Cc*screenMass 0 ((2:ℝ)^ell*t) := by
        rw [Real.sqrt_mul hCc,Real.sqrt_sq (screenMass_pos _ _).le]
      _ ≤ _ := mul_le_mul_of_nonneg_left (screenMass_zero_mono (by positivity) htu) (Real.sqrt_nonneg _)
  apply H.trans
  have HH := mul_le_mul Hc2 hM (T.dataRMS_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le)
  exact HH.trans_eq (by ring)

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_TotalDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

theorem atomic_weighted_exterior_deletion : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j, S.position j=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal) ≤ unrestrictedFormBottom S → form S ψ ≤ E →
    ∀ {t : ℝ}, 0<t → ∀ w : Space → ℝ, Measurable w →
      (∀ y, 0 ≤ w y) → (∀ y, w y ≤ 1) →
      (∀ y, ‖y‖<t → w y=0) →
      potentialForm (weightedInnerField S (t/4) w) ψ ≤
        C*(screenMass 0 (t/4))^2/t := by
  obtain ⟨C,hC,H⟩ := atomic_weighted_shell_deletion
  refine ⟨4*C,by positivity,?_⟩
  intro J n S hatom ψ hψ hm E hE hstate t ht w hwm hw0 hw1 hws
  have hwabs y : |w y| ≤ 1 := by rw [abs_of_nonneg (hw0 y)]; exact hw1 y
  have hterm k :
      potentialForm (weightedInnerField S (t/4) (fun y => ∑ j∈Finset.range k, deletionShellWeight t w j y)) ψ ≤
        4*C*(screenMass 0 (t/4))^2/t := by
    have hfun : weightedInnerField (n:=n) S (t/4) (fun y => ∑ j∈Finset.range k, deletionShellWeight t w j y)=
        (fun x => ∑ j∈Finset.range k, weightedInnerField S (t/4) (deletionShellWeight t w j) x) :=
      funext (weightedInnerField_sum_weights S (t/4) (Finset.range k) (deletionShellWeight t w))
    rw [hfun,potentialForm_sum_values]
    · calc
        _ ≤ ∑ j∈Finset.range k, C*(screenMass 0 (t/4))^2*((j:ℝ)+1)/((2:ℝ)^j*t) := by
          apply Finset.sum_le_sum
          intro j hj
          exact H S hatom ψ hψ hm hE hstate ht j (deletionShellWeight t w j)
            (deletionShellWeight_measurable hwm t j) (deletionShellWeight_nonneg hw0 t j)
            (deletionShellWeight_le_one hw1 t j) (deletionShellWeight_supported t w j)
        _ = (C*(screenMass 0 (t/4))^2/t)*∑ j∈Finset.range k, ((j:ℝ)+1)*(1/2:ℝ)^j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [div_pow,one_pow]
          field_simp
        _ ≤ (C*(screenMass 0 (t/4))^2/t)*4 :=
          mul_le_mul_of_nonneg_left (deletion_geometric_sum k) (by positivity)
        _ = _ := by ring
    · intro j hj s
      apply boundedObservable_integrable ψ _ (weightedInnerField_measurable S (t/4)
        (deletionShellWeight_measurable hwm t j))
      have hpow : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
      have hu : 0<(2:ℝ)^j*t := by positivity
      exact weightedInnerField_abs_le S hatom hu (by nlinarith)
        (fun y => by rw [abs_of_nonneg (deletionShellWeight_nonneg hw0 t j y)]; exact deletionShellWeight_le_one hw1 t j y)
        (deletionShellWeight_supported t w j)
  exact le_of_tendsto (weightedInnerField_shell_partial_tendsto S hatom ψ ht hwm hwabs hws)
    (Eventually.of_forall hterm)

end Coulomb
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma particleInnerExterior_measurable {J n : ℕ} (S : Nuclei J) (h t : ℝ) (i : Fin n) :
    Measurable (particleInnerExterior S h t i) := by
  have hp : Measurable (fun x : Configuration n => position x i) := (continuous_position i).measurable
  have hr : Measurable (fun x : Configuration n => restrictedOutPotential x (Metric.ball 0 h) (position x i)) :=
    (restrictedOutPotential_joint_measurable (m:=n) (A:=Metric.ball (0:Space) h) measurableSet_ball).comp
      (f:=fun x : Configuration n => (x,position x i)) (measurable_id.prodMk hp)
  exact Measurable.ite (measurableSet_le measurable_const hp.norm)
    (((attraction_measurable S).comp hp).sub hr) measurable_const

lemma particleInnerExterior_abs_le {J n : ℕ} (S : Nuclei J) (hatom : ∀ j,S.position j=0)
    {h t : ℝ} (ht : 0<t) (hh : h ≤ t/2) (i : Fin n) (x : Configuration n) :
    |particleInnerExterior S h t i x| ≤ totalCharge S/t+(n:ℝ)/(t/2) := by
  let w : Space → ℝ := fun y => if t≤‖y‖ then 1 else 0
  have hw y : |w y| ≤ 1 := by dsimp [w]; split_ifs <;> norm_num
  have hs y (hy : ‖y‖<t) : w y=0 := ite_eq_right (not_le.mpr hy)
  have H := weighted_raw_inner_exterior_abs_le S hatom ht hh hw hs (position x i) x
  simpa only [w,particleInnerExterior,ite_mul,one_mul,zero_mul] using H

lemma particleInnerExterior_reindex {J m n : ℕ} (S : Nuclei J) (h t : ℝ)
    (e : Fin m ≃ Fin n) (i : Fin m) (x : Configuration m) :
    particleInnerExterior S h t (e i) (reindexConfiguration e x)=particleInnerExterior S h t i x := by
  simp only [particleInnerExterior,position_reindex,rawSignedField_reindex]

lemma outerDeletionField_measurable {J m k : ℕ} (S : Nuclei J) (h t : ℝ) :
    Measurable (@outerDeletionField J m k S h t) :=
  Finset.measurable_fun_sum _ (fun index _ => particleInnerExterior_measurable S h t (Fin.castAdd k index))

lemma outerDeletionField_abs_le {J m k : ℕ} (S : Nuclei J) (hatom : ∀ j,S.position j=0)
    {h t : ℝ} (ht : 0<t) (hh : h ≤ t/2) (v : Configuration (m+k)) :
    |outerDeletionField (m:=m) (k:=k) S h t v| ≤ (m:ℝ)*(totalCharge S/t+((m+k:ℕ):ℝ)/(t/2)) := by
  exact (Finset.abs_sum_le_sum_abs ..).trans (by
    have H := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => particleInnerExterior_abs_le S hatom ht hh (Fin.castAdd k i) v)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H)

lemma outerDeletionField_ge_attraction_sub_cross {J m k : ℕ} (S : Nuclei J)
    {h t : ℝ} (hh : h ≤ t) (x : Configuration m) (z : Configuration k)
    (hx : ∀ i, t ≤ ‖position x i‖) :
    nuclearPotential S x-crossPotential x z ≤ outerDeletionField S h t (joinConfiguration m k (x,z)) := by
  have hzero (y : Space) : restrictedOutPotential x (Metric.ball 0 h) y=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply ite_eq_right
    simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hh.trans (hx i)
  have hle (i : Fin m) : restrictedOutPotential z (Metric.ball 0 h) (position x i) ≤
      ∑ j : Fin k, coulombKernel (position x i-position z j) := by
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · exact le_of_eq (coulombKernel_sub_comm ..)
    · exact inv_nonneg.mpr (norm_nonneg _)
  simp only [outerDeletionField,particleInnerExterior,position_join_left,ite_eq_left (hx _),rawSignedField,
    restrictedOutPotential_join,hzero,zero_add,nuclearPotential,crossPotential,←Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun i _ => sub_le_sub_left (hle i) _)

lemma slice_core_form_le_raw_deletion {J m k : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (v : H1Vector (m+k)) {h t : ℝ} (ht : 0<t) (hh : h ≤ t/2)
    (hs : PartlySupported v (outIndexSet m k) {y | t ≤ ‖y‖}) :
    sliceExpectation v (fun s x => form S (v.coreSlice s x).normalized) ≤
      form S v+potentialForm (outerDeletionField (m:=m) (k:=k) S h t) v := by
  have hfield : potentialForm (fun q => nuclearPotential S ((joinConfiguration m k).symm q).1) v-
      potentialForm (fun q => crossPotential ((joinConfiguration m k).symm q).1 ((joinConfiguration m k).symm q).2) v ≤
      potentialForm (outerDeletionField (m:=m) (k:=k) S h t) v := by
    unfold potentialForm
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro s hsu
    rw [←integral_sub (v.outer_nuclear_integrable S s) (v.cross_integrable s)]
    apply integral_mono_ae ((v.outer_nuclear_integrable S s).sub (v.cross_integrable s))
      (boundedObservable_integrable v _ (outerDeletionField_measurable S h t)
        (outerDeletionField_abs_le S hatom ht hh) s)
    filter_upwards [hs s] with q hq
    by_cases hz : v.value s q=0
    · simp [hz]
    · have hx i : t ≤ ‖position ((joinConfiguration m k).symm q).1 i‖ := by
        have he : position q (Fin.castAdd k i)=position ((joinConfiguration m k).symm q).1 i := by
          have H := position_join_left ((joinConfiguration m k).symm q).1 ((joinConfiguration m k).symm q).2 i
          simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] using H
        rw [←he]
        exact by_contra (fun hn => hz (hq _ ⟨i,rfl⟩ hn))
      have H := outerDeletionField_ge_attraction_sub_cross S (show h≤t by linarith)
        ((joinConfiguration m k).symm q).1 ((joinConfiguration m k).symm q).2 hx
      simp only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply] at H
      simpa only [Pi.sub_apply,sub_mul] using mul_le_mul_of_nonneg_right H (sq_nonneg ‖v.value s q‖)
  have hp : 0 ≤ potentialForm (fun q => pairPotential ((joinConfiguration m k).symm q).1) v :=
    Finset.sum_nonneg (fun s _ => integral_nonneg (fun q =>
      mul_nonneg (pairPotential_nonneg_pointwise _) (sq_nonneg _)))
  have hk := outerKinetic_nonneg v
  change (∑ s, ∫ x, mass (v.coreSlice s x)*form S (v.coreSlice s x).normalized) ≤ _
  rw [conditional_core_form_identity]
  change _ ≤ kinetic v-nuclearEnergy S v+pairEnergy v+_
  rw [kinetic_split,nuclearEnergy_split,pairEnergy_split]
  linarith

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_BinaryDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb

lemma coloredDeletion_reindex {J m k n : ℕ} (S : Nuclei J) (h t : ℝ)
    (p : Fin n → Fin 2) (e : Fin (m+k) ≃ Fin n)
    (he0 : ∀ i, p (e (Fin.castAdd k i))=0) (he1 : ∀ i, p (e (Fin.natAdd m i))=1)
    (x : Configuration (m+k)) :
    coloredObservable (particleInnerExterior S h t) p (reindexConfiguration e x)=
      outerDeletionField (m:=m) (k:=k) S h t x := by
  unfold coloredObservable
  rw [←Equiv.sum_comp e (fun i : Fin n => if p i=0 then particleInnerExterior S h t i (reindexConfiguration e x) else 0)]
  simp only [particleInnerExterior_reindex,Fin.sum_univ_add,he0,he1,ite_true,
    show (1:Fin 2)≠0 by decide,ite_false,Finset.sum_const_zero,add_zero,outerDeletionField]

lemma coloredDeletion_labelCut {J n : ℕ} (S : Nuclei J) (hatom : ∀ j,S.position j=0)
    (u : H1Vector n) (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ ∞ (χ l))
    (hp : ∀ y, ∑ l, χ l y^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b y, |fderiv ℝ (χ l) y (EuclideanSpace.single b 1)|≤D)
    {h t : ℝ} (ht : 0<t) (hh : h≤t/2) (hinner : ∀ y, ‖y‖<t → χ 0 y=0) :
    (∑ p : Fin n → Fin 2, potentialForm (coloredObservable (particleInnerExterior S h t) p)
      (u.labelCut χ hχ hp D hD hd p))=
      potentialForm (weightedInnerField S h (fun y => χ 0 y^2)) u := by
  rw [potentialForm_colored_labelCut u χ hχ hp D hD hd _
    (particleInnerExterior_measurable S h t) (show 0≤totalCharge S/t+(n:ℝ)/(t/2) by
      exact add_nonneg (div_nonneg (totalCharge_nonneg S) ht.le) (by positivity))
    (particleInnerExterior_abs_le S hatom ht hh)]
  congr 1
  funext x
  unfold weightedInnerField
  apply Finset.sum_congr rfl
  intro i hi
  unfold particleInnerExterior
  split_ifs with hy
  · rfl
  · simp [hinner _ (lt_of_not_ge hy)]

namespace RecordedEnsemble

theorem binary_localization_deletion {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    (χ : Fin 2 → Space → ℝ) (hχ : ∀ l, ContDiff ℝ ∞ (χ l))
    (hp : ∀ y, ∑ l, χ l y^2=1) (D : ℝ) (hD : 0≤D)
    (hd : ∀ l b y, |fderiv ℝ (χ l) y (EuclideanSpace.single b 1)|≤D)
    {h t : ℝ} (ht : 0<t) (hh : h≤t/2) (hinner : ∀ y, ‖y‖<t → χ 0 y=0)
    (B : Set Space) (hB : ∀ y∉B, χ 1 y=0) :
    ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.CoreSupported B ∧
      T.OutSupported {y | t≤‖y‖} ∧ T.totalMass=mass ψ ∧
      T.totalForm S=∑ p : Fin n → Fin 2, form S (ψ.labelCut χ hχ hp D hD hd p) ∧
      T.totalCoreForm S ≤ T.totalForm S+potentialForm (weightedInnerField S h (fun y => χ 0 y^2)) ψ := by
  have H (p : Fin n → Fin 2) := exists_binary_order p
  choose m k e he0 he1 using H
  let v (p : Fin n → Fin 2) := (ψ.labelCut χ hχ hp D hD hd p).reindex (e p)
  let T : RecordedEnsemble n := {
    index := Fin n → Fin 2
    finite := inferInstance
    out := m
    core := k
    vector := v
    labels := e }
  have hanti (p : Fin n → Fin 2) : PartlyAntisymmetric (v p) (coreIndexSet (m p) (k p)) := by
    let K : Set (Fin n) := {i | p i=1}
    have hc := (hψ.partly (Set.univ : Set (Fin n))).labelCut χ hχ hp D hD hd p K
      (Set.subset_univ _) 1 (fun _ h => h)
    exact hc.reindex (e p) (coreIndexSet (m p) (k p)) (by rintro _ ⟨i,rfl⟩; exact he1 p i)
  have hsupp (p : Fin n → Fin 2) (I : Set (Fin (m p+k p))) (l : Fin 2)
      (hi : ∀ i∈I, p (e p i)=l) (C : Set Space) (hC : ∀ y∉C, χ l y=0) :
      PartlySupported (v p) I C := by
    let K : Set (Fin n) := {i | p i=l}
    have hc := labelCut_partlySupported ψ χ hχ hp D hD hd p K l (fun _ h => h) C hC
    exact hc.reindex (e p) I hi
  have hout p : PartlySupported (v p) (outIndexSet (m p) (k p)) {y | t≤‖y‖} :=
    hsupp p _ 0 (by rintro _ ⟨i,rfl⟩; exact he0 p i) _ (fun y hy => hinner y (lt_of_not_ge hy))
  refine ⟨T,?_,hanti,?_,hout,?_,?_,?_⟩
  · intro W hW hbound
    dsimp [T,v]
    simp only [potentialForm_reindex]
    obtain ⟨M,hM⟩ := hbound
    exact potentialForm_labelCut ψ χ hχ hp D hD hd W hW hM
  · intro p
    exact hsupp p (coreIndexSet (m p) (k p)) 1 (by rintro _ ⟨i,rfl⟩; exact he1 p i) B hB
  · dsimp [totalMass,T,v]
    simp only [mass_reindex]
    exact mass_labelCut ψ χ hχ hp D hD hd
  · dsimp [totalForm,T,v]
    simp only [form_reindex]
  · have hc p := slice_core_form_le_raw_deletion S hatom (v p) ht hh (hout p)
    have he p : potentialForm (outerDeletionField (m:=m p) (k:=k p) S h t) (v p)=
        potentialForm (coloredObservable (particleInnerExterior S h t) p)
          (ψ.labelCut χ hχ hp D hD hd p) := by
      have hf : outerDeletionField (m:=m p) (k:=k p) S h t=
          coloredObservable (particleInnerExterior S h t) p ∘ reindexConfiguration (e p) := by
        funext x
        exact (coloredDeletion_reindex S h t p (e p) (he0 p) (he1 p) x).symm
      rw [hf]
      exact potentialForm_reindex _ _ _
    have hu := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => hc p)
    simp only [Finset.sum_add_distrib,he,coloredDeletion_labelCut S hatom ψ χ hχ hp D hD hd ht hh hinner] at hu
    exact hu

end RecordedEnsemble
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_CoreBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology ContDiff
noncomputable section
namespace Coulomb
namespace RecordedEnsemble

theorem atomic_zero_offset_core_deletion_oai : ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ j,S.position j=0) →
    ∀ ψ : H1Vector n, Antisymmetric ψ → mass ψ=1 →
    ∀ {E : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E →
    ∀ {t : ℝ}, 0<t → ∃ T : RecordedEnsemble n,
      T.Conserves ψ ∧ T.CoreFermionic ∧ T.CoreSupported {y | ‖y‖<2*t} ∧
      T.OutSupported {y | t≤‖y‖} ∧ T.totalMass=1 ∧
      T.totalCoreForm S ≤ E+C*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2) := by
  obtain ⟨Ci,hCi,Hi⟩ := exists_atomic_exterior_IMS_bound
  obtain ⟨Ca,hCa,Ha⟩ := atomic_weighted_exterior_deletion
  refine ⟨Ci+Ca,add_nonneg hCi hCa,?_⟩
  intro J n S hatom ψ hψ hm E hE he t ht
  have hinner y (hy : ‖y‖<t) : exteriorCut t 0 y=0 := exteriorCut_out_zero ht hy.le
  have hcore y (hy : y∉{y | ‖y‖<2*t}) : exteriorCut t 1 y=0 :=
    exteriorCut_core_zero ht (le_of_not_gt hy)
  obtain ⟨T,hT,hF,hS,hO,hM,hform,hcoreform⟩ := binary_localization_deletion S hatom ψ hψ
    (exteriorCut t) (exteriorCut_smooth t) (exteriorCut_partition t)
    (radialCutCoefficient/t) (div_nonneg radialCutCoefficient_pos.le ht.le)
    (exteriorCut_derivative_bound ht) ht (by linarith : t/4≤t/2)
    hinner {y | ‖y‖<2*t} hcore
  refine ⟨T,hT,hF,hS,hO,by simpa only [hm] using hM,?_⟩
  have hweight y : exteriorCut t 0 y^2≤1 := by
    have H := exteriorCut_partition t y
    simp only [Fin.sum_univ_two] at H
    nlinarith [sq_nonneg (exteriorCut t 1 y)]
  have ha := Ha S hatom ψ hψ hm hE he ht (fun y => exteriorCut t 0 y^2)
    ((exteriorCut_smooth t 0).continuous.measurable.pow_const 2) (fun y => sq_nonneg _) hweight
    (fun y hy => by simp only [hinner y hy,zero_pow (by decide : 2≠0)])
  have hi := Hi S hatom ψ hψ hm hE he ht
  rw [←hform] at hi
  have h1 : 0≤(screenMass 0 (t/4))^2/t := div_nonneg (sq_nonneg _) ht.le
  have h2 : 0 ≤ screenMass 0 t/t^2 := div_nonneg (screenMass_pos _ _).le (sq_nonneg _)
  calc
    T.totalCoreForm S ≤ T.totalForm S+potentialForm (weightedInnerField S (t/4) (fun y => exteriorCut t 0 y^2)) ψ := hcoreform
    _ ≤ (form S ψ+Ci*screenMass 0 t/t^2)+Ca*(screenMass 0 (t/4))^2/t := add_le_add hi ha
    _ ≤ E+(Ci+Ca)*((screenMass 0 (t/4))^2/t+screenMass 0 t/t^2) := by
      simp only [mul_div_assoc] at *
      nlinarith [mul_nonneg hCi h1,mul_nonneg hCa h2]

end RecordedEnsemble
end Coulomb
end

end

end OAI
end

theorem solution : type_of% @OAI.Coulomb.RecordedEnsemble.atomic_zero_offset_core_deletion_oai := @OAI.Coulomb.RecordedEnsemble.atomic_zero_offset_core_deletion_oai
