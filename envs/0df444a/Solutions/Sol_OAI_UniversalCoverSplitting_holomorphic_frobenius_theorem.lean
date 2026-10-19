-- Prove2me | solution 1 for OAI.UniversalCoverSplitting.holomorphic_frobenius_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:50:05.587288+00:00
-- url     : https://prove2.me/submissions/e9e6a801-d5b1-4b8d-9f72-f1b8641c8cc5

import Mathlib
import Definitions.Def_OAIQWUCS000
import Definitions.Def_OAIQWUCS001
import Theorems.Thm_OAI_UniversalCoverSplitting_exists_holomorphic_local_flow

section
-- module Solutions.OAIQW_UniversalCover.FlowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology
open scoped ContDiff
open Set Metric Filter Topology MeasureTheory
open scoped Interval

open Set Metric Filter Topology
open scoped ContDiff

open Set Metric Filter Topology
open scoped ContDiff

open Set Metric Filter Topology
open scoped ContDiff

open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem exists_holomorphicFlowData (V : C(E,E)) (D : C(E,E →L[ℂ] E))
    {U : Set E} (hU : IsOpen U) (hV : ∀ x ∈ U, HasFDerivAt V (D x) x)
    {p : E} (hp : p ∈ U) : Nonempty (HolomorphicFlowData V D U p) := by
  obtain ⟨O,F,hO,hpO,hF,hFU,hF0,hFt,hFA⟩ := exists_holomorphic_local_flow V D hU hV hp
  exact ⟨⟨O,hO,hpO,F,hF,hFU,hF0,hFt,hFA⟩⟩

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.CommutingFlows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem exists_commutingFlowData (n : ℕ) (V : Fin n → C(E,E))
    (D : Fin n → C(E,E →L[ℂ] E)) {U : Set E} (hU : IsOpen U)
    (hV : ∀ i x, x ∈ U → HasFDerivAt (V i) (D i x) x)
    (hcomm : ∀ i j x, x ∈ U → D j x (V i x) = D i x (V j x))
    {p : E} (hp : p ∈ U) : Nonempty (CommutingFlowData n V D U p) := by
  induction n with
  | zero =>
    refine ⟨⟨U ×ˢ univ,hU.prod isOpen_univ,⟨hp,mem_univ _⟩,Prod.fst,
      contDiff_fst.contDiffOn,fun q hq ↦ hq.1,fun _ _ ↦ rfl,?_,?_⟩⟩
    · intro q hq i
      exact Fin.elim0 i
    · intro A DA hA hcomm q hq
      simp [fderiv_fst]
  | succ n ih =>
    obtain ⟨G⟩ := ih (fun i ↦ V i.castSucc) (fun i ↦ D i.castSucc)
      (fun i ↦ hV i.castSucc) (fun i j ↦ hcomm i.castSucc j.castSucc)
    obtain ⟨H⟩ := exists_holomorphicFlowData (V (Fin.last n)) (D (Fin.last n))
      hU (hV (Fin.last n)) hp
    let pr : E × FlowTimes (n+1) →L[ℂ] E × FlowTimes n :=
      (ContinuousLinearMap.fst ℂ E (FlowTimes (n+1))).prod
        ((trimFlowTimes n).comp (ContinuousLinearMap.snd ℂ E (FlowTimes (n+1))))
    let last : E × FlowTimes (n+1) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (Fin.last n)).comp
        (ContinuousLinearMap.snd ℂ E (FlowTimes (n+1)))
    let c : E × FlowTimes (n+1) → E × ℂ := fun q ↦ (G.map (pr q),last q)
    let O := pr ⁻¹' G.domain ∩ c ⁻¹' H.domain
    let F : E × FlowTimes (n+1) → E := H.map ∘ c
    have hpr : IsOpen (pr ⁻¹' G.domain) := G.isOpen_domain.preimage pr.continuous
    have hc : ContDiffOn ℂ 1 c (pr ⁻¹' G.domain) :=
      (G.contDiff.comp pr.contDiff.contDiffOn (fun _ hq ↦ hq)).prodMk last.contDiff.contDiffOn
    have hO : IsOpen O := hc.continuousOn.isOpen_inter_preimage hpr H.isOpen_domain
    have hbase : (p,0) ∈ O := by
      have hG0 := G.zero p G.base_mem
      constructor
      · simpa [pr] using G.base_mem
      · simpa [c,pr,last,hG0] using H.base_mem
    have hF : ContDiffOn ℂ 1 F O := H.contDiff.comp (hc.mono inter_subset_left)
      (fun q hq ↦ hq.2)
    have hFd (q : E × FlowTimes (n+1)) (hq : q ∈ O) :
        fderiv ℂ F q = (fderiv ℂ H.map (c q)).comp
          (((fderiv ℂ G.map (pr q)).comp pr).prod last) := by
      have hGq := (G.contDiff.contDiffAt (G.isOpen_domain.mem_nhds hq.1)).differentiableAt (by norm_num)
      have hHq := (H.contDiff.contDiffAt (H.isOpen_domain.mem_nhds hq.2)).differentiableAt (by norm_num)
      exact (hHq.hasFDerivAt.comp q ((hGq.hasFDerivAt.comp q pr.hasFDerivAt).prodMk
        last.hasFDerivAt)).fderiv
    refine ⟨⟨O,hO,hbase,F,hF,fun q hq ↦ H.mapsTo hq.2,?_,?_,?_⟩⟩
    · intro x hx
      have hGx : G.map (x,0) = x := G.zero x (by simpa [pr] using hx.1)
      have hHx : (x,0) ∈ H.domain := by simpa [c,pr,last,hGx] using hx.2
      simpa [F,c,pr,last,hGx] using H.zero x hHx
    · intro q hq i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [hFd q hq]
        change (fderiv ℂ H.map (c q))
          ((fderiv ℂ G.map (pr q)) (pr (0,Pi.single (Fin.last n) 1)),
            last (0,Pi.single (Fin.last n) 1)) = _
        have hpr0 : pr (0,Pi.single (Fin.last n) 1) = 0 := by simp [pr]
        have hl1 : last (0,Pi.single (Fin.last n) 1) = 1 := by simp [last]
        rw [hpr0,map_zero,hl1]
        exact H.time (c q) hq.2
      · rw [hFd q hq]
        have hGi := G.time (pr q) hq.1 j
        have hHi := H.preserves (V j.castSucc) (D j.castSucc)
          (hV j.castSucc) (fun x hx ↦ hcomm (Fin.last n) j.castSucc x hx) (c q) hq.2
        change (fderiv ℂ H.map (c q))
          ((fderiv ℂ G.map (pr q)) (pr (0,Pi.single j.castSucc 1)),
            last (0,Pi.single j.castSucc 1)) = _
        have hprj : pr (0,Pi.single j.castSucc 1) = (0,Pi.single j 1) := by simp [pr]
        have hlj : last (0,Pi.single j.castSucc 1) = 0 := by simp [last]
        rw [hprj,hlj,hGi]
        exact hHi
    · intro A DA hA hAC q hq
      rw [hFd q hq]
      have hGA := G.preserves A DA hA (fun i ↦ hAC i.castSucc) (pr q) hq.1
      have hHA := H.preserves A DA hA (hAC (Fin.last n)) (c q) hq.2
      change (fderiv ℂ H.map (c q))
        ((fderiv ℂ G.map (pr q)) (pr (A q.1,0)),last (A q.1,0)) = _
      have hprA : pr (A q.1,0) = (A (pr q).1,0) := by simp [pr]
      have hlA : last (A q.1,0) = 0 := by simp [last]
      rw [hprA,hlA,hGA]
      exact hHA

end UniversalCoverSplitting

open Set Filter Topology Metric Complex
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

variable [CompleteSpace F]

theorem finite_holomorphic_contDiffOn_one [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ 1 f U := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from by simp, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨hf,by simp,?_⟩
  rw [contDiffOn_zero]
  intro p hp
  apply ContinuousAt.continuousWithinAt
  rw [continuousAt_clm_apply]
  exact continuousAt_directional_fderiv hU hf hp

end UniversalCoverSplitting

open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem continuous_radialClamp (p : E) {r : ℝ} (hr : 0 < r) :
    Continuous (radialClamp p r) := by
  have hn (x : E) : max r ‖x-p‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))
  unfold radialClamp
  exact continuous_const.add ((continuous_const.div
    (continuous_const.max (continuous_id.sub continuous_const).norm) hn).smul
      (continuous_id.sub continuous_const))

 theorem radialClamp_eq_self_of_mem_closedBall {p x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ closedBall p r) : radialClamp p r x = x := by
  rw [mem_closedBall,dist_eq_norm] at hx
  simp [radialClamp,max_eq_left hx,div_self (ne_of_gt hr)]

 theorem radialClamp_mem_closedBall (p x : E) {r : ℝ} (hr : 0 < r) :
    radialClamp p r x ∈ closedBall p r := by
  by_cases hx : x ∈ closedBall p r
  · simpa [radialClamp_eq_self_of_mem_closedBall hr hx] using hx
  · rw [mem_closedBall,dist_eq_norm] at hx ⊢
    have hnx : r < ‖x-p‖ := lt_of_not_ge hx
    have hnorm : 0 < ‖x-p‖ := hr.trans hnx
    rw [radialClamp,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      max_eq_right hnx.le,abs_of_nonneg (div_nonneg hr.le (norm_nonneg _)),
      div_mul_cancel₀ _ (ne_of_gt hnorm)]

 theorem radialClamp_eventuallyEq_id {p x : E} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ ball p r) : radialClamp p r =ᶠ[𝓝 x] id := by
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact radialClamp_eq_self_of_mem_closedBall hr (ball_subset_closedBall hy)

end UniversalCoverSplitting
open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [IsScalarTower ℝ ℂ E] in

theorem holomorphic_continuous_representatives {U : Set E} (hU : IsOpen U)
    {V : E → F} (hV : DifferentiableOn ℂ V U) {p : E} (hp : p ∈ U) :
    ∃ r > 0, ∃ f : C(E,F), ∃ D : C(E,E →L[ℂ] F),
      ball p r ⊆ U ∧ ∀ x ∈ ball p r,
        f x = V x ∧ D x = fderiv ℂ V x ∧ HasFDerivAt f (D x) x := by
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let r := d/2
  have hr : 0 < r := half_pos hd
  have hcU : closedBall p r ⊆ U :=
    (closedBall_subset_ball (by dsimp [r]; linarith : r < d)).trans hdU
  have hclamp := continuous_radialClamp p hr
  have hm (x : E) : radialClamp p r x ∈ U := hcU (radialClamp_mem_closedBall p x hr)
  have hDV := (finite_holomorphic_contDiffOn_one hU hV).continuousOn_fderiv_of_isOpen hU le_rfl
  let f : C(E,F) := ⟨V ∘ radialClamp p r,
    hV.continuousOn.comp_continuous hclamp (fun x ↦ hm x)⟩
  let D : C(E,E →L[ℂ] F) := ⟨fderiv ℂ V ∘ radialClamp p r,
    hDV.comp_continuous hclamp (fun x ↦ hm x)⟩
  refine ⟨r,hr,f,D,ball_subset_closedBall.trans hcU,?_⟩
  intro x hx
  have hid := radialClamp_eq_self_of_mem_closedBall hr (ball_subset_closedBall hx)
  have hf : f x = V x := by dsimp [f]; rw [hid]
  have hD : D x = fderiv ℂ V x := by dsimp [D]; rw [hid]
  refine ⟨hf,hD,?_⟩
  rw [hD]
  apply (hV.differentiableAt (hU.mem_nhds (hcU (ball_subset_closedBall hx)))).hasFDerivAt.congr_of_eventuallyEq
  filter_upwards [radialClamp_eventuallyEq_id hr hx] with y hy
  change V (radialClamp p r y) = V y
  rw [hy]; rfl

end UniversalCoverSplitting

open Set Metric Filter Topology

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem finite_holomorphic_representatives {ι : Type*} [Finite ι]
    {U : Set E} (hU : IsOpen U) (V : ι → E → F)
    (hV : ∀ i, DifferentiableOn ℂ (V i) U) {p : E} (hp : p ∈ U) :
    ∃ O : Set E, IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧
      ∃ f : ι → C(E,F), ∃ D : ι → C(E,E →L[ℂ] F),
        ∀ i x, x ∈ O → f i x = V i x ∧ D i x = fderiv ℂ (V i) x ∧
          HasFDerivAt (f i) (D i x) x := by
  choose r hr f D hball hrep using fun i ↦ holomorphic_continuous_representatives hU (hV i) hp
  let O := U ∩ ⋂ i, ball p (r i)
  refine ⟨O,hU.inter (isOpen_iInter_of_finite fun i ↦ isOpen_ball),
    ⟨hp,mem_iInter.mpr (fun i ↦ mem_ball_self (hr i))⟩,inter_subset_left,f,D,?_⟩
  intro i x hx
  exact hrep i x (mem_iInter.mp hx.2 i)

end UniversalCoverSplitting

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.Frobenius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Filter Topology
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open Set
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Metric Filter Topology
open Set Filter Topology Metric
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem exists_normalized_projection_lift {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    {p : E} (hp : p ∈ U) (L : F →L[ℂ] E) (Q : E →L[ℂ] F)
    (hQL : Q.comp L = ContinuousLinearMap.id ℂ F) (hLQ : L.comp Q = P p) :
    ∃ O : Set E, IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧
      ∃ W : E → F →L[ℂ] E, DifferentiableOn ℂ W O ∧ W p = L ∧
        ∀ x ∈ O,
          (∀ v, P x (W x v) = W x v) ∧
          (∀ v, Q (W x v) = v) ∧
          (∀ v, P x v = v → W x (Q v) = v) := by
  let A : E → F →L[ℂ] F := fun x ↦ Q.comp ((P x).comp L)
  have hQLe (v : F) : Q (L v) = v := by
    simpa using congrArg (fun B : F →L[ℂ] F ↦ B v) hQL
  have hLQe (v : E) : L (Q v) = P p v := by
    simpa using congrArg (fun B : E →L[ℂ] E ↦ B v) hLQ
  have hPL (v : F) : P p (L v) = L v := by rw [← hLQe,hQLe]
  have hAp : A p = ContinuousLinearMap.id ℂ F := by
    ext v
    change Q (P p (L v)) = v
    rw [hPL,hQLe]
  have hA : DifferentiableOn ℂ A U :=
    (differentiableOn_const Q).clm_comp (hP.clm_comp (differentiableOn_const L))
  have hAc := hA.differentiableAt (hU.mem_nhds hp)
  have hAn : ∀ᶠ x in 𝓝 p, IsUnit (A x) := by
    have hn : {B : F →L[ℂ] F | IsUnit B} ∈ 𝓝 (A p) := by
      rw [hAp]
      exact Units.isOpen.mem_nhds isUnit_one
    exact hAc.continuousAt.tendsto.eventually hn
  have hPn : ∀ᶠ x in 𝓝 p, ‖P x - P p‖ < 1 := by
    apply ((hP.differentiableAt (hU.mem_nhds hp)).continuousAt.sub continuousAt_const).norm.eventually_lt continuousAt_const
    simp
  have hn : U ∩ {x | IsUnit (A x) ∧ ‖P x - P p‖ < 1} ∈ 𝓝 p :=
    inter_mem (hU.mem_nhds hp) (hAn.and hPn)
  obtain ⟨O,hO,hOo,hOp⟩ := _root_.mem_nhds_iff.mp hn
  have hOU : O ⊆ U := fun x hx ↦ (hO hx).1
  have hInv (x : E) (hx : x ∈ O) : (A x).IsInvertible := by
    obtain ⟨u,hu⟩ := (hO hx).2.1
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℂ F u,hu⟩
  let W : E → F →L[ℂ] E := fun x ↦ (P x).comp (L.comp (A x).inverse)
  have hAi : DifferentiableOn ℂ (fun x ↦ (A x).inverse) O := by
    intro x hx
    have hInvD := ((hInv x hx).contDiffAt_map_inverse (n := (1 : ℕ∞ω))).differentiableAt (by norm_num)
    exact (hInvD.comp x (hA.differentiableAt (hU.mem_nhds (hOU hx)))).differentiableWithinAt
  have hW : DifferentiableOn ℂ W O :=
    (hP.mono hOU).clm_comp ((differentiableOn_const L).clm_comp hAi)
  have hWp : W p = L := by
    ext v
    simp [W,hAp,hPL]
  refine ⟨O,hOo,hOp,hOU,W,hW,hWp,?_⟩
  intro x hx
  have hWrange (v : F) : P x (W x v) = W x v := hid x (hOU hx) _
  have hQW (v : F) : Q (W x v) = v := (hInv x hx).self_apply_inverse v
  have hinj (v : E) (hv : P x v = v) (hq : Q v = 0) : v = 0 := by
    have hpv : P p v = 0 := by rw [← hLQe,hq,map_zero]
    have hd : (P x - P p) v = v := by simp [hv,hpv]
    have hle := (P x - P p).le_opNorm v
    rw [hd] at hle
    have hs := (hO hx).2.2
    by_contra hv0
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    nlinarith
  refine ⟨hWrange,hQW,?_⟩
  intro v hv
  apply sub_eq_zero.mp
  apply hinj
  · rw [map_sub,hWrange,hv]
  · rw [map_sub,hQW,sub_self]

end UniversalCoverSplitting

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem normalized_lift_commutes {U : Set E} (hU : IsOpen U)
    {P : E → E →L[ℂ] E} (hInt : InvolutiveProjectionOn P U)
    (Q : E →L[ℂ] F) (W : E → F →L[ℂ] E) (hW : DifferentiableOn ℂ W U)
    (hrange : ∀ x ∈ U, ∀ v, P x (W x v) = W x v)
    (hQW : ∀ x ∈ U, ∀ v, Q (W x v) = v)
    (hRet : ∀ x ∈ U, ∀ v, P x v = v → W x (Q v) = v)
    (v w : F) {x : E} (hx : x ∈ U) :
    fderiv ℂ (fun y ↦ W y w) x (W x v) =
      fderiv ℂ (fun y ↦ W y v) x (W x w) := by
  have hd (u : F) : DifferentiableOn ℂ (fun y ↦ W y u) U :=
    hW.clm_apply (differentiableOn_const u)
  have hzero (u : F) : Q.comp (fderiv ℂ (fun y ↦ W y u) x) = 0 := by
    have hdu := (hd u).differentiableAt (hU.mem_nhds hx)
    have hc := Q.hasFDerivAt.comp x hdu.hasFDerivAt
    have hh : HasFDerivAt (fun y ↦ Q (W y u)) (0 : E →L[ℂ] F) x := by
      apply (hasFDerivAt_const u x).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hQW y hy u
    exact hc.unique hh
  have hb := hInt (fun y ↦ W y v) (fun y ↦ W y w) (hd v) (hd w)
    (fun y hy ↦ hrange y hy v) (fun y hy ↦ hrange y hy w) x hx
  have hQb : Q (VectorField.lieBracket ℂ (fun y ↦ W y v) (fun y ↦ W y w) x) = 0 := by
    have hv := congrArg (fun L : E →L[ℂ] F ↦ L (W x w)) (hzero v)
    have hw := congrArg (fun L : E →L[ℂ] F ↦ L (W x v)) (hzero w)
    change Q (fderiv ℂ (fun y ↦ W y v) x (W x w)) = 0 at hv
    change Q (fderiv ℂ (fun y ↦ W y w) x (W x v)) = 0 at hw
    simp only [VectorField.lieBracket,map_sub,hv,hw,sub_self]
  have h := hRet x hx _ hb
  rw [hQb,map_zero] at h
  exact sub_eq_zero.mp h.symm

end UniversalCoverSplitting

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_normalized_commuting_frame {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    (hInt : ∀ O : Set E, IsOpen O → O ⊆ U → InvolutiveProjectionOn P O)
    {p : E} (hp : p ∈ U) (n : ℕ) (L : (Fin n → ℂ) →L[ℂ] E)
    (Q : E →L[ℂ] (Fin n → ℂ))
    (hQL : Q.comp L = ContinuousLinearMap.id ℂ (Fin n → ℂ)) (hLQ : L.comp Q = P p) :
    ∃ O : Set E, IsOpen O ∧ p ∈ O ∧ O ⊆ U ∧
      ∃ W : E → (Fin n → ℂ) →L[ℂ] E,
      ∃ V : Fin n → C(E,E), ∃ D : Fin n → C(E,E →L[ℂ] E),
        W p = L ∧
        (∀ x ∈ O, (∀ v, P x (W x v) = W x v) ∧
          (∀ v, Q (W x v) = v) ∧ (∀ v, P x v = v → W x (Q v) = v)) ∧
        (∀ i x, x ∈ O → V i x = W x (Pi.single i 1) ∧ HasFDerivAt (V i) (D i x) x) ∧
        (∀ i j x, x ∈ O → D j x (V i x) = D i x (V j x)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨N,hNo,hNp,hNU,W,hW,hWp,hWN⟩ :=
    exists_normalized_projection_lift hU P hP hid hp L Q hQL hLQ
  let F : Fin n → E → E := fun i x ↦ W x (Pi.single i 1)
  have hF (i : Fin n) : DifferentiableOn ℂ (F i) N :=
    hW.clm_apply (differentiableOn_const (Pi.single i 1))
  obtain ⟨O,hOo,hOp,hON,V,D,hrep⟩ := finite_holomorphic_representatives hNo F hF hNp
  refine ⟨O,hOo,hOp,hON.trans hNU,W,V,D,hWp,fun x hx ↦ hWN x (hON hx),?_,?_⟩
  · intro i x hx
    exact ⟨(hrep i x hx).1,(hrep i x hx).2.2⟩
  · intro i j x hx
    rw [(hrep j x hx).2.1,(hrep i x hx).2.1,(hrep i x hx).1,(hrep j x hx).1]
    exact normalized_lift_commutes hNo (hInt N hNo hNU) Q W hW
      (fun x hx ↦ (hWN x hx).1) (fun x hx ↦ (hWN x hx).2.1)
      (fun x hx ↦ (hWN x hx).2.2) (Pi.single i 1) (Pi.single j 1) (hON hx)

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace CommutingFlowData
variable {n : ℕ} {V : Fin n → C(E,E)} {D : Fin n → C(E,E →L[ℂ] E)}
  {U : Set E} {p : E} (G : CommutingFlowData n V D U p)

theorem fderiv_initial_zero {x : E} (hx : (x,0) ∈ G.domain) (u : E) :
    fderiv ℂ G.map (x,0) (u,0) = u := by
  have hG := (G.contDiff.contDiffAt (G.isOpen_domain.mem_nhds hx)).differentiableAt (by norm_num)
  let emb : E →L[ℂ] E × FlowTimes n :=
    (ContinuousLinearMap.id ℂ E).prod 0
  have he : HasFDerivAt (fun y ↦ G.map (y,0))
      ((fderiv ℂ G.map (x,0)).comp emb) x := hG.hasFDerivAt.comp x emb.hasFDerivAt
  have hz : (fun y ↦ G.map (y,0)) =ᶠ[𝓝 x] (fun y ↦ y) := by
    have hn := emb.continuous.continuousAt.tendsto.eventually
      (G.isOpen_domain.mem_nhds hx)
    filter_upwards [hn] with y hy
    exact G.zero y hy
  have hid := (hasFDerivAt_id (𝕜 := ℂ) x).congr_of_eventuallyEq hz
  have heq := congrArg (fun A : E →L[ℂ] E ↦ A u) (he.unique hid)
  exact heq

theorem fderiv_time_sum {q : E × FlowTimes n} (hq : q ∈ G.domain) (t : FlowTimes n) :
    fderiv ℂ G.map q (0,t) = ∑ i, t i • V i (G.map q) := by
  let A : FlowTimes n →L[ℂ] E := (fderiv ℂ G.map q).comp
    ((0 : FlowTimes n →L[ℂ] E).prod (ContinuousLinearMap.id ℂ (FlowTimes n)))
  have h := congrArg A (pi_eq_sum_univ' t)
  simpa only [A,map_sum,map_smul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,zero_apply,
    ContinuousLinearMap.id_apply,G.time q hq] using h

theorem fderiv_base (u : E) (t : FlowTimes n) :
    fderiv ℂ G.map (p,0) (u,t) = u + ∑ i, t i • V i p := by
  have hsplit : (u,t) = (u,0) + (0,t) := by simp
  rw [hsplit,map_add,G.fderiv_initial_zero G.base_mem,
    G.fderiv_time_sum G.base_mem,G.zero p G.base_mem]

end CommutingFlowData

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]

theorem transverse_flow_hasFDerivAt {n : ℕ} {V : Fin n → C(E,E)}
    {D : Fin n → C(E,E →L[ℂ] E)} {U : Set E} {p : E}
    (G : CommutingFlowData n V D U p) (L : (FlowTimes n × C) ≃L[ℂ] E)
    (hV : ∀ i, V i p = L (Pi.single i 1,0)) :
    HasFDerivAt (fun q : FlowTimes n × C ↦ G.map (p+L (0,q.2),q.1))
      (L : (FlowTimes n × C) →L[ℂ] E) 0 := by
  let B : (FlowTimes n × C) →L[ℂ] E × FlowTimes n :=
    ((L : (FlowTimes n × C) →L[ℂ] E).comp
      ((0 : (FlowTimes n × C) →L[ℂ] FlowTimes n).prod (ContinuousLinearMap.snd ℂ _ _))).prod
      (ContinuousLinearMap.fst ℂ _ _)
  have hB : HasFDerivAt (fun q : FlowTimes n × C ↦ (p+L (0,q.2),q.1)) B 0 := by
    convert! B.hasFDerivAt.const_add (p,0) using 1
    ext q <;> simp [B]
  have hG := (G.contDiff.contDiffAt (G.isOpen_domain.mem_nhds G.base_mem)).differentiableAt (by norm_num)
  have hG' : HasFDerivAt G.map (fderiv ℂ G.map (p,0))
      ((fun q : FlowTimes n × C ↦ (p+L (0,q.2),q.1)) 0) := by
    change HasFDerivAt G.map (fderiv ℂ G.map (p,0)) (p+L (0 : FlowTimes n × C),0)
    simpa only [map_zero,add_zero] using hG.hasFDerivAt
  have hc := hG'.comp (f := fun q : FlowTimes n × C ↦ (p+L (0,q.2),q.1)) 0 hB
  convert! hc using 1
  apply ContinuousLinearMap.ext
  intro q
  change L q = fderiv ℂ G.map (p,0) (L (0,q.2),q.1)
  rw [G.fderiv_base]
  simp_rw [hV,← map_smul]
  rw [← map_sum,← map_add]
  congr 1
  let J : FlowTimes n →L[ℂ] FlowTimes n × C :=
    (ContinuousLinearMap.id ℂ (FlowTimes n)).prod 0
  have hs := congrArg J (pi_eq_sum_univ' q.1)
  simp only [map_sum,map_smul,J,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply] at hs
  rw [← hs]
  simp

end UniversalCoverSplitting

open Set Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup C] [NormedSpace ℂ C]

theorem transverseFlowParameter_hasFDerivAt {n : ℕ} (p : E)
    (L : (FlowTimes n × C) ≃L[ℂ] E) (q : FlowTimes n × C) :
    HasFDerivAt (transverseFlowParameter p L) (transverseFlowLinear L) q := by
  convert! (transverseFlowLinear L).hasFDerivAt.const_add (p,0) using 1
  ext z <;> simp [transverseFlowLinear]

theorem transverseFlow_time {n : ℕ} {V : Fin n → C(E,E)}
    {D : Fin n → C(E,E →L[ℂ] E)} {U : Set E} {p : E}
    (G : CommutingFlowData n V D U p) (L : (FlowTimes n × C) ≃L[ℂ] E)
    {q : FlowTimes n × C} (hq : transverseFlowParameter p L q ∈ G.domain)
    (t : FlowTimes n) :
    fderiv ℂ (G.map ∘ transverseFlowParameter p L) q (t,0) =
      ∑ i, t i • V i (G.map (transverseFlowParameter p L q)) := by
  have hG := (G.contDiff.contDiffAt (G.isOpen_domain.mem_nhds hq)).differentiableAt (by norm_num)
  have hd := (hG.hasFDerivAt.comp q (transverseFlowParameter_hasFDerivAt p L q)).fderiv
  rw [hd]
  change fderiv ℂ G.map (transverseFlowParameter p L q) (L (0,0),t) = _
  have hL0 : L (0,(0 : C)) = 0 := map_zero L
  rw [hL0,G.fderiv_time_sum hq]

end UniversalCoverSplitting

open Set Filter Topology
open scoped ContDiff

open Set Filter Topology

namespace UniversalCoverSplitting
variable {E F C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup C] [NormedSpace ℂ C]

theorem chart_fderiv_inverse (e : OpenPartialHomeomorph F E)
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    {x : F} (hx : x ∈ e.source) (v : F) (w : E) :
    fderiv ℂ e.symm (e x) (fderiv ℂ e x v) = v ∧
      fderiv ℂ e x (fderiv ℂ e.symm (e x) w) = w := by
  have hd := he.differentiableAt (e.open_source.mem_nhds hx)
  have hdi := hi.differentiableAt (e.open_target.mem_nhds (e.map_source hx))
  have hleft : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hright : (e ∘ e.symm) =ᶠ[𝓝 (e x)] id := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    exact e.right_inv hy
  have hcl := hdi.hasFDerivAt.comp x hd.hasFDerivAt
  have hdr : HasFDerivAt e (fderiv ℂ e x) (e.symm (e x)) := by
    simpa only [e.left_inv hx] using hd.hasFDerivAt
  have hcr := hdr.comp (f := e.symm) (e x) hdi.hasFDerivAt
  have hl := hcl.unique ((hasFDerivAt_id (𝕜 := ℂ) x).congr_of_eventuallyEq hleft)
  have hr := hcr.unique ((hasFDerivAt_id (𝕜 := ℂ) (e x)).congr_of_eventuallyEq hright)
  exact ⟨congrArg (fun A : F →L[ℂ] F ↦ A v) hl,
    congrArg (fun A : E →L[ℂ] E ↦ A w) hr⟩

theorem chart_kernel_eq_projection
    (e : OpenPartialHomeomorph (F × C) E)
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (P : E → E →L[ℂ] E) (W : E → F →L[ℂ] E) (Q : E →L[ℂ] F)
    (hframe : ∀ q ∈ e.source, ∀ t, fderiv ℂ e q (t,0) = W (e q) t)
    (hrange : ∀ y ∈ e.target, ∀ t, P y (W y t) = W y t)
    (hret : ∀ y ∈ e.target, ∀ v, P y v = v → W y (Q v) = v)
    {y : E} (hy : y ∈ e.target) (v : E) :
    P y v = v ↔ (fderiv ℂ e.symm y v).2 = 0 := by
  let q := e.symm y
  have hq : q ∈ e.source := e.map_target hy
  have heq : e q = y := e.right_inv hy
  constructor
  · intro hv
    have hw : fderiv ℂ e q (Q v,0) = v := by
      rw [hframe q hq,heq,hret y hy v hv]
    have hl := (chart_fderiv_inverse e he hi hq (Q v,0) v).1
    rw [heq,hw] at hl
    exact congrArg Prod.snd hl
  · intro hv
    have hr := (chart_fderiv_inverse e he hi hq (0,0) v).2
    rw [heq] at hr
    have ht : fderiv ℂ e.symm y v = ((fderiv ℂ e.symm y v).1,0) := by
      exact Prod.ext rfl hv
    rw [ht,hframe q hq,heq] at hr
    rw [← hr]
    exact hrange y hy _

end UniversalCoverSplitting

open Set Filter Topology
open scoped ContDiff

namespace UniversalCoverSplitting
variable {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]

theorem foliation_chart_from_flows {n : ℕ} {V : Fin n → C(E,E)}
    {D : Fin n → C(E,E →L[ℂ] E)} {U : Set E} {p : E}
    (G : CommutingFlowData n V D U p) (L : (FlowTimes n × C) ≃L[ℂ] E)
    (hV0 : ∀ i, V i p = L (Pi.single i 1,0))
    (P : E → E →L[ℂ] E) (W : E → FlowTimes n →L[ℂ] E) (Q : E →L[ℂ] FlowTimes n)
    (hVW : ∀ i x, x ∈ U → V i x = W x (Pi.single i 1))
    (hrange : ∀ x ∈ U, ∀ t, P x (W x t) = W x t)
    (hret : ∀ x ∈ U, ∀ v, P x v = v → W x (Q v) = v) :
    ∃ e : OpenPartialHomeomorph (FlowTimes n × C) E,
      (0 : FlowTimes n × C) ∈ e.source ∧ e 0 = p ∧ e.target ⊆ U ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.target, ∀ v, P y v = v ↔ (fderiv ℂ e.symm y v).2 = 0 := by
  let η := transverseFlowParameter p L
  have hη : ContDiff ℂ 1 η := by
    exact (contDiff_const.add (L.contDiff.comp (contDiff_const.prodMk contDiff_snd))).prodMk contDiff_fst
  let O := η ⁻¹' G.domain
  have hO : IsOpen O := G.isOpen_domain.preimage hη.continuous
  have hL0 : L (0,(0 : C)) = 0 := map_zero L
  have h0 : (0 : FlowTimes n × C) ∈ O := by
    simpa only [O,mem_preimage,η,transverseFlowParameter,Prod.fst_zero,Prod.snd_zero,
      hL0,add_zero] using G.base_mem
  let f : FlowTimes n × C → E := G.map ∘ η
  have hf : ContDiffOn ℂ 1 f O := G.contDiff.comp hη.contDiffOn (fun _ hq ↦ hq)
  have hd : HasFDerivAt f (L : (FlowTimes n × C) →L[ℂ] E) 0 :=
    transverse_flow_hasFDerivAt G L hV0
  obtain ⟨e,he,hep,heO,hee,hei⟩ := exists_holomorphic_ift_chart hO hf h0 L hd
  have htarget : e.target ⊆ U := by
    intro y hy
    have hx := e.map_target hy
    have hr := G.mapsTo (heO hx)
    change f (e.symm y) ∈ U at hr
    rw [← he,e.right_inv hy] at hr
    exact hr
  have htime (q : FlowTimes n × C) (hq : q ∈ e.source) (t : FlowTimes n) :
      fderiv ℂ e q (t,0) = W (e q) t := by
    rw [he]
    have ht := transverseFlow_time G L (heO hq) t
    change fderiv ℂ f q (t,0) = _ at ht
    rw [ht]
    calc
      (∑ i, t i • V i (f q)) = ∑ i, t i • W (f q) (Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hVW i (f q) (G.mapsTo (heO hq))]
      _ = W (f q) t := by
        simpa only [map_sum,map_smul] using (congrArg (W (f q)) (pi_eq_sum_univ' t)).symm
  refine ⟨e,hep,?_,htarget,hee,hei,?_⟩
  · rw [he]
    change G.map (p+L (0,0),0) = p
    rw [hL0,add_zero]
    exact G.zero p G.base_mem
  · intro y hy v
    exact chart_kernel_eq_projection e (hee.differentiableOn (by norm_num))
      (hei.differentiableOn (by norm_num)) P W Q htime
      (fun x hx ↦ hrange x (htarget hx)) (fun x hx ↦ hret x (htarget hx)) hy v

end UniversalCoverSplitting

open Set

end

end OAI
end

section
-- module Solutions.OAIQW_UniversalCover.ProductCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped ENNReal
open Set Metric
open scoped ENNReal NNReal
open scoped Manifold ENNReal NNReal
open Complex
open Set Metric Filter Topology Complex
open Set Metric Filter Topology MeasureTheory Complex
open scoped Manifold ENNReal
open scoped Manifold
open Set Metric Filter Topology Asymptotics
open Set MeasureTheory
open Set Metric Filter Topology MeasureTheory
open scoped Interval
open Set Filter Topology Metric Complex
open Set Filter Topology Metric
open Set Metric Filter Topology
open scoped ContDiff
open Set
open Set Filter Topology

namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem holomorphic_frobenius_proof {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    (hInt : ∀ O : Set E, IsOpen O → O ⊆ U → InvolutiveProjectionOn P O)
    {p : E} (hp : p ∈ U) {r s : ℕ}
    (hr : Module.finrank ℂ (LinearMap.range (P p).toLinearMap) = r)
    (hs : Module.finrank ℂ (LinearMap.ker (P p).toLinearMap) = s) :
    ∃ e : OpenPartialHomeomorph ((Fin r → ℂ) × (Fin s → ℂ)) E,
      (0 : (Fin r → ℂ) × (Fin s → ℂ)) ∈ e.source ∧ e 0 = p ∧ e.target ⊆ U ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.target, ∀ v, P y v = v ↔ (fderiv ℂ e.symm y v).2 = 0 := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨L,hL⟩ := exists_projection_coordinates (P p) (hid p hp) hr hs
  let J : (Fin r → ℂ) →L[ℂ] ((Fin r → ℂ) × (Fin s → ℂ)) :=
    (ContinuousLinearMap.id ℂ (Fin r → ℂ)).prod 0
  let A : (Fin r → ℂ) →L[ℂ] E := L.toContinuousLinearMap.comp J
  let Q : E →L[ℂ] (Fin r → ℂ) :=
    (ContinuousLinearMap.fst ℂ (Fin r → ℂ) (Fin s → ℂ)).comp L.symm.toContinuousLinearMap
  have hQA : Q.comp A = ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
    ext t
    simp [Q,A,J]
  have hAQ : A.comp Q = P p := by
    apply ContinuousLinearMap.ext
    intro v
    exact hL v
  obtain ⟨O,hOo,hOp,hOU,W,V,D,hWp,hW,hV,hcomm⟩ :=
    exists_normalized_commuting_frame hU P hP hid hInt hp r A Q hQA hAQ
  obtain ⟨G⟩ := exists_commutingFlowData r V D hOo (fun i x hx ↦ (hV i x hx).2) hcomm hOp
  have hV0 (i : Fin r) : V i p = L (Pi.single i 1,0) := by
    rw [(hV i p hOp).1,hWp]
    rfl
  obtain ⟨e,he0,hep,heO,he,hei,hker⟩ := foliation_chart_from_flows G L hV0 P W Q
    (fun i x hx ↦ (hV i x hx).1) (fun x hx ↦ (hW x hx).1)
    (fun x hx ↦ (hW x hx).2.2)
  exact ⟨e,he0,hep,heO.trans hOU,he,hei,hker⟩

theorem holomorphic_frobenius_theorem_oai {U : Set E} (hU : IsOpen U)
    (P : E → E →L[ℂ] E) (hP : DifferentiableOn ℂ P U)
    (hid : ∀ x ∈ U, ∀ v, P x (P x v) = P x v)
    (hInt : ∀ O : Set E, IsOpen O → O ⊆ U → ∀ V W : E → E,
      DifferentiableOn ℂ V O → DifferentiableOn ℂ W O →
      (∀ x ∈ O, P x (V x) = V x) → (∀ x ∈ O, P x (W x) = W x) →
      ∀ x ∈ O, P x (VectorField.lieBracket ℂ V W x) = VectorField.lieBracket ℂ V W x)
    {p : E} (hp : p ∈ U) {r s : ℕ}
    (hr : Module.finrank ℂ (LinearMap.range (P p).toLinearMap) = r)
    (hs : Module.finrank ℂ (LinearMap.ker (P p).toLinearMap) = s) :
    ∃ e : OpenPartialHomeomorph ((Fin r → ℂ) × (Fin s → ℂ)) E,
      (0 : (Fin r → ℂ) × (Fin s → ℂ)) ∈ e.source ∧ e 0 = p ∧ e.target ⊆ U ∧
      ContDiffOn ℂ 1 e e.source ∧ ContDiffOn ℂ 1 e.symm e.target ∧
      ∀ y ∈ e.target, ∀ v, P y v = v ↔ (fderiv ℂ e.symm y v).2 = 0 :=
  holomorphic_frobenius_proof hU P hP hid hInt hp hr hs

end UniversalCoverSplitting

open Set Filter Topology

open Set Filter Topology

open Set Filter Topology
open scoped Manifold ContDiff
open Set Metric
open scoped Manifold
open Set Filter Topology
open scoped Manifold

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.UniversalCoverSplitting.holomorphic_frobenius_theorem_oai.{u_1} := @OAI.UniversalCoverSplitting.holomorphic_frobenius_theorem_oai.{u_1}
