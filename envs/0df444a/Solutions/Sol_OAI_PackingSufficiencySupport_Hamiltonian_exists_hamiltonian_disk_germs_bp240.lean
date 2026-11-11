-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_germs_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:14:18.627223+00:00
-- url     : https://prove2.me/submissions/ca28bb87-3258-4986-9e8f-d9e49a75bb1e

import Mathlib
import Definitions.Def_OAIQ240Bp010
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_planar_embedding_isotopy_bp240
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_hamiltonian_disk_isotopy_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldMoserField
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped NNReal
open MeasureTheory
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem fixedStep_affine {L M : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (Y : C(F,F)) (hY : LipschitzWith M Y) (A : E →L[ℝ] F) (b : F)
    (hXY : ∀ x, Y (b+A x) = A (X x))
    {h : ℝ} (hhX : ‖h‖*L < 1) (hhY : ‖h‖*M < 1) (x : E) :
    fixedStep Y hY h (b+A x) =
      ⟨fun s => b+A (fixedStep X hX h x s),
        continuous_const.add (A.continuous.comp (fixedStep X hX h x).continuous)⟩ := by
  let u := fixedStep X hX h x
  let q : C(Time,F) := ⟨fun s => b+A (u s),continuous_const.add (A.continuous.comp u.continuous)⟩
  change fixedStep Y hY h (b+A x) = q
  apply (picard_contracts Y hY (p := (b+A x,h)) hhY).fixedPoint_unique'
    (localPath_fixed Y hY (p := (b+A x,h)) hhY)
  apply ContinuousMap.ext
  intro s
  have hu := congrArg (fun v : C(Time,E) => v s) (fixedStep_equation X hX hhX x)
  have hq : (fun t : ℝ => extendPath (Y.comp q) t) =
      fun t => A (extendPath (X.comp u) t) := by
    funext t
    exact hXY _
  have hi := A.intervalIntegral_comp_comm (μ := volume)
    ((extendPath (X.comp u)).continuous.intervalIntegrable 0 (s:ℝ))
  change b+A x + h • (∫ t in 0..(s:ℝ), extendPath (Y.comp q) t) = b+A (u s)
  rw [hq,hi]
  change u s = x + h • (∫ t in 0..(s:ℝ), extendPath (X.comp u) t) at hu
  rw [hu,map_add,map_smul]
  simp only [add_assoc]

theorem stepEndpoint_affine {L M : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (Y : C(F,F)) (hY : LipschitzWith M Y) (A : E →L[ℝ] F) (b : F)
    (hXY : ∀ x, Y (b+A x) = A (X x))
    {h : ℝ} (hhX : ‖h‖*L < 1) (hhY : ‖h‖*M < 1) (x : E) :
    stepEndpoint Y hY h (b+A x) = b+A (stepEndpoint X hX h x) := by
  exact congrArg (fun u : C(Time,F) => u ⟨1,by simp⟩)
    (fixedStep_affine X hX Y hY A b hXY hhX hhY x)

end

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem timeStep_fiber {L : ℝ≥0} (X : C(ℝ × (P × E),E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖*L < 1) (t : ℝ) (y : P) (x : E) :
    timeStep (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX) h t (y,x) =
      (y,timeStep (fiberField X y) (fiberField_lipschitz X hX y) h t x) := by
  let A : (ℝ × E) →L[ℝ] (ℝ × (P × E)) :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod
      ((0 : (ℝ × E) →L[ℝ] P).prod (ContinuousLinearMap.snd ℝ ℝ E))
  let b : ℝ × (P × E) := (0,(y,0))
  have hXY : ∀ p, clockField (E := P × E) (parameterField X) (b+A p) =
      A (clockField (E := E) (fiberField X y) p) := by
    intro p
    simp only [b,A,ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd',zero_apply,Prod.mk_add_mk,
      zero_add,add_zero,clockField_apply,parameterField,fiberField,ContinuousMap.coe_mk]
  have he := stepEndpoint_affine (clockField (E := E) (fiberField X y))
    (clockField_lipschitz (E := E) (fiberField X y) (fiberField_lipschitz X hX y)) (clockField (E := P × E) (parameterField X))
    (clockField_lipschitz (E := P × E) (parameterField X) (parameterField_lipschitz X hX)) A b hXY hh hh (t,x)
  have he' := congrArg Prod.snd he
  simpa only [b,A,ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd',zero_apply,Prod.mk_add_mk,
    zero_add,add_zero,timeStep] using he'

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

theorem timeSteps_fiber {L : ℝ≥0} (X : C(ℝ × (P × E),E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) {h : ℝ} (hh : ‖h‖*L < 1) (t : ℝ) (N : ℕ) (y : P) (x : E) :
    timeSteps (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
        (parameterField_smooth X hXs) hh t N (y,x) =
      (y,timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
        (fiberField_smooth X hXs y) hh t N x) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change timeStep (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX) h (t+N*h)
      (timeSteps (E := P × E) (L := L) (parameterField X) (parameterField_lipschitz X hX)
        (parameterField_smooth X hXs) hh t N (y,x)) = _
    rw [ih,timeStep_fiber X hX hh]
    rfl

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SymplecticFamily
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology NNReal
open Set Function

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem timeStep_comp_smooth {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h t : Q → ℝ} {x : Q → E} (hhs : ContDiff ℝ ∞ h)
    (hts : ContDiff ℝ ∞ t) (hxs : ContDiff ℝ ∞ x)
    (hh : ∀ q, ‖h q‖ * L < 1) :
    ContDiff ℝ ∞ (fun q => timeStep X hX (h q) (t q) (x q)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  have hloc := (localPath_smooth (clockField X) (clockField_lipschitz X hX)
    (clockField_smooth X hXs)).contDiffAt ((picardDomain_open L).mem_nhds
      (show ((t q,x q),h q) ∈ picardDomain L from hh q))
  have hc := hloc.comp q ((hts.prodMk hxs).prodMk hhs).contDiffAt
  exact ((ContinuousMap.evalCLM (M := ℝ × E) ℝ (⟨1,by simp⟩ : Time)).contDiff.contDiffAt.comp q hc).snd

theorem timeSteps_variable_smooth {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h t : Q → ℝ} (hhs : ContDiff ℝ ∞ h) (hts : ContDiff ℝ ∞ t)
    (hh : ∀ q, ‖h q‖ * L < 1) (N : ℕ) :
    ContDiff ℝ ∞ (fun p : Q × E => timeSteps X hX hXs (hh p.1) (t p.1) N p.2) ∧
    ContDiff ℝ ∞ (fun p : Q × E => (timeSteps X hX hXs (hh p.1) (t p.1) N).symm p.2) := by
  induction N with
  | zero => exact ⟨contDiff_snd,contDiff_snd⟩
  | succ N ih =>
    constructor
    · exact timeStep_comp_smooth X hX hXs (hhs.comp contDiff_fst)
        ((hts.add (contDiff_const.mul hhs)).comp contDiff_fst) ih.1 (fun p => hh p.1)
    · have hg : ContDiff ℝ ∞ (fun p : Q × E =>
          timeStep X hX (-h p.1) ((t p.1+N*h p.1)+h p.1) p.2) :=
        timeStep_comp_smooth X hX hXs (hhs.neg.comp contDiff_fst)
          (((hts.add (contDiff_const.mul hhs)).add hhs).comp contDiff_fst)
          contDiff_snd (fun p => by simpa only [norm_neg] using hh p.1)
      exact ih.2.comp (contDiff_fst.prodMk hg)


end

open scoped ContDiff Topology NNReal
open Set Function



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology ENNReal
open Set Function MeasureTheory
open Filter
open scoped Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,E) hK.isClosed hKL (n := ⊤)
  have hs : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  exact ⟨χ,χ.contMDiff.contDiff,hL.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hLU,hχ1,hχrange⟩

theorem exists_smooth_compact_extension {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧
      ContDiff ℝ ∞ (fun x => χ x • f x) ∧
      HasCompactSupport (fun x => χ x • f x) ∧
      (∀ᶠ x in 𝓝ˢ K, χ x • f x = f x) := by
  obtain ⟨χ,hχ,hχc,hχU,hχ1,hχrange⟩ := exists_smooth_cutoff hK hU hKU
  have hg : ContDiff ℝ ∞ (fun x => χ x • f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hn : x ∉ tsupport χ := fun h => hx (hχU h)
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn)
      apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp only [hy,zero_smul,Pi.zero_apply]
  have hs : tsupport (fun x => χ x • f x) ⊆ tsupport χ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    apply hx
    change χ x • f x = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  refine ⟨χ,hχ,hχc,hχU,hχrange,hχ1,hg,
    hχc.of_isClosed_subset (isClosed_tsupport _) hs,?_⟩
  filter_upwards [hχ1] with x hx
  rw [hx,one_smul]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_SmoothInverse
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem smooth_inverse_on {f : E → F} {D : Set E} (hD : IsOpen D)
    (hf : ContDiffOn ℝ ∞ f D) (hfi : InjOn f D)
    (hi : ∀ x ∈ D, (fderiv ℝ f x).IsInvertible) :
    IsOpen (f '' D) ∧ ContDiffOn ℝ ∞ (invFunOn f D) (f '' D) ∧
      (∀ x ∈ D, invFunOn f D (f x) = x) ∧
      (∀ y ∈ f '' D, f (invFunOn f D y) = y) := by
  have hlocal (x : E) (hx : x ∈ D) :
      f '' D ∈ 𝓝 (f x) ∧ ContDiffAt ℝ ∞ (invFunOn f D) (f x) := by
    have hfx : ContDiffAt ℝ ∞ f x := (hf x hx).contDiffAt (hD.mem_nhds hx)
    obtain ⟨A,hA⟩ := hi x hx
    have hd : HasFDerivAt f (A : E →L[ℝ] F) x := by
      rw [hA]
      exact (hfx.differentiableAt (by simp)).hasFDerivAt
    let e := hfx.toOpenPartialHomeomorph f hd (by simp)
    have hex : x ∈ e.source := hfx.mem_toOpenPartialHomeomorph_source hd (by simp)
    have heq : (e : E → F) = f := rfl
    let V : Set F := e '' (e.source ∩ D)
    have hV : IsOpen V := e.isOpen_image_of_subset_source (e.open_source.inter hD) inter_subset_left
    have hxV : f x ∈ V := ⟨x,⟨hex,hx⟩,rfl⟩
    have hVD : V ⊆ f '' D := by
      rintro _ ⟨z,hz,rfl⟩
      exact ⟨z,hz.2,rfl⟩
    have hginv : invFunOn f D =ᶠ[𝓝 (f x)] e.symm := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      obtain ⟨z,hz,rfl⟩ := hy
      rw [e.left_inv hz.1]
      exact hfi.leftInvOn_invFunOn hz.2
    have hei : ContDiffAt ℝ ∞ (e.symm : F → E) (f x) :=
      hfx.to_localInverse hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact ⟨Filter.mem_of_superset (hV.mem_nhds hxV) hVD,hei.congr_of_eventuallyEq hginv⟩
  refine ⟨?_,?_,fun x hx => hfi.leftInvOn_invFunOn hx,?_⟩
  · apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact (hlocal x hx).1
  · rintro _ ⟨x,hx,rfl⟩
    exact (hlocal x hx).2.contDiffWithinAt
  · intro y hy
    exact invFunOn_eq hy

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [CompleteSpace Q]

theorem clockGraph_linear_invertible (C : (Q × E) →L[ℝ] E)
    (hC : (C.comp (ContinuousLinearMap.inr ℝ Q E)).IsInvertible) :
    ((ContinuousLinearMap.fst ℝ Q E).prod C).IsInvertible := by
  let A := C.comp (ContinuousLinearMap.inr ℝ Q E)
  let B := (ContinuousLinearMap.fst ℝ Q E).prod C
  have hdecomp (p : Q × E) : C p = C (p.1,0) + A p.2 := by
    change C p = C (p.1,0) + C (0,p.2)
    rw [← map_add]
    congr 1
    ext <;> simp
  have hinj : Injective B := by
    intro p q he
    change (p.1,C p) = (q.1,C q) at he
    have ht := congrArg (fun z : Q × E => z.1) he
    have hx : C p = C q := congrArg (fun z : Q × E => z.2) he
    rw [hdecomp p,hdecomp q,ht] at hx
    have hs : p.2 = q.2 := hC.injective (add_left_cancel hx)
    exact Prod.ext ht hs
  have hsurj : Surjective B := by
    rintro ⟨t,x⟩
    refine ⟨(t,A.inverse (x-C (t,0))),?_⟩
    change (t,C (t,A.inverse (x-C (t,0)))) = (t,x)
    refine Prod.ext (by rfl) ?_
    change C (t,A.inverse (x-C (t,0))) = x
    rw [hdecomp,hC.self_apply_inverse]
    exact add_sub_cancel _ _
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj),rfl⟩

theorem parametric_inverse_on (f : Q × E → E) (hf : ContDiff ℝ ∞ f)
    (D : Set (Q × E)) (hD : IsOpen D)
    (hinj : ∀ t, InjOn (fun x => f (t,x)) {x | (t,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible) :
    ∃ (U : Set (Q × E)) (g : Q × E → E), IsOpen U ∧ ContDiffOn ℝ ∞ g U ∧
      U = (fun p => (p.1,f p)) '' D ∧
      (∀ p ∈ D, (p.1,f p) ∈ U ∧ g (p.1,f p) = p.2) ∧
      (∀ p ∈ U, (p.1,g p) ∈ D ∧ f (p.1,g p) = p.2) := by
  let F : Q × E → Q × E := fun p => (p.1,f p)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hf
  have hFi : InjOn F D := by
    rintro ⟨t,x⟩ hp ⟨s,y⟩ hq he
    have ht : t = s := congrArg (fun z : Q × E => z.1) he
    cases ht
    have hx : f (t,x) = f (t,y) := congrArg (fun z : Q × E => z.2) he
    exact Prod.ext rfl (hinj t hp hq hx)
  have hFd (p : Q × E) : fderiv ℝ F p =
      (ContinuousLinearMap.fst ℝ Q E).prod (fderiv ℝ f p) := by
    exact (hasFDerivAt_fst.prodMk (hf.differentiable (by simp) p).hasFDerivAt).fderiv
  have hFiv (p : Q × E) (hp : p ∈ D) : (fderiv ℝ F p).IsInvertible := by
    rw [hFd]
    apply clockGraph_linear_invertible
    have hd : fderiv ℝ (fun x => f (p.1,x)) p.2 =
        (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ Q E) := by
      exact ((hf.differentiable (by simp) p).hasFDerivAt.comp p.2
        ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))).fderiv
    rw [← hd]
    exact hi p hp
  obtain ⟨hU,hg,hleft,hright⟩ := smooth_inverse_on hD hF.contDiffOn hFi hFiv
  let g : Q × E → E := fun p => (invFunOn F D p).2
  refine ⟨F '' D,g,hU,hg.snd,rfl,?_,?_⟩
  · intro p hp
    refine ⟨⟨p,hp,rfl⟩,?_⟩
    exact congrArg Prod.snd (hleft p hp)
  · intro p hp
    have he := hright p hp
    change ((invFunOn F D p).1,f (invFunOn F D p)) = p at he
    have hfirst := congrArg (fun z : Q × E => z.1) he
    have hmem := invFunOn_mem hp
    have hid : (p.1,g p) = invFunOn F D p := Prod.ext hfirst.symm rfl
    rw [hid]
    exact ⟨hmem,congrArg (fun z : Q × E => z.2) he⟩


end

section
open scoped ContDiff Topology NNReal
open Set Function

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem timeSteps_fiber_variable_smooth {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ → ℝ} (hhs : ContDiff ℝ ∞ h) (hh : ∀ t, ‖h t‖ * L < 1) (N : ℕ) :
    ContDiff ℝ ∞ (fun p : (P × ℝ) × E => timeSteps (fiberField X p.1.1)
      (fiberField_lipschitz X hX p.1.1) (fiberField_smooth X hXs p.1.1) (hh p.1.2) 0 N p.2) ∧
    ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (timeSteps (fiberField X p.1.1)
      (fiberField_lipschitz X hX p.1.1) (fiberField_smooth X hXs p.1.1) (hh p.1.2) 0 N).symm p.2) := by
  let Φ : P → ℝ → E ≃ₜ E := fun y t => timeSteps (fiberField X y)
    (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y) (hh t) 0 N
  let Ψ : ℝ → (P × E) ≃ₜ (P × E) := fun t => timeSteps (parameterField X)
    (parameterField_lipschitz X hX) (parameterField_smooth X hXs) (hh t) 0 N
  have hΨ : ContDiff ℝ ∞ (fun p : ℝ × (P × E) => Ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (P × E) => (Ψ p.1).symm p.2) :=
    timeSteps_variable_smooth (E := P × E) (Q := ℝ) (L := L)
      (parameterField X) (parameterField_lipschitz X hX)
      (parameterField_smooth X hXs) (h := h) (t := fun _ : ℝ => 0)
      hhs contDiff_const hh N
  have he (t : ℝ) (p : P × E) : Ψ t p = (p.1,Φ p.1 t p.2) :=
    timeSteps_fiber X hX hXs (hh t) 0 N p.1 p.2
  have hei (t : ℝ) (p : P × E) : (Ψ t).symm p = (p.1,(Φ p.1 t).symm p.2) := by
    apply (Ψ t).injective
    rw [(Ψ t).apply_symm_apply,he,(Φ p.1 t).apply_symm_apply]
  have hswap : ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (p.1.2,(p.1.1,p.2))) :=
    contDiff_fst.snd.prodMk (contDiff_fst.fst.prodMk contDiff_snd)
  constructor
  · have hhsm := (hΨ.1.comp hswap).snd
    convert hhsm using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact (congrArg Prod.snd (he p.1.2 (p.1.1,p.2))).symm
  · have hhsm := (hΨ.2.comp hswap).snd
    convert hhsm using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact (congrArg Prod.snd (hei p.1.2 (p.1.1,p.2))).symm

theorem exists_parametric_time_isotopy {L : ℝ≥0} (X : C(ℝ × (P × E),E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (S : Set E) (hs : ∀ t y x, x ∉ S → X (t,(y,x)) = 0) :
    ∃ Φ : P → ℝ → E ≃ₜ E,
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y (u : ℝ → E), Continuous u →
        (∀ t, HasDerivAt u (X (t,(y,u t))) t) →
        ∀ t, Φ y t (u 0) = u (Real.smoothTransition t)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (L:ℝ)
  have hN0 : (0:ℝ) < N := L.coe_nonneg.trans_lt hN
  let h : ℝ → ℝ := fun t => Real.smoothTransition t / N
  have hh (t : ℝ) : ‖h t‖ * L < 1 := by
    change ‖Real.smoothTransition t / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le,
      Real.norm_of_nonneg (Real.smoothTransition.nonneg t),div_mul_eq_mul_div]
    apply (div_lt_one hN0).mpr
    exact (mul_le_of_le_one_left L.coe_nonneg (Real.smoothTransition.le_one t)).trans_lt hN
  have hhs : ContDiff ℝ ∞ h := Real.smoothTransition.contDiff.div_const N
  let Φ : P → ℝ → E ≃ₜ E := fun y t => timeSteps (fiberField X y)
    (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y) (hh t) 0 N
  have hΦ := timeSteps_fiber_variable_smooth X hX hXs hhs hh N
  refine ⟨Φ,hΦ.1,hΦ.2,?_,?_,?_⟩
  · intro y
    ext x
    change timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) (hh 0) 0 N x = x
    have hh0 : h 0 = 0 := by simp [h,Real.smoothTransition.zero_of_nonpos (le_refl 0)]
    simpa only [hh0] using timeSteps_zero (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) 0 N x
  · intro y t x hx
    exact timeSteps_of_stationary (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) (hh t) 0 N (fun r => hs r y x hx)
  · intro y u hu hud t
    have heh : (N:ℝ) * h t = Real.smoothTransition t := by dsimp [h]; field_simp
    simpa only [zero_add,heh] using timeSteps_eq_solution (fiberField X y)
      (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y) (hh t) u hu hud 0 N

theorem exists_parametric_isotopy_extension
    (f g : (P × ℝ) × E → E) (hf : ContDiff ℝ ∞ f)
    (U : Set ((P × ℝ) × E)) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (Y : Set P) (hY : IsCompact Y) (K : Set E) (hK : IsCompact K) (W : Set E)
    (hUW : ∀ p ∈ U, p.2 ∈ W)
    (htrack : ∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, ((y,t),f ((y,t),a)) ∈ U)
    (hinv : ∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, g ((y,t),f ((y,t),a)) = a)
    (hstationary : ∀ y t, t ∉ Ioo (0:ℝ) 1 → ∀ a,
      fderiv ℝ f ((y,t),a) ((0,1),0) = 0) :
    ∃ (S : Set E) (Φ : P → ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y ∈ Y, ∀ t a, a ∈ K → Φ y t (f ((y,0),a)) =
        f ((y,Real.smoothTransition t),a)) := by
  let V : (P × ℝ) × E → E := fun p => fderiv ℝ f (p.1,g p) ((0,1),0)
  have hV : ContDiffOn ℝ ∞ V U := by
    have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact (hd.comp_contDiffOn (contDiffOn_fst.prodMk hg)).clm_apply contDiffOn_const
  let C : Set ((P × ℝ) × E) := (fun p : (P × ℝ) × E => (p.1,f p)) ''
    ((Y ×ˢ Icc (0:ℝ) 1) ×ˢ K)
  have hC : IsCompact C := ((hY.prod isCompact_Icc).prod hK).image
    (continuous_fst.prodMk hf.continuous)
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨⟨y,t⟩,a⟩,⟨⟨hy,ht⟩,ha⟩,rfl⟩
    exact htrack y hy t ht a ha
  obtain ⟨χ,_,hχc,hχU,_,hχ1,hVs,hVc,_⟩ :=
    exists_smooth_compact_extension hC hU hCU hV
  let σ : ℝ × (P × E) → (P × ℝ) × E := fun p => ((p.2.1,p.1),p.2.2)
  have hσ : ContDiff ℝ ∞ σ := (contDiff_snd.fst.prodMk contDiff_fst).prodMk contDiff_snd.snd
  let X : C(ℝ × (P × E),E) := ⟨fun p => χ (σ p) • V (σ p),(hVs.comp hσ).continuous⟩
  have hXs : ContDiff ℝ ∞ X := hVs.comp hσ
  let S : Set E := Prod.snd '' tsupport χ
  have hS : IsCompact S := hχc.image continuous_snd
  have hSW : S ⊆ W := by
    rintro _ ⟨p,hp,rfl⟩
    exact hUW p (hχU hp)
  have hs (t : ℝ) (y : P) (x : E) (hx : x ∉ S) : X (t,(y,x)) = 0 := by
    have hn : ((y,t),x) ∉ tsupport χ := fun hp => hx ⟨((y,t),x),hp,rfl⟩
    change χ ((y,t),x) • V ((y,t),x) = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hVc hVs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hσL : LipschitzWith 1 σ := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [NNReal.coe_one,one_mul,σ,Prod.dist_eq]
    exact le_of_eq (by ac_rfl)
  have hXL : LipschitzWith L X := by
    change LipschitzWith L ((fun p => χ p • V p) ∘ σ)
    simpa only [mul_one] using hL.comp hσL
  obtain ⟨Φ,hΦ,hΦi,hΦ0,hΦs,hΦu⟩ := exists_parametric_time_isotopy X hXL hXs S hs
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro y hy t a ha
  apply hΦu y (fun t => f ((y,t),a))
    (hf.continuous.comp ((continuous_const.prodMk continuous_id).prodMk continuous_const))
  intro r
  have hd : HasDerivAt (fun t => f ((y,t),a))
      (fderiv ℝ f ((y,r),a) ((0,1),0)) r :=
    (hf.differentiable (by simp) ((y,r),a)).hasFDerivAt.comp_hasDerivAt r
      (((hasDerivAt_const r y).prodMk (hasDerivAt_id r)).prodMk (hasDerivAt_const r a))
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  by_cases hr : r ∈ Ioo (0:ℝ) 1
  · have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.le⟩
    have he : ((y,r),f ((y,r),a)) ∈ C := ⟨((y,r),a),⟨⟨hy,hr'⟩,ha⟩,rfl⟩
    have hχr : χ ((y,r),f ((y,r),a)) = 1 := hχ1.self_of_nhdsSet _ he
    change χ ((y,r),f ((y,r),a)) •
      fderiv ℝ f ((y,r),g ((y,r),f ((y,r),a))) ((0,1),0) = _
    rw [hχr,one_smul,hinv y hy r hr' a ha]
  · change χ ((y,r),f ((y,r),a)) •
      fderiv ℝ f ((y,r),g ((y,r),f ((y,r),a))) ((0,1),0) = _
    rw [hstationary y r hr,hstationary y r hr,smul_zero]

theorem exists_parametric_embedding_isotopy_extension
    (f : (P × ℝ) × E → E) (hf : ContDiff ℝ ∞ f)
    (D : Set ((P × ℝ) × E)) (hD : IsOpen D)
    (hinj : ∀ q, InjOn (fun x => f (q,x)) {x | (q,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible)
    (Y : Set P) (hY : IsCompact Y) (K : Set E) (hK : IsCompact K) (W : Set E)
    (hDW : ∀ p ∈ D, f p ∈ W)
    (htrack : (Y ×ˢ Icc (0:ℝ) 1) ×ˢ K ⊆ D)
    (hstationary : ∀ y t, t ∉ Ioo (0:ℝ) 1 → ∀ a,
      fderiv ℝ f ((y,t),a) ((0,1),0) = 0) :
    ∃ (S : Set E) (Φ : P → ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y ∈ Y, ∀ t a, a ∈ K → Φ y t (f ((y,0),a)) =
        f ((y,Real.smoothTransition t),a)) := by
  obtain ⟨U,g,hU,hg,himage,hleft,_⟩ := parametric_inverse_on f hf D hD hinj hi
  apply exists_parametric_isotopy_extension f g hf U hU hg Y hY K hK W
  · intro p hp
    rw [himage] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact hDW q hq
  · intro y hy t ht a ha
    exact (hleft ((y,t),a) (htrack ⟨⟨hy,ht⟩,ha⟩)).1
  · intro y hy t ht a ha
    exact (hleft ((y,t),a) (htrack ⟨⟨hy,ht⟩,ha⟩)).2
  · exact hstationary


end

open scoped ContDiff Topology NNReal
open Set Function

theorem smoothTransition_deriv_eq_zero {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have hm : IsLocalMin Real.smoothTransition x := by
      apply IsMinOn.isLocalMin (s := univ) _ (by simp)
      intro y _
      rw [Real.smoothTransition.zero_of_nonpos hx]
      exact Real.smoothTransition.nonneg y
    exact hm.deriv_eq_zero
  · have hm : IsLocalMax Real.smoothTransition x := by
      apply IsMaxOn.isLocalMax (s := univ) _ (by simp)
      intro y _
      rw [Real.smoothTransition.one_of_one_le hx]
      exact Real.smoothTransition.le_one y
    exact hm.deriv_eq_zero



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_FlatIsotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open scoped ComplexConjugate
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SupportedSmoothIsotopy

 theorem mapsTo {W : Set E} (Φ : SupportedSmoothIsotopy W) (t : ℝ) :
    MapsTo (Φ.map t) W W := by
  intro x hx
  by_contra hn
  have hn' : Φ.map t x ∉ Φ.support := fun h => hn (Φ.support_subset h)
  have he := Φ.fixed t (Φ.map t x) hn'
  exact hn (((Φ.map t).injective he).symm ▸ hx)

end SupportedSmoothIsotopy

end
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem parametric_flat_isotopy_stationary {f : (P × ℝ) × E → E} (hf : ContDiff ℝ ∞ f)
    (y : P) (t : ℝ) (ht : t ∉ Ioo (0:ℝ) 1) (x : E) :
    fderiv ℝ (fun p : (P × ℝ) × E => f ((p.1.1,Real.smoothTransition p.1.2),p.2))
      ((y,t),x) ((0,1),0) = 0 := by
  have hst : deriv Real.smoothTransition t = 0 :=
    smoothTransition_deriv_eq_zero (by simpa only [mem_Ioo,not_and_or,not_lt] using ht)
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hs := (hsm.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt
  have hp := hasFDerivAt_fst (𝕜 := ℝ) (p := ((y,t),x))
  have hy := (hasFDerivAt_fst (𝕜 := ℝ) (p := (y,t))).comp ((y,t),x) hp
  have ht' := (hasFDerivAt_snd (𝕜 := ℝ) (p := (y,t))).comp ((y,t),x) hp
  have hi := (hy.prodMk (hs.hasFDerivAt.comp ((y,t),x) ht')).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := ((y,t),x)))
  have hd := ((hf.differentiable (by simp) _).hasFDerivAt.comp ((y,t),x) hi).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  simp [hst]
  exact map_zero _

variable [CompleteSpace P] [FiniteDimensional ℝ P]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_parametric_flat_embedding_extension
    (f : (P × ℝ) × E → E) (hf : ContDiff ℝ ∞ f)
    (O : Set P) (hO : IsOpen O) (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1, InjOn (fun x => f ((y,t),x)) U)
    (hi : ∀ y ∈ O, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      (fderiv ℝ (fun x => f ((y,t),x)) x).IsInvertible)
    (Y : Set P) (hY : IsCompact Y) (hYO : Y ⊆ O)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, f ((y,t),x) ∈ W) :
    ∃ (S : Set E) (Φ : P → ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => Φ p.1.1 p.1.2 p.2) ∧
      ContDiff ℝ ∞ (fun p : (P × ℝ) × E => (Φ p.1.1 p.1.2).symm p.2) ∧
      (∀ y, Φ y 0 = Homeomorph.refl E) ∧
      (∀ y t x, x ∉ S → Φ y t x = x) ∧
      (∀ y ∈ Y, ∀ x ∈ K, Φ y 1 (f ((y,0),x)) = f ((y,1),x)) := by
  let F : (P × ℝ) × E → E := fun p => f ((p.1.1,Real.smoothTransition p.1.2),p.2)
  have hF : ContDiff ℝ ∞ F := hf.comp
    ((contDiff_fst.fst.prodMk (Real.smoothTransition.contDiff.comp contDiff_fst.snd)).prodMk contDiff_snd)
  let D : Set ((P × ℝ) × E) := (fun p => p.1.1) ⁻¹' O ∩ (Prod.snd ⁻¹' U ∩ F ⁻¹' W)
  have hD : IsOpen D := (hO.preimage continuous_fst.fst).inter
    ((hU.preimage continuous_snd).inter (hW.preimage hF.continuous))
  have hstep (t : ℝ) : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ :=
    exists_parametric_embedding_isotopy_extension F hF D hD
      (fun q => by
        intro x hx z hz he
        exact hinj q.1 hx.1 _ (hstep q.2) hx.2.1 hz.2.1 he)
      (fun p hp => hi _ hp.1 _ (hstep p.1.2) _ hp.2.1) Y hY K hK W (fun _ hp => hp.2.2)
      (fun p hp => ⟨hYO hp.1.1,hKU hp.2,htrack _ hp.1.1 _ (hstep p.1.2) _ hp.2⟩)
      (parametric_flat_isotopy_stationary hf)
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro y hy x hx
  simpa only [F,Real.smoothTransition.zero_of_nonpos (le_refl 0),
    Real.smoothTransition.one_of_one_le (le_refl 1)] using hΦf y hy 1 x hx

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CompactEmbeddingIsotopy
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.pull_carrier _root_.OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.pull_radius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem complex_det (A : ℂ →L[ℝ] ℂ) :
    A.det = (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re := by
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix Complex.basisOneI,Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Complex.coe_basisOneI,Complex.coe_basisOneI_repr]
  ring

end
section

variable (P E : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {P E}

variable [CompleteSpace P] [FiniteDimensional ℝ P]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem exists_embedding_family_transport
    (f : P × E → E) (hf : ContDiff ℝ ∞ f)
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ y ∈ O, InjOn (fun x => f (y,x)) U)
    (hi : ∀ y ∈ O, ∀ x ∈ U, (fderiv ℝ (fun x => f (y,x)) x).IsInvertible)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ y ∈ Y, ∀ x ∈ K, f (y,x) ∈ W) :
    ∃ Φ : SupportedSmoothIsotopyFamily P E W,
      ∀ y ∈ Y, ∀ x ∈ K, Φ.map y 1 (f (y₀,x)) = f (y,x) := by
  let a : P × ℝ → P := fun p => (1-p.2) • y₀ + p.2 • p.1
  have ha : ContDiff ℝ ∞ a := ((contDiff_const.sub contDiff_snd).smul contDiff_const).add
    (contDiff_snd.smul contDiff_fst)
  have haO (y : P) (hy : y ∈ O) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : a (y,t) ∈ O :=
    hcO (hYO hy₀) hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have haY (y : P) (hy : y ∈ Y) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : a (y,t) ∈ Y :=
    hcY hy₀ hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  let F : (P × ℝ) × E → E := fun p => f (a p.1,p.2)
  have hF : ContDiff ℝ ∞ F := hf.comp ((ha.comp contDiff_fst).prodMk contDiff_snd)
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ := exists_parametric_flat_embedding_extension
    F hF O hO U W hU hW (fun y hy t ht => hinj _ (haO y hy t ht))
    (fun y hy t ht => hi _ (haO y hy t ht)) Y hY hYO K hK hKU
    (fun y hy t ht x hx => htrack _ (haY y hy t ht) x hx)
  refine ⟨⟨Φ,hΦ,hΦi,hΦ0,S,hS,hSW,hΦs⟩,?_⟩
  intro y hy x hx
  simpa only [F,a,sub_zero,one_smul,zero_smul,add_zero,sub_self,zero_add] using hΦf y hy x hx

end
section

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SupportedSmoothIsotopyFamily

theorem conjugate_image {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (e : E ≃L[ℝ] F) (y : P) (t : ℝ) (S : Set E) :
    (Φ.conjugate e).map y t '' (e '' S) = e '' (Φ.map y t '' S) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨Φ.map y t x,⟨x,hx,rfl⟩,?_⟩
    simp [conjugate]
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨e x,⟨x,hx,rfl⟩,?_⟩
    simp [conjugate]

end SupportedSmoothIsotopyFamily

theorem complex_plane_image_closedBall {R : ℝ} (hR : 0 ≤ R) :
    Complex.equivRealProdCLM '' Metric.closedBall (0:ℂ) R = closedRoundDisk R := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.re^2+z.im^2 ≤ R^2
    have hn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have he := Complex.sq_norm z
    rw [Complex.normSq_apply] at he
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hn 2]
  · intro hx
    change x.1^2+x.2^2 ≤ R^2 at hx
    refine ⟨(⟨x.1,x.2⟩ : ℂ),?_,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,← sq_le_sq₀ (norm_nonneg _) hR]
    have he := Complex.sq_norm (⟨x.1,x.2⟩ : ℂ)
    rw [Complex.normSq_apply] at he
    nlinarith

theorem complex_plane_image_ball {R : ℝ} (hR : 0 ≤ R) :
    Complex.equivRealProdCLM '' Metric.ball (0:ℂ) R = roundDisk R := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    change z.re^2+z.im^2 < R^2
    have hn : ‖z‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have he := Complex.sq_norm z
    rw [Complex.normSq_apply] at he
    nlinarith [(sq_lt_sq₀ (norm_nonneg _) hR).mpr hn]
  · intro hx
    change x.1^2+x.2^2 < R^2 at hx
    refine ⟨(⟨x.1,x.2⟩ : ℂ),?_,rfl⟩
    rw [Metric.mem_ball,dist_zero_right,← sq_lt_sq₀ (norm_nonneg _) hR]
    have he := Complex.sq_norm (⟨x.1,x.2⟩ : ℂ)
    rw [Complex.normSq_apply] at he
    nlinarith

theorem complex_plane_volume_image (S : Set ℂ) :
    volume (Complex.equivRealProdCLM '' S) = volume S := by
  have hh := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
    (Complex.measurableEquivRealProd '' S)
  rw [preimage_image_eq S Complex.measurableEquivRealProd.injective] at hh
  exact hh.symm

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_ParameterRelativeDiskMoser
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.ParametricDiskEmbedding.eval_carrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

open scoped ContDiff Topology
open Set Function

namespace PlanarDiskEmbedding

theorem nested_pull {W : Set ℂ} {D E : PlanarDiskEmbedding} (h : D.Nested E)
    (Φ : SupportedSmoothIsotopy W) : (D.pull Φ).Nested (E.pull Φ) := by
  refine ⟨h.1,?_⟩
  simp only [pull_carrier]
  rw [← (Φ.map 1).symm.image_interior]
  exact image_mono h.2

theorem exists_isotopy (D : PlanarDiskEmbedding) {R : ℝ}
    (hDR : D.radius < R) (hD : D.carrier ⊆ Metric.ball 0 R) :
    ∃ Φ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R),
      Φ.map 1 '' Metric.closedBall 0 D.radius = D.carrier := by
  have h0 : (0:ℂ) ∈ Metric.closedBall 0 D.radius := Metric.mem_closedBall_self D.radius_pos.le
  have HH := exists_compact_planar_embedding_isotopy_bp240 D.map D.smooth D.domain
    (Metric.ball 0 R) D.open_domain Metric.isOpen_ball D.convex_domain (convex_ball (0:ℂ) R)
    D.injective D.nonsingular (Metric.closedBall 0 D.radius) (isCompact_closedBall _ _) h0
    D.subset_domain (Metric.closedBall_subset_ball hDR) (fun x hx => hD ⟨x,hx,rfl⟩)
    (by rw [← complex_det]; exact D.orientation)
  obtain ⟨Φ,hΦ⟩ := HH
  refine ⟨Φ,?_⟩
  apply image_congr
  intro x hx
  exact hΦ x hx

end PlanarDiskEmbedding

namespace SupportedSmoothIsotopy

theorem image_closedBall {R : ℝ} (Φ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R))
    (t : ℝ) : Φ.map t '' Metric.closedBall 0 R = Metric.closedBall 0 R := by
  have hh (Ψ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R)) :
      MapsTo (Ψ.map t) (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro x hx
    by_cases hx' : x ∈ Metric.ball 0 R
    · exact Metric.ball_subset_closedBall (Ψ.mapsTo t hx')
    · rwa [Ψ.fixed t x (fun h => hx' (Ψ.support_subset h))]
  apply Subset.antisymm (image_subset_iff.mpr (hh Φ))
  intro x hx
  exact ⟨(Φ.map t).symm x,hh Φ.symm hx,(Φ.map t).apply_symm_apply x⟩

end SupportedSmoothIsotopy

theorem exists_nested_disk_isotopy (L : List PlanarDiskEmbedding)
    (hL : L.Pairwise PlanarDiskEmbedding.Nested) (R : ℝ)
    (hR : ∀ D ∈ L, D.radius < R)
    (hW : ∀ D ∈ L, D.carrier ⊆ Metric.ball 0 R) :
    ∃ Φ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R),
      ∀ D ∈ L, Φ.map 1 '' Metric.closedBall 0 D.radius = D.carrier := by
  induction hn : L.length using Nat.strong_induction_on generalizing L R with
  | h n ih =>
    cases L with
    | nil => exact ⟨SupportedSmoothIsotopy.refl _,by simp⟩
    | cons D L =>
      obtain ⟨Φ,hΦ⟩ := D.exists_isotopy (hR D (by simp)) (hW D (by simp))
      let L' := L.map (fun E => E.pull Φ)
      have hLL : L.Pairwise PlanarDiskEmbedding.Nested := hL.of_cons
      have hDL : ∀ E ∈ L, D.Nested E := fun _ h => List.rel_of_pairwise_cons hL h
      have hL' : L'.Pairwise PlanarDiskEmbedding.Nested := by
        exact List.Pairwise.map (fun E => E.pull Φ)
          (fun _ _ h => PlanarDiskEmbedding.nested_pull h Φ) hLL
      have hR' : ∀ E ∈ L', E.radius < D.radius := by
        intro E hE
        change E ∈ L.map (fun E => E.pull Φ) at hE
        obtain ⟨E0,hE0,he⟩ := List.mem_map.mp hE
        subst E
        exact (hDL E0 hE0).1
      have hW' : ∀ E ∈ L', E.carrier ⊆ Metric.ball 0 D.radius := by
        intro E hE
        change E ∈ L.map (fun E => E.pull Φ) at hE
        obtain ⟨E0,hE0,he⟩ := List.mem_map.mp hE
        subst E
        rw [PlanarDiskEmbedding.pull_carrier]
        have hsub := image_mono (f := (Φ.map 1).symm) (hDL E0 hE0).2
        rw [(Φ.map 1).symm.image_interior,← hΦ] at hsub
        simpa only [Set.image_image,(Φ.map 1).symm_apply_apply,Set.image_id',
          interior_closedBall'] using hsub
      have hlen : L'.length < n := by
        simp only [L',List.length_map]
        simp only [List.length_cons] at hn
        omega
      obtain ⟨Ψ,hΨ⟩ := ih L'.length hlen L' hL' D.radius hR' hW' rfl
      let Ψ' := Ψ.mono (Metric.ball_subset_ball (hR D (by simp)).le)
      refine ⟨Ψ'.trans Φ,?_⟩
      intro E hE
      rcases List.mem_cons.mp hE with hE | hE
      · subst E
        change (fun x => Φ.map 1 (Ψ.map 1 x)) '' Metric.closedBall 0 D.radius = D.carrier
        rw [← Set.image_image,Ψ.image_closedBall 1,hΦ]
      · have he := hΨ (E.pull Φ) (List.mem_map.mpr ⟨E,hE,rfl⟩)
        simp only [PlanarDiskEmbedding.pull_radius] at he
        change (fun x => Φ.map 1 (Ψ.map 1 x)) '' Metric.closedBall 0 E.radius = E.carrier
        rw [← Set.image_image,he,PlanarDiskEmbedding.pull_carrier]
        simp only [Set.image_image,(Φ.map 1).apply_symm_apply,Set.image_id']



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Layers_ParametricNestedDisks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open Metric
section

variable (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]

variable {P}
namespace ParametricDiskEmbedding
variable {O : Set P}

theorem nested_pull {W : Set ℂ} {Y : Set P} {D E : ParametricDiskEmbedding P O}
    (h : NestedOn Y D E) (Φ : SupportedSmoothIsotopyFamily P ℂ W) :
    NestedOn Y (D.pull Φ) (E.pull Φ) := by
  intro y hy
  simp only [pull_carrier]
  rw [← (Φ.map y 1).symm.image_interior]
  exact image_mono (h y hy)

end ParametricDiskEmbedding

theorem supported_homeomorph_image {E : Type*} [TopologicalSpace E]
    (φ : E ≃ₜ E) (S : Set E) (h : ∀ x ∉ S, φ x = x) : φ '' S = S := by
  apply Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    by_contra hn
    have hh : φ (φ y) = φ y := h (φ y) hn
    apply hn
    rw [φ.injective hh]
    exact hy
  · intro x hx
    refine ⟨φ.symm x,?_,φ.apply_symm_apply x⟩
    by_contra hn
    have hh := h (φ.symm x) hn
    rw [φ.apply_symm_apply] at hh
    exact hn (hh ▸ hx)

variable [CompleteSpace P] [FiniteDimensional ℝ P]

theorem exists_nested_disk_family_transport
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y)
    (L : List (ParametricDiskEmbedding P O))
    (hL : L.Pairwise (ParametricDiskEmbedding.NestedOn Y))
    (W : Set ℂ) (hW : IsOpen W) (hLW : ∀ D ∈ L, ∀ y ∈ Y, D.carrier y ⊆ W) :
    ∃ Φ : SupportedSmoothIsotopyFamily P ℂ W,
      ∀ D ∈ L, ∀ y ∈ Y, Φ.map y 1 '' D.carrier y₀ = D.carrier y := by
  induction hn : L.length using Nat.strong_induction_on generalizing L W with
  | h n ih =>
    cases L with
    | nil => exact ⟨SupportedSmoothIsotopyFamily.refl _,by simp⟩
    | cons D L =>
      obtain ⟨Φ,hΦ⟩ := exists_embedding_family_transport D.map D.smooth O hO hcO
        D.domain W D.open_domain hW D.injective D.nonsingular Y hY hcY hYO y₀ hy₀
        (Metric.closedBall 0 D.radius) (isCompact_closedBall _ _) D.subset_domain
        (fun y hy x hx => hLW D (by simp) y hy ⟨x,hx,rfl⟩)
      have hΦim (y : P) (hy : y ∈ Y) : Φ.map y 1 '' D.carrier y₀ = D.carrier y := by
        rw [ParametricDiskEmbedding.carrier,ParametricDiskEmbedding.carrier,Set.image_image]
        exact image_congr (hΦ y hy)
      have hΦfix (x : ℂ) (hx : x ∈ D.carrier y₀) : Φ.map y₀ 1 x = x := by
        obtain ⟨z,hz,rfl⟩ := hx
        exact hΦ y₀ hy₀ z hz
      let L' := L.map (fun E => E.pull Φ)
      have hLL : L.Pairwise (ParametricDiskEmbedding.NestedOn Y) := hL.of_cons
      have hDL : ∀ E ∈ L, ParametricDiskEmbedding.NestedOn Y D E :=
        fun _ h => List.rel_of_pairwise_cons hL h
      have hL' : L'.Pairwise (ParametricDiskEmbedding.NestedOn Y) := by
        exact List.Pairwise.map (fun E => E.pull Φ)
          (fun _ _ h => ParametricDiskEmbedding.nested_pull h Φ) hLL
      have hW' : ∀ E ∈ L', ∀ y ∈ Y, E.carrier y ⊆ interior (D.carrier y₀) := by
        intro E hE y hy
        change E ∈ L.map (fun E => E.pull Φ) at hE
        obtain ⟨E0,hE0,he⟩ := List.mem_map.mp hE
        subst E
        rw [ParametricDiskEmbedding.pull_carrier]
        have hsub := image_mono (f := (Φ.map y 1).symm) (hDL E0 hE0 y hy)
        rw [(Φ.map y 1).symm.image_interior,← hΦim y hy] at hsub
        simpa only [Set.image_image,(Φ.map y 1).symm_apply_apply,Set.image_id'] using hsub
      have hlen : L'.length < n := by
        simp only [L',List.length_map]
        simp only [List.length_cons] at hn
        omega
      obtain ⟨Ψ,hΨ⟩ := ih L'.length hlen L' hL' (interior (D.carrier y₀)) isOpen_interior hW' rfl
      let Ψ' := Ψ.mono (interior_subset.trans (hLW D (by simp) y₀ hy₀))
      refine ⟨Ψ'.trans Φ,?_⟩
      intro E hE y hy
      rcases List.mem_cons.mp hE with hE | hE
      · subst E
        change (fun x => Φ.map y 1 (Ψ.map y 1 x)) '' D.carrier y₀ = D.carrier y
        have hΨim : Ψ.map y 1 '' D.carrier y₀ = D.carrier y₀ :=
          supported_homeomorph_image _ _ (fun x hx => Ψ.fixed y 1 x
            (fun h => hx (interior_subset (Ψ.support_subset h))))
        rw [← Set.image_image,hΨim,hΦim y hy]
      · have he := hΨ (E.pull Φ) (List.mem_map.mpr ⟨E,hE,rfl⟩) y hy
        have hE0 : (E.pull Φ).carrier y₀ = E.carrier y₀ := by
          rw [ParametricDiskEmbedding.pull_carrier]
          calc
            (Φ.map y₀ 1).symm '' E.carrier y₀ = id '' E.carrier y₀ := by
              apply image_congr
              intro x hx
              apply (Φ.map y₀ 1).injective
              rw [(Φ.map y₀ 1).apply_symm_apply]
              exact (hΦfix x (interior_subset (hDL E hE y₀ hy₀ hx))).symm
            _ = E.carrier y₀ := image_id _
        rw [hE0] at he
        change (fun x => Φ.map y 1 (Ψ.map y 1 x)) '' E.carrier y₀ = E.carrier y
        rw [← Set.image_image,he,ParametricDiskEmbedding.pull_carrier]
        simp only [Set.image_image,(Φ.map y 1).apply_symm_apply,Set.image_id']

theorem exists_ordinary_nested_disk_family
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y)
    (L : List (ParametricDiskEmbedding P O))
    (hL : L.Pairwise (ParametricDiskEmbedding.NestedOn Y))
    (hr : L.Pairwise (fun D E => E.radius < D.radius))
    (R : ℝ) (hR : ∀ D ∈ L, D.radius < R)
    (hLW : ∀ D ∈ L, ∀ y ∈ Y, D.carrier y ⊆ Metric.ball 0 R) :
    ∃ Φ : SupportedSmoothIsotopyFamily P ℂ (Metric.ball 0 R),
      ∀ D ∈ L, ∀ y ∈ Y,
        Φ.map y 1 '' Metric.closedBall 0 D.radius = D.carrier y := by
  let L₀ := L.map (fun D => D.eval y₀ (hYO hy₀))
  have hL₀ : L₀.Pairwise PlanarDiskEmbedding.Nested := by
    apply List.Pairwise.map _ _ (hr.and hL)
    intro D E h
    exact ⟨h.1,h.2 y₀ hy₀⟩
  have hR₀ : ∀ D ∈ L₀, D.radius < R := by
    intro D hD
    change D ∈ L.map _ at hD
    obtain ⟨E,hE,he⟩ := List.mem_map.mp hD
    subst D
    exact hR E hE
  have hW₀ : ∀ D ∈ L₀, D.carrier ⊆ Metric.ball 0 R := by
    intro D hD
    change D ∈ L.map _ at hD
    obtain ⟨E,hE,he⟩ := List.mem_map.mp hD
    subst D
    exact hLW E hE y₀ hy₀
  obtain ⟨Φ₀,hΦ₀⟩ := exists_nested_disk_isotopy L₀ hL₀ R hR₀ hW₀
  obtain ⟨Ψ,hΨ⟩ := exists_nested_disk_family_transport O hO hcO Y hY hcY hYO y₀ hy₀
    L hL (Metric.ball 0 R) Metric.isOpen_ball hLW
  refine ⟨(SupportedSmoothIsotopyFamily.constant Φ₀).trans Ψ,?_⟩
  intro D hD y hy
  have hh := hΦ₀ (D.eval y₀ (hYO hy₀)) (List.mem_map.mpr ⟨D,hD,rfl⟩)
  change Φ₀.map 1 '' Metric.closedBall 0 D.radius = D.carrier y₀ at hh
  change (fun x => Ψ.map y 1 (Φ₀.map 1 x)) '' Metric.closedBall 0 D.radius = D.carrier y
  rw [← Set.image_image,hh,hΨ D hD y hy]

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_nested_disk_family
    (O : Set P) (hO : IsOpen O) (hcO : Convex ℝ O)
    (Y : Set P) (hY : IsCompact Y) (hcY : Convex ℝ Y) (hYO : Y ⊆ O)
    (y₀ : P) (hy₀ : y₀ ∈ Y)
    {m : ℕ} (D : Fin m → ParametricDiskEmbedding P O)
    (hfamily : ∀ ⦃i j⦄, i < j → ParametricDiskEmbedding.NestedOn Y (D i) (D j))
    (hr : StrictAnti (fun i => (D i).radius))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, (D i).radius < R)
    (hDW : ∀ i y, y ∈ Y → (D i).carrier y ⊆ Metric.ball 0 R)
    (harea : ∀ i y, y ∈ Y → volume ((D i).carrier y) =
      volume (Metric.closedBall (0:ℂ) (D i).radius)) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (D i).radius =
        Complex.equivRealProdCLM '' (D i).carrier y := by
  have hL : (List.ofFn D).Pairwise (ParametricDiskEmbedding.NestedOn Y) :=
    List.pairwise_ofFn.mpr hfamily
  have hLr : (List.ofFn D).Pairwise (fun D E => E.radius < D.radius) :=
    List.pairwise_ofFn.mpr hr
  obtain ⟨Φ,hΦ⟩ := exists_ordinary_nested_disk_family O hO hcO Y hY hcY hYO y₀ hy₀
    (List.ofFn D) hL hLr R
    (by intro E hE; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE; exact hrR i)
    (by intro E hE; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hE; exact hDW i)
  let e := Complex.equivRealProdCLM
  let Φreal : SupportedSmoothIsotopyFamily P Plane (roundDisk R) :=
    (Φ.conjugate e).mono (by rw [complex_plane_image_ball hR.le])
  have himage (i : Fin m) (y : P) (hy : y ∈ Y) :
      Φreal.map y 1 '' closedRoundDisk (D i).radius = e '' (D i).carrier y := by
    rw [← complex_plane_image_closedBall (D i).radius_pos.le]
    change (Φ.conjugate e).map y 1 '' (e '' Metric.closedBall 0 (D i).radius) = _
    rw [Φ.conjugate_image e y 1,hΦ (D i) (List.mem_ofFn.mpr ⟨i,rfl⟩) y hy]
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_disk_isotopy_bp240 hR Φreal Y hY
    (fun i => (D i).radius) (fun i => (D i).radius_pos) hrR hr.injective (by
      intro i y hy
      rw [himage i y hy]
      change volume (Complex.equivRealProdCLM '' (D i).carrier y) = _
      rw [complex_plane_volume_image,harea i y hy,
        ← complex_plane_image_closedBall (D i).radius_pos.le,complex_plane_volume_image])
  refine ⟨Ψ,?_⟩
  intro i y hy
  rw [hΨ i y hy,himage i y hy]

end
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_disk_representative
    {Y A : Set P} (hY : IsCompact Y) (hcY : Convex ℝ Y)
    (hA : IsOpen A) (hYA : Y ⊆ A) {r : ℝ} (hr : 0 < r)
    (f : P × ℂ → ℂ) (hf : ContDiffOn ℝ ∞ f (A ×ˢ univ))
    (hi : ∀ y ∈ A, Injective (fun x => f (y,x)))
    (hd : ∀ y ∈ A, ∀ x, (fderiv ℝ (fun x => f (y,x)) x).IsInvertible)
    (ho : ∀ y ∈ A, 0 < (fderiv ℝ (fun x => f (y,x)) 0).det) :
    ∃ O : Set P, IsOpen O ∧ Convex ℝ O ∧ Y ⊆ O ∧ O ⊆ A ∧
      ∃ D : ParametricDiskEmbedding P O, D.radius = r ∧
        ∀ y ∈ O, ∀ x ∈ Metric.closedBall (0:ℂ) r, D.map (y,x) = f (y,x) := by
  let K := Y ×ˢ Metric.closedBall (0:ℂ) r
  have hK : IsCompact K := hY.prod (isCompact_closedBall _ _)
  obtain ⟨χ,_,_,_,_,_,hg,_,he⟩ := exists_smooth_compact_extension hK
    (hA.prod isOpen_univ) (by
      rintro ⟨y,x⟩ ⟨hy,_⟩
      exact ⟨hYA hy,mem_univ _⟩) hf
  let g : P × ℂ → ℂ := fun p => χ p • f p
  obtain ⟨W,hW,hKW,hWe⟩ := mem_nhdsSet_iff_exists.mp he
  obtain ⟨U,V,hU,hV,hYU,hBV,hUV⟩ :=
    generalized_tube_lemma hY (isCompact_closedBall (0:ℂ) r) hW hKW
  obtain ⟨δ,hδ,hδO⟩ := hY.exists_thickening_subset_open (hU.inter hA)
    (subset_inter hYU hYA)
  let O := thickening δ Y
  obtain ⟨ε,hε,hεV⟩ := (isCompact_closedBall (0:ℂ) r).exists_thickening_subset_open hV hBV
  have hball : ball (0:ℂ) (r+ε) ⊆ V := by
    rw [add_comm r ε,← thickening_closedBall hε hr.le (0:ℂ)]
    exact hεV
  have hEq (y : P) (hy : y ∈ O) (x : ℂ) (hx : x ∈ ball (0:ℂ) (r+ε)) :
      g (y,x) = f (y,x) := hWe (hUV ⟨(hδO hy).1,hball hx⟩)
  have hfder (y : P) (hy : y ∈ O) (x : ℂ) (hx : x ∈ ball (0:ℂ) (r+ε)) :
      fderiv ℝ (fun x => g (y,x)) x = fderiv ℝ (fun x => f (y,x)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    exact hEq y hy z hz
  let D : ParametricDiskEmbedding P O := {
      radius := r
      radius_pos := hr
      map := g
      smooth := hg
      domain := ball 0 (r+ε)
      open_domain := isOpen_ball
      convex_domain := convex_ball _ _
      subset_domain := closedBall_subset_ball (by linarith)
      injective := by
        intro y hy x hx z hz heq
        apply hi y (hδO hy).2
        change f (y,x) = f (y,z)
        rw [← hEq y hy x hx,← hEq y hy z hz]
        exact heq
      nonsingular := by
        intro y hy x hx
        rw [hfder y hy x hx]
        exact hd y (hδO hy).2 x
      orientation := by
        intro y hy
        rw [hfder y hy 0 (mem_ball_self (by linarith))]
        exact ho y (hδO hy).2 }
  refine ⟨O,isOpen_thickening,hcY.thickening δ,self_subset_thickening hδ Y,
    fun _ hy => (hδO hy).2,D,rfl,?_⟩
  intro y hy x hx
  exact hEq y hy x (closedBall_subset_ball (by linarith) hx)

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_hamiltonian_disk_germs_bp240_oai {m : ℕ} {Y A : Set P}
    (hY : IsCompact Y) (hcY : Convex ℝ Y) (hA : IsOpen A) (hYA : Y ⊆ A)
    (y₀ : P) (hy₀ : y₀ ∈ Y) (r : Fin m → ℝ) (hr : ∀ i, 0 < r i)
    (hrmono : StrictMono r) (f : Fin m → P × ℂ → ℂ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (A ×ˢ univ))
    (hi : ∀ i y, y ∈ A → Injective (fun x => f i (y,x)))
    (hd : ∀ i y, y ∈ A → ∀ x, (fderiv ℝ (fun x => f i (y,x)) x).IsInvertible)
    (ho : ∀ i y, y ∈ A → 0 < (fderiv ℝ (fun x => f i (y,x)) 0).det)
    (hnest : ∀ ⦃i j⦄, i < j → ∀ y ∈ Y,
      (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆
        interior ((fun x => f j (y,x)) '' Metric.closedBall 0 (r j)))
    (R : ℝ) (hR : 0 < R) (hrR : ∀ i, r i < R)
    (hfit : ∀ i y, y ∈ Y →
      (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) ⊆ Metric.ball 0 R)
    (harea : ∀ i y, y ∈ Y → volume ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i)) =
      volume (Metric.closedBall (0:ℂ) (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) =
        Complex.equivRealProdCLM '' ((fun x => f i (y,x)) '' Metric.closedBall 0 (r i)) := by
  classical
  have hex (i : Fin m) := exists_parametric_disk_representative hY hcY hA hYA (hr i)
    (f i) (hf i) (hi i) (hd i) (ho i)
  choose O hO hcO hYO hOA D hDr hDf using hex
  let U : Set P := ⋂ i, O i
  have hU : IsOpen U := isOpen_iInter_of_finite hO
  have hcU : Convex ℝ U := convex_iInter hcO
  have hYU : Y ⊆ U := by intro y hy; exact mem_iInter.mpr (fun i => hYO i hy)
  have hUO (i : Fin m) : U ⊆ O i := iInter_subset _ i
  let E (i : Fin m) : ParametricDiskEmbedding P U := (D i).restrictParam (hUO i)
  have hEr (i : Fin m) : (E i).radius = r i := hDr i
  have hEc (i : Fin m) (y : P) (hy : y ∈ Y) :
      (E i).carrier y = (fun x => f i (y,x)) '' Metric.closedBall 0 (r i) := by
    change (fun x => (D i).map (y,x)) '' Metric.closedBall 0 (D i).radius = _
    rw [hDr i]
    apply image_congr
    intro x hx
    exact hDf i y (hYO i hy) x hx
  let Erev (i : Fin m) := E i.rev
  obtain ⟨Ψ,hΨ⟩ := exists_hamiltonian_nested_disk_family U hU hcU Y hY hcY hYU y₀ hy₀
    Erev (by
      intro i j hij y hy
      change (E j.rev).carrier y ⊆ interior ((E i.rev).carrier y)
      rw [hEc _ y hy,hEc _ y hy]
      exact hnest (Fin.rev_lt_rev.mpr hij) y hy)
    (by
      intro i j hij
      change (E j.rev).radius < (E i.rev).radius
      rw [hEr,hEr]
      exact hrmono (Fin.rev_lt_rev.mpr hij))
    R hR (by intro i; change (E i.rev).radius < R; rw [hEr]; exact hrR _)
    (by intro i y hy; change (E i.rev).carrier y ⊆ _; rw [hEc _ y hy]; exact hfit _ y hy)
    (by
      intro i y hy
      change volume ((E i.rev).carrier y) = volume (Metric.closedBall (0:ℂ) (E i.rev).radius)
      rw [hEc _ y hy,hEr]
      exact harea _ y hy)
  refine ⟨Ψ,?_⟩
  intro i y hy
  have hh := hΨ i.rev y hy
  change Ψ.isotopy.map y 1 '' closedRoundDisk (E i.rev.rev).radius =
    Complex.equivRealProdCLM '' (E i.rev.rev).carrier y at hh
  simpa only [Fin.rev_rev,hEr,hEc _ y hy] using hh

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_germs_bp240_oai := @OAI.PackingSufficiencySupport.Hamiltonian.exists_hamiltonian_disk_germs_bp240_oai
