-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_planar_embedding_isotopy_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:06:28.90824+00:00
-- url     : https://prove2.me/submissions/70bb6323-ad79-4337-9e37-8861a8a555ff

import Mathlib
import Definitions.Def_OAIQ240Bp007

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem exists_compact_time_isotopy {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (S : Set E) (hs : ∀ t x, x ∉ S → X (t,x) = 0) :
    ∃ Φ : ℝ → E ≃ₜ E,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ (u : ℝ → E), Continuous u →
        (∀ t, HasDerivAt u (X (t,u t)) t) →
        ∀ t, Φ t (u 0) = u (Real.smoothTransition t)) := by
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
  let Φ : ℝ → E ≃ₜ E := fun t => timeSteps X hX hXs (hh t) 0 N
  have hsm := timeSteps_variable_smooth X hX hXs hhs (contDiff_const (c := (0:ℝ))) hh N
  refine ⟨Φ,hsm.1,hsm.2,?_,?_,?_⟩
  · ext x
    change timeSteps X hX hXs (hh 0) 0 N x = x
    have hh0 : h 0 = 0 := by simp [h,Real.smoothTransition.zero_of_nonpos (le_refl 0)]
    simpa only [hh0] using timeSteps_zero X hX hXs 0 N x
  · intro t x hx
    exact timeSteps_of_stationary X hX hXs (hh t) 0 N (fun r => hs r x hx)
  · intro u hu hud t
    have he : (N:ℝ) * h t = Real.smoothTransition t := by dsimp [h]; field_simp
    simpa only [zero_add,he] using timeSteps_eq_solution X hX hXs (hh t) u hu hud 0 N

theorem exists_isotopy_extension
    (f g : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (U : Set (ℝ × E)) (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (K : Set E) (hK : IsCompact K) (W : Set E)
    (hUW : ∀ p ∈ U, p.2 ∈ W)
    (htrack : ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, (t,f (t,a)) ∈ U)
    (hinv : ∀ t ∈ Icc (0:ℝ) 1, ∀ a ∈ K, g (t,f (t,a)) = a)
    (hstationary : ∀ t ∉ Ioo (0:ℝ) 1, ∀ a, fderiv ℝ f (t,a) (1,0) = 0) :
    ∃ (S : Set E) (Φ : ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ t a, a ∈ K → Φ t (f (0,a)) = f (Real.smoothTransition t,a)) := by
  let V : ℝ × E → E := fun p => fderiv ℝ f (p.1,g p) (1,0)
  have hV : ContDiffOn ℝ ∞ V U := by
    have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    exact (hd.comp_contDiffOn (contDiffOn_fst.prodMk hg)).clm_apply contDiffOn_const
  let C : Set (ℝ × E) := (fun p : ℝ × E => (p.1,f p)) '' (Icc (0:ℝ) 1 ×ˢ K)
  have hC : IsCompact C := (isCompact_Icc.prod hK).image (continuous_fst.prodMk hf.continuous)
  have hCU : C ⊆ U := by
    rintro _ ⟨⟨t,a⟩,⟨ht,ha⟩,rfl⟩
    exact htrack t ht a ha
  obtain ⟨χ,hχ,hχc,hχU,_,hχ1,hXs,hXc,_⟩ :=
    exists_smooth_compact_extension hC hU hCU hV
  let X : C(ℝ × E,E) := ⟨fun p => χ p • V p,hXs.continuous⟩
  let S : Set E := Prod.snd '' tsupport χ
  have hS : IsCompact S := hχc.image continuous_snd
  have hSW : S ⊆ W := by
    rintro _ ⟨p,hp,rfl⟩
    exact hUW p (hχU hp)
  have hs (t : ℝ) (x : E) (hx : x ∉ S) : X (t,x) = 0 := by
    have hn : (t,x) ∉ tsupport χ := fun hp => hx ⟨(t,x),hp,rfl⟩
    change χ (t,x) • V (t,x) = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨Φ,hΦ,hΦi,hΦ0,hΦs,hΦu⟩ := exists_compact_time_isotopy X hL hXs S hs
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro t a ha
  apply hΦu (fun t => f (t,a)) (hf.continuous.comp (continuous_id.prodMk continuous_const))
  intro r
  have hd : HasDerivAt (fun t => f (t,a)) (fderiv ℝ f (r,a) (1,0)) r :=
    (hf.differentiable (by simp) (r,a)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r a))
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  by_cases hr : r ∈ Ioo (0:ℝ) 1
  · have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.le⟩
    have he : (r,f (r,a)) ∈ C := ⟨(r,a),⟨hr',ha⟩,rfl⟩
    have hχr : χ (r,f (r,a)) = 1 := hχ1.self_of_nhdsSet _ he
    change χ (r,f (r,a)) • fderiv ℝ f (r,g (r,f (r,a))) (1,0) = _
    rw [hχr,one_smul,hinv r hr' a ha]
  · change χ (r,f (r,a)) • fderiv ℝ f (r,g (r,f (r,a))) (1,0) = _
    rw [hstationary r hr,hstationary r hr,smul_zero]

theorem exists_embedding_isotopy_extension
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (D : Set (ℝ × E)) (hD : IsOpen D)
    (hinj : ∀ t, InjOn (fun x => f (t,x)) {x | (t,x) ∈ D})
    (hi : ∀ p ∈ D, (fderiv ℝ (fun x => f (p.1,x)) p.2).IsInvertible)
    (K : Set E) (hK : IsCompact K) (W : Set E)
    (hDW : ∀ p ∈ D, f p ∈ W)
    (htrack : Icc (0:ℝ) 1 ×ˢ K ⊆ D)
    (hstationary : ∀ t ∉ Ioo (0:ℝ) 1, ∀ a, fderiv ℝ f (t,a) (1,0) = 0) :
    ∃ (S : Set E) (Φ : ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ t a, a ∈ K → Φ t (f (0,a)) = f (Real.smoothTransition t,a)) := by
  obtain ⟨U,g,hU,hg,himage,hleft,_⟩ := parametric_inverse_on f hf D hD hinj hi
  apply exists_isotopy_extension f g hf U hU hg K hK W
  · intro p hp
    rw [himage] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact hDW q hq
  · intro t ht a ha
    exact (hleft (t,a) (htrack ⟨ht,ha⟩)).1
  · intro t ht a ha
    exact (hleft (t,a) (htrack ⟨ht,ha⟩)).2
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
 theorem flat_isotopy_stationary {f : ℝ × E → E} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (ht : t ∉ Ioo (0:ℝ) 1) (x : E) :
    fderiv ℝ (fun p : ℝ × E => f (Real.smoothTransition p.1,p.2)) (t,x) (1,0) = 0 := by
  have hst : deriv Real.smoothTransition t = 0 :=
    smoothTransition_deriv_eq_zero (by simpa only [mem_Ioo,not_and_or,not_lt] using ht)
  have hsm : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hs := (hsm.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) t).hasDerivAt
  have hi := (hs.hasFDerivAt.comp (t,x)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (t,x)))).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (t,x)))
  have hd := ((hf.differentiable (by simp) _).hasFDerivAt.comp (t,x) hi).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  simp [hst]
  exact map_zero _

theorem exists_flat_embedding_extension
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ t ∈ Icc (0:ℝ) 1, InjOn (fun x => f (t,x)) U)
    (hi : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      (fderiv ℝ (fun x => f (t,x)) x).IsInvertible)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, f (t,x) ∈ W) :
    ∃ (S : Set E) (Φ : ℝ → E ≃ₜ E), IsCompact S ∧ S ⊆ W ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      Φ 0 = Homeomorph.refl E ∧
      (∀ t x, x ∉ S → Φ t x = x) ∧
      (∀ x ∈ K, Φ 1 (f (0,x)) = f (1,x)) := by
  let F : ℝ × E → E := fun p => f (Real.smoothTransition p.1,p.2)
  have hF : ContDiff ℝ ∞ F :=
    hf.comp ((Real.smoothTransition.contDiff.comp contDiff_fst).prodMk contDiff_snd)
  let D : Set (ℝ × E) := Prod.snd ⁻¹' U ∩ F ⁻¹' W
  have hD : IsOpen D := (hU.preimage continuous_snd).inter (hW.preimage hF.continuous)
  have hstep (t : ℝ) : Real.smoothTransition t ∈ Icc (0:ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ :=
    exists_embedding_isotopy_extension F hF D hD
      (fun t => (hinj _ (hstep t)).mono (fun _ hx => hx.1))
      (fun p hp => hi _ (hstep p.1) _ hp.1) K hK W (fun _ hp => hp.2)
      (fun p hp => ⟨hKU hp.2,htrack _ (hstep p.1) _ hp.2⟩)
      (flat_isotopy_stationary hf)
  refine ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,?_⟩
  intro x hx
  simpa only [F,Real.smoothTransition.zero_of_nonpos (le_refl 0),
    Real.smoothTransition.one_of_one_le (le_refl 1)] using hΦf 1 x hx

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SmoothlyAmbientRelated

 theorem trans {W K : Set E} {f g h : E → E}
    (hfg : SmoothlyAmbientRelated W K f g) (hgh : SmoothlyAmbientRelated W K g h) :
    SmoothlyAmbientRelated W K f h := by
  obtain ⟨Φ,hΦ⟩ := hfg
  obtain ⟨Ψ,hΨ⟩ := hgh
  refine ⟨Φ.trans Ψ,?_⟩
  intro x hx
  change Ψ.map 1 (Φ.map 1 (f x)) = h x
  rw [hΦ x hx,hΨ x hx]

 theorem symm {W K : Set E} {f g : E → E} (hfg : SmoothlyAmbientRelated W K f g) :
    SmoothlyAmbientRelated W K g f := by
  obtain ⟨Φ,hΦ⟩ := hfg
  refine ⟨Φ.symm,?_⟩
  intro x hx
  change (Φ.map 1).symm (g x) = f x
  rw [← hΦ x hx,(Φ.map 1).symm_apply_apply]

end SmoothlyAmbientRelated

variable [CompleteSpace E] [FiniteDimensional ℝ E]

 theorem smoothlyAmbientRelated_of_path
    (f : ℝ × E → E) (hf : ContDiff ℝ ∞ f)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W)
    (hinj : ∀ t ∈ Icc (0:ℝ) 1, InjOn (fun x => f (t,x)) U)
    (hi : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U,
      (fderiv ℝ (fun x => f (t,x)) x).IsInvertible)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (htrack : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ K, f (t,x) ∈ W) :
    SmoothlyAmbientRelated W K (fun x => f (0,x)) (fun x => f (1,x)) := by
  obtain ⟨S,Φ,hS,hSW,hΦ,hΦi,hΦ0,hΦs,hΦf⟩ :=
    exists_flat_embedding_extension f hf U W hU hW hinj hi K hK hKU htrack
  exact ⟨⟨Φ,hΦ,hΦi,hΦ0,S,hS,hSW,hΦs⟩,hΦf⟩

end
section

universe u
variable {P E F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiff_fixed_integral {f : ℝ × P → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p => ∫ t in (0:ℝ)..1, f (t,p)) := by
  let τ : C(Time,ℝ × P) := ⟨fun t => ((t:ℝ),0),continuous_subtype_val.prodMk continuous_const⟩
  let v : P → C(Time,ℝ × P) := fun p => τ + constantPath (0,p)
  have hv : ContDiff ℝ ∞ v := contDiff_const.add
    ((constantPath (E := ℝ × P)).contDiff.comp (contDiff_const.prodMk contDiff_id))
  let I : C(Time,F) →L[ℝ] F := (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : Time)).comp pathIntegral
  have he : (fun p => ∫ t in (0:ℝ)..1, f (t,p)) =
      fun p => I ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) := by
    funext p
    change _ = ∫ t in (0:ℝ)..1, extendPath ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) t
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [show extendPath ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) t =
      ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) ⟨t,ht⟩ from extendPath_coe _ ⟨t,ht⟩]
    change f (t,p) = f ((t,0)+(0,p))
    simp
  rw [he]
  exact I.contDiff.comp ((postcomp_contDiff hf).comp hv)

 theorem smoothBlowup_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothBlowup f) := by
  unfold smoothBlowup
  apply contDiff_fixed_integral (f := fun q : ℝ × (ℝ × E) =>
    fderiv ℝ f ((q.1*q.2.1) • q.2.2) q.2.2)
  exact ((hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp
    ((contDiff_fst.mul contDiff_snd.fst).smul contDiff_snd.snd)).clm_apply contDiff_snd.snd

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_zero (f : E → F) (x : E) :
    smoothBlowup f (0,x) = fderiv ℝ f 0 x := by
  simp [smoothBlowup]

omit [FiniteDimensional ℝ E] in
 theorem smul_smoothBlowup {f : E → F} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    t • smoothBlowup f (t,x) = f (t • x)-f 0 := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => f ((r*t) • x))
      (t • fderiv ℝ f ((s*t) • x) x) s := by
    simpa only [Function.comp_def,id_eq,one_mul,map_smul] using
      (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
        (((hasDerivAt_id s).mul_const t).smul_const x)
  have hc : Continuous (fun s : ℝ => t • fderiv ℝ f ((s*t) • x) x) :=
    continuous_const.smul (((hf.fderiv_right (m := ∞) (by simp)).continuous.comp
      ((continuous_id.mul continuous_const).smul continuous_const)).clm_apply continuous_const)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_smul,one_mul,zero_mul,zero_smul,smoothBlowup] using hi

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_eq {f : E → F} (hf : ContDiff ℝ ∞ f) {t : ℝ} (ht : t ≠ 0) (x : E) :
    smoothBlowup f (t,x) = t⁻¹ • (f (t • x)-f 0) := by
  rw [← smul_smoothBlowup hf t x,smul_smul,inv_mul_cancel₀ ht,one_smul]

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_injOn {f : E → F} (hf : ContDiff ℝ ∞ f)
    {U : Set E} (hinj : InjOn f U) (hi0 : Injective (fderiv ℝ f 0)) (t : ℝ) :
    InjOn (fun x => smoothBlowup f (t,x)) {x | t • x ∈ U} := by
  intro x hx y hy he
  by_cases ht : t = 0
  · subst t
    simp only [smoothBlowup_zero] at he
    exact hi0 he
  · have h := congrArg (fun z : F => t • z) he
    rw [smul_smoothBlowup hf,smul_smoothBlowup hf,sub_left_inj] at h
    exact (smul_right_injective E ht) (hinj hx hy h)

omit [FiniteDimensional ℝ E] in
 theorem smoothBlowup_hasFDerivAt {f : E → F} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    HasFDerivAt (fun x => smoothBlowup f (t,x)) (fderiv ℝ f (t • x)) x := by
  by_cases ht : t = 0
  · subst t
    simpa only [smoothBlowup_zero,zero_smul] using (fderiv ℝ f 0).hasFDerivAt
  · have he : (fun x => smoothBlowup f (t,x)) = fun x => t⁻¹ • (f (t • x)-f 0) :=
      funext (smoothBlowup_eq hf ht)
    rw [he]
    have hd := (((hf.differentiable (by simp) (t • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul t)).sub_const (f 0)).const_smul t⁻¹
    have hde : t⁻¹ • (fderiv ℝ f (t • x)).comp (t • ContinuousLinearMap.id ℝ E) =
        fderiv ℝ f (t • x) := by
      ext v
      change t⁻¹ • fderiv ℝ f (t • x) (t • v) = fderiv ℝ f (t • x) v
      rw [map_smul,smul_smul,inv_mul_cancel₀ ht,one_smul]
    refine hd.congr_fderiv (Eq.symm ?_)
    · exact hde.symm

end

 theorem realLinear_complex_decomposition (A : ℂ →L[ℝ] ℂ) :
    A = complexPair ((A 1-Complex.I*A Complex.I)/2) ((A 1+Complex.I*A Complex.I)/2) := by
  ext z
  have hz : z = z.re • (1:ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_one,mul_one] using
      (Complex.re_add_im z).symm
  conv_lhs => rw [hz,map_add,map_smul,map_smul]
  simp only [complexPair_apply,Complex.real_smul]
  apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] <;> ring

 theorem complex_decomposition_orientation (A : ℂ →L[ℝ] ℂ) :
    Complex.normSq ((A 1-Complex.I*A Complex.I)/2) -
      Complex.normSq ((A 1+Complex.I*A Complex.I)/2) =
      (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re := by
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

 theorem complexPair_invertible {a b : ℂ} (h : ‖b‖ < ‖a‖) :
    (complexPair a b).IsInvertible := by
  have hi : Injective (complexPair a b) := by
    apply (injective_iff_map_eq_zero (complexPair a b)).mpr
    intro z hz
    change a*z+b*conj z = 0 at hz
    have hn := congrArg norm (eq_neg_of_add_eq_zero_left hz)
    rw [norm_mul,norm_neg,norm_mul,Complex.norm_conj] at hn
    have hz0 : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
    exact norm_eq_zero.mp hz0
  have hs := (LinearMap.injective_iff_surjective (f := (complexPair a b).toLinearMap)).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective (complexPair a b)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs),rfl⟩

theorem exists_positive_complex_linear_path (A : ℂ →L[ℝ] ℂ)
    (hA : 0 < (A 1).re * (A Complex.I).im - (A 1).im * (A Complex.I).re) :
    ∃ L : ℝ → ℂ →L[ℝ] ℂ, ContDiff ℝ ∞ L ∧
      (∀ t, (L t).IsInvertible) ∧ L 0 = ContinuousLinearMap.id ℝ ℂ ∧ L 1 = A ∧
      (∀ t ≤ 0, L t = ContinuousLinearMap.id ℝ ℂ) ∧ (∀ t, 1 ≤ t → L t = A) := by
  let a := (A 1-Complex.I*A Complex.I)/2
  let b := (A 1+Complex.I*A Complex.I)/2
  have hab : ‖b‖ < ‖a‖ := by
    have he := complex_decomposition_orientation A
    change Complex.normSq a-Complex.normSq b = _ at he
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at he
    nlinarith [norm_nonneg a,norm_nonneg b]
  have ha : a ≠ 0 := norm_pos_iff.mp ((norm_nonneg b).trans_lt hab)
  let s : ℝ → ℝ := fun t => Real.smoothTransition (2*t)
  let r : ℝ → ℝ := fun t => Real.smoothTransition (2*t-1)
  let α : ℝ → ℂ := fun t => Complex.exp (s t • Complex.log a)
  let β : ℝ → ℂ := fun t => r t • b
  let L : ℝ → ℂ →L[ℝ] ℂ := fun t => complexPair (α t) (β t)
  have hs : ContDiff ℝ ∞ s := Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)
  have hr : ContDiff ℝ ∞ r := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hα : ContDiff ℝ ∞ α := (hs.smul contDiff_const).cexp
  have hβ : ContDiff ℝ ∞ β := hr.smul contDiff_const
  have hL : ContDiff ℝ ∞ L := (hα.smul contDiff_const).add (hβ.smul contDiff_const)
  have hαa (t : ℝ) (ht : 1 ≤ 2*t) : α t = a := by
    dsimp [α,s]
    simp only [Real.smoothTransition.one_of_one_le ht,Complex.ofReal_one,one_mul,Complex.exp_log ha]
  have hL0 (t : ℝ) (ht : t ≤ 0) : L t = ContinuousLinearMap.id ℝ ℂ := by
    have ht0 : 2*t ≤ 0 := by linarith
    have ht1 : 2*t-1 ≤ 0 := by linarith
    ext z
    simp [L,α,β,s,r,Real.smoothTransition.zero_of_nonpos ht0,
      Real.smoothTransition.zero_of_nonpos ht1]
  have hL1 (t : ℝ) (ht : 1 ≤ t) : L t = A := by
    have ht1 : 1 ≤ 2*t-1 := by linarith
    have ht0 : 1 ≤ 2*t := by linarith
    change complexPair (α t) (r t • b) = A
    rw [hαa t ht0,show r t = 1 from Real.smoothTransition.one_of_one_le ht1,one_smul]
    exact (realLinear_complex_decomposition A).symm
  refine ⟨L,hL,?_,hL0 0 le_rfl,hL1 1 le_rfl,hL0,hL1⟩
  intro t
  apply complexPair_invertible
  by_cases ht : 2*t-1 ≤ 0
  · have hr0 : r t = 0 := Real.smoothTransition.zero_of_nonpos ht
    change ‖r t • b‖ < ‖Complex.exp (s t • Complex.log a)‖
    rw [hr0,zero_smul,norm_zero]
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  · have ht0 : 1 ≤ 2*t := by linarith
    change ‖r t • b‖ < ‖α t‖
    rw [hαa t ht0,norm_smul,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg b) (Real.smoothTransition.le_one _)).trans_lt hab

variable {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]

theorem exists_small_positive_perturbation {K : Set P} (hK : IsCompact K)
    {F : ℝ × P → E} (hF : Continuous F) {W : Set E} (hW : IsOpen W)
    (h0 : ∀ p ∈ K, F (0,p) ∈ W) :
    ∃ δ > 0, ∀ ε : ℝ, |ε| < δ → ∀ p ∈ K, F (ε,p) ∈ W := by
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ F ⁻¹' W := by
    rintro ⟨ε,p⟩ ⟨hε,hp⟩
    have he : ε = 0 := hε
    subst ε
    exact h0 p hp
  obtain ⟨U,V,hU,_,h0U,hKV,hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hW.preimage hF) hsub
  obtain ⟨δ,hδ,hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0U (mem_singleton 0)))
  refine ⟨δ,hδ,?_⟩
  intro ε hε p hp
  exact hUV ⟨hδU (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hε),hKV hp⟩

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_CompactEmbeddingIsotopy
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

 theorem scalar_id_isInvertible {a : ℝ} (ha : a ≠ 0) :
    (a • ContinuousLinearMap.id ℝ E).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := a⁻¹ • ContinuousLinearMap.id ℝ E)
  · ext x
    simp [smul_smul,ha]
  · ext x
    simp [smul_smul,ha]

 theorem smul_isInvertible {A : E →L[ℝ] E} (hA : A.IsInvertible)
    {a : ℝ} (ha : a ≠ 0) : (a • A).IsInvertible := by
  have he : a • A = (a • ContinuousLinearMap.id ℝ E).comp A := by ext x; rfl
  rw [he]
  exact (scalar_id_isInvertible ha).comp hA

 theorem isInvertible_injective {A : E →L[ℝ] E} (hA : A.IsInvertible) : Injective A := by
  obtain ⟨e,he⟩ := hA
  rw [← he]
  exact e.injective

variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem smoothlyAmbientRelated_contraction
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (U W : Set E) (hU : IsOpen U) (hW : IsOpen W) (hcW : Convex ℝ W)
    (hinj : InjOn f U) (hi : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U) (hKW : MapsTo f K W)
    (c : E) (hc : c ∈ W) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    SmoothlyAmbientRelated W K f (fun x => c + ε • (f x-c)) := by
  let a : ℝ → ℝ := fun t => 1-t+t*ε
  have ha (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : 0 < a t ∧ a t ≤ 1 := by
    dsimp [a]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hε.le]
    · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hε1)]
  let F : ℝ × E → E := fun p => c + a p.1 • (f p.2-c)
  have hF : ContDiff ℝ ∞ F := contDiff_const.add
    (((contDiff_const.sub contDiff_fst).add (contDiff_fst.mul contDiff_const)).smul
      ((hf.comp contDiff_snd).sub contDiff_const))
  have hFi (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : InjOn (fun x => F (t,x)) U := by
    intro x hx y hy he
    apply hinj hx hy
    have hh := (smul_right_injective E (ne_of_gt (ha t ht).1)) (add_left_cancel he)
    exact sub_left_injective hh
  have hFd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : E) (hx : x ∈ U) :
      (fderiv ℝ (fun x => F (t,x)) x).IsInvertible := by
    have hd := (((hf.differentiable (by simp) x).hasFDerivAt.sub_const c).const_smul (a t)).const_add c
    change HasFDerivAt (fun x => F (t,x)) (a t • fderiv ℝ f x) x at hd
    rw [hd.fderiv]
    exact smul_isInvertible (hi x hx) (ne_of_gt (ha t ht).1)
  have htrack (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : E) (hx : x ∈ K) : F (t,x) ∈ W := by
    have hh := hcW hc (hKW hx) (sub_nonneg.mpr (ha t ht).2) (ha t ht).1.le
      (show (1-a t)+a t = 1 by ring)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [F]
    module
  have hh := smoothlyAmbientRelated_of_path F hF U W hU hW hFi hFd K hK hKU htrack
  simpa [F,a] using hh

theorem exists_compact_planar_embedding_isotopy_bp240_oai
    (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W)
    (hcU : Convex ℝ U) (hcW : Convex ℝ W)
    (hinj : InjOn f U) (hi : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible)
    (K : Set ℂ) (hK : IsCompact K) (h0K : (0:ℂ) ∈ K)
    (hKU : K ⊆ U) (hKW : K ⊆ W) (hfKW : MapsTo f K W)
    (hor : 0 < (fderiv ℝ f 0 1).re * (fderiv ℝ f 0 Complex.I).im -
      (fderiv ℝ f 0 1).im * (fderiv ℝ f 0 Complex.I).re) :
    SmoothlyAmbientRelated W K id f := by
  obtain ⟨L,hL,hLi,hL0,hL1,_⟩ := exists_positive_complex_linear_path (fderiv ℝ f 0) hor
  have h0W : (0:ℂ) ∈ W := hKW h0K
  have hf0W : f 0 ∈ W := hfKW h0K
  have h0U : (0:ℂ) ∈ U := hKU h0K
  let T : Set (ℝ × ℂ) := Icc (0:ℝ) 1 ×ˢ K
  have hT : IsCompact T := isCompact_Icc.prod hK
  let F₂ : ℝ × (ℝ × ℂ) → ℂ := fun q => q.2.1 • f 0 + q.1 • L q.2.1 q.2.2
  have hF₂ : ContDiff ℝ ∞ F₂ := (contDiff_snd.fst.smul contDiff_const).add
    (contDiff_fst.smul ((hL.comp contDiff_snd.fst).clm_apply contDiff_snd.snd))
  have hF₂0 (p : ℝ × ℂ) (hp : p ∈ T) : F₂ (0,p) ∈ W := by
    simpa [F₂] using hcW.smul_mem_of_zero_mem h0W hf0W hp.1
  obtain ⟨δ₂,hδ₂,hδ₂W⟩ := exists_small_positive_perturbation hT hF₂.continuous hW hF₂0
  let F₃ : ℝ × (ℝ × ℂ) → ℂ := fun q => f 0 + q.1 • smoothBlowup f q.2
  have hF₃ : ContDiff ℝ ∞ F₃ := contDiff_const.add
    (contDiff_fst.smul ((smoothBlowup_contDiff hf).comp contDiff_snd))
  obtain ⟨δ₃,hδ₃,hδ₃W⟩ := exists_small_positive_perturbation hT hF₃.continuous hW
    (fun _ _ => by simpa [F₃] using hf0W)
  let ε : ℝ := min (min δ₂ δ₃) 1 / 2
  have hε : 0 < ε := div_pos (lt_min (lt_min hδ₂ hδ₃) zero_lt_one) (by norm_num)
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    linarith [min_le_right (min δ₂ δ₃) 1]
  have hε₂ : |ε| < δ₂ := by
    rw [abs_of_pos hε]
    have hh := (min_le_left (min δ₂ δ₃) 1).trans (min_le_left δ₂ δ₃)
    dsimp [ε] at *
    linarith
  have hε₃ : |ε| < δ₃ := by
    rw [abs_of_pos hε]
    have hh := (min_le_left (min δ₂ δ₃) 1).trans (min_le_right δ₂ δ₃)
    dsimp [ε] at *
    linarith
  have hrel₂ : SmoothlyAmbientRelated W K (fun x => ε • x)
      (fun x => f 0 + ε • fderiv ℝ f 0 x) := by
    have hh := smoothlyAmbientRelated_of_path (fun p => F₂ (ε,p))
      (hF₂.comp (contDiff_const.prodMk contDiff_id)) U W hU hW
      (fun t _ => by
        intro x _ y _ he
        apply isInvertible_injective (hLi t)
        exact (smul_right_injective ℂ (ne_of_gt hε)) (add_left_cancel he))
      (fun t _ x _ => by
        have hd := (((L t).hasFDerivAt (x := x)).const_smul ε).const_add (t • f 0)
        change HasFDerivAt (fun x => F₂ (ε,(t,x))) (ε • L t) x at hd
        rw [hd.fderiv]
        exact smul_isInvertible (hLi t) (ne_of_gt hε)) K hK hKU
      (fun t ht x hx => hδ₂W ε hε₂ (t,x) ⟨ht,hx⟩)
    simpa [F₂,hL0,hL1] using hh
  have hsmulU (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : ℂ) (hx : x ∈ U) :
      t • x ∈ U := hcU.smul_mem_of_zero_mem h0U hx ht
  have hrel₃ : SmoothlyAmbientRelated W K (fun x => f 0 + ε • fderiv ℝ f 0 x)
      (fun x => f 0 + ε • (f x-f 0)) := by
    have hh := smoothlyAmbientRelated_of_path (fun p => F₃ (ε,p))
      (hF₃.comp (contDiff_const.prodMk contDiff_id)) U W hU hW
      (fun t ht => by
        intro x hx y hy he
        apply smoothBlowup_injOn hf hinj (isInvertible_injective (hi 0 h0U)) t
          (hsmulU t ht x hx) (hsmulU t ht y hy)
        exact (smul_right_injective ℂ (ne_of_gt hε)) (add_left_cancel he))
      (fun t ht x hx => by
        have hd := ((smoothBlowup_hasFDerivAt hf t x).const_smul ε).const_add (f 0)
        change HasFDerivAt (fun x => F₃ (ε,(t,x))) (ε • fderiv ℝ f (t • x)) x at hd
        rw [hd.fderiv]
        exact smul_isInvertible (hi _ (hsmulU t ht x hx)) (ne_of_gt hε)) K hK hKU
      (fun t ht x hx => hδ₃W ε hε₃ (t,x) ⟨ht,hx⟩)
    have hb (x : ℂ) : smoothBlowup f (1,x) = f x-f 0 := by
      simpa only [one_smul] using smul_smoothBlowup hf 1 x
    simpa only [F₃,smoothBlowup_zero,hb] using hh
  have hshrink : SmoothlyAmbientRelated W K id (fun x => ε • x) := by
    have hh := smoothlyAmbientRelated_contraction id contDiff_id U W hU hW hcW
      (injOn_id U) (fun x _ => by
        rw [fderiv_id]
        exact ⟨ContinuousLinearEquiv.refl ℝ ℂ,rfl⟩)
      K hK hKU hKW 0 h0W ε hε hε1
    simpa only [id_eq,sub_zero,zero_add] using hh
  have hexpand := smoothlyAmbientRelated_contraction f hf U W hU hW hcW hinj hi
    K hK hKU hfKW (f 0) hf0W ε hε hε1
  exact hshrink.trans (hrel₂.trans (hrel₃.trans hexpand.symm))

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_planar_embedding_isotopy_bp240_oai := @OAI.PackingSufficiencySupport.Hamiltonian.exists_compact_planar_embedding_isotopy_bp240_oai
