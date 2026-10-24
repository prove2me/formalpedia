-- Prove2me | solution 1 for K24.Global.section_neumann_transfer
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:37:33.365124+00:00
-- url     : https://prove2.me/submissions/55e5bae7-9e5b-4145-81a8-a4e70fb41034

import Definitions.Def_K24GlobalAnalysis
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal


set_option autoImplicit false

open scoped NNReal ENNReal

namespace K24.Global

variable {X Y Z : Type*}

/-- Every admissible bound bounds the infimum defining the operator norm. -/
theorem sectionOperatorENorm_le_of_bound
    {S : Set X} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    {A : X → Y} {C : ℝ≥0∞}
    (hC : ∀ u ∈ S, ny (A u) ≤ C * nx u) :
    sectionOperatorENorm S nx ny A ≤ C := sInf_le hC

/-- A finite section-map bound makes its actual operator norm finite. -/
theorem SectionBoundedOn.sectionOperatorENorm_lt_top
    {S : Set X} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞} {A : X → Y}
    (hA : SectionBoundedOn S nx ny A) :
    sectionOperatorENorm S nx ny A < ⊤ := by
  obtain ⟨C, hC⟩ := hA
  exact (sectionOperatorENorm_le_of_bound hC).trans_lt ENNReal.coe_lt_top

/-- On finite-norm sections, the infimum operator norm itself is an admissible
bound. Finiteness of the domain norm is essential for commuting multiplication
with this infimum. -/
theorem sectionOperatorENorm_apply_le
    {S : Set X} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞} {A : X → Y}
    (hfinite : ∀ u ∈ S, nx u < ⊤)
    (hA : SectionBoundedOn S nx ny A) (u : X) (hu : u ∈ S) :
    ny (A u) ≤ sectionOperatorENorm S nx ny A * nx u := by
  let bounds : Set ℝ≥0∞ := {D | ∀ v ∈ S, ny (A v) ≤ D * nx v}
  have hne : bounds.Nonempty := by
    obtain ⟨D, hD⟩ := hA
    exact ⟨D, hD⟩
  have : Nonempty bounds := hne.to_subtype
  change ny (A u) ≤ sInf bounds * nx u
  rw [sInf_eq_iInf', ENNReal.iInf_mul (by simp [(hfinite u hu).ne])]
  exact le_iInf fun D => D.property u hu

/-- Bounds for genuine section maps compose on their specified domains. -/
theorem SectionBoundedOn.comp
    {S : Set X} {T : Set Y}
    {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞} {nz : Z → ℝ≥0∞}
    {A : X → Y} {F : Y → Z}
    (hF : SectionBoundedOn T ny nz F)
    (hA : SectionBoundedOn S nx ny A) (hAT : Set.MapsTo A S T) :
    SectionBoundedOn S nx nz (F ∘ A) := by
  obtain ⟨CF, hF⟩ := hF
  obtain ⟨CA, hA⟩ := hA
  refine ⟨CF * CA, fun u hu => ?_⟩
  calc
    nz ((F ∘ A) u) ≤ (CF : ℝ≥0∞) * ny (A u) := hF _ (hAT hu)
    _ ≤ (CF : ℝ≥0∞) * ((CA : ℝ≥0∞) * nx u) := mul_le_mul' le_rfl (hA u hu)
    _ = ((CF * CA : ℝ≥0) : ℝ≥0∞) * nx u := by simp [mul_assoc]

/-- A surjective section map with inverse bound transfers every bounded
functional's operator norm to the norm of its actual pullback. This is proved
directly for the infimum definition of `sectionOperatorENorm`. -/
theorem sectionOperatorENorm_le_inverseBound
    {S : Set X} {T : Set Y}
    {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞} {nz : Z → ℝ≥0∞}
    {A : X → Y} {F : Y → Z} {C : ℝ≥0}
    (hSurj : ∀ v ∈ T, ∃ u ∈ S, A u = v)
    (hInv : SectionInverseBound S nx ny A C)
    (hComp : SectionBoundedOn S nx nz (F ∘ A)) :
    sectionOperatorENorm T ny nz F ≤
      (C : ℝ≥0∞) * sectionOperatorENorm S nx nz (F ∘ A) := by
  let bounds : Set ℝ≥0∞ := {D | ∀ u ∈ S, nz ((F ∘ A) u) ≤ D * nx u}
  have hne : bounds.Nonempty := by
    obtain ⟨D, hD⟩ := hComp
    exact ⟨D, hD⟩
  have : Nonempty bounds := hne.to_subtype
  change sectionOperatorENorm T ny nz F ≤ (C : ℝ≥0∞) * sInf bounds
  rw [sInf_eq_iInf', ENNReal.mul_iInf (by simp)]
  apply le_iInf
  rintro ⟨D, hD⟩
  apply sInf_le
  intro v hv
  obtain ⟨u, hu, rfl⟩ := hSurj v hv
  calc
    nz (F (A u)) ≤ D * nx u := hD u hu
    _ ≤ D * ((C : ℝ≥0∞) * ny (A u)) := mul_le_mul' le_rfl (hInv u hu)
    _ = (C : ℝ≥0∞) * D * ny (A u) := by ac_rfl

/-- The dual-gap conclusion required by K24 follows from its actual section
isomorphism and inverse estimate, with exactly the same constant. -/
theorem SectionIsomorphism.dualGap
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    {S : Set X} {T : Set Y}
    {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞} {A : X → Y} {C : ℝ≥0}
    (hA : SectionIsomorphism S T nx ny A)
    (hInv : SectionInverseBound S nx ny A C) :
    SectionDualGap S T nx ny A C := by
  intro phi _ hphi
  exact sectionOperatorENorm_le_inverseBound hA.2.2.2.2 hInv
    (hphi.comp hA.2.2.1 hA.1)

end K24.Global



set_option autoImplicit false

namespace SiweiK24

/-- The abstract Banach-space perturbation statement in K24, Section 4.
The equivalence is constructed using the convergent Neumann series. -/
theorem neumann_transfer
    (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : X ≃L[ℝ] Y) (R : X →L[ℝ] Y) (C_A : ℝ)
    (hC : 0 < C_A)
    (hA : ‖A.symm.toContinuousLinearMap‖ ≤ C_A)
    (hR : C_A * ‖R‖ < (1 / 2 : ℝ)) :
    ∃ B : X ≃L[ℝ] Y,
      B.toContinuousLinearMap = A.toContinuousLinearMap + R ∧
      ‖B.symm.toContinuousLinearMap‖ ≤ 2 * C_A := by
  let T : X →L[ℝ] X := A.symm.toContinuousLinearMap.comp R
  have hT : ‖T‖ < 1 := by
    calc
      ‖T‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖R‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C_A * ‖R‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg R)
      _ < 1 := by linarith
  let U : (X →L[ℝ] X)ˣ := Units.oneSub (-T) (by simpa using hT)
  let B : X ≃L[ℝ] Y := (ContinuousLinearEquiv.ofUnit U).trans A
  have hB : B.toContinuousLinearMap = A.toContinuousLinearMap + R := by
    ext x
    change A ((1 - -T) x) = A x + R x
    simp [T]
  refine ⟨B, hB, ?_⟩
  have hB_apply (x : X) : B x = A x + R x :=
    congrArg (fun f : X →L[ℝ] Y => f x) hB
  have h_bound (x : X) :
      ‖x‖ ≤ C_A * ‖B x‖ + (C_A * ‖R‖) * ‖x‖ := by
    have hAx : A x = B x - R x := by rw [hB_apply]; simp
    calc
      ‖x‖ = ‖A.symm (A x)‖ := by simp
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A x‖ :=
        A.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ C_A * ‖A x‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ ≤ C_A * (‖B x‖ + ‖R x‖) := by
        rw [hAx]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hC.le
      _ ≤ C_A * (‖B x‖ + ‖R‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (R.le_opNorm x)) hC.le
      _ = C_A * ‖B x‖ + (C_A * ‖R‖) * ‖x‖ := by ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith [hC])
  intro y
  have hy := h_bound (B.symm y)
  rw [B.apply_symm_apply] at hy
  have hsmall := mul_le_mul_of_nonneg_right hR.le (norm_nonneg (B.symm y))
  change ‖B.symm y‖ ≤ 2 * C_A * ‖y‖
  nlinarith

end SiweiK24



set_option autoImplicit false
noncomputable section
open scoped NNReal ENNReal

namespace K24.Global

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

private def sectionSubmodule {S : Set X} {nx : X → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) : Submodule ℝ X where
  carrier := S
  zero_mem' := hS.zero_mem
  add_mem' := fun hu hv => hS.add_mem _ hu _ hv
  smul_mem' := fun c _ hu => hS.smul_mem c _ hu

private instance sectionNorm {S : Set X} {nx : X → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) : Norm (sectionSubmodule hS) :=
  ⟨fun u => (nx u).toReal⟩

private theorem sectionCore {S : Set X} {nx : X → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) : NormedSpace.Core ℝ (sectionSubmodule hS) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c u := by
    change (nx (c • (u : X))).toReal = ‖c‖ * (nx u).toReal
    rw [hS.homogeneous c u u.property, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg c), Real.norm_eq_abs]
  norm_triangle u v := by
    change (nx ((u : X) + v)).toReal ≤ (nx u).toReal + (nx v).toReal
    rw [← ENNReal.toReal_add (hS.finite u u.property).ne (hS.finite v v.property).ne]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨(hS.finite u u.property).ne, (hS.finite v v.property).ne⟩)
      (hS.triangle u u.property v v.property)
  norm_eq_zero_iff u := by
    constructor
    · intro h
      change (nx u).toReal = 0 at h
      apply Subtype.ext
      apply hS.definite u u.property
      have := congrArg ENNReal.ofReal h
      simpa only [ENNReal.ofReal_zero,
        ENNReal.ofReal_toReal (hS.finite u u.property).ne] using this
    · intro h
      subst u
      change (nx 0).toReal = 0
      rw [hS.zero_norm, ENNReal.toReal_zero]

private instance sectionNormedGroup {S : Set X} {nx : X → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) : NormedAddCommGroup (sectionSubmodule hS) :=
  .ofCore (sectionCore hS)

private instance sectionNormedSpace {S : Set X} {nx : X → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) : NormedSpace ℝ (sectionSubmodule hS) :=
  .ofCore (sectionCore hS)

private theorem section_norm_eq {S : Set X} {nx : X → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (u : sectionSubmodule hS) :
    ‖u‖ = (nx u).toReal := rfl

private instance sectionCompleteSpace {S : Set X} {nx : X → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) : CompleteSpace (sectionSubmodule hS) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  have hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      nx ((f i : X) - f j) < ENNReal.ofReal eps := by
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hij := hN i hi j hj
    rw [dist_eq_norm, section_norm_eq] at hij
    exact (ENNReal.toReal_lt_toReal
      (hS.finite _ (show (f i : X) - f j ∈ S from (sectionSubmodule hS).sub_mem
        (f i).property (f j).property)).ne ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal heps.le, Submodule.coe_sub] using hij)
  obtain ⟨v, hv, hconv⟩ := hS.complete (fun n => f n) (fun n => (f n).property) hc
  refine ⟨⟨v, hv⟩, Metric.tendsto_atTop.mpr ?_⟩
  intro eps heps
  obtain ⟨N, hN⟩ := hconv eps heps
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm, section_norm_eq]
  have hi' := ENNReal.toReal_strict_mono ENNReal.ofReal_ne_top (hN i hi)
  simpa only [ENNReal.toReal_ofReal heps.le, Submodule.coe_sub] using hi'

private def sectionLinearMap {S : Set X} {T : Set Y}
    {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    {A : X → Y} (hAT : Set.MapsTo A S T) (hAL : SectionLinearOn S A) :
    sectionSubmodule hS →ₗ[ℝ] sectionSubmodule hT where
  toFun u := ⟨A u, hAT u.property⟩
  map_add' u v := Subtype.ext (hAL.2.1 u u.property v v.property)
  map_smul' c u := Subtype.ext (hAL.2.2 c u u.property)

private theorem section_real_bound {S : Set X} {T : Set Y}
    {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (_hT : SectionBanachSpace T ny)
    {A : X → Y} (_hAT : Set.MapsTo A S T) {D : ℝ≥0∞} (hD : D < ⊤)
    (hbound : ∀ u ∈ S, ny (A u) ≤ D * nx u) (u : sectionSubmodule hS) :
    (ny (A u)).toReal ≤ D.toReal * ‖u‖ := by
  rw [section_norm_eq, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hD.ne (hS.finite u u.property).ne) (hbound u u.property)

private def sectionContinuousLinearMap {S : Set X} {T : Set Y}
    {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    {A : X → Y} (hAT : Set.MapsTo A S T) (hAL : SectionLinearOn S A)
    (hAB : SectionBoundedOn S nx ny A) :
    sectionSubmodule hS →L[ℝ] sectionSubmodule hT :=
  (sectionLinearMap hS hT hAT hAL).mkContinuous hAB.choose
    (fun u => by
      exact section_real_bound hS hT hAT (ENNReal.coe_lt_top)
        hAB.choose_spec u)

private theorem sectionContinuousLinearMap_apply {S : Set X} {T : Set Y}
    {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    {A : X → Y} (hAT : Set.MapsTo A S T) (hAL : SectionLinearOn S A)
    (hAB : SectionBoundedOn S nx ny A) (u : sectionSubmodule hS) :
    (sectionContinuousLinearMap hS hT hAT hAL hAB u : Y) = A u := rfl

private theorem sectionContinuousLinearMap_norm_le {S : Set X} {T : Set Y}
    {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    {A : X → Y} (hAT : Set.MapsTo A S T) (hAL : SectionLinearOn S A)
    (hAB : SectionBoundedOn S nx ny A) :
    ‖sectionContinuousLinearMap hS hT hAT hAL hAB‖ ≤
      (sectionOperatorENorm S nx ny A).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
  intro u
  exact section_real_bound hS hT hAT hAB.sectionOperatorENorm_lt_top
    (sectionOperatorENorm_apply_le hS.finite hAB) u

private theorem section_neg_norm {T : Set Y} {ny : Y → ℝ≥0∞}
    (hT : SectionBanachSpace T ny) {v : Y} (hv : v ∈ T) : ny (-v) = ny v := by
  simpa using hT.homogeneous (-1) v hv

omit [AddCommGroup X] [Module ℝ X] in
private theorem section_sub_bounded {S : Set X} {T : Set Y}
    {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hT : SectionBanachSpace T ny) {A B : X → Y}
    (hAT : Set.MapsTo A S T) (hBT : Set.MapsTo B S T)
    (hAB : SectionBoundedOn S nx ny A) (hBB : SectionBoundedOn S nx ny B) :
    SectionBoundedOn S nx ny (fun u => B u - A u) := by
  obtain ⟨CA, hCA⟩ := hAB
  obtain ⟨CB, hCB⟩ := hBB
  refine ⟨CB + CA, fun u hu => ?_⟩
  calc
    ny (B u - A u) ≤ ny (B u) + ny (-A u) := by
      simpa only [sub_eq_add_neg] using
        hT.triangle _ (hBT hu) _ ((sectionSubmodule hT).neg_mem (hAT hu))
    _ = ny (B u) + ny (A u) := by rw [section_neg_norm hT (hAT hu)]
    _ ≤ (CB : ℝ≥0∞) * nx u + (CA : ℝ≥0∞) * nx u := add_le_add (hCB u hu) (hCA u hu)
    _ = ((CB + CA : ℝ≥0) : ℝ≥0∞) * nx u := by simp [add_mul]

/-- Neumann perturbation transfer for the exact concrete section predicates.
The Banach structure is constructed from the stated section norm laws. -/
theorem SectionIsomorphism.neumann_transfer
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    {A B : X → Y} {C : ℝ≥0}
    (hA : SectionIsomorphism S T nx ny A)
    (hInv : SectionInverseBound S nx ny A C)
    (hBT : Set.MapsTo B S T) (hBL : SectionLinearOn S B)
    (hBB : SectionBoundedOn S nx ny B)
    (hsmall : (C : ℝ≥0∞) * sectionOperatorENorm S nx ny (fun u => B u - A u) < 1 / 2) :
    SectionIsomorphism S T nx ny B ∧ SectionInverseBound S nx ny B (2 * C) := by
  by_cases hCzero : C = 0
  · have hz : ∀ u ∈ S, u = 0 := by
      intro u hu
      apply hS.definite u hu
      have h := hInv u hu
      simpa [hCzero] using h
    refine ⟨⟨hBT, hBL, hBB, ?_, ?_⟩, ?_⟩
    · intro u hu v hv _
      rw [hz u hu, hz v hv]
    · intro v hv
      obtain ⟨u, hu, huv⟩ := hA.2.2.2.2 v hv
      refine ⟨0, hS.zero_mem, ?_⟩
      rw [hBL.1, ← huv, hz u hu, hA.2.1.1]
    · intro u hu
      simp [hz u hu, hS.zero_norm]
  have hCpos : (0 : ℝ) < C := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hCzero)
  let a := sectionContinuousLinearMap hS hT hA.1 hA.2.1 hA.2.2.1
  have ha_inj : Function.Injective a := by
    intro u v huv
    apply Subtype.ext
    exact hA.2.2.2.1 u.property v.property (congrArg Subtype.val huv)
  have ha_surj : Function.Surjective a := by
    intro v
    obtain ⟨u, hu, huv⟩ := hA.2.2.2.2 v v.property
    exact ⟨⟨u, hu⟩, Subtype.ext huv⟩
  let eA : sectionSubmodule hS ≃L[ℝ] sectionSubmodule hT :=
    ContinuousLinearEquiv.ofBijective a (LinearMap.ker_eq_bot.mpr ha_inj)
      (LinearMap.range_eq_top.mpr ha_surj)
  have heA_apply (u : sectionSubmodule hS) : (eA u : Y) = A u := rfl
  have hInvReal (u : sectionSubmodule hS) : ‖u‖ ≤ (C : ℝ) * ‖eA u‖ := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (hT.finite _ (hA.1 u.property)).ne)
      (hInv u u.property)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, section_norm_eq, heA_apply] using h
  have hInvNorm : ‖eA.symm.toContinuousLinearMap‖ ≤ (C : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
    intro v
    simpa using hInvReal (eA.symm v)
  have hRT : Set.MapsTo (fun u => B u - A u) S T := by
    intro u hu
    exact (sectionSubmodule hT).sub_mem (hBT hu) (hA.1 hu)
  have hRL : SectionLinearOn S (fun u => B u - A u) := by
    refine ⟨by simp [hBL.1, hA.2.1.1], ?_, ?_⟩
    · intro u hu v hv
      dsimp only
      rw [hBL.2.1 u hu v hv, hA.2.1.2.1 u hu v hv]
      abel
    · intro c u hu
      dsimp only
      rw [hBL.2.2 c u hu, hA.2.1.2.2 c u hu, smul_sub]
  have hRB := section_sub_bounded hT hA.1 hBT hA.2.2.1 hBB
  let r := sectionContinuousLinearMap hS hT hRT hRL hRB
  have hrNorm : ‖r‖ ≤ (sectionOperatorENorm S nx ny (fun u => B u - A u)).toReal :=
    sectionContinuousLinearMap_norm_le hS hT hRT hRL hRB
  have hsmallReal : (C : ℝ) * ‖r‖ < (1 / 2 : ℝ) := by
    have hs := ENNReal.toReal_strict_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) hsmall
    have hs' : (C : ℝ) * (sectionOperatorENorm S nx ny (fun u => B u - A u)).toReal < 1 / 2 := by
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_div,
        ENNReal.toReal_one, ENNReal.toReal_ofNat] using hs
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrNorm C.coe_nonneg) hs'
  obtain ⟨eB, heB, heBInv⟩ := SiweiK24.neumann_transfer
    (sectionSubmodule hS) (sectionSubmodule hT) eA r C hCpos hInvNorm hsmallReal
  have heB_apply (u : sectionSubmodule hS) : (eB u : Y) = B u := by
    have h := congrArg (fun f : sectionSubmodule hS →L[ℝ] sectionSubmodule hT => (f u : Y)) heB
    change (eB u : Y) = A u + (B u - A u) at h
    exact h.trans (by abel)
  refine ⟨⟨hBT, hBL, hBB, ?_, ?_⟩, ?_⟩
  · intro u hu v hv huv
    have huv' : eB ⟨u, hu⟩ = eB ⟨v, hv⟩ := by
      apply Subtype.ext
      simpa only [heB_apply] using huv
    exact congrArg Subtype.val (eB.injective huv')
  · intro v hv
    refine ⟨eB.symm ⟨v, hv⟩, (eB.symm ⟨v, hv⟩).property, ?_⟩
    rw [← heB_apply]
    exact congrArg Subtype.val (eB.apply_symm_apply ⟨v, hv⟩)
  · intro u hu
    let u' : sectionSubmodule hS := ⟨u, hu⟩
    have h : ‖u'‖ ≤ (2 * (C : ℝ)) * ‖eB u'‖ := by
      calc
        ‖u'‖ = ‖eB.symm (eB u')‖ := by rw [eB.symm_apply_apply]
        _ ≤ ‖eB.symm.toContinuousLinearMap‖ * ‖eB u'‖ :=
          eB.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ (2 * (C : ℝ)) * ‖eB u'‖ :=
          mul_le_mul_of_nonneg_right heBInv (norm_nonneg _)
    apply (ENNReal.toReal_le_toReal (hS.finite u hu).ne
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (hT.finite _ (hBT hu)).ne)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_mul,
      NNReal.coe_ofNat, section_norm_eq, heB_apply] using h

 /-- The form used by the tensor and vector inverse-transfer fields of K24:
surjectivity and the inverse estimate also give the actual dual gap. -/
theorem SectionIsomorphism.neumann_transfer_with_dualGap
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    {A B : X → Y} {C : ℝ≥0}
    (hA : SectionIsomorphism S T nx ny A)
    (hInv : SectionInverseBound S nx ny A C)
    (hBT : Set.MapsTo B S T) (hBL : SectionLinearOn S B)
    (hBB : SectionBoundedOn S nx ny B)
    (hsmall : (C : ℝ≥0∞) * sectionOperatorENorm S nx ny (fun u => B u - A u) < 1 / 2) :
    SectionIsomorphism S T nx ny B ∧ SectionInverseBound S nx ny B (2 * C) ∧
      SectionDualGap S T nx ny B (2 * C) := by
  obtain ⟨hIso, hBound⟩ := hA.neumann_transfer hS hT hInv hBT hBL hBB hsmall
  exact ⟨hIso, hBound, hIso.dualGap hBound⟩

end K24.Global


open K24.Global

theorem solution
    {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    {A B : X → Y} {C : ℝ≥0}
    (hA : SectionIsomorphism S T nx ny A)
    (hInv : SectionInverseBound S nx ny A C)
    (hBT : Set.MapsTo B S T) (hBL : SectionLinearOn S B)
    (hBB : SectionBoundedOn S nx ny B)
    (hsmall : (C : ℝ≥0∞) * sectionOperatorENorm S nx ny (fun u => B u - A u) < 1 / 2) :
    SectionIsomorphism S T nx ny B ∧ SectionInverseBound S nx ny B (2 * C) ∧
      SectionDualGap S T nx ny B (2 * C) := by
  exact hA.neumann_transfer_with_dualGap hS hT hInv hBT hBL hBB hsmall

#print axioms solution
