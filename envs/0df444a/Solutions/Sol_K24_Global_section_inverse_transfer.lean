-- Prove2me | solution 1 for K24.Global.section_inverse_transfer
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:38:23.87846+00:00
-- url     : https://prove2.me/submissions/640cc204-e455-48f8-bfdc-65fd61e21fac

import Definitions.Def_K24GlobalAnalysis
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units

set_option autoImplicit false

noncomputable section
open scoped NNReal ENNReal Topology
open Filter

namespace K24.Global

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
  {A : X → Y}

/-- The infimum defining the section operator norm is an actual bound when
the source norms are finite and at least one finite bound exists. -/
theorem sectionOperatorENorm_bound
    (hfinite : ∀ u ∈ S, nx u < ⊤) (hbounded : SectionBoundedOn S nx ny A)
    (u : X) (hu : u ∈ S) :
    ny (A u) ≤ sectionOperatorENorm S nx ny A * nx u := by
  let bounds : Set ℝ≥0∞ := {C | ∀ v ∈ S, ny (A v) ≤ C * nx v}
  obtain ⟨C, hC⟩ := hbounded
  haveI : Nonempty bounds := ⟨⟨C, hC⟩⟩
  change ny (A u) ≤ sInf bounds * nx u
  rw [sInf_eq_iInf', ENNReal.iInf_mul (by simp [(hfinite u hu).ne])]
  exact le_iInf (fun c => c.property u hu)

theorem sectionOperatorENorm_le {C : ℝ≥0∞}
    (hC : ∀ u ∈ S, ny (A u) ≤ C * nx u) :
    sectionOperatorENorm S nx ny A ≤ C :=
  sInf_le hC

theorem sectionOperatorENorm_lt_top (hbounded : SectionBoundedOn S nx ny A) :
    sectionOperatorENorm S nx ny A < ⊤ := by
  obtain ⟨C, hC⟩ := hbounded
  exact lt_of_le_of_lt (sectionOperatorENorm_le hC) ENNReal.coe_lt_top

/-- Surjectivity and the inverse estimate give the exact dual gap occurring
in the Hölder and Sobolev conclusions. No choice of an unrelated dual is used. -/
theorem sectionDualGap_of_inverseBound
    (hfinite : ∀ u ∈ S, nx u < ⊤)
    (hA : SectionIsomorphism S T nx ny A)
    {C : ℝ≥0} (hinverse : SectionInverseBound S nx ny A C) :
    SectionDualGap S T nx ny A C := by
  intro phi _ hphi
  have hcomp : SectionBoundedOn S nx (fun r : ℝ => ENNReal.ofReal |r|) (phi ∘ A) := by
    obtain ⟨D, hD⟩ := hphi
    obtain ⟨E, hE⟩ := hA.2.2.1
    refine ⟨D * E, fun u hu => ?_⟩
    calc
      ENNReal.ofReal |phi (A u)| ≤ (D : ℝ≥0∞) * ny (A u) := hD _ (hA.1 hu)
      _ ≤ (D : ℝ≥0∞) * ((E : ℝ≥0∞) * nx u) := mul_le_mul le_rfl (hE u hu) bot_le bot_le
      _ = ((D * E : ℝ≥0) : ℝ≥0∞) * nx u := by simp [mul_assoc]
  apply sectionOperatorENorm_le
  intro v hv
  obtain ⟨u, hu, rfl⟩ := hA.2.2.2.2 v hv
  calc
    ENNReal.ofReal |phi (A u)| ≤
        sectionOperatorENorm S nx (fun r : ℝ => ENNReal.ofReal |r|) (phi ∘ A) * nx u :=
      sectionOperatorENorm_bound hfinite hcomp u hu
    _ ≤ sectionOperatorENorm S nx (fun r : ℝ => ENNReal.ofReal |r|) (phi ∘ A) *
        ((C : ℝ≥0∞) * ny (A u)) := mul_le_mul le_rfl (hinverse u hu) bot_le bot_le
    _ = (C : ℝ≥0∞) *
        sectionOperatorENorm S nx (fun r : ℝ => ENNReal.ofReal |r|) (phi ∘ A) * ny (A u) := by
      ac_rfl

end K24.Global


namespace K24.Global.SectionBanachSpace

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}

/-- The actual section set, equipped with its inherited linear operations. -/
def toSubmodule (h : SectionBanachSpace S nx) : Submodule ℝ X where
  carrier := S
  zero_mem' := h.zero_mem
  add_mem' := fun hu hv => h.add_mem _ hu _ hv
  smul_mem' := h.smul_mem

variable (h : SectionBanachSpace S nx)

instance sectionNorm : Norm h.toSubmodule := ⟨fun u => (nx u.val).toReal⟩

theorem norm_def (u : h.toSubmodule) : ‖u‖ = (nx u.val).toReal := rfl

theorem normCore : NormedSpace.Core ℝ h.toSubmodule where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c u := by
    change (nx (c • u.val)).toReal = ‖c‖ * (nx u.val).toReal
    rw [h.homogeneous c u.val u.property, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg c), Real.norm_eq_abs]
  norm_triangle u v := by
    change (nx (u.val + v.val)).toReal ≤ (nx u.val).toReal + (nx v.val).toReal
    rw [← ENNReal.toReal_add (h.finite _ u.property).ne (h.finite _ v.property).ne]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨(h.finite _ u.property).ne, (h.finite _ v.property).ne⟩)
      (h.triangle _ u.property _ v.property)
  norm_eq_zero_iff u := by
    constructor
    · intro hu
      apply Subtype.ext
      apply h.definite _ u.property
      have hh := ENNReal.ofReal_toReal (h.finite _ u.property).ne
      rw [← norm_def h u, hu, ENNReal.ofReal_zero] at hh
      exact hh.symm
    · rintro rfl
      change (nx 0).toReal = 0
      rw [h.zero_norm, ENNReal.toReal_zero]

instance normedAddCommGroup : NormedAddCommGroup h.toSubmodule :=
  NormedAddCommGroup.ofCore h.normCore

instance normedSpace : NormedSpace ℝ h.toSubmodule :=
  NormedSpace.ofCore h.normCore

@[simp] theorem ofReal_norm (u : h.toSubmodule) : ENNReal.ofReal ‖u‖ = nx u.val :=
  ENNReal.ofReal_toReal (h.finite _ u.property).ne

instance completeSpace : CompleteSpace h.toSubmodule := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  have hc : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      nx ((f i).val - (f j).val) < ENNReal.ofReal eps := by
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hh := ENNReal.ofReal_lt_ofReal_iff heps |>.mpr (hN i hi j hj)
    simpa only [dist_eq_norm, ofReal_norm, Submodule.coe_sub] using hh
  obtain ⟨v, hv, hlim⟩ := h.complete (fun n => (f n).val) (fun n => (f n).property) hc
  refine ⟨⟨v, hv⟩, Metric.tendsto_atTop.mpr ?_⟩
  intro eps heps
  obtain ⟨N, hN⟩ := hlim eps heps
  refine ⟨N, fun i hi => ?_⟩
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  simpa only [dist_eq_norm, ofReal_norm, Submodule.coe_sub] using hN i hi

variable (k : SectionBanachSpace T ny)
  {A : X → Y}

/-- A section map becomes a continuous linear map on the actual subspaces,
using precisely its stated section bound. -/
def continuousLinearMap (hmaps : Set.MapsTo A S T)
    (hlinear : SectionLinearOn S A) (hbounded : SectionBoundedOn S nx ny A) :
    h.toSubmodule →L[ℝ] k.toSubmodule := by
  let a : h.toSubmodule →ₗ[ℝ] k.toSubmodule :=
    { toFun := fun u => ⟨A u.val, hmaps u.property⟩
      map_add' := fun u v => Subtype.ext (hlinear.2.1 _ u.property _ v.property)
      map_smul' := fun c u => Subtype.ext (hlinear.2.2 c _ u.property) }
  let C := hbounded.choose
  have hC := hbounded.choose_spec
  exact a.mkContinuous (C : ℝ) (fun u => by
    change (ny (A u.val)).toReal ≤ (C : ℝ) * (nx u.val).toReal
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (h.finite _ u.property).ne) (hC _ u.property)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hh)

@[simp] theorem continuousLinearMap_apply (hmaps : Set.MapsTo A S T)
    (hlinear : SectionLinearOn S A) (hbounded : SectionBoundedOn S nx ny A)
    (u : h.toSubmodule) :
    (h.continuousLinearMap k hmaps hlinear hbounded u).val = A u.val := rfl

theorem bounded_of_realization (f : h.toSubmodule →L[ℝ] k.toSubmodule)
    (hf : ∀ u : h.toSubmodule, (f u).val = A u.val) : SectionBoundedOn S nx ny A := by
  refine ⟨‖f‖₊, fun u hu => ?_⟩
  have hh := ENNReal.ofReal_le_ofReal (f.le_opNorm (⟨u, hu⟩ : h.toSubmodule))
  rw [ENNReal.ofReal_mul (norm_nonneg f), h.ofReal_norm, k.ofReal_norm, hf] at hh
  simpa only [_root_.ofReal_norm, enorm] using hh

/-- The standard operator norm is bounded by the real conversion of the
exact section operator norm, with no loss in constants. -/
theorem norm_le_sectionOperatorENorm (f : h.toSubmodule →L[ℝ] k.toSubmodule)
    (hf : ∀ u : h.toSubmodule, (f u).val = A u.val) :
    ‖f‖ ≤ (sectionOperatorENorm S nx ny A).toReal := by
  have hb := h.bounded_of_realization k f hf
  apply f.opNorm_le_bound ENNReal.toReal_nonneg
  intro u
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (sectionOperatorENorm_lt_top hb).ne (h.finite _ u.property).ne)
    (sectionOperatorENorm_bound h.finite hb u.val u.property)
  simpa only [ENNReal.toReal_mul, ← hf u, norm_def] using hh

end K24.Global.SectionBanachSpace


namespace K24.Global

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
  {A B : X → Y}

/-- Neumann perturbation on the exact section spaces in the K24 statement.
Geometric membership, linearity and boundedness of the perturbed operator
remain explicit hypotheses. The conclusion includes the exact dual gap. -/
theorem section_inverse_transfer_proof
    (hS : SectionBanachSpace S nx) (hT : SectionBanachSpace T ny)
    (hA : SectionIsomorphism S T nx ny A)
    (hBmaps : Set.MapsTo B S T) (hBlinear : SectionLinearOn S B)
    (hBbounded : SectionBoundedOn S nx ny B)
    (C : ℝ≥0) (hC : 0 < C)
    (hInv : SectionInverseBound S nx ny A C)
    (hsmall : (C : ℝ≥0∞) * sectionOperatorENorm S nx ny (fun u => B u - A u) <
      (1 / 2 : ℝ≥0∞)) :
    SectionIsomorphism S T nx ny B ∧
      SectionInverseBound S nx ny B (2 * C) ∧
      SectionDualGap S T nx ny B (2 * C) := by
  let a := hS.continuousLinearMap hT hA.1 hA.2.1 hA.2.2.1
  let b := hS.continuousLinearMap hT hBmaps hBlinear hBbounded
  have ha (u : hS.toSubmodule) : (a u).val = A u.val := rfl
  have hb (u : hS.toSubmodule) : (b u).val = B u.val := rfl
  have hai : Function.Injective a := by
    intro u v huv
    apply Subtype.ext
    exact hA.2.2.2.1 u.property v.property (congrArg Subtype.val huv)
  have has : Function.Surjective a := by
    intro v
    obtain ⟨u, hu, huv⟩ := hA.2.2.2.2 v.val v.property
    exact ⟨⟨u, hu⟩, Subtype.ext huv⟩
  let e : hS.toSubmodule ≃L[ℝ] hT.toSubmodule :=
    ContinuousLinearEquiv.ofBijective a
      (LinearMap.ker_eq_bot.mpr hai) (LinearMap.range_eq_top.mpr has)
  have he (u : hS.toSubmodule) : e u = a u := rfl
  have hinv (u : hS.toSubmodule) : ‖u‖ ≤ (C : ℝ) * ‖a u‖ := by
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (hT.finite _ (hA.1 u.property)).ne)
      (hInv u.val u.property)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal,
      SectionBanachSpace.norm_def, ha] using hh
  have henorm : ‖(e.symm : hT.toSubmodule →L[ℝ] hS.toSubmodule)‖ ≤ (C : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
    intro v
    change ‖e.symm v‖ ≤ (C : ℝ) * ‖v‖
    calc
      ‖e.symm v‖ ≤ (C : ℝ) * ‖a (e.symm v)‖ := hinv (e.symm v)
      _ = (C : ℝ) * ‖v‖ := by rw [← he, e.apply_symm_apply]
  let D := sectionOperatorENorm S nx ny (fun u => B u - A u)
  have hdrep (u : hS.toSubmodule) : ((b - a) u).val = B u.val - A u.val := rfl
  have hDbounded := hS.bounded_of_realization hT (A := fun u => B u - A u) (b - a) hdrep
  have hDfinite : D ≠ ⊤ := (sectionOperatorENorm_lt_top hDbounded).ne
  have hd : ‖b - a‖ ≤ D.toReal :=
    hS.norm_le_sectionOperatorENorm hT (A := fun u => B u - A u) (b - a) hdrep
  have hsmallreal : (C : ℝ) * D.toReal < 1 / 2 := by
    have hh := (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hDfinite) (by norm_num)).mpr hsmall
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_ofNat] using hh
  have hcompnorm : ‖(e.symm : hT.toSubmodule →L[ℝ] hS.toSubmodule).comp (b - a)‖ < 1 := by
    calc
      _ ≤ ‖(e.symm : hT.toSubmodule →L[ℝ] hS.toSubmodule)‖ * ‖b - a‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C : ℝ) * D.toReal := mul_le_mul henorm hd (norm_nonneg _) C.coe_nonneg
      _ < 1 := lt_trans hsmallreal (by norm_num)
  let w := Units.oneSub
    (-((e.symm : hT.toSubmodule →L[ℝ] hS.toSubmodule).comp (b - a)))
    (by simpa only [norm_neg] using hcompnorm)
  have hw : (w : hS.toSubmodule →L[ℝ] hS.toSubmodule) =
      (e.symm : hT.toSubmodule →L[ℝ] hS.toSubmodule).comp b := by
    apply ContinuousLinearMap.ext
    intro u
    change u - -(e.symm (b u - a u)) = e.symm (b u)
    rw [map_sub, ← he, e.symm_apply_apply]
    abel
  have hbijcomp : Function.Bijective
      ((e.symm : hT.toSubmodule →L[ℝ] hS.toSubmodule).comp b) := by
    rw [← hw]
    exact (ContinuousLinearEquiv.ofUnit w).bijective
  have hbi : Function.Injective b := by
    intro u v huv
    exact hbijcomp.1 (congrArg e.symm huv)
  have hbs : Function.Surjective b := by
    intro v
    obtain ⟨u, hu⟩ := hbijcomp.2 (e.symm v)
    exact ⟨u, e.symm.injective hu⟩
  have hBiso : SectionIsomorphism S T nx ny B := by
    refine ⟨hBmaps, hBlinear, hBbounded, ?_, ?_⟩
    · intro u hu v hv huv
      have hh : b (⟨u, hu⟩ : hS.toSubmodule) = b ⟨v, hv⟩ := Subtype.ext huv
      exact congrArg Subtype.val (hbi hh)
    · intro v hv
      obtain ⟨u, hu⟩ := hbs (⟨v, hv⟩ : hT.toSubmodule)
      exact ⟨u.val, u.property, congrArg Subtype.val hu⟩
  have hinvBreal (u : hS.toSubmodule) : ‖u‖ ≤ (2 * (C : ℝ)) * ‖b u‖ := by
    have hdiff : ‖(b - a) u‖ ≤ D.toReal * ‖u‖ :=
      (b - a).le_of_opNorm_le hd u
    have ha_le : ‖a u‖ ≤ ‖b u‖ + ‖(b - a) u‖ := by
      have hh := norm_sub_le (b u) ((b - a) u)
      simpa only [ContinuousLinearMap.sub_apply, sub_sub_cancel] using hh
    have hfirst : ‖u‖ ≤ (C : ℝ) * (‖b u‖ + D.toReal * ‖u‖) :=
      (hinv u).trans (mul_le_mul_of_nonneg_left (ha_le.trans (add_le_add le_rfl hdiff)) C.coe_nonneg)
    have hhalf : ((C : ℝ) * D.toReal) * ‖u‖ ≤ (1 / 2 : ℝ) * ‖u‖ :=
      mul_le_mul_of_nonneg_right hsmallreal.le (norm_nonneg _)
    nlinarith
  have hBInv : SectionInverseBound S nx ny B (2 * C) := by
    intro u hu
    have hh := ENNReal.ofReal_le_ofReal (hinvBreal (⟨u, hu⟩ : hS.toSubmodule))
    rw [ENNReal.ofReal_mul (by positivity), hS.ofReal_norm, hT.ofReal_norm] at hh
    simpa only [hb, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, ENNReal.coe_ofNat] using hh
  exact ⟨hBiso, hBInv, sectionDualGap_of_inverseBound hS.finite hBiso hBInv⟩

end K24.Global

namespace K24.Global
universe u v

theorem _root_.solution :
  ∀ {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    {A B : X → Y},
    SectionBanachSpace S nx → SectionBanachSpace T ny →
    SectionIsomorphism S T nx ny A → Set.MapsTo B S T →
    SectionLinearOn S B → SectionBoundedOn S nx ny B →
    ∀ C : ℝ≥0, 0 < C → SectionInverseBound S nx ny A C →
    (C : ℝ≥0∞) * sectionOperatorENorm S nx ny (fun u => B u - A u) <
      (1 / 2 : ℝ≥0∞) →
    SectionIsomorphism S T nx ny B ∧
      SectionInverseBound S nx ny B (2 * C) ∧
      SectionDualGap S T nx ny B (2 * C) :=
  @section_inverse_transfer_proof

end K24.Global
