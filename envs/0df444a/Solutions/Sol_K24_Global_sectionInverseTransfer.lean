-- Prove2me | solution 1 for K24.Global.sectionInverseTransfer
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:04:15.921383+00:00
-- url     : https://prove2.me/submissions/baf7b582-8fcc-4cb9-80f2-54094f4ef79c

import Definitions.Def_K24GlobalAnalysis
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Bundled from Solutions/K24INV_Adapter.lean. -/

set_option autoImplicit false

noncomputable section

open scoped NNReal ENNReal Topology

namespace K24.Global.SectionBanachSpace

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}

/-- The submodule consists of the original admissible sections. -/
def submodule (h : SectionBanachSpace S nx) : Submodule ℝ X where
  carrier := S
  zero_mem' := h.zero_mem
  add_mem' := fun hu hv => h.add_mem _ hu _ hv
  smul_mem' := fun c _ hu => h.smul_mem c _ hu

/-- The real norm is obtained from the finite, supplied section norm. -/
@[instance_reducible]
def sectionNorm (h : SectionBanachSpace S nx) : Norm h.submodule :=
  ⟨fun u => (nx u).toReal⟩

theorem normCore (h : SectionBanachSpace S nx) :
    letI := h.sectionNorm
    NormedSpace.Core ℝ h.submodule := by
  letI := h.sectionNorm
  refine
    { norm_nonneg := fun _ => ENNReal.toReal_nonneg
      norm_smul := ?_
      norm_triangle := ?_
      norm_eq_zero_iff := ?_ }
  · intro c u
    change (nx (c • (u : X))).toReal = ‖c‖ * (nx u).toReal
    rw [h.homogeneous c u u.property, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
  · intro u v
    change (nx ((u : X) + v)).toReal ≤ (nx u).toReal + (nx v).toReal
    calc
      _ ≤ (nx u + nx v).toReal := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨(h.finite u u.property).ne,
          (h.finite v v.property).ne⟩) (h.triangle u u.property v v.property)
      _ = _ := ENNReal.toReal_add (h.finite u u.property).ne (h.finite v v.property).ne
  · intro u
    change (nx u).toReal = 0 ↔ u = 0
    constructor
    · intro hu
      apply Subtype.ext
      exact h.definite u u.property
        ((ENNReal.toReal_eq_zero_iff _).mp hu |>.resolve_right (h.finite u u.property).ne)
    · intro hu
      subst u
      simp [h.zero_norm]

/-- A normed group on the original section submodule, with its given norm. -/
abbrev normedAddCommGroup (h : SectionBanachSpace S nx) :
    NormedAddCommGroup h.submodule :=
  letI := h.sectionNorm
  NormedAddCommGroup.ofCore h.normCore

/-- The scalar action remains the original pointwise scalar action. -/
abbrev normedSpace (h : SectionBanachSpace S nx) :
    letI := h.normedAddCommGroup
    NormedSpace ℝ h.submodule :=
  letI := h.normedAddCommGroup
  NormedSpace.ofCore h.normCore

theorem norm_eq_toReal (h : SectionBanachSpace S nx) (u : h.submodule) :
    letI := h.normedAddCommGroup
    ‖u‖ = (nx u).toReal := rfl

theorem ofReal_norm (h : SectionBanachSpace S nx) (u : h.submodule) :
    letI := h.normedAddCommGroup
    ENNReal.ofReal ‖u‖ = nx u :=
  ENNReal.ofReal_toReal (h.finite u u.property).ne

/-- The explicit section Cauchy-sequence axiom supplies completeness of the
actual section norm, without completing or enlarging the section space. -/
theorem completeSpace (h : SectionBanachSpace S nx) :
    letI := h.normedAddCommGroup
    CompleteSpace h.submodule := by
  letI := h.normedAddCommGroup
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  obtain ⟨v, hv, hlim⟩ := h.complete (fun n => f n) (fun n => (f n).property) (by
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf eps heps
    refine ⟨N, fun i hi j hj => ?_⟩
    have hij := hN i hi j hj
    rw [dist_eq_norm] at hij
    have hh := (ENNReal.ofReal_lt_ofReal_iff heps).mpr hij
    rwa [h.ofReal_norm (f i - f j)] at hh)
  refine ⟨⟨v, hv⟩, Metric.tendsto_atTop.mpr ?_⟩
  intro eps heps
  obtain ⟨N, hN⟩ := hlim eps heps
  refine ⟨N, fun i hi => ?_⟩
  rw [dist_eq_norm]
  apply (ENNReal.ofReal_lt_ofReal_iff heps).mp
  rw [h.ofReal_norm]
  exact hN i hi

/-- Restriction of the given map, without changing its values. -/
def linearMap (hX : SectionBanachSpace S nx) (hY : SectionBanachSpace T ny)
    (A : X → Y) (hmap : Set.MapsTo A S T) (hlin : SectionLinearOn S A) :
    hX.submodule →ₗ[ℝ] hY.submodule where
  toFun u := ⟨A u, hmap u.property⟩
  map_add' u v := Subtype.ext (hlin.2.1 u u.property v v.property)
  map_smul' c u := Subtype.ext (hlin.2.2 c u u.property)

@[simp]
theorem linearMap_apply (hX : SectionBanachSpace S nx) (hY : SectionBanachSpace T ny)
    (A : X → Y) (hmap : Set.MapsTo A S T) (hlin : SectionLinearOn S A)
    (u : hX.submodule) :
    (hX.linearMap hY A hmap hlin u : Y) = A u := rfl

theorem linearMap_norm_le (hX : SectionBanachSpace S nx) (hY : SectionBanachSpace T ny)
    (A : X → Y) (hmap : Set.MapsTo A S T) (hlin : SectionLinearOn S A)
    (C : ℝ≥0) (hC : ∀ u ∈ S, ny (A u) ≤ (C : ℝ≥0∞) * nx u)
    (u : hX.submodule) :
    letI := hX.normedAddCommGroup
    letI := hY.normedAddCommGroup
    ‖hX.linearMap hY A hmap hlin u‖ ≤ (C : ℝ) * ‖u‖ := by
  letI := hX.normedAddCommGroup
  letI := hY.normedAddCommGroup
  change (ny (A u)).toReal ≤ (C : ℝ) * (nx u).toReal
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (hX.finite u u.property).ne) (hC u u.property)
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hh

/-- The bounded linear map is the restriction of the original actual map. -/
def continuousLinearMap (hX : SectionBanachSpace S nx) (hY : SectionBanachSpace T ny)
    (A : X → Y) (hmap : Set.MapsTo A S T) (hlin : SectionLinearOn S A)
    (hbdd : SectionBoundedOn S nx ny A) :
    letI := hX.normedAddCommGroup
    letI := hY.normedAddCommGroup
    letI := hX.normedSpace
    letI := hY.normedSpace
    hX.submodule →L[ℝ] hY.submodule := by
  letI := hX.normedAddCommGroup
  letI := hY.normedAddCommGroup
  letI := hX.normedSpace
  letI := hY.normedSpace
  have bounds : ∃ C : ℝ≥0, ∀ u ∈ S, ny (A u) ≤ (C : ℝ≥0∞) * nx u := hbdd
  exact (hX.linearMap hY A hmap hlin).mkContinuous ((Classical.choose bounds : ℝ≥0) : ℝ)
    (hX.linearMap_norm_le hY A hmap hlin _ (Classical.choose_spec bounds))

@[simp]
theorem continuousLinearMap_apply (hX : SectionBanachSpace S nx)
    (hY : SectionBanachSpace T ny) (A : X → Y)
    (hmap : Set.MapsTo A S T) (hlin : SectionLinearOn S A)
    (hbdd : SectionBoundedOn S nx ny A) (u : hX.submodule) :
    letI := hX.normedAddCommGroup
    letI := hY.normedAddCommGroup
    letI := hX.normedSpace
    letI := hY.normedSpace
    (hX.continuousLinearMap hY A hmap hlin hbdd u : Y) = A u := rfl

/-- The usual continuous-linear-map norm equals the canonical infimum over
all extended section bounds, including the zero-dimensional case. -/
theorem ofReal_norm_continuousLinearMap (hX : SectionBanachSpace S nx)
    (hY : SectionBanachSpace T ny) (A : X → Y)
    (hmap : Set.MapsTo A S T) (hlin : SectionLinearOn S A)
    (hbdd : SectionBoundedOn S nx ny A) :
    letI := hX.normedAddCommGroup
    letI := hY.normedAddCommGroup
    letI := hX.normedSpace
    letI := hY.normedSpace
    ENNReal.ofReal ‖hX.continuousLinearMap hY A hmap hlin hbdd‖ =
      sectionOperatorENorm S nx ny A := by
  letI := hX.normedAddCommGroup
  letI := hY.normedAddCommGroup
  letI := hX.normedSpace
  letI := hY.normedSpace
  let f := hX.continuousLinearMap hY A hmap hlin hbdd
  apply le_antisymm
  · apply le_sInf
    intro C hC
    by_cases htop : C = ⊤
    · simp [htop]
    apply ENNReal.ofReal_le_of_le_toReal
    apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
    intro u
    change (ny (A u)).toReal ≤ C.toReal * (nx u).toReal
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top htop (hX.finite u u.property).ne) (hC u u.property)
    simpa only [ENNReal.toReal_mul] using hh
  · apply sInf_le
    intro u hu
    have hh := ENNReal.ofReal_le_ofReal (f.le_opNorm ⟨u, hu⟩)
    rw [ENNReal.ofReal_mul (norm_nonneg _), hY.ofReal_norm, hX.ofReal_norm] at hh
    exact hh

/-- A concrete section isomorphism induces an equivalence on exactly the
same section sets. The Banach inverse theorem supplies inverse continuity. -/
def continuousLinearEquiv (hX : SectionBanachSpace S nx)
    (hY : SectionBanachSpace T ny) (A : X → Y)
    (hIso : SectionIsomorphism S T nx ny A) :
    letI := hX.normedAddCommGroup
    letI := hY.normedAddCommGroup
    letI := hX.normedSpace
    letI := hY.normedSpace
    hX.submodule ≃L[ℝ] hY.submodule := by
  letI := hX.normedAddCommGroup
  letI := hY.normedAddCommGroup
  letI := hX.normedSpace
  letI := hY.normedSpace
  letI := hX.completeSpace
  letI := hY.completeSpace
  let f := hX.continuousLinearMap hY A hIso.1 hIso.2.1 hIso.2.2.1
  apply ContinuousLinearEquiv.ofBijective f
  · apply LinearMap.ker_eq_bot.mpr
    intro u v huv
    apply Subtype.ext
    exact hIso.2.2.2.1 u.property v.property (congrArg Subtype.val huv)
  · apply LinearMap.range_eq_top.mpr
    intro v
    obtain ⟨u, hu, huv⟩ := hIso.2.2.2.2 v v.property
    exact ⟨⟨u, hu⟩, Subtype.ext huv⟩

@[simp]
theorem continuousLinearEquiv_apply (hX : SectionBanachSpace S nx)
    (hY : SectionBanachSpace T ny) (A : X → Y)
    (hIso : SectionIsomorphism S T nx ny A) (u : hX.submodule) :
    letI := hX.normedAddCommGroup
    letI := hY.normedAddCommGroup
    letI := hX.normedSpace
    letI := hY.normedSpace
    (hX.continuousLinearEquiv hY A hIso u : Y) = A u := rfl

/-- A supplied concrete inverse estimate is preserved by the equivalence. -/
theorem inverse_opNorm_le (hX : SectionBanachSpace S nx)
    (hY : SectionBanachSpace T ny) (A : X → Y)
    (hIso : SectionIsomorphism S T nx ny A) (C : ℝ≥0)
    (hInv : SectionInverseBound S nx ny A C) :
    letI := hX.normedAddCommGroup
    letI := hY.normedAddCommGroup
    letI := hX.normedSpace
    letI := hY.normedSpace
    ‖(hX.continuousLinearEquiv hY A hIso).symm.toContinuousLinearMap‖ ≤ (C : ℝ) := by
  letI := hX.normedAddCommGroup
  letI := hY.normedAddCommGroup
  letI := hX.normedSpace
  letI := hY.normedSpace
  let e := hX.continuousLinearEquiv hY A hIso
  have hbound (u : hX.submodule) : ‖u‖ ≤ (C : ℝ) * ‖e u‖ := by
    change (nx u).toReal ≤ (C : ℝ) * (ny (A u)).toReal
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (hY.finite (A u) (hIso.1 u.property)).ne)
      (hInv u u.property)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal] using hh
  apply ContinuousLinearMap.opNorm_le_bound _ C.coe_nonneg
  intro v
  change ‖e.symm v‖ ≤ (C : ℝ) * ‖v‖
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hbound (e.symm v)

end K24.Global.SectionBanachSpace


/- Bundled from Solutions/K24INV_DualGap.lean. -/

set_option autoImplicit false

open scoped NNReal ENNReal

namespace K24.Global

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

/-- The actual inverse estimate gives the gap for the actual composed dual
functional, with the canonical infimum definition of the operator norm.
No finiteness, completeness, positivity, or nontriviality is silently added. -/
theorem sectionDualGap_of_isomorphism_inverseBound
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}
    {A : X → Y} {C : ℝ≥0}
    (hA : SectionIsomorphism S T nx ny A)
    (hInv : SectionInverseBound S nx ny A C) :
    SectionDualGap S T nx ny A C := by
  intro phi _hlin hphi
  let P : Set ℝ≥0∞ := {b | ∀ u ∈ S,
    ENNReal.ofReal |(phi ∘ A) u| ≤ b * nx u}
  have hP : P.Nonempty := by
    obtain ⟨a, ha⟩ := hA.2.2.1
    obtain ⟨b, hb⟩ := hphi
    refine ⟨(b : ℝ≥0∞) * a, ?_⟩
    intro u hu
    calc
      ENNReal.ofReal |(phi ∘ A) u| ≤ (b : ℝ≥0∞) * ny (A u) := hb _ (hA.1 hu)
      _ ≤ (b : ℝ≥0∞) * ((a : ℝ≥0∞) * nx u) := mul_le_mul_right (ha u hu) _
      _ = ((b : ℝ≥0∞) * a) * nx u := (mul_assoc _ _ _).symm
  have hbound (b : ℝ≥0∞) (hb : b ∈ P) :
      sectionOperatorENorm T ny (fun r : ℝ => ENNReal.ofReal |r|) phi ≤
        (C : ℝ≥0∞) * b := by
    apply sInf_le
    intro v hv
    obtain ⟨u, hu, rfl⟩ := hA.2.2.2.2 v hv
    calc
      ENNReal.ofReal |phi (A u)| ≤ b * nx u := hb u hu
      _ ≤ b * ((C : ℝ≥0∞) * ny (A u)) := mul_le_mul_right (hInv u hu) _
      _ = ((C : ℝ≥0∞) * b) * ny (A u) := by ac_rfl
  change _ ≤ (C : ℝ≥0∞) * sInf P
  rw [sInf_eq_iInf']
  let : Nonempty P := hP.to_subtype
  rw [ENNReal.mul_iInf (by simp)]
  exact le_iInf fun b => hbound b b.property

end K24.Global


/- Bundled from Solutions/K24INV_Neumann.lean. -/

set_option autoImplicit false


/- Reused verbatim modulo namespace/name from accepted source submission
   d2164e9a-4f6e-48fc-ab99-2d93c32cb11c, target
   c530dacb-1066-40aa-bc01-11bfd395c908. This is attribution, not a claim
   that the present task proved the abstract Neumann result. -/
namespace K24.Global.K24INV

/-- The abstract Banach-space perturbation statement in K24, Section 4.
The equivalence is constructed using the convergent Neumann series. -/
theorem neumannPerturbation
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

end K24.Global.K24INV


/- Bundled from Solutions/K24INV_Transfer.lean. -/

set_option autoImplicit false

noncomputable section

open scoped NNReal ENNReal

namespace K24.Global

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y]
  {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞}

/-- Transport back from an equivalence on the actual section submodules.
The equality hypothesis fixes the original map at every admissible section. -/
theorem sectionIsoInverseDual_of_equiv
    (hX : SectionBanachSpace S nx) (hY : SectionBanachSpace T ny)
    (A : X → Y) (C : ℝ≥0) :
    letI := hX.normedAddCommGroup
    letI := hY.normedAddCommGroup
    letI := hX.normedSpace
    letI := hY.normedSpace
    ∀ e : hX.submodule ≃L[ℝ] hY.submodule,
      (∀ u : hX.submodule, (e u : Y) = A u) →
      ‖e.symm.toContinuousLinearMap‖ ≤ (C : ℝ) →
      SectionIsomorphism S T nx ny A ∧
      SectionInverseBound S nx ny A C ∧
      SectionDualGap S T nx ny A C := by
  letI := hX.normedAddCommGroup
  letI := hY.normedAddCommGroup
  letI := hX.normedSpace
  letI := hY.normedSpace
  intro e he hC
  have hIso : SectionIsomorphism S T nx ny A := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rw [← he ⟨u, hu⟩]
      exact (e ⟨u, hu⟩).property
    · refine ⟨?_, ?_, ?_⟩
      · simpa only [he, Submodule.coe_zero] using
          congrArg (fun v : hY.submodule => (v : Y)) e.map_zero
      · intro u hu v hv
        simpa only [he, Submodule.coe_add] using
          congrArg (fun w : hY.submodule => (w : Y)) (e.map_add ⟨u, hu⟩ ⟨v, hv⟩)
      · intro c u hu
        simpa only [he, Submodule.coe_smul] using
          congrArg (fun w : hY.submodule => (w : Y)) (e.map_smul c ⟨u, hu⟩)
    · refine ⟨(ENNReal.ofReal ‖e.toContinuousLinearMap‖).toNNReal, ?_⟩
      intro u hu
      have hh := ENNReal.ofReal_le_ofReal (e.toContinuousLinearMap.le_opNorm ⟨u, hu⟩)
      rw [ENNReal.ofReal_mul (norm_nonneg _), hY.ofReal_norm, hX.ofReal_norm] at hh
      change ny (e ⟨u, hu⟩ : Y) ≤ ENNReal.ofReal ‖e.toContinuousLinearMap‖ * nx u at hh
      rw [he] at hh
      rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
      exact hh
    · intro u hu v hv huv
      have hh : e ⟨u, hu⟩ = e ⟨v, hv⟩ := Subtype.ext (by simpa only [he] using huv)
      exact congrArg (fun w : hX.submodule => (w : X)) (e.injective hh)
    · intro v hv
      refine ⟨e.symm ⟨v, hv⟩, (e.symm ⟨v, hv⟩).property, ?_⟩
      rw [← he, e.apply_symm_apply]
  have hInv : SectionInverseBound S nx ny A C := by
    intro u hu
    have hh : ‖(⟨u, hu⟩ : hX.submodule)‖ ≤ (C : ℝ) * ‖e ⟨u, hu⟩‖ := by
      calc
        _ = ‖e.symm (e ⟨u, hu⟩)‖ := by rw [e.symm_apply_apply]
        _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e ⟨u, hu⟩‖ :=
          e.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ (C : ℝ) * ‖e ⟨u, hu⟩‖ :=
          mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    have hh' := ENNReal.ofReal_le_ofReal hh
    rw [ENNReal.ofReal_mul C.coe_nonneg, hX.ofReal_norm, hY.ofReal_norm, he,
      ENNReal.ofReal_coe_nnreal] at hh'
    exact hh'
  exact ⟨hIso, hInv, sectionDualGap_of_isomorphism_inverseBound hIso hInv⟩


/-- Genuine K24 inverse transfer for the supplied section spaces and the supplied
map `B`, with the exact canonical extended operator norm smallness condition. -/
theorem K24INVProtocol.sectionInverseTransferImpl
    (hX : SectionBanachSpace S nx) (hY : SectionBanachSpace T ny)
    (A B : X → Y) (CA : ℝ≥0) (hCA : 0 < CA)
    (hA : SectionIsomorphism S T nx ny A)
    (hAinv : SectionInverseBound S nx ny A CA)
    (hRmap : Set.MapsTo (fun u => B u - A u) S T)
    (hRlin : SectionLinearOn S (fun u => B u - A u))
    (hRbdd : SectionBoundedOn S nx ny (fun u => B u - A u))
    (hsmall : (CA : ℝ≥0∞) *
      sectionOperatorENorm S nx ny (fun u => B u - A u) < (1 / 2 : ℝ≥0∞)) :
    SectionIsomorphism S T nx ny B ∧
    SectionInverseBound S nx ny B (2 * CA) ∧
    SectionDualGap S T nx ny B (2 * CA) := by
  letI := hX.normedAddCommGroup
  letI := hY.normedAddCommGroup
  letI := hX.normedSpace
  letI := hY.normedSpace
  letI := hX.completeSpace
  letI := hY.completeSpace
  let e := hX.continuousLinearEquiv hY A hA
  let r := hX.continuousLinearMap hY (fun u => B u - A u) hRmap hRlin hRbdd
  have hCAreal : 0 < (CA : ℝ) := by exact_mod_cast hCA
  have heinv : ‖e.symm.toContinuousLinearMap‖ ≤ (CA : ℝ) :=
    hX.inverse_opNorm_le hY A hA CA hAinv
  have hrnorm : ENNReal.ofReal ‖r‖ =
      sectionOperatorENorm S nx ny (fun u => B u - A u) :=
    hX.ofReal_norm_continuousLinearMap hY _ hRmap hRlin hRbdd
  have hsmallreal : (CA : ℝ) * ‖r‖ < (1 / 2 : ℝ) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp
    rw [ENNReal.ofReal_mul CA.coe_nonneg, ENNReal.ofReal_coe_nnreal, hrnorm]
    convert hsmall using 1
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  obtain ⟨eB, heB, heBinv⟩ := K24INV.neumannPerturbation
    hX.submodule hY.submodule e r (CA : ℝ) hCAreal heinv hsmallreal
  have hBval (u : hX.submodule) : (eB u : Y) = B u := by
    have hh := congrArg (fun f : hX.submodule →L[ℝ] hY.submodule => (f u : Y)) heB
    change (eB u : Y) = (e u : Y) + (r u : Y) at hh
    change (eB u : Y) = A u + (B u - A u) at hh
    rw [add_comm, sub_add_cancel] at hh
    exact hh
  apply sectionIsoInverseDual_of_equiv hX hY B (2 * CA) eB hBval
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using heBinv

end K24.Global



universe u v

theorem solution :
  ∀ {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    {S : Set X} {T : Set Y} {nx : X → ℝ≥0∞} {ny : Y → ℝ≥0∞},
    K24.Global.SectionBanachSpace S nx →
    K24.Global.SectionBanachSpace T ny →
    ∀ (A B : X → Y) (CA : ℝ≥0), 0 < CA →
    K24.Global.SectionIsomorphism S T nx ny A →
    K24.Global.SectionInverseBound S nx ny A CA →
    Set.MapsTo (fun u => B u - A u) S T →
    K24.Global.SectionLinearOn S (fun u => B u - A u) →
    K24.Global.SectionBoundedOn S nx ny (fun u => B u - A u) →
    (CA : ℝ≥0∞) * K24.Global.sectionOperatorENorm S nx ny (fun u => B u - A u)
      < (1 / 2 : ℝ≥0∞) →
    K24.Global.SectionIsomorphism S T nx ny B ∧
    K24.Global.SectionInverseBound S nx ny B (2 * CA) ∧
    K24.Global.SectionDualGap S T nx ny B (2 * CA) := by
  exact @K24.Global.K24INVProtocol.sectionInverseTransferImpl
