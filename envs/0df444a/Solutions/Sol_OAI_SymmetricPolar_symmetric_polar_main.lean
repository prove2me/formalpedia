-- Prove2me | solution 1 for OAI.SymmetricPolar.symmetric_polar_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:31:15.606321+00:00
-- url     : https://prove2.me/submissions/0d4f7a6a-3410-4934-bbbe-5fb7c99bbac1

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_OAIQWSP000
import Theorems.Thm_OAI_CylinderNonsqueezing_radius_le_of_map
import Theorems.Thm_OAI_Moser_compactlySupported_deformation
import Theorems.Thm_OAI_PolarStrips_exists_scaled_image

section
-- module Solutions.OAIQW_SymmetricPolar.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_SymmetricPolar.TensorCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u17 u18 u19 u20 u21 u22

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal

open Set Filter Function
open scoped Topology ContDiff

namespace TensorCalculus

variable {E : Type u17} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

attribute [local instance] OAI.TensorCalculus.oneTensorGroup
attribute [local instance] OAI.TensorCalculus.oneTensorSpace
attribute [local instance] OAI.TensorCalculus.twoTensorGroup
attribute [local instance] OAI.TensorCalculus.twoTensorSpace
theorem exteriorD_skew (γ : E → E →L[ℝ] ℝ) (x a b : E) :
    exteriorD γ x a b = -exteriorD γ x b a := by
  simp only [exteriorD_apply]; ring

theorem fderiv_exteriorD {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : DifferentiableAt ℝ (fderiv ℝ γ) x) (d a b : E) :
    fderiv ℝ (exteriorD γ) x d a b =
      fderiv ℝ (fderiv ℝ γ) x d a b - fderiv ℝ (fderiv ℝ γ) x d b a := by
  change fderiv ℝ (alt ∘ fderiv ℝ γ) x d a b = _
  rw [fderiv_comp x (ContinuousLinearMap.differentiableAt (alt (E := E))) hγ]
  simp

theorem exteriorD_closed {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : ContDiffAt ℝ ∞ γ x) (a b c : E) :
    fderiv ℝ (exteriorD γ) x a b c + fderiv ℝ (exteriorD γ) x b c a +
      fderiv ℝ (exteriorD γ) x c a b = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ γ) x :=
    (hγ.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiableAt (by simp)
  have hs := hγ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [fderiv_exteriorD hd]
  have h1 := congrArg (fun L : E →L[ℝ] ℝ => L c) (hs.eq a b)
  have h2 := congrArg (fun L : E →L[ℝ] ℝ => L a) (hs.eq b c)
  have h3 := congrArg (fun L : E →L[ℝ] ℝ => L b) (hs.eq c a)
  linarith

end
end TensorCalculus

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PotentialForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u27 u28 u29

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped Topology ContDiff

variable {E : Type u27} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

attribute [local instance] OAI.ComplexPotential.oneTensorGroup
attribute [local instance] OAI.ComplexPotential.oneTensorSpace
attribute [local instance] OAI.ComplexPotential.twoTensorGroup
attribute [local instance] OAI.ComplexPotential.twoTensorSpace
theorem contDiff_dc (J : E →L[ℝ] E) {φ : E → ℝ}
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (dc J φ) := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => contDiffAt_dc J (hφ.contDiffAt (x := x))

theorem ddc_skew (J : E →L[ℝ] E) (φ : E → ℝ) (x a b : E) :
    ddc J φ x a b = -ddc J φ x b a := exteriorD_skew _ _ _ _

theorem contDiffAt_ddc (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) : ContDiffAt ℝ ∞ (ddc J φ) x := by
  change ContDiffAt ℝ ∞ (alt ∘ fderiv ℝ (dc J φ)) x
  exact (alt (E := E)).contDiff.contDiffAt.comp x
    ((contDiffAt_dc J hφ).fderiv_right (m := ∞) (by simp))

theorem ddc_closed (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (a b c : E) :
    fderiv ℝ (ddc J φ) x a b c + fderiv ℝ (ddc J φ) x b c a +
      fderiv ℝ (ddc J φ) x c a b = 0 := exteriorD_closed (contDiffAt_dc J hφ) a b c

theorem dc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : dc J φ x = dc J ψ x := by
  rw [dc, dc, h.fderiv_eq]

theorem ddc_congr (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (h : φ =ᶠ[𝓝 x] ψ) : ddc J φ x = ddc J ψ x := by
  have he : dc J φ =ᶠ[𝓝 x] dc J ψ := h.eventuallyEq_nhds.mono (fun y hy => dc_congr J hy)
  simpa only [ddc, exteriorD] using congrArg alt he.fderiv_eq

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus
open scoped ContDiff Topology

variable {E : Type u28} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

theorem dc_norm_sq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b) (x : E) :
    dc J (fun x : E => ‖x‖^2) x = (1 / 2 : ℝ) • standardTensor J x := by
  ext a
  rw [dc_apply, fderiv_norm_sq_apply]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, standardTensor_apply]
  rw [hsk]
  ring

theorem ddc_norm_sq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b) (x : E) :
    ddc J (fun x : E => ‖x‖^2) x = standardTensor J := by
  have he : dc J (fun x : E => ‖x‖^2) = fun x => (1 / 2 : ℝ) • standardTensor J x :=
    funext (dc_norm_sq J hsk)
  apply ContinuousLinearMap.ext
  intro a
  apply ContinuousLinearMap.ext
  intro b
  rw [ddc, he, exteriorD_apply]
  have hd : fderiv ℝ (fun x => (1 / 2 : ℝ) • standardTensor J x) x =
      (1 / 2 : ℝ) • standardTensor J := by
    exact ((standardTensor J).hasFDerivAt.const_smul (1 / 2 : ℝ)).fderiv
  rw [hd]
  simp only [smul_apply, smul_eq_mul, standardTensor_apply]
  have hh : inner (𝕜 := ℝ) (J b) a = -inner (𝕜 := ℝ) (J a) b := by
    rw [real_inner_comm, hsk]
  rw [hh]
  ring

theorem standardTensor_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, ‖J a‖ = ‖a‖) (a : E) :
    standardTensor J a (J a) = ‖a‖^2 := by
  rw [standardTensor_apply, real_inner_self_eq_norm_sq, hJ]

theorem isInvertible_of_positive_complex_line [FiniteDimensional ℝ E]
    (B : TwoTensor E) (J : E →L[ℝ] E) (hp : ∀ a : E, a ≠ 0 → 0 < B a (J a)) :
    B.IsInvertible := by
  have hi : Function.Injective B := by
    intro a b hab
    have hz : B (a - b) = 0 := by rw [map_sub, hab, sub_self]
    by_contra hn
    have hpos := hp (a - b) (sub_ne_zero.mpr hn)
    rw [hz, zero_apply] at hpos
    exact (lt_irrefl 0) hpos
  let e := (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv
  let L : E →L[ℝ] E := e.symm.toContinuousLinearMap.comp B
  have hL : Function.Injective L := e.symm.injective.comp hi
  have hsL : Function.Surjective L := LinearMap.surjective_of_injective hL
  have hs : Function.Surjective B := by
    intro v
    obtain ⟨x, hx⟩ := hsL (e.symm v)
    refine ⟨x, ?_⟩
    exact e.symm.injective hx
  exact ⟨ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped ContDiff Topology

variable {E : Type u29} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

attribute [local instance] OAI.ComplexPotential.linearOneGroup
attribute [local instance] OAI.ComplexPotential.linearOneSpace
attribute [local instance] OAI.ComplexPotential.linearTwoGroup
local instance linearTwoSpace_re4bb3c_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
theorem ddc_neg (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) :
    ddc J (fun y => -φ y) x = -ddc J φ x := by
  simpa only [neg_one_mul, neg_one_smul] using ddc_const_smul J (-1) hφ

theorem ddc_sub (J : E →L[ℝ] E) {φ ψ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hψ : ContDiffAt ℝ ∞ ψ x) :
    ddc J (fun y => φ y - ψ y) x = ddc J φ x - ddc J ψ x := by
  simp_rw [sub_eq_add_neg]
  rw [ddc_add J hφ hψ.neg, ddc_neg J hψ]

theorem ddc_sub_const (J : E →L[ℝ] E) {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (c : ℝ) :
    ddc J (fun y => φ y - c) x = ddc J φ x := by
  rw [ddc_sub J hφ contDiffAt_const, ddc_const, sub_zero]

theorem IsPSHAt.sub_const {J : E →L[ℝ] E} {φ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (c : ℝ) : IsPSHAt J (fun y => φ y - c) x := by
  refine ⟨hφ.1.sub contDiffAt_const, fun a => ?_⟩
  rw [ddc_sub_const J hφ.1 c]
  exact hφ.2 a

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PotentialDeformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u30 u31 u32 u33 u34 u35

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff

open Set Filter Function
open scoped ContDiff Topology

namespace CompactExtension
noncomputable section

variable {E : Type u30} {F : Type u31} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem eventuallyEq_extend {U : Set E} (hU : IsOpen U) (f : E → F) {x : E} (hx : x ∈ U) :
    extend U f =ᶠ[𝓝 x] f := by
  classical
  filter_upwards [hU.mem_nhds hx] with y hy
  exact indicator_of_mem hy f

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem tsupport_extend_subset {U C : Set E} (hC : IsClosed C) {f : E → F}
    (hf : ∀ x ∈ U, x ∉ C → f x = 0) : tsupport (extend U f) ⊆ C := by
  classical
  apply closure_minimal _ hC
  intro x hx
  by_contra hn
  have hh : extend U f x = 0 := by
    by_cases hU : x ∈ U
    · exact (indicator_of_mem hU f).trans (hf x hU hn)
    · exact indicator_of_notMem hU f
  exact hx hh

theorem contDiff_extend {U C : Set E} (hU : IsOpen U) (hC : IsClosed C) (hCU : C ⊆ U)
    {f : E → F} (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x)
    (hzero : ∀ x ∈ U, x ∉ C → f x = 0) : ContDiff ℝ ∞ (extend U f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hf x hx).congr_of_eventuallyEq (eventuallyEq_extend hU f hx)
  · have hxc : x ∉ C := fun hc => hx (hCU hc)
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hC.isOpen_compl.mem_nhds hxc] with y hy
    exact image_eq_zero_of_notMem_tsupport (fun ht => hy (tsupport_extend_subset hC hzero ht))

end
end CompactExtension

namespace ComplexPotential

open TensorCalculus Set Filter Function
open scoped ContDiff Topology

noncomputable section

variable {E : Type u32} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

attribute [local instance] OAI.ComplexPotential.moserOneGroup
attribute [local instance] OAI.ComplexPotential.moserOneSpace
attribute [local instance] OAI.ComplexPotential.moserTwoGroup
attribute [local instance] OAI.ComplexPotential.moserTwoSpace
omit [FiniteDimensional ℝ E] in
theorem tsupport_dc_subset (J : E →L[ℝ] E) (φ : E → ℝ) :
    tsupport (dc J φ) ⊆ tsupport φ :=
  (tsupport_comp_subset (map_zero (dcOp J)) (fderiv ℝ φ)).trans (tsupport_fderiv_subset ℝ)

omit [FiniteDimensional ℝ E] in
theorem fderiv_homeomorph_apply_symm (F : E ≃ₜ E)
    (hF : ContDiff ℝ ∞ (F : E → E)) (hFi : ContDiff ℝ ∞ (F.symm : E → E)) (x a : E) :
    fderiv ℝ (F : E → E) (F.symm x) (fderiv ℝ (F.symm : E → E) x a) = a := by
  have he : (F : E → E) ∘ (F.symm : E → E) = id := funext F.apply_symm_apply
  have hd := fderiv_comp x (hF.differentiable (by simp) (F.symm x))
    (hFi.differentiable (by simp) x)
  rw [he, fderiv_id] at hd
  exact (congrArg (fun L : E →L[ℝ] E => L a) hd).symm

theorem exists_potential_transport (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖)
    {U C : Set E} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {τ T : E → ℝ} (hτ : ∀ x ∈ U, IsPSHAt J τ x) (hT : ∀ x ∈ U, IsPSHAt J T x)
    (heq : ∀ x ∈ U, x ∉ C → T x = τ x) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x, x ∉ U → F x = x) ∧ (∀ x, F x ∈ U ↔ x ∈ U) ∧
      ∀ x ∈ U, ∀ a b,
        ddc J (fun y => ‖y‖^2 + τ y) (F x) (fderiv ℝ (F : E → E) x a)
          (fderiv ℝ (F : E → E) x b) = ddc J (fun y => ‖y‖^2 + T y) x a b := by
  let g := CompactExtension.extend U (fun y => T y - τ y)
  have hz : ∀ x ∈ U, x ∉ C → T x - τ x = 0 := by
    intro x hx hxc
    rw [heq x hx hxc, sub_self]
  have hg : ContDiff ℝ ∞ g := CompactExtension.contDiff_extend hU hC.isClosed hCU
    (fun x hx => (hT x hx).1.sub (hτ x hx).1) hz
  have hgs : tsupport g ⊆ C := CompactExtension.tsupport_extend_subset hC.isClosed hz
  let γ := dc J g
  let W := ddc J (fun y => ‖y‖^2 + τ y)
  have hγ : ContDiff ℝ ∞ γ := contDiff_dc J hg
  have hsγ : tsupport γ ⊆ C := (tsupport_dc_subset J g).trans hgs
  have hcγ : HasCompactSupport γ := hC.of_isClosed_subset (isClosed_tsupport _) hsγ
  have hdiff (x : E) (hx : x ∈ U) :
      exteriorD γ x = ddc J T x - ddc J τ x := by
    change ddc J g x = _
    rw [ddc_congr J (CompactExtension.eventuallyEq_extend hU _ hx)]
    exact ddc_sub J (hT x hx).1 (hτ x hx).1
  have hnorm (x : E) (hx : x ∈ U) : W x = standardTensor J + ddc J τ x := by
    dsimp [W]
    rw [ddc_add J (contDiff_norm_sq ℝ).contDiffAt (hτ x hx).1, ddc_norm_sq J hsk]
  have hW : ∀ x ∈ U, ContDiffAt ℝ ∞ W x := fun x hx =>
    contDiffAt_ddc J ((contDiff_norm_sq ℝ).contDiffAt.add (hτ x hx).1)
  have hWi : ∀ x ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, (W x + s • exteriorD γ x).IsInvertible := by
    intro x hx s hs
    apply isInvertible_of_positive_complex_line _ J
    intro a ha
    rw [hnorm x hx, hdiff x hx]
    simp only [add_apply, smul_apply, sub_apply, smul_eq_mul,
      standardTensor_complex_line J hJ]
    have hn : 0 < ‖a‖^2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
    have h₀ := mul_nonneg (sub_nonneg.mpr hs.2) ((hτ x hx).2 a)
    have h₁ := mul_nonneg hs.1 ((hT x hx).2 a)
    nlinarith
  obtain ⟨F, hF, hFi, hout, hmap, hpull⟩ := Moser.compactlySupported_deformation hU hW
    (fun x _ a b => ddc_skew J _ x a b)
    (fun x hx a b c => ddc_closed J ((contDiff_norm_sq ℝ).contDiffAt.add (hτ x hx).1) a b c)
    hγ hcγ (hsγ.trans hCU) hWi
  refine ⟨F.symm, hFi, hF, ?_, ?_, ?_⟩
  · intro x hx
    exact (F.symm_apply_eq.mpr (hout x hx).symm)
  · intro x
    simpa using (hmap (F.symm x)).symm
  · intro x hx a b
    have hix : F.symm x ∈ U := (hmap (F.symm x)).mp (by simpa using hx)
    have hh := hpull (F.symm x) hix (fderiv ℝ (F.symm : E → E) x a)
      (fderiv ℝ (F.symm : E → E) x b)
    rw [F.apply_symm_apply, fderiv_homeomorph_apply_symm F hF hFi,
      fderiv_homeomorph_apply_symm F hF hFi, hnorm x hx, hdiff x hx] at hh
    have hend : standardTensor J + ddc J τ x + (ddc J T x - ddc J τ x) =
        ddc J (fun y => ‖y‖^2 + T y) x := by
      rw [ddc_add J (contDiff_norm_sq ℝ).contDiffAt (hT x hx).1, ddc_norm_sq J hsk]
      abel
    rw [hend] at hh
    exact hh.symm

end
end ComplexPotential

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped ContDiff Topology

variable {E : Type u33} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

theorem dc_scalar_comp (J : E →L[ℝ] E) {φ : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) (hh : DifferentiableAt ℝ h (φ x)) :
    dc J (h ∘ φ) x = deriv h (φ x) • dc J φ x := by
  have hd := (hh.hasDerivAt.comp_hasFDerivAt x hφ.hasFDerivAt).fderiv
  ext a
  rw [dc_apply, hd]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  ring

theorem exteriorD_smul_one {γ : E → E →L[ℝ] ℝ} {s : E → ℝ} {x : E}
    (hs : DifferentiableAt ℝ s x) (hγ : DifferentiableAt ℝ γ x) (a b : E) :
    exteriorD (fun y => s y • γ y) x a b = s x * exteriorD γ x a b +
      fderiv ℝ s x a * γ x b - fderiv ℝ s x b * γ x a := by
  simp only [exteriorD_apply, fderiv_fun_smul hs hγ, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

theorem ddc_scalar_comp (J : E →L[ℝ] E) {φ : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hh : ContDiffAt ℝ ∞ h (φ x)) (a b : E) :
    ddc J (h ∘ φ) x a b = deriv h (φ x) * ddc J φ x a b +
      deriv (deriv h) (φ x) *
        (fderiv ℝ φ x b * fderiv ℝ φ x (J a) -
          fderiv ℝ φ x a * fderiv ℝ φ x (J b)) / 4 := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (h ∘ φ) =ᶠ[𝓝 x] fun y => deriv h (φ y) • dc J φ y := by
    filter_upwards [(hφ.of_le h1).eventually (by simp),
      hφ.continuousAt ((hh.of_le h1).eventually (by simp))] with y hy hz
    exact dc_scalar_comp J (hy.differentiableAt one_ne_zero)
      ((show ContDiffAt ℝ (1 : ℕ∞ω) h (φ y) from hz).differentiableAt one_ne_zero)
  have hdh := (hh.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hs : DifferentiableAt ℝ (fun y => deriv h (φ y)) x :=
    hdh.comp x (hφ.differentiableAt (by simp))
  have hd : fderiv ℝ (fun y => deriv h (φ y)) x =
      deriv (deriv h) (φ x) • fderiv ℝ φ x :=
    (hdh.hasDerivAt.comp_hasFDerivAt x (hφ.differentiableAt (by simp)).hasFDerivAt).fderiv
  have heD : exteriorD (dc J (h ∘ φ)) x =
      exteriorD (fun y => deriv h (φ y) • dc J φ y) x := by
    unfold exteriorD
    rw [he.fderiv_eq]
  rw [ddc, heD, exteriorD_smul_one hs ((contDiffAt_dc J hφ).differentiableAt (by simp))]
  rw [hd]
  simp only [smul_apply, smul_eq_mul, dc_apply]
  change _ = deriv h (φ x) * exteriorD (dc J φ) x a b + _
  ring

theorem ddc_scalar_comp_complex_line (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {φ : E → ℝ} {h : ℝ → ℝ} {x : E}
    (hφ : ContDiffAt ℝ ∞ φ x) (hh : ContDiffAt ℝ ∞ h (φ x)) (a : E) :
    ddc J (h ∘ φ) x a (J a) = deriv h (φ x) * ddc J φ x a (J a) +
      deriv (deriv h) (φ x) * ((fderiv ℝ φ x a)^2 + (fderiv ℝ φ x (J a))^2) / 4 := by
  rw [ddc_scalar_comp J hφ hh, hJ, map_neg]
  ring

theorem IsPSHAt.scalar_comp (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {φ : E → ℝ} {h : ℝ → ℝ} {x : E} (hφ : IsPSHAt J φ x)
    (hh : ContDiffAt ℝ ∞ h (φ x)) (hmono : 0 ≤ deriv h (φ x))
    (hconv : 0 ≤ deriv (deriv h) (φ x)) : IsPSHAt J (h ∘ φ) x := by
  refine ⟨hh.comp x hφ.1, fun a => ?_⟩
  rw [ddc_scalar_comp_complex_line J hJ hφ.1 hh]
  exact add_nonneg (mul_nonneg hmono (hφ.2 a))
    (div_nonneg (mul_nonneg hconv (add_nonneg (sq_nonneg _) (sq_nonneg _))) (by norm_num))

end
end ComplexPotential

namespace ComplexPotential

variable {E : Type u34} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem complex_line_inner_sq_le (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (x a : E) :
    (inner (𝕜 := ℝ) x a)^2 + (inner (𝕜 := ℝ) x (J a))^2 ≤ ‖x‖^2 * ‖a‖^2 := by
  let p := inner (𝕜 := ℝ) x a
  let q := inner (𝕜 := ℝ) x (J a)
  have hxa : inner (𝕜 := ℝ) (J x) a = -q := by
    dsimp [q]
    linarith [hsk x a]
  have hxj : inner (𝕜 := ℝ) x (J x) = 0 := by
    linarith [hsk x x, real_inner_comm x (J x)]
  have hjx : inner (𝕜 := ℝ) (J x) x = 0 := by rw [real_inner_comm, hxj]
  let w := p • x - q • J x
  have hw : inner (𝕜 := ℝ) w a = p^2 + q^2 := by
    dsimp [w]
    simp only [inner_sub_left, real_inner_smul_left, hxa]
    change p * p - q * (-q) = _
    ring
  have hww : inner (𝕜 := ℝ) w w = (p^2 + q^2) * ‖x‖^2 := by
    dsimp [w]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hxj, hjx]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hJ]
    ring
  have hcs := real_inner_mul_inner_self_le w a
  rw [hw, hww, real_inner_self_eq_norm_sq] at hcs
  change p^2 + q^2 ≤ ‖x‖^2 * ‖a‖^2
  rcases eq_or_lt_of_le (add_nonneg (sq_nonneg p) (sq_nonneg q)) with hs | hs
  · rw [← hs]
    positivity
  · exact (mul_le_mul_iff_right₀ hs).mp (by nlinarith [hcs])

end ComplexPotential

namespace ComplexPotential

open Set Filter
open scoped ContDiff Topology

noncomputable section

theorem second_deriv_log_add (δ t : ℝ) (ht : t + δ ≠ 0) :
    deriv (deriv (fun s => Real.log (s + δ))) t = -1 / (t + δ)^2 := by
  have he : deriv (fun s => Real.log (s + δ)) = fun t => (t + δ)⁻¹ :=
    funext (deriv_log_add δ)
  rw [he]
  exact ((hasDerivAt_id t).add_const δ |>.inv ht).deriv

variable {E : Type u35} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiffAt_logNormSq (δ : ℝ) {x : E} (hx : ‖x‖^2 + δ ≠ 0) :
    ContDiffAt ℝ ∞ (logNormSq δ) x :=
  ((contDiff_norm_sq ℝ).contDiffAt.add contDiffAt_const).log hx

theorem ddc_logNormSq_complex_line (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (hJJ : ∀ a, J (J a) = -a)
    (δ : ℝ) {x : E} (hx : ‖x‖^2 + δ ≠ 0) (a : E) :
    ddc J (logNormSq δ) x a (J a) = ‖a‖^2 / (‖x‖^2 + δ) -
      ((inner (𝕜 := ℝ) x a)^2 + (inner (𝕜 := ℝ) x (J a))^2) / (‖x‖^2 + δ)^2 := by
  have hl : ContDiffAt ℝ ∞ (fun t : ℝ => Real.log (t + δ)) (‖x‖^2) :=
    (contDiffAt_id.add contDiffAt_const).log hx
  have he := ddc_scalar_comp_complex_line J hJJ (contDiff_norm_sq ℝ).contDiffAt hl a
  rw [ddc_norm_sq J hsk, standardTensor_complex_line J hJ,
    deriv_log_add, second_deriv_log_add δ _ hx, fderiv_norm_sq_apply] at he
  simp only [smul_apply, innerSL_apply_apply] at he
  change ddc J (logNormSq δ) x a (J a) = _ at he
  rw [he]
  ring

theorem isPSHAt_logNormSq (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (hJJ : ∀ a, J (J a) = -a)
    {δ : ℝ} (hδ : 0 ≤ δ) {x : E} (hx : 0 < ‖x‖^2 + δ) :
    IsPSHAt J (logNormSq δ) x := by
  refine ⟨contDiffAt_logNormSq δ hx.ne', fun a => ?_⟩
  rw [ddc_logNormSq_complex_line J hsk hJ hJJ δ hx.ne']
  have hineq := complex_line_inner_sq_le J hsk hJ x a
  have hnum : (inner (𝕜 := ℝ) x a)^2 + (inner (𝕜 := ℝ) x (J a))^2 ≤
      ‖a‖^2 * (‖x‖^2 + δ) := by
    nlinarith [mul_nonneg (sq_nonneg ‖a‖) hδ]
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (sq_pos_of_pos hx) hx).mpr
  nlinarith [mul_le_mul_of_nonneg_right hnum hx.le]

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.RegularizedMaximum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u36 u37

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace SmoothPositivePart

noncomputable section

theorem hasDerivAt_primitive (t : ℝ) : HasDerivAt primitive (Real.smoothTransition t) t := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact Real.smoothTransition.continuous.intervalIntegrable _ _
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_univ
      (fun _ _ => Real.smoothTransition.continuousAt) t (mem_univ t)
  · exact Real.smoothTransition.continuousAt

@[simp] theorem deriv_primitive : deriv primitive = Real.smoothTransition :=
  funext (fun t => (hasDerivAt_primitive t).deriv)

theorem primitive_smooth : ContDiff ℝ ∞ primitive := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun t => (hasDerivAt_primitive t).differentiableAt,
    deriv_primitive ▸ Real.smoothTransition.contDiff⟩

theorem primitive_of_nonpos {t : ℝ} (ht : t ≤ 0) : primitive t = 0 := by
  calc
    primitive t = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      apply Real.smoothTransition.zero_of_nonpos
      exact le_trans hs.2 (max_eq_left ht).le
    _ = 0 := intervalIntegral.integral_zero

theorem primitive_one_mem : primitive 1 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro s _
    exact Real.smoothTransition.nonneg s
  · calc
      primitive 1 ≤ ∫ s in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · exact Real.smoothTransition.continuous.intervalIntegrable _ _
        · exact continuous_const.intervalIntegrable _ _
        · intro s _
          exact Real.smoothTransition.le_one s
      _ = 1 := by simp

theorem primitive_of_one_le {t : ℝ} (ht : 1 ≤ t) : primitive t = t + (primitive 1 - 1) := by
  have he : (∫ s in (1 : ℝ)..t, Real.smoothTransition s) = t - 1 := by
    calc
      _ = ∫ s in (1 : ℝ)..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact Real.smoothTransition.one_of_one_le (le_trans (by simp [ht]) hs.1)
      _ = t - 1 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (Real.smoothTransition.continuous.intervalIntegrable (μ := volume) (0 : ℝ) 1)
    (Real.smoothTransition.continuous.intervalIntegrable (1 : ℝ) t)
  change primitive 1 + _ = primitive t at hadd
  rw [he] at hadd
  linarith

theorem shift_mem : shift ∈ Icc (-1 : ℝ) 0 := by
  have h := primitive_one_mem
  change -1 ≤ primitive 1 - 1 ∧ primitive 1 - 1 ≤ 0
  constructor <;> linarith [h.1, h.2]

theorem positivePart_smooth : ContDiff ℝ ∞ positivePart :=
  primitive_smooth.comp (contDiff_id.sub contDiff_const)

theorem positivePart_zero {t : ℝ} (ht : t ≤ -1) : positivePart t = 0 := by
  apply primitive_of_nonpos
  linarith [shift_mem.1]

theorem positivePart_eq_self {t : ℝ} (ht : 1 ≤ t) : positivePart t = t := by
  rw [positivePart, primitive_of_one_le (by linarith [shift_mem.2])]
  unfold shift
  ring

theorem deriv_positivePart (t : ℝ) : deriv positivePart t = Real.smoothTransition (t - shift) := by
  change deriv (fun t => primitive (t - shift)) t = _
  simpa only [mul_one, Function.comp_def, id_eq] using
    ((hasDerivAt_primitive (t - shift)).comp t ((hasDerivAt_id t).sub_const shift)).deriv

theorem deriv_positivePart_mem (t : ℝ) : deriv positivePart t ∈ Icc (0 : ℝ) 1 := by
  rw [deriv_positivePart]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem second_deriv_positivePart_nonneg (t : ℝ) : 0 ≤ deriv (deriv positivePart) t := by
  apply Monotone.deriv_nonneg
  intro x y hxy
  rw [deriv_positivePart, deriv_positivePart]
  exact Real.smoothTransition.monotone (sub_le_sub_right hxy _)

theorem smoothMax_left {h p : ℝ} (hp : p + 1 ≤ h) : smoothMax h p = h := by
  rw [smoothMax, positivePart_eq_self (by linarith)]
  ring

theorem smoothMax_right {h p : ℝ} (hp : h + 1 ≤ p) : smoothMax h p = p := by
  rw [smoothMax, positivePart_zero (by linarith), add_zero]

end
end SmoothPositivePart

namespace ComplexPotential

open TensorCalculus SmoothPositivePart Set Filter
open scoped ContDiff Topology

variable {E : Type u36} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

local instance maxOneGroup_re4bb3c_1 : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance maxOneSpace_re4bb3c_1 : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance maxTwoGroup_re4bb3c_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance maxTwoSpace_re4bb3c_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
theorem IsPSHAt.smoothMax {J : E →L[ℝ] E} (hJ : ∀ a, J (J a) = -a)
    {φ ψ : E → ℝ} {x : E} (hφ : IsPSHAt J φ x) (hψ : IsPSHAt J ψ x) :
    IsPSHAt J (fun y => smoothMax (φ y) (ψ y)) x := by
  have hdiff := hφ.1.sub hψ.1
  have hs : ContDiffAt ℝ ∞ (positivePart ∘ fun y => φ y - ψ y) x :=
    positivePart_smooth.contDiffAt.comp x hdiff
  refine ⟨hψ.1.add hs, fun a => ?_⟩
  change 0 ≤ ddc J (fun y => ψ y + (positivePart ∘ fun z => φ z - ψ z) y) x a (J a)
  rw [ddc_add J hψ.1 hs, add_apply, add_apply,
    ddc_scalar_comp_complex_line J hJ hdiff positivePart_smooth.contDiffAt,
    ddc_sub J hφ.1 hψ.1, sub_apply, sub_apply]
  have hβ := deriv_positivePart_mem (φ x - ψ x)
  have h2 := second_deriv_positivePart_nonneg (φ x - ψ x)
  have hpos : 0 ≤ (1 - deriv positivePart (φ x - ψ x)) * ddc J ψ x a (J a) +
      deriv positivePart (φ x - ψ x) * ddc J φ x a (J a) :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hβ.2) (hψ.2 a))
      (mul_nonneg hβ.1 (hφ.2 a))
  have hquad : 0 ≤ deriv (deriv positivePart) (φ x - ψ x) *
      ((fderiv ℝ (fun y => φ y - ψ y) x a)^2 +
        (fderiv ℝ (fun y => φ y - ψ y) x (J a))^2) / 4 := by positivity
  nlinarith

theorem IsPSHAt.congr {J : E →L[ℝ] E} {φ ψ : E → ℝ} {x : E}
    (hφ : IsPSHAt J φ x) (he : ψ =ᶠ[𝓝 x] φ) : IsPSHAt J ψ x := by
  refine ⟨hφ.1.congr_of_eventuallyEq he, fun a => ?_⟩
  rw [ddc_congr J he]
  exact hφ.2 a

end
end ComplexPotential

namespace ComplexPotential

open SmoothPositivePart Set Filter
open scoped ContDiff Topology

variable {E : Type u37} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

omit [NormedSpace ℝ E] in
theorem gluedPotential_outer (R : ℝ) (H P : E → ℝ) {x : E} (hx : R ≤ ‖x‖) :
    gluedPotential R H P x = H x := by
  classical
  simp [gluedPotential, not_lt.mpr hx]

omit [NormedSpace ℝ E] in
theorem gluedPotential_inner {r R : ℝ} (hrR : r < R) (H P : E → ℝ)
    (hdom : ∀ x : E, x ≠ 0 → ‖x‖ ≤ r → H x + 1 ≤ P x) {x : E} (hx : ‖x‖ ≤ r) :
    gluedPotential R H P x = P x := by
  classical
  have hR : ‖x‖ < R := hx.trans_lt hrR
  by_cases hzero : x = 0
  · rw [gluedPotential, ite_eq_left hR, ite_eq_left hzero]
  · rw [gluedPotential, ite_eq_left hR, ite_eq_right hzero, smoothMax_right (hdom x hzero hx)]

theorem isPSHAt_gluedPotential (J : E →L[ℝ] E) (hJ : ∀ a, J (J a) = -a)
    {U : Set E} {r R : ℝ} (hr : 0 < r) (hrR : r < R) (H P : E → ℝ)
    (hH : ∀ x ∈ U, x ≠ 0 → IsPSHAt J H x)
    (hP : ∀ x ∈ U, IsPSHAt J P x)
    (hinner : ∀ x : E, x ≠ 0 → ‖x‖ ≤ r → H x + 1 ≤ P x)
    (houter : ∀ x ∈ U, ‖x‖ = R → P x + 1 < H x)
    {x : E} (hx : x ∈ U) : IsPSHAt J (gluedPotential R H P) x := by
  classical
  have hRpos : 0 < R := hr.trans hrR
  by_cases hzero : x = 0
  · have hn : ‖x‖ < r := by simpa [hzero] using hr
    apply (hP x hx).congr
    filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hn] with y hy
    exact gluedPotential_inner hrR H P hinner hy.le
  have hHx := hH x hx hzero
  have hPx := hP x hx
  rcases lt_trichotomy ‖x‖ R with hn | hn | hn
  · apply (hHx.smoothMax hJ hPx).congr
    filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hn,
      eventually_ne_nhds hzero] with y hy hy0
    simp [gluedPotential, hy, hy0]
  · apply hHx.congr
    have hlt := houter x hx hn
    filter_upwards [(hPx.1.continuousAt.add continuousAt_const).eventually_lt
      hHx.1.continuousAt hlt, eventually_ne_nhds hzero] with y hy hy0
    by_cases hny : ‖y‖ < R
    · simp [gluedPotential, hny, hy0, smoothMax_left hy.le]
    · simp [gluedPotential, hny]
  · apply hHx.congr
    filter_upwards [continuousAt_const.eventually_lt continuous_norm.continuousAt hn] with y hy
    exact gluedPotential_outer R H P hy.le

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.RadialMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u38 u39 u40

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace RadialSymplectic

open Set Filter Function TensorCalculus
open scoped Topology ContDiff

variable {E : Type u38} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

attribute [local instance] OAI.RadialSymplectic.oneTensorGroup
attribute [local instance] OAI.RadialSymplectic.oneTensorSpace
local instance twoTensorGroup_re4bb3c_1 : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance twoTensorSpace_re4bb3c_1 : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
theorem fderiv_radialMap {α : E → ℝ} {x : E} (hα : DifferentiableAt ℝ α x) (a : E) :
    fderiv ℝ (radialMap α) x a = α x • a + (fderiv ℝ α x a) • x := by
  have hh := hα.hasFDerivAt.smul (hasFDerivAt_id x)
  have he := congrArg (fun L : E →L[ℝ] E => L a) hh.fderiv
  change fderiv ℝ (radialMap α) x a = _ at he
  simpa only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, id_eq] using he

theorem fderiv_radialPrimitive (B : TwoTensor E) {α : E → ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (a b : E) :
    fderiv ℝ (radialPrimitive B α) x a b =
      (α x ^ 2 / 2) * B a b + α x * fderiv ℝ α x a * B x b := by
  have hs : HasFDerivAt (fun y => α y ^ 2 / 2) (α x • fderiv ℝ α x) x := by
    convert! (hα.hasFDerivAt.pow 2).mul_const (1 / 2 : ℝ) using 1 <;>
      simp [div_eq_mul_inv, smul_smul]
  have hh := hs.smul B.hasFDerivAt
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) hh.fderiv
  change fderiv ℝ (radialPrimitive B α) x a b = _ at he
  simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, mul_assoc] using he

theorem radial_pullback (B : TwoTensor E) (hsk : ∀ a b, B a b = -B b a)
    {α : E → ℝ} {x : E} (hα : DifferentiableAt ℝ α x) (a b : E) :
    B (fderiv ℝ (radialMap α) x a) (fderiv ℝ (radialMap α) x b) =
      exteriorD (radialPrimitive B α) x a b := by
  have hz : B x x = 0 := by have hh := hsk x x; linarith
  simp only [fderiv_radialMap hα, exteriorD_apply, fderiv_radialPrimitive B hα,
    map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hz, mul_zero, add_zero]
  rw [hsk a x, hsk b a]
  ring

end
end RadialSymplectic

open Set
open scoped Topology ContDiff

namespace RadialSymplectic

noncomputable section

theorem radiusSq_inverse {μ δ t : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (ht : 0 ≤ t) :
    radiusSq μ δ (inverseScaleSq μ δ t * t) = t := by
  have hq := inverseScaleSq_pos hμ hδ ht
  have hquad := inverseScaleSq_quadratic hμ hδ ht
  have hd : 0 < inverseScaleSq μ δ t * t + δ :=
    add_pos_of_nonneg_of_pos (mul_nonneg hq.le ht) hδ
  unfold radiusSq
  field_simp [hd.ne']
  nlinarith [mul_eq_zero_of_left hquad t]

end
end RadialSymplectic

namespace RadialSymplectic

open Set
open scoped Topology ContDiff

variable {E : Type u39} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

theorem radialContraction_mapsTo {μ δ a r : ℝ} (hμ : 0 < μ) (hδ : 0 < δ)
    (hbound : a ≤ radiusSq μ δ (r^2)) :
    MapsTo (radialContraction μ δ : E → E) {x | ‖x‖^2 < a} {x | ‖x‖^2 < r^2} := by
  intro x hx
  have hi := radiusSq_inverse hμ hδ (sq_nonneg ‖x‖)
  have hh : radiusSq μ δ (‖radialContraction μ δ x‖^2) < radiusSq μ δ (r^2) := by
    rw [norm_sq_radialContraction hμ hδ, hi]
    exact lt_of_lt_of_le hx hbound
  exact ((radiusSq_strictMonoOn hμ.le hδ).lt_iff_lt
    (show ‖radialContraction μ δ x‖^2 ∈ Ici (0 : ℝ) from sq_nonneg ‖radialContraction μ δ x‖)
    (show r^2 ∈ Ici (0 : ℝ) from sq_nonneg r)).mp hh

end
end RadialSymplectic

namespace RadialSymplectic

open ComplexPotential TensorCalculus
open scoped ContDiff

noncomputable section

variable {E : Type u40} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_modelPotential (μ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (modelPotential μ δ : E → ℝ) :=
  (contDiff_norm_sq ℝ).add (contDiff_const.mul
    (((contDiff_norm_sq ℝ).add contDiff_const).log
      (fun x => (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) hδ).ne')))

theorem dc_modelPotential (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x : E) :
    dc J (modelPotential μ δ) x = radialPrimitive (standardTensor J) (expansionScale μ δ) x := by
  let h : ℝ → ℝ := fun t => t + μ * Real.log (t + δ)
  have hp : ‖x‖^2 + δ ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ).ne'
  have hd : HasDerivAt h (1 + μ * (‖x‖^2 + δ)⁻¹) (‖x‖^2) := by
    convert (hasDerivAt_id (‖x‖^2)).add
      ((((hasDerivAt_id (‖x‖^2)).add_const δ).log hp).const_mul μ) using 1 <;> first | rfl | simp [one_div]
  change dc J (h ∘ (fun y : E => ‖y‖^2)) x = _
  rw [dc_scalar_comp J ((contDiff_norm_sq ℝ).differentiable (show (∞ : ℕ∞ω) ≠ 0 by simp) x)
    hd.differentiableAt, hd.deriv, dc_norm_sq J hsk, smul_smul]
  unfold radialPrimitive
  rw [expansionScale_sq hμ hδ]
  congr 1
  ring

theorem radialExpansion_pullback (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x a b : E) :
    standardTensor J (fderiv ℝ (radialExpansion μ δ : E → E) x a)
      (fderiv ℝ (radialExpansion μ δ : E → E) x b) = ddc J (modelPotential μ δ) x a b := by
  have hsk' (a b : E) : standardTensor J a b = -standardTensor J b a := by
    change inner (𝕜 := ℝ) (J a) b = -inner (𝕜 := ℝ) (J b) a
    rw [← real_inner_comm (J a) b, hsk]
  have he : dc J (modelPotential μ δ) = radialPrimitive (standardTensor J) (expansionScale μ δ) :=
    funext (dc_modelPotential J hsk hμ hδ)
  rw [ddc, he]
  exact radial_pullback (standardTensor J) hsk' ((contDiff_expansionScale hμ hδ).differentiable
    (by simp) x) a b

theorem radialContraction_pullback (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    {μ δ : ℝ} (hμ : 0 < μ) (hδ : 0 < δ) (x a b : E) :
    ddc J (modelPotential μ δ) (radialContraction μ δ x)
      (fderiv ℝ (radialContraction μ δ : E → E) x a)
      (fderiv ℝ (radialContraction μ δ : E → E) x b) = standardTensor J a b := by
  have hd (v : E) : fderiv ℝ (radialExpansion μ δ : E → E) (radialContraction μ δ x)
      (fderiv ℝ (radialContraction μ δ : E → E) x v) = v := by
    have he : (radialExpansion μ δ : E → E) ∘ radialContraction μ δ = id :=
      funext (radialExpansion_radialContraction hμ hδ)
    have hh := fderiv_comp x ((contDiff_radialExpansion hμ hδ).differentiable (by simp)
      (radialContraction μ δ x)) ((contDiff_radialContraction hμ hδ).differentiable (by simp) x)
    rw [he, fderiv_id] at hh
    exact (congrArg (fun L : E →L[ℝ] E => L v) hh).symm
  rw [← radialExpansion_pullback J hsk hμ hδ, hd, hd]

end
end RadialSymplectic

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HolomorphicBalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u41 u42 u43 u44 u45 u46 u47 u48 u49

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff

open Set
namespace SingularComparison
noncomputable section

theorem exists_inner_radius {μ α R : ℝ} (hμ : 0 ≤ μ) (hμα : μ < α)
    (hR : 0 < R) (M C : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ (t δ H : ℝ), 0 < t → t ≤ r^2 → 0 < δ →
      H ≤ α * Real.log t + C → H + 2 ≤ μ * Real.log (t + δ) - M := by
  let L := (-M - C - 2) / (α - μ)
  obtain ⟨r, hr, hrsmall⟩ := exists_between (show (0 : ℝ) < min R (Real.sqrt (Real.exp L)) by
    exact lt_min hR (Real.sqrt_pos.mpr (Real.exp_pos L)))
  refine ⟨r, hr, hrsmall.trans_le (min_le_left _ _), ?_⟩
  intro t δ H ht htr hδ hH
  have hre : r < Real.sqrt (Real.exp L) := hrsmall.trans_le (min_le_right _ _)
  have hr2 : r^2 ≤ Real.exp L := by
    have hs := Real.sq_sqrt (Real.exp_pos L).le
    nlinarith [Real.sqrt_nonneg (Real.exp L)]
  have htL : Real.log t ≤ L := by
    calc
      Real.log t ≤ Real.log (Real.exp L) := Real.log_le_log ht (htr.trans hr2)
      _ = L := Real.log_exp L
  have hlog : Real.log t ≤ Real.log (t + δ) := Real.log_le_log ht (by linarith)
  have hcoef : (α - μ) * Real.log t ≤ -M - C - 2 := by
    calc
      _ ≤ (α - μ) * L := mul_le_mul_of_nonneg_left htL (sub_nonneg.mpr hμα.le)
      _ = -M - C - 2 := by dsimp [L]; field_simp [sub_ne_zero.mpr hμα.ne']
  have hmono := mul_le_mul_of_nonneg_left hlog hμ
  linarith

theorem outer_comparison {μ R δ H L M : ℝ} (hμ : 0 ≤ μ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hH : L ≤ H)
    (hM : μ * Real.log (R^2 + 1) - L + 2 < M) :
    μ * Real.log (R^2 + δ) - M + 2 < H := by
  have hp : 0 < R^2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg R) hδ
  have hlog := Real.log_le_log hp (show R^2 + δ ≤ R^2 + 1 by linarith)
  have hh := mul_le_mul_of_nonneg_left hlog hμ
  linarith

theorem radius_bound {a μ r δ : ℝ} (ha : 0 < a) (_ham : a < μ) (hr : 0 < r)
    (hδ : 0 < δ) (hδb : δ < r^2 * (μ / a - 1)) :
    a < r^2 * (1 + μ / (r^2 + δ)) := by
  have hd : 0 < r^2 + δ := add_pos_of_nonneg_of_pos (sq_nonneg r) hδ
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have hδa : δ * a < r^2 * (μ - a) := by
    calc
      δ * a < (r^2 * (μ / a - 1)) * a := mul_lt_mul_of_pos_right hδb ha
      _ = r^2 * (μ - a) := by field_simp
  have hfrac : a < r^2 * μ / (r^2 + δ) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  calc
    a < r^2 * μ / (r^2 + δ) := hfrac
    _ < r^2 * (1 + μ / (r^2 + δ)) := by
      rw [mul_add, mul_one, mul_div_assoc]
      linarith

end
end SingularComparison

namespace ComplexPotential

open Set Filter RadialSymplectic
open scoped ContDiff Topology

noncomputable section

variable {E : Type u41} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_ball_from_logarithmic_pole (J : E →L[ℝ] E)
    (hsk : ∀ a b, inner (𝕜 := ℝ) a (J b) = -inner (𝕜 := ℝ) (J a) b)
    (hJ : ∀ a, ‖J a‖ = ‖a‖) (hJJ : ∀ a, J (J a) = -a)
    {U : Set E} (hU : IsOpen U) (hU0 : (0 : E) ∈ U)
    {τ H : E → ℝ} (hτ : ∀ x ∈ U, IsPSHAt J τ x) (hτ0 : τ 0 = 0)
    (hH : ∀ x ∈ U, x ≠ 0 → IsPSHAt J H x)
    (hcompact : ∀ s : ℝ, 0 < s → s < 1 → IsCompact {x | x ∈ U ∧ τ x ≤ s})
    {s₀ α C ρ : ℝ} (hs₀ : s₀ < 1) (hρ : 0 < ρ)
    (htail : ∀ x ∈ U, s₀ ≤ τ x → H x = τ x)
    (hpole : ∀ x ∈ U, x ≠ 0 → ‖x‖ ≤ ρ → H x ≤ α * Real.log (‖x‖^2) + C)
    {a : ℝ} (ha : 0 < a) (haα : a < α) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x : E, ‖x‖^2 < a → F x ∈ U) ∧
      ∀ x : E, ‖x‖^2 < a → ∀ v w : E,
        ddc J (fun y => ‖y‖^2 + τ y) (F x) (fderiv ℝ (F : E → E) x v)
          (fderiv ℝ (F : E → E) x w) = standardTensor J v w := by
  obtain ⟨μ, haμ, hμα⟩ := exists_between haα
  have hμ : 0 < μ := ha.trans haμ
  have hn : {x : E | x ∈ U ∧ τ x < 1/2} ∈ 𝓝 (0 : E) := by
    exact inter_mem (hU.mem_nhds hU0)
      ((hτ 0 hU0).1.continuousAt.eventually_lt continuousAt_const (by norm_num [hτ0]))
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp hn
  let R := ε / 2
  have hR : 0 < R := half_pos hε
  have hRball (x : E) (hx : ‖x‖ ≤ R) : x ∈ U ∧ τ x < 1/2 := by
    apply hεball
    rw [Metric.mem_ball, dist_zero_right]
    exact hx.trans_lt (half_lt_self hε)
  have hsp : IsCompact {x : E | ‖x‖ = R} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) R
  have hcont : ContinuousOn H {x : E | ‖x‖ = R} := by
    intro x hx
    apply ((hH x (hRball x hx.le).1 ?_).1.continuousAt).continuousWithinAt
    intro hz
    have : R = 0 := by simpa [hz] using hx.symm
    exact hR.ne' this
  obtain ⟨L, hL⟩ := hsp.bddBelow_image hcont
  let M := μ * Real.log (R^2 + 1) - L + 3
  obtain ⟨r, hr, hrlt, hrdom⟩ := SingularComparison.exists_inner_radius hμ.le hμα
    (lt_min hR hρ) M C
  have hrR : r < R := hrlt.trans_le (min_le_left _ _)
  have hrρ : r < ρ := hrlt.trans_le (min_le_right _ _)
  have hδmax : 0 < min (1 : ℝ) (r^2 * (μ / a - 1)) := by
    apply lt_min zero_lt_one
    exact mul_pos (sq_pos_of_pos hr) (sub_pos.mpr ((one_lt_div ha).mpr haμ))
  obtain ⟨δ, hδ, hδlt⟩ := exists_between hδmax
  have hδ1 : δ ≤ 1 := (hδlt.trans_le (min_le_left _ _)).le
  have hδb : δ < r^2 * (μ / a - 1) := hδlt.trans_le (min_le_right _ _)
  let P : E → ℝ := fun x => μ * logNormSq δ x - M
  have hP (x : E) : IsPSHAt J P x :=
    ((isPSHAt_logNormSq J hsk hJ hJJ hδ.le
      (add_pos_of_nonneg_of_pos (sq_nonneg _) hδ)).const_smul hμ.le).sub_const M
  have hinner (x : E) (hx0 : x ≠ 0) (hx : ‖x‖ ≤ r) : H x + 1 ≤ P x := by
    have hxu := (hRball x (hx.trans hrR.le)).1
    have hh := hrdom (‖x‖^2) δ (H x) (sq_pos_of_pos (norm_pos_iff.mpr hx0))
      ((sq_le_sq₀ (norm_nonneg _) hr.le).mpr hx) hδ
      (hpole x hxu hx0 (hx.trans hrρ.le))
    change H x + 1 ≤ μ * Real.log (‖x‖^2 + δ) - M
    linarith
  have houter (x : E) (_hx : x ∈ U) (hnorm : ‖x‖ = R) : P x + 1 < H x := by
    have hh := SingularComparison.outer_comparison hμ.le hδ hδ1
      (hL ⟨x, hnorm, rfl⟩) (show μ * Real.log (R^2 + 1) - L + 2 < M by dsimp [M]; linarith)
    change μ * Real.log (‖x‖^2 + δ) - M + 1 < H x
    rw [hnorm]
    linarith
  let T := gluedPotential R H P
  have hT (x : E) (hx : x ∈ U) : IsPSHAt J T x :=
    isPSHAt_gluedPotential J hJJ hr hrR H P hH (fun x _ => hP x) hinner houter hx
  obtain ⟨σ, hσmin, hσ1⟩ := exists_between (show max s₀ (1/2 : ℝ) < 1 from
    max_lt hs₀ (by norm_num))
  have hσ0 : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 1/2)
    ((le_max_right _ _).trans_lt hσmin)
  let K : Set E := {x | x ∈ U ∧ τ x ≤ σ}
  have hK : IsCompact K := hcompact σ hσ0 hσ1
  have heq (x : E) (hx : x ∈ U) (hxK : x ∉ K) : T x = τ x := by
    have hστ : σ < τ x := lt_of_not_ge (fun h => hxK ⟨hx, h⟩)
    have hnorm : R ≤ ‖x‖ := by
      by_contra hh
      have hhalf := (hRball x (not_le.mp hh).le).2
      linarith [(le_max_right s₀ (1/2 : ℝ)).trans_lt hσmin]
    exact (gluedPotential_outer R H P hnorm).trans (htail x hx
      (((le_max_left _ _).trans_lt hσmin).le.trans hστ.le))
  obtain ⟨Q, hQ, hQi, _hout, hQmap, hQpull⟩ := exists_potential_transport J hsk hJ
    hU hK (fun _ hx => hx.1) hτ hT heq
  let F := (radialHomeomorph (E := E) hμ hδ).symm.trans Q
  have hF : ContDiff ℝ ∞ (F : E → E) := hQ.comp (contDiff_radialContraction hμ hδ)
  have hFi : ContDiff ℝ ∞ (F.symm : E → E) := (contDiff_radialExpansion hμ hδ).comp hQi
  have hmap (x : E) (hx : ‖x‖^2 < a) : ‖radialContraction μ δ x‖ < r := by
    apply (sq_lt_sq₀ (norm_nonneg _) hr.le).mp
    apply radialContraction_mapsTo hμ hδ _ hx
    calc
      a ≤ r^2 * (1 + μ / (r^2 + δ)) := (SingularComparison.radius_bound ha haμ hr hδ hδb).le
      _ = radiusSq μ δ (r^2) := by unfold radiusSq; ring
  have hUmap (x : E) (hx : ‖x‖^2 < a) : radialContraction μ δ x ∈ U :=
    (hRball _ ((hmap x hx).trans hrR).le).1
  refine ⟨F, hF, hFi, fun x hx => (hQmap _).mpr (hUmap x hx), ?_⟩
  intro x hx v w
  change ddc J (fun y => ‖y‖^2 + τ y) (Q (radialContraction μ δ x))
    (fderiv ℝ ((Q : E → E) ∘ radialContraction μ δ) x v)
    (fderiv ℝ ((Q : E → E) ∘ radialContraction μ δ) x w) = _
  rw [fderiv_comp x (hQ.differentiable (by simp) _) ((contDiff_radialContraction hμ hδ).differentiable
    (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hQpull _ (hUmap x hx)]
  have heT : (fun z : E => ‖z‖^2 + T z) =ᶠ[𝓝 (radialContraction μ δ x)]
      fun z => modelPotential μ δ z - M := by
    filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const (hmap x hx)] with z hz
    dsimp only [T]
    rw [gluedPotential_inner hrR H P hinner hz.le]
    dsimp [P, logNormSq, modelPotential]
    ring
  rw [ddc_congr J heT, ddc_sub_const J (contDiff_modelPotential μ hδ).contDiffAt,
    radialContraction_pullback J hsk hμ hδ]

end
end ComplexPotential

namespace TensorCalculus

open Set Filter
open scoped Topology ContDiff

variable {E : Type u42} {F : Type u43} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

attribute [local instance] OAI.TensorCalculus.pullbackOneTensorGroup
attribute [local instance] OAI.TensorCalculus.pullbackOneTensorSpace
local instance pullbackTwoTensorGroup_re4bb3c_1 : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance pullbackTwoTensorSpace_re4bb3c_1 : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
theorem fderiv_pullbackOneForm {f : E → F} {γ : F → F →L[ℝ] ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hd : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hγ : DifferentiableAt ℝ γ (f x)) (a b : E) :
    fderiv ℝ (pullbackOneForm f γ) x a b =
      fderiv ℝ γ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) +
        γ (f x) (fderiv ℝ (fderiv ℝ f) x a b) := by
  unfold pullbackOneForm
  rw [fderiv_clm_comp (c := fun y => γ (f y)) (hγ.comp x hf) hd]
  rw [show fderiv ℝ (fun y => γ (f y)) x = (fderiv ℝ γ (f x)).comp (fderiv ℝ f x) by
    exact fderiv_comp x hγ hf]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]
  ring

theorem exteriorD_pullbackOneForm {f : E → F} {γ : F → F →L[ℝ] ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hγ : DifferentiableAt ℝ γ (f x)) (a b : E) :
    exteriorD (pullbackOneForm f γ) x a b =
      exteriorD γ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) := by
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hf' := hf.differentiableAt (by simp)
  have hs := hf.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [exteriorD_apply, fderiv_pullbackOneForm hf' hd hγ]
  rw [hs.eq a b]
  ring

end
end TensorCalculus

namespace ComplexPotential

open TensorCalculus Set Filter
open scoped ContDiff Topology

variable {E : Type u44} {F : Type u45} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable section

theorem dc_comp (J : E →L[ℝ] E) (K : F →L[ℝ] F) {f : E → F} {φ : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x))
    (hCR : ∀ a, fderiv ℝ f x (J a) = K (fderiv ℝ f x a)) :
    dc J (φ ∘ f) x = pullbackOneForm f (dc K φ) x := by
  ext a
  rw [dc_apply, fderiv_comp x hφ hf, ContinuousLinearMap.comp_apply, hCR,
    pullbackOneForm_apply, dc_apply]

theorem ddc_comp (J : E →L[ℝ] E) (K : F →L[ℝ] F) {f : E → F} {φ : F → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hφ : ContDiffAt ℝ ∞ φ (f x))
    (hCR : ∀ᶠ y in 𝓝 x, ∀ a, fderiv ℝ f y (J a) = K (fderiv ℝ f y a)) (a b : E) :
    ddc J (φ ∘ f) x a b = ddc K φ (f x) (fderiv ℝ f x a) (fderiv ℝ f x b) := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have he : dc J (φ ∘ f) =ᶠ[𝓝 x] pullbackOneForm f (dc K φ) := by
    filter_upwards [(hf.of_le h1).eventually (by simp),
      hf.continuousAt ((hφ.of_le h1).eventually (by simp)), hCR] with y hy hz hc
    exact dc_comp J K (hy.differentiableAt one_ne_zero)
      ((show ContDiffAt ℝ (1 : ℕ∞ω) φ (f y) from hz).differentiableAt one_ne_zero) hc
  unfold ddc exteriorD
  rw [he.fderiv_eq]
  exact exteriorD_pullbackOneForm hf ((contDiffAt_dc K hφ).differentiableAt (by simp)) a b

end
end ComplexPotential

namespace ComplexPotential

open Set Filter TensorCalculus
open scoped ContDiff Topology

noncomputable section

variable {E : Type u46} {F : Type u47} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem complexStructure_sq (a : E) : complexStructure E (complexStructure E a) = -a := by
  simp [complexStructure_apply, smul_smul]

theorem complexStructure_norm (a : E) : ‖complexStructure E a‖ = ‖a‖ := by
  simp [complexStructure_apply, norm_smul]

theorem fderiv_commutes_complexStructure {f : E → F} {x : E}
    (hf : DifferentiableAt ℂ f x) (a : E) :
    fderiv ℝ f x (complexStructure E a) = complexStructure F (fderiv ℝ f x a) := by
  rw [hf.fderiv_restrictScalars ℝ]
  simp [complexStructure_apply]

theorem complexStructure_skew {G : Type u49} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (a b : G) :
    let : InnerProductSpace ℝ G := InnerProductSpace.complexToReal
    inner (𝕜 := ℝ) a (complexStructure G b) = -inner (𝕜 := ℝ) (complexStructure G a) b := by
  let : InnerProductSpace ℝ G := InnerProductSpace.complexToReal
  simp [real_inner_eq_re_inner ℂ, inner_smul_right, inner_smul_left]

theorem IsPSHAt.holomorphic_comp {f : E → F} {φ : F → ℝ} {x : E}
    (hφ : IsPSHAt (complexStructure F) φ (f x))
    (hf : ContDiffAt ℝ ∞ f x) (hhol : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y) :
    IsPSHAt (complexStructure E) (φ ∘ f) x := by
  refine ⟨hφ.1.comp x hf, fun a => ?_⟩
  rw [ddc_comp (complexStructure E) (complexStructure F) hf hφ.1
    (hhol.mono (fun y hy => fderiv_commutes_complexStructure hy)),
    fderiv_commutes_complexStructure hhol.self_of_nhds]
  exact hφ.2 _

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LogProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u50 u51

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace SmoothLogProfile
noncomputable section

variable (b l u : ℝ)

theorem cutoff_smooth : ContDiff ℝ ∞ (cutoff l u) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem slope_smooth : ContDiff ℝ ∞ (slope b l u) :=
  contDiff_const.add ((cutoff_smooth l u).mul (Real.contDiff_exp.sub contDiff_const))

theorem cutoff_mem (t : ℝ) : cutoff l u t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_zero (hlu : l < u) {t : ℝ} (ht : t ≤ l) : cutoff l u t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_nonneg.mpr hlu.le)

theorem cutoff_one (hlu : l < u) {t : ℝ} (ht : u ≤ t) : cutoff l u t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (sub_pos.mpr hlu)).mpr (by linarith)

theorem cutoff_monotone (hlu : l < u) : Monotone (cutoff l u) := by
  intro x y hxy
  exact Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hxy l) (sub_nonneg.mpr hlu.le))

theorem slope_left (hlu : l < u) {t : ℝ} (ht : t ≤ l) : slope b l u t = b := by
  simp [slope, cutoff_zero l u hlu ht]

theorem slope_right (hlu : l < u) {t : ℝ} (ht : u ≤ t) : slope b l u t = Real.exp t := by
  simp [slope, cutoff_one l u hlu ht]

theorem slope_pos (hb : 0 < b) (t : ℝ) : 0 < slope b l u t := by
  have hc := cutoff_mem l u t
  have he := Real.exp_pos t
  by_cases h : cutoff l u t = 1
  · simpa [slope, h] using he
  have hp : 0 < (1 - cutoff l u t) * b := mul_pos (sub_pos.mpr (lt_of_le_of_ne hc.2 h)) hb
  have hq : 0 ≤ cutoff l u t * Real.exp t := mul_nonneg hc.1 he.le
  unfold slope
  nlinarith

theorem slope_monotone (hlu : l < u) (hbl : b ≤ Real.exp l) : Monotone (slope b l u) := by
  intro x y hxy
  by_cases hyl : y ≤ l
  · rw [slope_left b l u hlu (hxy.trans hyl), slope_left b l u hlu hyl]
  have hly : l ≤ y := (not_le.mp hyl).le
  have hey : b ≤ Real.exp y := hbl.trans (Real.exp_le_exp.mpr hly)
  by_cases hxl : x ≤ l
  · rw [slope_left b l u hlu hxl]
    exact le_add_of_nonneg_right (mul_nonneg (cutoff_mem l u y).1 (sub_nonneg.mpr hey))
  have hlx : l ≤ x := (not_le.mp hxl).le
  have hex : b ≤ Real.exp x := hbl.trans (Real.exp_le_exp.mpr hlx)
  unfold slope
  apply add_le_add le_rfl
  exact mul_le_mul (cutoff_monotone l u hlu hxy)
    (sub_le_sub_right (Real.exp_le_exp.mpr hxy) b) (sub_nonneg.mpr hex) (cutoff_mem l u y).1

theorem hasDerivAt_profile (t : ℝ) : HasDerivAt (profile b l u) (slope b l u t) t := by
  have hd : HasDerivAt (fun t => ∫ s in u..t, slope b l u s) (slope b l u t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (slope_smooth b l u).continuous.intervalIntegrable _ _
    · exact (slope_smooth b l u).continuous.stronglyMeasurableAtFilter _ _
    · exact (slope_smooth b l u).continuous.continuousAt
  exact hd.const_add _

@[simp] theorem deriv_profile : deriv (profile b l u) = slope b l u :=
  funext (fun t => (hasDerivAt_profile b l u t).deriv)

theorem profile_smooth : ContDiff ℝ ∞ (profile b l u) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun t => (hasDerivAt_profile b l u t).differentiableAt,
    deriv_profile b l u ▸ slope_smooth b l u⟩

theorem deriv_profile_pos (hb : 0 < b) (t : ℝ) : 0 < deriv (profile b l u) t := by
  rw [deriv_profile]
  exact slope_pos b l u hb t

theorem second_deriv_profile_nonneg (hlu : l < u) (hbl : b ≤ Real.exp l) (t : ℝ) :
    0 ≤ deriv (deriv (profile b l u)) t := by
  rw [deriv_profile]
  exact (slope_monotone b l u hlu hbl).deriv_nonneg

theorem profile_sub (s t : ℝ) :
    profile b l u t - profile b l u s = ∫ x in s..t, slope b l u x := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    ((slope_smooth b l u).continuous.intervalIntegrable (μ := volume) u s)
    ((slope_smooth b l u).continuous.intervalIntegrable s t)
  unfold profile
  linarith

theorem profile_right (hlu : l < u) {t : ℝ} (ht : u ≤ t) :
    profile b l u t = Real.exp t := by
  have he : (∫ s in u..t, slope b l u s) = Real.exp t - Real.exp u := by
    calc
      _ = ∫ s in u..t, Real.exp s := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact slope_right b l u hlu (le_trans (by simp [ht]) hs.1)
      _ = Real.exp t - Real.exp u := by simp
  simp [profile, he]

theorem profile_left (hlu : l < u) {t : ℝ} (ht : t ≤ l) :
    profile b l u t = b * t + (profile b l u l - b * l) := by
  have he : (∫ s in t..l, slope b l u s) = (l - t) * b := by
    calc
      _ = ∫ s in t..l, b := by
        apply intervalIntegral.integral_congr
        intro s hs
        exact slope_left b l u hlu (le_trans hs.2 (by simp [ht]))
      _ = (l - t) * b := by simp
  have hdiff := profile_sub b l u t l
  rw [he] at hdiff
  nlinarith

end
end SmoothLogProfile

namespace ComplexPotential

open Set Filter Asymptotics
open scoped Topology ContDiff
noncomputable section

variable {E : Type u50} {F : Type u51} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem exists_ball_from_holomorphic_zero {Ω : Set E} (hΩ : IsOpen Ω) (hΩ0 : (0 : E) ∈ Ω)
    {f : E → F} (hf : AnalyticOnNhd ℂ f Ω)
    (hfzero : ∀ x ∈ Ω, f x = 0 ↔ x = 0)
    {k : ℕ} (hk : 1 ≤ k) (ho : f =O[𝓝 (0 : E)] (fun x : E => ‖x‖^k))
    (hcompact : ∀ s : ℝ, 0 < s → s < 1 → IsCompact {x | x ∈ Ω ∧ ‖f x‖^2 ≤ s})
    {a : ℝ} (ha : 0 < a) (hak : a < (k : ℝ)) :
    let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    ∃ Q : E ≃ₜ E, ContDiff ℝ ∞ (Q : E → E) ∧ ContDiff ℝ ∞ (Q.symm : E → E) ∧
      (∀ x : E, ‖x‖^2 < a → Q x ∈ Ω ∧ ‖f (Q x)‖^2 < 1) ∧
      ∀ x : E, ‖x‖^2 < a → ∀ v w : E,
        ddc (complexStructure E) (fun y => ‖y‖^2 + ‖f y‖^2) (Q x)
          (fderiv ℝ (Q : E → E) x v) (fderiv ℝ (Q : E → E) x w) =
            standardTensor (complexStructure E) v w := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  let τ : E → ℝ := fun x => ‖f x‖^2
  let U : Set E := {x | x ∈ Ω ∧ τ x < 1}
  have hτsmooth (x : E) (hx : x ∈ Ω) : ContDiffAt ℝ ∞ τ x :=
    (contDiff_norm_sq ℝ).contDiffAt.comp x ((hf x hx).contDiffAt.restrict_scalars ℝ)
  have hτcont : ContinuousOn τ Ω := fun x hx => (hτsmooth x hx).continuousAt.continuousWithinAt
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact inter_mem (hΩ.mem_nhds hx.1)
      ((hτsmooth x hx.1).continuousAt.eventually_lt continuousAt_const hx.2)
  have hf0 : f 0 = 0 := (hfzero 0 hΩ0).mpr rfl
  have hτ0 : τ 0 = 0 := by simp [τ, hf0]
  have hU0 : (0 : E) ∈ U := ⟨hΩ0, by rw [hτ0]; norm_num⟩
  have hτpsh (x : E) (hx : x ∈ U) : IsPSHAt (complexStructure E) τ x := by
    have hn : IsPSHAt (complexStructure F) (fun z : F => ‖z‖^2) (f x) := by
      refine ⟨(contDiff_norm_sq ℝ).contDiffAt, fun v => ?_⟩
      rw [ddc_norm_sq _ (complexStructure_skew), standardTensor_complex_line _ complexStructure_norm]
      exact sq_nonneg _
    apply hn.holomorphic_comp ((hf x hx.1).contDiffAt.restrict_scalars ℝ)
    filter_upwards [hΩ.mem_nhds hx.1] with y hy
    exact (hf y hy).differentiableAt
  have hpos (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) : 0 < τ x := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (fun hh => hx0 ((hfzero x hx.1).mp hh)))
  have hlogpsh (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) :
      IsPSHAt (complexStructure E) (Real.log ∘ τ) x := by
    have hn := isPSHAt_logNormSq (complexStructure F) complexStructure_skew
      complexStructure_norm complexStructure_sq (δ := 0) le_rfl
        (show 0 < ‖f x‖^2 + 0 by simpa [τ] using hpos x hx hx0)
    have hh := hn.holomorphic_comp ((hf x hx.1).contDiffAt.restrict_scalars ℝ) (by
      filter_upwards [hΩ.mem_nhds hx.1] with y hy
      exact (hf y hy).differentiableAt)
    simpa only [logNormSq, add_zero, Function.comp_def, τ] using hh
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  obtain ⟨b, hab, hb1⟩ := exists_between ((div_lt_one hkpos).mpr hak)
  have hb : 0 < b := (div_pos ha hkpos).trans hab
  obtain ⟨l, hbl, hl0⟩ := exists_between (Real.log_neg hb hb1)
  obtain ⟨u, hlu, hu0⟩ := exists_between hl0
  have hble : b ≤ Real.exp l := by
    exact ((Real.log_le_iff_le_exp hb).mp hbl.le)
  let H : E → ℝ := SmoothLogProfile.profile b l u ∘ Real.log ∘ τ
  have hH (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) : IsPSHAt (complexStructure E) H x := by
    exact (hlogpsh x hx hx0).scalar_comp _ complexStructure_sq
      (SmoothLogProfile.profile_smooth b l u).contDiffAt
      (SmoothLogProfile.deriv_profile_pos b l u hb _).le
      (SmoothLogProfile.second_deriv_profile_nonneg b l u hlu hble _)
  have htail (x : E) (hx : x ∈ U) (ht : Real.exp u ≤ τ x) : H x = τ x := by
    have htpos : 0 < τ x := (Real.exp_pos u).trans_le ht
    have hlog : u ≤ Real.log (τ x) := by
      simpa using Real.log_le_log (Real.exp_pos u) ht
    change SmoothLogProfile.profile b l u (Real.log (τ x)) = τ x
    rw [SmoothLogProfile.profile_right b l u hlu hlog, Real.exp_log htpos]
  obtain ⟨C, hC, hCb⟩ := ho.exists_pos
  have hev : ∀ᶠ x in 𝓝 (0 : E), ‖f x‖ ≤ C * ‖x‖^k ∧ τ x < Real.exp l := by
    filter_upwards [hCb.bound,
      (hτsmooth 0 hΩ0).continuousAt.eventually_lt continuousAt_const
        (show τ 0 < Real.exp l by rw [hτ0]; exact Real.exp_pos l)] with x hx ht
    exact ⟨by simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hx, ht⟩
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hev
  let ρ := ε / 2
  have hρ : 0 < ρ := half_pos hε
  let C₁ := b * (2 * Real.log C) + (SmoothLogProfile.profile b l u l - b * l)
  have hpole (x : E) (hx : x ∈ U) (hx0 : x ≠ 0) (hnorm : ‖x‖ ≤ ρ) :
      H x ≤ (b * k) * Real.log (‖x‖^2) + C₁ := by
    have hdist : dist x 0 < ε := by rw [dist_zero_right]; exact hnorm.trans_lt (half_lt_self hε)
    obtain ⟨hbound, hsmall⟩ := hεprop hdist
    have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hfxp : 0 < ‖f x‖ := norm_pos_iff.mpr (fun hh => hx0 ((hfzero x hx.1).mp hh))
    have hlogl : Real.log (τ x) ≤ l := (Real.log_le_iff_le_exp (hpos x hx hx0)).mpr hsmall.le
    change SmoothLogProfile.profile b l u (Real.log (τ x)) ≤ _
    rw [SmoothLogProfile.profile_left b l u hlu hlogl]
    have hlg := Real.log_le_log hfxp hbound
    rw [Real.log_mul hC.ne' (pow_pos hxp k).ne', Real.log_pow] at hlg
    have hmul := mul_le_mul_of_nonneg_left hlg hb.le
    dsimp [τ, C₁]
    rw [Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  apply exists_ball_from_logarithmic_pole (complexStructure E) complexStructure_skew
    complexStructure_norm complexStructure_sq hU hU0 hτpsh hτ0 hH
  · intro s hs hs1
    have he : {x | x ∈ U ∧ τ x ≤ s} = {x | x ∈ Ω ∧ ‖f x‖^2 ≤ s} := by
      ext x
      constructor
      · exact fun hx => ⟨hx.1.1, hx.2⟩
      · exact fun hx => ⟨⟨hx.1, hx.2.trans_lt hs1⟩, hx.2⟩
    rw [he]
    exact hcompact s hs hs1
  · exact Real.exp_lt_one_iff.mpr hu0
  · exact hρ
  · exact htail
  · exact hpole
  · exact ha
  · exact (div_lt_iff₀ hkpos).mp hab

end
end ComplexPotential

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology

open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
noncomputable section

theorem hasDerivAt_term (n : ℕ) (w : ℂ) : HasDerivAt (term n) (termDeriv n w) w := by
  have hn : (2 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
  convert (((hasDerivAt_id w).pow (2*n+1)).const_mul ((-1 : ℂ)^n)).div_const
    ((2*(n : ℂ)+1)^2) using 1 <;> try rfl
  simp only [termDeriv, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.add_sub_cancel]
  field_simp [hn]
  rfl

theorem norm_termDeriv_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {w : ℂ} (hw : ‖w‖ ≤ r) (n : ℕ) : ‖termDeriv n w‖ ≤ r^n := by
  have hn : (1 : ℝ) ≤ 2 * n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  calc
    ‖termDeriv n w‖ = ‖w‖^(2*n) / (2*n+1) := by
      simp only [termDeriv, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      congr 1
      norm_cast
    _ ≤ r^(2*n) := (div_le_self (pow_nonneg (norm_nonneg _) _) hn).trans
      (pow_le_pow_left₀ (norm_nonneg _) hw _)
    _ ≤ r^n := pow_le_pow_of_le_one hr hr1 (by omega)

theorem hasDerivAt_F {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt F ((8 / (Real.pi^2) : ℝ) * ∑' n : ℕ, termDeriv n w) w := by
  obtain ⟨r, hwr, hr1⟩ := exists_between hw
  have hr : 0 < r := (norm_nonneg w).trans_lt hwr
  have hh := hasDerivAt_tsum_of_isPreconnected
    (summable_geometric_of_lt_one hr.le hr1) Metric.isOpen_ball
    (convex_ball (0 : ℂ) r).isPreconnected
    (fun n z _ => hasDerivAt_term n z)
    (fun n z hz => norm_termDeriv_le hr.le hr1.le ((by simpa [Metric.mem_ball] using hz : ‖z‖ < r).le) n)
    (show (0 : ℂ) ∈ Metric.ball 0 r by simpa using hr)
    (show Summable (fun n => term n (0 : ℂ)) by simp)
    (show w ∈ Metric.ball 0 r by simpa using hwr)
  exact hh.const_mul _

theorem analyticOnNhd_F : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro w hw
  exact (hasDerivAt_F (by simpa using hw)).differentiableAt.differentiableWithinAt

theorem mul_deriv_F {w : ℂ} (hw : ‖w‖ < 1) :
    w * deriv F w = (8 / (Real.pi^2) : ℝ) * Complex.arctan w := by
  rw [(hasDerivAt_F hw).deriv, mul_left_comm, ← tsum_mul_left]
  congr 1
  have he : (fun n : ℕ => w * termDeriv n w) =
      (fun n : ℕ => (-1)^n * w^(2*n+1) / (2*n+1)) := by
    funext n
    dsimp [termDeriv]
    rw [pow_succ]
    ring
  rw [he]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using (Complex.hasSum_arctan hw).tsum_eq

theorem norm_term_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖term n w‖ ≤ 1 / ((n : ℝ)+1)^2 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  calc
    ‖term n w‖ = ‖w‖^(2*n+1) / (2*(n : ℝ)+1)^2 := by
      simp only [term, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      congr 2
      norm_cast
    _ ≤ 1 / (2*(n : ℝ)+1)^2 := div_le_div_of_nonneg_right
      (pow_le_one₀ (norm_nonneg _) hw) (sq_nonneg _)
    _ ≤ 1 / ((n : ℝ)+1)^2 := one_div_le_one_div_of_le (sq_pos_of_pos hn)
      (pow_le_pow_left₀ hn.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) 2)

theorem summable_bound : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^2) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))

theorem continuousOn_F_closedBall : ContinuousOn F (Metric.closedBall 0 1) := by
  apply ContinuousOn.const_mul _ _
  apply continuousOn_tsum (fun n => (by unfold term; fun_prop : Continuous (term n)).continuousOn)
    summable_bound
  intro n w hw
  exact norm_term_le (by simpa using hw) n

theorem cayley_re (w : ℂ) : (cayley w).re = (1 - ‖w‖^2) / normSq (1-w*I) := by
  rw [cayley, div_re, Complex.sq_norm]
  simp only [add_re, one_re, mul_re, I_re, mul_zero, mul_im, I_im, mul_one,
    zero_sub, sub_re, add_im, one_im, sub_im, add_zero, zero_add, normSq_apply]
  ring

theorem cayley_im (w : ℂ) : (cayley w).im = 2*w.re / normSq (1-w*I) := by
  rw [cayley, div_im]
  simp only [add_re, one_re, mul_re, I_re, mul_zero, mul_im, I_im, mul_one,
    zero_sub, sub_re, add_im, one_im, sub_im, add_zero, zero_add]
  ring

theorem cayley_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayley w).re := by
  have hn : 1-w*I ≠ 0 := by
    intro h
    have he := congr_arg norm (sub_eq_zero.mp h)
    simp only [norm_one, norm_mul, norm_I, mul_one] at he
    linarith
  rw [cayley_re]
  exact div_pos (by nlinarith [norm_nonneg w]) (normSq_pos.mpr hn)

theorem arctan_re_eq {w : ℂ} (hw : ‖w‖ < 1) :
    (Complex.arctan w).re = (1/2 : ℝ) * Real.arctan (2*w.re/(1-‖w‖^2)) := by
  have harg := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (cayley_re_pos hw)))
  have ht := Real.arctan_tan harg.1 harg.2
  rw [Complex.tan_arg, cayley_re, cayley_im] at ht
  have hn : normSq (1-w*I) ≠ 0 := by
    apply ne_of_gt
    have h := cayley_re_pos hw
    rw [cayley_re] at h
    exact (div_pos_iff.mp h).resolve_right (by rintro ⟨_, hneg⟩; exact (normSq_nonneg _).not_gt hneg) |>.2
  have he : (2*w.re/normSq (1-w*I)) / ((1-‖w‖^2)/normSq (1-w*I)) =
      2*w.re/(1-‖w‖^2) := by field_simp
  rw [he] at ht
  rw [Complex.arctan, mul_re]
  have hre : (-I / 2 : ℂ).re = 0 := by norm_num [div_re]
  have him : (-I / 2 : ℂ).im = -1/2 := by norm_num [div_im]
  rw [hre, him, zero_mul, log_im]
  change 0 - (-1/2) * (cayley w).arg = _
  rw [← ht]
  ring

theorem re_mul_deriv_F {w : ℂ} (hw : ‖w‖ < 1) :
    (w * deriv F w).re = (4 / Real.pi^2) * Real.arctan (2*w.re/(1-‖w‖^2)) := by
  rw [mul_deriv_F hw, re_ofReal_mul, arctan_re_eq hw]
  ring

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem norm_one_add_mul_I_sq (w : ℂ) : ‖1+w*I‖^2 = 1-2*w.im+‖w‖^2 := by
  simp only [Complex.sq_norm, normSq_apply, add_re, one_re, mul_re, I_re, I_im,
    mul_zero, mul_one, zero_sub, add_im, one_im, mul_im, zero_add, add_zero]
  ring

theorem norm_one_sub_mul_I_sq (w : ℂ) : ‖1-w*I‖^2 = 1+2*w.im+‖w‖^2 := by
  simp only [Complex.sq_norm, normSq_apply, sub_re, one_re, mul_re, I_re, I_im,
    mul_zero, mul_one, zero_sub, sub_im, one_im, mul_im, add_zero]
  ring

theorem one_add_mul_I_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1+w*I ≠ 0 := by
  intro h
  have he : w*I = -1 := eq_neg_of_add_eq_zero_right h
  have hh := congr_arg norm he
  simp only [norm_mul, norm_I, mul_one, norm_neg, norm_one] at hh
  linarith

theorem one_sub_mul_I_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1-w*I ≠ 0 := by
  have h := one_add_mul_I_ne_zero (w := -w) (by simpa using hw)
  simpa only [neg_mul, sub_eq_add_neg] using h

theorem arctan_im_eq (w : ℂ) :
    (Complex.arctan w).im = -(1/2 : ℝ) * Real.log (‖1+w*I‖/‖1-w*I‖) := by
  rw [Complex.arctan, mul_im]
  have hre : (-I / 2 : ℂ).re = 0 := by norm_num [div_re]
  have him : (-I / 2 : ℂ).im = -1/2 := by norm_num [div_im]
  rw [hre, him, zero_mul, zero_add, log_re, norm_div]
  ring

theorem arctan_im_pos {w : ℂ} (hw : ‖w‖ < 1) (hi : 0 < w.im) :
    0 < (Complex.arctan w).im := by
  have ha : 0 < ‖1+w*I‖ := norm_pos_iff.mpr (one_add_mul_I_ne_zero hw)
  have hb : 0 < ‖1-w*I‖ := norm_pos_iff.mpr (one_sub_mul_I_ne_zero hw)
  have hab : ‖1+w*I‖ < ‖1-w*I‖ := by
    have h1 := norm_one_add_mul_I_sq w
    have h2 := norm_one_sub_mul_I_sq w
    nlinarith [norm_nonneg (1+w*I), norm_nonneg (1-w*I)]
  rw [arctan_im_eq]
  have := Real.log_neg (div_pos ha hb) ((div_lt_one hb).mpr hab)
  linarith

theorem arctan_im_neg {w : ℂ} (hw : ‖w‖ < 1) (hi : w.im < 0) :
    (Complex.arctan w).im < 0 := by
  have hb : 0 < ‖1-w*I‖ := norm_pos_iff.mpr (one_sub_mul_I_ne_zero hw)
  have hab : ‖1-w*I‖ < ‖1+w*I‖ := by
    have h1 := norm_one_add_mul_I_sq w
    have h2 := norm_one_sub_mul_I_sq w
    nlinarith [norm_nonneg (1+w*I), norm_nonneg (1-w*I)]
  rw [arctan_im_eq]
  have := Real.log_pos ((one_lt_div hb).mpr hab)
  linarith

theorem arctan_im_mul_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (Complex.arctan w).im * w.im := by
  rcases lt_trichotomy w.im 0 with hi | hi | hi
  · exact mul_nonneg_of_nonpos_of_nonpos (arctan_im_neg hw hi).le hi.le
  · simp [hi]
  · exact (mul_pos (arctan_im_pos hw hi) hi).le

theorem arctan_re_mul_nonneg {w : ℂ} (hw : ‖w‖ < 1) :
    0 ≤ (Complex.arctan w).re * w.re := by
  rw [arctan_re_eq hw]
  have hn : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
  rcases lt_trichotomy w.re 0 with hi | hi | hi
  · have hr : Real.arctan (2*w.re/(1-‖w‖^2)) < 0 :=
      Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos (by linarith) hn)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hi.le
  · simp [hi]
  · have hr : 0 < Real.arctan (2*w.re/(1-‖w‖^2)) :=
      Real.arctan_pos.mpr (div_pos (by linarith) hn)
    positivity

theorem arctan_div_re_pos {w : ℂ} (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    0 < (Complex.arctan w / w).re := by
  rw [div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hw0)
  have hr := arctan_re_mul_nonneg hw
  have hi := arctan_im_mul_nonneg hw
  by_cases hre : w.re = 0
  · have him : w.im ≠ 0 := by
      intro h; apply hw0; exact Complex.ext (by simpa using hre) (by simpa using h)
    rcases lt_or_gt_of_ne him with him | him
    · have := mul_pos_of_neg_of_neg (arctan_im_neg hw him) him
      linarith
    · have := mul_pos (arctan_im_pos hw him) him
      linarith
  · have hn : 0 < 1-‖w‖^2 := by nlinarith [norm_nonneg w]
    have hp : 0 < (Complex.arctan w).re * w.re := by
      rw [arctan_re_eq hw]
      rcases lt_or_gt_of_ne hre with hre | hre
      · have h := Real.arctan_lt_zero.mpr (div_neg_of_neg_of_pos
          (by linarith : 2*w.re < 0) hn)
        exact mul_pos_of_neg_of_neg (by linarith) hre
      · have h := Real.arctan_pos.mpr (div_pos (by linarith : 0 < 2*w.re) hn)
        positivity
    linarith

@[simp] theorem deriv_F_zero : deriv F 0 = (8 / Real.pi^2 : ℝ) := by
  rw [(hasDerivAt_F (by simp : ‖(0 : ℂ)‖ < 1)).deriv]
  have he : (∑' n : ℕ, termDeriv n 0) = 1 := by
    rw [tsum_eq_single 0]
    · simp [termDeriv]
    · intro n hn
      have h : 2*n ≠ 0 := by omega
      simp [termDeriv, h]
  rw [he, mul_one]

theorem deriv_F_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (deriv F w).re := by
  by_cases hw0 : w = 0
  · rw [hw0, deriv_F_zero, ofReal_re]
    positivity
  · have he : deriv F w = (8 / Real.pi^2 : ℝ) * (Complex.arctan w / w) := by
      apply (mul_left_cancel₀ hw0)
      rw [mul_deriv_F hw]
      field_simp
    rw [he, re_ofReal_mul]
    exact mul_pos (by positivity) (arctan_div_re_pos hw hw0)

theorem F_injOn : InjOn F (Metric.ball 0 1) := by
  intro x hx y hy hxy
  by_contra hn
  have hd : y-x ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ‖x+(t : ℂ)*(y-x)‖ < 1 := by
    intro t ht
    have hh := (convex_ball (0 : ℂ) 1).add_smul_sub_mem hx hy ht
    simpa only [Metric.mem_ball, dist_zero_right, Complex.real_smul] using hh
  let H : ℝ → ℝ := fun t => (F (x+(t : ℂ)*(y-x))/(y-x)).re
  have hh : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt H (deriv F (x+(t : ℂ)*(y-x))).re t := by
    intro t ht
    have hf := (hasDerivAt_F (hseg t ht)).differentiableAt.hasDerivAt
    have hc := ((hasDerivAt_id (t : ℂ)).mul_const (y-x)).const_add x
    have hm := (hf.comp (t : ℂ) hc).div_const (y-x)
    have he : deriv F (x+(t : ℂ)*(y-x)) * (1*(y-x)) / (y-x) =
        deriv F (x+(t : ℂ)*(y-x)) := by field_simp
    rw [he] at hm
    exact hm.real_of_complex
  have hmono : StrictMonoOn H (Icc (0 : ℝ) 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 1)
      (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hh t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact deriv_F_re_pos (hseg t (interior_subset ht))
  have hlt := hmono (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
  simp only [H, ofReal_zero, zero_mul, add_zero, ofReal_one, one_mul, add_sub_cancel] at hlt
  rw [hxy] at hlt
  exact lt_irrefl _ hlt

theorem re_F_imaginary (t : ℝ) : (F ((t : ℂ)*I)).re = 0 := by
  have h : (starRingEnd ℂ) ((t : ℂ)*I) = -((t : ℂ)*I) := by simp
  have he := F_conj ((t : ℂ)*I)
  rw [h, F_neg] at he
  have hre := congr_arg Complex.re he
  simp only [neg_re, conj_re] at hre
  linarith

theorem re_F_pos {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re) : 0 < (F w).re := by
  let H : ℝ → ℝ := fun t => (F ((t : ℂ)+(w.im : ℂ)*I)).re
  have hseg : ∀ t ∈ Icc 0 w.re, ‖(t : ℂ)+(w.im : ℂ)*I‖ < 1 := by
    intro t ht
    have he : ‖(t : ℂ)+(w.im : ℂ)*I‖^2 = t^2+w.im^2 := by
      rw [Complex.sq_norm]
      simp [normSq_apply, pow_two]
    have hh : ‖w‖^2 = w.re^2+w.im^2 := by
      rw [Complex.sq_norm]
      simp [normSq_apply, pow_two]
    have hn : ‖w‖^2 < 1 := by nlinarith [norm_nonneg w]
    nlinarith [norm_nonneg ((t : ℂ)+(w.im : ℂ)*I), ht.1, ht.2]
  have hh : ∀ t ∈ Icc 0 w.re, HasDerivAt H (deriv F ((t : ℂ)+(w.im : ℂ)*I)).re t := by
    intro t ht
    have hf := (hasDerivAt_F (hseg t ht)).differentiableAt.hasDerivAt
    have hm := hf.comp (t : ℂ) ((hasDerivAt_id _).add_const ((w.im : ℂ)*I))
    convert hm.real_of_complex using 1 <;> first | rfl | simp
  have hmono : StrictMonoOn H (Icc 0 w.re) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 w.re)
      (fun t ht => (hh t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hh t (interior_subset ht)).hasDerivWithinAt)
    exact fun t ht => deriv_F_re_pos (hseg t (interior_subset ht))
  have hlt := hmono ⟨le_rfl, hr.le⟩ ⟨hr.le, le_rfl⟩ hr
  have he : (w.re : ℂ)+(w.im : ℂ)*I = w := by simp
  simpa only [H, ofReal_zero, zero_add, re_F_imaginary, he] using hlt

theorem re_F_neg {w : ℂ} (hw : ‖w‖ < 1) (hr : w.re < 0) : (F w).re < 0 := by
  have h := re_F_pos (w := -w) (by simpa using hw) (by simpa using neg_pos.mpr hr)
  simpa only [F_neg, neg_re, neg_pos] using h

theorem re_F_eq_zero {w : ℂ} (hr : w.re = 0) : (F w).re = 0 := by
  have he : w = (w.im : ℂ)*I := by apply Complex.ext <;> simp [hr]
  rw [he, re_F_imaginary]

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LensArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem g_F {w : ℂ} (hw : ‖w‖ < 1) : g (F w) = w :=
  F_injOn.leftInvOn_invFunOn (by simpa using hw)

theorem F_g {z : ℂ} (hz : z ∈ D) : F (g z) = z :=
  Function.invFunOn_eq hz

theorem norm_g_lt {z : ℂ} (hz : z ∈ D) : ‖g z‖ < 1 := by
  have h := Function.invFunOn_mem hz
  simpa [g] using h

theorem zero_mem_D : (0 : ℂ) ∈ D := ⟨0, by simp, F_zero⟩

@[simp] theorem g_zero : g 0 = 0 := by
  simpa using g_F (by simp : ‖(0 : ℂ)‖ < 1)

theorem g_eq_zero_iff {z : ℂ} (hz : z ∈ D) : g z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [← F_g hz, h, F_zero]
  · rintro rfl; exact g_zero

theorem deriv_F_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : deriv F w ≠ 0 := by
  intro h
  have hh := deriv_F_re_pos hw
  rw [h, zero_re] at hh
  exact lt_irrefl _ hh

theorem analyticOnNhd_g : AnalyticOnNhd ℂ g D := by
  rintro z ⟨w, hw, rfl⟩
  have hw' : ‖w‖ < 1 := by simpa using hw
  apply (analyticAt_comp_iff_of_deriv_ne_zero (analyticOnNhd_F w hw)
    (deriv_F_ne_zero hw')).mp
  apply analyticAt_id.congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hw] with v hv
  exact (g_F (by simpa using hv)).symm

theorem isOpen_D : IsOpen D := by
  rcases analyticOnNhd_F.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with h | h
  · obtain ⟨c, hc⟩ := h
    have hz : (0 : ℂ) ∈ Metric.ball 0 1 := by simp
    have hh : (1/2 : ℂ) ∈ Metric.ball 0 1 := by norm_num [Metric.mem_ball, norm_div]
    have he := F_injOn hz hh ((hc 0 hz).trans (hc _ hh).symm)
    norm_num at he
  · exact h _ Subset.rfl Metric.isOpen_ball

theorem deriv_g_F {w : ℂ} (hw : ‖w‖ < 1) : deriv g (F w) = (deriv F w)⁻¹ := by
  have hFw : F w ∈ D := ⟨w, by simpa using hw, rfl⟩
  have hg := (analyticOnNhd_g _ hFw).differentiableAt.hasDerivAt
  have hf := (hasDerivAt_F hw).differentiableAt.hasDerivAt
  have hc := hg.comp w hf
  have he : g ∘ F =ᶠ[𝓝 w] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simpa using hw : w ∈ Metric.ball 0 1)] with z hz
    exact g_F (by simpa using hz)
  have hid := hc.congr_of_eventuallyEq he.symm
  have hm : deriv g (F w) * deriv F w = 1 := hid.unique (hasDerivAt_id w)
  apply mul_right_cancel₀ (deriv_F_ne_zero hw)
  rw [hm, inv_mul_cancel₀ (deriv_F_ne_zero hw)]

theorem re_g_pos {z : ℂ} (hz : z ∈ D) (hr : 0 < z.re) : 0 < (g z).re := by
  by_contra h
  rcases (le_of_not_gt h).eq_or_lt with he | he
  · have hh := re_F_eq_zero he
    rw [F_g hz] at hh
    linarith
  · have hh := re_F_neg (norm_g_lt hz) he
    rw [F_g hz] at hh
    linarith

end
end PlanarLens

namespace PlanarLens
open Set Filter Complex
open scoped Topology ContDiff
noncomputable section

theorem A_pos {w : ℂ} (hw : ‖w‖ < 1) (hr : 0 < w.re) : 0 < A w := by
  rw [A, re_mul_deriv_F hw]
  apply mul_pos (by positivity)
  apply Real.arctan_pos.mpr
  apply div_pos (by linarith)
  nlinarith [norm_nonneg w]

theorem hasDerivAt_horizontal_g {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    HasDerivAt (fun h : ℝ => g ((h : ℂ)+(t : ℂ)*I))
      (deriv g ((v : ℂ)+(t : ℂ)*I)) v := by
  have hg := (analyticOnNhd_g _ hz).differentiableAt.hasDerivAt
  have hc := hg.comp (v : ℂ) ((hasDerivAt_id _).add_const ((t : ℂ)*I))
  convert hc.comp_ofReal using 1 <;> first | rfl | simp only [mul_one]

theorem horizontal_normSq_deriv {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) :
    HasDerivAt (fun h : ℝ => ‖g ((h : ℂ)+(t : ℂ)*I)‖^2)
      (2*A (g ((v : ℂ)+(t : ℂ)*I)) / ‖deriv F (g ((v : ℂ)+(t : ℂ)*I))‖^2) v := by
  have hh := (hasDerivAt_horizontal_g hz).norm_sq
  have he : deriv g ((v : ℂ)+(t : ℂ)*I) = (deriv F (g ((v : ℂ)+(t : ℂ)*I)))⁻¹ := by
    rw [← deriv_g_F (norm_g_lt hz), F_g hz]
  rw [he] at hh
  convert hh using 1
  rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
  simp only [A, Complex.sq_norm, Complex.mul_re, Complex.inv_re, Complex.inv_im,
    Complex.conj_re, Complex.conj_im, RCLike.re_to_complex]
  ring

theorem horizontal_normSq_deriv_pos {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hv : 0 < v) :
    0 < 2*A (g ((v : ℂ)+(t : ℂ)*I)) / ‖deriv F (g ((v : ℂ)+(t : ℂ)*I))‖^2 := by
  apply div_pos
  · exact mul_pos (by norm_num) (A_pos (norm_g_lt hz) (re_g_pos hz (by simpa using hv)))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (deriv_F_ne_zero (norm_g_lt hz)))

theorem horizontal_segment_mem {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    (_hv : 0 ≤ v) {h : ℝ} (hh : h ∈ Icc 0 v) : (h : ℂ)+(t : ℂ)*I ∈ D := by
  let R := ‖g ((v : ℂ)+(t : ℂ)*I)‖
  have hR : R < 1 := norm_g_lt hz
  let C := F '' Metric.closedBall (0 : ℂ) R
  have hCD : C ⊆ D := by
    apply image_mono
    intro w hw
    have hw' : ‖w‖ ≤ R := by simpa using hw
    simpa using hw'.trans_lt hR
  have hCc : IsCompact C := by
    apply (isCompact_closedBall (0 : ℂ) R).image_of_continuousOn
    exact continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall hR.le)
  have hCm {a : ℝ} : (a : ℂ)+(t : ℂ)*I ∈ C ↔
      (a : ℂ)+(t : ℂ)*I ∈ D ∧ ‖g ((a : ℂ)+(t : ℂ)*I)‖ ≤ R := by
    constructor
    · rintro ⟨w, hw, he⟩
      have hw' : ‖w‖ ≤ R := by simpa using hw
      refine ⟨hCD ⟨w, hw, he⟩, ?_⟩
      rw [← he, g_F (hw'.trans_lt hR)]
      exact hw'
    · rintro ⟨ha, hr⟩
      exact ⟨g _, by simpa using hr, F_g ha⟩
  let S := Icc h v ∩ (fun a : ℝ => (a : ℂ)+(t : ℂ)*I) ⁻¹' C
  have hSc : IsCompact S := isCompact_Icc.inter_right (hCc.isClosed.preimage (by fun_prop))
  have hvS : v ∈ S := ⟨⟨hh.2, le_rfl⟩, hCm.mpr ⟨hz, le_rfl⟩⟩
  obtain ⟨a, ha, hmin⟩ := hSc.exists_isMinOn ⟨v, hvS⟩ (continuous_id.continuousOn)
  have haD := (hCm.mp ha.2).1
  have haR := (hCm.mp ha.2).2
  have hha : h ≤ a := ha.1.1
  by_cases he : a = h
  · simpa only [he] using haD
  have hha' : h < a := lt_of_le_of_ne hha (Ne.symm he)
  have ha0 : 0 < a := hh.1.trans_lt hha'
  have hopen : IsOpen ((fun b : ℝ => (b : ℂ)+(t : ℂ)*I) ⁻¹' D) :=
    isOpen_D.preimage (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen a haD
  let d := min (a-h) ε / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hdh : d < a-h := by dsimp [d]; linarith [min_le_left (a-h) ε]
  have hdε : d < ε := by dsimp [d]; linarith [min_le_right (a-h) ε]
  let b := a-d
  have hhb : h < b := by dsimp [b]; linarith
  have hba : b < a := by dsimp [b]; linarith
  have hseg : ∀ x ∈ Icc b a, (x : ℂ)+(t : ℂ)*I ∈ D := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hx.2] : x-a ≤ 0)]
    have hxb : a-d ≤ x := hx.1
    linarith
  have hmono : StrictMonoOn (fun x : ℝ => ‖g ((x : ℂ)+(t : ℂ)*I)‖^2) (Icc b a) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc b a)
      (fun x hx => (horizontal_normSq_deriv (hseg x hx)).continuousAt.continuousWithinAt)
      (fun x hx => (horizontal_normSq_deriv (hseg x (interior_subset hx))).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    apply horizontal_normSq_deriv_pos (hseg x hx')
    linarith [hx'.1, hh.1]
  have hnorm : ‖g ((b : ℂ)+(t : ℂ)*I)‖ ≤ R := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    have hm := hmono ⟨le_rfl, hba.le⟩ ⟨hba.le, le_rfl⟩ hba
    have hR0 : 0 ≤ R := norm_nonneg _
    nlinarith [norm_nonneg (g ((a : ℂ)+(t : ℂ)*I))]
  have hbS : b ∈ S := ⟨⟨hhb.le, hba.le.trans ha.1.2⟩,
    hCm.mpr ⟨hseg b ⟨le_rfl, hba.le⟩, hnorm⟩⟩
  have ham : a ≤ b := hmin hbS
  exact False.elim (not_le_of_gt hba ham)

theorem neg_conj_mem_D {z : ℂ} (hz : z ∈ D) : -(starRingEnd ℂ) z ∈ D := by
  rcases hz with ⟨w, hw, rfl⟩
  refine ⟨-(starRingEnd ℂ) w, by simpa using hw, ?_⟩
  simp

theorem horizontal_segment_mem_signed {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D)
    {h : ℝ} (hh : h ∈ uIcc 0 v) : (h : ℂ)+(t : ℂ)*I ∈ D := by
  rcases le_total 0 v with hv | hv
  · rw [uIcc_of_le hv] at hh
    exact horizontal_segment_mem hz hv hh
  · rw [uIcc_of_ge hv] at hh
    have he (a : ℝ) : -((starRingEnd ℂ) ((a : ℂ)+(t : ℂ)*I)) = ((-a : ℝ) : ℂ)+(t : ℂ)*I := by
      apply Complex.ext <;> simp
    have hz' := neg_conj_mem_D hz
    rw [he] at hz'
    have hh' : -h ∈ Icc 0 (-v) := ⟨by linarith [hh.2], by linarith [hh.1]⟩
    have hhD := horizontal_segment_mem hz' (by linarith) hh'
    have hneg := neg_conj_mem_D hhD
    simpa only [he, neg_neg] using hneg

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.HorizontalIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u52 u53 u54

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff

namespace SmoothPaths
open Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section

universe u
variable {E F : Type u} {H : Type u52} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem contDiff_integralPath {f : E → F} (hf : ContDiff ℝ ∞ f)
    (L : H →L[ℝ] C(SmoothODE.Time, E)) :
    ContDiff ℝ ∞ (fun z => integralPath (superpose hf.continuous (L z))) :=
  (integralPath (F := F)).contDiff.comp ((contDiff_superpose hf).comp L.contDiff)

end
end SmoothPaths

namespace SmoothExtension
open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section

variable {E : Type u53} {F : Type u54} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_global_near_closed {U K : Set E} (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ f₁ : E → F, ContDiff ℝ ∞ f₁ ∧ f₁ =ᶠ[𝓝ˢ K] f := by
  obtain ⟨b, hb0, hb1, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hK
    (disjoint_left.mpr (by intro x hx hxK; exact hx (hKU hxK))) (n := ⊤)
  have hb : ContDiff ℝ ∞ b := contMDiff_iff_contDiff.mp b.contMDiff
  refine ⟨fun x => b x • f x, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hb.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hh : ∀ᶠ y in 𝓝 x, b y = 0 := hb0.filter_mono (nhds_le_nhdsSet hx)
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [hh] with y hy
      simp [hy]
  · filter_upwards [hb1] with x hx
    simp [hx]

end
end SmoothExtension

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem density_nonneg (k : ℕ) (z : ℂ) : 0 ≤ density k z := by
  unfold density; positivity

theorem contDiffOn_density (k : ℕ) : ContDiffOn ℝ ∞ (density k) D := by
  have hg : ContDiffOn ℝ ∞ g D := (analyticOnNhd_g.contDiffOn isOpen_D.uniqueDiffOn).restrict_scalars ℝ
  have hd : ContDiffOn ℝ ∞ (deriv g) D :=
    (analyticOnNhd_g.deriv.contDiffOn isOpen_D.uniqueDiffOn).restrict_scalars ℝ
  have he : density k = fun z => (‖g z‖^2)^(k-1) * ‖deriv g z‖^2 := by
    funext z
    simp only [density, ← pow_mul]
    congr 2
    omega
  rw [he]
  exact ((hg.norm_sq ℂ).pow (k-1)).mul (hd.norm_sq ℂ)

theorem continuousOn_density (k : ℕ) : ContinuousOn (density k) D :=
  (contDiffOn_density k).continuousOn

theorem integrable_density {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    IntervalIntegrable (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) volume 0 v := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_density k).comp (by fun_prop)
  intro h hh
  exact horizontal_segment_mem_signed hz hh

theorem hasDerivAt_J {v t : ℝ} (hz : (v : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    HasDerivAt (fun v => J k v t) ((k : ℝ)^2*density k ((v : ℂ)+(t : ℂ)*I)) v := by
  have hc : ContinuousAt (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) v :=
    ((continuousOn_density k).continuousAt (isOpen_D.mem_nhds hz)).comp (f := fun h : ℝ => (h : ℂ)+(t : ℂ)*I)
      (show ContinuousAt (fun h : ℝ => (h : ℂ)+(t : ℂ)*I) v from by fun_prop)
  have hm : StronglyMeasurableAtFilter
      (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) (𝓝 v) volume := by
    apply ContinuousAt.stronglyMeasurableAtFilter
      (isOpen_D.preimage (show Continuous (fun h : ℝ => (h : ℂ)+(t : ℂ)*I) from by fun_prop))
      (fun h hh => ((continuousOn_density k).continuousAt (isOpen_D.mem_nhds hh)).comp (f := fun a : ℝ => (a : ℂ)+(t : ℂ)*I)
        (show ContinuousAt (fun a : ℝ => (a : ℂ)+(t : ℂ)*I) h from by fun_prop))
      v hz
  exact (intervalIntegral.integral_hasDerivAt_right (integrable_density hz k) hm hc).const_mul _

theorem J_affine (k : ℕ) (v t : ℝ) :
    J k v t = (k : ℝ)^2*v*∫ a in (0 : ℝ)..1, density k (((a*v : ℝ) : ℂ)+(t : ℂ)*I) := by
  rw [J, mul_assoc]
  congr 1
  have hh := intervalIntegral.smul_integral_comp_mul_right
    (fun h : ℝ => density k ((h : ℂ)+(t : ℂ)*I)) v (a := 0) (b := 1)
  simpa only [smul_eq_mul, zero_mul, one_mul] using hh.symm

theorem contDiffOn_J (k : ℕ) : ContDiffOn ℝ ∞ (fun z : ℂ => J k z.re z.im) D := by
  intro z hz
  let C := (fun a : ℝ => (((a*z.re : ℝ) : ℂ)+(z.im : ℂ)*I)) '' Icc (0 : ℝ) 1
  have hCc : IsCompact C := isCompact_Icc.image (by fun_prop)
  have hCD : C ⊆ D := by
    rintro _ ⟨a, ha, rfl⟩
    apply horizontal_segment_mem_signed (v := z.re) (t := z.im)
      (by simpa only [re_add_im] using hz)
    by_cases hv : 0 ≤ z.re
    · rw [uIcc_of_le hv]
      constructor <;> nlinarith [ha.1, ha.2]
    · rw [uIcc_of_ge (le_of_not_ge hv)]
      constructor <;> nlinarith [ha.1, ha.2]
  obtain ⟨f, hf, he⟩ := SmoothExtension.exists_global_near_closed isOpen_D hCc.isClosed hCD
    (contDiffOn_density k)
  have hglob : ContDiff ℝ ∞ (fun w : ℂ =>
      (k : ℝ)^2*w.re*SmoothPaths.integralPath (SmoothPaths.superpose hf.continuous (horizontalPath w))) :=
    (contDiff_const.mul Complex.reCLM.contDiff).mul
      (SmoothPaths.contDiff_integralPath hf horizontalPath)
  have heq : ∀ᶠ w in 𝓝 z, ∀ a ∈ Icc (0 : ℝ) 1,
      f ((((a*w.re : ℝ) : ℂ)+(w.im : ℂ)*I)) = density k ((((a*w.re : ℝ) : ℂ)+(w.im : ℂ)*I)) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro a ha
    have hs : ∀ᶠ y in 𝓝 ((((a*z.re : ℝ) : ℂ)+(z.im : ℂ)*I)), f y = density k y :=
      he.filter_mono (nhds_le_nhdsSet (mem_image_of_mem _ ha))
    exact (show ContinuousAt (fun p : ℂ×ℝ => (((p.2*p.1.re : ℝ) : ℂ)+(p.1.im : ℂ)*I)) (z,a)
      from by fun_prop) hs
  apply ContDiffAt.contDiffWithinAt
  apply hglob.contDiffAt.congr_of_eventuallyEq
  filter_upwards [heq] with w hw
  rw [J_affine, SmoothPaths.integralPath_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ha
  have hp : projIcc (0 : ℝ) 1 zero_le_one a = ⟨a, ha⟩ := by exact projIcc_of_mem zero_le_one ha
  simp only [SmoothODE.extend, hp, SmoothPaths.superpose_apply, horizontalPath_apply]
  exact (hw a ha).symm

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.StripMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u55 u56 u57 u58 u59 u60

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set Filter Asymptotics
open scoped Topology ContDiff
noncomputable section

variable {E : Type u55} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {ι : Type u56} [Fintype ι]

theorem isOpen_domain (ℓ : ι → E →L[ℂ] ℂ) : IsOpen (domain ℓ) := by
  have he : domain ℓ = ⋂ j, (ℓ j) ⁻¹' PlanarLens.D := by ext z; simp [domain]
  rw [he]
  exact isOpen_iInter_of_finite (fun j => PlanarLens.isOpen_D.preimage (ℓ j).continuous)

omit [Fintype ι] in
theorem zero_mem_domain (ℓ : ι → E →L[ℂ] ℂ) : (0 : E) ∈ domain ℓ := by
  intro j
  simpa using PlanarLens.zero_mem_D

theorem analyticOnNhd_tuple (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ (tuple ℓ k) (domain ℓ) := by
  intro z hz
  apply ((EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.analyticAt _).comp
  exact AnalyticAt.pi (fun j => ((PlanarLens.analyticOnNhd_g _ (hz j)).comp ((ℓ j).analyticAt z)).pow k)

omit [Fintype ι] in
theorem tuple_zero_iff (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) {k : ℕ} (hk : 1 ≤ k)
    {z : E} (hz : z ∈ domain ℓ) : tuple ℓ k z = 0 ↔ z = 0 := by
  constructor
  · intro hf
    apply hℓ
    funext j
    have hj := congrArg (fun w : EuclideanSpace ℂ ι => w j) hf
    have hg : PlanarLens.g (ℓ j z) = 0 := (pow_eq_zero_iff (by omega : k ≠ 0)).mp (by simpa using hj)
    simpa using (PlanarLens.g_eq_zero_iff (hz j)).mp hg
  · rintro rfl
    ext j
    simp only [tuple_apply, map_zero, PlanarLens.g_zero, zero_pow (by omega : k ≠ 0)]
    rfl

theorem tuple_order (ℓ : ι → E →L[ℂ] ℂ) (k : ℕ) :
    tuple ℓ k =O[𝓝 (0 : E)] (fun z : E => ‖z‖^k) := by
  have hc (j : ι) : (fun z => PlanarLens.g (ℓ j z)) =O[𝓝 (0 : E)] (fun z : E => ‖z‖) := by
    have ha : AnalyticAt ℂ (fun z => PlanarLens.g (ℓ j z)) (0 : E) :=
      (PlanarLens.analyticOnNhd_g _ (by simpa using PlanarLens.zero_mem_D)).comp ((ℓ j).analyticAt 0)
    have hh := ha.differentiableAt.isBigO_sub.norm_right
    simpa only [map_zero, PlanarLens.g_zero, sub_zero] using hh
  have hp : (fun z j => PlanarLens.g (ℓ j z)^k) =O[𝓝 (0 : E)] (fun z : E => ‖z‖^k) :=
    isBigO_pi.mpr (fun j => (hc j).pow k)
  exact ((EuclideanSpace.equiv ι ℂ).symm.toContinuousLinearMap.isBigO_comp
    (fun z j => PlanarLens.g (ℓ j z)^k) _).trans hp

variable [FiniteDimensional ℂ E]

omit [Fintype ι] in

theorem compact_inner_preimage (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) {r : ℝ} (hr : r < 1) :
    IsCompact {z : E | ∀ j, ℓ j z ∈ PlanarLens.F '' Metric.closedBall (0 : ℂ) r} := by
  let L : E →L[ℂ] (ι → ℂ) := ContinuousLinearMap.pi ℓ
  have hL : Topology.IsClosedEmbedding L :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hℓ)
  have hC : IsCompact (PlanarLens.F '' Metric.closedBall (0 : ℂ) r) :=
    (isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
      (PlanarLens.continuousOn_F_closedBall.mono (Metric.closedBall_subset_closedBall hr.le))
  have hc := hL.isCompact_preimage (isCompact_pi_infinite (fun _ : ι => hC))
  exact hc

theorem compact_sublevel (ℓ : ι → E →L[ℂ] ℂ)
    (hℓ : Function.Injective (fun z => fun j => ℓ j z)) {k : ℕ} (hk : 1 ≤ k)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    IsCompact {z : E | z ∈ domain ℓ ∧ ‖tuple ℓ k z‖^2 ≤ s} := by
  have hk0 : 2*k ≠ 0 := by omega
  have hval : (s+1)/2 ∈ Icc ((0 : ℝ)^(2*k)) ((1 : ℝ)^(2*k)) := by
    simp only [zero_pow hk0, one_pow]
    constructor <;> linarith
  obtain ⟨r, hr, hre⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun r : ℝ => r^(2*k)) (by fun_prop) hval
  dsimp only at hre
  have hr0 : 0 ≤ r := hr.1
  have hr1 : r < 1 := by
    by_contra hn
    have her : r = 1 := le_antisymm hr.2 (le_of_not_gt hn)
    rw [her, one_pow] at hre
    linarith
  let C := {z : E | ∀ j, ℓ j z ∈ PlanarLens.F '' Metric.closedBall (0 : ℂ) r}
  have hC : IsCompact C := compact_inner_preimage ℓ hℓ hr1
  have hCD : C ⊆ domain ℓ := by
    intro z hz j
    rcases hz j with ⟨w, hw, he⟩
    refine ⟨w, ?_, he⟩
    have hw' : ‖w‖ ≤ r := by simpa using hw
    simpa using hw'.trans_lt hr1
  have hsub : ∀ z ∈ domain ℓ, ‖tuple ℓ k z‖^2 ≤ s → z ∈ C := by
    intro z hz hzs j
    have hcoord : ‖PlanarLens.g (ℓ j z)‖^(2*k) ≤ ‖tuple ℓ k z‖^2 := by
      have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (tuple ℓ k z) j) 2
      simpa only [tuple_apply, norm_pow, ← pow_mul, Nat.mul_comm k 2] using hh
    have hp : ‖PlanarLens.g (ℓ j z)‖^(2*k) ≤ r^(2*k) := by linarith
    have hn : ‖PlanarLens.g (ℓ j z)‖ ≤ r := (pow_le_pow_iff_left₀ (norm_nonneg _) hr0 hk0).mp hp
    exact ⟨PlanarLens.g (ℓ j z), by simpa using hn, PlanarLens.F_g (hz j)⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hcont : Continuous (fun z : C => ‖tuple ℓ k z‖^2) :=
    ((analyticOnNhd_tuple ℓ k).continuousOn.mono hCD).domRestrict.norm.pow 2
  have hclosed : IsClosed {z : C | ‖tuple ℓ k z‖^2 ≤ s} := isClosed_le hcont continuous_const
  have hc := hclosed.isCompact.image continuous_subtype_val
  convert hc using 1
  ext z
  constructor
  · intro hz
    exact ⟨⟨z, hsub z hz.1 hz.2⟩, hz.2, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hCD z.2, hz⟩

end
end PolarStrips

namespace ComplexCoordinates
open scoped ComplexConjugate ContDiff
noncomputable section
variable {ι : Type u57} [Fintype ι]

theorem re_functional (b : R ι) (z : C ι) :
    (functional b z).re = inner (𝕜 := ℝ) b (re z) := by
  simp [functional_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem im_functional (b : R ι) (z : C ι) :
    (functional b z).im = inner (𝕜 := ℝ) b (im z) := by
  simp [functional_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem norm_sq_parts (z : C ι) : ‖z‖^2 = ‖re z‖^2+‖im z‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, re_apply, im_apply, Real.norm_eq_abs, sq_abs,
    Complex.sq_norm, Complex.normSq_apply, ← pow_two, Finset.sum_add_distrib]

theorem real_inner_parts (z w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    inner (𝕜 := ℝ) z w = inner (𝕜 := ℝ) (re z) (re w)+inner (𝕜 := ℝ) (im z) (im w) := by
  let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
  simp [real_inner_eq_re_inner, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Finset.sum_add_distrib]

theorem functional_injective {κ : Type u60} (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x)) :
    Function.Injective (fun z : C ι => fun j => functional (b j) z) := by
  intro z w h
  apply parts.injective
  apply Prod.ext
  · apply hb
    funext j
    have hh := congrArg Complex.re (congrFun h j)
    simpa only [re_functional, parts_apply] using hh
  · apply hb
    funext j
    have hh := congrArg Complex.im (congrFun h j)
    simpa only [im_functional, parts_apply] using hh

end
end ComplexCoordinates

namespace PlanarLens
open Set Filter Complex MeasureTheory
open scoped Topology ContDiff
noncomputable section

theorem contDiffAt_primitive {z : ℂ} (hz : z ∈ D) (k : ℕ) :
    ContDiffAt ℝ ∞ (primitive k) z :=
  (contDiffOn_J k).contDiffAt (isOpen_D.mem_nhds hz)

theorem J_mono {v w t : ℝ} (hv : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hw : (w : ℂ)+(t : ℂ)*I ∈ D) (hvw : v ≤ w) (k : ℕ) : J k v t ≤ J k w t := by
  have hi := (integrable_density hv k).symm.trans (integrable_density hw k)
  have he := intervalIntegral.integral_add_adjacent_intervals (integrable_density hv k) hi
  have hp : 0 ≤ ∫ h in v..w, density k ((h : ℂ)+(t : ℂ)*I) :=
    intervalIntegral.integral_nonneg hvw (fun _ _ => density_nonneg _ _)
  unfold J
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  linarith

theorem J_product_nonneg {v w t : ℝ} (hv : (v : ℂ)+(t : ℂ)*I ∈ D)
    (hw : (w : ℂ)+(t : ℂ)*I ∈ D) (k : ℕ) :
    0 ≤ (J k w t-J k v t)*(w-v) := by
  rcases le_total v w with h | h
  · exact mul_nonneg (sub_nonneg.mpr (J_mono hv hw h k)) (sub_nonneg.mpr h)
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (J_mono hw hv h k)) (sub_nonpos.mpr h)

theorem fderiv_primitive_one {z : ℂ} (hz : z ∈ D) (k : ℕ) :
    fderiv ℝ (primitive k) z 1 = (k : ℝ)^2*density k z := by
  have hp := (contDiffAt_primitive hz k).differentiableAt (by simp)
  have hd : HasDerivAt (fun v : ℝ => (v : ℂ)+(z.im : ℂ)*I) 1 z.re :=
    by simpa using ((hasDerivAt_id (z.re : ℂ)).comp_ofReal.add_const ((z.im : ℂ)*I))
  have hp' : HasFDerivAt (primitive k) (fderiv ℝ (primitive k) z) ((z.re : ℂ)+(z.im : ℂ)*I) := by
    simpa only [Complex.re_add_im] using hp.hasFDerivAt
  have hh := hp'.comp_hasDerivAt z.re hd
  have hj := hasDerivAt_J (v := z.re) (t := z.im) (by simpa only [Complex.re_add_im] using hz) k
  have hh' : HasDerivAt (fun v => J k v z.im) (fderiv ℝ (primitive k) z 1) z.re := by
    simpa [primitive, Function.comp_def] using hh
  simpa only [Complex.re_add_im] using hh'.unique hj

theorem fderiv_primitive_apply {z : ℂ} (hz : z ∈ D) (k : ℕ) (h : ℂ) :
    fderiv ℝ (primitive k) z h =
      (k : ℝ)^2*density k z * h.re + fderiv ℝ (primitive k) z I * h.im := by
  have he : h = h.re • (1 : ℂ)+h.im • I := by apply Complex.ext <;> simp
  calc
    fderiv ℝ (primitive k) z h = fderiv ℝ (primitive k) z (h.re • (1 : ℂ)+h.im • I) := congrArg _ he
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul, fderiv_primitive_one hz k]; ring

end
end PlanarLens

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.StripEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u61 u62 u63 u64 u65 u66 u67 u68 u69

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set ComplexCoordinates
open scoped ContDiff
noncomputable section
variable {ι : Type u61} {κ : Type u62} [Fintype ι] [Fintype κ]

theorem contDiffAt_phase (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) : ContDiffAt ℝ ∞ (phase b k) z := by
  change ContDiffAt ℝ ∞ (fun z : C ι => (ComplexCoordinates.im z, -ComplexCoordinates.re z - ∑ j, PlanarLens.primitive k (functional (b j) z) • b j)) z
  refine (ComplexCoordinates.im : C ι →L[ℝ] R ι).contDiff.contDiffAt.prodMk
    ((ComplexCoordinates.re : C ι →L[ℝ] R ι).contDiff.contDiffAt.neg.sub ?_)
  apply ContDiffAt.sum
  intro j _
  exact ((PlanarLens.contDiffAt_primitive (hz j) k).comp z
    ((functional (b j)).restrictScalars ℝ).contDiff.contDiffAt).smul contDiffAt_const

theorem momentum_monotonic (b : κ → R ι) (k : ℕ) {z w : C ι}
    (hz : z ∈ domain (fun j => functional (b j)))
    (hw : w ∈ domain (fun j => functional (b j))) (hx : im z = im w) :
    inner (𝕜 := ℝ) ((phase b k w).2-(phase b k z).2) (re w-re z) ≤ -‖re w-re z‖^2 := by
  have hj (j : κ) : 0 ≤
      (PlanarLens.primitive k (functional (b j) w)-PlanarLens.primitive k (functional (b j) z)) *
      inner (𝕜 := ℝ) (b j) (re w-re z) := by
    have ht : (functional (b j) z).im = (functional (b j) w).im := by rw [im_functional, im_functional, hx]
    have hv : (((functional (b j) z).re : ℂ)+((functional (b j) w).im : ℂ)*Complex.I) ∈ PlanarLens.D := by
      rw [← ht, Complex.re_add_im]; exact hz j
    have hh := PlanarLens.J_product_nonneg (w := (functional (b j) w).re) hv (by simpa only [Complex.re_add_im] using hw j) k
    simpa only [PlanarLens.primitive, ht, inner_sub_right, ← re_functional] using hh
  have he : (phase b k w).2-(phase b k z).2 = -(re w-re z) -
      ∑ j, (PlanarLens.primitive k (functional (b j) w)-PlanarLens.primitive k (functional (b j) z)) • b j := by
    simp only [phase, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [he, inner_sub_left, inner_neg_left, real_inner_self_eq_norm_sq]
  have hsum : 0 ≤ inner (𝕜 := ℝ)
      (∑ j, (PlanarLens.primitive k (functional (b j) w)-PlanarLens.primitive k (functional (b j) z)) • b j)
      (re w-re z) := by
    simp only [sum_inner, real_inner_smul_left]
    exact Finset.sum_nonneg (fun j _ => hj j)
  linarith

theorem injOn_phase (b : κ → R ι) (k : ℕ) :
    InjOn (phase b k) (domain (fun j => functional (b j))) := by
  intro z hz w hw he
  have hx : im z = im w := congrArg Prod.fst he
  have hp : (phase b k w).2-(phase b k z).2 = 0 := sub_eq_zero.mpr (congrArg Prod.snd he).symm
  have hh := momentum_monotonic b k hz hw hx
  rw [hp, inner_zero_left] at hh
  have hr : re w = re z := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (re w-re z)]))
  apply parts.injective
  exact Prod.ext hr.symm hx

end
end PolarStrips

namespace ComplexPotential
open ComplexCoordinates Set Filter
open scoped Topology ContDiff
noncomputable section

variable {E : Type u63} {F : Type u64} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem ddc_holomorphic_norm_sq {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : AnalyticOnNhd ℂ f U) {z : E} (hz : z ∈ U) (v w : E) :
    let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
    let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    ddc (complexStructure E) (fun x => ‖f x‖^2) z v w =
      standardTensor (complexStructure F) (fderiv ℝ f z v) (fderiv ℝ f z w) := by
  let : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have he := ddc_comp (complexStructure E) (complexStructure F)
    ((hf z hz).contDiffAt.restrict_scalars ℝ) (contDiff_norm_sq ℝ).contDiffAt
    (show ∀ᶠ x in 𝓝 z, ∀ a, fderiv ℝ f x (complexStructure E a) = complexStructure F (fderiv ℝ f x a) by
      filter_upwards [hU.mem_nhds hz] with x hx
      exact fderiv_commutes_complexStructure (hf x hx).differentiableAt) v w
  rw [ddc_norm_sq (complexStructure F) complexStructure_skew] at he
  exact he

variable {ι : Type u65} [Fintype ι]

theorem standardTensor_parts (v w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    standardTensor (complexStructure (C ι)) v w = phaseForm (parts v) (parts w) := by
  let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
  dsimp only
  rw [standardTensor_apply, complexStructure_apply, real_inner_parts]
  simp only [re_I_smul, im_I_smul, inner_neg_left, phaseForm, parts_apply]
  rw [real_inner_comm (im v) (re w)]
  ring

theorem standardTensor_coordinates (v w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    standardTensor (complexStructure (C ι)) v w =
      ∑ i, ((v i).re*(w i).im-(w i).re*(v i).im) := by
  dsimp only
  rw [standardTensor_parts]
  simp [phaseForm, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.sum_sub_distrib, mul_comm]

theorem scalar_wedge_mul (c v w : ℂ) :
    (c*v).re*(c*w).im-(c*w).re*(c*v).im =
      ‖c‖^2*(v.re*w.im-w.re*v.im) := by
  rw [Complex.sq_norm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

end
end ComplexPotential

namespace PolarStrips
open Set Filter ComplexCoordinates ComplexPotential
open scoped Topology ContDiff
noncomputable section
variable {ι : Type u66} {κ : Type u67} [Fintype ι] [Fintype κ]

theorem fderiv_tuple_apply (ℓ : κ → C ι →L[ℂ] ℂ) (k : ℕ) {z : C ι}
    (hz : z ∈ domain ℓ) (v : C ι) (j : κ) :
    fderiv ℝ (tuple ℓ k) z v j =
      (k : ℂ)*PlanarLens.g (ℓ j z)^(k-1)*deriv PlanarLens.g (ℓ j z)*ℓ j v := by
  have ht := ((analyticOnNhd_tuple ℓ k z hz).differentiableAt.restrictScalars ℝ).hasFDerivAt
  have hp := (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : κ => ℂ) j).restrictScalars ℝ).hasFDerivAt.comp z ht)
  have hg := ((PlanarLens.analyticOnNhd_g _ (hz j)).differentiableAt.hasDerivAt.pow k).hasFDerivAt
  have hc := (hg.comp z (ℓ j).hasFDerivAt).restrictScalars ℝ
  have he := hc.unique hp
  have hh := congrArg (fun L : C ι →L[ℝ] ℂ => L v) he
  change (ℓ j v)*((k : ℂ)*PlanarLens.g (ℓ j z)^(k-1)*deriv PlanarLens.g (ℓ j z)) =
    fderiv ℝ (tuple ℓ k) z v j at hh
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh.symm

theorem norm_coefficient (k : ℕ) (w : ℂ) :
    ‖(k : ℂ)*PlanarLens.g w^(k-1)*deriv PlanarLens.g w‖^2 =
      (k : ℝ)^2*PlanarLens.density k w := by
  simp only [norm_mul, norm_pow, Complex.norm_natCast, mul_pow, ← pow_mul, PlanarLens.density]
  have he : (k-1)*2 = 2*k-2 := by omega
  rw [he]
  ring

theorem fderiv_phase_apply (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) (v : C ι) :
    fderiv ℝ (phase b k) z v = (im v, -re v - ∑ j,
      fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) v) • b j) := by
  let L : κ → C ι →L[ℝ] R ι := fun j =>
    ((fderiv ℝ (PlanarLens.primitive k) (functional (b j) z)).comp
      ((functional (b j)).restrictScalars ℝ)).smulRight (b j)
  have hj (j : κ) : HasFDerivAt (fun x : C ι => PlanarLens.primitive k (functional (b j) x) • b j) (L j) z :=
    (((PlanarLens.contDiffAt_primitive (hz j) k).differentiableAt (by simp)).hasFDerivAt.comp z
      ((functional (b j)).restrictScalars ℝ).hasFDerivAt).smul_const (b j)
  have hs : HasFDerivAt (fun x : C ι => ∑ j, PlanarLens.primitive k (functional (b j) x) • b j)
      (∑ j, L j) z := by
    simpa only [Finset.sum_fn] using (HasFDerivAt.sum (u := Finset.univ) (fun j _ => hj j))
  have hd : HasFDerivAt (phase b k)
      ((im : C ι →L[ℝ] R ι).prod (-(re : C ι →L[ℝ] R ι)-∑ j, L j)) z :=
    im.hasFDerivAt.prodMk (re.hasFDerivAt.neg.sub hs)
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.prod_apply, sub_apply,
    neg_apply, sum_apply, L,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
  rfl

theorem phase_form_formula (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) (v w : C ι) :
    phaseForm (fderiv ℝ (phase b k) z v) (fderiv ℝ (phase b k) z w) =
      phaseForm (parts v) (parts w) + ∑ j,
        (k : ℝ)^2*PlanarLens.density k (functional (b j) z) *
          ((functional (b j) v).re*(functional (b j) w).im -
            (functional (b j) w).re*(functional (b j) v).im) := by
  rw [fderiv_phase_apply b k hz, fderiv_phase_apply b k hz]
  have he (a : C ι) (j : κ) : inner (𝕜 := ℝ) (im a) (b j) = (functional (b j) a).im := by
    rw [real_inner_comm, im_functional]
  have hf : phaseForm (im v, -re v - ∑ j,
        fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) v) • b j)
      (im w, -re w - ∑ j,
        fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) w) • b j) =
      phaseForm (parts v) (parts w) + ∑ j,
        (fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) v) * (functional (b j) w).im -
         fderiv ℝ (PlanarLens.primitive k) (functional (b j) z) (functional (b j) w) * (functional (b j) v).im) := by
    simp only [phaseForm, parts_apply, inner_sub_right, inner_neg_right, inner_sum,
      real_inner_smul_right, he, Finset.sum_sub_distrib]
    rw [real_inner_comm (im v) (re w), real_inner_comm (im w) (re v)]
    ring
  rw [hf]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [PlanarLens.fderiv_primitive_apply (hz j) k (functional (b j) v),
    PlanarLens.fderiv_primitive_apply (hz j) k (functional (b j) w)]
  ring

theorem phase_pullback (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) (v w : C ι) :
    let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
    phaseForm (fderiv ℝ (phase b k) z v) (fderiv ℝ (phase b k) z w) =
      ddc (complexStructure (C ι)) (fun x => ‖x‖^2 + ‖tuple (fun j => functional (b j)) k x‖^2) z v w := by
  let : InnerProductSpace ℝ (C ι) := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ (C κ) := InnerProductSpace.complexToReal
  let ℓ := fun j => functional (b j)
  have hτ : ContDiffAt ℝ ∞ (fun x => ‖tuple ℓ k x‖^2) z :=
    ((analyticOnNhd_tuple ℓ k z hz).contDiffAt.restrict_scalars ℝ).norm_sq ℂ
  dsimp only
  rw [ddc_add _ (contDiff_norm_sq ℝ).contDiffAt hτ,
    add_apply, add_apply,
    ddc_norm_sq _ complexStructure_skew,
    ddc_holomorphic_norm_sq (isOpen_domain ℓ) (analyticOnNhd_tuple ℓ k) hz,
    standardTensor_parts v w,
    standardTensor_coordinates (fderiv ℝ (tuple ℓ k) z v) (fderiv ℝ (tuple ℓ k) z w),
    phase_form_formula b k hz]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_tuple_apply ℓ k hz v j, fderiv_tuple_apply ℓ k hz w j, scalar_wedge_mul, norm_coefficient]

end
end PolarStrips

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u68} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem polar_antitone {K L : Set E} (h : K ⊆ L) : polar L ⊆ polar K :=
  fun _ hp q hq => hp q (h hq)

end
end ConvexPolar

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.MomentumBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u70 u71 u72 u73

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar
open Set Filter
open scoped ContDiff Topology
noncomputable section
variable {n : ℕ}

theorem isOpen_capacityBall (n : ℕ) (c : ℝ) : IsOpen (capacityBall n c) :=
  isOpen_lt (by fun_prop) continuous_const

theorem diagScale_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (diagScale a b : Phase n → Phase n) := by
  intro x y h
  exact Prod.ext ((smul_right_injective _ ha) (congrArg Prod.fst h))
    ((smul_right_injective _ hb) (congrArg Prod.snd h))

theorem omega0_diagScale (a b : ℝ) (v w : Phase n) :
    omega0 (diagScale a b v) (diagScale a b w) = (a*b)*omega0 v w := by
  simp only [omega0, diagScale_apply, real_inner_smul_left, real_inner_smul_right]
  ring

theorem omega0_nondegenerate (v : Phase n) (h : ∀ w : Phase n, omega0 v w = 0) : v = 0 := by
  have hh := h (-v.2, v.1)
  simp only [omega0, inner_neg_left, real_inner_self_eq_norm_sq, sub_neg_eq_add] at hh
  have h1 : v.1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.1, sq_nonneg ‖v.2‖])
  have h2 : v.2 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.2, sq_nonneg ‖v.1‖])
  exact Prod.ext h1 h2

theorem isInvertible_of_preserves_omega0 (L : Phase n →L[ℝ] Phase n)
    (hL : ∀ v w, omega0 (L v) (L w) = omega0 v w) : L.IsInvertible := by
  have hi : Function.Injective L := by
    intro v w hvw
    have hz : L (v-w) = 0 := by rw [map_sub, hvw, sub_self]
    apply sub_eq_zero.mp
    apply omega0_nondegenerate
    intro a
    rw [← hL, hz]
    simp [omega0]
  have hs : Function.Surjective L := LinearMap.surjective_of_injective hi
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

theorem hasSymplecticEmbedding_of_injOn {U V : Set (Phase n)} (hU : IsOpen U)
    {e : Phase n → Phase n} (he : ContDiffOn ℝ ∞ e U) (hi : InjOn e U)
    (hm : MapsTo e U V) (hω : ∀ z ∈ U, ∀ v w,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    HasSymplecticEmbedding U V := by
  refine ⟨e, he, ?_, hm, hω⟩
  exact (LocalEmbedding.isOpenEmbedding hU he hi (fun z hz => isInvertible_of_preserves_omega0 _ (hω z hz))).isEmbedding

theorem HasSymplecticEmbedding.injOn {U : Set (Phase n)} {e : Phase n → Phase n}
    (he : Topology.IsEmbedding (fun z : U => e z)) : InjOn e U := by
  intro x hx y hy h
  exact congrArg Subtype.val (he.injective (show e (⟨x,hx⟩ : U) = e (⟨y,hy⟩ : U) from h))

theorem mapsTo_scaled_ball {lam c : ℝ} (hlam : 0 < lam) :
    MapsTo (diagScale (Real.sqrt lam) (Real.sqrt lam) : Phase n → Phase n)
      (capacityBall n c) (capacityBall n (lam*c)) := by
  intro z hz
  change Real.pi*(‖Real.sqrt lam • z.1‖^2+‖Real.sqrt lam • z.2‖^2) < lam*c
  have hsq : |Real.sqrt lam|^2 = lam := by rw [sq_abs, Real.sq_sqrt hlam.le]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, hsq]
  have hh := mul_lt_mul_of_pos_left hz hlam
  nlinarith

theorem embedding_of_scaled_ball_map {lam c a b : ℝ} (hlam : 0 < lam) (hab : a*b = lam⁻¹)
    {V : Set (Phase n)} {e : Phase n → Phase n}
    (he : ContDiffOn ℝ ∞ e (capacityBall n (lam*c)))
    (hi : InjOn e (capacityBall n (lam*c)))
    (hm : MapsTo (fun z => diagScale a b (e z)) (capacityBall n (lam*c)) V)
    (hω : ∀ z ∈ capacityBall n (lam*c), ∀ v w,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    HasSymplecticEmbedding (capacityBall n c) V := by
  let D : Phase n →L[ℝ] Phase n := diagScale (Real.sqrt lam) (Real.sqrt lam)
  let L : Phase n →L[ℝ] Phase n := diagScale a b
  let F : Phase n → Phase n := fun z => L (e (D z))
  have hD : MapsTo D (capacityBall n c) (capacityBall n (lam*c)) := mapsTo_scaled_ball hlam
  have hLinj : Function.Injective L := diagScale_injective (left_ne_zero_of_mul (by rw [hab]; exact inv_ne_zero hlam.ne'))
    (right_ne_zero_of_mul (by rw [hab]; exact inv_ne_zero hlam.ne'))
  have hDinj : Function.Injective D := diagScale_injective (Real.sqrt_pos.mpr hlam).ne' (Real.sqrt_pos.mpr hlam).ne'
  have hs (z : Phase n) (hz : z ∈ capacityBall n c) : ContDiffAt ℝ ∞ e (D z) :=
    he.contDiffAt ((isOpen_capacityBall _ _).mem_nhds (hD hz))
  apply hasSymplecticEmbedding_of_injOn (isOpen_capacityBall n c) (e := F)
  · intro z hz
    exact (L.contDiff.contDiffAt.comp z ((hs z hz).comp z D.contDiff.contDiffAt)).contDiffWithinAt
  · intro z hz w hw h
    exact hDinj (hi (hD hz) (hD hw) (hLinj h))
  · intro z hz
    exact hm (hD hz)
  · intro z hz v w
    have hd : HasFDerivAt F (L.comp ((fderiv ℝ e (D z)).comp D)) z :=
      L.hasFDerivAt.comp z (((hs z hz).differentiableAt (by simp)).hasFDerivAt.comp z D.hasFDerivAt)
    rw [hd.fderiv]
    change omega0 (diagScale a b (fderiv ℝ e (D z) (D v)))
      (diagScale a b (fderiv ℝ e (D z) (D w))) = _
    rw [omega0_diagScale, hω _ (hD hz), hab, omega0_diagScale]
    rw [← pow_two, Real.sq_sqrt hlam.le, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]

end
end SymmetricPolar

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PolarApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u74 u75 u76 u77

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real
open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar
open Set Filter ComplexCoordinates ComplexPotential PolarStrips
open scoped Topology ContDiff
noncomputable section
variable {n : ℕ} {κ : Type u74} [Fintype κ]

theorem exists_positive_slack {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    ∃ η : ℝ, 0 < η ∧ (1+η)*c < d := by
  let η := (d-c)/(2*c)
  have hη : 0 < η := div_pos (sub_pos.mpr hcd) (mul_pos (by norm_num) hc)
  have he : η*c = (d-c)/2 := by dsimp [η]; field_simp
  exact ⟨η, hη, by nlinarith⟩

theorem finite_strips_embedding (b : κ → Position n)
    (hb : Function.Injective (fun x : Position n => fun j => inner (𝕜 := ℝ) (b j) x))
    {c : ℝ} (hc : 0 < c) (hc4 : c < 4) :
    HasSymplecticEmbedding (capacityBall n c)
      (interior (ConvexPolar.stripBody b) ×ˢ interior (ConvexPolar.polar (ConvexPolar.stripBody b))) := by
  let : InnerProductSpace ℝ (C (Fin n)) := InnerProductSpace.complexToReal
  obtain ⟨η, hη, hηc⟩ := exists_positive_slack hc hc4
  obtain ⟨k, hk, hscaled⟩ := exists_scaled_image b hb hη
  let ℓ := fun j => functional (b j)
  have hℓ : Function.Injective (fun z : C (Fin n) => fun j => ℓ j z) := functional_injective b hb
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  let S := (1+η)*Real.pi*(k : ℝ)/4
  have hS : 0 < S := by dsimp [S]; positivity
  let a := S*c/Real.pi
  have ha : 0 < a := div_pos (mul_pos hS hc) Real.pi_pos
  have hak : a < (k : ℝ) := by
    apply (div_lt_iff₀ Real.pi_pos).mpr
    have hh := mul_lt_mul_of_pos_right hηc (mul_pos Real.pi_pos hkpos)
    dsimp [S]
    nlinarith
  obtain ⟨Q, hQ, _hQi, hQm, hQω⟩ :=
    exists_ball_from_holomorphic_zero (isOpen_domain ℓ) (zero_mem_domain ℓ)
      (analyticOnNhd_tuple ℓ k) (fun x hx => tuple_zero_iff ℓ hℓ hk hx) hk (tuple_order ℓ k)
      (fun s hs hs1 => compact_sublevel ℓ hℓ hk hs hs1) ha hak
  let i : Phase n →L[ℝ] C (Fin n) := parts.symm.toContinuousLinearMap
  have hi (z : Phase n) (hz : z ∈ capacityBall n (S*c)) : ‖i z‖^2 < a := by
    apply (lt_div_iff₀ Real.pi_pos).mpr
    have he : ‖i z‖^2 = ‖z.1‖^2+‖z.2‖^2 := by
      have hh := norm_sq_parts (parts.symm z)
      have hre : re (parts.symm z) = z.1 := congrArg Prod.fst (parts.apply_symm_apply z)
      have him : im (parts.symm z) = z.2 := congrArg Prod.snd (parts.apply_symm_apply z)
      simpa only [i, ContinuousLinearEquiv.coe_coe, hre, him] using hh
    rw [he, mul_comm]
    exact hz
  let e : Phase n → Phase n := fun z => phase b k (Q (i z))
  have hs (z : Phase n) (hz : z ∈ capacityBall n (S*c)) : ContDiffAt ℝ ∞ e z := by
    have hphase : ContDiffAt ℝ ∞ (phase b k) (Q (i z)) :=
      contDiffAt_phase b k (hQm _ (hi z hz)).1
    have hh := hphase.comp z (hQ.contDiffAt.comp z i.contDiff.contDiffAt)
    simpa only [Function.comp_def, e] using hh
  apply embedding_of_scaled_ball_map hS (a := 1) (b := S⁻¹) (by simp) (e := e)
  · exact fun z hz => (hs z hz).contDiffWithinAt
  · intro z hz w hw he
    have hq : Q (i z) = Q (i w) := injOn_phase b k (hQm _ (hi z hz)).1 (hQm _ (hi w hw)).1 he
    exact parts.symm.injective (Q.injective hq)
  · intro z hz
    have hm := hscaled (Q (i z)) (hQm _ (hi z hz)).1 (hQm _ (hi z hz)).2
    simpa only [diagScale_apply, one_smul, e, S, Set.mem_prod] using hm
  · intro z hz v w
    have hphase : HasFDerivAt (phase b k) (fderiv ℝ (phase b k) (Q (i z))) (Q (i z)) :=
      ((contDiffAt_phase b k (hQm _ (hi z hz)).1).differentiableAt (by simp)).hasFDerivAt
    have hd : HasFDerivAt e ((fderiv ℝ (phase b k) (Q (i z))).comp
        ((fderiv ℝ (Q : C (Fin n) → C (Fin n)) (i z)).comp i)) z := by
      have hh := hphase.comp z ((hQ.differentiable (by simp) (i z)).hasFDerivAt.comp z i.hasFDerivAt)
      simpa only [Function.comp_def, e] using hh
    rw [hd.fderiv]
    change phaseForm (fderiv ℝ (phase b k) (Q (i z)) (fderiv ℝ (Q : C (Fin n) → C (Fin n)) (i z) (i v)))
      (fderiv ℝ (phase b k) (Q (i z)) (fderiv ℝ (Q : C (Fin n) → C (Fin n)) (i z) (i w))) = _
    rw [phase_pullback b k (hQm _ (hi z hz)).1, hQω _ (hi z hz), standardTensor_parts]
    change phaseForm (parts (parts.symm v)) (parts (parts.symm w)) = _
    rw [parts.apply_symm_apply, parts.apply_symm_apply]
    rfl

end
end SymmetricPolar

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u75} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem zero_mem_interior_of_symmetric {K : Set E} (hK : Convex ℝ K)
    (hi : (interior K).Nonempty) (hs : ∀ x, x ∈ K ↔ -x ∈ K) : (0 : E) ∈ interior K := by
  obtain ⟨x, hx⟩ := hi
  have hn : -x ∈ interior K := by
    apply mem_interior_iff_mem_nhds.mpr
    have hh : K ∈ 𝓝 (-(-x)) := by simpa using mem_interior_iff_mem_nhds.mp hx
    have hh' := continuous_neg.continuousAt.preimage_mem_nhds hh
    have he : (fun y : E => -y) ⁻¹' K = K := by ext y; exact (hs y).symm
    rwa [he] at hh'
  have hm := hK.interior hx hn (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)+1/2 = 1)
  simpa using hm

theorem isClosed_polar (K : Set E) : IsClosed (polar K) := by
  have he : polar K = ⋂ q ∈ K, {p : E | inner (𝕜 := ℝ) q p ≤ 1} := by ext p; simp [polar]
  rw [he]
  exact isClosed_biInter (fun q _ => isClosed_le (by fun_prop) continuous_const)

theorem polar_abs_pairing {K : Set E} (hs : ∀ x, x ∈ K ↔ -x ∈ K)
    {p : E} (hp : p ∈ polar K) {x : E} (hx : x ∈ K) : |inner (𝕜 := ℝ) p x| ≤ 1 := by
  apply abs_le.mpr
  have hn := hp (-x) ((hs x).mp hx)
  rw [inner_neg_left, real_inner_comm] at hn
  exact ⟨by linarith, by rw [real_inner_comm]; exact hp x hx⟩

theorem norm_smul_normalized {x : E} (hx : x ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    ‖(r/‖x‖) • x‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr (norm_nonneg _)), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]

theorem normalized_inner {x : E} (hx : x ≠ 0) (r : ℝ) :
    inner (𝕜 := ℝ) ((r/‖x‖) • x) x = r*‖x‖ := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

theorem norm_le_of_mem_polar {K : Set E} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (0 : E) r ⊆ K) {p : E} (hp : p ∈ polar K) : ‖p‖ ≤ r⁻¹ := by
  by_cases hp0 : p = 0
  · simp [hp0, hr.le]
  have hq : (r/‖p‖) • p ∈ K := hball (by simpa using (norm_smul_normalized hp0 hr.le).le)
  have hh := hp _ hq
  rw [normalized_inner hp0] at hh
  have hh' : ‖p‖ ≤ r⁻¹ * (1 : ℝ) := (le_inv_mul_iff₀ hr).mpr hh
  simpa only [mul_one] using hh'

theorem isCompact_polar [FiniteDimensional ℝ E] {K : Set E} (h0 : (0 : E) ∈ interior K) : IsCompact (polar K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  have hr2 : 0 < r/2 := half_pos hr
  have hclosed : Metric.closedBall (0 : E) (r/2) ⊆ K := by
    intro x hx
    apply hball
    exact (Metric.mem_closedBall.mp hx).trans_lt (half_lt_self hr)
  apply (isCompact_closedBall (0 : E) ((r/2)⁻¹)).of_isClosed_subset (isClosed_polar K)
  intro p hp
  simpa using norm_le_of_mem_polar hr2 hclosed hp

theorem mem_polar_polar_iff [FiniteDimensional ℝ E] {K : Set E} (hK : Convex ℝ K) (hc : IsClosed K)
    (h0 : (0 : E) ∈ K) (x : E) : x ∈ polar (polar K) ↔ x ∈ K := by
  constructor
  · intro hx
    by_contra hn
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hK hc hn
    have hu : 0 < u := by simpa using hfu 0 h0
    let v : E := (InnerProductSpace.toDual ℝ E).symm f
    have hv (y : E) : inner (𝕜 := ℝ) y v = f y := by
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hp : u⁻¹ • v ∈ polar K := by
      intro y hy
      rw [real_inner_smul_right, hv, ← div_eq_inv_mul]
      exact (div_le_one hu).mpr (hfu y hy).le
    have hh := hx _ hp
    rw [real_inner_smul_left, real_inner_comm, hv, ← div_eq_inv_mul] at hh
    exact (not_le_of_gt hux) ((div_le_one hu).mp hh)
  · intro hx p hp
    rw [real_inner_comm]
    exact hp x hx

theorem closedBall_subset_polar_of_norm_bound {K : Set E} {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x ∈ K, ‖x‖ ≤ B) : Metric.closedBall (0 : E) ((B+1)⁻¹) ⊆ polar K := by
  intro p hp x hx
  have hp' : ‖p‖ ≤ (B+1)⁻¹ := by simpa using hp
  have hi := real_inner_le_norm x p
  have hm := mul_le_mul (hbound x hx) hp' (norm_nonneg _) hB
  have hr : 0 < B+1 := by linarith
  have hb : B*(B+1)⁻¹ ≤ 1 := (div_le_one hr).mpr (by linarith)
  exact hi.trans (hm.trans hb)

end
end ConvexPolar

namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u76} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κ : Type u77}

theorem pairing_le_of_net {P : Set E} {b : κ → E} {δ M : ℝ}
    (hnet : ∀ p ∈ P, ∃ j, ‖p-b j‖ ≤ δ) {x : E}
    (hx : ∀ j, inner (𝕜 := ℝ) (b j) x ≤ M) {p : E} (hp : p ∈ P) :
    inner (𝕜 := ℝ) p x ≤ M+δ*‖x‖ := by
  obtain ⟨j, hj⟩ := hnet p hp
  have hh := real_inner_le_norm (p-b j) x
  rw [inner_sub_left] at hh
  have hm := mul_le_mul_of_nonneg_right hj (norm_nonneg x)
  linarith [hx j]

theorem net_norm_bound {P : Set E} {b : κ → E} {δ M r : ℝ}
    (hr : 0 ≤ r) (hM : 0 ≤ M) (hball : Metric.closedBall (0 : E) r ⊆ P)
    (hnet : ∀ p ∈ P, ∃ j, ‖p-b j‖ ≤ δ) {x : E}
    (hx : ∀ j, inner (𝕜 := ℝ) (b j) x ≤ M) : (r-δ)*‖x‖ ≤ M := by
  by_cases hx0 : x = 0
  · simpa [hx0] using hM
  have hp : (r/‖x‖) • x ∈ P := hball (by simpa using (norm_smul_normalized hx0 hr).le)
  have hh := pairing_le_of_net hnet hx hp
  rw [normalized_inner hx0] at hh
  nlinarith

theorem finite_polar_approximation [FiniteDimensional ℝ E] {K : Set E}
    (hc : IsCompact K) (hK : Convex ℝ K) (hi : (interior K).Nonempty)
    (hs : ∀ x, x ∈ K ↔ -x ∈ K) {α : ℝ} (hα : 0 < α) :
    ∃ t : Finset E,
      Function.Injective (fun x : E => fun j : t => inner (𝕜 := ℝ) (j : E) x) ∧
      K ⊆ stripBody (fun j : t => (j : E)) ∧
      (∀ x ∈ stripBody (fun j : t => (j : E)), (1+α)⁻¹ • x ∈ K) ∧
      polar (stripBody (fun j : t => (j : E))) ⊆ polar K := by
  classical
  have h0 := zero_mem_interior_of_symmetric hK hi hs
  obtain ⟨B, hB, hbound⟩ := hc.isBounded.exists_pos_norm_le
  let r := (B+1)⁻¹
  have hr : 0 < r := inv_pos.mpr (by linarith)
  let δ := α*r/(1+α)
  have hlam : 0 < 1+α := by linarith
  have hδ : 0 < δ := div_pos (mul_pos hα hr) hlam
  have hrδ : 0 < r-δ := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ hlam).mpr
    nlinarith
  have hδeq : δ = α*(r-δ) := by dsimp [δ]; field_simp; ring
  have hball : Metric.closedBall (0 : E) r ⊆ polar K :=
    closedBall_subset_polar_of_norm_bound hB.le hbound
  obtain ⟨t, htK, ht, hcover⟩ := (isCompact_polar h0).finite_cover_balls hδ
  let b : ht.toFinset → E := fun j => j
  have hb (j : ht.toFinset) : b j ∈ polar K := htK (by simpa only [b, Set.Finite.mem_toFinset] using j.2)
  have hnet (p : E) (hp : p ∈ polar K) : ∃ j : ht.toFinset, ‖p-b j‖ ≤ δ := by
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcover hp)
    obtain ⟨hqmem, hdist⟩ := mem_iUnion.mp hq
    refine ⟨⟨q, by simpa using hqmem⟩, ?_⟩
    simpa only [dist_eq_norm, b] using (Metric.mem_ball.mp hdist).le
  have hKK' : K ⊆ stripBody b := by
    intro x hx j
    exact polar_abs_pairing hs (hb j) hx
  have hspans : Function.Injective (fun x : E => fun j => inner (𝕜 := ℝ) (b j) x) := by
    intro x y hxy
    have hz (j) : inner (𝕜 := ℝ) (b j) (x-y) ≤ 0 := by
      rw [inner_sub_right]
      have hh : inner (𝕜 := ℝ) (b j) x = inner (𝕜 := ℝ) (b j) y := congrFun hxy j
      rw [hh, sub_self]
    have hh := net_norm_bound hr.le le_rfl hball hnet hz
    have he : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp he)
  refine ⟨ht.toFinset, hspans, hKK', ?_, polar_antitone hKK'⟩
  intro x hx
  apply (mem_polar_polar_iff hK hc.isClosed (interior_subset h0) _).mp
  have hx' (j) : inner (𝕜 := ℝ) (b j) x ≤ 1 := (le_abs_self _).trans (hx j)
  have hh := net_norm_bound hr.le (by norm_num : (0 : ℝ) ≤ 1) hball hnet hx'
  have hd : δ*‖x‖ ≤ α := by nlinarith
  intro p hp
  rw [real_inner_smul_right, ← div_eq_inv_mul]
  apply (div_le_one hlam).mpr
  have hh' := pairing_le_of_net hnet hx' hp
  linarith

end
end ConvexPolar

namespace SymmetricPolar
open Set Filter
open scoped Topology ContDiff Pointwise
noncomputable section
variable {n : ℕ}

theorem symmetric_polar_embedding {K : Set (Position n)} (hK : IsSymmetricConvexBody K)
    {c : ℝ} (hc : 0 < c) (hc4 : c < 4) :
    HasSymplecticEmbedding (capacityBall n c) (polarProduct K) := by
  obtain ⟨α, hα, hαc⟩ := exists_positive_slack hc hc4
  let lam := 1+α
  have hlam : 0 < lam := by dsimp [lam]; linarith
  rcases hK with ⟨hcompact, hconvex, hinterior, hsymm⟩
  obtain ⟨t, htinj, hKK', hK'K, hpolar⟩ :=
    ConvexPolar.finite_polar_approximation hcompact hconvex hinterior hsymm hα
  let b : t → Position n := fun j => j
  have hsubset : ConvexPolar.stripBody b ⊆ lam • K := by
    intro x hx
    refine ⟨lam⁻¹ • x, hK'K x hx, ?_⟩
    change lam • (lam⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
  have hposition {q : Position n} (hq : q ∈ interior (ConvexPolar.stripBody b)) :
      lam⁻¹ • q ∈ interior K := by
    have hh := interior_mono hsubset hq
    rw [interior_smul₀ hlam.ne'] at hh
    obtain ⟨w, hw, rfl⟩ := hh
    simpa only [smul_smul, inv_mul_cancel₀ hlam.ne', one_smul] using hw
  obtain ⟨e, he, hi, hm, hω⟩ := finite_strips_embedding b htinj (mul_pos hlam hc) hαc
  apply embedding_of_scaled_ball_map hlam (a := lam⁻¹) (b := 1) (by simp) he
    (HasSymplecticEmbedding.injOn hi) ?_ hω
  intro z hz
  obtain ⟨hq, hp⟩ := hm hz
  change lam⁻¹ • (e z).1 ∈ interior K ∧ (1 : ℝ) • (e z).2 ∈ interior (polar K)
  refine ⟨hposition hq, ?_⟩
  change (1 : ℝ) • (e z).2 ∈ interior (ConvexPolar.polar K)
  simpa only [one_smul] using interior_mono hpolar hp

end
end SymmetricPolar

end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.LowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real
open Set
open scoped ContDiff ENNReal

namespace SymmetricPolar
open Set
open scoped ENNReal
noncomputable section
variable {n : ℕ}

theorem four_le_gromovWidth_polarProduct {K : Set (Position n)} (hK : IsSymmetricConvexBody K) :
    4 ≤ gromovWidth (polarProduct K) := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro r hr hr4
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr
  have hr4real : (r : ℝ) < 4 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)).mp
    simpa using hr4
  apply le_sSup
  refine ⟨(r : ℝ), ⟨hrreal, symmetric_polar_embedding hK hrreal hr4real⟩, ?_⟩
  simp

end
end SymmetricPolar
end LowerBoundInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.EmbeddingInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u121 u122

section NonsqueezingInline

namespace ComplexSymplectic
noncomputable section
open Set Filter
open scoped ContDiff Topology
open FourierPolynomial
variable {κ : Type u122} [Fintype κ]

 theorem form_ext {v w : Vector κ} (h : ∀ z, form v z = form w z) : v = w := by
   exact smul_right_injective _ Complex.I_ne_zero (ext_inner_right ℝ h)

 theorem injective {A : Vector κ →L[ℝ] Vector κ} (hA : Preserves A) : Function.Injective A := by
   intro v w hvw
   apply form_ext
   intro z
   calc
     form v z = form (A v) (A z) := (hA v z).symm
     _ = form (A w) (A z) := by rw [hvw]
     _ = form w z := hA w z

end
end ComplexSymplectic

end NonsqueezingInline

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.CanonicalCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u128

section
namespace ConvexPolar
open Set Filter
open scoped Topology
noncomputable section
variable {E : Type u128} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_lt_one_of_mem_interior {K : Set E} {p x : E}
    (hp : p ∈ polar K) (hp0 : p ≠ 0) (hx : x ∈ interior K) :
    inner (𝕜 := ℝ) p x < 1 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let t := r/(2*‖p‖)
  have ht : 0 < t := div_pos hr (mul_pos (by norm_num) (norm_pos_iff.mpr hp0))
  have htn : t*‖p‖ = r/2 := by dsimp [t]; field_simp
  have hy : x+t • p ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht, htn]
    exact half_lt_self hr
  have hh := hp _ hy
  rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm] at hh
  have hpos : 0 < t*‖p‖^2 := mul_pos ht (sq_pos_of_pos (norm_pos_iff.mpr hp0))
  linarith

theorem abs_inner_lt_one_of_mem_interior {K : Set E}
    (hs : ∀ x, x ∈ K ↔ -x ∈ K) {p x : E}
    (hp : p ∈ polar K) (hp0 : p ≠ 0) (hx : x ∈ interior K) :
    |inner (𝕜 := ℝ) p x| < 1 := by
  have hpneg : -p ∈ polar K := by
    intro q hq
    have hh := hp (-q) ((hs q).mp hq)
    simpa only [inner_neg_left, inner_neg_right] using hh
  have hpos := inner_lt_one_of_mem_interior hp hp0 hx
  have hneg := inner_lt_one_of_mem_interior hpneg (neg_ne_zero.mpr hp0) hx
  rw [inner_neg_left] at hneg
  exact abs_lt.mpr ⟨by linarith, hpos⟩

theorem polar_symmetric {K : Set E} (hs : ∀ x, x ∈ K ↔ -x ∈ K) :
    ∀ p, p ∈ polar K ↔ -p ∈ polar K := by
  have hh : ∀ p ∈ polar K, -p ∈ polar K := by
    intro p hp x hx
    simpa only [inner_neg_left, inner_neg_right] using hp (-x) ((hs x).mp hx)
  intro p
  exact ⟨hh p, fun hp => by simpa using hh (-p) hp⟩

theorem exists_support_pair {K : Set E}
    (hc : IsCompact K) (h0 : (0 : E) ∈ interior K) {v : E} (hv : v ≠ 0) :
    ∃ q ∈ K, ∃ p ∈ polar K, inner (𝕜 := ℝ) p q = 1 := by
  obtain ⟨q, hq, hmax⟩ := hc.exists_isMaxOn ⟨0, interior_subset h0⟩
    (show ContinuousOn (fun x : E => inner (𝕜 := ℝ) v x) K from by fun_prop)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  have hx : (r/(2*‖v‖)) • v ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr (mul_pos (by norm_num) (norm_pos_iff.mpr hv)))]
    have he : r/(2*‖v‖)*‖v‖ = r/2 := by field_simp
    rw [he]
    exact half_lt_self hr
  have hspos : 0 < inner (𝕜 := ℝ) v q := by
    have hh : inner (𝕜 := ℝ) v ((r/(2*‖v‖)) • v) ≤ inner (𝕜 := ℝ) v q := hmax hx
    have he : inner (𝕜 := ℝ) v ((r/(2*‖v‖)) • v) = r/2*‖v‖ := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [he] at hh
    exact (mul_pos (half_pos hr) (norm_pos_iff.mpr hv)).trans_le hh
  refine ⟨q, hq, (inner (𝕜 := ℝ) v q)⁻¹ • v, ?_, ?_⟩
  · intro x hx
    rw [real_inner_smul_right, show inner (𝕜 := ℝ) x v = inner (𝕜 := ℝ) v x from real_inner_comm _ _, ← div_eq_inv_mul]
    exact (div_le_one hspos).mpr (hmax hx)
  · rw [real_inner_smul_left, inv_mul_cancel₀ hspos.ne']

end
end ConvexPolar

namespace SymmetricPolar
open Set
noncomputable section
variable {n : ℕ}

theorem polarProduct_subset_squareCylinder {K : Set (Position n)}
    (hK : IsSymmetricConvexBody K) {q₀ p₀ : Position n}
    (hq : q₀ ∈ K) (hp : p₀ ∈ polar K) (hqp : inner (𝕜 := ℝ) p₀ q₀ = 1) :
    polarProduct K ⊆ canonicalSquareCylinder q₀ p₀ := by
  have hp0 : p₀ ≠ 0 := by intro he; simp [he] at hqp
  have hq0 : q₀ ≠ 0 := by intro he; simp [he] at hqp
  intro z hz
  have hqp' : q₀ ∈ ConvexPolar.polar (ConvexPolar.polar K) := by
    intro p hp
    rw [real_inner_comm]
    exact hp _ hq
  exact ⟨ConvexPolar.abs_inner_lt_one_of_mem_interior hK.2.2.2 hp hp0 hz.1,
    ConvexPolar.abs_inner_lt_one_of_mem_interior (ConvexPolar.polar_symmetric hK.2.2.2) hqp' hq0 hz.2⟩

theorem exists_squareCylinder {K : Set (Position n)} (hK : IsSymmetricConvexBody K)
    (hn : 0 < n) : ∃ q₀ p₀ : Position n, inner (𝕜 := ℝ) p₀ q₀ = 1 ∧
      polarProduct K ⊆ canonicalSquareCylinder q₀ p₀ := by
  let v : Position n := (EuclideanSpace.basisFun (Fin n) ℝ) ⟨0, hn⟩
  have hv : v ≠ 0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ne_zero _
  obtain ⟨q₀, hq, p₀, hp, hqp⟩ := ConvexPolar.exists_support_pair hK.1
    (ConvexPolar.zero_mem_interior_of_symmetric hK.2.1 hK.2.2.1 hK.2.2.2) hv
  exact ⟨q₀, p₀, hqp, polarProduct_subset_squareCylinder hK hq hp hqp⟩

end
end SymmetricPolar
end

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.PlanarSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u129 u130

section
namespace PlanarSquare
noncomputable section
open Set Filter
open scoped ContDiff Topology

theorem radius_pos {z : ℂ} (hz : -1 < z.im) : 0 < radius z := by
  apply Real.sqrt_pos.2
  exact div_pos (by linarith) Real.pi_pos

theorem radius_sq {z : ℂ} (hz : -1 < z.im) : radius z ^ 2 = 2*(z.im+1)/Real.pi :=
  Real.sq_sqrt (div_nonneg (by linarith) Real.pi_pos.le)

theorem norm_map_sq {z : ℂ} (hz : -1 < z.im) : ‖map z‖^2 = 2*(z.im+1)/Real.pi := by
  rw [map, norm_mul, norm_rotation, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, radius_sq hz]

theorem map_bound {z : ℂ} (hz : z ∈ square) : ‖map z‖^2 < 4/Real.pi := by
  rw [norm_map_sq (abs_lt.mp hz.2).1]
  exact (div_lt_div_iff_of_pos_right Real.pi_pos).2 (by linarith [(abs_lt.mp hz.2).2])

theorem map_injOn : InjOn map square := by
  intro z hz w hw hzw
  have him : z.im = w.im := by
    have hh := congrArg (fun t : ℂ => ‖t‖^2) hzw
    rw [norm_map_sq (abs_lt.mp hz.2).1, norm_map_sq (abs_lt.mp hw.2).1] at hh
    have := (div_left_inj' Real.pi_ne_zero).mp hh
    linarith
  have hrad : radius z = radius w := by simp only [radius, him]
  have hrot : rotation z = rotation w := by
    change (radius z : ℂ)*rotation z = (radius w : ℂ)*rotation w at hzw
    rw [← hrad] at hzw
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (radius_pos (abs_lt.mp hz.2).1).ne') hzw
  have hab (x : ℂ) (hx : x ∈ square) : -Real.pi < (angle x).im ∧ (angle x).im ≤ Real.pi := by
    rw [angle_im]
    have ht := mul_lt_mul_of_pos_left (abs_lt.mp hx.1).2 Real.pi_pos
    have hb := mul_lt_mul_of_pos_left (abs_lt.mp hx.1).1 Real.pi_pos
    constructor <;> linarith
  have hangle := Complex.exp_inj_of_neg_pi_lt_of_le_pi (hab z hz).1 (hab z hz).2
    (hab w hw).1 (hab w hw).2 hrot
  have hre : z.re = w.re := by
    have hh := congrArg Complex.im hangle
    simp only [angle_im] at hh
    nlinarith [Real.pi_pos]
  exact Complex.ext hre him

theorem contDiffAt_map {z : ℂ} (hz : -1 < z.im) : ContDiffAt ℝ ∞ map z := by
  have hrad : ContDiffAt ℝ ∞ radius z := by
    apply ContDiffAt.sqrt
    · exact (contDiffAt_const.mul (Complex.imCLM.contDiff.contDiffAt.add contDiffAt_const)).div_const Real.pi
    · exact ne_of_gt (div_pos (by linarith) Real.pi_pos)
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hrad).mul (angle.contDiff.contDiffAt.cexp)

theorem hasFDerivAt_radius {z : ℂ} (hz : -1 < z.im) :
    HasFDerivAt radius ((1/(Real.pi*radius z)) • Complex.imCLM) z := by
  have hbase : HasFDerivAt (fun w : ℂ => 2*(w.im+1)/Real.pi)
      ((2/Real.pi) • Complex.imCLM) z := by
    have hf : (fun w : ℂ => 2*(w.im+1)/Real.pi) =
        (fun w : ℂ => (2/Real.pi)*(Complex.imCLM w+1)) := by funext w; simp only [Complex.imCLM_apply]; ring
    rw [hf]
    exact (Complex.imCLM.hasFDerivAt.add_const 1).const_mul (2/Real.pi)
  have hs := hbase.sqrt (ne_of_gt (div_pos (by linarith) Real.pi_pos))
  rw [smul_smul] at hs
  change HasFDerivAt radius (((1/(2*radius z))*(2/Real.pi)) • Complex.imCLM) z at hs
  have hcoef : (1/(2*radius z))*(2/Real.pi) = 1/(Real.pi*radius z) := by
    field_simp
  rwa [hcoef] at hs

theorem hasFDerivAt_map {z : ℂ} (hz : -1 < z.im) : HasFDerivAt map (derivative z) z := by
  exact ((Complex.ofRealCLM.hasFDerivAt.comp z (hasFDerivAt_radius hz)).mul
    angle.hasFDerivAt.cexp)

theorem derivative_apply (z v : ℂ) :
    derivative z v = rotation z * (((v.im/(Real.pi*radius z) : ℝ) : ℂ) -
      Complex.I * ((Real.pi*radius z*v.re : ℝ) : ℂ)) := by
  simp [derivative, angle, Complex.real_smul, smul_eq_mul, div_eq_mul_inv]
  ring

theorem form_mul (a v w : ℂ) : form (a*v) (a*w) = ‖a‖^2*form v w := by
  simp only [form, Complex.mul_re, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem derivative_preserves {z : ℂ} (hz : -1 < z.im) (v w : ℂ) :
    form (derivative z v) (derivative z w) = form v w := by
  simp only [derivative_apply, form_mul, norm_rotation, one_pow, one_mul]
  simp only [form, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hr := (radius_pos hz).ne'
  field_simp
  ring

end
end PlanarSquare
end

section
namespace PlanarCylinder
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {κ : Type u129} [Fintype κ] [DecidableEq κ]

omit [Fintype κ] in
theorem map_injOn (j₀ : κ) : InjOn (map j₀) (domain j₀) := by
  intro z hz w hw hzw
  ext j
  have hh := congrArg (fun v : V κ => v j) hzw
  by_cases hj : j = j₀
  · subst j
    apply PlanarSquare.map_injOn hz hw
    simpa only [map_first] using hh
  · simpa only [map_apply, ite_eq_right hj] using hh

theorem hasFDerivAt_map (j₀ : κ) {z : V κ} (hz : -1 < (z j₀).im) :
    HasFDerivAt (map j₀) (derivative j₀ z) z := by
  apply (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp
  apply hasFDerivAt_pi.mpr
  intro j
  by_cases hj : j = j₀
  · subst j
    simp only [ite_true]
    exact (PlanarSquare.hasFDerivAt_map hz).comp z (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z j₀)
  · simp only [ite_eq_right hj]
    exact PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z j

theorem contDiffAt_map (j₀ : κ) {z : V κ} (hz : -1 < (z j₀).im) :
    ContDiffAt ℝ ∞ (map j₀) z := by
  apply (contDiffAt_piLp 2).mpr
  intro j
  by_cases hj : j = j₀
  · subst j
    simp only [map_first]
    exact (PlanarSquare.contDiffAt_map hz).comp z
      (show ContDiffAt ℝ ∞ (fun w : V κ => w j₀) z from contDiffAt_piLp_apply 2)
  · simp only [map_apply, ite_eq_right hj]
    exact contDiffAt_piLp_apply 2

omit [DecidableEq κ] in
theorem form_eq_inner (v w : V κ) : form v w = inner (𝕜 := ℝ) (Complex.I • v) w := by
  simp only [form, PiLp.inner_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_eq_re_inner, RCLike.inner_apply']
  change PlanarSquare.form (v j) (w j) = ((starRingEnd ℂ) (Complex.I * v j) * w j).re
  simp only [PlanarSquare.form, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem derivative_preserves (j₀ : κ) {z : V κ} (hz : -1 < (z j₀).im) (v w : V κ) :
    form (derivative j₀ z v) (derivative j₀ z w) = form v w := by
  unfold form
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = j₀
  · subst j
    simp only [derivative_apply, ite_true]
    exact PlanarSquare.derivative_preserves hz _ _
  · simp only [derivative_apply, ite_eq_right hj]

omit [Fintype κ] in
theorem first_bound (j₀ : κ) {z : V κ} (hz : z ∈ domain j₀) :
    ‖map j₀ z j₀‖^2 < 4/Real.pi := by
  rw [map_first]
  exact PlanarSquare.map_bound hz

theorem norm_bound (j₀ : κ) {z : V κ} (hz : z ∈ domain j₀) :
    ‖map j₀ z‖^2 ≤ ‖z‖^2 + 4/Real.pi := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ j, (‖z j‖^2 + if j = j₀ then 4/Real.pi else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = j₀
      · subst j
        simp only [ite_true]
        exact (first_bound j₀ hz).le.trans (le_add_of_nonneg_left (sq_nonneg _))
      · simp [map_apply, ite_eq_right hj]
    _ = _ := by simp [Finset.sum_add_distrib]

end
end PlanarCylinder
end

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.CanonicalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u131 u132 u133

section
namespace CanonicalLinear
noncomputable section
open scoped InnerProductSpace
variable {κ : Type u131} [Fintype κ] [DecidableEq κ]

theorem adaptedMap_u {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) : adaptedMap u v j u = EuclideanSpace.single j 1 := by
  simp [adaptedMap_apply, div_self huj, hvu]

theorem adapted_first {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) (q : E κ) :
    adapted j huj hvu q j = inner (𝕜 := ℝ) v q := adaptedMap_coordinate u v q j huj

theorem adapted_inverse_single {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) :
    (adapted j huj hvu).symm (EuclideanSpace.single j 1) = u := by
  apply (adapted j huj hvu).injective
  simpa only [ContinuousLinearEquiv.apply_symm_apply, adapted_apply] using (adaptedMap_u j huj hvu).symm

omit [DecidableEq κ] in
theorem cotangent_preserves (A : E κ ≃L[ℝ] E κ) (x y : E κ × E κ) :
    inner (𝕜 := ℝ) (cotangent A x).1 (cotangent A y).2 -
      inner (𝕜 := ℝ) (cotangent A y).1 (cotangent A x).2 =
    inner (𝕜 := ℝ) x.1 y.2 - inner (𝕜 := ℝ) y.1 x.2 := by
  simp only [cotangent_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

omit [DecidableEq κ] in
theorem cotangent_injective (A : E κ ≃L[ℝ] E κ) : Function.Injective (cotangent A) := by
  intro x y hxy
  apply Prod.ext
  · exact A.injective (congrArg Prod.fst hxy)
  · apply ext_inner_left ℝ
    intro z
    obtain ⟨w,rfl⟩ := A.symm.surjective z
    have hh := congrArg (fun t : E κ × E κ => inner (𝕜 := ℝ) w t.2) hxy
    simpa only [cotangent_apply, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearEquiv.coe_coe] using hh

theorem cotangent_first {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) (x : E κ × E κ) :
    (cotangent (adapted j huj hvu) x).1 j = inner (𝕜 := ℝ) v x.1 ∧
    (cotangent (adapted j huj hvu) x).2 j = inner (𝕜 := ℝ) u x.2 := by
  constructor
  · exact adapted_first j huj hvu x.1
  · calc
      _ = inner (𝕜 := ℝ) (EuclideanSpace.single j 1) (cotangent (adapted j huj hvu) x).2 := by simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
      _ = _ := by
        simp only [cotangent_apply, ContinuousLinearMap.adjoint_inner_right,
          ContinuousLinearEquiv.coe_coe, adapted_inverse_single]

end
end CanonicalLinear
end

section
namespace UpperCoordinates
noncomputable section
open Set
open scoped ContDiff
variable {κ : Type u133} [Fintype κ] [DecidableEq κ]
open ComplexCoordinates CanonicalLinear

omit [DecidableEq κ] in
theorem form_parts (v w : C κ) : PlanarCylinder.form v w = phaseForm (parts v) (parts w) := by
  simp only [PlanarCylinder.form, PlanarSquare.form, phaseForm, parts_apply, PiLp.inner_apply,
    re_apply, im_apply, RCLike.inner_apply', RCLike.conj_to_real, ← Finset.sum_sub_distrib]

omit [DecidableEq κ] in
theorem form_parts_symm (x y : R κ × R κ) :
    PlanarCylinder.form (parts.symm x) (parts.symm y) = phaseForm x y := by
  rw [form_parts, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

omit [DecidableEq κ] in
theorem targetCoordinates_preserves (A : E κ ≃L[ℝ] E κ) (x y : E κ × E κ) :
    PlanarCylinder.form (targetCoordinates A x) (targetCoordinates A y) = phaseForm x y := by
  change PlanarCylinder.form (parts.symm (cotangent A x)) (parts.symm (cotangent A y)) = _
  rw [form_parts_symm]
  exact cotangent_preserves A x y

omit [DecidableEq κ] in
theorem targetCoordinates_injective (A : E κ ≃L[ℝ] E κ) :
    Function.Injective (targetCoordinates A) :=
  parts.symm.injective.comp (cotangent_injective A)

theorem targetCoordinates_first {u v : E κ} (j : κ) (huj : u j ≠ 0)
    (hvu : inner (𝕜 := ℝ) v u = 1) (x : E κ × E κ) :
    (targetCoordinates (adapted j huj hvu) x j).re = inner (𝕜 := ℝ) v x.1 ∧
    (targetCoordinates (adapted j huj hvu) x j).im = inner (𝕜 := ℝ) u x.2 := by
  have hh := cotangent_first j huj hvu x
  have hp := parts.apply_symm_apply (cotangent (adapted j huj hvu) x)
  have hre : re (parts.symm (cotangent (adapted j huj hvu) x)) = (cotangent (adapted j huj hvu) x).1 :=
    congrArg Prod.fst hp
  have him : im (parts.symm (cotangent (adapted j huj hvu) x)) = (cotangent (adapted j huj hvu) x).2 :=
    congrArg Prod.snd hp
  change re (parts.symm (cotangent (adapted j huj hvu) x)) j = _ ∧
    im (parts.symm (cotangent (adapted j huj hvu) x)) j = _
  rw [hre, him]
  exact hh

end
end UpperCoordinates
end

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.UpperBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SymmetricPolar
noncomputable section
open Set Filter
open scoped ContDiff Topology ENNReal
open ComplexCoordinates UpperCoordinates
variable {n : ℕ}

theorem capacity_le_four_of_embedding {K : Set (Position n)} (hK : IsSymmetricConvexBody K)
    (hn : 0 < n) {c : ℝ} (hc : 0 < c)
    (hemb : HasSymplecticEmbedding (capacityBall n c) (polarProduct K)) : c ≤ 4 := by
  obtain ⟨u,v,hvu,hcyl⟩ := exists_squareCylinder hK hn
  have hu : u ≠ 0 := by intro h; simp [h] at hvu
  obtain ⟨j,huj⟩ : ∃ j : Fin n, u j ≠ 0 := by
    by_contra h
    apply hu
    ext j
    exact not_not.mp ((not_exists.mp h) j)
  let A := CanonicalLinear.adapted j huj hvu
  let T := targetCoordinates A
  obtain ⟨e,he,hei,heK,heω⟩ := hemb
  let f : C (Fin n) → C (Fin n) := fun z => PlanarCylinder.map j (T (e (parts z)))
  have hball {z : C (Fin n)} (hz : z ∈ PushedBall.domain (c/Real.pi)) :
      parts z ∈ capacityBall n c := by
    change Real.pi*(‖re z‖^2+‖im z‖^2) < c
    rw [← norm_sq_parts]
    exact (lt_div_iff₀ Real.pi_pos).mp hz |> fun h => by simpa [mul_comm] using h
  have hfirst (z : C (Fin n)) (hz : z ∈ PushedBall.domain (c/Real.pi)) :
      T (e (parts z)) ∈ PlanarCylinder.domain j := by
    have hh := hcyl (heK (hball hz))
    have hi := targetCoordinates_first j huj hvu (e (parts z))
    change |(T (e (parts z)) j).re| < 1 ∧ |(T (e (parts z)) j).im| < 1
    rw [hi.1, hi.2]
    exact hh
  have hsm (z : C (Fin n)) (hz : z ∈ PushedBall.domain (c/Real.pi)) : ContDiffAt ℝ ∞ f z := by
    have hez := he.contDiffAt ((isOpen_lt (by fun_prop) continuous_const).mem_nhds (hball hz))
    have hP : ContDiffAt ℝ ∞ (parts : C (Fin n) → Phase n) z :=
      (parts (ι := Fin n)).contDiff.contDiffAt
    have hT : ContDiffAt ℝ ∞ (fun w => T (e (parts w))) z :=
      T.contDiff.contDiffAt.comp z (hez.comp z hP)
    have hout := (PlanarCylinder.contDiffAt_map j (abs_lt.mp (hfirst z hz).2).1).comp z hT
    exact hout
  have hfi : InjOn f (PushedBall.domain (c/Real.pi)) := by
    intro z hz w hw hzw
    apply parts.injective
    apply HasSymplecticEmbedding.injOn hei (hball hz) (hball hw)
    apply targetCoordinates_injective A
    exact PlanarCylinder.map_injOn j (hfirst z hz) (hfirst w hw) hzw
  have hfω (z : C (Fin n)) (hz : z ∈ PushedBall.domain (c/Real.pi)) :
      ComplexSymplectic.Preserves (fderiv ℝ f z) := by
    have hez := he.contDiffAt ((isOpen_lt (by fun_prop) continuous_const).mem_nhds (hball hz))
    have hed := (hez.differentiableAt (by simp)).hasFDerivAt
    have hd := (PlanarCylinder.hasFDerivAt_map j (abs_lt.mp (hfirst z hz).2).1).comp z
      (T.hasFDerivAt.comp z (hed.comp z (parts (ι := Fin n)).hasFDerivAt))
    have hfd : fderiv ℝ f z = (PlanarCylinder.derivative j (T (e (parts z)))).comp
        (T.comp ((fderiv ℝ e (parts z)).comp parts.toContinuousLinearMap)) := hd.fderiv
    intro a b
    change inner (𝕜 := ℝ) (Complex.I • fderiv ℝ f z a) (fderiv ℝ f z b) =
      inner (𝕜 := ℝ) (Complex.I • a) b
    rw [← PlanarCylinder.form_eq_inner, ← PlanarCylinder.form_eq_inner, hfd]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [PlanarCylinder.derivative_preserves j (abs_lt.mp (hfirst z hz).2).1,
      targetCoordinates_preserves, form_parts]
    exact heω _ (hball hz) (parts a) (parts b)
  have hpK : IsCompact (polar K) := ConvexPolar.isCompact_polar
    (ConvexPolar.zero_mem_interior_of_symmetric hK.2.1 hK.2.2.1 hK.2.2.2)
  obtain ⟨B,hB,hTB⟩ := ((hK.1.prod hpK).image T.continuous).isBounded.exists_pos_norm_le
  have hbnd (z : C (Fin n)) (hz : z ∈ PushedBall.domain (c/Real.pi)) :
      ‖f z‖^2 ≤ B^2 + 4/Real.pi := by
    have hh := heK (hball hz)
    have hT := hTB _ ⟨e (parts z), ⟨interior_subset hh.1,interior_subset hh.2⟩, rfl⟩
    have hsq := (sq_le_sq₀ (norm_nonneg _) hB.le).mpr hT
    have hnorm := PlanarCylinder.norm_bound j (hfirst z hz)
    change ‖PlanarCylinder.map j (T (e (parts z)))‖^2 ≤ _
    linarith
  have hle := CylinderNonsqueezing.radius_le_of_map j (div_pos hc Real.pi_pos)
    (by positivity : (0:ℝ) ≤ 4/Real.pi) (by positivity : (0:ℝ) ≤ B^2+4/Real.pi)
    f (fun z hz => (hsm z hz).contDiffWithinAt) hfi hfω hbnd
    (fun z hz => (PlanarCylinder.first_bound j (hfirst z hz)).le)
  exact (div_le_div_iff_of_pos_right Real.pi_pos).mp hle

theorem gromovWidth_polarProduct_le_four {K : Set (Position n)}
    (hK : IsSymmetricConvexBody K) (hn : 0 < n) : gromovWidth (polarProduct K) ≤ 4 := by
  apply sSup_le
  rintro _ ⟨c,⟨hc,he⟩,rfl⟩
  exact (ENNReal.ofReal_le_ofReal (capacity_le_four_of_embedding hK hn hc he)).trans_eq (by norm_num)

end
end SymmetricPolar
end

end OAI
end

section
-- module Solutions.OAIQW_SymmetricPolar.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricPolar

theorem symmetric_polar_main_oai {n : ℕ} (hn : 2 ≤ n)
    (K : Set (Position n)) (hK : IsSymmetricConvexBody K) :
    gromovWidth (polarProduct K) = 4 ∧
      ∀ c : ℝ, 0 < c → c < 4 →
        HasSymplecticEmbedding (capacityBall n c) (polarProduct K) := by
  refine ⟨le_antisymm (gromovWidth_polarProduct_le_four hK (by omega))
    (four_le_gromovWidth_polarProduct hK), ?_⟩
  intro c hc hc4
  exact symmetric_polar_embedding hK hc hc4

end SymmetricPolar

end OAI
end

theorem solution : type_of% @OAI.SymmetricPolar.symmetric_polar_main_oai := @OAI.SymmetricPolar.symmetric_polar_main_oai
