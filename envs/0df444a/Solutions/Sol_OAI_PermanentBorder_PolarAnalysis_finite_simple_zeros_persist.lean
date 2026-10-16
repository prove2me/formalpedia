-- Prove2me | solution 1 for OAI.PermanentBorder.PolarAnalysis.finite_simple_zeros_persist
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:34:32.061681+00:00
-- url     : https://prove2.me/submissions/731bba48-faa3-4efb-9a2f-56da44bd6ec4

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/PointBounds.lean:L290-L315
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.PolarAnalysis.finite_simple_zeros_persist. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds

-- ---- from OAI.Algebra.Determinantal.PointBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
section AffineCokernel
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K W]

end AffineCokernel
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section GenericPieceBound
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]

end GenericPieceBound

section ProductComparison
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

end ProductComparison
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section BlockInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]
variable (group : σ → ι) (base : ι → σ) (hbase : ∀ j, group (base j) = j)

variable [Fintype L] [DecidableEq L]

end BlockInterpolation
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section NormalizedPointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

end NormalizedPointBound
end PermanentBorder.Multigraded

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Persistence
variable {C V : Type*}
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem isInvertible_iff_isUnit (T : V →L[ℂ] V) : T.IsInvertible ↔ IsUnit T := by
  constructor
  · intro h
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr h.bijective
  · intro h
    obtain ⟨U,hU⟩ := h
    exact ⟨ContinuousLinearEquiv.ofUnit U, hU⟩

omit [CompleteSpace C] in

theorem isOpen_simple {F : C × V → V} (hF : ContDiff ℂ 1 F) :
    IsOpen {u : C × V | SimpleAt F u.1 u.2} := by
  have hc : Continuous (fun u : C × V =>
      fderiv ℂ F u ∘L ContinuousLinearMap.inr ℂ C V) := by
    exact (hF.continuous_fderiv (by decide)).clm_comp continuous_const
  simpa only [SimpleAt, Prod.mk.eta, isInvertible_iff_isUnit, Set.preimage_ofPred_eq] using
    Units.isOpen.preimage hc

theorem simple_branch {F : C × V → V} (hF : ContDiff ℂ 1 F)
    {c : C} {x : V} (hz : F (c,x) = 0) (hs : SimpleAt F c x) :
    ∃ ψ : C → V, Tendsto ψ (𝓝 c) (𝓝 x) ∧
      ∀ᶠ c' in 𝓝 c, F (c', ψ c') = 0 ∧ SimpleAt F c' (ψ c') := by
  let hf := hF.contDiffAt (x := (c,x))
  let ψ := hf.implicitFunction (by decide) hs
  have ht : Tendsto ψ (𝓝 c) (𝓝 x) :=
    hf.hasStrictFDerivAt (by decide) |>.tendsto_implicitFunctionOfProdDomain hs
  refine ⟨ψ,ht,?_⟩
  have hz' := hf.eventually_apply_implicitFunction (by decide) hs
  have hne := (tendsto_id.prodMk_nhds ht).eventually ((isOpen_simple hF).mem_nhds hs)
  filter_upwards [hz', hne] with c' hc' hs'
  exact ⟨hc'.trans hz, hs'⟩

theorem finite_simple_zeros_persist {ι : Type*} [Fintype ι]
    {F : C × V → V} (hF : ContDiff ℂ 1 F) {c : C}
    (x : ι → V) (hx : Function.Injective x)
    (hz : ∀ i, F (c,x i) = 0) (hs : ∀ i, SimpleAt F c (x i)) :
    ∀ᶠ c' in 𝓝 c, ∃ y : ι → V, Function.Injective y ∧
      ∀ i, F (c',y i) = 0 ∧ SimpleAt F c' (y i) := by
  classical
  choose ψ ht hψ using fun i => simple_branch hF (hz i) (hs i)
  have hall : ∀ᶠ c' in 𝓝 c, ∀ i, F (c',ψ i c') = 0 ∧ SimpleAt F c' (ψ i c') :=
    Filter.eventually_all.mpr hψ
  have hsep : ∀ᶠ c' in 𝓝 c, Function.Injective (fun i => ψ i c') := by
    have hp : ∀ i j : ι, ∀ᶠ c' in 𝓝 c, i ≠ j → ψ i c' ≠ ψ j c' := by
      intro i j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall (by simp [hij])
      · have hh : (x i, x j) ∈ {p : V × V | p.1 ≠ p.2} := by
          exact fun h => hij (hx h)
        have ho : IsOpen {p : V × V | p.1 ≠ p.2} := isOpen_compl_iff.mpr (isClosed_eq continuous_fst continuous_snd)
        have he := ((ht i).prodMk_nhds (ht j)).eventually (ho.mem_nhds hh)
        exact he.mono fun _ h _ => h
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hp i))] with c' hc'
    intro i j he
    by_contra hij
    exact hc' i j hij he
  filter_upwards [hall,hsep] with c' hc' hi
  exact ⟨fun i => ψ i c',hi,hc'⟩
end Persistence
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open MvPolynomial
variable {τ : Type*} [Fintype τ]
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section ProductSimplePointBound
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

end ProductSimplePointBound
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.PolarAnalysis
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.PolarAnalysis.finite_simple_zeros_persist := @_root_.OAI.PermanentBorder.PolarAnalysis.finite_simple_zeros_persist
