-- Prove2me | solution 1 for OAI.PermanentBorder.CI.normalized_count_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:08:52.385634+00:00
-- url     : https://prove2.me/submissions/50f3df55-8bb6-4c06-8706-87569ec2e553

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/SmoothSlices.lean:L158-L177
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.CI.normalized_count_constant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Theorems.Thm_OAI_PermanentBorder_CI_good_derivative_invertible
import Theorems.Thm_OAI_PermanentBorder_Polar_homogeneous_normalized_proper
import Theorems.Thm_OAI_PermanentBorder_Polar_proper_localHomeomorph_card

-- ---- from OAI.Algebra.Determinantal.RegularSections ----
namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

end
end PermanentBorder.CI

namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

theorem zero_projection_chart {X F P : Type*} [TopologicalSpace X]
    [TopologicalSpace F] [TopologicalSpace P] [Zero F]
    (f : X → F) (p : X → P) (x : {x : X // f x = 0})
    (e : OpenPartialHomeomorph X (F × P)) (hx : x.val ∈ e.source)
    (he : ∀ z, e z = (f z,p z)) :
    ∃ U ∈ 𝓝 x, IsOpenEmbedding (U.domRestrict (fun z : {x : X // f x = 0} => p z)) := by
  let U : Set {x : X // f x = 0} := Subtype.val ⁻¹' e.source
  let A : Set (F × P) := {v | v.1 = 0}
  let h : U ≃ₜ ((e.source.domRestrict e) ⁻¹' A) :=
    { toFun := fun z => ⟨⟨z.val.val,z.property⟩,by simpa [A, he] using z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val,by simpa [A, he] using z.property⟩,z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let g : A ≃ₜ P :=
    { toFun := fun v => v.val.2
      invFun := fun b => ⟨(0,b),rfl⟩
      left_inv := fun v => by apply Subtype.ext; exact Prod.ext v.property.symm rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨U, (e.open_source.preimage continuous_subtype_val).mem_nhds hx, ?_⟩
  have H := g.isOpenEmbedding.comp ((e.isOpenEmbedding_restrict.restrictPreimage A).comp
    h.isOpenEmbedding)
  convert H using 1
  funext z
  exact (congrArg Prod.snd (he z.val.val)).symm

end PermanentBorder.Polar
namespace PermanentBorder.Polar
open Topology Filter
open scoped Topology

theorem localHomeomorphOn_restrictPreimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (s : Set Y)
    (h : IsLocalHomeomorphOn f (f ⁻¹' s)) :
    IsLocalHomeomorph (s.restrictPreimage f) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U,hU,hE⟩ := (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mp h x.val x.property
  let V : Set (f ⁻¹' s) := Subtype.val ⁻¹' U
  let e : V ≃ₜ ((U.domRestrict f) ⁻¹' s) :=
    { toFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      invFun := fun z => ⟨⟨z.val.val,z.property⟩,z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine ⟨V, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
  exact (hE.restrictPreimage s).comp e.isOpenEmbedding

theorem implicit_zero_projection_on {𝕜 P V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
    (f : P × V → V) (s : Set P)
    (h : ∀ x : {x : P × V // f x = 0}, x.val.1 ∈ s → ∃ D : P × V →L[𝕜] V,
      HasStrictFDerivAt f D x.val ∧ (D ∘L ContinuousLinearMap.inr 𝕜 P V).IsInvertible) :
    IsLocalHomeomorph (s.restrictPreimage
      (fun x : {x : P × V // f x = 0} => x.val.1)) := by
  apply localHomeomorphOn_restrictPreimage
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro x hx
  obtain ⟨D,hd,hi⟩ := h x hx
  let φ := hd.implicitFunctionDataOfProdDomain hi
  exact zero_projection_chart f Prod.fst x φ.toOpenPartialHomeomorph
    φ.pt_mem_toOpenPartialHomeomorph_source φ.toOpenPartialHomeomorph_apply

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open Topology Set

end PermanentBorder.Polar

end OAI

-- ---- from OAI.Algebra.Determinantal.SmoothSlices ----
namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

lemma homogeneous_aeval_scale {K L σ : Type*} [CommSemiring K] [CommSemiring L]
    [Algebra K L] {f : MvPolynomial σ K} {r : ℕ} (hf : f.IsHomogeneous r)
    (a : L) (x : σ → L) :
    aeval (fun i => a * x i) f = a^r * aeval x f := by
  classical
  conv_lhs => rw [← f.support_sum_monomial_coeff]
  conv_rhs => rw [← f.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hf.degree_eq_sum_deg_support hs]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end PermanentBorder.SliceParameters

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

lemma normalized_eval_zero_iff (H : ι → MvPolynomial (Option ι) ℂ) (l y : Option ι → ℂ) :
    (fun i => eval y (normalized H l i)) = 0 ↔
      (∀ i, eval y (H i) = 0) ∧ eval y (linear l) = 1 := by
  constructor
  · intro h
    constructor
    · intro i; exact congrFun h (some i)
    · have hh := congrFun h none
      simpa [normalized, sub_eq_zero] using hh
  · rintro ⟨hH,hl⟩
    funext i
    cases i <;> simp [normalized, hH, hl]

lemma fderiv_parameter_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {F : ℂ × V → V} (hF : ContDiff ℂ 1 F) (t : ℂ) (x : V) :
    fderiv ℂ (fun x => F (t,x)) x =
      fderiv ℂ F (t,x) ∘L ContinuousLinearMap.inr ℂ ℂ V := by
  have hi : HasFDerivAt (fun x : V => (t,x)) (ContinuousLinearMap.inr ℂ ℂ V) x := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const (𝕜 := ℂ) t x).prodMk (hasFDerivAt_id (𝕜 := ℂ) x)
  exact ((hF.differentiable (by decide) (t,x)).hasFDerivAt.comp x hi).fderiv

lemma normalized_family_proper (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (e : ι → ℕ)
    (hh : ∀ t i, (H t i).IsHomogeneous (e i))
    (hcH : ∀ i, Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (H z.1 i)))
    (hcL : Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (linear (l z.1))))
    (s : Set ℂ) (hg : ∀ t ∈ s, Good (H t) (l t)) :
    IsProperMap (familyProjection H l s) := by
  let V := Option ι → ℂ
  have hval : Continuous (fun z : s × V => (z.1.val,z.2) : s × V → ℂ × V) := by fun_prop
  have hc (i : ι) : Continuous (fun z : s × V => eval z.2 (H z.1.val i)) :=
    Continuous.comp (f := fun z : s × V => (z.1.val,z.2)) (hcH i) hval
  have hci (i : ι) : IsClosed {z : s × V | eval z.2 (H z.1.val i) = 0} :=
    isClosed_eq (hc i) continuous_const
  have hclosed : IsClosed {z : s × V | ∀ i, eval z.2 (H z.1.val i) = 0} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter hci
  have hL : Continuous (fun z : s × V => linearEval (l z.1.val) z.2) := by
    simp only [linearEval_apply]
    exact Continuous.comp (f := fun z : s × V => (z.1.val,z.2)) hcL hval
  apply PermanentBorder.Polar.homogeneous_normalized_proper
    (T := s) (V := V) (fun t y => ∀ i, eval y (H t.val i) = 0) hclosed
    (L := fun t => linearEval (l t.val)) (hL := hL)
  · intro t y c hy i
    have hs := PermanentBorder.SliceParameters.homogeneous_aeval_scale (hh t.val i) c y
    have he : eval (c • y) (H t.val i) = c ^ e i * eval y (H t.val i) := by
      change eval (fun j => c * y j) (H t.val i) = _
      simpa [aeval_def] using hs
    rw [he, hy i, mul_zero]
  · intro t y hy hz
    by_contra hn
    exact (hg t.val t.property y hn hy).1 hz

lemma normalized_family_local (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ)
    (hc : ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (H z.1) (l z.1) i)))
    (s : Set ℂ) (hg : ∀ t ∈ s, Good (H t) (l t)) :
    IsLocalHomeomorph (familyProjection H l s) := by
  let V := Option ι → ℂ
  let S : ℂ × V → V := fun z i => eval z.2 (normalized (H z.1) (l z.1) i)
  let q : {z : ℂ × V // S z = 0} → ℂ := fun z => z.val.1
  let W := q ⁻¹' s
  let E : FamilyRoots H l s ≃ₜ W :=
    { toFun := fun z => ⟨⟨(z.val.1.val,z.val.2),
        (normalized_eval_zero_iff _ _ _).mpr z.property⟩,z.val.1.property⟩
      invFun := fun z => ⟨(⟨z.val.val.1,z.property⟩,z.val.val.2),
        (normalized_eval_zero_iff _ _ _).mp z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hq : IsLocalHomeomorph (s.restrictPreimage q) := by
    apply PermanentBorder.Polar.implicit_zero_projection_on (𝕜 := ℂ) S s
    intro z hz
    refine ⟨fderiv ℂ S z.val, hc.hasStrictFDerivAt (by decide), ?_⟩
    rw [← fderiv_parameter_slice hc z.val.1 z.val.2]
    exact good_derivative_invertible (H z.val.1) (l z.val.1) z.val.2
      (hg z.val.1 hz) z.property
  exact hq.comp E.isLocalHomeomorph

theorem normalized_count_constant (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (e : ι → ℕ)
    (hh : ∀ t i, (H t i).IsHomogeneous (e i))
    (hc : ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (H z.1) (l z.1) i)))
    (s : Set ℂ) [PreconnectedSpace s] (hg : ∀ t ∈ s, Good (H t) (l t))
    (a b : s) :
    Nat.card (Roots (H a.val) (l a.val)) = Nat.card (Roots (H b.val) (l b.val)) := by
  have hcH (i : ι) : Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (H z.1 i)) :=
    (continuous_apply (some i)).comp hc.continuous
  have hcL : Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (linear (l z.1))) := by
    have hcont : Continuous (fun z : ℂ × (Option ι → ℂ) =>
        eval z.2 (normalized (H z.1) (l z.1) none) + (1 : ℂ)) :=
      ((continuous_apply none).comp hc.continuous).add continuous_const
    convert! hcont using 1
    funext z
    simp [normalized]
  rw [← Nat.card_congr (familyFiberEquiv H l s a), ← Nat.card_congr (familyFiberEquiv H l s b)]
  exact PermanentBorder.Polar.proper_localHomeomorph_card
    (normalized_family_proper H l e hh hcH hcL s hg) (normalized_family_local H l hc s hg) a b

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

end Surjectivity
end PermanentBorder.SliceParameters

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical


theorem solution : type_of% @_root_.OAI.PermanentBorder.CI.normalized_count_constant := @_root_.OAI.PermanentBorder.CI.normalized_count_constant
