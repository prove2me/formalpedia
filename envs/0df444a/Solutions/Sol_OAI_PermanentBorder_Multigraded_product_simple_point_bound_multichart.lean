-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.product_simple_point_bound_multichart
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:37:14.540969+00:00
-- url     : https://prove2.me/submissions/33bdbe53-2ebf-4d04-90e1-4e82fac59539

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/ProjectiveCounts.lean:L289-L368
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.product_simple_point_bound_multichart. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Theorems.Thm_OAI_PermanentBorder_Multigraded_affine_independent_polynomial
import Theorems.Thm_OAI_PermanentBorder_Multigraded_comparison_piece_bound
import Theorems.Thm_OAI_PermanentBorder_Multigraded_homogeneousIdealMap_range
import Theorems.Thm_OAI_PermanentBorder_Multigraded_projective_interpolation

-- ---- from OAI.Algebra.Determinantal.LinearForms ----
namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearCoefficients
variable {K σ τ : Type*} [Field K] [Fintype τ]

end LinearCoefficients

section Vandermonde
variable {K : Type*} [Field K]

end Vandermonde
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section VandermondeLeaves
variable {K ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype L]

end VandermondeLeaves
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BinaryChoices
variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

end BinaryChoices
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section MixedCoefficient
variable {ι E : Type*} [Fintype E] [DecidableEq ι]

end MixedCoefficient
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section ComparisonPieceBound
variable {K ι σ : Type*} [Field K] [DecidableEq ι]

variable [Fintype ι]

end ComparisonPieceBound
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section HomogeneousIdealMap
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]
variable (w : σ → G) (e : E → G) (F : E → MvPolynomial σ K)
  (hF : ∀ i, (F i).IsWeightedHomogeneous w (e i))

lemma homogeneousIdealMap_val (d : G) (p : ∀ i : E, Piece (K := K) w (d-e i)) :
    (homogeneousIdealMap w e F hF d p).val = ∑ i, F i * (p i).val := by
  simp [homogeneousIdealMap]

lemma homogeneousIdealMap_affine (Q : E → MvPolynomial σ K)
    (hQ : ∀ i, (Q i).IsWeightedHomogeneous w (e i)) (d : G) (t : K) :
    homogeneousIdealMap w e (fun i => (1-t) • Q i + t • F i)
      (fun i => (isWeightedHomogeneous_smul w (hQ i) (1-t)).add
        (isWeightedHomogeneous_smul w (hF i) t)) d =
      (1-t) • homogeneousIdealMap w e Q hQ d + t • homogeneousIdealMap w e F hF d := by
  classical
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
    Submodule.coe_smul]
  rw [homogeneousIdealMap_val, homogeneousIdealMap_val, homogeneousIdealMap_val]
  simp only [add_mul, smul_mul_assoc, Finset.sum_add_distrib, ← Finset.smul_sum]

end HomogeneousIdealMap

lemma pairProduct_mem_productIdeal {K σ G : Type*} [Field K] [AddCommGroup G]
    (w : σ → G) (qs : List (FactorPair (K := K) w)) (i : Fin qs.length) :
    (qs.get i).left * (qs.get i).right ∈ productIdeal w qs := by
  induction qs with
  | nil => exact Fin.elim0 i
  | cons q qs ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Submodule.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
    · exact Submodule.mem_sup_right (ih i)

lemma productIdeal_le {K σ G : Type*} [Field K] [AddCommGroup G]
    (w : σ → G) (qs : List (FactorPair (K := K) w)) (I : Ideal (MvPolynomial σ K))
    (h : ∀ i : Fin qs.length, (qs.get i).left * (qs.get i).right ∈ I) :
    productIdeal w qs ≤ I := by
  induction qs with
  | nil => exact bot_le
  | cons q qs ih =>
    exact sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (h 0)))
      (ih (fun i => h i.succ))

lemma productIdeal_eq_span {K σ G : Type*} [Field K] [AddCommGroup G]
    (w : σ → G) (qs : List (FactorPair (K := K) w)) :
    productIdeal w qs = Ideal.span (Set.range (fun i : Fin qs.length =>
      (qs.get i).left * (qs.get i).right)) := by
  apply le_antisymm
  · exact productIdeal_le w qs _ (fun _ => Ideal.mem_span_range_self)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact pairProduct_mem_productIdeal w qs i

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
section AffineIndependent
variable {K E V : Type*} [Field K] [Fintype E]
  [AddCommGroup V] [Module K V]

end AffineIndependent
end PermanentBorder.Multigraded

end OAI

-- ---- from OAI.Algebra.Determinantal.PointBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
section AffineCokernel
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K W]

theorem affine_cokernel_polynomial (f g : V →ₗ[K] W) :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ t : K, p.eval t ≠ 0 →
      Module.finrank K (W ⧸ LinearMap.range ((1-t) • f + t • g)) ≤
        Module.finrank K (W ⧸ LinearMap.range f) := by
  classical
  let b := Module.finBasis K (LinearMap.range f)
  choose z hz using fun i => (b i).property
  have hli : LinearIndependent K (fun i => f (z i)) := by
    have h := b.linearIndependent.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
    simpa only [hz, Function.comp_def, Submodule.subtype_apply] using h
  obtain ⟨p,hp,hi⟩ := affine_independent_polynomial (fun i => f (z i))
    (fun i => g (z i)) hli
  refine ⟨p,hp,?_⟩
  intro t ht
  let ft : V →ₗ[K] W := (1-t) • f + t • g
  let bt : Fin (Module.finrank K (LinearMap.range f)) → LinearMap.range ft :=
    fun i => ⟨ft (z i), LinearMap.mem_range_self _ _⟩
  have htli : LinearIndependent K bt := by
    apply LinearIndependent.of_comp (LinearMap.range ft).subtype
    exact hi t ht
  have hb := htli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hb
  have hf := (LinearMap.range f).finrank_quotient_add_finrank
  have hg := (LinearMap.range ft).finrank_quotient_add_finrank
  dsimp only [ft] at hg hb
  omega

end AffineCokernel
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section GenericPieceBound
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]

theorem generic_homogeneous_quotient_bound (w : σ → G) (e : E → G)
    (F Q : E → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous w (e i))
    (hQ : ∀ i, (Q i).IsWeightedHomogeneous w (e i))
    (d : G) [Module.Finite K (Piece (K := K) w d)] :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ t : K, p.eval t ≠ 0 →
      Module.finrank K (componentQuotient w
        (Ideal.span (Set.range (fun i => (1-t) • Q i + t • F i))) d) ≤
      Module.finrank K (componentQuotient w (Ideal.span (Set.range Q)) d) := by
  obtain ⟨p,hp,h⟩ := affine_cokernel_polynomial
    (homogeneousIdealMap w e Q hQ d) (homogeneousIdealMap w e F hF d)
  refine ⟨p,hp,?_⟩
  intro t ht
  have h' := h t ht
  rw [← homogeneousIdealMap_affine w e F hF Q hQ d t] at h'
  rw [homogeneousIdealMap_range w e Q hQ d] at h'
  rw [homogeneousIdealMap_range] at h'
  exact h'

end GenericPieceBound

section ProductComparison
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem generic_product_piece_bound (a : ι →₀ ℕ)
    (qs : List (FactorPair (K := K) (blockWeight (fun v : BlockVariables a => v.1))))
    (u v : Fin qs.length → ι) (t : (Fin qs.length × Bool) → K)
    (ht : Function.Injective t)
    (hleft : ∀ i, (qs.get i).left = blockLinearForm a (u i) (t (i,false)))
    (hright : ∀ i, (qs.get i).right = blockLinearForm a (v i) (t (i,true)))
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1)
    (hlen : qs.length = ∑ j, a j)
    (F : Fin qs.length → MvPolynomial (BlockVariables a) K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      ((qs.get i).leftDegree + (qs.get i).rightDegree))
    (d : ι → ℤ) (hd : ∀ j, (qs.length : ℤ) < d j) :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ c : K, p.eval c ≠ 0 →
      pieceDim (blockWeight (fun v : BlockVariables a => v.1))
        (Ideal.span (Set.range (fun i =>
          (1-c) • ((qs.get i).left * (qs.get i).right) + c • F i))) d ≤
      (mixedPolynomial u v).coeff a := by
  let w := blockWeight (fun v : BlockVariables a => v.1)
  obtain ⟨p,hp,h⟩ := generic_homogeneous_quotient_bound w
    (fun i => (qs.get i).leftDegree + (qs.get i).rightDegree) F
    (fun i => (qs.get i).left * (qs.get i).right) hF
    (fun i => (qs.get i).left_homogeneous.mul (qs.get i).right_homogeneous) d
  refine ⟨p,hp,?_⟩
  intro c hc
  apply (h c hc).trans
  rw [← productIdeal_eq_span]
  exact comparison_piece_bound a qs u v t ht hleft hright hdeg hlen d hd

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

end Persistence
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
theorem fderiv_slice {C V : Type*} [NormedAddCommGroup C] [NormedSpace ℂ C]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    {F : C × V → V} (hF : ContDiff ℂ 1 F) (c : C) (x : V) :
    fderiv ℂ (fun x => F (c,x)) x =
      fderiv ℂ F (c,x) ∘L ContinuousLinearMap.inr ℂ C V := by
  have hi : HasFDerivAt (fun x : V => (c,x)) (ContinuousLinearMap.inr ℂ C V) x := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const (𝕜 := ℂ) c x).prodMk (hasFDerivAt_id (𝕜 := ℂ) x)
  exact ((hF.differentiable (by decide) (c,x)).hasFDerivAt.comp x hi).fderiv

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open MvPolynomial
variable {τ : Type*} [Fintype τ]
theorem contDiff_mvPolynomial_eval (p : MvPolynomial τ ℂ) :
    ContDiff ℂ 1 (fun x : τ → ℂ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℂ 1 (fun _ : τ → ℂ => a))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul, eval_X] using hp.mul (contDiff_apply ℂ ℂ i)

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section ProductSimplePointBound
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

end ProductSimplePointBound
end PermanentBorder.Multigraded

end OAI

-- ---- from OAI.Algebra.Determinantal.ProjectiveCounts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearPointCount
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

end BilinearPointCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProductAffineChart
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {L : Type*} [Fintype L] [DecidableEq L]

end ProductAffineChart
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectiveInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]

variable [Fintype L] [DecidableEq L]

end ProjectiveInterpolation
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectivePointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

theorem projective_points_le_pieceDim (group : σ → ι) (base : L → ι → σ)
    (hbase : ∀ i j, group (base i j) = j) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) (hd : ∀ j, (Fintype.card L : ℤ) ≤ d j)
    (x : L → σ → K) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    (hb : ∀ i j, x i (base i j) ≠ 0)
    (hz : ∀ i, ∀ p ∈ I, eval (x i) p = 0) :
    Fintype.card L ≤ Module.finrank K (componentQuotient (blockWeight group) I d) := by
  classical
  let P := Piece (K := K) (blockWeight group) d
  let S : Submodule K P := (I.restrictScalars K).comap P.subtype
  let ev : P →ₗ[K] (L → K) := LinearMap.pi fun i =>
    (aeval (x i)).toLinearMap.comp P.subtype
  have heval (p : P) (i : L) : ev p i = eval (x i) p.val := by
    simp [ev]
  have hker : S ≤ LinearMap.ker ev := by
    intro p hp
    apply LinearMap.mem_ker.mpr
    funext i
    rw [heval]
    exact hz i p.val hp
  let qev := S.liftQ ev hker
  obtain ⟨p,hp⟩ := projective_interpolation group d hd x hx base hbase hb
  have hs : Function.Surjective qev := by
    intro y
    refine ⟨S.mkQ (∑ i, y i • p i), ?_⟩
    change ev (∑ i, y i • p i) = y
    apply _root_.funext
    intro j
    have hei (i : L) : ev (p i) j = if j = i then 1 else 0 :=
      (heval (p i) j).trans (hp i j)
    calc
      ev (∑ i, y i • p i) j = ∑ i, y i * ev (p i) j := by simp
      _ = y j := by simp [hei]
  have h := LinearMap.finrank_le_finrank_of_surjective hs
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] using h

end ProjectivePointBound
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section MultiChartProductCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

omit [Fintype ι] [DecidableEq ι] in

lemma eventually_blockSeparated {σ : Type*} (group : σ → ι)
    (x : L → σ → ℂ) (hx : ∀ i j, i ≠ j → BlockSeparated group (x i) (x j))
    {y : L → ℂ → σ → ℂ} {c : ℂ}
    (hy : ∀ i, Tendsto (y i) (𝓝 c) (𝓝 (x i))) :
    ∀ᶠ c' in 𝓝 c, ∀ i j, i ≠ j → BlockSeparated group (y i c') (y j c') := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
  obtain ⟨v,w,hvw,hn⟩ := hx i j hij
  have hv₁ := (continuous_apply v).tendsto (x i) |>.comp (hy i)
  have hw₁ := (continuous_apply w).tendsto (x i) |>.comp (hy i)
  have hv₂ := (continuous_apply v).tendsto (x j) |>.comp (hy j)
  have hw₂ := (continuous_apply w).tendsto (x j) |>.comp (hy j)
  have he := ((hv₁.mul hw₂).sub (hw₁.mul hv₂)).eventually_ne (sub_ne_zero.mpr hn)
  exact he.mono (fun c' hc' _ => ⟨v,w,hvw,sub_ne_zero.mp hc'⟩)

theorem product_simple_point_bound_multichart (a : ι →₀ ℕ)
    (qs : List (FactorPair (K := ℂ) (blockWeight (fun v : BlockVariables a => v.1))))
    (u v : Fin qs.length → ι) (t : (Fin qs.length × Bool) → ℂ)
    (ht : Function.Injective t)
    (hleft : ∀ i, (qs.get i).left = blockLinearForm a (u i) (t (i,false)))
    (hright : ∀ i, (qs.get i).right = blockLinearForm a (v i) (t (i,true)))
    (hdeg : ∀ q ∈ qs, ∀ j, q.leftDegree j ≤ 1)
    (hlen : qs.length = ∑ j, a j)
    (F : Fin qs.length → MvPolynomial (BlockVariables a) ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous
      (blockWeight (fun v : BlockVariables a => v.1))
      ((qs.get i).leftDegree + (qs.get i).rightDegree))
    (base : L → ι → BlockVariables a) (hbase : ∀ i j, (base i j).1 = j)
    (e : L → (Fin qs.length → ℂ) ≃L[ℂ] V)
    (chart : L → V → BlockVariables a → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
      (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let Q : Fin qs.length → MvPolynomial (BlockVariables a) ℂ :=
    fun j => (qs.get j).left * (qs.get j).right
  let family : L → ℂ × V → V := fun i z => e i
    (fun j => (1-z.1) * eval (chart i z.2) (Q j) + z.1 * eval (chart i z.2) (F j))
  have hcont (i : L) : ContDiff ℂ 1 (family i) := by
    apply (e i).contDiff.comp
    apply contDiff_pi.mpr
    intro j
    exact ((contDiff_const.sub contDiff_fst).mul
      ((PolarAnalysis.contDiff_mvPolynomial_eval (Q j)).comp ((hc i).comp contDiff_snd))).add
      (contDiff_fst.mul
        ((PolarAnalysis.contDiff_mvPolynomial_eval (F j)).comp ((hc i).comp contDiff_snd)))
  have hone (i : L) : (fun z => family i (1,z)) =
      (fun z => e i (fun j => eval (chart i z) (F j))) := by
    funext z
    simp [family]
  have hzero (i : L) : family i (1,x i) = 0 := by
    rw [congrFun (hone i)]
    rw [show (fun j => eval (chart i (x i)) (F j)) = 0 from funext (hz i), map_zero]
  have hsimple (i : L) : PolarAnalysis.SimpleAt (family i) 1 (x i) := by
    unfold PolarAnalysis.SimpleAt
    rw [← PolarAnalysis.fderiv_slice (hcont i), hone]
    exact hs i
  choose ψ hψ hzψ using fun i => PolarAnalysis.simple_branch (hcont i) (hzero i) (hsimple i)
  have hsep := eventually_blockSeparated (fun v : BlockVariables a => v.1)
    (fun i => chart i (x i)) hx (fun i => (hc i).continuous.continuousAt.tendsto.comp (hψ i))
  have hpersist : ∀ᶠ c in 𝓝 (1 : ℂ),
      (∀ i, family i (c,ψ i c) = 0) ∧
      ∀ i j, i ≠ j → BlockSeparated (fun v : BlockVariables a => v.1)
        (chart i (ψ i c)) (chart j (ψ j c)) := by
    filter_upwards [Filter.eventually_all.mpr hzψ, hsep] with c hz hc
    exact ⟨fun i => (hz i).1,hc⟩
  let d : ι → ℤ := fun _ => qs.length + Fintype.card L + 1
  obtain ⟨p,hp,hbound⟩ := generic_product_piece_bound a qs u v t ht hleft hright hdeg
    hlen F hF d (by intro j; dsimp [d]; omega)
  have hpne : p ≠ 0 := by
    intro h
    rw [h, Polynomial.eval_zero] at hp
    exact zero_ne_one hp
  have hdense : Dense {c : ℂ | p.eval c ≠ 0} :=
    (Polynomial.finite_setOfPred_isRoot hpne).countable.dense_compl ℂ
  obtain ⟨c,hpc,hyz,hy⟩ := hdense.inter_nhds_nonempty hpersist
  let I := Ideal.span (Set.range (fun j => (1-c) • Q j + c • F j))
  have hyideal (i : L) : ∀ p ∈ I, eval (chart i (ψ i c)) p = 0 := by
    have hI : I ≤ RingHom.ker (eval (chart i (ψ i c))) := by
      apply Ideal.span_le.mpr
      rintro p ⟨j,rfl⟩
      change eval (chart i (ψ i c)) ((1-c) • Q j + c • F j) = 0
      have h := (e i).injective ((hyz i).trans (map_zero (e i)).symm)
      have h := congrFun h j
      simpa only [map_add, smul_eval, Pi.zero_apply] using h
    exact fun p hp => hI hp
  have hpoints := projective_points_le_pieceDim (fun v : BlockVariables a => v.1)
    base hbase I d (by intro j; dsimp [d]; omega) (fun i => chart i (ψ i c)) hy
    (fun i j => by rw [hcn]; exact one_ne_zero) hyideal
  exact hpoints.trans (hbound c hpc)

end MultiChartProductCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearMultiChartCount
variable {ι L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

end BilinearMultiChartCount
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.product_simple_point_bound_multichart := @_root_.OAI.PermanentBorder.Multigraded.product_simple_point_bound_multichart
