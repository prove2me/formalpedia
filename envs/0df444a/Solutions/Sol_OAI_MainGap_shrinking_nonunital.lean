-- Prove2me | solution 1 for OAI.MainGap.shrinking_nonunital
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:13:47.624995+00:00
-- url     : https://prove2.me/submissions/d1eec4d2-9bc8-4307-9863-1fc13ec3a3c2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Shrinking.lean:L205-L239
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.shrinking_nonunital. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Ultrafilter
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Avoidance
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Graph
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Nonvanishing
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Compression
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Shrinking
import Theorems.Thm_OAI_MainGap_conditional_shrinking
import Theorems.Thm_OAI_MainGap_graph_nonvanishing
import Theorems.Thm_OAI_MainGap_unitization_Her

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Cutoffs ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section MoreHer
variable [PartialOrder A] [StarOrderedRing A]

end MoreHer
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
section Ramps
variable [PartialOrder A] [StarOrderedRing A]

end Ramps
end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_map {B : Type*} [NonUnitalCStarAlgebra B] (π : A →⋆ₙₐ[ℂ] B)
    {h k : A} (hk : k ∈ Her h) : π k ∈ Her (π h) := by
  have hc : IsClosed {k : A | π k ∈ Her (π h)} :=
    (isClosed_Her (π h)).preimage (map_continuous π)
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change π (h * a * star h) ∈ Her (π h)
  simpa only [map_mul, map_star] using sandwich_mem_Her (π h) (π a)

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Shrinking ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.shrinkingPartialOrder
attribute [local instance] OAI.MainGap.shrinkingStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingOperatorPartialOrder
attribute [local instance] OAI.MainGap.shrinkingOperatorStarOrderedRing
theorem shrinking_unital_local {a y c : A} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    (hp : ∀ z : A, 0 ≤ z → z ∈ Her a → ProperlyInfinite z) :
    ∃ (p q : A) (κ : ℝ), 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her y ∧ 0 ≤ κ ∧ κ < 1 ∧
      HerCompression p q c κ ∧
      (∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom a‖ → ‖R.hom p‖=1) ∧
      (∀ R : HilbertRep.{u,u} A, (1/2:ℝ)<‖R.hom y‖ → ‖R.hom q‖=1) := by
  obtain ⟨p,hpp,hpn,hpH,hsignal,hvan⟩ := graph_nonvanishing.{u,u} ha hy hcn hp
  exact conditional_shrinking ha hy hpp hpn hyn hcn hpH hsignal hvan

end MainGap

namespace MainGap
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma matrixMap_mul (π : A →⋆ₙₐ[ℂ] B) {l m n : ℕ}
    (x : CStarMatrix (Fin l) (Fin m) A) (y : CStarMatrix (Fin m) (Fin n) A) :
    matrixMap π (x*y)=matrixMap π x * matrixMap π y := by
  ext i j
  change π (∑ k, x i k * y k j) = ∑ k, π (x i k) * π (y k j)
  simp only [map_sum, map_mul]

lemma matrixMap_star (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ}
    (x : CStarMatrix (Fin m) (Fin n) A) :
    matrixMap π x.conjTranspose=(matrixMap π x).conjTranspose := by
  ext i j
  change π (star (x j i)) = star (π (x j i))
  exact map_star π _

lemma continuous_matrixMap (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ} :
    Continuous (matrixMap π : CStarMatrix (Fin m) (Fin n) A → CStarMatrix (Fin m) (Fin n) B) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (map_continuous π).comp ((continuous_apply j).comp (continuous_apply i))

lemma FiniteCuntzLE.map (π : A →⋆ₙₐ[ℂ] B) {m n : ℕ}
    {d : CStarMatrix (Fin n) (Fin n) A} {v : CStarMatrix (Fin m) (Fin m) A}
    (h : FiniteCuntzLE d v) : FiniteCuntzLE (matrixMap π d) (matrixMap π v) := by
  obtain ⟨r,ht⟩ := h
  refine ⟨fun j => matrixMap π (r j), ?_⟩
  have he := (continuous_matrixMap π).continuousAt.tendsto.comp ht
  change Tendsto (fun j => matrixMap π ((r j).conjTranspose * v * r j)) atTop (𝓝 (matrixMap π d)) at he
  simpa only [matrixMap_mul, matrixMap_star] using he

lemma ProperlyInfinite.map (π : A →⋆ₙₐ[ℂ] B) {h : A} (hh : ProperlyInfinite h) :
    ProperlyInfinite (π h) := by
  have he := FiniteCuntzLE.map π hh
  have hdouble : matrixMap π (doubleCorner h)=doubleCorner (π h) := by
    ext i j
    change π (if i=j then h else 0) = if i=j then π h else 0
    split_ifs <;> simp
  have hsingle : matrixMap π (scalarCorner h)=scalarCorner (π h) := rfl
  change FiniteCuntzLE _ _
  rwa [hdouble, hsingle] at he

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.shrinkingHerPartialOrder
attribute [local instance] OAI.MainGap.shrinkingHerStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingHerUnitizationPartialOrder
attribute [local instance] OAI.MainGap.shrinkingHerUnitizationStarOrderedRing
lemma unitization_inr_snd_of_Her {a : A} {z : Unitization ℂ A}
    (hz : z ∈ Her (a : Unitization ℂ A)) : (z.snd : Unitization ℂ A)=z := by
  have he := Unitization.inl_fst_add_inr_snd_eq z
  simpa only [(unitization_Her hz).1, Unitization.inl_zero, zero_add] using he

lemma unitization_proper_hereditary (hp : PropertyP A) {a : A}
    {z : Unitization ℂ A} (hz : 0 ≤ z) (hzH : z ∈ Her (a : Unitization ℂ A)) :
    ProperlyInfinite z := by
  have he := unitization_inr_snd_of_Her hzH
  have hz' : 0 ≤ z.snd := Unitization.inr_nonneg_iff.mp (he.symm ▸ hz)
  have hh := (hp z.snd hz').map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  change ProperlyInfinite (z.snd : Unitization ℂ A) at hh
  rwa [he] at hh

end MainGap

namespace MainGap
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.shrinkingNonunitalPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationStarOrderedRing
theorem shrinking_nonunital (hp : PropertyP A) {a y c : A} (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1) :
    ∃ (p q : A) (κ : ℝ), 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her y ∧ 0 ≤ κ ∧ κ < 1 ∧
      HerCompression p q c κ ∧ NormSignal a p ∧ NormSignal y q := by
  obtain ⟨p,q,κ,hp0,hpn,hpH,hq0,hqn,hqH,hκ0,hκ1,hcomp,hps,hqs⟩ :=
    shrinking_unital_local (Unitization.inr_nonneg_iff.mpr ha)
      (Unitization.inr_nonneg_iff.mpr hy)
      (by simpa only [Unitization.norm_inr] using hyn : ‖(y : Unitization ℂ A)‖ ≤ 1)
      (by simpa only [Unitization.norm_inr] using hcn : ‖(c : Unitization ℂ A)‖ ≤ 1)
      (fun z hz hzH => unitization_proper_hereditary hp hz hzH)
  have hep := unitization_inr_snd_of_Her hpH
  have heq := unitization_inr_snd_of_Her hqH
  refine ⟨p.snd,q.snd,κ,Unitization.inr_nonneg_iff.mp (hep.symm ▸ hp0),?_,
    (unitization_Her hpH).2,Unitization.inr_nonneg_iff.mp (heq.symm ▸ hq0),?_,
    (unitization_Her hqH).2,hκ0,hκ1,?_,?_,?_⟩
  · have hn : ‖p.snd‖=‖p‖ := by simpa only [Unitization.norm_inr] using congrArg norm hep
    rwa [hn]
  · have hn : ‖q.snd‖=‖q‖ := by simpa only [Unitization.norm_inr] using congrArg norm heq
    rwa [hn]
  · intro x hx k hk
    have hx' := Her_map (Unitization.inrNonUnitalStarAlgHom ℂ A) hx
    have hk' := Her_map (Unitization.inrNonUnitalStarAlgHom ℂ A) hk
    change (x : Unitization ℂ A) ∈ Her (p.snd : Unitization ℂ A) at hx'
    change (k : Unitization ℂ A) ∈ Her (q.snd : Unitization ℂ A) at hk'
    rw [hep] at hx'
    rw [heq] at hk'
    have hb := hcomp _ hx' _ hk'
    simpa only [← Unitization.inr_mul, Unitization.norm_inr] using hb
  · intro R hRa
    rw [hep]
    exact hps R hRa
  · intro R hRy
    rw [heq]
    exact hqs R hRy
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.shrinkingNonunitalPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalStarOrderedRing
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationPartialOrder
attribute [local instance] OAI.MainGap.shrinkingNonunitalUnitizationStarOrderedRing


theorem solution.{u} : type_of% @_root_.OAI.MainGap.shrinking_nonunital.{u} := @_root_.OAI.MainGap.shrinking_nonunital.{u}
