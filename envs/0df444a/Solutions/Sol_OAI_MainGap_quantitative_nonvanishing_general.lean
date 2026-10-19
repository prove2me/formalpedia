-- Prove2me | solution 1 for OAI.MainGap.quantitative_nonvanishing_general
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:56:37.570471+00:00
-- url     : https://prove2.me/submissions/00df9a0d-d9b9-4c40-b623-0cc8048761d0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Nonvanishing.lean:L83-L132
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.quantitative_nonvanishing_general. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_limitRep_annihilates
import Theorems.Thm_OAI_MainGap_limitRep_nonzero
import Theorems.Thm_OAI_MainGap_norm_sub_cut_le

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.FourChoices ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.fourChoicesPartialOrder
attribute [local instance] OAI.MainGap.fourChoicesStarOrderedRing
end MainGap

namespace MainGap
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]
attribute [local instance] OAI.MainGap.fourChoicesMapDomainOrder
attribute [local instance] OAI.MainGap.fourChoicesMapDomainStarOrder
attribute [local instance] OAI.MainGap.fourChoicesMapCodomainOrder
attribute [local instance] OAI.MainGap.fourChoicesMapCodomainStarOrder
variable (π : A →⋆ₐ[ℂ] D)

lemma map_cut_sa {a : A} (ha : IsSelfAdjoint a) {l : ℝ} (hl : 0 ≤ l) :
    π (cut a l) = cut (π a) l :=
  π.toNonUnitalStarAlgHom.map_cfcₙ (fun t : ℝ => max (t-l) 0) a
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hl)]) (map_continuous π) ha (ha.map π)

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.fourChoiceStructureOrder
attribute [local instance] OAI.MainGap.fourChoiceStructureStarOrder
universe v

namespace FourChoice
variable {X : A} {B : Fin 4 → A} {E : Finset A} {η : ℝ} (F : FourChoice.{v, _} X B E η)

variable {D : Type v} [CStarAlgebra D]
attribute [local instance] OAI.MainGap.FourChoice.fourChoiceRepresentationOrder
attribute [local instance] OAI.MainGap.FourChoice.fourChoiceRepresentationStarOrder
variable (π : A →⋆ₐ[ℂ] D) (hX : 0 ≤ X) (hη : 0 < η)
  (hmatch : ∀ i, π (F.T i) = π (B i))

end FourChoice
end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Nonvanishing ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.nonvanishingPartialOrder
attribute [local instance] OAI.MainGap.nonvanishingStarOrderedRing
attribute [local instance] OAI.MainGap.nonvanishingOperatorPartialOrder
attribute [local instance] OAI.MainGap.nonvanishingOperatorStarOrderedRing
lemma cut_eq_zero_of_norm_le {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : ‖a‖ ≤ l) :
    cut a l = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  change ‖cfcₙ (fun t : ℝ => max (t-l) 0) a‖ ≤ 0
  apply norm_cfcₙ_le
  intro r hr
  have hb := NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a hr
    ha.isSelfAdjoint
  have hb' : |r| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using hb
  have ht : r ≤ l := (le_abs_self r).trans (hb'.trans hl)
  rw [max_eq_right (sub_nonpos.mpr ht), norm_zero]

theorem quantitative_nonvanishing_general {d y : A} (hy : 0 ≤ y)
    {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s')
    (h : ∀ R : HilbertRep.{u,u} A, R.hom d=0 → ‖R.hom y‖ ≤ s) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ R : HilbertRep.{u,u} A,
      s' < ‖R.hom y‖ → δ < ‖R.hom d‖ := by
  classical
  by_contra! hh
  let η : ℕ → ℝ := fun n => 1 / ((n : ℝ)+2)
  have hηpos (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hηlt (n : ℕ) : η n < 1 := by
    dsimp [η]
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hbad (n : ℕ) : ∃ R : HilbertRep.{u,u} A,
      s' < ‖R.hom y‖ ∧ ‖R.hom d‖ ≤ η n := hh (η n) (hηpos n) (hηlt n)
  choose R hRy hRd using hbad
  let π := fun n => (R n).hom
  let a := cut y ((s+s')/2)
  have ha : ∀ n, ((s'-s)/2) < ‖π n a‖ := by
    intro n
    have h₁ : ‖π n y - π n a‖ ≤ ((s+s')/2) := by
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le (π n) _).trans
        (norm_sub_cut_le hy (by linarith))
    have h₂ := norm_sub_norm_le (π n y) (π n a)
    have h₃ := hRy n
    change s' < ‖π n y‖ at h₃
    linarith
  choose ξ hξ hξa using fun n => (π n a).exists_lt_apply_of_lt_opNorm (ha n)
  have hnξ : ∀ n, ‖ξ n‖ ≤ 1 := fun n => (hξ n).le
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have hη : Tendsto η (ω : Filter ℕ) (𝓝 0) := by
    have he : η = fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ)+1) := by
      funext n
      dsimp [η]
      push_cast
      congr 1; ring
    rw [he]
    exact ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)).mono_left hω
  let ρ : HilbertRep.{u,u} A := ⟨LimitHilbert ω π ξ hnξ, limitRep ω π ξ hnξ⟩
  have hd₀ : ρ.hom d=0 := limitRep_annihilates ω π ξ hnξ d
    (squeeze_zero (fun n => norm_nonneg _) hRd hη)
  have han : ρ.hom a ≠ 0 := limitRep_nonzero ω π ξ hnξ a (by linarith : (0:ℝ)<(s'-s)/2)
    (Filter.Eventually.of_forall (fun n => (hξa n).le))
  apply han
  change ρ.hom (cut y ((s+s')/2))=0
  rw [map_cut_sa ρ.hom hy.isSelfAdjoint (by linarith)]
  exact cut_eq_zero_of_norm_le (map_nonneg ρ.hom hy) ((h ρ hd₀).trans (by linarith))

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.nonvanishingPartialOrder
attribute [local instance] OAI.MainGap.nonvanishingStarOrderedRing
attribute [local instance] OAI.MainGap.nonvanishingOperatorPartialOrder
attribute [local instance] OAI.MainGap.nonvanishingOperatorStarOrderedRing


theorem solution.{u} : type_of% @_root_.OAI.MainGap.quantitative_nonvanishing_general.{u} := @_root_.OAI.MainGap.quantitative_nonvanishing_general.{u}
