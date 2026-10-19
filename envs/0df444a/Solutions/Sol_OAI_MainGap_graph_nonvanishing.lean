-- Prove2me | solution 1 for OAI.MainGap.graph_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:52:36.727798+00:00
-- url     : https://prove2.me/submissions/dddb146f-6169-4d94-a695-73af82a5677a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Graph.lean:L590-L634
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.graph_nonvanishing. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_ProperlyInfinite_finite_copies
import Theorems.Thm_OAI_MainGap_cut_cut
import Theorems.Thm_OAI_MainGap_four_avoidance_unital
import Theorems.Thm_OAI_MainGap_graph_failure_of_identities
import Theorems.Thm_OAI_MainGap_orthogonalSlots_of_comparison

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma Her_sandwich {h k : A} (hk : k ∈ Her h) (a : A) : k * a * star k ∈ Her h := by
  let k' : Her h := ⟨k, hk⟩
  change (k' : A) * a * star (k' : A) ∈ Her h
  refine (sandwichMap_dense h).induction_on k'
    ((isClosed_Her h).preimage (by fun_prop)) ?_
  intro b
  change (h * b * star h) * a * star (h * b * star h) ∈ Her h
  convert sandwich_mem_Her h (b * star h * a * h * star b) using 1
  simp only [star_mul, star_star, mul_assoc]

lemma Her_mono_of_mem {h k : A} (hk : k ∈ Her h) : Her k ≤ Her h := by
  apply closure_minimal _ (isClosed_Her h)
  rintro _ ⟨a, rfl⟩
  exact Her_sandwich hk a

namespace RegularTransport
variable {h v : A} (T : RegularTransport h v)

end RegularTransport

section Order
variable [PartialOrder A] [StarOrderedRing A]

lemma mul_star_mem_Her (h : A) : h * star h ∈ Her h := by
  apply (isClosed_Her h).mem_of_tendsto
    (((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const (star h))
  exact Filter.Eventually.of_forall (sandwich_mem_Her h)

lemma self_mem_Her {h : A} (hh : 0 ≤ h) : h ∈ Her h := by
  have hm : h * h ∈ Her h := by
    simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using mul_star_mem_Her h
  simpa only [CFC.sqrt_mul_self h hh] using
    sqrt_mem_Her hm (by simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using
      star_mul_self_nonneg h)

lemma cut_nonneg (d : A) (ε : ℝ) : 0 ≤ cut d ε := by
  exact cfcₙ_nonneg (fun _ _ => le_max_right _ _)

lemma cut_mem_Her {d : A} (hd : 0 ≤ d) (ε : ℝ) : cut d ε ∈ Her d := by
  exact cfcₙ_mem (𝕜' := ℂ) _ (self_mem_Her hd)

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.OrthogonalSlots ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
open scoped CStarAlgebra
attribute [local instance] OAI.MainGap.orthogonalSlotsPartialOrder
attribute [local instance] OAI.MainGap.orthogonalSlotsStarOrderedRing
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixIsScalarTower
attribute [local instance] OAI.MainGap.orthogonalSlotsMatrixSMulCommClass
lemma cut_map {B : Type*} [NonUnitalCStarAlgebra B]
    (f : A →⋆ₙₐ[ℂ] B) (a : A) (ε : ℝ) (ha : IsSelfAdjoint a) (hε : 0 ≤ ε) :
    cut (f a) ε = f (cut a ε) :=
  (f.map_cfcₙ (q := IsSelfAdjoint) (fun t : ℝ => max (t-ε) 0) a
    (hf₀ := by simp [hε]) (ha := ha)).symm

namespace RegularTransport
variable {n : ℕ} {h v : A} (i₀ : Fin n)
    (T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v))

end RegularTransport

theorem ProperlyInfinite.orthogonalSlots {d : A} (hd : 0 ≤ d) (hp : ProperlyInfinite d)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) : Nonempty (OrthogonalSlots n (cut d ε) d) :=
  orthogonalSlots_of_comparison hd hd (hp.finite_copies n) hε

namespace OrthogonalSlots
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

end OrthogonalSlots

section FiniteSum

end FiniteSum
end MainGap

end

end OAI

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

lemma norm_mem_quasispectrum_of_nonneg {a : A} (ha : 0 ≤ a) :
    ‖a‖ ∈ quasispectrum ℝ a := by
  simpa using quasispectrum.algebraMap_mem ℝ
    (NonUnitalIsometricContinuousFunctionalCalculus.isGreatest_quasispectrum a ha).1

lemma continuous_rampFn (l u : ℝ) : Continuous (rampFn l u) :=
  continuous_const.min (((continuous_id.sub continuous_const).max continuous_const).div_const _)

lemma rampFn_nonneg {l u t : ℝ} (hlu : l ≤ u) : 0 ≤ rampFn l u t :=
  le_min (by norm_num) (div_nonneg (le_max_right _ _) (sub_nonneg.mpr hlu))

lemma rampFn_le_one (l u t : ℝ) : rampFn l u t ≤ 1 := min_le_left _ _

lemma rampFn_zero {l u t : ℝ} (ht : t ≤ l) : rampFn l u t = 0 := by
  simp only [rampFn, max_eq_right (sub_nonpos.mpr ht), zero_div, min_eq_right (by norm_num : (0:ℝ) ≤ 1)]

lemma rampFn_one {l u t : ℝ} (hlu : l < u) (ht : u ≤ t) : rampFn l u t = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ (sub_pos.mpr hlu)).mpr
  rw [one_mul, max_eq_left (sub_nonneg.mpr (hlu.le.trans ht))]
  linarith

lemma ramp_nonneg (a : A) {l u : ℝ} (hlu : l ≤ u) : 0 ≤ ramp a l u :=
  cfcₙ_nonneg (fun _ _ => rampFn_nonneg hlu)

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_ramp_le_one (a : A) {l u : ℝ} (hlu : l ≤ u) : ‖ramp a l u‖ ≤ 1 := by
  apply norm_cfcₙ_le
  intro t _
  rw [Real.norm_eq_abs, abs_of_nonneg (rampFn_nonneg hlu)]
  exact rampFn_le_one _ _ _

lemma ramp_mem_Her_cut {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l) :
    ramp a l u ∈ Her (cut a l) := by
  have hcomp : ramp a l u = cfcₙ (fun t : ℝ => min 1 (t / (u-l))) (cut a l) := by
    unfold ramp cut
    exact cfcₙ_comp (fun t : ℝ => min 1 (t / (u-l))) (fun t : ℝ => max (t-l) 0) a
      (continuous_const.min (continuous_id.div_const _)).continuousOn (by norm_num)
      ((continuous_id.sub continuous_const).max continuous_const).continuousOn
      (by simp [max_eq_right (neg_nonpos.mpr hl)]) (.of_nonneg ha)
  rw [hcomp]
  exact cfcₙ_mem (𝕜' := ℂ) _ (self_mem_Her (cut_nonneg a l))

lemma norm_ramp_eq_one {a : A} (ha : 0 ≤ a) {l u : ℝ} (hl : 0 ≤ l)
    (hlu : l < u) (hu : u ≤ ‖a‖) : ‖ramp a l u‖ = 1 := by
  apply le_antisymm (norm_ramp_le_one a hlu.le)
  have ht := norm_apply_le_norm_cfcₙ (rampFn l u) a
    (norm_mem_quasispectrum_of_nonneg ha) (continuous_rampFn l u).continuousOn
    (rampFn_zero hl) (.of_nonneg ha)
  change 1 ≤ ‖cfcₙ (rampFn l u) a‖
  simpa only [rampFn_one hlu hu, norm_one] using ht

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

lemma map_ramp_sa {a : A} (ha : IsSelfAdjoint a) {l u : ℝ} (hl : 0 ≤ l) :
    π (ramp a l u) = ramp (π a) l u :=
  π.toNonUnitalStarAlgHom.map_cfcₙ (rampFn l u) a
    (continuous_rampFn l u).continuousOn (rampFn_zero hl)
    (map_continuous π) ha (ha.map π)

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

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Graph ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
namespace OrthogonalSlots
section GraphAlgebra
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

lemma graphWord_inner (R : Fin n → A) (hR : ∀ i (k : Her h), R i * (k : A) ∈ Her h)
    (k l : Her h) :
    star (S.graphWord R hR k) * S.graphWord R hR l =
      star (k : A) * (∑ i, star (R i) * R i) * (l : A) := by
  classical
  simp only [graphWord, star_sum, Finset.sum_mul, Finset.mul_sum, S.inner]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [star_mul, mul_assoc]

lemma graphWord_outer (R : Fin n → A) (hR : ∀ i (k : Her h), R i * (k : A) ∈ Her h)
    (k l : Her h) : S.graphWord R hR k * star (S.graphWord R hR l) ∈ Her v := by
  classical
  simp only [graphWord, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact (Her v).sum_mem fun i _ => (Her v).sum_mem fun j _ => S.outer j i _ _

lemma slot_graphWord (R : Fin n → A) (hR : ∀ i (k : Her h), R i * (k : A) ∈ Her h)
    (i : Fin n) (k l : Her h) :
    star (S.carrier i k) * S.graphWord R hR l = star (k : A) * R i * (l : A) := by
  classical
  simp only [graphWord, Finset.mul_sum, S.inner]
  simp [mul_assoc]

end GraphAlgebra
end OrthogonalSlots

section UnitalGraph
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma graphComplement_nonneg (S : Fin 4 → D) : 0 ≤ graphComplement S :=
  cfc_nonneg fun _ _ => Real.sqrt_nonneg _

lemma graphComplement_mul_self (S : Fin 4 → D) (hS : ∀ i, ‖S i‖ ≤ 1) :
    graphComplement S * graphComplement S =
      (15/16 : ℝ) • (1 : D) - (1/16 : ℝ) • (∑ i, star (S i)*S i) := by
  rcases subsingleton_or_nontrivial D with hD | hD
  · exact Subsingleton.elim _ _
  let q := ∑ i, star (S i)*S i
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => star_mul_self_nonneg _
  have hn : ‖q‖ ≤ 4 := by
    calc
      ‖q‖ ≤ ∑ i, ‖star (S i)*S i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 4, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [CStarRing.norm_star_mul_self]
        simpa using mul_self_le_mul_self (norm_nonneg _) (hS i)
      _ = 4 := by simp
  have hc : Continuous (fun t : ℝ => Real.sqrt ((15-t)/16)) := by fun_prop
  change cfc _ q * cfc _ q = _
  rw [← cfc_mul _ _ q hc.continuousOn hc.continuousOn]
  have he : cfc (fun t : ℝ => Real.sqrt ((15-t)/16) * Real.sqrt ((15-t)/16)) q =
      cfc (fun t : ℝ => 15/16 - (1/16)*t) q := by
    apply cfc_congr
    intro t ht
    have ht' : t ≤ 4 := (Real.le_norm_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans hn)
    dsimp only
    rw [Real.mul_self_sqrt (by linarith : 0 ≤ (15-t)/16)]
    ring
  rw [he, cfc_sub (fun _ : ℝ => 15/16) (fun t : ℝ => (1/16)*t) q,
    cfc_const _ q hq.isSelfAdjoint, cfc_const_mul (1/16 : ℝ) (fun t : ℝ => t) q,
    cfc_id' ℝ q hq.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]

lemma graphCoeffs_inner (T : Fin 4 → D) (hT : ∀ i, ‖T i‖ ≤ 1) :
    ∑ i, star (graphCoeffs T i) * graphCoeffs T i = 1 := by
  classical
  rw [Fin.sum_univ_six]
  dsimp [graphCoeffs]
  simp only [star_smul, star_trivial, star_one, smul_mul_assoc, mul_smul_comm,
    smul_smul, one_mul]
  rw [(graphComplement_nonneg T).isSelfAdjoint.star_eq,
    graphComplement_mul_self T hT, Fin.sum_univ_four]
  module

end UnitalGraph
lemma continuous_graphInverseFn : Continuous graphInverseFn := by
  apply Continuous.div continuous_id
    (((continuous_const : Continuous (fun _ : ℝ => (1/32 : ℝ))).max continuous_id).pow 2)
  intro t
  exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/32) (le_max_left _ _)))

lemma graphInverseFn_zero : graphInverseFn 0 = 0 := by simp [graphInverseFn]

section InverseOrder
variable [PartialOrder A] [StarOrderedRing A]

lemma map_graphInverse {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : A →⋆ₙₐ[ℂ] B) {X : A} (hX : 0 ≤ X) :
    π (graphInverse X) = graphInverse (π X) :=
  π.map_cfcₙ graphInverseFn X continuous_graphInverseFn.continuousOn graphInverseFn_zero
    (map_continuous π) hX.isSelfAdjoint (map_nonneg π hX).isSelfAdjoint

end InverseOrder
section GraphDefect
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end GraphDefect

section GraphConstruction
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable {h a t : D} (V : OrthogonalSlots 6 h a) (ht : 0 ≤ t) (htH : t ∈ Her h)

lemma graphZ_inner (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) (hn : ∀ i, ‖T i‖ ≤ 1) :
    star (graphZ V ht htH T hT) * graphZ V ht htH T hT = t := by
  rw [graphZ, V.graphWord_inner, graphCoeffs_inner T hn]
  simpa only [mul_one, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq] using CFC.sqrt_mul_sqrt_self t ht

lemma graphP_nonneg (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) : 0 ≤ graphP V ht htH T hT :=
  mul_star_self_nonneg _

lemma graphP_mem (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) : graphP V ht htH T hT ∈ Her a :=
  V.graphWord_outer _ _ _ _

lemma graphP_represented_norm {E : Type*} [NonUnitalCStarAlgebra E]
    (π : D →⋆ₙₐ[ℂ] E) (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) (hn : ∀ i, ‖T i‖ ≤ 1) :
    ‖π (graphP V ht htH T hT)‖ = ‖π t‖ := by
  rw [graphP, map_mul, map_star, CStarRing.norm_self_mul_star,
    ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul, graphZ_inner V ht htH T hT hn]

include ht in
lemma slot_sandwich_mem (i j : Fin 6) (F : D) :
    star (graphSlot V htH i) * F * graphSlot V htH j ∈ Her h := by
  let r : Her h := ⟨CFC.sqrt t, sqrt_mem_Her htH ht⟩
  have he : (⟨t, htH⟩ : Her h) = r*r := by
    apply Subtype.ext
    exact (CFC.sqrt_mul_sqrt_self t ht).symm
  have hWi : graphSlot V htH i = V.carrier i r * CFC.sqrt t := by rw [graphSlot, he, V.mul]
  have hWj : graphSlot V htH j = V.carrier j r * CFC.sqrt t := by rw [graphSlot, he, V.mul]
  rw [hWi, hWj, star_mul, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq]
  have hm := Her_sandwich (sqrt_mem_Her htH ht) (star (V.carrier i r) * F * V.carrier j r)
  simpa only [(CFC.sqrt_nonneg t).isSelfAdjoint.star_eq, mul_assoc] using hm

lemma graphX_nonneg {F : D} (hF : 0 ≤ F) : 0 ≤ graphX V htH F :=
  smul_nonneg (by norm_num) (star_left_conjugate_nonneg hF _)

include ht in
lemma graphX_mem (F : D) : graphX V htH F ∈ Her h :=
  real_smul_mem_Her (slot_sandwich_mem V ht htH 0 0 F) _

lemma graphSlot0_Z (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) :
    star (graphSlot V htH 0) * graphZ V ht htH T hT = (1/4 : ℝ) • (t * CFC.sqrt t) := by
  rw [graphSlot, graphZ, V.slot_graphWord]
  simp [graphCoeffs, ht.isSelfAdjoint.star_eq]

lemma graphSlot_Z (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) (i : Fin 4) :
    star (graphSlot V htH i.castSucc.succ) * graphZ V ht htH T hT =
      (1/4 : ℝ) • (t * T i * CFC.sqrt t) := by
  rw [graphSlot, graphZ, V.slot_graphWord]
  have he : graphCoeffs T i.castSucc.succ = (1/4 : ℝ) • T i := by fin_cases i <;> rfl
  rw [he, ht.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc]

end GraphConstruction

section AbstractMeasurements
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end AbstractMeasurements

section RepresentedGraph
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
variable (π : D →⋆ₐ[ℂ] E) {h a t : D} (V : OrthogonalSlots 6 h a)
  (ht : 0 ≤ t) (htH : t ∈ Her h)

omit [PartialOrder D] [StarOrderedRing D] [PartialOrder E] [StarOrderedRing E] in
lemma graph_map_real_smul (r : ℝ) (x : D) : π (r • x) = r • π x :=
  π.toAlgHom.map_smul_of_tower r x

lemma graph_map_inverse {X : D} (hX : 0 ≤ X) :
    π (graphInverse X)=graphInverse (π X) := map_graphInverse π.toNonUnitalStarAlgHom hX

omit [PartialOrder D] [StarOrderedRing D] [PartialOrder E] [StarOrderedRing E] in
lemma graphX_map (F : D) : π (graphX V htH F) =
    measurementX (π (graphSlot V htH 0)) (π F) := by
  simp only [graphX, measurementX, graph_map_real_smul π, map_mul, map_star]

lemma graphB_map {F : D} (hF : 0 ≤ F) (i : Fin 4) : π (graphB V htH F i) =
    measurementB (fun j => π (graphSlot V htH j)) (π F) i := by
  simp only [graphB, measurementB, graph_map_real_smul π, map_mul, map_star,
    graph_map_inverse π (graphX_nonneg V htH hF), graphX_map]

theorem graph_failure_represented (htn : ‖t‖ ≤ 1) (c y : D) (hy : 0 ≤ y) (hcn : ‖c‖ ≤ 1)
    (T : Fin 4 → D) (hT : ∀ i, T i ∈ Her h) (hTn : ∀ i, ‖T i‖ ≤ 1)
    (hTX : ∀ i, T i ∈ Her (cut (graphX V htH (c*y*star c)) (1/32)))
    (hd : π (y * (1-star c*(graphP V ht htH T hT * graphP V ht htH T hT)*c)*y)=0) :
    ‖π (graphX V htH (c*y*star c))‖=‖π y‖ ∧
      ∀ i, π (graphB V htH (c*y*star c) i) = π (T i) := by
  have hF : 0 ≤ c*y*star c := star_right_conjugate_nonneg hy c
  have hm : π (CFC.sqrt t)=CFC.sqrt (π t) :=
    π.toNonUnitalStarAlgHom.map_cfcₙ NNReal.sqrt t (by fun_prop) (by simp)
      (map_continuous π) ht (map_nonneg π ht)
  have hc := graph_failure_of_identities (map_nonneg π ht)
    ((NonUnitalStarAlgHom.norm_apply_le π t).trans htn)
    (fun j => π (graphSlot V htH j)) (z := π (graphZ V ht htH T hT))
    (by simpa only [map_mul, map_star] using congrArg π (graphZ_inner V ht htH T hT hTn))
    (fun i => π (T i))
    (by simpa only [map_mul, map_star, graph_map_real_smul π, hm] using
      (congrArg π (graphSlot0_Z V ht htH T hT)))
    (fun i => by simpa only [map_mul, map_star, graph_map_real_smul π, hm] using
      (congrArg π (graphSlot_Z V ht htH T hT i)))
    (π c) (π y) (map_nonneg π hy)
    ((NonUnitalStarAlgHom.norm_apply_le π c).trans hcn) (fun i => ?_) ?_
  · simpa only [graphX_map, graphB_map π V htH hF, map_mul, map_star] using hc
  · have hmem := Her_map π.toNonUnitalStarAlgHom (hTX i)
    have hh := cut_map π.toNonUnitalStarAlgHom (graphX V htH (c*y*star c)) (1/32)
      (graphX_nonneg V htH hF).isSelfAdjoint (by norm_num)
    change π (T i) ∈ Her (π (cut (graphX V htH (c*y*star c)) (1/32))) at hmem
    change cut (π (graphX V htH (c*y*star c))) (1/32) =
      π (cut (graphX V htH (c*y*star c)) (1/32)) at hh
    rw [← hh] at hmem
    simpa only [graphX_map, map_mul, map_star] using hmem
  · simpa only [graphP, map_mul, map_star, map_sub, map_one] using hd

end RepresentedGraph

end MainGap

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.graphNonvanishingOrder
attribute [local instance] OAI.MainGap.graphNonvanishingStarOrder
attribute [local instance] OAI.MainGap.graphOperatorOrder
attribute [local instance] OAI.MainGap.graphOperatorStarOrder
theorem graph_nonvanishing {a y c : A} (ha : 0 ≤ a) (hy : 0 ≤ y) (hcn : ‖c‖ ≤ 1)
    (hp : ∀ z : A, 0 ≤ z → z ∈ Her a → ProperlyInfinite z) :
    ∃ p : A, 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
      (∀ R : HilbertRep.{u,v} A, (1/2 : ℝ) < ‖R.hom a‖ → ‖R.hom p‖=1) ∧
      (∀ R : HilbertRep.{u,v} A, R.hom (y*(1-star c*(p*p)*c)*y)=0 → ‖R.hom y‖ ≤ (1/4 : ℝ)) := by
  classical
  obtain ⟨V⟩ := (hp a ha (self_mem_Her ha)).orthogonalSlots ha 6 (by norm_num : (0:ℝ)<1/8)
  let t := ramp a (1/4) (1/2)
  have ht : 0 ≤ t := ramp_nonneg a (by norm_num)
  have htn : ‖t‖ ≤ 1 := norm_ramp_le_one a (by norm_num)
  have htH : t ∈ Her (cut a (1/8)) := by
    have hcut : cut a (1/4) ∈ Her (cut a (1/8)) := by
      have hh := cut_mem_Her (cut_nonneg a (1/8)) (1/8)
      rw [cut_cut ha (by norm_num) (by norm_num)] at hh
      convert hh using 1; norm_num
    exact Her_mono_of_mem hcut (ramp_mem_Her_cut ha (by norm_num))
  let F := c*y*star c
  have hF : 0 ≤ F := star_right_conjugate_nonneg hy c
  let X := graphX V htH F
  let B := graphB V htH F
  have hX : 0 ≤ X := graphX_nonneg V htH hF
  have hXH : X ∈ Her (cut a (1/8)) := graphX_mem V ht htH F
  have hfour : fourHer X ≤ Her (cut a (1/8)) :=
    Her_mono_of_mem (Her_mono_of_mem hXH (cut_mem_Her hX (1/32)))
  obtain ⟨T,hTn,hTX,havoid⟩ := four_avoidance_unital.{u,v} hX B (fun z hz hzm =>
    hp z hz (Her_mono_of_mem (cut_mem_Her ha (1/8)) (hfour hzm)))
  have hT : ∀ i, T i ∈ Her (cut a (1/8)) := fun i => hfour (hTX i)
  let p := graphP V ht htH T hT
  have hpn : ‖p‖ ≤ 1 := by
    have he := graphP_represented_norm V ht htH (NonUnitalStarAlgHom.id ℂ A) T hT hTn
    change ‖p‖=‖t‖ at he
    rw [he]
    exact htn
  refine ⟨p, graphP_nonneg V ht htH T hT, hpn, graphP_mem V ht htH T hT, ?_, ?_⟩
  · intro R hRa
    change ‖R.hom.toNonUnitalStarAlgHom (graphP V ht htH T hT)‖=1
    rw [graphP_represented_norm V ht htH R.hom.toNonUnitalStarAlgHom T hT hTn]
    change ‖R.hom (ramp a (1/4) (1/2))‖=1
    rw [map_ramp_sa R.hom ha.isSelfAdjoint (by norm_num)]
    exact norm_ramp_eq_one (map_nonneg R.hom ha) (by norm_num) (by norm_num) hRa.le
  · intro R hd
    by_contra! hRy
    obtain ⟨hRX,hB⟩ := graph_failure_represented R.hom V ht htH htn c y hy hcn T hT hTn hTX hd
    exact havoid R (by rw [hRX]; exact hRy)
      (fun i => (hB i).symm)
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.graphNonvanishingOrder
attribute [local instance] OAI.MainGap.graphNonvanishingStarOrder
attribute [local instance] OAI.MainGap.graphOperatorOrder
attribute [local instance] OAI.MainGap.graphOperatorStarOrder


theorem solution.{u,v} : type_of% @_root_.OAI.MainGap.graph_nonvanishing.{u,v} := @_root_.OAI.MainGap.graph_nonvanishing.{u,v}
