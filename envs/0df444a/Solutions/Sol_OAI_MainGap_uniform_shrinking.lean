-- Prove2me | solution 1 for OAI.MainGap.uniform_shrinking
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:17:17.497178+00:00
-- url     : https://prove2.me/submissions/8d1f9839-a6d6-4812-bb21-fdf36cf37701

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Products.lean:L243-L287
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.uniform_shrinking. The node keeps its source
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
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Products
import Theorems.Thm_OAI_MainGap_ProperlyInfinite_finite_copies
import Theorems.Thm_OAI_MainGap_cutInverseFn_bound
import Theorems.Thm_OAI_MainGap_cut_cut
import Theorems.Thm_OAI_MainGap_lp_nonneg_iff
import Theorems.Thm_OAI_MainGap_norm_sub_cut_le
import Theorems.Thm_OAI_MainGap_orthogonalSlots_of_comparison
import Theorems.Thm_OAI_MainGap_shrinking_nonunital

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

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

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Comparison ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

attribute [local instance] OAI.MainGap.positivityOrder
attribute [local instance] OAI.MainGap.positivityStarOrder
lemma finiteCuntzLE_iff_closure {m n : ℕ} (d : CStarMatrix (Fin n) (Fin n) A)
    (v : CStarMatrix (Fin m) (Fin m) A) :
    FiniteCuntzLE d v ↔ d ∈ closure (Set.range
      (fun r : CStarMatrix (Fin m) (Fin n) A => r.conjTranspose * v * r)) := by
  rw [mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨_, fun j => ⟨r j, rfl⟩, hr⟩
  · rintro ⟨x, hx, ht⟩
    choose r hr using hx
    exact ⟨r, by simpa only [hr] using ht⟩

lemma finiteCuntzLE_of_forall_approx {m n : ℕ} {d : CStarMatrix (Fin n) (Fin n) A}
    {v : CStarMatrix (Fin m) (Fin m) A}
    (h : ∀ ε > 0, ∃ r : CStarMatrix (Fin m) (Fin n) A,
      ‖d - r.conjTranspose * v * r‖ < ε) : FiniteCuntzLE d v := by
  rw [finiteCuntzLE_iff_closure, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hr⟩ := h ε hε
  exact ⟨_, ⟨r, rfl⟩, by simpa only [dist_eq_norm] using hr⟩

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
namespace RegularTransport
variable {n : ℕ} {h v : A} (i₀ : Fin n)
    (T : RegularTransport (diagonalCorner n h) (entry i₀ i₀ v))

end RegularTransport

theorem ProperlyInfinite.orthogonalSlots {d : A} (hd : 0 ≤ d) (hp : ProperlyInfinite d)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) : Nonempty (OrthogonalSlots n (cut d ε) d) :=
  orthogonalSlots_of_comparison hd hd (hp.finite_copies n) hε

namespace OrthogonalSlots
variable {n : ℕ} {h v : A} (S : OrthogonalSlots n h v)

lemma represented_norm {B : Type*} [NonUnitalCStarAlgebra B]
    (π : A →⋆ₙₐ[ℂ] B) (i : Fin n) (k : Her h) :
    ‖π (S.carrier i k)‖ = ‖π (k : A)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [pow_two, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul,
    S.inner, ite_true]

lemma norm_carrier (i : Fin n) (k : Her h) : ‖S.carrier i k‖ = ‖(k : A)‖ :=
  S.represented_norm (NonUnitalStarAlgHom.id ℂ A) i k

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

lemma map_cut {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (π : A →⋆ₙₐ[ℂ] B) {a : A} (ha : 0 ≤ a) {l : ℝ} (hl : 0 ≤ l) :
    π (cut a l) = cut (π a) l :=
  π.map_cfcₙ (fun t : ℝ => max (t-l) 0) a
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    (by simp [max_eq_right (neg_nonpos.mpr hl)]) (map_continuous π)
    (.of_nonneg ha) (.of_nonneg (map_nonneg π ha))

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

lemma Her_fixed_left {h t : A} (ht : t * h = h) {k : A} (hk : k ∈ Her h) : t * k = k := by
  have hc : IsClosed {k : A | t * k = k} := isClosed_eq (by fun_prop) continuous_id
  apply closure_minimal (s := Set.range (fun a : A => h * a * star h)) _ hc hk
  rintro k ⟨a, rfl⟩
  change t * (h * a * star h) = h * a * star h
  simp only [← mul_assoc, ht]

section UnitalCutBounds
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end UnitalCutBounds

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

end GraphAlgebra
end OrthogonalSlots

section UnitalGraph
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end UnitalGraph
lemma Her_fixed_right {h t : A} (hh : IsSelfAdjoint h) (ht : h * t = h)
    {k : A} (hk : k ∈ Her h) : k * t = k := by
  have he : star t * h = h := by
    simpa only [star_mul, hh.star_eq] using congrArg star ht
  have hs := Her_fixed_left he (StarMemClass.star_mem (s := Her h) hk)
  simpa only [star_mul, star_star] using congrArg star hs

section InverseOrder
variable [PartialOrder A] [StarOrderedRing A]

end InverseOrder
section GraphDefect
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end GraphDefect

section GraphConstruction
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable {h a t : D} (V : OrthogonalSlots 6 h a) (ht : 0 ≤ t) (htH : t ∈ Her h)

end GraphConstruction

section AbstractMeasurements
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

end AbstractMeasurements

section RepresentedGraph
variable {D E : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]
variable (π : D →⋆ₐ[ℂ] E) {h a t : D} (V : OrthogonalSlots 6 h a)
  (ht : 0 ≤ t) (htH : t ∈ Her h)

end RepresentedGraph

end MainGap

namespace MainGap
universe u v
variable {A : Type u} [CStarAlgebra A]
attribute [local instance] OAI.MainGap.graphNonvanishingOrder
attribute [local instance] OAI.MainGap.graphNonvanishingStarOrder
attribute [local instance] OAI.MainGap.graphOperatorOrder
attribute [local instance] OAI.MainGap.graphOperatorStarOrder
end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Compression ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma continuous_cutInverseFn {δ : ℝ} (hδ : 0 < δ) : Continuous (cutInverseFn δ) := by
  exact continuous_id.div (((continuous_const.max continuous_id).pow 2))
    (fun t => pow_ne_zero _ (ne_of_gt (hδ.trans_le (le_max_left _ _))))

lemma cutInverseFn_zero (δ : ℝ) : cutInverseFn δ 0=0 := by simp [cutInverseFn]

lemma norm_cutInverse_le {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    ‖cutInverse a δ‖ ≤ 1/δ := by
  apply norm_cfcₙ_le
  intro t ht
  have hb := cutInverseFn_bound hδ (quasispectrum_nonneg_of_nonneg a ha t ht)
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

lemma cut_mul_cutInverse {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    cut a δ * (cutInverse a δ * a) = cut a δ := by
  have hc : Continuous (fun t : ℝ => max (t-δ) 0) := by fun_prop
  have h0 : (fun t : ℝ => max (t-δ) 0) 0=0 := by
    simp [max_eq_right (neg_nonpos.mpr hδ.le)]
  have he : cutInverse a δ*a = cfcₙ (fun t : ℝ => cutInverseFn δ t*t) a := by
    simpa only [id_eq, cfcₙ_id ℝ a ha.isSelfAdjoint, cfcₙ_id' ℝ a ha.isSelfAdjoint, cutInverse] using
      (cfcₙ_mul (cutInverseFn δ) id a (continuous_cutInverseFn hδ).continuousOn
        (cutInverseFn_zero δ) continuousOn_id rfl).symm
  rw [he, cut, ← cfcₙ_mul (fun t : ℝ => max (t-δ) 0)
    (fun t : ℝ => cutInverseFn δ t*t) a hc.continuousOn h0
    ((continuous_cutInverseFn hδ).mul continuous_id).continuousOn (by simp [cutInverseFn_zero])]
  apply cfcₙ_congr
  intro t _
  dsimp only
  by_cases ht : t ≤ δ
  · rw [max_eq_right (sub_nonpos.mpr ht), zero_mul]
  · have ht0 : t ≠ 0 := ne_of_gt (hδ.trans (lt_of_not_ge ht))
    dsimp [cutInverseFn]
    rw [max_eq_right (le_of_not_ge ht)]
    field_simp

lemma Her_right_fixed_cutInverse {a x : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ)
    (hx : x ∈ Her (cut a δ)) : x*(cutInverse a δ*a)=x :=
  Her_fixed_right (cut_nonneg a δ).isSelfAdjoint (cut_mul_cutInverse ha hδ) hx

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Products ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.boundedSlotsOrder
attribute [local instance] OAI.MainGap.boundedSlotsStarOrder
lemma cut_le_self {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 ≤ δ) : cut a δ ≤ a := by
  have he : cfcₙ (fun t : ℝ => t) a = a := cfcₙ_id ℝ a ha.isSelfAdjoint
  conv_rhs => rw [← he]
  change cfcₙ (fun t : ℝ => max (t-δ) 0) a ≤ cfcₙ (fun t : ℝ => t) a
  exact cfcₙ_mono (fun t ht => max_le (by linarith) (quasispectrum_nonneg_of_nonneg a ha t ht))
    ((continuous_id.sub continuous_const).max continuous_const).continuousOn
    continuousOn_id (by simp [max_eq_right (neg_nonpos.mpr hδ)]) rfl

lemma norm_cut_le {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 ≤ δ) : ‖cut a δ‖ ≤ ‖a‖ :=
  CStarAlgebra.norm_le_norm_of_le_of_nonneg (cut_le_self ha hδ) (cut_nonneg a δ)

lemma cutInverse_nonneg {a : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ cutInverse a δ := by
  apply cfcₙ_nonneg
  intro t ht
  exact (cutInverseFn_bound hδ (quasispectrum_nonneg_of_nonneg a ha t ht)).1

lemma fixed_of_outer_fixed {F r : A} (h : F*(r*star r)=r*star r) : F*r=r := by
  apply sub_eq_zero.mp
  apply (CStarRing.mul_star_self_eq_zero_iff _).mp
  have hs : r*star r*star F = r*star r := by
    simpa only [star_mul, star_star, mul_assoc] using congrArg star h
  calc
    (F*r-r)*star (F*r-r) = F*(r*star r)*star F - F*(r*star r) - r*star r*star F+r*star r := by
      simp only [star_sub, star_mul]
      noncomm_ring
    _ = 0 := by rw [h, hs]; noncomm_ring

lemma cutInverse_fixed_carrier {a r : A} (ha : 0 ≤ a) {δ : ℝ} (hδ : 0 < δ)
    (hr : r*star r ∈ Her (cut a δ)) : (cutInverse a δ*a)*r=r := by
  have hFsa : IsSelfAdjoint (cutInverse a δ*a) := by
    have hcomm : Commute (cutInverse a δ) a := (Commute.refl a).cfcₙ_real (cutInverseFn δ)
    exact (IsSelfAdjoint.commute_iff (cutInverse_nonneg ha hδ).isSelfAdjoint ha.isSelfAdjoint).mp hcomm
  have ht := Her_right_fixed_cutInverse ha hδ hr
  have hs : (cutInverse a δ*a)*(r*star r)=r*star r := by
    simpa only [star_mul, star_star, hFsa.star_eq] using congrArg star ht
  exact fixed_of_outer_fixed hs

theorem bounded_two_slots (hp : PropertyP A) {d : A} (hd : 0 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Fin 2 → A,
      (∀ i j, star (s i)*d*s j = if i=j then cut d (δ+δ) else 0) ∧
      (∀ i, ‖s i‖ ≤ Real.sqrt (1/δ) * Real.sqrt ‖d‖) := by
  let h := cut d δ
  let k := cut h δ
  have hh : 0 ≤ h := cut_nonneg d δ
  have hk : 0 ≤ k := cut_nonneg h δ
  obtain ⟨S⟩ := (hp h hh).orthogonalSlots hh 2 hδ
  let z : Her k := ⟨CFC.sqrt k, sqrt_mem_Her (self_mem_Her hk) hk⟩
  let r := fun i => S.carrier i z
  let v := CFC.sqrt (cutInverse d δ)
  have hv : 0 ≤ cutInverse d δ := cutInverse_nonneg hd hδ
  have hvr : ∀ i, (cutInverse d δ*d)*r i=r i := fun i =>
    cutInverse_fixed_carrier hd hδ (S.outer i i z z)
  have hvd : star v*d*v=cutInverse d δ*d := by
    have hc : Commute v d := by
      exact ((Commute.refl d).cfcₙ_real (cutInverseFn δ)).cfcₙ_nnreal NNReal.sqrt
    rw [(CFC.sqrt_nonneg (cutInverse d δ)).isSelfAdjoint.star_eq]
    calc
      v*d*v = v*v*d := by rw [mul_assoc, ← hc.eq, ← mul_assoc]
      _ = cutInverse d δ*d := by rw [show v*v=cutInverse d δ from CFC.sqrt_mul_sqrt_self _ hv]
  refine ⟨fun i => v*r i, ?_, ?_⟩
  · intro i j
    calc
      star (v*r i)*d*(v*r j) = star (r i)*(star v*d*v)*r j := by simp only [star_mul]; noncomm_ring
      _ = star (r i)*r j := by rw [hvd, mul_assoc, hvr]
      _ = if i=j then cut d (δ+δ) else 0 := by
        rw [S.inner]
        have he : k=cut d (δ+δ) := cut_cut hd hδ.le hδ.le
        change (if i=j then star (CFC.sqrt k)*CFC.sqrt k else 0) = if i=j then cut d (δ+δ) else 0
        rw [(CFC.sqrt_nonneg k).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ hk, he]
  · intro i
    calc
      ‖v*r i‖ ≤ ‖v‖*‖r i‖ := norm_mul_le _ _
      _ ≤ Real.sqrt (1/δ) * Real.sqrt ‖d‖ := by
        apply mul_le_mul
        · rw [CFC.norm_sqrt _ hv]
          exact Real.sqrt_le_sqrt (norm_cutInverse_le hd hδ)
        · rw [S.norm_carrier, CFC.norm_sqrt _ hk]
          exact Real.sqrt_le_sqrt ((norm_cut_le hh hδ.le).trans (norm_cut_le hd hδ.le))
        · exact norm_nonneg _
        · positivity
end MainGap

namespace MainGap
open scoped ENNReal
variable {I : Type*} {E : I → Type*} [∀ i, NonUnitalCStarAlgebra (E i)]
attribute [local instance] OAI.MainGap.productFactorOrder
attribute [local instance] OAI.MainGap.productFactorStarOrder
attribute [local instance] OAI.MainGap.boundedProductOrder
attribute [local instance] OAI.MainGap.boundedProductStarOrder
theorem propertyP_lp (hp : ∀ i, PropertyP (E i)) : PropertyP (lp E ∞) := by
  intro d hd
  apply finiteCuntzLE_of_forall_approx
  intro ε hε
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd' : ∀ i, 0 ≤ d i := (lp_nonneg_iff d).mp hd
  choose s hs hn using fun i => bounded_two_slots (hp i) (hd' i) hδ
  have hb (i : I) (j : Fin 2) :
      ‖s i j‖ ≤ Real.sqrt (1/δ)*Real.sqrt ‖d‖ :=
    (hn i j).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (lp.norm_apply_le_norm ENNReal.top_ne_zero d i)) (Real.sqrt_nonneg _))
  let S : Fin 2 → lp E ∞ := fun j => lpBuild (fun i => s i j) _ (fun i => hb i j)
  let R : CStarMatrix (Fin 1) (Fin 2) (lp E ∞) := CStarMatrix.ofMatrix (fun _ j => S j)
  have he : R.conjTranspose * scalarCorner d * R = doubleCorner (cut d (δ+δ)) := by
    apply CStarMatrix.ext
    intro j k
    apply lp.ext
    funext i
    change ((∑ l : Fin 1, (∑ m : Fin 1, star (R m j)*scalarCorner d m l)*R l k) i) =
      (Matrix.diagonal (fun _ : Fin 2 => cut d (δ+δ)) j k) i
    simp only [Fin.sum_univ_one]
    change star (s i j)*d i*s i k=(if j=k then cut d (δ+δ) else 0) i
    rw [hs i j k]
    split_ifs with hjk
    · exact (map_cut (lpEval i) hd (show 0 ≤ δ+δ by positivity)).symm
    · rfl
  refine ⟨R,?_⟩
  rw [he]
  change ‖diagonalHom 2 d - diagonalHom 2 (cut d (δ+δ))‖ < ε
  rw [← map_sub]
  exact ((NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := lp E ∞) 2) _).trans
    (norm_sub_cut_le hd (by positivity))).trans_lt (by dsimp [δ]; linarith)

end MainGap

namespace MainGap
open scoped ENNReal
variable {I : Type*} {E : I → Type*} [∀ i, NonUnitalCStarAlgebra (E i)] [DecidableEq I]

lemma lp_single_mem_Her (i : I) {p : lp E ∞} {x : E i} (hx : x ∈ Her (p i)) :
    lp.single ∞ i x ∈ Her p := by
  have hc : IsClosed {x : E i | lp.single ∞ i x ∈ Her p} :=
    (isClosed_Her p).preimage (lp.isometry_single i).continuous
  apply closure_minimal (s := Set.range (fun b : E i => p i*b*star (p i))) _ hc hx
  rintro x ⟨b,rfl⟩
  change lp.single ∞ i (p i*b*star (p i)) ∈ Her p
  have he : lp.single ∞ i (p i*b*star (p i)) = p*lp.single ∞ i b*star p := by
    apply lp.ext
    funext j
    by_cases hj : j=i
    · subst j
      change lp.single ∞ i (p i*b*star (p i)) i = p i*lp.single ∞ i b i*star (p i)
      simp only [lp.single_apply_self]
    · change lp.single ∞ i (p i*b*star (p i)) j = p j*lp.single ∞ i b j*star (p j)
      rw [lp.single_apply_ne _ _ _ hj, lp.single_apply_ne _ _ _ hj, mul_zero, zero_mul]
  rw [he]
  exact sandwich_mem_Her p _

lemma HerCompression.lp_eval {p q c : lp E ∞} {κ : ℝ}
    (h : HerCompression p q c κ) (i : I) : HerCompression (p i) (q i) (c i) κ := by
  intro x hx k hk
  have hi := h _ (lp_single_mem_Her i hx) _ (lp_single_mem_Her i hk)
  have he : lp.single ∞ i x*c*lp.single ∞ i k = lp.single ∞ i (x*c i*k) := by
    apply lp.ext
    funext j
    by_cases hj : j=i
    · subst j
      change lp.single ∞ i x i*c i*lp.single ∞ i k i=lp.single ∞ i (x*c i*k) i
      simp only [lp.single_apply_self]
    · change lp.single ∞ i x j*c j*lp.single ∞ i k j=lp.single ∞ i (x*c i*k) j
      rw [lp.single_apply_ne _ _ _ hj, lp.single_apply_ne _ _ _ hj,
        lp.single_apply_ne _ _ _ hj, zero_mul, mul_zero]
  rw [he, lp.norm_single (by simp : (0 : ℝ≥0∞)<∞),
    lp.norm_single (by simp : (0 : ℝ≥0∞)<∞),
    lp.norm_single (by simp : (0 : ℝ≥0∞)<∞)] at hi
  exact hi
end MainGap

namespace MainGap
open scoped ENNReal
universe u
variable {A : Type u} [NonUnitalCStarAlgebra A]
attribute [local instance] OAI.MainGap.sequenceFactorOrder
attribute [local instance] OAI.MainGap.sequenceFactorStarOrder
attribute [local instance] OAI.MainGap.boundedSequenceOrder
attribute [local instance] OAI.MainGap.boundedSequenceStarOrder
lemma NormSignal.lp_eval {a p : lp (fun _ : ℕ => A) ∞} (h : NormSignal a p) (i : ℕ) :
    NormSignal (a i) (p i) := by
  intro R hR
  let S : HilbertRep.{u,u} (Unitization ℂ (lp (fun _ : ℕ => A) ∞)) :=
    { R with hom := R.hom.comp (Unitization.starMap (lpEval i)) }
  have he (x : lp (fun _ : ℕ => A) ∞) :
      S.hom (x : Unitization ℂ (lp (fun _ : ℕ => A) ∞)) =
        R.hom (x i : Unitization ℂ A) := by
    simp [S]
  have hr : (1/2:ℝ)<‖S.hom (a : Unitization ℂ (lp (fun _ : ℕ => A) ∞))‖ := by
    rwa [he]
  have ht := h S hr
  rwa [he] at ht

theorem uniform_shrinking (hp : PropertyP A) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ a y c : A, 0 ≤ a → ‖a‖ ≤ 1 → 0 ≤ y → ‖y‖ ≤ 1 → ‖c‖ ≤ 1 →
        ∃ p q : A, 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ p ∈ Her a ∧
          0 ≤ q ∧ ‖q‖ ≤ 1 ∧ q ∈ Her y ∧
          HerCompression p q c θ ∧ NormSignal a p ∧ NormSignal y q := by
  classical
  by_contra hn
  push Not at hn
  let θ : ℕ → ℝ := fun n => 1-1/((n:ℝ)+2)
  have hθ0 (n : ℕ) : 0 < θ n := by
    dsimp [θ]
    have h : (1:ℝ)/((n:ℝ)+2)<1 := (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hθ1 (n : ℕ) : θ n < 1 := by
    dsimp [θ]
    have : 0 < (1:ℝ)/((n:ℝ)+2) := by positivity
    linarith
  choose a y c ha han hy hyn hcn hfail using fun n => hn (θ n) (hθ0 n) (hθ1 n)
  let a' : lp (fun _ : ℕ => A) ∞ := lpBuild a 1 han
  let y' : lp (fun _ : ℕ => A) ∞ := lpBuild y 1 hyn
  let c' : lp (fun _ : ℕ => A) ∞ := lpBuild c 1 hcn
  have ha' : 0 ≤ a' := (lp_nonneg_iff a').mpr ha
  have hy' : 0 ≤ y' := (lp_nonneg_iff y').mpr hy
  have hyn' : ‖y'‖ ≤ 1 := lp.norm_le_of_forall_le (by norm_num) hyn
  have hcn' : ‖c'‖ ≤ 1 := lp.norm_le_of_forall_le (by norm_num) hcn
  obtain ⟨p,q,κ,hp0,hpn,hpH,hq0,hqn,hqH,hκ0,hκ1,hcomp,hps,hqs⟩ :=
    shrinking_nonunital (propertyP_lp (fun _ : ℕ => hp)) ha' hy' hyn' hcn'
  obtain ⟨n,hnκ⟩ := exists_nat_gt (1/(1-κ))
  have hκθ : κ ≤ θ n := by
    have hn2 : 1/(1-κ) < (n:ℝ)+2 := by linarith
    have hmul : (1:ℝ) < ((n:ℝ)+2)*(1-κ) := (div_lt_iff₀ (by linarith)).mp hn2
    have hdiv : 1/((n:ℝ)+2) < 1-κ := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
    dsimp [θ]; linarith
  apply hfail n (p n) (q n)
  · exact (lp_nonneg_iff p).mp hp0 n
  · exact (lp.norm_apply_le_norm ENNReal.top_ne_zero p n).trans hpn
  · exact Her_map (lpEval n) hpH
  · exact (lp_nonneg_iff q).mp hq0 n
  · exact (lp.norm_apply_le_norm ENNReal.top_ne_zero q n).trans hqn
  · exact Her_map (lpEval n) hqH
  · intro x hx k hk
    exact ((hcomp.lp_eval n) x hx k hk).trans (by gcongr)
  · exact hps.lp_eval n
  · exact hqs.lp_eval n
end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
open scoped ENNReal
attribute [local instance] OAI.MainGap.sequenceFactorOrder
attribute [local instance] OAI.MainGap.sequenceFactorStarOrder
attribute [local instance] OAI.MainGap.boundedSequenceOrder
attribute [local instance] OAI.MainGap.boundedSequenceStarOrder


theorem solution.{u} : type_of% @_root_.OAI.MainGap.uniform_shrinking.{u} := @_root_.OAI.MainGap.uniform_shrinking.{u}
