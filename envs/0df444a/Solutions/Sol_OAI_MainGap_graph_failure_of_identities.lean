-- Prove2me | solution 1 for OAI.MainGap.graph_failure_of_identities
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:50:45.077116+00:00
-- url     : https://prove2.me/submissions/3ad69df4-c2e2-4f14-9cba-4457ccb662f9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Graph.lean:L447-L517
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.graph_failure_of_identities. The node keeps its source
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

lemma continuous_graphInverseFn : Continuous graphInverseFn := by
  apply Continuous.div continuous_id
    (((continuous_const : Continuous (fun _ : ℝ => (1/32 : ℝ))).max continuous_id).pow 2)
  intro t
  exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/32) (le_max_left _ _)))

lemma graphInverseFn_zero : graphInverseFn 0 = 0 := by simp [graphInverseFn]

section InverseOrder
variable [PartialOrder A] [StarOrderedRing A]

lemma cut_mul_graphInverse {X : A} (hX : 0 ≤ X) :
    cut X (1/32) * (X * graphInverse X) = cut X (1/32) := by
  have hc : Continuous (fun t : ℝ => max (t-1/32) 0) := by fun_prop
  have h0 : (fun t : ℝ => max (t-1/32) 0) 0 = 0 := by norm_num
  have he : X * graphInverse X = cfcₙ (fun t : ℝ => t * graphInverseFn t) X := by
    simpa only [id_eq, cfcₙ_id ℝ X hX.isSelfAdjoint, cfcₙ_id' ℝ X hX.isSelfAdjoint, graphInverse] using
      (cfcₙ_mul id graphInverseFn X continuousOn_id rfl
        continuous_graphInverseFn.continuousOn graphInverseFn_zero).symm
  rw [he, cut, ← cfcₙ_mul (fun t : ℝ => max (t-1/32) 0)
    (fun t : ℝ => t * graphInverseFn t) X hc.continuousOn h0
    (continuous_id.mul continuous_graphInverseFn).continuousOn (by simp)]
  apply cfcₙ_congr
  intro t ht
  dsimp only
  by_cases h : t ≤ 1/32
  · rw [max_eq_right (sub_nonpos.mpr h), zero_mul]
  · have ht0 : t ≠ 0 := ne_of_gt (lt_trans (by norm_num) (lt_of_not_ge h))
    dsimp [graphInverseFn]
    rw [max_eq_right (le_of_not_ge h)]
    field_simp

lemma right_fixed_by_graphInverse {X S : A} (hX : 0 ≤ X)
    (hS : S ∈ Her (cut X (1/32))) : S * (X * graphInverse X) = S :=
  Her_fixed_right (cut_nonneg X (1/32)).isSelfAdjoint (cut_mul_graphInverse hX) hS

end InverseOrder
section GraphDefect
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma positive_mul_zero_of_conjugate_zero {a x : D} (ha : 0 ≤ a)
    (hz : star x * a * x = 0) : a * x = 0 := by
  have hr : CFC.sqrt a * x = 0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    calc
      star (CFC.sqrt a * x) * (CFC.sqrt a * x) =
          star x * (CFC.sqrt a * CFC.sqrt a) * x := by
        simp only [star_mul, (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, mul_assoc]
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self a ha, hz]
  rw [← CFC.sqrt_mul_sqrt_self a ha, mul_assoc, hr, mul_zero]

lemma positive_fixed_of_square_fixed {p x : D} (hp : 0 ≤ p)
    (he : p * p * x = x) : p * x = x := by
  have hi : IsUnit ((1 : D) + p) := CStarAlgebra.isUnit_of_le 1 (le_add_of_nonneg_right hp)
  apply hi.mul_left_cancel
  simp only [add_mul, one_mul, ← mul_assoc, he]
  exact add_comm _ _

lemma sqrt_fixed_of_fixed {p x : D} (hp : 0 ≤ p) (he : p*x=x) : CFC.sqrt p*x=x := by
  apply positive_fixed_of_square_fixed (CFC.sqrt_nonneg _)
  rwa [CFC.sqrt_mul_sqrt_self p hp]

lemma star_mul_le_one_of_norm_le_one {x : D} (hx : ‖x‖ ≤ 1) : star x * x ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg x)).mp
  rw [CStarRing.norm_star_mul_self]
  simpa using mul_self_le_mul_self (norm_nonneg _) hx

lemma graph_defect_forces {p c y : D} (hp : 0 ≤ p) (hpn : ‖p‖ ≤ 1)
    (hcn : ‖c‖ ≤ 1) (hy : 0 ≤ y)
    (hd : y * (1 - star c * (p*p) * c) * y = 0) :
    p * (c*y) = c*y ∧ star c * c * y = y := by
  have hp2 : 0 ≤ 1 - p*p := sub_nonneg.mpr (by
    simpa only [hp.isSelfAdjoint.star_eq] using star_mul_le_one_of_norm_le_one hpn)
  have hc2 : 0 ≤ 1 - star c*c := sub_nonneg.mpr (star_mul_le_one_of_norm_le_one hcn)
  have h₁ : 0 ≤ y*(1-star c*c)*y := by
    simpa only [hy.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg hc2 y
  have h₂ : 0 ≤ star (c*y)*(1-p*p)*(c*y) := star_left_conjugate_nonneg hp2 _
  have he : y*(1-star c*c)*y + star (c*y)*(1-p*p)*(c*y) = 0 := by
    calc
      _ = y * (1 - star c * (p*p) * c) * y := by
        simp only [star_mul, hy.isSelfAdjoint.star_eq]; noncomm_ring
      _ = 0 := hd
  have hz₁ : y*(1-star c*c)*y = 0 := le_antisymm ((le_add_of_nonneg_right h₂).trans_eq he) h₁
  have hz₂ : star (c*y)*(1-p*p)*(c*y) = 0 := le_antisymm ((le_add_of_nonneg_left h₁).trans_eq he) h₂
  have hcfix := positive_mul_zero_of_conjugate_zero hc2
    (show star y*(1-star c*c)*y=0 by simpa only [hy.isSelfAdjoint.star_eq] using hz₁)
  have hpfix := positive_mul_zero_of_conjugate_zero hp2 hz₂
  have hec : star c*c*y=y := by
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [sub_mul, one_mul] using hcfix
  have hep : p*p*(c*y)=c*y := by
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [sub_mul, one_mul] using hpfix
  exact ⟨positive_fixed_of_square_fixed hp hep, hec⟩

lemma norm_conjugate_eq_of_isometric_on {c y : D} (hy : 0 ≤ y)
    (hc : star c*c*y=y) : ‖c*y*star c‖=‖y‖ := by
  have hs := Her_fixed_left hc (sqrt_mem_Her (self_mem_Her hy) hy)
  have he : c*y*star c = (c*CFC.sqrt y)*star (c*CFC.sqrt y) := by
    simp only [star_mul, (CFC.sqrt_nonneg y).isSelfAdjoint.star_eq]
    rw [show c*y*star c = c * (CFC.sqrt y * CFC.sqrt y) * star c by rw [CFC.sqrt_mul_sqrt_self y hy]]
    simp only [mul_assoc]
  rw [he, CStarRing.norm_self_mul_star, ← CStarRing.norm_star_mul_self]
  congr 1
  calc
    star (c*CFC.sqrt y)*(c*CFC.sqrt y) = CFC.sqrt y*(star c*c*CFC.sqrt y) := by
      simp only [star_mul, (CFC.sqrt_nonneg y).isSelfAdjoint.star_eq, mul_assoc]
    _ = y := by rw [hs, CFC.sqrt_mul_sqrt_self y hy]

end GraphDefect

section GraphConstruction
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable {h a t : D} (V : OrthogonalSlots 6 h a) (ht : 0 ≤ t) (htH : t ∈ Her h)

lemma norm_compression_eq_of_fixed {z F : D} (hF : 0 ≤ F) (hfix : z*star z*F=F) :
    ‖star z*F*z‖=‖F‖ := by
  have hs := Her_fixed_left hfix (sqrt_mem_Her (self_mem_Her hF) hF)
  calc
    ‖star z*F*z‖ = ‖star (CFC.sqrt F*z)*(CFC.sqrt F*z)‖ := by
      congr 1
      simp only [star_mul, (CFC.sqrt_nonneg F).isSelfAdjoint.star_eq]
      calc
        star z*F*z = star z*(CFC.sqrt F*CFC.sqrt F)*z := by rw [CFC.sqrt_mul_sqrt_self F hF]
        _ = _ := by noncomm_ring
    _ = ‖(CFC.sqrt F*z)*star (CFC.sqrt F*z)‖ := by
      rw [CStarRing.norm_star_mul_self, CStarRing.norm_self_mul_star]
    _ = ‖F‖ := by
      congr 1
      calc
        (CFC.sqrt F*z)*star (CFC.sqrt F*z) = CFC.sqrt F*(z*star z*CFC.sqrt F) := by
          simp only [star_mul, (CFC.sqrt_nonneg F).isSelfAdjoint.star_eq, mul_assoc]
        _ = F := by rw [hs, CFC.sqrt_mul_sqrt_self F hF]

end GraphConstruction

section AbstractMeasurements
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem graph_failure_of_identities {t z : D} (ht : 0 ≤ t) (htn : ‖t‖ ≤ 1)
    (w : Fin 6 → D) (hz : star z*z=t) (T : Fin 4 → D)
    (hW₀ : star (w 0)*z=(1/4 : ℝ) • (t*CFC.sqrt t))
    (hWi : ∀ i : Fin 4, star (w i.castSucc.succ)*z=(1/4 : ℝ) • (t*T i*CFC.sqrt t))
    (c y : D) (hy : 0 ≤ y) (hcn : ‖c‖ ≤ 1)
    (hTX : ∀ i, T i ∈ Her (cut (measurementX (w 0) (c*y*star c)) (1/32)))
    (hd : y*(1-star c*((z*star z)*(z*star z))*c)*y=0) :
    ‖measurementX (w 0) (c*y*star c)‖=‖y‖ ∧ ∀ i, measurementB w (c*y*star c) i=T i := by
  let p := z*star z
  let F := c*y*star c
  let H₀ := star z*F*z
  have hp : 0 ≤ p := mul_star_self_nonneg z
  have hpn : ‖p‖ ≤ 1 := by
    change ‖z*star z‖ ≤ 1
    rw [CStarRing.norm_self_mul_star, ← CStarRing.norm_star_mul_self, hz]
    exact htn
  have hdf : y*(1-star c*(p*p)*c)*y=0 := hd
  obtain ⟨hpc,hcc⟩ := graph_defect_forces hp hpn hcn hy hdf
  have hF : 0 ≤ F := star_right_conjugate_nonneg hy c
  have hFH : 0 ≤ H₀ := star_left_conjugate_nonneg hF z
  have hpF : p*F=F := by
    change p*(c*y*star c)=c*y*star c
    rw [← mul_assoc, hpc]
  have hFp : F*p=F := by
    simpa only [star_mul, hF.isSelfAdjoint.star_eq, hp.isSelfAdjoint.star_eq] using congrArg star hpF
  have heF : F=z*H₀*star z := by
    calc
      F = p*F*p := by rw [hpF,hFp]
      _ = z*H₀*star z := by dsimp [p,H₀]; noncomm_ring
  have htH₀ : t*H₀=H₀ := by
    calc
      t*H₀ = star z*(p*F)*z := by rw [← hz]; dsimp [H₀,p]; noncomm_ring
      _ = H₀ := by rw [hpF]
  have hH₀t : H₀*t=H₀ := by
    simpa only [star_mul, hFH.isSelfAdjoint.star_eq, ht.isSelfAdjoint.star_eq] using congrArg star htH₀
  have hrH₀ : CFC.sqrt t*H₀=H₀ := sqrt_fixed_of_fixed ht htH₀
  have hH₀r : H₀*CFC.sqrt t=H₀ := by
    simpa only [star_mul, hFH.isSelfAdjoint.star_eq, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq]
      using congrArg star hrH₀
  have hzW : star z*w 0=(1/4 : ℝ) • (CFC.sqrt t*t) := by
    simpa only [star_mul, star_star, star_smul, star_trivial,
      ht.isSelfAdjoint.star_eq, (CFC.sqrt_nonneg t).isSelfAdjoint.star_eq] using congrArg star hW₀
  have hW (i : Fin 6) : star (w i)*F*w 0 =
      (star (w i)*z)*H₀*(star z*w 0) := by
    rw [heF]; noncomm_ring
  have hXeq : measurementX (w 0) F=H₀ := by
    rw [measurementX, hW 0, hW₀, hzW]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [show (t*CFC.sqrt t)*H₀*(CFC.sqrt t*t)=H₀ by
      rw [mul_assoc t (CFC.sqrt t) H₀, hrH₀, htH₀, ← mul_assoc, hH₀r, hH₀t]]
    norm_num
  have hX : 0 ≤ measurementX (w 0) F := smul_nonneg (by norm_num) (star_left_conjugate_nonneg hF (w 0))
  refine ⟨?_, fun i => ?_⟩
  · rw [hXeq, norm_compression_eq_of_fixed hF hpF, norm_conjugate_eq_of_isometric_on hy hcc]
  · have hTi := hTX i
    change T i ∈ Her (cut (measurementX (w 0) F) (1/32)) at hTi
    have htX : t*measurementX (w 0) F=measurementX (w 0) F := by rw [hXeq]; exact htH₀
    have htT : t*T i=T i := Her_fixed_left htX (Her_mono_of_mem (cut_mem_Her hX _) hTi)
    have hright := right_fixed_by_graphInverse hX hTi
    change measurementB w F i=T i
    rw [measurementB, hW i.castSucc.succ, hWi i, hzW]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    have he : (t*T i*CFC.sqrt t)*H₀*(CFC.sqrt t*t)*graphInverse (measurementX (w 0) F) = T i := by
      calc
        _ = (t*T i)*H₀*graphInverse (measurementX (w 0) F) := by
          rw [mul_assoc (t*T i) (CFC.sqrt t) H₀, hrH₀,
            mul_assoc (t*T i) H₀ (CFC.sqrt t*t), ← mul_assoc H₀,
            hH₀r, hH₀t]
        _ = T i := by rw [htT, ← hXeq, mul_assoc]; exact hright
    rw [he]
    norm_num

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

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.graph_failure_of_identities := @_root_.OAI.MainGap.graph_failure_of_identities
