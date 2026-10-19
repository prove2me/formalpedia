-- Prove2me | solution 1 for OAI.MainGap.regularTransport_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:14:25.653139+00:00
-- url     : https://prove2.me/submissions/1780d31c-320c-4acc-bab5-af5372f68906

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Hereditary.lean:L559-L605
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.regularTransport_of_approx. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Theorems.Thm_OAI_MainGap_cut_sandwich_lower
import Theorems.Thm_OAI_MainGap_mem_Her_of_nonneg_le

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Hereditary ----
namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma carrier_on_sandwich {z h : A} (hzh : star z * z = star h * h) (a : A) :
    carrier z h (sandwichMap h a) = z * a * star h := by
  apply LinearMap.extendOfNorm_eq (sandwichMap_dense h)
  refine ⟨1, fun b => ?_⟩
  change ‖z * b * star h‖ ≤ 1 * ‖h * b * star h‖
  rw [one_mul, mul_assoc, mul_assoc, norm_mul_eq_of_star_mul_eq hzh]

lemma carrier_inner {z h : A} (hzh : star z * z = star h * h) (k l : Her h) :
    star (carrier z h k) * carrier z h l = star (k : A) * (l : A) := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  refine (sandwichMap_dense h).induction_on l (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [carrier_on_sandwich hzh, sandwichMap_val, star_mul, star_star]
  calc
    h * (star a * star z) * (z * b * star h) =
        h * star a * (star z * z) * b * star h := by noncomm_ring
    _ = h * star a * (star h * h) * b * star h := by rw [hzh]
    _ = h * (star a * star h) * (h * b * star h) := by noncomm_ring

lemma carrier_mul {z h : A} (hzh : star z * z = star h * h) (k l : Her h) :
    carrier z h (k * l) = carrier z h k * (l : A) := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  refine (sandwichMap_dense h).induction_on l (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have heq : sandwichMap h a * sandwichMap h b =
      sandwichMap h (a * star h * h * b) := Subtype.ext (by
        change (h * a * star h) * (h * b * star h) =
          h * (a * star h * h * b) * star h
        simp only [mul_assoc])
  rw [heq, carrier_on_sandwich hzh, carrier_on_sandwich hzh, sandwichMap_val]
  simp only [mul_assoc]

lemma conjugation_mem {z h : A} (hzh : star z * z = star h * h) (k : Her h) :
    conjugation z h k ∈ Her z := by
  refine (sandwichMap_dense h).induction_on k
    ((isClosed_Her z).preimage (conjugation z h).continuous) ?_
  intro a
  rw [conjugation_on_sandwich hzh]
  exact sandwich_mem_Her z a

lemma carrier_outer {z h : A} (hzh : star z * z = star h * h) (k l : Her h) :
    carrier z h k * star (carrier z h l) = conjugation z h (k * star l) := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  refine (sandwichMap_dense h).induction_on l (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have heq : sandwichMap h a * star (sandwichMap h b) =
      sandwichMap h (a * star h * h * star b) := Subtype.ext (by
        change (h * a * star h) * star (h * b * star h) =
          h * (a * star h * h * star b) * star h
        simp only [star_mul, star_star, mul_assoc])
  rw [heq, carrier_on_sandwich hzh, carrier_on_sandwich hzh, conjugation_on_sandwich hzh]
  simp only [star_mul, star_star, mul_assoc]

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

lemma Her_mul_le (h k : A) : Her (h * k) ≤ Her h := by
  apply closure_minimal _ (isClosed_Her h)
  rintro _ ⟨a, rfl⟩
  change (h * k) * a * star (h * k) ∈ Her h
  convert sandwich_mem_Her h (k * a * star k) using 1
  simp only [star_mul, mul_assoc]

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

lemma sqrt_Her_eq {h : A} (hh : 0 ≤ h) : Her (CFC.sqrt h) = Her h := by
  apply le_antisymm
  · exact Her_mono_of_mem (sqrt_mem_Her (self_mem_Her hh) hh)
  · apply Her_mono_of_mem
    have ht := self_mem_Her (CFC.sqrt_nonneg h)
    have hm : CFC.sqrt h * CFC.sqrt h ∈ Her (CFC.sqrt h) := (Her (CFC.sqrt h)).mul_mem ht ht
    rwa [CFC.sqrt_mul_sqrt_self h hh] at hm

lemma Her_mono {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) : Her a ≤ Her b :=
  Her_mono_of_mem (mem_Her_of_nonneg_le ha hab)

lemma smul_Her_eq {h : A} (hh : 0 ≤ h) {r : ℝ} (hr : 0 < r) :
    Her (r • h) = Her h := by
  apply le_antisymm
  · exact Her_mono_of_mem (real_smul_mem_Her (self_mem_Her hh) r)
  · apply Her_mono_of_mem
    have hm := real_smul_mem_Her (self_mem_Her (smul_nonneg hr.le hh)) r⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul] using hm

lemma square_Her_eq {h : A} (hh : 0 ≤ h) : Her (h * h) = Her h := by
  have hm : 0 ≤ h * h := by
    simpa only [(IsSelfAdjoint.of_nonneg hh).star_eq] using star_mul_self_nonneg h
  simpa only [CFC.sqrt_mul_self h hh] using (sqrt_Her_eq hm).symm

lemma Her_eq_of_order_bounds {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hl : r • a ≤ b) (hu : b ≤ R • a) :
    Her b = Her a := by
  apply le_antisymm
  · simpa only [smul_Her_eq ha hR] using Her_mono hb hu
  · simpa only [smul_Her_eq ha hr] using Her_mono (smul_nonneg hr.le ha) hl

lemma cut_nonneg (d : A) (ε : ℝ) : 0 ≤ cut d ε := by
  exact cfcₙ_nonneg (fun _ _ => le_max_right _ _)

lemma cut_transport_lower {d v s : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (ε - ‖d - star s * v * s‖) • (cut d ε * cut d ε) ≤
      cut d ε * (star s * v * s) * cut d ε := by
  let h := cut d ε
  have hh : IsSelfAdjoint h := .of_nonneg (cut_nonneg d ε)
  have hb : IsSelfAdjoint (d - star s * v * s) :=
    (IsSelfAdjoint.of_nonneg hd).sub (.of_nonneg (star_left_conjugate_nonneg hv s))
  have hbound : h * d * h - h * (star s * v * s) * h ≤
      ‖d - star s * v * s‖ • (h * h) := by
    simpa only [hh.star_eq, mul_sub, sub_mul] using
      CStarAlgebra.star_left_conjugate_le_norm_smul (a := h) (b := d - star s * v * s) hb
  calc
    (ε - ‖d - star s * v * s‖) • (h * h) =
        ε • (h * h) - ‖d - star s * v * s‖ • (h * h) := sub_smul _ _ _
    _ ≤ h * d * h - ‖d - star s * v * s‖ • (h * h) :=
      sub_le_sub_right (cut_sandwich_lower (.of_nonneg hd) hε) _
    _ ≤ h * (star s * v * s) * h := (sub_le_comm).mp hbound

theorem regularTransport_of_approx {d v s : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    {ε : ℝ} (hε : 0 < ε) (hs : ‖d - star s * v * s‖ < ε) :
    Nonempty (RegularTransport (cut d ε) v) := by
  let h := cut d ε
  let z := CFC.sqrt v * s * h
  have hhpos : 0 ≤ h := cut_nonneg d ε
  have hh : IsSelfAdjoint h := .of_nonneg hhpos
  have hvroot : IsSelfAdjoint (CFC.sqrt v) := .of_nonneg (CFC.sqrt_nonneg v)
  have hzz : star z * z = h * (star s * v * s) * h := by
    simp only [z, star_mul, hh.star_eq, hvroot.star_eq]
    calc
      h * (star s * CFC.sqrt v) * (CFC.sqrt v * s * h) =
          h * (star s * (CFC.sqrt v * CFC.sqrt v) * s) * h := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self v hv]
  have hspos : 0 ≤ star s * v * s := star_left_conjugate_nonneg hv s
  have hh2pos : 0 ≤ h * h := by simpa only [hh.star_eq] using star_mul_self_nonneg h
  have hl : (ε - ‖d - star s * v * s‖) • (h * h) ≤ star z * z := by
    rw [hzz]
    exact cut_transport_lower hd hv hε.le
  have hu : star z * z ≤ (‖star s * v * s‖ + 1) • (h * h) := by
    rw [hzz]
    calc
      h * (star s * v * s) * h ≤ ‖star s * v * s‖ • (h * h) := by
        simpa only [hh.star_eq] using
          CStarAlgebra.star_left_conjugate_le_norm_smul (a := h) (b := star s * v * s) (.of_nonneg hspos)
      _ ≤ _ := smul_le_smul_of_nonneg_right (by linarith) hh2pos
  have heq : Her (star z * z) = Her h := by
    rw [Her_eq_of_order_bounds hh2pos (star_mul_self_nonneg z)
      (sub_pos.mpr hs) (by positivity) hl hu, square_Her_eq hhpos]
  let q := CFC.sqrt (star z * z)
  have hq : star z * z = star q * q := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (star z * z))).star_eq]
    exact (CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg z)).symm
  have hqHer : Her q = Her h := (sqrt_Her_eq (star_mul_self_nonneg z)).trans heq
  have hrange : Her z ≤ Her v := by
    calc
      Her z = Her (CFC.sqrt v * (s * h)) := by simp only [z, mul_assoc]
      _ ≤ Her (CFC.sqrt v) := Her_mul_le _ _
      _ = Her v := sqrt_Her_eq hv
  let T : RegularTransport q v := {
    carrier := carrier z q
    hom := transportHom hq
    inner := carrier_inner hq
    outer := carrier_outer hq
    mul := carrier_mul hq
    image := fun k => hrange (conjugation_mem hq k) }
  exact ⟨T.restrict hqHer.ge⟩

end Order

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.regularTransport_of_approx := @_root_.OAI.MainGap.regularTransport_of_approx
