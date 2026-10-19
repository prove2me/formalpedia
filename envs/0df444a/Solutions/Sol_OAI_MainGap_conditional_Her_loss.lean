-- Prove2me | solution 1 for OAI.MainGap.conditional_Her_loss
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:04:08.029986+00:00
-- url     : https://prove2.me/submissions/49031caa-5813-438e-93a9-5eb564ed7e7e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Compression.lean:L191-L212
-- (upload_full_project.md Phase 4): solution for node OAI.MainGap.conditional_Her_loss. The node keeps its source
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
import Theorems.Thm_OAI_MainGap_conditional_defect_bounds
import Theorems.Thm_OAI_MainGap_cut_sqrt_lower

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

lemma cut_nonneg (d : A) (ε : ℝ) : 0 ≤ cut d ε := by
  exact cfcₙ_nonneg (fun _ _ => le_max_right _ _)

end Order

end MainGap

end

end OAI

-- ---- from OAI.Analysis.CStarAlgebra.PureInfiniteness.Compression ----
-- Lean 4.34 name (arguments swapped) of CStarAlgebra.norm_le_norm_of_nonneg_of_le in Mathlib 0df444a.
private theorem CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

namespace MainGap
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_mul_factor_of_order {m z : A} {r : ℝ} (hr : 0 ≤ r)
    (h : star (m*z) * (m*z) ≤ r^2 • (star z*z)) (b : A) :
    ‖m*(z*b)‖ ≤ r*‖z*b‖ := by
  have ho := star_left_conjugate_le_conjugate h b
  have ht : star (m*(z*b))*(m*(z*b)) ≤ r^2 • (star (z*b)*(z*b)) := by
    simpa only [star_mul, mul_assoc, mul_smul_comm, smul_mul_assoc] using ho
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg ht (star_mul_self_nonneg _)
  rw [CStarRing.norm_star_mul_self, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg r), CStarRing.norm_star_mul_self] at hn
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp
  calc
    ‖m*(z*b)‖^2 = ‖m*(z*b)‖*‖m*(z*b)‖ := pow_two _
    _ ≤ r^2 * (‖z*b‖*‖z*b‖) := hn
    _ = (r*‖z*b‖)^2 := by ring

lemma norm_mul_Her_of_order {m z : A} {r : ℝ} (hr : 0 ≤ r)
    (h : star (m*z) * (m*z) ≤ r^2 • (star z*z))
    {k : A} (hk : k ∈ Her (z*star z)) : ‖m*k‖ ≤ r*‖k‖ := by
  have hc : IsClosed {k : A | ‖m*k‖ ≤ r*‖k‖} := isClosed_le (by fun_prop) (by fun_prop)
  apply closure_minimal (s := Set.range (fun b : A => (z*star z)*b*star (z*star z))) _ hc hk
  rintro k ⟨b, rfl⟩
  change ‖m*((z*star z)*b*star (z*star z))‖ ≤ r*‖(z*star z)*b*star (z*star z)‖
  simpa only [star_mul, star_star, mul_assoc] using
    norm_mul_factor_of_order hr h (star z*b*(z*star z))

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma conditional_order_loss {p y c d : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hd : 0 ≤ d) (_hyd : d ≤ y*y) (hy₂ : y*y ≤ 1)
    (he : d=y*(1-star c*(p*p)*c)*y) {δ : ℝ} (hδ : 0 ≤ δ) :
    let z := y*CFC.sqrt (cut d δ)
    star ((p*c)*z)*((p*c)*z) ≤ (1-δ) • (star z*z) := by
  let s := CFC.sqrt (cut d δ)
  let z := y*s
  have hs : IsSelfAdjoint s := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hZ : star z*z ≤ cut d δ := by
    calc
      star z*z = s*(y*y)*s := by
        dsimp [z]
        simp only [star_mul, hs.star_eq, hy.isSelfAdjoint.star_eq, mul_assoc]
      _ ≤ s*1*s := by
        simpa only [hs.star_eq] using star_left_conjugate_le_conjugate hy₂ s
      _ = cut d δ := by
        rw [mul_one]
        exact CFC.sqrt_mul_sqrt_self (cut d δ) (cut_nonneg d δ)
  have hδZ : δ • (star z*z) ≤ s*d*s :=
    (smul_le_smul_of_nonneg_left hZ hδ).trans (cut_sqrt_lower hd hδ)
  have hid : star ((p*c)*z)*((p*c)*z) = star z*z-s*d*s := by
    dsimp [z]
    rw [he]
    simp only [star_mul, hp.isSelfAdjoint.star_eq, hy.isSelfAdjoint.star_eq, hs.star_eq]
    noncomm_ring
  change star ((p*c)*z)*((p*c)*z) ≤ (1-δ) • (star z*z)
  rw [hid, sub_smul, one_smul]
  exact sub_le_sub_left hδZ _

lemma conditional_Her_loss {p y c : A} (hp : 0 ≤ p) (hy : 0 ≤ y)
    (hpn : ‖p‖ ≤ 1) (hyn : ‖y‖ ≤ 1) (hcn : ‖c‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    let d := y*(1-star c*(p*p)*c)*y
    let q := y*cut d δ*y
    ∀ k : A, k ∈ Her q → ‖p*c*k‖ ≤ Real.sqrt (1-δ) * ‖k‖ := by
  let d := y*(1-star c*(p*p)*c)*y
  let z := y*CFC.sqrt (cut d δ)
  have hb := conditional_defect_bounds hp hy hpn hyn hcn
  have hh : star ((p*c)*z)*((p*c)*z) ≤ (Real.sqrt (1-δ))^2 • (star z*z) := by
    rw [Real.sq_sqrt (sub_nonneg.mpr hδ₁)]
    exact conditional_order_loss hp hy hb.1 hb.2.1 hb.2.2 rfl hδ
  have hq : z*star z=y*cut d δ*y := by
    dsimp [z]
    simp only [star_mul, hy.isSelfAdjoint.star_eq, (CFC.sqrt_nonneg (cut d δ)).isSelfAdjoint.star_eq]
    calc
      y*CFC.sqrt (cut d δ)*(CFC.sqrt (cut d δ)*y) =
          y*(CFC.sqrt (cut d δ)*CFC.sqrt (cut d δ))*y := by simp only [mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self (cut d δ) (cut_nonneg d δ)]
  change ∀ k : A, k ∈ Her (y*cut d δ*y) → ‖p*c*k‖ ≤ Real.sqrt (1-δ)*‖k‖
  intro k hk
  exact norm_mul_Her_of_order (Real.sqrt_nonneg _) hh (hq.symm ▸ hk)

end MainGap

namespace MainGap
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end MainGap

end

end OAI

-- ---- platform node ----
open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace


theorem solution : type_of% @_root_.OAI.MainGap.conditional_Her_loss := @_root_.OAI.MainGap.conditional_Her_loss
