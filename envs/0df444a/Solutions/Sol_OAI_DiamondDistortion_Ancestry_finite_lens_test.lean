-- Prove2me | solution 1 for OAI.DiamondDistortion.Ancestry.finite_lens_test
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:57:35.007274+00:00
-- url     : https://prove2.me/submissions/d68e9c40-5278-4188-957e-062ad2ddce37

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Ancestry.lean:L1076-L1102
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.Ancestry.finite_lens_test. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_finite_atomic_representation
import Theorems.Thm_OAI_DiamondDistortion_Ancestry_pooled_tail_test

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

lemma headDual_eq_self {H : Finset ι} {x : T.Dual}
    (hx : ∀ v, v ∉ H → x (T.unitVector v) = 0) : T.headDual H x = x := by
  apply T.dual_ext
  intro v
  rw [headDual_unit]
  split_ifs with hv
  · rfl
  · exact (hx v hv).symm

variable {T}

lemma LocalFamily.asFamily_subset {K : Finset ι} (F : T.LocalFamily K)
    (i : Fin F.asFamily.n) : F.asFamily.seg i ⊆ K :=
  T.localFamily_subset F _

variable (T)

lemma lawOfCoefficients_subset {K : Finset ι} (x : T.Dual) {R : ℝ} (hR : 0 < R)
    (c : T.Coefficients K) (hc : c ∈ T.coefficientBall K R)
    (hce : T.totalMap K c = fun v : K => x (T.unitVector v.val))
    (ω : Option (T.LocalFamily K))
    (i : Fin ((T.lawOfCoefficients x hR c hc hce).atom ω).family.n) :
    ((T.lawOfCoefficients x hR c hc hce).atom ω).family.seg i ⊆ K := by
  cases ω with
  | none => exact Fin.elim0 i
  | some F => exact F.asFamily_subset i

lemma pairLaws_subset {Ω : Type*} [Fintype Ω] {R : ℝ} {x y : T.Dual}
    (Lp : T.AtomLaw Ω R (x+y)) (Lm : T.AtomLaw Ω R (x-y)) (K : Finset ι)
    (hp : ∀ ω i, (Lp.atom ω).family.seg i ⊆ K)
    (hm : ∀ ω i, (Lm.atom ω).family.seg i ⊆ K) :
    ∀ ω i, ((T.pairLaws Lp Lm).atom ω).family.seg i ⊆ K := by
  rintro ⟨b,ω⟩ i
  cases b
  · exact hm ω i
  · exact hp ω i

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- from OAI.Analysis.DiamondDistortion.Ancestry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Ancestry
open scoped Classical
variable {ι : Type*} [A : Ancestry ι]
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
lemma finite_atomic_representation_radius {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (x : A.segments.Dual) {R : ℝ} (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) :
    ∃ c ∈ A.segments.coefficientBall K R,
      A.segments.totalMap K c = fun v : K => x (A.segments.unitVector v.val) := by
  classical
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hx0 : x = 0 := norm_eq_zero.mp (le_antisymm (by simpa [← hR0] using hx) (norm_nonneg _))
    refine ⟨0, ?_, ?_⟩
    · simp [SegmentSystem.coefficientBall, ← hR0]
    · rw [map_zero]
      ext v
      simp [hx0]
  have hxn : ‖R⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRpos)]
    exact (inv_mul_le_iff₀ hRpos).mpr (by simpa using hx)
  obtain ⟨c, hc, hce⟩ := A.finite_atomic_representation hK (R⁻¹ • x) hxn
  refine ⟨R • c, ?_, ?_⟩
  · change (∑ F, ‖R • c F‖) ≤ R
    simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos]
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hc hRpos.le).trans_eq (mul_one _)
  · rw [map_smul, hce]
    ext v
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hRpos.ne', one_mul]

/-- Pair the two exact finite atomic representations, retaining their common
    ancestral support and their actual endpoints. -/
lemma finite_lens_test {H K : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι)) (hHK : H ⊆ K)
    {R : ℝ} (hR : 0 < R) {x y : A.segments.Dual}
    (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R)
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H (A.segments.headDual K y)‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by
  classical
  obtain ⟨cp,hcp,hcep⟩ := A.finite_atomic_representation_radius hK (x+y) hR.le hplus
  obtain ⟨cm,hcm,hcem⟩ := A.finite_atomic_representation_radius hK (x-y) hR.le hminus
  have hxK : A.segments.headDual K x = x :=
    A.segments.headDual_eq_self (fun v hv => hx v (fun h => hv (hHK h)))
  let Lp0 := A.segments.lawOfCoefficients (x+y) hR cp hcp hcep
  let Lm0 := A.segments.lawOfCoefficients (x-y) hR cm hcm hcem
  let Lp : A.segments.AtomLaw (Option (A.segments.LocalFamily K)) R
      (x+A.segments.headDual K y) :=
    { Lp0 with mean := by rw [Lp0.mean, map_add, hxK] }
  let Lm : A.segments.AtomLaw (Option (A.segments.LocalFamily K)) R
      (x-A.segments.headDual K y) :=
    { Lm0 with mean := by rw [Lm0.mean, map_sub, hxK] }
  apply A.pooled_tail_test hH hK (A.segments.pairLaws Lp Lm) _ hx p hp hpn
  apply A.segments.pairLaws_subset Lp Lm K
  · exact A.segments.lawOfCoefficients_subset (x+y) hR cp hcp hcep
  · exact A.segments.lawOfCoefficients_subset (x-y) hR cm hcm hcem

end Ancestry

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder


theorem solution : type_of% @_root_.OAI.DiamondDistortion.Ancestry.finite_lens_test := @_root_.OAI.DiamondDistortion.Ancestry.finite_lens_test
